/*
 * Author: Ryota Mibu
 *
 * Copyright (C) 2011-2012 NEC Corporation
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License, version 2, as
 * published by the Free Software Foundation.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License along
 * with this program; if not, write to the Free Software Foundation, Inc.,
 * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 */


#include <assert.h>
#include <errno.h>
#include <linux/limits.h>
#include <string.h>
#include <sys/inotify.h>
#include <unistd.h>
#include "file_modification_watcher.h"


typedef struct {
  char file[ PATH_MAX ];
  void ( *callback )( void *user_data );
  void *user_data;
  int watch_descriptor;
  bool modified;
} watch_entry;


const static uint32_t watch_mask = IN_MODIFY | IN_CLOSE_WRITE | IN_MOVE_SELF | IN_DELETE_SELF;
const static uint32_t error_mask = IN_MOVE_SELF | IN_DELETE_SELF | IN_IGNORED | IN_Q_OVERFLOW | IN_UNMOUNT;
static int fd = -1;
static dlist_element *watch_list = NULL;


static watch_entry *
find_watch_by_file( const char *file ) {
  if ( watch_list == NULL ) {
    return NULL;
  }

  for ( dlist_element *e = watch_list->next; e != NULL; e = e->next ) {
    watch_entry *watch = e->data;
    if ( watch != NULL && compare_string( file, watch->file ) ) {
      return watch;
    }
  }

  return NULL;
}


static watch_entry *
find_watch_by_descriptor( const int descriptor ) {
  if ( watch_list == NULL ) {
    return NULL;
  }

  for ( dlist_element *e = watch_list->next; e != NULL; e = e->next ) {
    watch_entry *watch = e->data;
    if ( watch != NULL && descriptor == watch->watch_descriptor ) {
      return watch;
    }
  }

  return NULL;
}


static void
finalize_file_modification_watcher() {
  debug( "Finalizing file modification watcher." );

  assert( fd >= 0 );
  assert( watch_list != NULL );

  set_readable( fd, false );
  delete_fd_handler( fd );
  close( fd );
  fd = -1;

  debug( "Deleting watch list ( watch_list = %p ).", watch_list );
  for ( dlist_element *e = watch_list->next; e != NULL; e = e->next ) {
    xfree( e->data );
  }
  delete_dlist( watch_list );
  watch_list = NULL;
}


static void
read_inotify_events() {
  static char read_buffer[ sizeof( struct inotify_event ) * 128 ];

  ssize_t length = read( fd, read_buffer, sizeof( read_buffer ) );
  if ( length <= 0 ) {
    if ( errno == EINVAL || errno == EINTR ) {
      error( "Failed to read events ( length = %d, errno = %s [%d] ).", length, strerror( errno ), errno );
      finalize_file_modification_watcher();
    }
    else {
      warn( "Failed to read events ( length = %d )." );
    }
    return;
  }
  debug( "Read inotify events ( length = %d ).", length );

  struct inotify_event *event = ( struct inotify_event * ) read_buffer;
  while ( length >= sizeof( struct inotify_event ) ) {
    watch_entry *watch = find_watch_by_descriptor( event->wd );

    debug( "Event notified ( fd = %d, wd = %d, mask = %#x, length = %d, file = %s ).",
           fd, event->wd, event->mask, event->len, watch->file );

    if ( ( event->mask & error_mask ) != 0 ) {
      warn( "Error event(s) detected ( file = %s, mask = %#x ).", watch->file, event->mask );
      delete_file_modification_watch( watch->file );
      return;
    }

    if ( ( event->mask & IN_MODIFY ) != 0 ) {
      debug( "File modified ( file = %s, mask = %#x ).", watch->file, event->mask );
      watch->modified = true;
    }

    if ( ( watch->modified == true ) && ( ( event->mask & IN_CLOSE_WRITE ) != 0 ) ) {
      debug( "Executing callback ( callback = %p, user_data = %p ).", watch->callback, watch->user_data );
      watch->callback( watch->user_data );
      watch->modified = false;
    }

    size_t offset = sizeof( struct inotify_event ) + event->len;
    event = ( struct inotify_event * ) ( ( char * ) event + offset );
    length -= offset;
  }
}


static bool
init_file_modification_watcher() {
  debug( "Initializing file modification watcher." );

  assert( fd == -1 );
  assert( watch_list == NULL );

  fd = inotify_init();
  if ( fd < 0 ) {
    error( "Failed to initialize inotify ( fd = %d, errno = %s [%d]).", fd, strerror( errno ), errno );
    return false;
  }

  set_fd_handler( fd, ( event_fd_callback ) read_inotify_events, NULL, NULL, NULL );
  set_readable( fd, true );

  watch_list = create_dlist();
  if ( watch_list == NULL ) {
    error( "Failed to create watch list." );
    return false;
  }
  debug( "watch list created ( watch_list = %p ).", watch_list );
  return true;
}


bool
add_file_modification_watch( const char *file, void ( *callback )( void *user_data ), void *user_data ) {
  debug( "Adding a file modification watch ( file = %s, callback = %p, user_data = %p ).", file, callback, user_data );

  if ( callback == NULL ) {
    error( "Callback function must be specified." );
    return false;
  }

  if ( fd < 0 && !init_file_modification_watcher() ) {
    error( "Failed to initialize file_modification_watcher." );
    return false;
  }

  if ( find_watch_by_file( file ) != NULL ) {
    warn( "Watch entry already exists ( file = %s ).", file );
    return false;
  }

  watch_entry *watch = xmalloc( sizeof( watch_entry ) );
  memset( watch, 0, sizeof( watch_entry ) );

  watch->watch_descriptor = inotify_add_watch( fd, file, watch_mask );
  if ( watch->watch_descriptor < 0 ) {
    error( "Failed to add a watch ( file = %s, errno = %s [%d] ).", file, strerror( errno ), errno );
    xfree( watch );
    return false;
  }

  strncpy( watch->file, file, PATH_MAX );
  watch->file[ PATH_MAX - 1 ] = '\0';
  watch->callback = callback;
  watch->user_data = user_data;
  watch->modified = false;

  insert_after_dlist( watch_list, watch );

  return true;
}


bool
delete_file_modification_watch( const char *file ) {
  debug( "Deleting a file modification watch ( file = %s ).", file );

  watch_entry *watch = find_watch_by_file( file );
  if ( watch == NULL ) {
    error( "Watch entry does NOT exist ( file = %s ).", file );
    return false;
  }

  bool ret = true;
  if ( inotify_rm_watch( fd, watch->watch_descriptor ) != 0 ) {
    error( "Failed to remove a watch ( file = %s, fd = %d, watch_descriptor = %s , errno = %s [%d]).", file, fd, watch->watch_descriptor, strerror( errno ), errno );
    ret = false;
  }

  xfree( watch );

  dlist_element *e = ( dlist_element * ) ( ( char * ) watch - offsetof( dlist_element, data ) );
  if ( e->prev == NULL && e->next == NULL ) {
    finalize_file_modification_watcher();
  }
  else {
    delete_dlist_element( e );
  }

  return ret;
}


/*
 * Local variables:
 * c-basic-offset: 2
 * indent-tabs-mode: nil
 * End:
 */
