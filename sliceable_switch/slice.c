/*
 * Author: Yasunobu Chiba, Lei SUN
 *
 * Copyright (C) 2008-2012 NEC Corporation
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


#include <errno.h>
#include <inttypes.h>
#include <linux/limits.h>
#include <sqlite3.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>
#include "fdb.h"
#include "libpath.h"
#include "slice.h"
#include "port.h"
#include "filter.h"


#define SLICE_DB_UPDATE_INTERVAL 2

#define BINDING_AGING_INTERVAL 60
#define BINDING_TIMEOUT 3600
#define BINDING_ID_LENGTH 64

#define BINDING_TYPE_PORT 0x01
#define BINDING_TYPE_MAC 0x02
#define BINDING_TYPE_PORT_MAC 0x04

typedef struct {
  uint8_t type;
  uint64_t datapath_id;
  uint16_t port;
  uint16_t vid;
  uint8_t mac[ OFP_ETH_ALEN ];
  char id[ BINDING_ID_LENGTH ];
  uint16_t slice_number;
  bool dynamic;
  bool found_in_sqlite;
  time_t updated_at;
} binding_entry;

#define SLICE_NAME_LENGTH 64

typedef struct {
  uint16_t number;
  char id[ SLICE_NAME_LENGTH ];
  uint16_t n_mac_slice_maps;
  bool found_in_sqlite;
} slice_entry;

typedef struct {
  hash_table *slices;
  hash_table *port_slice_map;
  hash_table *mac_slice_map;
  hash_table *port_mac_slice_map;
  hash_table *port_slice_vid_map;
} slice_table;

static bool loose_mac_based_slicing = false;
static bool restrict_hosts_on_port = false;

static char slice_db_file[ PATH_MAX ];
static slice_table slice_db;
static time_t last_slice_db_mtime = 0;

static sliceable_switch *switch_instance = NULL;


static bool
compare_slice_entry( const void *x, const void *y ) {
  return ( memcmp( x, y, sizeof( uint16_t ) ) == 0 ) ? true : false;
}


static unsigned int
hash_slice_entry( const void *key ) {
  const uint16_t *hash = key;

  return ( unsigned int ) *hash;
}


static bool
compare_port_slice_entry( const void *x, const void *y ) {
  return ( memcmp( x, y, offsetof( binding_entry, mac ) ) == 0 ) ? true : false;
}


static unsigned int
hash_port_slice_entry( const void *key ) {
  unsigned int hash = 0;
  const binding_entry *entry = key;

  hash = ( unsigned int ) entry->datapath_id;
  hash += ( unsigned int ) entry->port;
  hash += ( unsigned int ) entry->vid;

  return hash;
}


static bool
compare_mac_slice_entry( const void *x, const void *y ) {
  const binding_entry *entry_x = x;
  const binding_entry *entry_y = y;

  bool ret = false;
  if ( entry_x->type == entry_y->type && memcmp( entry_x->mac, entry_y->mac, OFP_ETH_ALEN ) == 0 ) {
    ret = true;
  }

  return ret;
}


static unsigned int
hash_mac_slice_entry( const void *key ) {
  const binding_entry *entry = key;

  return hash_mac( entry->mac );
}


static bool
compare_port_mac_slice_entry( const void *x, const void *y ) {
  return ( memcmp( x, y, offsetof( binding_entry, id ) ) == 0 ) ? true : false;
}


static bool
compare_port_slice_vid_entry( const void *x, const void *y ) {
  const binding_entry *entry_x = x;
  const binding_entry *entry_y = y;

  if ( entry_x->datapath_id == entry_y->datapath_id &&
       entry_x->port == entry_y->port &&
       entry_x->slice_number == entry_y->slice_number ) {
    return true;
  }

  return false;
}


static unsigned int
hash_port_slice_vid_entry( const void *key ) {
  unsigned int hash = 0;
  const binding_entry *entry = key;

  hash = ( unsigned int ) entry->datapath_id;
  hash += ( unsigned int ) entry->port;
  hash += ( unsigned int ) entry->slice_number;

  return hash;
}


static bool
create_slice_db() {
  if ( slice_db.slices != NULL || slice_db.port_slice_map != NULL ||
       slice_db.mac_slice_map != NULL || slice_db.port_mac_slice_map != NULL ||
       slice_db.port_slice_vid_map != NULL ) {
    return false;
  }

  slice_db.slices = create_hash( compare_slice_entry, hash_slice_entry );
  slice_db.port_slice_map = create_hash( compare_port_slice_entry, hash_port_slice_entry );
  slice_db.mac_slice_map = create_hash( compare_mac_slice_entry, hash_mac_slice_entry );
  slice_db.port_mac_slice_map = create_hash( compare_port_mac_slice_entry, hash_mac_slice_entry );
  slice_db.port_slice_vid_map = create_hash( compare_port_slice_vid_entry, hash_port_slice_vid_entry );

  return true;
}


static bool
delete_slice_db() {
  if ( slice_db.slices == NULL || slice_db.port_slice_map == NULL ||
       slice_db.mac_slice_map == NULL || slice_db.port_mac_slice_map == NULL ||
       slice_db.port_slice_vid_map == NULL ) {
    return false;
  }

  hash_iterator iter;
  hash_entry *entry;

  init_hash_iterator( slice_db.slices, &iter );
  while ( ( entry = iterate_hash_next( &iter ) ) != NULL ) {
    xfree( entry->value );
  }
  delete_hash( slice_db.slices );
  slice_db.slices = NULL;

  init_hash_iterator( slice_db.port_slice_map, &iter );
  while ( ( entry = iterate_hash_next( &iter ) ) != NULL ) {
    if ( entry->value != NULL ) {
      xfree( entry->value );
      entry->value = NULL;
    }
  }
  delete_hash( slice_db.port_slice_map );
  slice_db.port_slice_map = NULL;

  delete_hash( slice_db.port_slice_vid_map );
  slice_db.port_slice_vid_map = NULL;

  init_hash_iterator( slice_db.mac_slice_map, &iter );
  while ( ( entry = iterate_hash_next( &iter ) ) != NULL ) {
    if ( entry->value != NULL ) {
      xfree( entry->value );
      entry->value = NULL;
    }
  }
  delete_hash( slice_db.mac_slice_map );
  slice_db.mac_slice_map = NULL;

  init_hash_iterator( slice_db.port_mac_slice_map, &iter );
  while ( ( entry = iterate_hash_next( &iter ) ) != NULL ) {
    if ( entry->value != NULL ) {
      xfree( entry->value );
      entry->value = NULL;
    }
  }
  delete_hash( slice_db.port_mac_slice_map );
  slice_db.port_mac_slice_map = NULL;

  return true;
}


static void
delete_slice_found_in_sqlite_flag( void *key, void *value, void *user_data ) {
  ( ( slice_entry * ) value)->found_in_sqlite = false;
}


static void
delete_binding_found_in_sqlite_flag( void *key, void *value, void *user_data ) {
  ( ( binding_entry * ) value)->found_in_sqlite = false;
}


static void
clean_found_in_sqlite_flags() {
  foreach_hash( slice_db.slices, delete_slice_found_in_sqlite_flag, NULL );
  foreach_hash( slice_db.port_slice_map, delete_binding_found_in_sqlite_flag, NULL );
  foreach_hash( slice_db.mac_slice_map, delete_binding_found_in_sqlite_flag, NULL );
  foreach_hash( slice_db.port_mac_slice_map, delete_binding_found_in_sqlite_flag, NULL );
}


static void
add_slice_entry( uint16_t number, const char *id ) {
  assert( id );

  slice_entry *found = lookup_hash_entry( slice_db.slices, &number );
  if ( found != NULL ) {
    found->found_in_sqlite = true;
    debug( "Slice entry is already registered ( number = %#x, id = %s ).",
           found->number, found->id );
    return;
  }

  slice_entry *entry = xmalloc( sizeof( slice_entry ) );
  entry->number = number;
  memset( entry->id, '\0', SLICE_NAME_LENGTH );
  memcpy( entry->id, id, SLICE_NAME_LENGTH - 1 );
  entry->n_mac_slice_maps = 0;
  entry->found_in_sqlite = true;

  info( "Adding a slice entry ( number = %#x, id = %s )", entry->number, entry->id );
  insert_hash_entry( slice_db.slices, entry, entry );
}


static void
add_port_slice_binding( uint64_t datapath_id, uint16_t port, uint16_t vid, uint16_t slice_number, const char *id, bool dynamic ) {
  assert( id );

  slice_entry *slice = lookup_hash_entry( slice_db.slices, &slice_number );
  if ( slice == NULL ) {
    error( "Invalid slice number ( %#x ).", slice_number );
    return;
  }

  binding_entry e;

  /* set required parameters to lookup_hash_entry() in port_slice_map */
  memset( &e, 0, offsetof( binding_entry, mac ) );
  e.type = BINDING_TYPE_PORT;
  e.datapath_id = datapath_id;
  e.port = port;
  e.vid = vid;

  binding_entry *found = lookup_hash_entry( slice_db.port_slice_map, &e );
  if ( found != NULL ) {
    found->found_in_sqlite = true;
    debug( "Port-slice entry is already registered ( datapath_id = %#" PRIx64 ", "
           "port = %u, vid = %u, id = %s, slice_number = %#x, dynamic = %d ).",
           found->datapath_id,
           found->port, found->vid, found->id, found->slice_number, found->dynamic );
    return;
  }

  binding_entry *entry = xmalloc( sizeof( binding_entry ) );
  memset( entry, 0, sizeof( binding_entry ) );
  memcpy( entry, &e, offsetof( binding_entry, mac ) );
  memset( entry->id, '\0', BINDING_ID_LENGTH );
  memcpy( entry->id, id, BINDING_ID_LENGTH - 1 );
  entry->slice_number = slice_number;
  entry->dynamic = dynamic;
  entry->found_in_sqlite = true;
  entry->updated_at = time( NULL );

  info( "Adding a port-slice binding ( datapath_id = %#" PRIx64 ", port = %#x, vid = %#x, "
        "id = %s, slice_number = %#x, dynamic = %d, updated_at = %" PRId64 " ).",
        entry->datapath_id, entry->port, entry->vid,
        entry->id, entry->slice_number, entry->dynamic, ( int64_t ) entry->updated_at );
  insert_hash_entry( slice_db.port_slice_map, entry, entry );
  insert_hash_entry( slice_db.port_slice_vid_map, entry, entry );
}


static void
add_mac_slice_binding( const uint8_t *mac, uint16_t slice_number, const char *id ) {
  assert( mac );
  assert( id );

  slice_entry *slice = lookup_hash_entry( slice_db.slices, &slice_number );
  if ( slice == NULL ) {
    error( "Invalid slice number ( %#x ).", slice_number );
    return;
  }

  binding_entry e;

  /* set required parameters to lookup_hash_entry() in mac_slice_map */
  memset( &e, 0, offsetof( binding_entry, id ) );
  e.type = BINDING_TYPE_MAC;
  memcpy( e.mac, mac, OFP_ETH_ALEN );

  binding_entry *found = lookup_hash_entry( slice_db.mac_slice_map, &e );
  if ( found != NULL ) {
    found->found_in_sqlite = true;
    debug( "Mac-slice entry is already registered ( mac = %02x:%02x:%02x:%02x:%02x:%02x, "
           "id = %s, slice_number = %#x ).",
           found->mac[ 0 ], found->mac[ 1 ], found->mac[ 2 ], found->mac[ 3 ], found->mac[ 4 ], found->mac[ 5 ],
           found->id, found->slice_number );
    return;
  }

  binding_entry *entry = xmalloc( sizeof( binding_entry ) );
  memset( entry, 0, sizeof( binding_entry ) );
  entry->type = e.type;
  memcpy( entry->mac, e.mac, OFP_ETH_ALEN );
  memset( entry->id, '\0', BINDING_ID_LENGTH );
  memcpy( entry->id, id, BINDING_ID_LENGTH - 1 );
  entry->slice_number = slice_number;
  entry->dynamic = false;
  entry->found_in_sqlite = true;
  entry->updated_at = time( NULL );

  info( "Adding a mac-slice binding ( mac = %02x:%02x:%02x:%02x:%02x:%02x, "
        "id = %s, slice_number = %#x ).",
        entry->mac[ 0 ], entry->mac[ 1 ], entry->mac[ 2 ], entry->mac[ 3 ], entry->mac[ 4 ], entry->mac[ 5 ],
        entry->id, entry->slice_number );
  insert_hash_entry( slice_db.mac_slice_map, entry, entry );
  slice->n_mac_slice_maps++;
}


static void
add_port_mac_slice_binding( uint64_t datapath_id, uint16_t port, uint16_t vid, uint8_t *mac, uint16_t slice_number, const char *id ) {
  assert( mac );
  assert( id );

  slice_entry *slice = lookup_hash_entry( slice_db.slices, &slice_number );
  if ( slice == NULL ) {
    error( "Invalid slice number ( %#x ).", slice_number );
    return;
  }

  binding_entry e;

  /* set required parameters to lookup_hash_entry() in port_mac_slice_map */
  memset( &e, 0, offsetof( binding_entry, id ) );
  e.type = BINDING_TYPE_PORT_MAC;
  e.datapath_id = datapath_id;
  e.port = port;
  e.vid = vid;
  memcpy( e.mac, mac, OFP_ETH_ALEN );

  binding_entry *found = lookup_hash_entry( slice_db.port_mac_slice_map, &e );
  if ( found != NULL ) {
    found->found_in_sqlite = true;
    debug( "Port_mac-slice entry is already registered ( datapath_id = %#" PRIx64 ", port = %#x, vid = %#x, "
           "mac = %02x:%02x:%02x:%02x:%02x:%02x, "
           "id = %s, slice_number = %#x ).",
           found->datapath_id, found->port, found->vid,
           found->mac[ 0 ], found->mac[ 1 ], found->mac[ 2 ], found->mac[ 3 ], found->mac[ 4 ], found->mac[ 5 ],
           found->id, found->slice_number );
    return;
  }

  binding_entry *entry = xmalloc( sizeof( binding_entry ) );
  memset( entry, 0, sizeof( binding_entry ) );
  memcpy( entry, &e, offsetof( binding_entry, id ) );
  entry->slice_number = slice_number;
  memset( entry->id, '\0', BINDING_ID_LENGTH );
  memcpy( entry->id, id, BINDING_ID_LENGTH - 1 );
  entry->dynamic = false;
  entry->found_in_sqlite = true;
  entry->updated_at = time( NULL );

  info( "Adding a port_mac-slice binding ( datapath_id = %#" PRIx64 ", port = %#x, vid = %#x, "
        "mac = %02x:%02x:%02x:%02x:%02x:%02x, "
        "id = %s,  slice_number = %#x ).",
        entry->datapath_id, entry->port, entry->vid,
        entry->mac[ 0 ], entry->mac[ 1 ], entry->mac[ 2 ], entry->mac[ 3 ], entry->mac[ 4 ], entry->mac[ 5 ],
        entry->id, entry->slice_number );
  insert_hash_entry( slice_db.port_mac_slice_map, entry, entry );
}


typedef struct {
  uint16_t slice_number;
  bool binding_exists;
} check_bindig_data;


static void
check_no_bindig_in_the_slice( void *key, void *value, void *user_data ) {
  binding_entry *b = value;
  check_bindig_data *data = user_data;

  if ( b->slice_number == data->slice_number ) {
    data->binding_exists = true;

    switch ( b->type ) {
    case BINDING_TYPE_PORT:
    {
      error( "a port-slice binding exists ( datapath_id = %#" PRIx64 ", port = %#x, vid = %#x, "
             "id = %s,  slice_number = %#x ).",
             b->datapath_id, b->port, b->vid,
             b->id, b->slice_number );
    }
    break;

    case BINDING_TYPE_MAC:
    {
      error( "a mac-slice binding exists ( mac = %02x:%02x:%02x:%02x:%02x:%02x, "
             "id = %s, slice_number = %#x ).",
             b->mac[ 0 ], b->mac[ 1 ], b->mac[ 2 ], b->mac[ 3 ], b->mac[ 4 ], b->mac[ 5 ],
             b->id, b->slice_number );
    }
    break;

    case BINDING_TYPE_PORT_MAC:
    {
      error( "a port_mac-slice binding exists ( datapath_id = %#" PRIx64 ", port = %#x, vid = %#x,"
             "mac = %02x:%02x:%02x:%02x:%02x:%02x, "
             "id = %s,  slice_number = %#x ).",
             b->datapath_id, b->port, b->vid,
             b->mac[ 0 ], b->mac[ 1 ], b->mac[ 2 ], b->mac[ 3 ], b->mac[ 4 ], b->mac[ 5 ],
             b->id, b->slice_number );
    }
    break;

    default:
      error( "Undefined binding type ( type = %u ).", b->type );
    }
  }
}


static void
delete_unfounded_in_sqlite_slices() {
  slice_entry *slice;
  hash_iterator iter;
  hash_entry *entry;
  check_bindig_data data;

  init_hash_iterator( slice_db.slices, &iter );
  while ( ( entry = iterate_hash_next( &iter ) ) != NULL ) {
    if ( entry->value != NULL ) {
      slice = entry->value;
      if ( slice->found_in_sqlite == false ) {
        info( "Deleting a slice entry ( number = %#x, id = %s )", slice->number, slice->id );

        data.slice_number = slice->number;
        data.binding_exists = false;

        foreach_hash( slice_db.port_slice_map, check_no_bindig_in_the_slice, &data );
        foreach_hash( slice_db.mac_slice_map, check_no_bindig_in_the_slice, &data );
        foreach_hash( slice_db.port_mac_slice_map, check_no_bindig_in_the_slice, &data );

        if ( data.binding_exists ) {
          error( "Failed to delete slice entry." );
        }
        else {
          delete_hash_entry( slice_db.slices, entry->value );
          xfree( entry->value );
        }
      }
    }
  }
}

static void
delete_flows_related_to_mac( const uint8_t *mac ) {
  struct ofp_match match;

  memset( &match, 0, sizeof( struct ofp_match ) );
  match.wildcards = OFPFW_ALL - OFPFW_DL_SRC;
  memcpy( match.dl_src, mac, OFP_ETH_ALEN );
  teardown_path_by_match( match );

  memset( &match, 0, sizeof( struct ofp_match ) );
  match.wildcards = OFPFW_ALL - OFPFW_DL_DST;
  memcpy( match.dl_dst, mac, OFP_ETH_ALEN );
  teardown_path_by_match( match );
}


static void
delete_unfounded_in_sqlite_bindings() {
  binding_entry *binding;
  hash_iterator iter;
  hash_entry *entry;

  init_hash_iterator( slice_db.port_mac_slice_map, &iter );
  while ( ( entry = iterate_hash_next( &iter ) ) != NULL ) {
    if ( entry->value != NULL ) {
      binding = entry->value;
      if ( binding->found_in_sqlite == false ) {
        info( "Deleting a port_mac-slice binding ( datapath_id = %#" PRIx64 ", port = %#x, vid = %#x, "
              "mac = %02x:%02x:%02x:%02x:%02x:%02x, "
              "id = %s,  slice_number = %#x ).",
              binding->datapath_id, binding->port, binding->vid,
              binding->mac[ 0 ], binding->mac[ 1 ], binding->mac[ 2 ],
              binding->mac[ 3 ], binding->mac[ 4 ], binding->mac[ 5 ],
              binding->id, binding->slice_number );

        delete_flows_related_to_mac( binding->mac );

        delete_hash_entry( slice_db.port_mac_slice_map, entry->value );
        xfree( entry->value );
      }
    }
  }

  /*
   * NOTE: Check if any mac binding is deleted. Since a dynamic port binding is
   *       automatically created from a mac binding, if any mac binding is deleted,
   *       all dynamic port bindings are cleaned in the deletion of port bindings.
   */
  bool mac_binding_deleted = false;

  init_hash_iterator( slice_db.mac_slice_map, &iter );
  while ( ( entry = iterate_hash_next( &iter ) ) != NULL ) {
    if ( entry->value != NULL ) {
      binding = entry->value;
      if ( binding->found_in_sqlite == false ) {
        info( "Deleting a mac-slice binding ( mac = %02x:%02x:%02x:%02x:%02x:%02x, "
              "id = %s,  slice_number = %#x ).",
              binding->mac[ 0 ], binding->mac[ 1 ], binding->mac[ 2 ],
              binding->mac[ 3 ], binding->mac[ 4 ], binding->mac[ 5 ],
              binding->id, binding->slice_number );

        delete_flows_related_to_mac( binding->mac );

        delete_hash_entry( slice_db.mac_slice_map, entry->value );
        xfree( entry->value );
        mac_binding_deleted = true;
      }
    }
  }

  init_hash_iterator( slice_db.port_slice_map, &iter );
  while ( ( entry = iterate_hash_next( &iter ) ) != NULL ) {
    if ( entry->value != NULL ) {
      binding = entry->value;
      if ( ( binding->found_in_sqlite == false && binding->dynamic == false ) ||
           ( mac_binding_deleted == true && binding->dynamic == true ) ) {
        info( "Deleting a port-slice binding ( datapath_id = %#" PRIx64 ", port = %#x, vid = %#x, "
              "id = %s,  slice_number = %#x ).",
              binding->datapath_id, binding->port, binding->vid,
              binding->id, binding->slice_number );

        teardown_path_by_port( binding->datapath_id, binding->port );

        delete_hash_entry( slice_db.port_slice_map, entry->value );
        delete_hash_entry( slice_db.port_slice_vid_map, entry->value );
        xfree( entry->value );
      }
    }
  }
}


static int
add_slice_entry_from_sqlite( void *NotUsed, int argc, char **argv, char **column ) {
  UNUSED( NotUsed );
  UNUSED( argc );
  UNUSED( column );

  uint16_t number = ( uint16_t ) atoi( argv[ 0 ] );

  add_slice_entry( number, argv[ 1 ] );

  return 0;
}


static int
add_binding_entry_from_sqlite( void *NotUsed, int argc, char **argv, char **column ) {
  UNUSED( NotUsed );
  UNUSED( argc );
  UNUSED( column );

  char *endp;

  uint8_t type = ( uint8_t ) atoi( argv[ 0 ] );

  switch ( type ) {
  case BINDING_TYPE_PORT:
  {
    uint64_t datapath_id = ( uint64_t ) strtoull( argv[ 1 ], &endp, 0 );
    uint16_t port = ( uint16_t ) atoi( argv[ 2 ] );
    uint16_t vid = ( uint16_t ) atoi( argv[ 3 ] );
    uint16_t slice_number = ( uint16_t ) atoi( argv[ 6 ] );
    char *id = argv[ 5 ];

    add_port_slice_binding( datapath_id, port, vid, slice_number, id, false );
  }
  break;

  case BINDING_TYPE_MAC:
  {
    uint8_t mac[ OFP_ETH_ALEN ];

    uint64_t mac_u64 = ( uint64_t ) strtoull( argv[ 4 ], &endp, 0 );

    mac[ 0 ] = ( uint8_t ) ( ( mac_u64 >> 40 ) & 0xff );
    mac[ 1 ] = ( uint8_t ) ( ( mac_u64 >> 32 ) & 0xff );
    mac[ 2 ] = ( uint8_t ) ( ( mac_u64 >> 24 ) & 0xff );
    mac[ 3 ] = ( uint8_t ) ( ( mac_u64 >> 16 ) & 0xff );
    mac[ 4 ] = ( uint8_t ) ( ( mac_u64 >> 8 ) & 0xff );
    mac[ 5 ] = ( uint8_t ) ( mac_u64 & 0xff );

    uint16_t slice_number = ( uint16_t ) atoi( argv[ 6 ] );
    char *id = argv[ 5 ];

    add_mac_slice_binding( mac, slice_number, id );
  }
  break;

  case BINDING_TYPE_PORT_MAC:
  {
    uint64_t datapath_id = ( uint64_t ) strtoull( argv[ 1 ], &endp, 0 );
    uint16_t port = ( uint16_t ) atoi( argv[ 2 ] );
    uint16_t vid = ( uint16_t ) atoi( argv[ 3 ] );
    uint16_t slice_number = ( uint16_t ) atoi( argv[ 6 ] );
    char *id = argv[ 5 ];

    uint8_t mac[ OFP_ETH_ALEN ];
    uint64_t mac_u64 = ( uint64_t ) strtoull( argv[ 4 ], &endp, 0 );

    mac[ 0 ] = ( uint8_t ) ( ( mac_u64 >> 40 ) & 0xff );
    mac[ 1 ] = ( uint8_t ) ( ( mac_u64 >> 32 ) & 0xff );
    mac[ 2 ] = ( uint8_t ) ( ( mac_u64 >> 24 ) & 0xff );
    mac[ 3 ] = ( uint8_t ) ( ( mac_u64 >> 16 ) & 0xff );
    mac[ 4 ] = ( uint8_t ) ( ( mac_u64 >> 8 ) & 0xff );
    mac[ 5 ] = ( uint8_t ) ( mac_u64 & 0xff );

    add_port_mac_slice_binding( datapath_id, port, vid, mac, slice_number, id );
  }
  break;

  default:
    error( "Undefined binding type ( type = %u ).", type );
    return -1;
  }

  return 0;
}


static void
age_dynamic_port_slice_bindings() {
  if ( slice_db.port_slice_map == NULL ) {
    return;
  }

  binding_entry *binding;
  hash_iterator iter;
  hash_entry *entry;

  init_hash_iterator( slice_db.port_slice_map, &iter );
  while ( ( entry = iterate_hash_next( &iter ) ) != NULL ) {
    if ( entry->value != NULL ){
      binding = entry->value;
      if ( ( binding->dynamic == true ) &&
           ( ( binding->updated_at + BINDING_TIMEOUT ) < time( NULL ) ) ){
        info( "Deleting a port-slice binding ( type = %#x, datapath_id = %#" PRIx64
              ", port = %#x, vid = %#x, slice_number = %#x, id = %s, dynamic = %d, updated_at = %" PRId64 " ).",
              binding->type, binding->datapath_id, binding->port, binding->vid, binding->slice_number, binding->id,
              binding->dynamic, ( int64_t ) binding->updated_at );
        delete_hash_entry( slice_db.port_slice_map, entry->value );
        delete_hash_entry( slice_db.port_slice_vid_map, entry->value );
        xfree( entry->value );
      }
    }
  }
}


void
delete_dynamic_port_slice_bindings( uint64_t datapath_id, uint16_t port ) {
  if ( slice_db.port_slice_map == NULL ) {
    return;
  }

  binding_entry *binding;
  hash_iterator iter;
  hash_entry *entry;

  init_hash_iterator( slice_db.port_slice_map, &iter );
  while ( ( entry = iterate_hash_next( &iter ) ) != NULL ) {
    if ( entry->value != NULL ){
      binding = entry->value;
      if ( binding->dynamic == true &&
           binding->datapath_id == datapath_id && binding->port == port ) {
        info( "Deleting a port-slice binding ( type = %#x, datapath_id = %#" PRIx64
              ", port = %#x, vid = %#x, slice_number = %#x, id = %s, dynamic = %d, updated_at = %" PRId64 " ).",
              binding->type, binding->datapath_id, binding->port, binding->vid, binding->slice_number, binding->id,
              binding->dynamic, ( int64_t ) binding->updated_at );
        delete_hash_entry( slice_db.port_slice_map, entry->value );
        delete_hash_entry( slice_db.port_slice_vid_map, entry->value );
        xfree( entry->value );
      }
    }
  }
}


static void
load_slice_definitions_from_sqlite( void *user_data ) {
  UNUSED( user_data );

  int ret;
  struct stat st;
  sqlite3 *db;

  memset( &st, 0, sizeof( struct stat ) );

  ret = stat( slice_db_file, &st );
  if ( ret < 0 ) {
    error( "Failed to stat %s (%s).", slice_db_file, strerror( errno ) );
    return;
  }

  if ( st.st_mtime == last_slice_db_mtime ) {
    debug( "Slice database is not changed." );
    return;
  }

  info( "Loading slice definitions." );

  last_slice_db_mtime = st.st_mtime;

  clean_found_in_sqlite_flags();

  ret = sqlite3_open( slice_db_file, &db );
  if ( ret ) {
    error( "Failed to load slice (%s).", sqlite3_errmsg( db ) );
    sqlite3_close( db );
    return;
  }

  ret = sqlite3_exec( db, "select * from slices",
                      add_slice_entry_from_sqlite, 0, NULL );
  if ( ret != SQLITE_OK ) {
    error( "Failed to execute a SQL statement (%s).", sqlite3_errmsg( db ) );
    sqlite3_close( db );
    return;
  }

  ret = sqlite3_exec( db, "select * from bindings",
                      add_binding_entry_from_sqlite, 0, NULL );
  if ( ret != SQLITE_OK ) {
    error( "Failed to execute a SQL statement (%s).", sqlite3_errmsg( db ) );
    sqlite3_close( db );
    return;
  }

  sqlite3_close( db );

  delete_unfounded_in_sqlite_bindings();
  delete_unfounded_in_sqlite_slices();

  return;
}


bool
init_slice( const char *file, uint16_t mode , sliceable_switch *instance ) {
  if ( switch_instance != NULL ) {
    error( "slice is already initialized." );
    return false;
  }

  if ( file == NULL || strlen( file ) == 0 ){
    error( "slice database must be specified." );
    return false;
  }

  if ( instance == NULL ){
    error( "switch instance must be specified." );
    return false;
  }

  switch_instance = instance;

  memset( slice_db_file, '\0', sizeof( slice_db_file ) );
  strncpy( slice_db_file, file, sizeof( slice_db_file) );

  create_slice_db();

  load_slice_definitions_from_sqlite( NULL );

  add_periodic_event_callback( SLICE_DB_UPDATE_INTERVAL,
                               load_slice_definitions_from_sqlite,
                               NULL );

  add_periodic_event_callback( BINDING_AGING_INTERVAL,
                               age_dynamic_port_slice_bindings,
                               NULL );

  if ( mode & LOOSE_MAC_BASED_SLICING ) {
    loose_mac_based_slicing = true;
  }
  if ( mode & RESTRICT_HOSTS_ON_PORT ) {
    restrict_hosts_on_port = true;
  }

  return true;
}


bool
finalize_slice() {
  delete_slice_db();
  memset( slice_db_file, '\0', sizeof( slice_db_file ) );
  switch_instance = NULL;

  return true;
}


bool
get_port_vid( uint16_t slice_number, uint64_t datapath_id, uint16_t port, uint16_t *vid ) {
  binding_entry entry;
  memset( &entry, 0, sizeof( binding_entry ) );
  entry.datapath_id = datapath_id;
  entry.port = port;
  entry.slice_number = slice_number;

  binding_entry *found = lookup_hash_entry( slice_db.port_slice_vid_map, &entry );
  if ( found == NULL ) {
    return false;
  }

  *vid = found->vid;

  return true;
}


uint16_t
lookup_slice_by_mac( const uint8_t *mac ) {
  if ( mac == NULL ) {
    error( "MAC address is not specified." );
    return SLICE_NOT_FOUND;
  }

  binding_entry entry;
  memset( &entry, 0, sizeof( binding_entry ) );
  entry.type = BINDING_TYPE_MAC;
  memcpy( entry.mac, mac, OFP_ETH_ALEN );
  binding_entry *found = lookup_hash_entry( slice_db.mac_slice_map, &entry );
  if ( found != NULL ) {
    debug( "Slice found in mac-slice map ( slice_number = %#x )", found->slice_number );
    return found->slice_number;
  }

  debug( "No slice found." );
  return SLICE_NOT_FOUND;
}


bool
loose_mac_based_slicing_enabled() {
  return loose_mac_based_slicing;
}


static bool
restrict_hosts_on_port_enabled() {
  return restrict_hosts_on_port;
}


bool
mac_slice_maps_exist( uint16_t slice_number ) {
  slice_entry *found = lookup_hash_entry( slice_db.slices, &slice_number );
  if ( found == NULL ) {
    return false;
  }

  if ( found->n_mac_slice_maps == 0 ) {
    return false;
  }

  return true;
}


uint16_t
lookup_slice( uint64_t datapath_id, uint16_t port, uint16_t vid, const uint8_t *mac ) {
  void *found;
  uint16_t slice_number;
  binding_entry entry;

  memset( &entry, 0, sizeof( binding_entry ) );
  entry.datapath_id = datapath_id;
  entry.port = port;
  entry.vid = vid;

  if ( mac != NULL ) {
    memcpy( entry.mac, mac, OFP_ETH_ALEN );
    entry.type = BINDING_TYPE_MAC;
    found = lookup_hash_entry( slice_db.mac_slice_map, &entry );
    if ( found != NULL ) {
      slice_number = ( ( binding_entry * ) found )->slice_number;
      debug( "Slice found in mac-slice map ( slice_number = %#x ).", slice_number );
      if ( !loose_mac_based_slicing_enabled() ) {
        entry.type = BINDING_TYPE_PORT;
        found = lookup_hash_entry( slice_db.port_slice_map, &entry );
        if ( found != NULL ) {
          uint16_t port_slice_number = ( ( binding_entry * ) found )->slice_number;
          if ( slice_number == port_slice_number ) {
            ( ( binding_entry * ) found )->updated_at = time( NULL );
          }
        }
        else{
          char id[ BINDING_ID_LENGTH ];
          sprintf( id, "%012" PRIx64 ":%04x:%04x", datapath_id, port, vid );
          add_port_slice_binding( datapath_id, port, vid, slice_number, id, true );
        }
      }
      goto found;
    }

    if ( restrict_hosts_on_port_enabled() ) {
      entry.type = BINDING_TYPE_PORT_MAC;
      found = lookup_hash_entry( slice_db.port_mac_slice_map, &entry );
      if( found != NULL ) {
        slice_number = ( ( binding_entry * ) found )->slice_number;
        debug( "Slice found in port_mac-slice map ( slice_number = %#x ).", slice_number );
        goto found;
      }
    }
  }

  if ( !restrict_hosts_on_port_enabled() ) {
    entry.type = BINDING_TYPE_PORT;
    found = lookup_hash_entry( slice_db.port_slice_map, &entry );
    if( found != NULL ) {
      slice_number = ( ( binding_entry * ) found )->slice_number;
      debug( "Slice found in port-slice map ( slice_number = %#x ).", slice_number );
      goto found;
    }
  }

not_found:
  debug( "No slice found." );
  return SLICE_NOT_FOUND;

found:
  found = lookup_hash_entry( slice_db.slices, &slice_number );
  if ( found == NULL ) {
    goto not_found;
  }

  return slice_number;
}


/*
 * Local variables:
 * c-basic-offset: 2
 * indent-tabs-mode: nil
 * End:
 */
