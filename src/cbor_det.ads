--  Deterministic CBOR (RFC 8949, section 4.2.1) in SPARK.
--
--  Copyright (c) 2026, Matt Doughty
--  SPDX-License-Identifier: BSD-3-Clause
--
--  This package will hold the types shared by the rest of the crate: the
--  byte and byte-array types, the nesting limit, and the status of a
--  check of an encoded item. Nothing is implemented yet: it contains
--  declarations only.

with Interfaces;

package Cbor_Det with SPARK_Mode, Pure is

   type Byte is new Interfaces.Unsigned_8;
   subtype U64 is Interfaces.Unsigned_64;
   subtype Index is Positive range 1 .. 2**31 - 2;
   type Bytes is array (Index range <>) of Byte;

   Max_Depth : constant := 16;

   type Status is
     (Ok,
      Truncated,
      Reserved_Info,
      Indefinite_Length,
      Unsupported_Type,
      Unsupported_Simple,
      Non_Shortest,
      Too_Deep,
      Unsorted_Key,
      Duplicate_Key,
      Trailing_Bytes);

end Cbor_Det;
