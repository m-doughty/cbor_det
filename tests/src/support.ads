--  cbor_det tests: counters, byte strings and the checks the runner makes
--  of its own build.
--
--  Copyright (c) 2026, Matt Doughty
--  SPDX-License-Identifier: BSD-3-Clause

with Interfaces;

with Cbor_Det; use Cbor_Det;

package Support is

   --  Every check passes or fails through these, so that the runner can
   --  print how many ran and fail the run if any failed.
   procedure Pass;
   procedure Fail (What : String);
   function Passed return Natural;
   function Failed return Natural;

   --  A byte string from hexadecimal ("" is empty), its first index 1.
   function Hex (Text : String) return Bytes;

   --  The bytes of B, with B'First = First. First may be any Integer when
   --  B is empty (a null array may have any bounds); otherwise the copy
   --  must fit in Index.
   function Rebase (B : Bytes; First : Integer) return Bytes;

   --  B in hexadecimal, for messages.
   function To_Hex (B : Bytes) return String;

   --  A decimal U64 ("18446744073709551615" at most).
   function Decimal (Text : String) return Interfaces.Unsigned_64;

   --  The bytes of B placed at Index'Last - B'Length + 1, so that the last
   --  byte is at Index'Last and an end is Index'Last + 1.
   function At_Top (B : Bytes) return Bytes;

   --  Whether the library was compiled with its contracts checked: a call
   --  whose precondition is false raises Assertion_Error only then. The
   --  library's ghost code exists only in that build.
   function Library_Has_Contracts return Boolean;

end Support;
