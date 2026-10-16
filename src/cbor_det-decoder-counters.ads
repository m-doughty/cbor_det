--  Deterministic CBOR: the decoder's operation counters.
--
--  Copyright (c) 2026, Matt Doughty
--  SPDX-License-Identifier: BSD-3-Clause
--
--  Ghost: what Check does, counted, for the tests of its cost bound. They
--  exist only in a build with assertions on (the contracts cell); a
--  production build has no trace of them. Each counter stops at U64'Last
--  rather than wrap.
--
--    Bytes_Parsed     the bytes of every head judged, and of every string
--                     accepted, once each
--    Bytes_Compared   the byte pairs compared while ordering map keys
--    Key_Comparisons  the comparisons of a map key with the key before it

package Cbor_Det.Decoder.Counters with SPARK_Mode, Ghost is

   use type Interfaces.Unsigned_64;

   Bytes_Parsed    : U64 := 0;
   Bytes_Compared  : U64 := 0;
   Key_Comparisons : U64 := 0;

   --  Every counter back to zero.
   procedure Reset
   with Global => (Output => (Bytes_Parsed, Bytes_Compared, Key_Comparisons)),
        Post   => Bytes_Parsed = 0 and then Bytes_Compared = 0
                  and then Key_Comparisons = 0,
        Always_Terminates;

   procedure Add_Parsed (N : Natural)
   with Global => (In_Out => Bytes_Parsed), Always_Terminates;

   procedure Add_Compared (N : Natural)
   with Global => (In_Out => Bytes_Compared), Always_Terminates;

   procedure Add_Comparison
   with Global => (In_Out => Key_Comparisons), Always_Terminates;

end Cbor_Det.Decoder.Counters;
