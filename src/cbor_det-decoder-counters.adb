--  Deterministic CBOR: the decoder's operation counters.
--
--  Copyright (c) 2026, Matt Doughty
--  SPDX-License-Identifier: BSD-3-Clause

package body Cbor_Det.Decoder.Counters with SPARK_Mode is

   --  C + N, or U64'Last if that is more.
   function Plus (C : U64; N : Natural) return U64 is
     (if C <= U64'Last - U64 (N) then C + U64 (N) else U64'Last);

   procedure Reset is
   begin
      Bytes_Parsed := 0;
      Bytes_Compared := 0;
      Key_Comparisons := 0;
   end Reset;

   procedure Add_Parsed (N : Natural) is
   begin
      Bytes_Parsed := Plus (Bytes_Parsed, N);
   end Add_Parsed;

   procedure Add_Compared (N : Natural) is
   begin
      Bytes_Compared := Plus (Bytes_Compared, N);
   end Add_Compared;

   procedure Add_Comparison is
   begin
      Key_Comparisons := Plus (Key_Comparisons, 1);
   end Add_Comparison;

end Cbor_Det.Decoder.Counters;
