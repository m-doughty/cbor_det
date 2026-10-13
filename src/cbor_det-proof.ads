--  Deterministic CBOR: the vocabulary shared by the proof units.
--
--  Copyright (c) 2026, Matt Doughty
--  SPDX-License-Identifier: BSD-3-Clause
--
--  The major type and additional information of an initial byte (RFC
--  8949, section 3), the bytes left in a buffer, slices of a buffer, and
--  the ghost relation "two slices hold the same bytes". Nothing here
--  reads or writes anything outside its arguments.
--
--  Positions. A buffer B has the index range of Index, so one past its
--  last byte, B'Last + 1, is still a Positive. An end (Ext) is one past
--  the last byte of an item, at most B'Last + 1; 0 means "no item".

package Cbor_Det.Proof with SPARK_Mode, Pure is

   --  One past the last byte of an item, or 0 for "rejected".
   subtype Ext is Natural;

   subtype Major is Byte range 0 .. 7;
   subtype Info is Byte range 0 .. 31;

   --  The major type (the high three bits) of an initial byte.
   function Major_Of (IB : Byte) return Major is (IB / 32);

   --  The additional information (the low five bits) of an initial byte.
   function Info_Of (IB : Byte) return Info is (IB mod 32);

   --  The bytes left from P to the end of B, P included.
   function Remaining (B : Bytes; P : Positive) return Positive is
     (B'Last - P + 1)
   with Pre => P in B'Range;

   --  P .. E - 1 is a slice of B: possibly empty, possibly at the end.
   function Slice_OK (B : Bytes; P : Natural; E : Natural) return Boolean is
     (P in B'First .. B'Last + 1 and then E in P .. B'Last + 1);

   --  Two slices hold the same bytes. Total: False unless both are
   --  slices. Stated both ways round, with an absolute index, so that a
   --  prover's quantifier triggers match the byte terms it meets. Hidden:
   --  the proofs use it through the lemmas of Cbor_Det.Proof.Det.
   function Same_Bytes
     (B1 : Bytes; P1 : Natural; E1 : Natural;
      B2 : Bytes; P2 : Natural; E2 : Natural) return Boolean
   is (Slice_OK (B1, P1, E1) and then Slice_OK (B2, P2, E2)
       and then E1 - P1 = E2 - P2
       and then (for all X in P1 .. E1 - 1 => B1 (X) = B2 (X - P1 + P2))
       and then (for all Y in P2 .. E2 - 1 => B2 (Y) = B1 (Y - P2 + P1)))
   with Ghost;
   pragma Annotate
     (GNATprove, Hide_Info, "Expression_Function_Body", Same_Bytes);

end Cbor_Det.Proof;
