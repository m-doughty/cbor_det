--  Deterministic CBOR: heads.
--
--  Copyright (c) 2026, Matt Doughty
--  SPDX-License-Identifier: BSD-3-Clause
--
--  A head is an initial byte and the argument that follows it (RFC 8949,
--  section 3). Additional information 0 to 23 is the argument itself; 24,
--  25, 26 and 27 are followed by an argument of 1, 2, 4 and 8 bytes, big
--  endian. Additional information 28 to 31 is never accepted: 28 to 30
--  are not well formed (section 3), and 31 is an indefinite length,
--  which section 4.2.1 forbids.
--
--  The head helpers (Head_Len, Head_Fits, Arg, Shortest, Head_OK,
--  Len_Of_Arg, Encode_Head) are ordinary functions, so a decoder and a
--  writer can call them. Their specification lemmas are ghost:
--
--    * uniqueness: the bytes of an accepted head are Encode_Head of its
--      major type and argument, so two accepted heads with the same
--      major type and argument are the same bytes (Lemma_Head_Canonical,
--      Lemma_Head_Unique);
--    * conversely, the bytes of Encode_Head (M, A), wherever they sit,
--      are an accepted head of major type M and argument A
--      (Lemma_Head_Encoded);
--    * exact extent: a head's length is a function of its first byte
--      (Head_Len), so a head copied byte for byte is the same head, with
--      the same length, major type, argument and shortness
--      (Lemma_Head_Same).

package Cbor_Det.Proof.Heads with SPARK_Mode, Pure is

   use type Interfaces.Unsigned_64;

   --  The length of a head from its first byte; 0 for information 28 to
   --  31, which is never accepted.
   function Head_Len (IB : Byte) return Natural is
     (case Info_Of (IB) is
        when 0 .. 23  => 1,
        when 24       => 2,
        when 25       => 3,
        when 26       => 5,
        when 27       => 9,
        when 28 .. 31 => 0);

   --  The head at P is well formed in this profile and lies within B.
   function Head_Fits (B : Bytes; P : Positive) return Boolean is
     (Head_Len (B (P)) >= 1 and then Remaining (B, P) >= Head_Len (B (P)))
   with Pre => P in B'Range;

   --  The big-endian value of the 2, 4 or 8 bytes at P.
   function Be2 (B : Bytes; P : Positive) return U64 is
     (U64 (B (P)) * 2**8 + U64 (B (P + 1)))
   with Pre => P in B'Range and then Remaining (B, P) >= 2;
   pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", Be2);

   function Be4 (B : Bytes; P : Positive) return U64 is
     (U64 (B (P)) * 2**24 + U64 (B (P + 1)) * 2**16
      + U64 (B (P + 2)) * 2**8 + U64 (B (P + 3)))
   with Pre => P in B'Range and then Remaining (B, P) >= 4;
   pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", Be4);

   function Be8 (B : Bytes; P : Positive) return U64 is
     (U64 (B (P)) * 2**56 + U64 (B (P + 1)) * 2**48
      + U64 (B (P + 2)) * 2**40 + U64 (B (P + 3)) * 2**32
      + U64 (B (P + 4)) * 2**24 + U64 (B (P + 5)) * 2**16
      + U64 (B (P + 6)) * 2**8 + U64 (B (P + 7)))
   with Pre => P in B'Range and then Remaining (B, P) >= 8;
   pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", Be8);

   --  The argument of a head that fits: an integer's value (for major
   --  type 1, the value is -1 minus the argument), a string's length in
   --  bytes, an array's count of members, a map's count of pairs, or a
   --  simple value's number. Head_Fits leaves additional information 0
   --  to 27, so the last branch is 27.
   function Arg (B : Bytes; P : Positive) return U64 is
     (if Info_Of (B (P)) <= 23 then U64 (Info_Of (B (P)))
      elsif Info_Of (B (P)) = 24 then U64 (B (P + 1))
      elsif Info_Of (B (P)) = 25 then Be2 (B, P + 1)
      elsif Info_Of (B (P)) = 26 then Be4 (B, P + 1)
      else Be8 (B, P + 1))
   with Pre => P in B'Range and then Head_Fits (B, P);
   pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", Arg);

   --  RFC 8949, section 4.2.1, rule 1: the argument is encoded in as few
   --  bytes as possible. As in Arg, the last branch is 27.
   function Shortest (B : Bytes; P : Positive) return Boolean is
     (if Info_Of (B (P)) <= 23 then True
      elsif Info_Of (B (P)) = 24 then Arg (B, P) >= 24
      elsif Info_Of (B (P)) = 25 then Arg (B, P) >= 2**8
      elsif Info_Of (B (P)) = 26 then Arg (B, P) >= 2**16
      else Arg (B, P) >= 2**32)
   with Pre => P in B'Range and then Head_Fits (B, P);
   pragma Annotate
     (GNATprove, Hide_Info, "Expression_Function_Body", Shortest);

   --  An accepted head: well formed in this profile, within B, shortest.
   function Head_OK (B : Bytes; P : Positive) return Boolean is
     (Head_Fits (B, P) and then Shortest (B, P))
   with Pre => P in B'Range;

   --  The length of the shortest head for an argument.
   function Len_Of_Arg (A : U64) return Positive is
     (if A < 24 then 1 elsif A < 2**8 then 2 elsif A < 2**16 then 3
      elsif A < 2**32 then 5 else 9);

   --  The encoding of a head: the shortest one, which is the only one
   --  accepted.
   function Encode_Head (M : Major; A : U64) return Bytes
   with Post => Encode_Head'Result'First = 1
                and then Encode_Head'Result'Length = Len_Of_Arg (A)
                and then Head_OK (Encode_Head'Result, 1)
                and then Head_Len (Encode_Head'Result (1)) = Len_Of_Arg (A)
                and then Major_Of (Encode_Head'Result (1)) = M
                and then Arg (Encode_Head'Result, 1) = A;

   --  Uniqueness: an accepted head's bytes are Encode_Head of its major
   --  type and argument, and its length is that of the shortest head.
   procedure Lemma_Head_Canonical (B : Bytes; P : Positive)
   with Ghost,
        Pre  => P in B'Range and then Head_OK (B, P),
        Post => Head_Len (B (P)) = Len_Of_Arg (Arg (B, P))
                and then Same_Bytes
                  (B, P, P + Head_Len (B (P)),
                   Encode_Head (Major_Of (B (P)), Arg (B, P)),
                   1, Len_Of_Arg (Arg (B, P)) + 1);

   --  Two accepted heads with the same major type and argument are the
   --  same bytes.
   procedure Lemma_Head_Unique
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive)
   with Ghost,
        Pre  => P1 in B1'Range and then Head_OK (B1, P1)
                and then P2 in B2'Range and then Head_OK (B2, P2)
                and then Major_Of (B1 (P1)) = Major_Of (B2 (P2))
                and then Arg (B1, P1) = Arg (B2, P2),
        Post => Head_Len (B1 (P1)) = Head_Len (B2 (P2))
                and then Same_Bytes (B1, P1, P1 + Head_Len (B1 (P1)),
                                     B2, P2, P2 + Head_Len (B2 (P2)));

   --  The converse of uniqueness: the bytes of Encode_Head (M, A), at any
   --  place in any buffer, are an accepted head of major type M and
   --  argument A, of the shortest length for A.
   procedure Lemma_Head_Encoded
     (B : Bytes; P : Positive; M : Major; A : U64)
   with Ghost,
        Pre  => P in B'Range
                and then Remaining (B, P) >= Len_Of_Arg (A)
                and then Same_Bytes (B, P, P + Len_Of_Arg (A),
                                     Encode_Head (M, A),
                                     1, Len_Of_Arg (A) + 1),
        Post => Head_OK (B, P)
                and then Head_Len (B (P)) = Len_Of_Arg (A)
                and then Major_Of (B (P)) = M
                and then Arg (B, P) = A;

   --  A head copied byte for byte is the same head: it fits, and has the
   --  same length, major type, argument and shortness.
   procedure Lemma_Head_Same
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive)
   with Ghost,
        Pre  => P1 in B1'Range and then Head_Fits (B1, P1)
                and then P2 in B2'Range
                and then Remaining (B2, P2) >= Head_Len (B1 (P1))
                and then (for all K in 0 .. Head_Len (B1 (P1)) - 1 =>
                            B2 (P2 + K) = B1 (P1 + K)),
        Post => Head_Fits (B2, P2)
                and then Head_Len (B2 (P2)) = Head_Len (B1 (P1))
                and then Major_Of (B2 (P2)) = Major_Of (B1 (P1))
                and then Arg (B2, P2) = Arg (B1, P1)
                and then Shortest (B2, P2) = Shortest (B1, P1)
                and then Head_OK (B2, P2) = Head_OK (B1, P1);

end Cbor_Det.Proof.Heads;
