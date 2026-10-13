--  Deterministic CBOR: transport and prefix-freedom.
--
--  Copyright (c) 2026, Matt Doughty
--  SPDX-License-Identifier: BSD-3-Clause
--
--  Transport: an accepted item, or an accepted run of members, copied
--  byte for byte to another place (in the same buffer or another) is
--  accepted there, with the corresponding end, and each member starts at
--  the corresponding place. So whether an item is accepted, and where it
--  ends, depends only on its own bytes: not on where it sits, nor on
--  what follows it. The key order carries with it.
--
--  Prefix-freedom: no accepted item is a proper prefix of another
--  accepted item.

with Cbor_Det.Proof.Det; use Cbor_Det.Proof.Det;

package Cbor_Det.Proof.Transport with SPARK_Mode, Ghost is

   --  The order depends only on the bytes compared.
   procedure Lemma_Lex_Less_Same
     (A1 : Bytes; P1 : Natural; E1 : Natural;
      A2 : Bytes; P2 : Natural; E2 : Natural;
      C1 : Bytes; R1 : Natural; F1 : Natural;
      C2 : Bytes; R2 : Natural; F2 : Natural)
   with Pre  => Slice_OK (A1, P1, E1) and then Slice_OK (A2, P2, E2)
                and then Slice_OK (C1, R1, F1) and then Slice_OK (C2, R2, F2)
                and then Same_Bytes (A1, P1, E1, C1, R1, F1)
                and then Same_Bytes (A2, P2, E2, C2, R2, F2),
        Post => Lex_Less (A1, P1, E1, A2, P2, E2)
                = Lex_Less (C1, R1, F1, C2, R2, F2),
        Subprogram_Variant => (Decreases => E1 - P1);

   --  The key order of N keys carries to a byte-for-byte copy of a run of
   --  K members whose members start at the corresponding places. The run
   --  holds at least the N keys: K >= 2 N - 1.
   procedure Lemma_Keys_Transport
     (B1 : Bytes; Q1 : Positive; B2 : Bytes; Q2 : Positive;
      N : Natural; K : Natural; D : Natural)
   with Pre  => Q1 in B1'First .. B1'Last + 1
                and then Q2 in B2'First .. B2'Last + 1
                and then N <= 2**30 - 1
                and then (N = 0 or else K >= 2 * N - 1)
                and then Members_End (B1, Q1, K, D) /= 0
                and then Keys_Ascending (B1, Q1, N, D)
                and then Members_End (B1, Q1, K, D) - Q1 <= B2'Last + 1 - Q2
                and then Same_Bytes
                  (B1, Q1, Members_End (B1, Q1, K, D),
                   B2, Q2, Q2 + (Members_End (B1, Q1, K, D) - Q1))
                and then (for all J in 0 .. K =>
                            Members_End (B1, Q1, J, D) /= 0
                            and then Members_End (B1, Q1, J, D)
                                     <= Members_End (B1, Q1, K, D)
                            and then Members_End (B2, Q2, J, D)
                                     = Q2 + (Members_End (B1, Q1, J, D) - Q1))
                and then (for all J in 1 .. K =>
                            Members_End (B1, Q1, J - 1, D)
                            < Members_End (B1, Q1, J, D)),
        Post => Keys_Ascending (B2, Q2, N, D);

   --  An accepted run of K members, copied byte for byte, is accepted at
   --  the copy, and every member ends at the corresponding place.
   procedure Lemma_Members_Transport
     (B1 : Bytes; Q1 : Positive; B2 : Bytes; Q2 : Positive;
      K : Natural; D : Natural)
   with Pre  => Q1 in B1'First .. B1'Last + 1
                and then Q2 in B2'First .. B2'Last + 1
                and then Members_End (B1, Q1, K, D) /= 0
                and then Members_End (B1, Q1, K, D) - Q1 <= B2'Last + 1 - Q2
                and then Same_Bytes
                  (B1, Q1, Members_End (B1, Q1, K, D),
                   B2, Q2, Q2 + (Members_End (B1, Q1, K, D) - Q1)),
        Post => (for all J in 0 .. K =>
                   Members_End (B1, Q1, J, D) /= 0
                   and then Members_End (B2, Q2, J, D)
                            = Q2 + (Members_End (B1, Q1, J, D) - Q1)),
        Subprogram_Variant => (Decreases => D, Decreases => K);

   --  An accepted item, copied byte for byte, is accepted at the copy and
   --  ends at the corresponding place.
   procedure Lemma_Transport
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Natural)
   with Pre  => P1 in B1'Range and then P2 in B2'Range
                and then Det_End (B1, P1, D) /= 0
                and then Det_End (B1, P1, D) - P1 <= B2'Last + 1 - P2
                and then Same_Bytes
                  (B1, P1, Det_End (B1, P1, D),
                   B2, P2, P2 + (Det_End (B1, P1, D) - P1)),
        Post => Det_End (B2, P2, D) = P2 + (Det_End (B1, P1, D) - P1);

   --  Prefix-freedom: no accepted item is a proper prefix of an accepted
   --  item. Stated as a contradiction: two accepted items at the same
   --  depth, the second longer than the first, cannot start with the
   --  bytes of the first.
   procedure Lemma_Prefix_Free
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Natural)
   with Pre  => P1 in B1'Range and then P2 in B2'Range
                and then Det_End (B1, P1, D) /= 0
                and then Det_End (B2, P2, D) /= 0
                and then Det_End (B2, P2, D) - P2 > Det_End (B1, P1, D) - P1
                and then Same_Bytes
                  (B1, P1, Det_End (B1, P1, D),
                   B2, P2, P2 + (Det_End (B1, P1, D) - P1)),
        Post => False;

end Cbor_Det.Proof.Transport;
