--  Deterministic CBOR: proof clients of the exported lemmas.
--
--  Copyright (c) 2026, Matt Doughty
--  SPDX-License-Identifier: BSD-3-Clause
--
--  Each procedure here consumes the contract of one or more lemmas of
--  Cbor_Det.Proof.Heads, .Det and .Transport, as a later proof will, and
--  proves from that contract alone a guarantee a later proof relies on:
--  each client's body hides the recursive definitions again (their
--  Hide_Info in Cbor_Det.Proof.Det follows a completion and so hides them
--  only within that unit); the slice relation and the decoding of
--  arguments are hidden everywhere; only Same_Bytes is opened where a
--  guarantee is stated byte by byte. So if a lemma's contract
--  said less, a client here would no longer prove: the clients pin what
--  the lemmas promise, beyond the uses the proofs of this crate make of
--  them so far.
--
--  Nothing here runs: the package is ghost.

with Cbor_Det.Proof.Heads;     use Cbor_Det.Proof.Heads;
with Cbor_Det.Proof.Det;       use Cbor_Det.Proof.Det;

package Cbor_Det.Proof.Surface with SPARK_Mode, Ghost is

   use type Interfaces.Unsigned_64;

   ---------------------------------------------------------------------
   --  Heads.
   ---------------------------------------------------------------------

   --  Two accepted heads with the same major type and argument have the
   --  same length and are the same bytes, byte by byte (from
   --  Lemma_Head_Unique).
   procedure Client_Head_Unique_Bytes
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; K : Natural)
   with Pre  => P1 in B1'Range and then Head_OK (B1, P1)
                and then P2 in B2'Range and then Head_OK (B2, P2)
                and then Major_Of (B1 (P1)) = Major_Of (B2 (P2))
                and then Arg (B1, P1) = Arg (B2, P2)
                and then K < Head_Len (B1 (P1)),
        Post => Head_Len (B2 (P2)) = Head_Len (B1 (P1))
                and then B2 (P2 + K) = B1 (P1 + K);

   --  The bytes of Encode_Head (M, A) for an integer, wherever they sit,
   --  are an accepted integer of argument A whose end is right after its
   --  head (from Lemma_Head_Encoded).
   procedure Client_Encoded_Integer
     (B : Bytes; P : Positive; M : Major; A : U64; D : Natural)
   with Pre  => P in B'Range and then M in 0 | 1
                and then Remaining (B, P) >= Len_Of_Arg (A)
                and then Same_Bytes (B, P, P + Len_Of_Arg (A),
                                     Encode_Head (M, A),
                                     1, Len_Of_Arg (A) + 1),
        Post => Det_End (B, P, D) = P + Len_Of_Arg (A)
                and then Major_Of (B (P)) = M
                and then Arg (B, P) = A;

   ---------------------------------------------------------------------
   --  Containers.
   ---------------------------------------------------------------------

   --  Every key of an accepted map is greater than the key before it
   --  (from Lemma_Det_Container's keys and Lemma_Keys_All).
   procedure Client_Map_Keys_Ordered
     (B : Bytes; P : Positive; D : Natural)
   with Pre  => P in B'Range and then Det_End (B, P, D) /= 0
                and then Major_Of (B (P)) = 5,
        Post => (for all J in 2 .. Arg_Nat (B, P) =>
                   Lex_Less
                     (B,
                      Members_End (B, P + Head_Len (B (P)), 2 * J - 4, D - 1),
                      Members_End (B, P + Head_Len (B (P)), 2 * J - 3, D - 1),
                      B,
                      Members_End (B, P + Head_Len (B (P)), 2 * J - 2, D - 1),
                      Members_End
                        (B, P + Head_Len (B (P)), 2 * J - 1, D - 1)));

   --  An accepted map ends where its keys and values end, one depth down
   --  (from Lemma_Det_Container).
   procedure Client_Map_Members (B : Bytes; P : Positive; D : Natural)
   with Pre  => P in B'Range and then Det_End (B, P, D) /= 0
                and then Major_Of (B (P)) = 5,
        Post => Det_End (B, P, D)
                = Members_End (B, P + Head_Len (B (P)),
                               2 * Arg_Nat (B, P), D - 1);

   --  An accepted array ends where its members end, and each member is
   --  an accepted item one depth down that starts where the one before
   --  it ends (from Lemma_Det_Container and Lemma_Members_Monotone).
   procedure Client_Array_Members (B : Bytes; P : Positive; D : Natural)
   with Pre  => P in B'Range and then Det_End (B, P, D) /= 0
                and then Major_Of (B (P)) = 4,
        Post => Det_End (B, P, D)
                = Members_End (B, P + Head_Len (B (P)), Arg_Nat (B, P), D - 1)
                and then
                  (for all J in 1 .. Arg_Nat (B, P) =>
                     Members_End (B, P + Head_Len (B (P)), J - 1, D - 1)
                     < Members_End (B, P + Head_Len (B (P)), J, D - 1)
                     and then Members_End (B, P + Head_Len (B (P)), J, D - 1)
                              <= B'Last + 1
                     and then
                       Members_End (B, P + Head_Len (B (P)), J, D - 1)
                       = Det_End
                           (B,
                            Members_End
                              (B, P + Head_Len (B (P)), J - 1, D - 1),
                            D - 1));

   --  A container with a member that is not accepted is not accepted
   --  (from Lemma_Members_Zero).
   procedure Client_Array_Member_Fails
     (B : Bytes; P : Positive; D : Natural; I : Natural)
   with Pre  => P in B'Range and then Head_OK (B, P)
                and then Major_Of (B (P)) = 4 and then D >= 1
                and then Arg_Fits (B, P, Remaining (B, P) - Head_Len (B (P)))
                and then I <= Arg_Nat (B, P)
                and then Members_End (B, P + Head_Len (B (P)), I, D - 1) = 0,
        Post => Det_End (B, P, D) = 0;

   --  A map with two keys out of order is not accepted (from
   --  Lemma_Keys_Break).
   procedure Client_Map_Unsorted
     (B : Bytes; P : Positive; D : Natural; J : Positive)
   with Pre  => P in B'Range and then Head_OK (B, P)
                and then Major_Of (B (P)) = 5 and then D >= 1
                and then Arg_Fits
                  (B, P, (Remaining (B, P) - Head_Len (B (P))) / 2)
                and then J in 2 .. Arg_Nat (B, P)
                and then not Lex_Less
                  (B, Members_End (B, P + Head_Len (B (P)), 2 * J - 4, D - 1),
                      Members_End (B, P + Head_Len (B (P)), 2 * J - 3, D - 1),
                   B, Members_End (B, P + Head_Len (B (P)), 2 * J - 2, D - 1),
                      Members_End (B, P + Head_Len (B (P)), 2 * J - 1, D - 1)),
        Post => Det_End (B, P, D) = 0;

   ---------------------------------------------------------------------
   --  Runs of members.
   ---------------------------------------------------------------------

   --  Member K of an accepted run takes at least one byte (from
   --  Lemma_Members_Last).
   procedure Client_Member_Takes_A_Byte
     (B : Bytes; Q : Positive; K : Positive; D : Natural)
   with Pre  => Q in B'First .. B'Last + 1
                and then Members_End (B, Q, K, D) /= 0,
        Post => Members_End (B, Q, K - 1, D) in B'First .. B'Last
                and then Members_End (B, Q, K, D)
                         >= Members_End (B, Q, K - 1, D) + 1;

   --  The first I members of an accepted run of K are accepted and end
   --  within it (from Lemma_Members_Prefix).
   procedure Client_Run_Prefix
     (B : Bytes; Q : Positive; I : Natural; K : Natural; D : Natural)
   with Pre  => Q in B'First .. B'Last + 1 and then I <= K
                and then Members_End (B, Q, K, D) /= 0,
        Post => Members_End (B, Q, I, D) in Q .. Members_End (B, Q, K, D);

   --  In an accepted run of K members, member J ends at least J bytes
   --  after the run starts and no later than the run ends (from
   --  Lemma_Members_Monotone).
   procedure Client_Run_Bounds
     (B : Bytes; Q : Positive; K : Natural; D : Natural)
   with Pre  => Q in B'First .. B'Last + 1
                and then Members_End (B, Q, K, D) /= 0,
        Post => (for all J in 0 .. K =>
                   Members_End (B, Q, J, D) /= 0
                   and then Members_End (B, Q, J, D) - Q >= J
                   and then Members_End (B, Q, J, D)
                            <= Members_End (B, Q, K, D))
                and then
                  (for all J in 1 .. K =>
                     Members_End (B, Q, J - 1, D) < Members_End (B, Q, J, D));

   ---------------------------------------------------------------------
   --  Key order.
   ---------------------------------------------------------------------

   --  The order is strict: no slice is less than itself (from
   --  Lemma_Lex_Step), so ascending keys are unique.
   procedure Client_Lex_Irreflexive (B : Bytes; P : Natural; E : Natural)
   with Pre  => Slice_OK (B, P, E),
        Post => not Lex_Less (B, P, E, B, P, E),
        Subprogram_Variant => (Decreases => E - P);

   --  Two non-empty slices whose first bytes differ are ordered by those
   --  bytes; an empty slice is less than exactly the non-empty ones (from
   --  Lemma_Lex_Step).
   procedure Client_Lex_First_Byte
     (B1 : Bytes; P1 : Natural; E1 : Natural;
      B2 : Bytes; P2 : Natural; E2 : Natural)
   with Pre  => Slice_OK (B1, P1, E1) and then Slice_OK (B2, P2, E2),
        Post => (if P1 = E1 then Lex_Less (B1, P1, E1, B2, P2, E2) = (P2 < E2))
                and then
                  (if P1 < E1 and then P2 < E2 and then B1 (P1) /= B2 (P2)
                   then Lex_Less (B1, P1, E1, B2, P2, E2)
                        = (B1 (P1) < B2 (P2)));

   --  The order is False on bounds that are not a slice, such as the
   --  bounds of a member that was not accepted (from Lemma_Lex_Not_Slice).
   procedure Client_Lex_Not_A_Slice
     (B : Bytes; P : Natural; E : Natural; Q : Natural; F : Natural)
   with Pre  => P > E,
        Post => not Lex_Less (B, P, E, B, Q, F)
                and then not Lex_Less (B, Q, F, B, P, E);

   ---------------------------------------------------------------------
   --  Equal slices.
   ---------------------------------------------------------------------

   --  A copy of a copy is a copy, either way round, and has the same
   --  length (from Lemma_Same_Bytes_Sym, _Trans and _Len).
   procedure Client_Same_Bytes_Copies
     (B1 : Bytes; P1 : Natural; E1 : Natural;
      B2 : Bytes; P2 : Natural; E2 : Natural;
      B3 : Bytes; P3 : Natural; E3 : Natural)
   with Pre  => Slice_OK (B1, P1, E1) and then Slice_OK (B2, P2, E2)
                and then Slice_OK (B3, P3, E3)
                and then Same_Bytes (B1, P1, E1, B2, P2, E2)
                and then Same_Bytes (B3, P3, E3, B2, P2, E2),
        Post => Same_Bytes (B1, P1, E1, B3, P3, E3)
                and then Same_Bytes (B3, P3, E3, B1, P1, E1)
                and then E1 - P1 = E3 - P3;

   --  A slice is a copy of itself, and two copied halves end to end are a
   --  copy of the whole (from Lemma_Same_Bytes_Refl and _Join).
   procedure Client_Same_Bytes_Whole
     (B1 : Bytes; P1 : Natural; M1 : Natural; E1 : Natural;
      B2 : Bytes; P2 : Natural; M2 : Natural; E2 : Natural)
   with Pre  => Slice_OK (B1, P1, M1) and then Slice_OK (B1, M1, E1)
                and then Slice_OK (B2, P2, M2) and then Slice_OK (B2, M2, E2)
                and then Same_Bytes (B1, P1, M1, B2, P2, M2)
                and then Same_Bytes (B1, M1, E1, B2, M2, E2),
        Post => Same_Bytes (B1, P1, E1, B1, P1, E1)
                and then Same_Bytes (B1, P1, E1, B2, P2, E2);

   ---------------------------------------------------------------------
   --  Prefix-freedom.
   ---------------------------------------------------------------------

   --  Two accepted items, the second starting with the bytes of the
   --  first, have the same length: neither is a proper prefix of the
   --  other (from Lemma_Prefix_Free).
   procedure Client_Prefix_Free_Equal_Length
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Natural)
   with Pre  => P1 in B1'Range and then P2 in B2'Range
                and then Det_End (B1, P1, D) /= 0
                and then Det_End (B2, P2, D) /= 0
                and then Det_End (B2, P2, D) - P2 >= Det_End (B1, P1, D) - P1
                and then Same_Bytes
                  (B1, P1, Det_End (B1, P1, D),
                   B2, P2, P2 + (Det_End (B1, P1, D) - P1)),
        Post => Det_End (B2, P2, D) - P2 = Det_End (B1, P1, D) - P1;

   ---------------------------------------------------------------------
   --  More heads.
   ---------------------------------------------------------------------

   --  The bytes of an accepted head are those Encode_Head writes for its
   --  major type and argument, and its length is that of the shortest
   --  head (from Lemma_Head_Canonical).
   procedure Client_Head_Canonical_Bytes (B : Bytes; P : Positive; K : Natural)
   with Pre  => P in B'Range and then Head_OK (B, P)
                and then K < Head_Len (B (P)),
        Post => Head_Len (B (P)) = Len_Of_Arg (Arg (B, P))
                and then B (P + K)
                         = Encode_Head (Major_Of (B (P)), Arg (B, P)) (1 + K);

   --  A head copied byte for byte has the same fit, length, major type,
   --  argument and acceptance (from Lemma_Head_Same).
   procedure Client_Head_Copy
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive)
   with Pre  => P1 in B1'Range and then Head_Fits (B1, P1)
                and then P2 in B2'Range
                and then Remaining (B2, P2) >= Head_Len (B1 (P1))
                and then (for all K in 0 .. Head_Len (B1 (P1)) - 1 =>
                            B2 (P2 + K) = B1 (P1 + K)),
        Post => Head_Fits (B2, P2)
                and then Head_Len (B2 (P2)) = Head_Len (B1 (P1))
                and then Major_Of (B2 (P2)) = Major_Of (B1 (P1))
                and then Arg (B2, P2) = Arg (B1, P1)
                and then Head_OK (B2, P2) = Head_OK (B1, P1);

   --  What Encode_Head writes for an integer is one accepted item, of
   --  exactly its own bytes, with the major type and argument asked for
   --  (from Encode_Head's postcondition and Lemma_Det_Step).
   procedure Client_Encode_Integer (M : Major; A : U64; D : Natural)
   with Pre  => M in 0 | 1,
        Post => Encode_Head (M, A)'First = 1
                and then Encode_Head (M, A)'Length = Len_Of_Arg (A)
                and then Det_End (Encode_Head (M, A), 1, D)
                         = Len_Of_Arg (A) + 1
                and then Major_Of (Encode_Head (M, A) (1)) = M
                and then Arg (Encode_Head (M, A), 1) = A;

   ---------------------------------------------------------------------
   --  Arguments as counts.
   ---------------------------------------------------------------------

   --  An argument equal to a Natural N fits a Natural; an argument known
   --  to fit one does; and two equal arguments fit together (from
   --  Lemma_Arg_Is, Lemma_Arg_Small_Of and Lemma_Arg_Same, with Arg_Small
   --  hidden).
   procedure Client_Arg_Counts
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; N : Natural)
   with Pre  => P1 in B1'Range and then Head_Fits (B1, P1)
                and then P2 in B2'Range and then Head_Fits (B2, P2)
                and then Arg (B1, P1) = U64 (N)
                and then Arg (B2, P2) = Arg (B1, P1),
        Post => Arg_Small (B1, P1) and then Arg_Small (B2, P2);

   procedure Client_Arg_Small (B : Bytes; P : Positive)
   with Pre  => P in B'Range and then Head_Fits (B, P)
                and then Arg (B, P) <= U64 (Natural'Last),
        Post => Arg_Small (B, P);

   ---------------------------------------------------------------------
   --  The shape of an accepted item, and runs of members.
   ---------------------------------------------------------------------

   --  What an accepted item is, from Det_End's postcondition alone.
   procedure Client_Accepted_Item (B : Bytes; P : Positive; D : Natural)
   with Pre  => P in B'Range and then Det_End (B, P, D) /= 0,
        Post => Det_End (B, P, D) in P + 1 .. B'Last + 1
                and then Head_OK (B, P)
                and then Major_Of (B (P)) in 0 .. 5 | 7
                and then (if Major_Of (B (P)) in 0 | 1
                          then Det_End (B, P, D) = P + Head_Len (B (P)))
                and then
                  (if Major_Of (B (P)) in 2 | 3
                   then Det_End (B, P, D)
                        = P + Head_Len (B (P)) + Arg_Nat (B, P))
                and then (if Major_Of (B (P)) in 4 | 5 then D >= 1)
                and then
                  (if Major_Of (B (P)) = 5
                   then Arg_Nat (B, P)
                        <= (Remaining (B, P) - Head_Len (B (P))) / 2)
                and then
                  (if Major_Of (B (P)) = 4
                   then Arg_Nat (B, P)
                        <= Remaining (B, P) - Head_Len (B (P)))
                and then
                  (if Major_Of (B (P)) = 7
                   then Info_Of (B (P)) in 20 .. 22
                        and then Det_End (B, P, D) = P + 1);

   --  A run of members ends within the buffer, or is refused (from
   --  Members_End's postcondition); a run of no members ends where it
   --  starts (Lemma_Members_Start); and one more member ends where the one
   --  item at the end of the run ends (Lemma_Members_Step).
   procedure Client_Run_Steps
     (B : Bytes; Q : Positive; K : Positive; D : Natural)
   with Pre  => Q in B'First .. B'Last + 1,
        Post => Members_End (B, Q, 0, D) = Q
                and then (Members_End (B, Q, K, D) = 0
                          or else Members_End (B, Q, K, D)
                                  in Q .. B'Last + 1)
                and then
                  (if Members_End (B, Q, K - 1, D) in B'First .. B'Last
                   then Members_End (B, Q, K, D)
                        = Det_End (B, Members_End (B, Q, K - 1, D), D));

   ---------------------------------------------------------------------
   --  More key order.
   ---------------------------------------------------------------------

   --  The order rule, one key at a time, both ways: N ascending keys are
   --  N - 1 ascending keys and one more greater than the last, and the
   --  first M of them are ascending (from Lemma_Keys_Step,
   --  Lemma_Keys_Extend and Lemma_Keys_Prefix).
   procedure Client_Keys_One_At_A_Time
     (B : Bytes; Q : Positive; N : Positive; M : Natural; D : Natural)
   with Pre  => Q in B'First .. B'Last + 1 and then N in 2 .. 2**30 - 1
                and then M <= N,
        Post => (if Keys_Ascending (B, Q, N, D)
                 then Keys_Ascending (B, Q, N - 1, D)
                      and then Keys_Ascending (B, Q, M, D)
                      and then Lex_Less (B, Members_End (B, Q, 2 * N - 4, D),
                                            Members_End (B, Q, 2 * N - 3, D),
                                         B, Members_End (B, Q, 2 * N - 2, D),
                                            Members_End (B, Q, 2 * N - 1, D)))
                and then
                  (if Keys_Ascending (B, Q, N - 1, D)
                      and then Lex_Less
                        (B, Members_End (B, Q, 2 * N - 4, D),
                            Members_End (B, Q, 2 * N - 3, D),
                         B, Members_End (B, Q, 2 * N - 2, D),
                            Members_End (B, Q, 2 * N - 1, D))
                   then Keys_Ascending (B, Q, N, D));

   --  N - 1 ascending keys and one more greater than the last are N
   --  ascending keys (from Lemma_Keys_Extend alone).
   procedure Client_Keys_Extend
     (B : Bytes; Q : Positive; N : Positive; D : Natural)
   with Pre  => Q in B'First .. B'Last + 1 and then N in 2 .. 2**30 - 1
                and then Keys_Ascending (B, Q, N - 1, D)
                and then Lex_Less (B, Members_End (B, Q, 2 * N - 4, D),
                                      Members_End (B, Q, 2 * N - 3, D),
                                   B, Members_End (B, Q, 2 * N - 2, D),
                                      Members_End (B, Q, 2 * N - 1, D)),
        Post => Keys_Ascending (B, Q, N, D);

   --  The order of two slices is that of their copies (from
   --  Lemma_Lex_Less_Same).
   procedure Client_Lex_Copies
     (A1 : Bytes; P1 : Natural; E1 : Natural;
      A2 : Bytes; P2 : Natural; E2 : Natural;
      C1 : Bytes; R1 : Natural; F1 : Natural;
      C2 : Bytes; R2 : Natural; F2 : Natural)
   with Pre  => Slice_OK (A1, P1, E1) and then Slice_OK (A2, P2, E2)
                and then Slice_OK (C1, R1, F1) and then Slice_OK (C2, R2, F2)
                and then Same_Bytes (A1, P1, E1, C1, R1, F1)
                and then Same_Bytes (A2, P2, E2, C2, R2, F2)
                and then Lex_Less (A1, P1, E1, A2, P2, E2),
        Post => Lex_Less (C1, R1, F1, C2, R2, F2);

   ---------------------------------------------------------------------
   --  Transport.
   ---------------------------------------------------------------------

   --  An accepted item copied anywhere is accepted there and has the same
   --  length (from Lemma_Transport).
   procedure Client_Item_Copy
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Natural)
   with Pre  => P1 in B1'Range and then P2 in B2'Range
                and then Det_End (B1, P1, D) /= 0
                and then Det_End (B1, P1, D) - P1 <= B2'Last + 1 - P2
                and then Same_Bytes
                  (B1, P1, Det_End (B1, P1, D),
                   B2, P2, P2 + (Det_End (B1, P1, D) - P1)),
        Post => Det_End (B2, P2, D) /= 0
                and then Det_End (B2, P2, D) - P2 = Det_End (B1, P1, D) - P1;

   --  An accepted run of members copied anywhere is accepted there, each
   --  member at the corresponding place (from Lemma_Members_Transport).
   procedure Client_Run_Copy
     (B1 : Bytes; Q1 : Positive; B2 : Bytes; Q2 : Positive;
      K : Natural; J : Natural; D : Natural)
   with Pre  => Q1 in B1'First .. B1'Last + 1
                and then Q2 in B2'First .. B2'Last + 1
                and then J <= K
                and then Members_End (B1, Q1, K, D) /= 0
                and then Members_End (B1, Q1, K, D) - Q1 <= B2'Last + 1 - Q2
                and then Same_Bytes
                  (B1, Q1, Members_End (B1, Q1, K, D),
                   B2, Q2, Q2 + (Members_End (B1, Q1, K, D) - Q1)),
        Post => Members_End (B1, Q1, J, D) /= 0
                and then Members_End (B2, Q2, J, D) - Q2
                         = Members_End (B1, Q1, J, D) - Q1;

end Cbor_Det.Proof.Surface;
