--  Deterministic CBOR: canonical uniqueness.
--
--  Copyright (c) 2026, Matt Doughty
--  SPDX-License-Identifier: BSD-3-Clause
--
--  Lemma_CU_Whole: two inputs, each accepted whole, that denote the same
--  value (Same, in Cbor_Det.Proof.Model) are the same bytes. So a value
--  has at most one accepted encoding.
--
--  The proof is by induction on the depth, in Lemma_CU, for an accepted
--  item at any place in any buffer. A scalar or a string is its head and
--  its bytes, and the head is unique (Lemma_Head_Unique). An array is its
--  head and its members in order, each unique by induction. A map needs
--  more, because Same compares its pairs as a set, in no order:
--
--    1. the order on keys is strict and transitive (Lemma_Lex_Irrefl,
--       Lemma_Lex_Trans), so the order of each key with the next, which
--       is what acceptance checks, gives the order of each key with every
--       later key (Lemma_Keys_Strict), and no two keys of one map are the
--       same bytes (Lemma_Keys_Distinct);
--    2. two maps that denote the same value have, by induction on their
--       keys, the same set of keys as bytes (Lemma_Map_Match);
--    3. two accepted maps with the same set of keys have the same keys in
--       the same order, because both orders are strict (Lemma_Map_Keys);
--       conversely, keys the same in order are the same set
--       (Lemma_Keys_Match_In_Order);
--    4. with the keys the same in order, the value under each key is,
--       by induction, the same bytes (Lemma_Map_Values);
--    5. a head and pairs that are the same bytes end to end make the
--       same map (Lemma_Map_Concat).
--
--  The converse, Lemma_Same_Of_Bytes and Lemma_Same_Of_Bytes_Whole: two
--  accepted items that are the same bytes, at any places, denote the same
--  value. Their members end at corresponding places (by transport), so
--  member I of one is the same bytes as member I of the other, and the
--  same value by induction; for a map, pair I matches pair I. So on
--  inputs accepted whole, Same is exactly byte equality
--  (Lemma_Same_Iff_Bytes_Whole).

with Cbor_Det.Proof.Heads; use Cbor_Det.Proof.Heads;
with Cbor_Det.Proof.Det;   use Cbor_Det.Proof.Det;
with Cbor_Det.Proof.Model; use Cbor_Det.Proof.Model;

package Cbor_Det.Proof.Unique with SPARK_Mode, Ghost is

   use type Interfaces.Unsigned_64;

   ---------------------------------------------------------------------
   --  The order is strict and transitive.
   ---------------------------------------------------------------------

   --  No slice is less than a slice of the same bytes.
   procedure Lemma_Lex_Irrefl
     (B1 : Bytes; P1 : Natural; E1 : Natural;
      B2 : Bytes; P2 : Natural; E2 : Natural)
   with Pre  => Slice_OK (B1, P1, E1) and then Slice_OK (B2, P2, E2)
                and then Same_Bytes (B1, P1, E1, B2, P2, E2),
        Post => not Lex_Less (B1, P1, E1, B2, P2, E2),
        Subprogram_Variant => (Decreases => E1 - P1);

   procedure Lemma_Lex_Trans
     (A : Bytes; PA : Natural; EA : Natural;
      B : Bytes; PB : Natural; EB : Natural;
      C : Bytes; PC : Natural; EC : Natural)
   with Pre  => Slice_OK (A, PA, EA) and then Slice_OK (B, PB, EB)
                and then Slice_OK (C, PC, EC)
                and then Lex_Less (A, PA, EA, B, PB, EB)
                and then Lex_Less (B, PB, EB, C, PC, EC),
        Post => Lex_Less (A, PA, EA, C, PC, EC),
        Subprogram_Variant => (Decreases => EA - PA);

   ---------------------------------------------------------------------
   --  From adjacent keys to all pairs of keys.
   ---------------------------------------------------------------------

   --  Each of the first I keys of the map at P is less than every later
   --  key. Hidden; built one key at a time, opened one pair at a time.
   function Keys_Strict_Upto
     (B : Bytes; P : Positive; D : Positive; I : Natural) return Boolean
   is (for all Y in 1 .. I =>
         (for all X in Y + 1 .. Pairs (B, P) =>
            Lex_Less (B, Key_S (B, P, Y, D), Key_E (B, P, Y, D),
                      B, Key_S (B, P, X, D), Key_E (B, P, X, D))))
   with Pre => Is_Map (B, P, D) and then I <= Pairs (B, P);
   pragma Annotate
     (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Strict_Upto);

   procedure Lemma_Strict_Zero (B : Bytes; P : Positive; D : Positive)
   with Pre  => Is_Map (B, P, D),
        Post => Keys_Strict_Upto (B, P, D, 0);

   procedure Lemma_Strict_Extend
     (B : Bytes; P : Positive; D : Positive; I : Positive)
   with Pre  => Is_Map (B, P, D) and then I <= Pairs (B, P)
                and then Keys_Strict_Upto (B, P, D, I - 1)
                and then (for all X in I + 1 .. Pairs (B, P) =>
                            Lex_Less (B, Key_S (B, P, I, D),
                                         Key_E (B, P, I, D),
                                      B, Key_S (B, P, X, D),
                                         Key_E (B, P, X, D))),
        Post => Keys_Strict_Upto (B, P, D, I);

   procedure Lemma_Strict_At
     (B : Bytes; P : Positive; D : Positive; I : Positive; J : Positive)
   with Pre  => Is_Map (B, P, D) and then I < J and then J <= Pairs (B, P)
                and then Keys_Strict_Upto (B, P, D, Pairs (B, P)),
        Post => Lex_Less (B, Key_S (B, P, I, D), Key_E (B, P, I, D),
                          B, Key_S (B, P, J, D), Key_E (B, P, J, D));

   --  Every key of an accepted map is less than every later key.
   procedure Lemma_Keys_Strict (B : Bytes; P : Positive; D : Positive)
   with Pre  => Is_Map (B, P, D),
        Post => Keys_Strict_Upto (B, P, D, Pairs (B, P));

   --  No two keys of an accepted map are the same bytes.
   procedure Lemma_Keys_Distinct
     (B : Bytes; P : Positive; I : Positive; J : Positive; D : Positive)
   with Pre  => Is_Map (B, P, D) and then I <= Pairs (B, P)
                and then J <= Pairs (B, P) and then I /= J,
        Post => not Same_Bytes (B, Key_S (B, P, I, D), Key_E (B, P, I, D),
                                B, Key_S (B, P, J, D), Key_E (B, P, J, D));

   ---------------------------------------------------------------------
   --  The keys of two maps as sets of byte strings.
   ---------------------------------------------------------------------

   --  Each of the first I keys of the map at P1 is the same bytes as some
   --  key of the map at P2. Hidden; built one key at a time, opened one
   --  key at a time.
   function Match_Fwd
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive;
      I : Natural) return Boolean
   is (for all Y in 1 .. I =>
         (for some J in 1 .. Pairs (B1, P1) =>
            Same_Bytes (B1, Key_S (B1, P1, Y, D), Key_E (B1, P1, Y, D),
                        B2, Key_S (B2, P2, J, D), Key_E (B2, P2, J, D))))
   with Pre => Is_Map (B1, P1, D) and then Is_Map (B2, P2, D)
               and then Pairs (B1, P1) = Pairs (B2, P2)
               and then I <= Pairs (B1, P1);
   pragma Annotate
     (GNATprove, Hide_Info, "Expression_Function_Body", Match_Fwd);

   --  The two maps have the same number of pairs and the same set of keys
   --  as byte strings: every key of each is the same bytes as a key of
   --  the other. The second direction is the first with the maps swapped.
   function Keys_Match
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive)
      return Boolean
   is (Pairs (B1, P1) = Pairs (B2, P2)
       and then Match_Fwd (B1, P1, B2, P2, D, Pairs (B1, P1))
       and then Match_Fwd (B2, P2, B1, P1, D, Pairs (B2, P2)))
   with Pre => Is_Map (B1, P1, D) and then Is_Map (B2, P2, D);

   procedure Lemma_Match_Zero
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive)
   with Pre  => Is_Map (B1, P1, D) and then Is_Map (B2, P2, D)
                and then Pairs (B1, P1) = Pairs (B2, P2),
        Post => Match_Fwd (B1, P1, B2, P2, D, 0);

   procedure Lemma_Match_Fwd_Extend
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive;
      I : Positive; J : Positive)
   with Pre  => Is_Map (B1, P1, D) and then Is_Map (B2, P2, D)
                and then Pairs (B1, P1) = Pairs (B2, P2)
                and then I <= Pairs (B1, P1) and then J <= Pairs (B1, P1)
                and then Match_Fwd (B1, P1, B2, P2, D, I - 1)
                and then Same_Bytes
                  (B1, Key_S (B1, P1, I, D), Key_E (B1, P1, I, D),
                   B2, Key_S (B2, P2, J, D), Key_E (B2, P2, J, D)),
        Post => Match_Fwd (B1, P1, B2, P2, D, I);

   procedure Lemma_Match_Fwd_At
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive;
      I : Positive)
   with Pre  => Is_Map (B1, P1, D) and then Is_Map (B2, P2, D)
                and then Pairs (B1, P1) = Pairs (B2, P2)
                and then I <= Pairs (B1, P1)
                and then Match_Fwd (B1, P1, B2, P2, D, Pairs (B1, P1)),
        Post => (for some J in 1 .. Pairs (B1, P1) =>
                   Same_Bytes
                     (B1, Key_S (B1, P1, I, D), Key_E (B1, P1, I, D),
                      B2, Key_S (B2, P2, J, D), Key_E (B2, P2, J, D)));

   --  A key of the map at P2 that is the same bytes as key I of the map
   --  at P1, found by search.
   function Find_Key
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive;
      I : Positive) return Positive
   with Pre  => Is_Map (B1, P1, D) and then Is_Map (B2, P2, D)
                and then Pairs (B1, P1) = Pairs (B2, P2)
                and then I <= Pairs (B1, P1)
                and then Match_Fwd (B1, P1, B2, P2, D, Pairs (B1, P1)),
        Post => Find_Key'Result <= Pairs (B1, P1)
                and then Same_Bytes
                  (B1, Key_S (B1, P1, I, D), Key_E (B1, P1, I, D),
                   B2, Key_S (B2, P2, Find_Key'Result, D),
                       Key_E (B2, P2, Find_Key'Result, D));

   --  One step of Lemma_Map_Keys: if the first I - 1 keys of two accepted
   --  maps are the same bytes in order, key I of the first is the same
   --  bytes as key J of the second, and key I of the second the same bytes
   --  as key M of the first, then key I of each is the same bytes: J or M
   --  out of place would put a key below itself.
   procedure Lemma_Key_In_Place
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive;
      I : Positive; J : Positive; M : Positive)
   with Pre  => Is_Map (B1, P1, D) and then Is_Map (B2, P2, D)
                and then Pairs (B1, P1) = Pairs (B2, P2)
                and then I <= Pairs (B1, P1) and then J <= Pairs (B1, P1)
                and then M <= Pairs (B1, P1)
                and then Keys_Strict_Upto (B1, P1, D, Pairs (B1, P1))
                and then Keys_Strict_Upto (B2, P2, D, Pairs (B2, P2))
                and then
                  (for all Y in 1 .. I - 1 =>
                     Same_Bytes
                       (B1, Key_S (B1, P1, Y, D), Key_E (B1, P1, Y, D),
                        B2, Key_S (B2, P2, Y, D), Key_E (B2, P2, Y, D)))
                and then Same_Bytes
                  (B1, Key_S (B1, P1, I, D), Key_E (B1, P1, I, D),
                   B2, Key_S (B2, P2, J, D), Key_E (B2, P2, J, D))
                and then Same_Bytes
                  (B2, Key_S (B2, P2, I, D), Key_E (B2, P2, I, D),
                   B1, Key_S (B1, P1, M, D), Key_E (B1, P1, M, D)),
        Post => Same_Bytes
                  (B1, Key_S (B1, P1, I, D), Key_E (B1, P1, I, D),
                   B2, Key_S (B2, P2, I, D), Key_E (B2, P2, I, D));

   --  Two accepted maps with the same set of keys have the same keys in
   --  the same order: key I of one is the same bytes as key I of the
   --  other. Both maps' keys are strictly ascending, so a key out of
   --  place would be less than itself.
   procedure Lemma_Map_Keys
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive)
   with Pre  => Is_Map (B1, P1, D) and then Is_Map (B2, P2, D)
                and then Keys_Match (B1, P1, B2, P2, D),
        Post => (for all I in 1 .. Pairs (B1, P1) =>
                   Same_Bytes
                     (B1, Key_S (B1, P1, I, D), Key_E (B1, P1, I, D),
                      B2, Key_S (B2, P2, I, D), Key_E (B2, P2, I, D)));

   --  The converse: two maps whose keys are the same bytes in order have
   --  the same set of keys.
   procedure Lemma_Keys_Match_In_Order
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive)
   with Pre  => Is_Map (B1, P1, D) and then Is_Map (B2, P2, D)
                and then Pairs (B1, P1) = Pairs (B2, P2)
                and then
                  (for all I in 1 .. Pairs (B1, P1) =>
                     Same_Bytes
                       (B1, Key_S (B1, P1, I, D), Key_E (B1, P1, I, D),
                        B2, Key_S (B2, P2, I, D), Key_E (B2, P2, I, D))),
        Post => Keys_Match (B1, P1, B2, P2, D);

   ---------------------------------------------------------------------
   --  The map case of Lemma_CU, in steps. Lemma_Map_Match and
   --  Lemma_Map_Values apply Lemma_CU to the members, one level down.
   ---------------------------------------------------------------------

   --  A pair of the map at P2 whose key and value are the same as those
   --  of pair I of the map at P1, found by search in the map clause.
   function Find_Pair
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive;
      I : Positive) return Positive
   with Pre  => Is_Map (B1, P1, D) and then Is_Map (B2, P2, D)
                and then Pairs (B1, P1) = Pairs (B2, P2)
                and then Same_Map_Clause (B1, P1, B2, P2, D)
                and then I <= Pairs (B1, P1),
        Post => Find_Pair'Result <= Pairs (B1, P1)
                and then Same (B1, Key_S (B1, P1, I, D),
                               B2, Key_S (B2, P2, Find_Pair'Result, D),
                               D - 1)
                and then Same (B1, Key_E (B1, P1, I, D),
                               B2, Key_E (B2, P2, Find_Pair'Result, D),
                               D - 1);

   --  The same, the other way: a pair of the map at P1 whose key and value
   --  are the same as those of pair J of the map at P2.
   function Find_Pair_Back
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive;
      J : Positive) return Positive
   with Pre  => Is_Map (B1, P1, D) and then Is_Map (B2, P2, D)
                and then Pairs (B1, P1) = Pairs (B2, P2)
                and then Same_Map_Clause (B1, P1, B2, P2, D)
                and then J <= Pairs (B1, P1),
        Post => Find_Pair_Back'Result <= Pairs (B1, P1)
                and then Same (B1, Key_S (B1, P1, Find_Pair_Back'Result, D),
                               B2, Key_S (B2, P2, J, D), D - 1)
                and then Same (B1, Key_E (B1, P1, Find_Pair_Back'Result, D),
                               B2, Key_E (B2, P2, J, D), D - 1);

   --  Two maps that denote the same value have the same set of keys.
   procedure Lemma_Map_Match
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive)
   with Pre  => Is_Map (B1, P1, D) and then Is_Map (B2, P2, D)
                and then Same (B1, P1, B2, P2, D),
        Post => Keys_Match (B1, P1, B2, P2, D),
        Subprogram_Variant => (Decreases => D, Decreases => Natural'(0));

   --  Of two maps that denote the same value, with the same keys in
   --  order, the value of pair I of one is the same bytes as the value of
   --  pair I of the other.
   procedure Lemma_Map_Values
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive)
   with Pre  => Is_Map (B1, P1, D) and then Is_Map (B2, P2, D)
                and then Same (B1, P1, B2, P2, D)
                and then Pairs (B1, P1) = Pairs (B2, P2)
                and then
                  (for all I in 1 .. Pairs (B1, P1) =>
                     Same_Bytes
                       (B1, Key_S (B1, P1, I, D), Key_E (B1, P1, I, D),
                        B2, Key_S (B2, P2, I, D), Key_E (B2, P2, I, D))),
        Post => (for all I in 1 .. Pairs (B1, P1) =>
                   Same_Bytes
                     (B1, Key_E (B1, P1, I, D), Val_E (B1, P1, I, D),
                      B2, Key_E (B2, P2, I, D), Val_E (B2, P2, I, D))),
        Subprogram_Variant => (Decreases => D, Decreases => Natural'(0));

   --  Two maps with the same head and, pair by pair, the same keys and
   --  values are the same bytes.
   procedure Lemma_Map_Concat
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive)
   with Pre  => Is_Map (B1, P1, D) and then Is_Map (B2, P2, D)
                and then Pairs (B1, P1) = Pairs (B2, P2)
                and then Head_Len (B1 (P1)) = Head_Len (B2 (P2))
                and then Same_Bytes (B1, P1, P1 + Head_Len (B1 (P1)),
                                     B2, P2, P2 + Head_Len (B2 (P2)))
                and then
                  (for all I in 1 .. Pairs (B1, P1) =>
                     Same_Bytes
                       (B1, Key_S (B1, P1, I, D), Key_E (B1, P1, I, D),
                        B2, Key_S (B2, P2, I, D), Key_E (B2, P2, I, D))
                     and then Same_Bytes
                       (B1, Key_E (B1, P1, I, D), Val_E (B1, P1, I, D),
                        B2, Key_E (B2, P2, I, D), Val_E (B2, P2, I, D))),
        Post => Det_End (B1, P1, D) - P1 = Det_End (B2, P2, D) - P2
                and then Same_Bytes (B1, P1, Det_End (B1, P1, D),
                                     B2, P2, Det_End (B2, P2, D));

   ---------------------------------------------------------------------
   --  Canonical uniqueness.
   ---------------------------------------------------------------------

   --  Two accepted items, at any place in any buffers, judged at the same
   --  depth, that denote the same value are the same bytes.
   procedure Lemma_CU
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Natural)
   with Pre  => P1 in B1'Range and then P2 in B2'Range
                and then Det_End (B1, P1, D) /= 0
                and then Det_End (B2, P2, D) /= 0
                and then Same (B1, P1, B2, P2, D),
        Post => Det_End (B1, P1, D) - P1 = Det_End (B2, P2, D) - P2
                and then Same_Bytes (B1, P1, Det_End (B1, P1, D),
                                     B2, P2, Det_End (B2, P2, D)),
        Subprogram_Variant => (Decreases => D, Decreases => Natural'(1));

   --  Two inputs, with any bounds, each accepted whole, that denote the
   --  same value are the same bytes: the same length, and byte K of one
   --  is byte K of the other.
   procedure Lemma_CU_Whole (B1 : Bytes; B2 : Bytes)
   with Pre  => Accept_Whole (B1) and then Accept_Whole (B2)
                and then Same (B1, B1'First, B2, B2'First, Max_Depth),
        Post => B1'Length = B2'Length
                and then (for all K in B1'Range =>
                            B1 (K) = B2 (K - B1'First + B2'First))
                and then Same_Bytes (B1, B1'First, B1'Last + 1,
                                     B2, B2'First, B2'Last + 1);

   ---------------------------------------------------------------------
   --  The converse: the same bytes denote the same value.
   ---------------------------------------------------------------------

   --  A head copied byte for byte, inside an item copied byte for byte,
   --  is the same head: the same initial byte, length, major type and
   --  argument.
   procedure Lemma_Head_Rebased
     (B1 : Bytes; P1 : Positive; E1 : Natural;
      B2 : Bytes; P2 : Positive; E2 : Natural)
   with Pre  => P1 in B1'Range and then P2 in B2'Range
                and then Head_Fits (B1, P1)
                and then E1 in P1 + Head_Len (B1 (P1)) .. B1'Last + 1
                and then E2 - P2 = E1 - P1
                and then Same_Bytes (B1, P1, E1, B2, P2, E2),
        Post => Head_Fits (B2, P2)
                and then B2 (P2) = B1 (P1)
                and then Head_Len (B2 (P2)) = Head_Len (B1 (P1))
                and then Major_Of (B2 (P2)) = Major_Of (B1 (P1))
                and then Arg (B2, P2) = Arg (B1, P1)
                and then Head_OK (B2, P2) = Head_OK (B1, P1);

   --  The members of a container copied byte for byte, both accepted,
   --  end at the corresponding places.
   procedure Lemma_Members_Rebased
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive)
   with Pre  => P1 in B1'Range and then P2 in B2'Range
                and then Det_End (B1, P1, D) /= 0
                and then Det_End (B2, P2, D) /= 0
                and then Det_End (B1, P1, D) - P1 = Det_End (B2, P2, D) - P2
                and then Same_Bytes (B1, P1, Det_End (B1, P1, D),
                                     B2, P2, Det_End (B2, P2, D))
                and then Major_Of (B1 (P1)) in 4 | 5,
        Post => Major_Of (B2 (P2)) = Major_Of (B1 (P1))
                and then Head_Len (B2 (P2)) = Head_Len (B1 (P1))
                and then Arg_Nat (B2, P2) = Arg_Nat (B1, P1)
                and then
                  (for all J in 0 .. Member_Count (B1, P1) =>
                     Members_End (B2, P2 + Head_Len (B2 (P2)), J, D - 1)
                     = Members_End (B1, P1 + Head_Len (B1 (P1)), J, D - 1)
                       - P1 + P2);

   --  Two accepted items, at any place in any buffers, judged at the same
   --  depth, that are the same bytes denote the same value.
   procedure Lemma_Same_Of_Bytes
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Natural)
   with Pre  => P1 in B1'Range and then P2 in B2'Range
                and then Det_End (B1, P1, D) /= 0
                and then Det_End (B2, P2, D) /= 0
                and then Det_End (B1, P1, D) - P1 = Det_End (B2, P2, D) - P2
                and then Same_Bytes (B1, P1, Det_End (B1, P1, D),
                                     B2, P2, Det_End (B2, P2, D)),
        Post => Same (B1, P1, B2, P2, D),
        Subprogram_Variant => (Decreases => D, Decreases => Natural'(2));

   --  The array case of Lemma_Same_Of_Bytes: member I of each array.
   procedure Lemma_Child_Same_Of_Bytes
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive;
      I : Positive)
   with Pre  => P1 in B1'Range and then P2 in B2'Range
                and then Det_End (B1, P1, D) /= 0
                and then Det_End (B2, P2, D) /= 0
                and then Det_End (B1, P1, D) - P1 = Det_End (B2, P2, D) - P2
                and then Same_Bytes (B1, P1, Det_End (B1, P1, D),
                                     B2, P2, Det_End (B2, P2, D))
                and then Major_Of (B1 (P1)) = 4
                and then I <= Arg_Nat (B1, P1),
        Post => Major_Of (B2 (P2)) = 4
                and then Arg_Nat (B2, P2) = Arg_Nat (B1, P1)
                and then Same (B1, Child (B1, P1, I, D),
                               B2, Child (B2, P2, I, D), D - 1),
        Subprogram_Variant => (Decreases => D, Decreases => Natural'(0));

   --  The array case of Lemma_Same_Of_Bytes: every member.
   procedure Lemma_Array_Same_Of_Bytes
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive)
   with Pre  => P1 in B1'Range and then P2 in B2'Range
                and then Det_End (B1, P1, D) /= 0
                and then Det_End (B2, P2, D) /= 0
                and then Det_End (B1, P1, D) - P1 = Det_End (B2, P2, D) - P2
                and then Same_Bytes (B1, P1, Det_End (B1, P1, D),
                                     B2, P2, Det_End (B2, P2, D))
                and then Major_Of (B1 (P1)) = 4,
        Post => Major_Of (B2 (P2)) = 4
                and then Arg_Nat (B2, P2) = Arg_Nat (B1, P1)
                and then
                  (for all I in 1 .. Arg_Nat (B1, P1) =>
                     Same (B1, Child (B1, P1, I, D),
                           B2, Child (B2, P2, I, D), D - 1)),
        Subprogram_Variant => (Decreases => D, Decreases => Natural'(1));

   --  The map case of Lemma_Same_Of_Bytes: pair I of each map, key with
   --  key and value with value.
   procedure Lemma_Pair_Same_Of_Bytes
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive;
      I : Positive)
   with Pre  => Is_Map (B1, P1, D)
                and then P2 in B2'Range
                and then Det_End (B2, P2, D) /= 0
                and then Det_End (B1, P1, D) - P1 = Det_End (B2, P2, D) - P2
                and then Same_Bytes (B1, P1, Det_End (B1, P1, D),
                                     B2, P2, Det_End (B2, P2, D))
                and then I <= Pairs (B1, P1),
        Post => Is_Map (B2, P2, D)
                and then Pairs (B2, P2) = Pairs (B1, P1)
                and then Same (B1, Key_S (B1, P1, I, D),
                               B2, Key_S (B2, P2, I, D), D - 1)
                and then Same (B1, Key_E (B1, P1, I, D),
                               B2, Key_E (B2, P2, I, D), D - 1),
        Subprogram_Variant => (Decreases => D, Decreases => Natural'(0));

   --  The map case of Lemma_Same_Of_Bytes: every pair, in order.
   procedure Lemma_Map_Same_Of_Bytes
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive)
   with Pre  => Is_Map (B1, P1, D)
                and then P2 in B2'Range
                and then Det_End (B2, P2, D) /= 0
                and then Det_End (B1, P1, D) - P1 = Det_End (B2, P2, D) - P2
                and then Same_Bytes (B1, P1, Det_End (B1, P1, D),
                                     B2, P2, Det_End (B2, P2, D)),
        Post => Is_Map (B2, P2, D)
                and then Pairs (B2, P2) = Pairs (B1, P1)
                and then
                  (for all I in 1 .. Pairs (B1, P1) =>
                     Same (B1, Key_S (B1, P1, I, D),
                           B2, Key_S (B2, P2, I, D), D - 1)
                     and then Same (B1, Key_E (B1, P1, I, D),
                                    B2, Key_E (B2, P2, I, D), D - 1)),
        Subprogram_Variant => (Decreases => D, Decreases => Natural'(1));

   --  Two inputs, with any bounds, each accepted whole, of the same length
   --  and the same bytes denote the same value.
   procedure Lemma_Same_Of_Bytes_Whole (B1 : Bytes; B2 : Bytes)
   with Pre  => Accept_Whole (B1) and then Accept_Whole (B2)
                and then B1'Length = B2'Length
                and then (for all K in B1'Range =>
                            B1 (K) = B2 (K - B1'First + B2'First)),
        Post => Same (B1, B1'First, B2, B2'First, Max_Depth);

   --  Both directions at once: of two inputs accepted whole, Same holds
   --  exactly when they have the same length and the same bytes.
   procedure Lemma_Same_Iff_Bytes_Whole (B1 : Bytes; B2 : Bytes)
   with Pre  => Accept_Whole (B1) and then Accept_Whole (B2),
        Post => Same (B1, B1'First, B2, B2'First, Max_Depth)
                = (B1'Length = B2'Length
                   and then (for all K in B1'Range =>
                               B1 (K) = B2 (K - B1'First + B2'First)));

end Cbor_Det.Proof.Unique;
