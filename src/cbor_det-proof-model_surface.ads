--  Deterministic CBOR: proof clients of the value relation and of the
--  uniqueness lemmas.
--
--  Copyright (c) 2026, Matt Doughty
--  SPDX-License-Identifier: BSD-3-Clause
--
--  One client per subprogram of Cbor_Det.Proof.Model and
--  Cbor_Det.Proof.Unique that has a postcondition. A client has the
--  subprogram's parameters and precondition; it calls the subprogram (a
--  function needs no call) and asserts each conjunct of its postcondition
--  on its own, from the contract alone: each client's body hides the
--  recursive definitions (Det_End, Members_End, Keys_Ascending, Lex_Less,
--  Same and Same_Map_Clause), which are visible outside their own units.
--  So if a postcondition said less, an assertion here would no longer
--  prove, unless what it dropped follows from the rest of the contract.
--
--  Nothing here runs: the package is ghost.

with Cbor_Det.Proof.Heads;  use Cbor_Det.Proof.Heads;
with Cbor_Det.Proof.Det;    use Cbor_Det.Proof.Det;
with Cbor_Det.Proof.Model;  use Cbor_Det.Proof.Model;
with Cbor_Det.Proof.Unique; use Cbor_Det.Proof.Unique;

package Cbor_Det.Proof.Model_Surface with SPARK_Mode, Ghost is

   use type Interfaces.Unsigned_64;

   --  Model.Child: each conjunct of its postcondition.
   procedure Client_Child
     (B : Bytes; P : Positive; I : Positive; D : Positive)
   with Pre => P in B'Range
               and then Det_End (B, P, D) /= 0
               and then Major_Of (B (P)) in 4 | 5
               and then I <= Member_Count (B, P);

   --  Model.Lemma_Child_At: each conjunct of its postcondition.
   procedure Client_Lemma_Child_At
     (B : Bytes; P : Positive; I : Positive; D : Positive)
   with Pre => P in B'Range
               and then Det_End (B, P, D) /= 0
               and then Major_Of (B (P)) in 4 | 5
               and then I <= Member_Count (B, P);

   --  Model.Key_S: each conjunct of its postcondition.
   procedure Client_Key_S
     (B : Bytes; P : Positive; M : Positive; D : Positive)
   with Pre => Is_Map (B, P, D) and then M <= Pairs (B, P);

   --  Model.Key_E: each conjunct of its postcondition.
   procedure Client_Key_E
     (B : Bytes; P : Positive; M : Positive; D : Positive)
   with Pre => Is_Map (B, P, D) and then M <= Pairs (B, P);

   --  Model.Val_E: each conjunct of its postcondition.
   procedure Client_Val_E
     (B : Bytes; P : Positive; M : Positive; D : Positive)
   with Pre => Is_Map (B, P, D) and then M <= Pairs (B, P);

   --  Model.Lemma_Key_Slice: each conjunct of its postcondition.
   procedure Client_Lemma_Key_Slice
     (B : Bytes; P : Positive; M : Positive; D : Positive)
   with Pre => Is_Map (B, P, D) and then M <= Pairs (B, P);

   --  Model.Lemma_Same_Open: each conjunct of its postcondition.
   procedure Client_Lemma_Same_Open
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Natural)
   with Pre => P1 in B1'Range and then P2 in B2'Range
               and then Det_End (B1, P1, D) /= 0
               and then Det_End (B2, P2, D) /= 0
               and then Same (B1, P1, B2, P2, D);

   --  Model.Lemma_Same_Map: each conjunct of its postcondition.
   procedure Client_Lemma_Same_Map
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive)
   with Pre => Is_Map (B1, P1, D) and then P2 in B2'Range
               and then Det_End (B2, P2, D) /= 0
               and then Same (B1, P1, B2, P2, D);

   --  Model.Lemma_Same_Map_At: each conjunct of its postcondition.
   procedure Client_Lemma_Same_Map_At
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive;
      I : Positive)
   with Pre => Is_Map (B1, P1, D) and then Is_Map (B2, P2, D)
               and then Pairs (B1, P1) = Pairs (B2, P2)
               and then Same_Map_Clause (B1, P1, B2, P2, D)
               and then I <= Pairs (B1, P1);

   --  Model.Lemma_Same_Map_Back_At: each conjunct of its postcondition.
   procedure Client_Lemma_Same_Map_Back_At
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive;
      J : Positive)
   with Pre => Is_Map (B1, P1, D) and then Is_Map (B2, P2, D)
               and then Pairs (B1, P1) = Pairs (B2, P2)
               and then Same_Map_Clause (B1, P1, B2, P2, D)
               and then J <= Pairs (B1, P1);

   --  Model.Lemma_Same_Close: each conjunct of its postcondition.
   procedure Client_Lemma_Same_Close
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Natural)
   with Pre => P1 in B1'Range and then P2 in B2'Range
               and then Det_End (B1, P1, D) /= 0
               and then Det_End (B2, P2, D) /= 0
               and then Major_Of (B1 (P1)) = Major_Of (B2 (P2))
               and then (if Major_Of (B1 (P1)) in 0 | 1
                         then Arg (B1, P1) = Arg (B2, P2))
               and then
                 (if Major_Of (B1 (P1)) in 2 | 3
                  then Arg_Nat (B1, P1) = Arg_Nat (B2, P2)
                       and then Same_Bytes
                         (B1, P1 + Head_Len (B1 (P1)), Det_End (B1, P1, D),
                          B2, P2 + Head_Len (B2 (P2)), Det_End (B2, P2, D)))
               and then
                 (if Major_Of (B1 (P1)) = 4
                  then Arg_Nat (B1, P1) = Arg_Nat (B2, P2)
                       and then
                         (for all I in 1 .. Arg_Nat (B1, P1) =>
                            Same (B1, Child (B1, P1, I, D),
                                  B2, Child (B2, P2, I, D), D - 1)))
               and then
                 (if Major_Of (B1 (P1)) = 5
                  then Arg_Nat (B1, P1) = Arg_Nat (B2, P2)
                       and then Same_Map_Clause (B1, P1, B2, P2, D))
               and then (if Major_Of (B1 (P1)) = 7
                         then Info_Of (B1 (P1)) = Info_Of (B2 (P2)));

   --  Model.Lemma_Same_Map_In_Order: each conjunct of its postcondition.
   procedure Client_Lemma_Same_Map_In_Order
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive)
   with Pre => Is_Map (B1, P1, D) and then Is_Map (B2, P2, D)
               and then Pairs (B1, P1) = Pairs (B2, P2)
               and then
                 (for all I in 1 .. Pairs (B1, P1) =>
                    Same (B1, Key_S (B1, P1, I, D),
                          B2, Key_S (B2, P2, I, D), D - 1)
                    and then Same (B1, Key_E (B1, P1, I, D),
                                   B2, Key_E (B2, P2, I, D), D - 1));

   --  Model.Lemma_Same_Refl: each conjunct of its postcondition.
   procedure Client_Lemma_Same_Refl
     (B : Bytes; P : Positive; D : Natural)
   with Pre => P in B'Range and then Det_End (B, P, D) /= 0;

   --  Unique.Lemma_Lex_Irrefl: each conjunct of its postcondition.
   procedure Client_Lemma_Lex_Irrefl
     (B1 : Bytes; P1 : Natural; E1 : Natural;
      B2 : Bytes; P2 : Natural; E2 : Natural)
   with Pre => Slice_OK (B1, P1, E1) and then Slice_OK (B2, P2, E2)
               and then Same_Bytes (B1, P1, E1, B2, P2, E2);

   --  Unique.Lemma_Lex_Trans: each conjunct of its postcondition.
   procedure Client_Lemma_Lex_Trans
     (A : Bytes; PA : Natural; EA : Natural;
      B : Bytes; PB : Natural; EB : Natural;
      C : Bytes; PC : Natural; EC : Natural)
   with Pre => Slice_OK (A, PA, EA) and then Slice_OK (B, PB, EB)
               and then Slice_OK (C, PC, EC)
               and then Lex_Less (A, PA, EA, B, PB, EB)
               and then Lex_Less (B, PB, EB, C, PC, EC);

   --  Unique.Lemma_Strict_Zero: each conjunct of its postcondition.
   procedure Client_Lemma_Strict_Zero
     (B : Bytes; P : Positive; D : Positive)
   with Pre => Is_Map (B, P, D);

   --  Unique.Lemma_Strict_Extend: each conjunct of its postcondition.
   procedure Client_Lemma_Strict_Extend
     (B : Bytes; P : Positive; D : Positive; I : Positive)
   with Pre => Is_Map (B, P, D) and then I <= Pairs (B, P)
               and then Keys_Strict_Upto (B, P, D, I - 1)
               and then (for all X in I + 1 .. Pairs (B, P) =>
                           Lex_Less (B, Key_S (B, P, I, D),
                                        Key_E (B, P, I, D),
                                     B, Key_S (B, P, X, D),
                                        Key_E (B, P, X, D)));

   --  Unique.Lemma_Strict_At: each conjunct of its postcondition.
   procedure Client_Lemma_Strict_At
     (B : Bytes; P : Positive; D : Positive; I : Positive; J : Positive)
   with Pre => Is_Map (B, P, D) and then I < J and then J <= Pairs (B, P)
               and then Keys_Strict_Upto (B, P, D, Pairs (B, P));

   --  Unique.Lemma_Keys_Strict: each conjunct of its postcondition.
   procedure Client_Lemma_Keys_Strict
     (B : Bytes; P : Positive; D : Positive)
   with Pre => Is_Map (B, P, D);

   --  Unique.Lemma_Keys_Distinct: each conjunct of its postcondition.
   procedure Client_Lemma_Keys_Distinct
     (B : Bytes; P : Positive; I : Positive; J : Positive; D : Positive)
   with Pre => Is_Map (B, P, D) and then I <= Pairs (B, P)
               and then J <= Pairs (B, P) and then I /= J;

   --  Unique.Lemma_Match_Zero: each conjunct of its postcondition.
   procedure Client_Lemma_Match_Zero
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive)
   with Pre => Is_Map (B1, P1, D) and then Is_Map (B2, P2, D)
               and then Pairs (B1, P1) = Pairs (B2, P2);

   --  Unique.Lemma_Match_Fwd_Extend: each conjunct of its postcondition.
   procedure Client_Lemma_Match_Fwd_Extend
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive;
      I : Positive; J : Positive)
   with Pre => Is_Map (B1, P1, D) and then Is_Map (B2, P2, D)
               and then Pairs (B1, P1) = Pairs (B2, P2)
               and then I <= Pairs (B1, P1) and then J <= Pairs (B1, P1)
               and then Match_Fwd (B1, P1, B2, P2, D, I - 1)
               and then Same_Bytes
                 (B1, Key_S (B1, P1, I, D), Key_E (B1, P1, I, D),
                  B2, Key_S (B2, P2, J, D), Key_E (B2, P2, J, D));

   --  Unique.Lemma_Match_Fwd_At: each conjunct of its postcondition.
   procedure Client_Lemma_Match_Fwd_At
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive;
      I : Positive)
   with Pre => Is_Map (B1, P1, D) and then Is_Map (B2, P2, D)
               and then Pairs (B1, P1) = Pairs (B2, P2)
               and then I <= Pairs (B1, P1)
               and then Match_Fwd (B1, P1, B2, P2, D, Pairs (B1, P1));

   --  Unique.Find_Key: each conjunct of its postcondition.
   procedure Client_Find_Key
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive;
      I : Positive)
   with Pre => Is_Map (B1, P1, D) and then Is_Map (B2, P2, D)
               and then Pairs (B1, P1) = Pairs (B2, P2)
               and then I <= Pairs (B1, P1)
               and then Match_Fwd (B1, P1, B2, P2, D, Pairs (B1, P1));

   --  Unique.Lemma_Key_In_Place: each conjunct of its postcondition.
   procedure Client_Lemma_Key_In_Place
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive;
      I : Positive; J : Positive; M : Positive)
   with Pre => Is_Map (B1, P1, D) and then Is_Map (B2, P2, D)
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
                  B1, Key_S (B1, P1, M, D), Key_E (B1, P1, M, D));

   --  Unique.Lemma_Map_Keys: each conjunct of its postcondition.
   procedure Client_Lemma_Map_Keys
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive)
   with Pre => Is_Map (B1, P1, D) and then Is_Map (B2, P2, D)
               and then Keys_Match (B1, P1, B2, P2, D);

   --  Unique.Lemma_Keys_Match_In_Order: each conjunct of its postcondition.
   procedure Client_Lemma_Keys_Match_In_Order
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive)
   with Pre => Is_Map (B1, P1, D) and then Is_Map (B2, P2, D)
               and then Pairs (B1, P1) = Pairs (B2, P2)
               and then
                 (for all I in 1 .. Pairs (B1, P1) =>
                    Same_Bytes
                      (B1, Key_S (B1, P1, I, D), Key_E (B1, P1, I, D),
                       B2, Key_S (B2, P2, I, D), Key_E (B2, P2, I, D)));

   --  Unique.Find_Pair: each conjunct of its postcondition.
   procedure Client_Find_Pair
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive;
      I : Positive)
   with Pre => Is_Map (B1, P1, D) and then Is_Map (B2, P2, D)
               and then Pairs (B1, P1) = Pairs (B2, P2)
               and then Same_Map_Clause (B1, P1, B2, P2, D)
               and then I <= Pairs (B1, P1);

   --  Unique.Find_Pair_Back: each conjunct of its postcondition.
   procedure Client_Find_Pair_Back
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive;
      J : Positive)
   with Pre => Is_Map (B1, P1, D) and then Is_Map (B2, P2, D)
               and then Pairs (B1, P1) = Pairs (B2, P2)
               and then Same_Map_Clause (B1, P1, B2, P2, D)
               and then J <= Pairs (B1, P1);

   --  Unique.Lemma_Map_Match: each conjunct of its postcondition.
   procedure Client_Lemma_Map_Match
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive)
   with Pre => Is_Map (B1, P1, D) and then Is_Map (B2, P2, D)
               and then Same (B1, P1, B2, P2, D);

   --  Unique.Lemma_Map_Values: each conjunct of its postcondition.
   procedure Client_Lemma_Map_Values
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive)
   with Pre => Is_Map (B1, P1, D) and then Is_Map (B2, P2, D)
               and then Same (B1, P1, B2, P2, D)
               and then Pairs (B1, P1) = Pairs (B2, P2)
               and then
                 (for all I in 1 .. Pairs (B1, P1) =>
                    Same_Bytes
                      (B1, Key_S (B1, P1, I, D), Key_E (B1, P1, I, D),
                       B2, Key_S (B2, P2, I, D), Key_E (B2, P2, I, D)));

   --  Unique.Lemma_Map_Concat: each conjunct of its postcondition.
   procedure Client_Lemma_Map_Concat
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive)
   with Pre => Is_Map (B1, P1, D) and then Is_Map (B2, P2, D)
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
                       B2, Key_E (B2, P2, I, D), Val_E (B2, P2, I, D)));

   --  Unique.Lemma_CU: each conjunct of its postcondition.
   procedure Client_Lemma_CU
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Natural)
   with Pre => P1 in B1'Range and then P2 in B2'Range
               and then Det_End (B1, P1, D) /= 0
               and then Det_End (B2, P2, D) /= 0
               and then Same (B1, P1, B2, P2, D);

   --  Unique.Lemma_CU_Whole: each conjunct of its postcondition.
   procedure Client_Lemma_CU_Whole
     (B1 : Bytes; B2 : Bytes)
   with Pre => Accept_Whole (B1) and then Accept_Whole (B2)
               and then Same (B1, B1'First, B2, B2'First, Max_Depth);

   --  Unique.Lemma_Head_Rebased: each conjunct of its postcondition.
   procedure Client_Lemma_Head_Rebased
     (B1 : Bytes; P1 : Positive; E1 : Natural;
      B2 : Bytes; P2 : Positive; E2 : Natural)
   with Pre => P1 in B1'Range and then P2 in B2'Range
               and then Head_Fits (B1, P1)
               and then E1 in P1 + Head_Len (B1 (P1)) .. B1'Last + 1
               and then E2 - P2 = E1 - P1
               and then Same_Bytes (B1, P1, E1, B2, P2, E2);

   --  Unique.Lemma_Members_Rebased: each conjunct of its postcondition.
   procedure Client_Lemma_Members_Rebased
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive)
   with Pre => P1 in B1'Range and then P2 in B2'Range
               and then Det_End (B1, P1, D) /= 0
               and then Det_End (B2, P2, D) /= 0
               and then Det_End (B1, P1, D) - P1 = Det_End (B2, P2, D) - P2
               and then Same_Bytes (B1, P1, Det_End (B1, P1, D),
                                    B2, P2, Det_End (B2, P2, D))
               and then Major_Of (B1 (P1)) in 4 | 5;

   --  Unique.Lemma_Same_Of_Bytes: each conjunct of its postcondition.
   procedure Client_Lemma_Same_Of_Bytes
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Natural)
   with Pre => P1 in B1'Range and then P2 in B2'Range
               and then Det_End (B1, P1, D) /= 0
               and then Det_End (B2, P2, D) /= 0
               and then Det_End (B1, P1, D) - P1 = Det_End (B2, P2, D) - P2
               and then Same_Bytes (B1, P1, Det_End (B1, P1, D),
                                    B2, P2, Det_End (B2, P2, D));

   --  Unique.Lemma_Child_Same_Of_Bytes: each conjunct of its postcondition.
   procedure Client_Lemma_Child_Same_Of_Bytes
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive;
      I : Positive)
   with Pre => P1 in B1'Range and then P2 in B2'Range
               and then Det_End (B1, P1, D) /= 0
               and then Det_End (B2, P2, D) /= 0
               and then Det_End (B1, P1, D) - P1 = Det_End (B2, P2, D) - P2
               and then Same_Bytes (B1, P1, Det_End (B1, P1, D),
                                    B2, P2, Det_End (B2, P2, D))
               and then Major_Of (B1 (P1)) = 4
               and then I <= Arg_Nat (B1, P1);

   --  Unique.Lemma_Array_Same_Of_Bytes: each conjunct of its postcondition.
   procedure Client_Lemma_Array_Same_Of_Bytes
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive)
   with Pre => P1 in B1'Range and then P2 in B2'Range
               and then Det_End (B1, P1, D) /= 0
               and then Det_End (B2, P2, D) /= 0
               and then Det_End (B1, P1, D) - P1 = Det_End (B2, P2, D) - P2
               and then Same_Bytes (B1, P1, Det_End (B1, P1, D),
                                    B2, P2, Det_End (B2, P2, D))
               and then Major_Of (B1 (P1)) = 4;

   --  Unique.Lemma_Pair_Same_Of_Bytes: each conjunct of its postcondition.
   procedure Client_Lemma_Pair_Same_Of_Bytes
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive;
      I : Positive)
   with Pre => Is_Map (B1, P1, D)
               and then P2 in B2'Range
               and then Det_End (B2, P2, D) /= 0
               and then Det_End (B1, P1, D) - P1 = Det_End (B2, P2, D) - P2
               and then Same_Bytes (B1, P1, Det_End (B1, P1, D),
                                    B2, P2, Det_End (B2, P2, D))
               and then I <= Pairs (B1, P1);

   --  Unique.Lemma_Map_Same_Of_Bytes: each conjunct of its postcondition.
   procedure Client_Lemma_Map_Same_Of_Bytes
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive)
   with Pre => Is_Map (B1, P1, D)
               and then P2 in B2'Range
               and then Det_End (B2, P2, D) /= 0
               and then Det_End (B1, P1, D) - P1 = Det_End (B2, P2, D) - P2
               and then Same_Bytes (B1, P1, Det_End (B1, P1, D),
                                    B2, P2, Det_End (B2, P2, D));

   --  Unique.Lemma_Same_Of_Bytes_Whole: each conjunct of its postcondition.
   procedure Client_Lemma_Same_Of_Bytes_Whole
     (B1 : Bytes; B2 : Bytes)
   with Pre => Accept_Whole (B1) and then Accept_Whole (B2)
               and then B1'Length = B2'Length
               and then (for all K in B1'Range =>
                           B1 (K) = B2 (K - B1'First + B2'First));

   --  Unique.Lemma_Same_Iff_Bytes_Whole: each conjunct of its postcondition.
   procedure Client_Lemma_Same_Iff_Bytes_Whole
     (B1 : Bytes; B2 : Bytes)
   with Pre => Accept_Whole (B1) and then Accept_Whole (B2);

end Cbor_Det.Proof.Model_Surface;
