--  Deterministic CBOR: the value an accepted item denotes.
--
--  Copyright (c) 2026, Matt Doughty
--  SPDX-License-Identifier: BSD-3-Clause
--
--  Same (B1, P1, B2, P2, D) says that the accepted items at P1 in B1 and
--  at P2 in B2, each judged at depth D, denote the same value. There is
--  no value object: the value is a relation between two encodings. The
--  kinds are kept apart (the major types must be equal), and within a
--  kind (RFC 8949, sections 3.1 and 3.3):
--
--    * an unsigned integer (major type 0) is its argument, and a negative
--      integer (major type 1) is -1 minus its argument; equal major types
--      and equal arguments are exactly equal sign and magnitude;
--    * a byte string (major type 2) is its bytes;
--    * a text string (major type 3) is its bytes, unchecked as UTF-8, and
--      is never the same as a byte string;
--    * an array (major type 4) is its members in order: the same count,
--      and member I of one the same as member I of the other;
--    * a map (major type 5) is the set of its key/value pairs, in no
--      order: the same count, every pair of one has a pair of the other
--      whose key is the same and whose value is the same, and the other
--      way round. A key may be of any kind, a container included;
--    * false, true and null (f4, f5, f6) are themselves: the same
--      additional information (20, 21 or 22).
--
--  Tags (major type 6) are never accepted, so they denote nothing. How
--  wide a head is and where an item sits play no part; nor does the
--  order of a map's pairs. The members of a container are compared at
--  depth D - 1, where Det_End accepted them.
--
--  Child names a container's members by index, and Key_S, Key_E and
--  Val_E the bytes of a map's pairs, so the relation can speak of them.
--  Same and its map clause are hidden from the provers and opened by the
--  lemmas at the end of this unit.

with Cbor_Det.Proof.Heads; use Cbor_Det.Proof.Heads;
with Cbor_Det.Proof.Det;   use Cbor_Det.Proof.Det;

package Cbor_Det.Proof.Model with SPARK_Mode, Ghost is

   use type Interfaces.Unsigned_64;

   ---------------------------------------------------------------------
   --  A container's members.
   ---------------------------------------------------------------------

   --  How many members the container at P has: N for an array of N, 2 N
   --  for a map of N pairs (key, value, key, value, ...).
   function Member_Count (B : Bytes; P : Positive) return Natural is
     (if Major_Of (B (P)) = 4 then Arg_Nat (B, P) else 2 * Arg_Nat (B, P))
   with Pre => P in B'Range and then Head_Fits (B, P)
               and then Arg_Small (B, P)
               and then Major_Of (B (P)) in 4 | 5
               and then (if Major_Of (B (P)) = 5
                         then Arg_Nat (B, P) <= 2**30 - 1);

   --  Member I (from 1) of the accepted container at P: it starts where
   --  the first I - 1 members end, and is itself an accepted item one
   --  level down. The rest of what is known about it is in
   --  Lemma_Child_At, so that this postcondition stays small where Child
   --  appears under a quantifier.
   function Child
     (B : Bytes; P : Positive; I : Positive; D : Positive) return Positive
   with Pre  => P in B'Range
                and then Det_End (B, P, D) /= 0
                and then Major_Of (B (P)) in 4 | 5
                and then I <= Member_Count (B, P),
        Post => Child'Result in B'Range
                and then Child'Result
                         = Members_End
                             (B, P + Head_Len (B (P)), I - 1, D - 1)
                and then Det_End (B, Child'Result, D - 1) /= 0;

   --  Member I ends where the first I members end, within the container.
   procedure Lemma_Child_At
     (B : Bytes; P : Positive; I : Positive; D : Positive)
   with Pre  => P in B'Range
                and then Det_End (B, P, D) /= 0
                and then Major_Of (B (P)) in 4 | 5
                and then I <= Member_Count (B, P),
        Post => Child (B, P, I, D)
                = Members_End (B, P + Head_Len (B (P)), I - 1, D - 1)
                and then Det_End (B, Child (B, P, I, D), D - 1)
                         = Members_End (B, P + Head_Len (B (P)), I, D - 1)
                and then Det_End (B, Child (B, P, I, D), D - 1)
                         <= Det_End (B, P, D);

   ---------------------------------------------------------------------
   --  A map's pairs, by index.
   ---------------------------------------------------------------------

   --  P starts an accepted map at depth D.
   function Is_Map (B : Bytes; P : Positive; D : Natural) return Boolean is
     (P in B'Range and then D >= 1 and then Det_End (B, P, D) /= 0
      and then Major_Of (B (P)) = 5);

   --  The number of pairs of the map at P.
   function Pairs (B : Bytes; P : Positive) return Natural is
     (Arg_Nat (B, P))
   with Pre => P in B'Range and then Head_Fits (B, P)
               and then Arg_Small (B, P);

   --  Where the key of pair M (from 1) starts.
   function Key_S
     (B : Bytes; P : Positive; M : Positive; D : Positive) return Positive
   is (Child (B, P, 2 * M - 1, D))
   with Pre  => Is_Map (B, P, D) and then M <= Pairs (B, P),
        Post => Key_S'Result in B'Range
                and then Det_End (B, Key_S'Result, D - 1) /= 0;
   pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", Key_S);

   --  Where the key of pair M ends: where its value starts.
   function Key_E
     (B : Bytes; P : Positive; M : Positive; D : Positive) return Positive
   is (Child (B, P, 2 * M, D))
   with Pre  => Is_Map (B, P, D) and then M <= Pairs (B, P),
        Post => Key_E'Result in B'Range
                and then Det_End (B, Key_E'Result, D - 1) /= 0;
   pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", Key_E);

   --  Where the value of pair M ends.
   function Val_E
     (B : Bytes; P : Positive; M : Positive; D : Positive) return Positive
   is (Det_End (B, Child (B, P, 2 * M, D), D - 1))
   with Pre  => Is_Map (B, P, D) and then M <= Pairs (B, P),
        Post => Val_E'Result in B'First + 1 .. B'Last + 1;
   pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", Val_E);

   --  Everything the proofs need about pair M: where its key and value
   --  lie, that each is an accepted item one level down, and where they
   --  sit among the map's members.
   procedure Lemma_Key_Slice
     (B : Bytes; P : Positive; M : Positive; D : Positive)
   with Pre  => Is_Map (B, P, D) and then M <= Pairs (B, P),
        Post => Key_S (B, P, M, D) in B'Range
                and then Key_E (B, P, M, D)
                         in Key_S (B, P, M, D) + 1 .. B'Last
                and then Val_E (B, P, M, D)
                         in Key_E (B, P, M, D) + 1 .. B'Last + 1
                and then Val_E (B, P, M, D) <= Det_End (B, P, D)
                and then Det_End (B, Key_S (B, P, M, D), D - 1)
                         = Key_E (B, P, M, D)
                and then Det_End (B, Key_E (B, P, M, D), D - 1)
                         = Val_E (B, P, M, D)
                and then Key_S (B, P, M, D)
                         = Members_End
                             (B, P + Head_Len (B (P)), 2 * M - 2, D - 1)
                and then Key_E (B, P, M, D)
                         = Members_End
                             (B, P + Head_Len (B (P)), 2 * M - 1, D - 1)
                and then Val_E (B, P, M, D)
                         = Members_End
                             (B, P + Head_Len (B (P)), 2 * M, D - 1);

   ---------------------------------------------------------------------
   --  The relation.
   ---------------------------------------------------------------------

   function Same
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Natural)
      return Boolean
   with Pre => P1 in B1'Range and then P2 in B2'Range
               and then Det_End (B1, P1, D) /= 0
               and then Det_End (B2, P2, D) /= 0,
        Subprogram_Variant => (Decreases => D, Decreases => Natural'(1));

   --  The map clause of Same: every pair of the map at P1 has a pair of
   --  the map at P2 whose key and value are the same, and every pair of
   --  the map at P2 has such a pair in the map at P1.
   function Same_Map_Clause
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive)
      return Boolean
   with Pre => Is_Map (B1, P1, D) and then Is_Map (B2, P2, D)
               and then Pairs (B1, P1) = Pairs (B2, P2),
        Subprogram_Variant => (Decreases => D, Decreases => Natural'(0));

   --  The branch for tags is never reached: Det_End accepts no tag, and
   --  the provers show it; the warning that says so is silenced here.
   pragma Warnings
     (GNATprove, Off, "unreachable branch",
      Reason => "Det_End accepts no tag (major type 6)");
   function Same
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Natural)
      return Boolean
   is (Major_Of (B1 (P1)) = Major_Of (B2 (P2))
       and then
         (case Major_Of (B1 (P1)) is
            --  Integers: major type 0 is the argument, major type 1 is
            --  -1 minus the argument (magnitude argument + 1, which can be
            --  2**64, so it is never computed).
            when 0 | 1 => Arg (B1, P1) = Arg (B2, P2),
            --  Byte strings and text strings: their bytes.
            when 2 | 3 =>
              Arg_Nat (B1, P1) = Arg_Nat (B2, P2)
              and then Same_Bytes
                (B1, P1 + Head_Len (B1 (P1)), Det_End (B1, P1, D),
                 B2, P2 + Head_Len (B2 (P2)), Det_End (B2, P2, D)),
            --  Arrays: their members, in order.
            when 4 =>
              Arg_Nat (B1, P1) = Arg_Nat (B2, P2)
              and then
                (for all I in 1 .. Arg_Nat (B1, P1) =>
                   Same (B1, Child (B1, P1, I, D),
                         B2, Child (B2, P2, I, D), D - 1)),
            --  Maps: their pairs, as a set.
            when 5 =>
              Arg_Nat (B1, P1) = Arg_Nat (B2, P2)
              and then Same_Map_Clause (B1, P1, B2, P2, D),
            --  Tags: never accepted.
            when 6 => False,
            --  False, true and null: the same simple value.
            when 7 => Info_Of (B1 (P1)) = Info_Of (B2 (P2))));
   pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", Same);
   pragma Warnings (GNATprove, On, "unreachable branch");

   function Same_Map_Clause
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive)
      return Boolean
   is ((for all I in 1 .. Pairs (B1, P1) =>
          (for some J in 1 .. Pairs (B1, P1) =>
             Same (B1, Key_S (B1, P1, I, D), B2, Key_S (B2, P2, J, D), D - 1)
             and then Same (B1, Key_E (B1, P1, I, D),
                            B2, Key_E (B2, P2, J, D), D - 1)))
       and then
         (for all J in 1 .. Pairs (B1, P1) =>
            (for some I in 1 .. Pairs (B1, P1) =>
               Same (B1, Key_S (B1, P1, I, D),
                     B2, Key_S (B2, P2, J, D), D - 1)
               and then Same (B1, Key_E (B1, P1, I, D),
                              B2, Key_E (B2, P2, J, D), D - 1))));
   pragma Annotate
     (GNATprove, Hide_Info, "Expression_Function_Body", Same_Map_Clause);

   ---------------------------------------------------------------------
   --  The relation, one step at a time.
   ---------------------------------------------------------------------

   --  Same, opened one level: the kinds are equal and accepted, and for
   --  every kind but a map, what Same says of it.
   procedure Lemma_Same_Open
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Natural)
   with Pre  => P1 in B1'Range and then P2 in B2'Range
                and then Det_End (B1, P1, D) /= 0
                and then Det_End (B2, P2, D) /= 0
                and then Same (B1, P1, B2, P2, D),
        Post => Major_Of (B1 (P1)) = Major_Of (B2 (P2))
                and then Major_Of (B1 (P1)) in 0 .. 5 | 7
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
                and then (if Major_Of (B1 (P1)) = 5
                          then Arg_Nat (B1, P1) = Arg_Nat (B2, P2))
                and then (if Major_Of (B1 (P1)) = 7
                          then Info_Of (B1 (P1)) = Info_Of (B2 (P2)));

   --  Same, opened at a map: the same count and the map clause.
   procedure Lemma_Same_Map
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive)
   with Pre  => Is_Map (B1, P1, D) and then P2 in B2'Range
                and then Det_End (B2, P2, D) /= 0
                and then Same (B1, P1, B2, P2, D),
        Post => Is_Map (B2, P2, D)
                and then Pairs (B1, P1) = Pairs (B2, P2)
                and then Same_Map_Clause (B1, P1, B2, P2, D);

   --  The map clause at one pair of the first map: it has a match.
   procedure Lemma_Same_Map_At
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive;
      I : Positive)
   with Pre  => Is_Map (B1, P1, D) and then Is_Map (B2, P2, D)
                and then Pairs (B1, P1) = Pairs (B2, P2)
                and then Same_Map_Clause (B1, P1, B2, P2, D)
                and then I <= Pairs (B1, P1),
        Post => (for some J in 1 .. Pairs (B1, P1) =>
                   Same (B1, Key_S (B1, P1, I, D),
                         B2, Key_S (B2, P2, J, D), D - 1)
                   and then Same (B1, Key_E (B1, P1, I, D),
                                  B2, Key_E (B2, P2, J, D), D - 1));

   --  The map clause at one pair of the second map: it has a match.
   procedure Lemma_Same_Map_Back_At
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive;
      J : Positive)
   with Pre  => Is_Map (B1, P1, D) and then Is_Map (B2, P2, D)
                and then Pairs (B1, P1) = Pairs (B2, P2)
                and then Same_Map_Clause (B1, P1, B2, P2, D)
                and then J <= Pairs (B1, P1),
        Post => (for some I in 1 .. Pairs (B1, P1) =>
                   Same (B1, Key_S (B1, P1, I, D),
                         B2, Key_S (B2, P2, J, D), D - 1)
                   and then Same (B1, Key_E (B1, P1, I, D),
                                  B2, Key_E (B2, P2, J, D), D - 1));

   ---------------------------------------------------------------------
   --  The relation, closed one step at a time, and its reflexivity.
   ---------------------------------------------------------------------

   --  Same, closed one level: the converse of Lemma_Same_Open, with the
   --  map clause for a map.
   procedure Lemma_Same_Close
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Natural)
   with Pre  => P1 in B1'Range and then P2 in B2'Range
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
                          then Info_Of (B1 (P1)) = Info_Of (B2 (P2))),
        Post => Same (B1, P1, B2, P2, D);

   --  Two maps whose pairs are the same in order satisfy the map clause:
   --  pair I matches pair I.
   procedure Lemma_Same_Map_In_Order
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive)
   with Pre  => Is_Map (B1, P1, D) and then Is_Map (B2, P2, D)
                and then Pairs (B1, P1) = Pairs (B2, P2)
                and then
                  (for all I in 1 .. Pairs (B1, P1) =>
                     Same (B1, Key_S (B1, P1, I, D),
                           B2, Key_S (B2, P2, I, D), D - 1)
                     and then Same (B1, Key_E (B1, P1, I, D),
                                    B2, Key_E (B2, P2, I, D), D - 1)),
        Post => Same_Map_Clause (B1, P1, B2, P2, D);

   --  Same is reflexive on accepted items of every kind: it is never
   --  False for an item that is accepted.
   procedure Lemma_Same_Refl (B : Bytes; P : Positive; D : Natural)
   with Pre  => P in B'Range and then Det_End (B, P, D) /= 0,
        Post => Same (B, P, B, P, D),
        Subprogram_Variant => (Decreases => D);

end Cbor_Det.Proof.Model;
