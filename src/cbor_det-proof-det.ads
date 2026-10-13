--  Deterministic CBOR: the deterministic-item predicate.
--
--  Copyright (c) 2026, Matt Doughty
--  SPDX-License-Identifier: BSD-3-Clause
--
--  Det_End (B, P, D) is the specification of acceptance. It is the end
--  (one past the last byte) of the deterministic item that starts at P,
--  or 0 if no item that starts at P is accepted. It says nothing about
--  the bytes after that item: in 00 00 the item at the first byte ends
--  at the second. D is the container depth still allowed: a scalar is
--  accepted at any D, 0 included; every container, an empty one too,
--  needs D >= 1, and its members are judged at D - 1. A check of a whole
--  input starts at D = Max_Depth, so Max_Depth containers nested in one
--  another are accepted and one more is not.
--
--  An item is accepted when (RFC 8949, sections 3 and 4.2.1):
--
--    * its head is well formed in this profile and shortest (rule 1):
--      additional information 28 to 30 (not well formed) and 31 (an
--      indefinite length, rule 3) are refused, and so is an argument
--      wider than it needs to be;
--    * it is an unsigned or negative integer (major types 0 and 1), with
--      any 64-bit argument;
--    * it is a byte string or a text string (major types 2 and 3) whose
--      length fits in the bytes left; a text string's bytes are not
--      checked to be UTF-8;
--    * it is an array (major type 4) whose members follow it, each an
--      accepted item at depth D - 1;
--    * it is a map (major type 5) whose keys and values follow it,
--      alternately, each an accepted item at depth D - 1, with the keys
--      strictly ascending in the bytewise lexicographic order of their
--      encodings (rule 4); being strict, the order also makes the keys
--      unique (section 5.6). A key may be of any accepted kind;
--    * it is false, true or null (f4, f5, f6).
--
--  Everything else is refused: tags (major type 6), every other simple
--  value or float of major type 7 (f7, simple values 0 to 19, f8 with any
--  following byte, and the floats f9, fa, fb), and every count or length
--  that does not fit in the bytes left. A count is checked by division
--  against the bytes left, never by multiplication, so no arithmetic can
--  overflow.
--
--  Members_End (B, Q, K, D) is the end of K consecutive accepted items
--  from Q, and Keys_Ascending the order rule on a map's keys. The three
--  are mutually recursive, with the variant (depth, member count). They
--  are hidden from the provers and opened one step at a time by the
--  lemmas below, which also give the facts the later proofs use:
--  bounds and progress of every end, the member-sequence facts (start,
--  step, prefix, monotonicity, failure propagation), the key-order rule
--  one key at a time, and the algebra of Same_Bytes.
--
--  Accept_Whole is the check of a whole input: B is not empty and holds
--  exactly one accepted item at depth Max_Depth, with no byte after it.

with Cbor_Det.Proof.Heads; use Cbor_Det.Proof.Heads;

package Cbor_Det.Proof.Det with SPARK_Mode is

   use type Interfaces.Unsigned_64;

   ---------------------------------------------------------------------
   --  Bytewise lexicographic order on slices (RFC 8949, section 4.2.1).
   ---------------------------------------------------------------------

   --  The slice B1 (P1 .. E1 - 1) is less than B2 (P2 .. E2 - 1): at the
   --  first byte where they differ it is smaller, or it is a proper
   --  prefix of the other. Total: False on anything that is not two
   --  slices.
   function Lex_Less
     (B1 : Bytes; P1 : Natural; E1 : Natural;
      B2 : Bytes; P2 : Natural; E2 : Natural) return Boolean
   with Ghost, Subprogram_Variant => (Decreases => E1 - P1);

   function Lex_Less
     (B1 : Bytes; P1 : Natural; E1 : Natural;
      B2 : Bytes; P2 : Natural; E2 : Natural) return Boolean
   is (if not Slice_OK (B1, P1, E1) or else not Slice_OK (B2, P2, E2)
       then False
       elsif P1 = E1 then P2 < E2
       elsif P2 = E2 then False
       elsif B1 (P1) /= B2 (P2) then B1 (P1) < B2 (P2)
       else Lex_Less (B1, P1 + 1, E1, B2, P2 + 1, E2));
   pragma Annotate
     (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);

   --  One step of the order's definition.
   procedure Lemma_Lex_Step
     (B1 : Bytes; P1 : Natural; E1 : Natural;
      B2 : Bytes; P2 : Natural; E2 : Natural)
   with Ghost,
        Pre  => Slice_OK (B1, P1, E1) and then Slice_OK (B2, P2, E2),
        Post => Lex_Less (B1, P1, E1, B2, P2, E2)
                = (if P1 = E1 then P2 < E2
                   elsif P2 = E2 then False
                   elsif B1 (P1) /= B2 (P2) then B1 (P1) < B2 (P2)
                   else Lex_Less (B1, P1 + 1, E1, B2, P2 + 1, E2));

   --  The order is False on anything that is not two slices.
   procedure Lemma_Lex_Not_Slice
     (B1 : Bytes; P1 : Natural; E1 : Natural;
      B2 : Bytes; P2 : Natural; E2 : Natural)
   with Ghost,
        Pre  => not Slice_OK (B1, P1, E1) or else not Slice_OK (B2, P2, E2),
        Post => not Lex_Less (B1, P1, E1, B2, P2, E2);

   ---------------------------------------------------------------------
   --  Arguments as counts and lengths.
   ---------------------------------------------------------------------

   --  The argument fits a Natural.
   function Arg_Small (B : Bytes; P : Positive) return Boolean is
     (Arg (B, P) <= U64 (Natural'Last))
   with Pre => P in B'Range and then Head_Fits (B, P);

   --  The argument as a Natural.
   function Arg_Nat (B : Bytes; P : Positive) return Natural is
     (Natural (Arg (B, P)))
   with Pre  => P in B'Range and then Head_Fits (B, P)
                and then Arg_Small (B, P),
        Post => U64 (Arg_Nat'Result) = Arg (B, P);

   --  The argument, as a count or a length, is at most Room.
   function Arg_Fits (B : Bytes; P : Positive; Room : Natural) return Boolean
   is (Arg_Small (B, P) and then Arg_Nat (B, P) <= Room)
   with Pre => P in B'Range and then Head_Fits (B, P);

   --  A Natural survives the trip through U64.
   procedure Lemma_Nat_Round (N : Natural)
   with Ghost, Post => Natural (U64 (N)) = N;

   --  A head whose argument is a Natural N has N as its count.
   procedure Lemma_Arg_Is (B : Bytes; P : Positive; N : Natural)
   with Ghost,
        Pre  => P in B'Range and then Head_Fits (B, P)
                and then Arg (B, P) = U64 (N),
        Post => Arg_Small (B, P) and then Arg_Nat (B, P) = N;

   --  An argument that fits a Natural is small.
   procedure Lemma_Arg_Small_Of (B : Bytes; P : Positive)
   with Ghost,
        Pre  => P in B'Range and then Head_Fits (B, P)
                and then Arg (B, P) <= U64 (Natural'Last),
        Post => Arg_Small (B, P);

   --  Two heads with the same argument are small together, with the
   --  same count.
   procedure Lemma_Arg_Same
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive)
   with Ghost,
        Pre  => P1 in B1'Range and then Head_Fits (B1, P1)
                and then P2 in B2'Range and then Head_Fits (B2, P2)
                and then Arg (B1, P1) = Arg (B2, P2),
        Post => Arg_Small (B1, P1) = Arg_Small (B2, P2)
                and then (if Arg_Small (B1, P1)
                          then Arg_Nat (B1, P1) = Arg_Nat (B2, P2));

   ---------------------------------------------------------------------
   --  The deterministic-item predicate: three mutually recursive ghost
   --  functions, with the variant (depth, member count).
   ---------------------------------------------------------------------

   --  The end of K consecutive accepted items at depth D from Q, or 0.
   function Members_End
     (B : Bytes; Q : Positive; K : Natural; D : Natural) return Ext
   with Ghost,
        Pre  => Q in B'First .. B'Last + 1,
        Post => Members_End'Result = 0
                or else Members_End'Result in Q .. B'Last + 1,
        Subprogram_Variant => (Decreases => D, Decreases => K);

   --  The keys of N pairs of members from Q are strictly ascending: each
   --  key after the first is greater than the one before it.
   function Keys_Ascending
     (B : Bytes; Q : Positive; N : Natural; D : Natural) return Boolean
   with Ghost,
        Pre => Q in B'First .. B'Last + 1 and then N <= 2**30 - 1,
        Subprogram_Variant => (Decreases => D, Decreases => 2 * N + 1);

   --  The end of the accepted item that starts at P, or 0. On success the
   --  end lies past P and within B, the head is accepted, the major type
   --  is not 6, an integer ends after its head, a string after its head
   --  and its length in bytes, a container needs D >= 1 and a count that
   --  fits in the bytes left (a map's twice), and a simple value is f4,
   --  f5 or f6 and ends after its one byte.
   function Det_End (B : Bytes; P : Positive; D : Natural) return Ext
   with Ghost,
        Pre  => P in B'Range,
        Post => Det_End'Result = 0
                or else
                  (Det_End'Result in P + 1 .. B'Last + 1
                   and then Head_OK (B, P)
                   and then Major_Of (B (P)) in 0 .. 5 | 7
                   and then (if Major_Of (B (P)) in 0 | 1
                             then Det_End'Result = P + Head_Len (B (P)))
                   and then
                     (if Major_Of (B (P)) in 2 | 3
                      then Arg_Fits (B, P, Remaining (B, P) - Head_Len (B (P)))
                           and then Det_End'Result
                                    = P + Head_Len (B (P)) + Arg_Nat (B, P))
                   and then
                     (if Major_Of (B (P)) = 4
                      then D >= 1
                           and then Arg_Fits
                             (B, P, Remaining (B, P) - Head_Len (B (P))))
                   and then
                     (if Major_Of (B (P)) = 5
                      then D >= 1
                           and then Arg_Fits
                             (B, P,
                              (Remaining (B, P) - Head_Len (B (P))) / 2))
                   and then
                     (if Major_Of (B (P)) = 7
                      then Info_Of (B (P)) in 20 .. 22
                           and then Det_End'Result = P + 1)),
        Subprogram_Variant => (Decreases => D, Decreases => Natural'(0));

   function Keys_Ascending
     (B : Bytes; Q : Positive; N : Natural; D : Natural) return Boolean
   is (N < 2
       or else (Keys_Ascending (B, Q, N - 1, D)
                and then Lex_Less (B, Members_End (B, Q, 2 * N - 4, D),
                                      Members_End (B, Q, 2 * N - 3, D),
                                   B, Members_End (B, Q, 2 * N - 2, D),
                                      Members_End (B, Q, 2 * N - 1, D))));
   pragma Annotate
     (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);

   function Det_End (B : Bytes; P : Positive; D : Natural) return Ext is
     (if not Head_OK (B, P) then 0
      else
        (declare
           L : constant Positive := Head_Len (B (P));
           R : constant Natural  := Remaining (B, P) - L;
         begin
           (case Major_Of (B (P)) is
              --  Unsigned and negative integers.
              when 0 | 1 => P + L,
              --  Byte and text strings: the head, then the bytes.
              when 2 | 3 =>
                (if Arg_Fits (B, P, R) then P + L + Arg_Nat (B, P) else 0),
              --  Arrays: the members, one depth down.
              when 4 =>
                (if D = 0 or else not Arg_Fits (B, P, R) then 0
                 else Members_End (B, P + L, Arg_Nat (B, P), D - 1)),
              --  Maps: key, value, key, value, ..., one depth down, the
              --  keys strictly ascending.
              when 5 =>
                (if D = 0 or else not Arg_Fits (B, P, R / 2) then 0
                 elsif Members_End (B, P + L, 2 * Arg_Nat (B, P), D - 1) = 0
                 then 0
                 elsif not Keys_Ascending (B, P + L, Arg_Nat (B, P), D - 1)
                 then 0
                 else Members_End (B, P + L, 2 * Arg_Nat (B, P), D - 1)),
              --  Tags.
              when 6 => 0,
              --  False, true and null (f4, f5, f6); every other simple
              --  value and every float is refused.
              when 7 =>
                (if Info_Of (B (P)) in 20 .. 22 then P + L else 0))));
   pragma Annotate
     (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);

   function Members_End
     (B : Bytes; Q : Positive; K : Natural; D : Natural) return Ext
   is (if K = 0 then Q
       else
         (declare
            S : constant Ext := Members_End (B, Q, K - 1, D);
          begin
            (if S = 0 or else S > B'Last then 0 else Det_End (B, S, D))));
   pragma Annotate
     (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);

   --  The check of a whole input: B is not empty and holds exactly one
   --  accepted item at depth Max_Depth, with no byte after it.
   function Accept_Whole (B : Bytes) return Boolean is
     (B'Length >= 1 and then Det_End (B, B'First, Max_Depth) = B'Last + 1)
   with Ghost;

   ---------------------------------------------------------------------
   --  The definitions, one step at a time. Each of these lemmas reveals
   --  one definition in its own proof and nowhere else.
   ---------------------------------------------------------------------

   --  A run of zero members ends where it starts.
   procedure Lemma_Members_Start (B : Bytes; Q : Positive; D : Natural)
   with Ghost,
        Pre  => Q in B'First .. B'Last + 1,
        Post => Members_End (B, Q, 0, D) = Q;

   --  Member K starts where the first K - 1 end, and ends where the one
   --  item that starts there ends; if the first K - 1 fail or use up B,
   --  the K fail.
   procedure Lemma_Members_Step
     (B : Bytes; Q : Positive; K : Positive; D : Natural)
   with Ghost,
        Pre  => Q in B'First .. B'Last + 1,
        Post => Members_End (B, Q, K, D)
                = (if Members_End (B, Q, K - 1, D) = 0
                     or else Members_End (B, Q, K - 1, D) > B'Last
                   then 0
                   else Det_End (B, Members_End (B, Q, K - 1, D), D));

   --  What Det_End is, case by case: its definition, one step. The case
   --  expression is qualified (Ext') only because GNAT 16.1.0 crashes
   --  compiling it unqualified with assertions on and overflow checks in
   --  assertions eliminated (-gnata -gnato13); the meaning is the same.
   procedure Lemma_Det_Step (B : Bytes; P : Positive; D : Natural)
   with Ghost,
        Pre  => P in B'Range,
        Post => Det_End (B, P, D)
                = (if not Head_OK (B, P) then 0
                   else
                     Ext'(case Major_Of (B (P)) is
                        when 0 | 1 => P + Head_Len (B (P)),
                        when 2 | 3 =>
                          (if Arg_Fits
                                (B, P, Remaining (B, P) - Head_Len (B (P)))
                           then P + Head_Len (B (P)) + Arg_Nat (B, P)
                           else 0),
                        when 4 =>
                          (if D = 0
                             or else not Arg_Fits
                               (B, P, Remaining (B, P) - Head_Len (B (P)))
                           then 0
                           else Members_End (B, P + Head_Len (B (P)),
                                             Arg_Nat (B, P), D - 1)),
                        when 5 =>
                          (if D = 0
                             or else not Arg_Fits
                               (B, P,
                                (Remaining (B, P) - Head_Len (B (P))) / 2)
                           then 0
                           elsif Members_End (B, P + Head_Len (B (P)),
                                              2 * Arg_Nat (B, P), D - 1) = 0
                           then 0
                           elsif not Keys_Ascending (B, P + Head_Len (B (P)),
                                                     Arg_Nat (B, P), D - 1)
                           then 0
                           else Members_End (B, P + Head_Len (B (P)),
                                             2 * Arg_Nat (B, P), D - 1)),
                        when 6 => 0,
                        when 7 =>
                          (if Info_Of (B (P)) in 20 .. 22
                           then P + Head_Len (B (P))
                           else 0)));

   --  The order rule, one key at a time: its definition, one step.
   procedure Lemma_Keys_Step
     (B : Bytes; Q : Positive; N : Natural; D : Natural)
   with Ghost,
        Pre  => Q in B'First .. B'Last + 1 and then N <= 2**30 - 1,
        Post => Keys_Ascending (B, Q, N, D)
                = (N < 2
                   or else
                     (Keys_Ascending (B, Q, N - 1, D)
                      and then Lex_Less (B, Members_End (B, Q, 2 * N - 4, D),
                                            Members_End (B, Q, 2 * N - 3, D),
                                         B, Members_End (B, Q, 2 * N - 2, D),
                                            Members_End (B, Q, 2 * N - 1, D)
                                        )));

   --  An accepted container, restated: an array ends where its members
   --  end, a map where its keys and values end, with its keys ascending;
   --  the members are judged at D - 1.
   procedure Lemma_Det_Container (B : Bytes; P : Positive; D : Natural)
   with Ghost,
        Pre  => P in B'Range and then Det_End (B, P, D) /= 0
                and then Major_Of (B (P)) in 4 | 5,
        Post => (if Major_Of (B (P)) = 4
                 then Det_End (B, P, D)
                      = Members_End (B, P + Head_Len (B (P)),
                                     Arg_Nat (B, P), D - 1)
                 else Det_End (B, P, D)
                      = Members_End (B, P + Head_Len (B (P)),
                                     2 * Arg_Nat (B, P), D - 1)
                      and then Keys_Ascending (B, P + Head_Len (B (P)),
                                               Arg_Nat (B, P), D - 1));

   ---------------------------------------------------------------------
   --  Member sequences.
   ---------------------------------------------------------------------

   --  Member I (counting from 1) of a run of members from Q starts where
   --  the first I - 1 members end.
   function Member_Start
     (B : Bytes; Q : Positive; I : Positive; D : Natural) return Ext
   is (Members_End (B, Q, I - 1, D))
   with Ghost, Pre => Q in B'First .. B'Last + 1;

   --  A run of K members that is accepted has its first K - 1 ending
   --  within B, where member K starts, and member K takes at least one
   --  byte.
   procedure Lemma_Members_Last
     (B : Bytes; Q : Positive; K : Positive; D : Natural)
   with Ghost,
        Pre  => Q in B'First .. B'Last + 1
                and then Members_End (B, Q, K, D) /= 0,
        Post => Members_End (B, Q, K - 1, D) in B'First .. B'Last
                and then Members_End (B, Q, K, D)
                         = Det_End (B, Members_End (B, Q, K - 1, D), D)
                and then Members_End (B, Q, K, D)
                         > Members_End (B, Q, K - 1, D);

   --  Every prefix of an accepted run of members is accepted, and ends
   --  no later.
   procedure Lemma_Members_Prefix
     (B : Bytes; Q : Positive; I : Natural; K : Natural; D : Natural)
   with Ghost,
        Pre  => Q in B'First .. B'Last + 1 and then I <= K
                and then Members_End (B, Q, K, D) /= 0,
        Post => Members_End (B, Q, I, D) /= 0
                and then Members_End (B, Q, I, D) <= Members_End (B, Q, K, D),
        Subprogram_Variant => (Decreases => K);

   --  In an accepted run every member starts where the one before it
   --  ends, and takes at least one byte.
   procedure Lemma_Members_Monotone
     (B : Bytes; Q : Positive; K : Natural; D : Natural)
   with Ghost,
        Pre  => Q in B'First .. B'Last + 1
                and then Members_End (B, Q, K, D) /= 0,
        Post => (for all J in 0 .. K =>
                   Members_End (B, Q, J, D) /= 0
                   and then Members_End (B, Q, J, D) >= Q + J
                   and then Members_End (B, Q, J, D)
                            <= Members_End (B, Q, K, D))
                and then
                  (for all J in 1 .. K =>
                     Members_End (B, Q, J - 1, D) < Members_End (B, Q, J, D)
                     and then Members_End (B, Q, J, D)
                              = Det_End (B, Members_End (B, Q, J - 1, D), D)),
        Subprogram_Variant => (Decreases => K);

   --  A run that fails at member I fails as a whole.
   procedure Lemma_Members_Zero
     (B : Bytes; Q : Positive; I : Natural; K : Natural; D : Natural)
   with Ghost,
        Pre  => Q in B'First .. B'Last + 1 and then I <= K
                and then Members_End (B, Q, I, D) = 0,
        Post => Members_End (B, Q, K, D) = 0,
        Subprogram_Variant => (Decreases => K);

   ---------------------------------------------------------------------
   --  The order rule on keys.
   ---------------------------------------------------------------------

   --  Ascending keys, extended by one key greater than the last.
   procedure Lemma_Keys_Extend
     (B : Bytes; Q : Positive; KN : Positive; D : Natural)
   with Ghost,
        Pre  => Q in B'First .. B'Last + 1 and then KN in 2 .. 2**30 - 1
                and then Keys_Ascending (B, Q, KN - 1, D)
                and then Lex_Less (B, Members_End (B, Q, 2 * KN - 4, D),
                                      Members_End (B, Q, 2 * KN - 3, D),
                                   B, Members_End (B, Q, 2 * KN - 2, D),
                                      Members_End (B, Q, 2 * KN - 1, D)),
        Post => Keys_Ascending (B, Q, KN, D);

   --  One key not greater than the key before it breaks the order.
   procedure Lemma_Keys_Break
     (B : Bytes; Q : Positive; N : Natural; J : Positive; D : Natural)
   with Ghost,
        Pre  => Q in B'First .. B'Last + 1 and then N <= 2**30 - 1
                and then J in 2 .. N
                and then not Lex_Less (B, Members_End (B, Q, 2 * J - 4, D),
                                          Members_End (B, Q, 2 * J - 3, D),
                                       B, Members_End (B, Q, 2 * J - 2, D),
                                          Members_End (B, Q, 2 * J - 1, D)),
        Post => not Keys_Ascending (B, Q, N, D);

   --  The first M keys of N ascending keys are ascending.
   procedure Lemma_Keys_Prefix
     (B : Bytes; Q : Positive; N : Natural; M : Natural; D : Natural)
   with Ghost,
        Pre  => Q in B'First .. B'Last + 1 and then N <= 2**30 - 1
                and then M <= N and then Keys_Ascending (B, Q, N, D),
        Post => Keys_Ascending (B, Q, M, D);

   --  The quantified form of Keys_Ascending: every key after the first
   --  is greater than the key before it.
   procedure Lemma_Keys_All
     (B : Bytes; Q : Positive; N : Natural; D : Natural)
   with Ghost,
        Pre  => Q in B'First .. B'Last + 1 and then N <= 2**30 - 1
                and then Keys_Ascending (B, Q, N, D),
        Post => (for all J in 2 .. N =>
                   Lex_Less (B, Members_End (B, Q, 2 * J - 4, D),
                                Members_End (B, Q, 2 * J - 3, D),
                             B, Members_End (B, Q, 2 * J - 2, D),
                                Members_End (B, Q, 2 * J - 1, D))),
        Subprogram_Variant => (Decreases => N);

   ---------------------------------------------------------------------
   --  Same_Bytes, as the proofs use it: reflexive, symmetric, transitive,
   --  of equal lengths, closed under joins and under sub-slices.
   ---------------------------------------------------------------------

   procedure Lemma_Same_Bytes_Refl (B : Bytes; P : Natural; E : Natural)
   with Ghost,
        Pre  => Slice_OK (B, P, E),
        Post => Same_Bytes (B, P, E, B, P, E);

   procedure Lemma_Same_Bytes_Sym
     (BL : Bytes; PL : Natural; EL : Natural;
      BR : Bytes; PR : Natural; ER : Natural)
   with Ghost,
        Pre  => Slice_OK (BL, PL, EL) and then Slice_OK (BR, PR, ER)
                and then Same_Bytes (BL, PL, EL, BR, PR, ER),
        Post => Same_Bytes (BR, PR, ER, BL, PL, EL);

   procedure Lemma_Same_Bytes_Trans
     (B1 : Bytes; P1 : Natural; E1 : Natural;
      B2 : Bytes; P2 : Natural; E2 : Natural;
      B3 : Bytes; P3 : Natural; E3 : Natural)
   with Ghost,
        Pre  => Slice_OK (B1, P1, E1) and then Slice_OK (B2, P2, E2)
                and then Slice_OK (B3, P3, E3)
                and then Same_Bytes (B1, P1, E1, B2, P2, E2)
                and then Same_Bytes (B2, P2, E2, B3, P3, E3),
        Post => Same_Bytes (B1, P1, E1, B3, P3, E3);

   procedure Lemma_Same_Bytes_Len
     (B1 : Bytes; P1 : Natural; E1 : Natural;
      B2 : Bytes; P2 : Natural; E2 : Natural)
   with Ghost,
        Pre  => Slice_OK (B1, P1, E1) and then Slice_OK (B2, P2, E2)
                and then Same_Bytes (B1, P1, E1, B2, P2, E2),
        Post => E1 - P1 = E2 - P2;

   --  Two equal slices end to end make one.
   procedure Lemma_Same_Bytes_Join
     (B1 : Bytes; P1 : Natural; M1 : Natural; E1 : Natural;
      B2 : Bytes; P2 : Natural; M2 : Natural; E2 : Natural)
   with Ghost,
        Pre  => Slice_OK (B1, P1, M1) and then Slice_OK (B1, M1, E1)
                and then Slice_OK (B2, P2, M2) and then Slice_OK (B2, M2, E2)
                and then Same_Bytes (B1, P1, M1, B2, P2, M2)
                and then Same_Bytes (B1, M1, E1, B2, M2, E2),
        Post => Same_Bytes (B1, P1, E1, B2, P2, E2);

   --  A sub-slice of equal slices is equal, at the corresponding place.
   procedure Lemma_Same_Bytes_Sub
     (B1 : Bytes; P1 : Natural; E1 : Natural;
      B2 : Bytes; P2 : Natural; E2 : Natural;
      Q1 : Natural; F1 : Natural)
   with Ghost,
        Pre  => Slice_OK (B1, P1, E1) and then Slice_OK (B2, P2, E2)
                and then Same_Bytes (B1, P1, E1, B2, P2, E2)
                and then Q1 in P1 .. E1 and then F1 in Q1 .. E1,
        Post => Same_Bytes (B1, Q1, F1, B2, Q1 - P1 + P2, F1 - P1 + P2);

end Cbor_Det.Proof.Det;
