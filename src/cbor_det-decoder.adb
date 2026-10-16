--  Deterministic CBOR: the decoder.
--
--  Copyright (c) 2026, Matt Doughty
--  SPDX-License-Identifier: BSD-3-Clause
--
--  One pass over the input. Judge judges the item at a position at a
--  depth: it reads the head with the helpers of Cbor_Det.Proof.Heads and
--  Cbor_Det.Proof.Det, checks a length or a count against the bytes left
--  before using it (a map's count against half of them: a division, never
--  a doubling), and judges a container's members in a loop, each by a
--  call one depth down. So it recurses only into nested items, with the
--  depth as its variant, and the stack depends on nesting, not on width:
--  at most Max_Depth + 1 calls are active. A map's keys are put in order
--  by comparing each key's bytes with the previous key's, whose start and
--  end are kept.
--
--  The proof is that Judge computes Det_End (its end, or 0), opened one
--  step at a time by the lemmas of Cbor_Det.Proof.Det, as the clients in
--  Cbor_Det.Proof.Surface do: each body hides the recursive definitions
--  again (their Hide_Info in Cbor_Det.Proof.Det hides them only within
--  that unit). Which Status a rejection reports, and its exact Where, are
--  tested, not proved.

with Cbor_Det.Proof;            use Cbor_Det.Proof;
with Cbor_Det.Proof.Heads;      use Cbor_Det.Proof.Heads;
with Cbor_Det.Proof.Det;        use Cbor_Det.Proof.Det;
with Cbor_Det.Decoder.Counters;

package body Cbor_Det.Decoder with SPARK_Mode is

   --  How a key compares with the key before it.
   type Order is (Less, Equal, Greater);

   --  Compare B (P1 .. E1 - 1) with B (P2 .. E2 - 1), bytewise.
   procedure Compare_Keys
     (B      : Bytes;
      P1     : Positive;
      E1     : Positive;
      P2     : Positive;
      E2     : Positive;
      Result : out Order)
   with Pre  => Slice_OK (B, P1, E1) and then Slice_OK (B, P2, E2),
        Post => (Result = Less) = Lex_Less (B, P1, E1, B, P2, E2),
        Always_Terminates;

   --  The item at P, at depth D: E is its end (Det_End), or 0 when it is
   --  refused, and then S is the rule and W the position of the fault.
   procedure Judge
     (B : Bytes;
      P : Positive;
      D : Natural;
      E : out Ext;
      S : out Status;
      W : out Positive)
   with Pre  => P in B'Range,
        Post => E = Det_End (B, P, D)
                and then (if E = 0 then S /= Ok and then W in B'Range),
        Subprogram_Variant => (Decreases => D),
        Always_Terminates;

   ------------------
   -- Compare_Keys --
   ------------------

   procedure Compare_Keys
     (B      : Bytes;
      P1     : Positive;
      E1     : Positive;
      P2     : Positive;
      E2     : Positive;
      Result : out Order)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
      I1 : Positive := P1;
      I2 : Positive := P2;
   begin
      Counters.Add_Comparison;
      loop
         pragma Loop_Invariant (I1 in P1 .. E1 and then I2 in P2 .. E2);
         pragma Loop_Invariant
           (Lex_Less (B, P1, E1, B, P2, E2)
            = Lex_Less (B, I1, E1, B, I2, E2));
         pragma Loop_Variant (Increases => I1);
         Lemma_Lex_Step (B, I1, E1, B, I2, E2);
         if I1 = E1 then
            Result := (if I2 < E2 then Less else Equal);
            return;
         elsif I2 = E2 then
            Result := Greater;
            return;
         end if;
         Counters.Add_Compared (1);
         if B (I1) /= B (I2) then
            Result := (if B (I1) < B (I2) then Less else Greater);
            return;
         end if;
         I1 := I1 + 1;
         I2 := I2 + 1;
      end loop;
   end Compare_Keys;

   -----------
   -- Judge --
   -----------

   procedure Judge
     (B : Bytes;
      P : Positive;
      D : Natural;
      E : out Ext;
      S : out Status;
      W : out Positive)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Shortest);
      IB : constant Byte    := B (P);
      L  : constant Natural := Head_Len (IB);
   begin
      E := 0;
      S := Ok;
      W := P;
      Lemma_Det_Step (B, P, D);

      --  The head's rules, in the order of the precedence table.
      if Info_Of (IB) in 28 .. 30 then
         S := Reserved_Info;
         return;
      elsif Info_Of (IB) = 31 then
         S := Indefinite_Length;
         return;
      elsif Remaining (B, P) < L then
         S := Truncated;
         return;
      end if;
      Counters.Add_Parsed (L);
      if Major_Of (IB) = 6 then
         S := Unsupported_Type;
         return;
      elsif Major_Of (IB) = 7 then
         if Info_Of (IB) in 20 .. 22 then
            E := P + 1;
         else
            S := Unsupported_Simple;
         end if;
         return;
      elsif not Shortest (B, P) then
         S := Non_Shortest;
         return;
      end if;

      declare
         R : constant Natural := Remaining (B, P) - L;
      begin
         --  Integers.
         if Major_Of (IB) in 0 | 1 then
            E := P + L;
            return;
         end if;

         --  Strings: the length against the bytes left.
         if Major_Of (IB) in 2 | 3 then
            if Arg_Fits (B, P, R) then
               E := P + L + Arg_Nat (B, P);
               Counters.Add_Parsed (Arg_Nat (B, P));
            else
               S := Truncated;
            end if;
            return;
         end if;

         --  Containers: the count against the bytes left (a map's against
         --  half of them), then the depth, then the members in a loop.
         declare
            Is_Map : constant Boolean  := Major_Of (IB) = 5;
            Q0     : constant Positive := P + L;  --  members start here
            A      : Natural;                     --  the argument
            N      : Natural;                     --  members to read
            Q      : Positive := Q0;              --  next member starts here
            PKS    : Positive := Q0;              --  last key, start
            PKE    : Positive := Q0;              --  last key, end
            KN     : Natural  := 0;               --  keys read so far
            ME     : Ext;
            MS     : Status;
            MW     : Positive;
            Ord    : Order;
         begin
            if not Is_Map then
               if not Arg_Fits (B, P, R) then
                  S := Truncated;
                  return;
               end if;
               A := Arg_Nat (B, P);
               N := A;
            else
               if not Arg_Fits (B, P, R / 2) then
                  S := Truncated;
                  return;
               end if;
               A := Arg_Nat (B, P);
               N := 2 * A;
            end if;
            if D = 0 then
               S := Too_Deep;
               return;
            end if;
            Lemma_Members_Start (B, Q0, D - 1);
            Lemma_Keys_Step (B, Q0, 0, D - 1);
            for I in 1 .. N loop
               Lemma_Members_Step (B, Q0, I, D - 1);
               if Q > B'Last then
                  --  A member is missing: the container is cut short.
                  Lemma_Members_Zero (B, Q0, I, N, D - 1);
                  S := Truncated;
                  return;
               end if;
               Judge (B, Q, D - 1, ME, MS, MW);
               pragma Assert (Members_End (B, Q0, I, D - 1) = ME);
               if ME = 0 then
                  Lemma_Members_Zero (B, Q0, I, N, D - 1);
                  S := MS;
                  W := MW;
                  return;
               end if;
               if Is_Map and then I mod 2 = 1 then
                  --  A key, complete: its order before its value.
                  if KN >= 1 then
                     Compare_Keys (B, PKS, PKE, Q, ME, Ord);
                     if Ord /= Less then
                        pragma Assert (I = 2 * KN + 1);
                        Lemma_Keys_Break (B, Q0, A, KN + 1, D - 1);
                        S := (if Ord = Equal then Duplicate_Key
                              else Unsorted_Key);
                        W := Q;
                        return;
                     end if;
                  end if;
                  KN  := KN + 1;
                  PKS := Q;
                  PKE := ME;
                  if KN >= 2 then
                     Lemma_Keys_Extend (B, Q0, KN, D - 1);
                  else
                     Lemma_Keys_Step (B, Q0, KN, D - 1);
                  end if;
               end if;
               Q := ME;
               pragma Loop_Invariant (Q = Members_End (B, Q0, I, D - 1));
               pragma Loop_Invariant
                 (if Is_Map
                  then I in 2 * KN - 1 .. 2 * KN
                       and then PKS = Members_End (B, Q0, 2 * KN - 2, D - 1)
                       and then PKE = Members_End (B, Q0, 2 * KN - 1, D - 1)
                       and then PKE in PKS + 1 .. B'Last + 1);
               pragma Loop_Invariant
                 (if Is_Map then Keys_Ascending (B, Q0, KN, D - 1));
            end loop;
            E := Q;
         end;
      end;
   end Judge;

   -----------
   -- Check --
   -----------

   procedure Check (Data : Bytes; Result : out Status; Where : out Integer)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
      E : Ext;
      S : Status;
      W : Positive;
   begin
      if Data'Length = 0 then
         Result := Truncated;
         Where := Data'First;
         return;
      end if;
      Judge (Data, Data'First, Max_Depth, E, S, W);
      if E = 0 then
         Result := S;
         Where := W;
      elsif E <= Data'Last then
         --  One item, and bytes after it.
         Result := Trailing_Bytes;
         Where := E;
      else
         Result := Ok;
         Where := Data'Last + 1;
      end if;
   end Check;

end Cbor_Det.Decoder;
