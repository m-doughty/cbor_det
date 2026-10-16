--  Deterministic CBOR: the decoder.
--
--  Copyright (c) 2026, Matt Doughty
--  SPDX-License-Identifier: BSD-3-Clause
--
--  Check says whether a buffer holds exactly one deterministic item of
--  the profile and nothing else, and if not, which rule failed and where.
--  Proved: Check returns Ok exactly when Accepts (Data), the range of
--  Where, no run-time error, and termination. Tested, not proved: which
--  Status a rejection reports, and the exact Where (the first fault in
--  decode order: heads in preorder, a map key judged for order when it is
--  complete, before its value, trailing bytes last).

with Cbor_Det.Proof.Det;

package Cbor_Det.Decoder with SPARK_Mode is

   --  P1's predicate: Data is not empty and holds exactly one deterministic
   --  item of the profile, nested at most Max_Depth containers deep, and
   --  nothing after it. Ghost: erased from a production build.
   function Accepts (Data : Bytes) return Boolean is
     (Cbor_Det.Proof.Det.Accept_Whole (Data))
   with Ghost;

   procedure Check (Data : Bytes; Result : out Status; Where : out Integer)
   with Always_Terminates,
        Post => (Result = Ok) = Accepts (Data)
                and then (if Result = Ok then Where = Data'Last + 1
                          elsif Data'Length = 0
                          then Result = Truncated and then Where = Data'First
                          else Where in Data'Range);

end Cbor_Det.Decoder;
