--  cbor_det tests: the differential test against the reference decoder in
--  tests/reference, which scripts/differential.sh runs.
--
--  Copyright (c) 2026, Matt Doughty
--  SPDX-License-Identifier: BSD-3-Clause
--
--  The reference's verdicts are read from files the script writes; the
--  reference never sees this crate's code, and this crate never sees the
--  reference's. Each mode prints its counts and adds its failures to the
--  runner's. Corpus and Exhaustive call the library's ghost code, so they
--  run only in the contracts cell (Ran tells); elsewhere, and on a file
--  that leaves nothing to compare, a mode fails: a run that compared
--  nothing is never a pass.

package Differential is

   --  CORPUS: the reference's corpus, classified by cost_model.py: per
   --  line the bytes in hexadecimal, the reference's end of the item at
   --  the first byte (-1 when refused), its whole-input verdict (0 or 1),
   --  the cost class and the predicted count of calls. Rows of class
   --  "run" are compared, separately: Det_End's end against the end, and
   --  Accept_Whole against the verdict, at index 1; also at the top of
   --  Index when the count is at most Top_Limit; and the lemmas run on
   --  the accepted item when the count is at most Lemma_Limit. Rows of
   --  class "deferred" (too costly to run) are counted and printed;
   --  a row of class "unmodelled" (the cost model's end differs from the
   --  reference's) is a failure.
   --  With Timings, the seconds each compared row took at index 1 are
   --  written there, one "count seconds" line per row.
   procedure Corpus (Path : String; Timings : String := "");

   Top_Limit   : constant := 1_000_000;
   Lemma_Limit : constant := 20_000;

   --  HEADS: the reference's head table: per line the bytes and either
   --  NONE or the major type, argument and length of the head at the
   --  first byte, for major types 0 to 5 only. Compared with Head_OK,
   --  Head_Len, Major_Of and Arg.
   procedure Heads (Path : String);

   --  EXHAUSTIVE: the reference's verdict on every input of 0 to 3 bytes,
   --  in order of length then value (big endian), one byte each: the end
   --  plus one (0 when refused) in the low 7 bits, the whole-input
   --  verdict in the top bit. Compared with Det_End and Accept_Whole.
   procedure Exhaustive (Path : String);

   function Ran return Boolean;

end Differential;
