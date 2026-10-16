--  cbor_det tests: the decoder against the two references in
--  tests/reference, which scripts/decoder-tests.sh runs.
--
--  Copyright (c) 2026, Matt Doughty
--  SPDX-License-Identifier: BSD-3-Clause
--
--  The references' answers are read from files the script writes; the
--  references never see this crate's code. A file that cannot be read is
--  reported by its role and the name of the exception only, never by its
--  path. Nothing here calls ghost code,
--  so every mode runs in every cell; in the contracts cell Check's own
--  postcondition (Accepts, so Det_End) also runs on every call.

package Decoder_Tests is

   --  VERDICT: the reference decoder's corpus, classified by cost_model.py
   --  (hex, end, whole-input verdict, cost class, count). Check's verdict
   --  (Result = Ok) against the whole-input verdict, and Where = Data'Last
   --  + 1 on Ok, at index 1. With Contracts (the library checks Check's
   --  postcondition, which runs Det_End), rows of class "deferred" are
   --  not run, and counted; without, every row is run. A row of class
   --  "unmodelled" is a failure. A file with no row run is a failure
   --  (nothing was compared), and so is one whose row count is not
   --  Expected_Rows (when that is not negative).
   procedure Verdict
     (Path : String; Contracts : Boolean; Expected_Rows : Integer := -1);

   --  VERDICT-EXHAUSTIVE: every input of 0 to 3 bytes, against the
   --  reference's whole-input verdict (the top bit of each byte of the
   --  file exhaustive.py writes).
   procedure Verdict_Exhaustive (Path : String);

   --  STATUS: the status oracle's rows (hex, status, where: 0-based).
   --  Check's Result and Where - Data'First against them, with the
   --  input at index 1, at index 1000 and ending at Index'Last; the
   --  empty input also with null bounds at -1, 0, 1000, Index'Last,
   --  Index'Last + 1, Integer'Last and Integer'First + 1. Counts per
   --  status are printed, and every disagreement is a failure, the first
   --  ones printed with their bytes. An empty file is a failure (nothing
   --  was compared), and so is one whose row count is not Expected_Rows
   --  (when that is not negative).
   procedure Status (Path : String; Expected_Rows : Integer := -1);

end Decoder_Tests;
