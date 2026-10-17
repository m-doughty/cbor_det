--  cbor_det tests: the value relation Same against the denotation oracle
--  in tests/reference, which scripts/model-tests.sh runs.
--
--  Copyright (c) 2026, Matt Doughty
--  SPDX-License-Identifier: BSD-3-Clause
--
--  The oracle's labels are read from files the script writes; the oracle
--  never sees this crate's code. The mode calls the library's ghost code
--  (Accept_Whole, Same and the uniqueness lemmas), so it runs only in the
--  contracts cell (Ran tells); elsewhere, and on a file that leaves
--  nothing to compare, it fails: a run that compared nothing is never a
--  pass.

package Model_Pairs is

   --  SAME: the oracle's pair file. Lines that start with "#" are its
   --  header; every other line is two inputs in hexadecimal and the
   --  oracle's label, separated by single spaces: S when the two denote
   --  the same value, D when they do not. Per row: both inputs must be
   --  accepted whole (Accept_Whole); Same (B1, B1'First, B2, B2'First,
   --  Max_Depth) must be True for S and False for D, and so must Same
   --  with the second input rebased to start at index Rebased_First. On
   --  the rebased pair the lemmas run, so that their contracts are
   --  checked on it: on an S row Lemma_CU_Whole (first input, rebased
   --  copy) and Lemma_Same_Of_Bytes_Whole (rebased copy, first input); on
   --  a D row Lemma_Same_Iff_Bytes_Whole (first input, rebased copy).
   --  Rows must be the number of data lines and Same_Rows the number
   --  of S lines (the counts the script pins); a negative value is not
   --  checked.
   procedure Same_Pairs (Path : String; Rows : Integer; Same_Rows : Integer);

   Rebased_First : constant := 1_000;

   function Ran return Boolean;

end Model_Pairs;
