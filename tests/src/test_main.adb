--  cbor_det test runner.
--
--  Copyright (c) 2026, Matt Doughty
--  SPDX-License-Identifier: BSD-3-Clause
--
--  test_main                       the vectors (every cell of the matrix)
--  test_main corpus FILE [TIMES]   the differential corpus
--  test_main heads FILE            the reference's head table
--  test_main exhaustive FILE       every input of up to 3 bytes
--  test_main verdict FILE [ROWS]   the decoder's verdict on the corpus
--                                  (ROWS: the row count the file must have)
--  test_main verdict-exhaustive FILE   ... on every input of up to 3 bytes
--  test_main status FILE [ROWS]    the decoder's Status and Where against
--                                  the status oracle
--
--  The checks that call the library's ghost code run only when the
--  library is compiled with its contracts (the contracts cell). The
--  runner says whether they ran, and fails if the library has its
--  contracts and they did not run, or the other way round, so that a
--  build that silently drops them is caught. Everything runs in a task
--  with a large stack, because the ghost definitions recurse once per
--  member of a container.

with Ada.Command_Line; use Ada.Command_Line;
with Ada.Exceptions;
with Ada.Text_IO;      use Ada.Text_IO;

with Decoder_Tests;
with Decoder_Vectors;
with Differential;
with Ghost_Vectors;
with Head_Vectors;
with Support;

procedure Test_Main is

   --  Set once, by the runner task, before it completes.
   procedure Set_Failed is
   begin
      Set_Exit_Status (Failure);
   end Set_Failed;

   procedure Run_All is
      Ghost_Ran : Boolean;
   begin
      if Argument_Count = 0 then
         Head_Vectors.Run;
         Ghost_Vectors.Run;
         Decoder_Vectors.Run;
         Ghost_Ran := Ghost_Vectors.Ran and then Decoder_Vectors.Ran;
      elsif Argument (1) = "corpus" and then Argument_Count in 2 .. 3 then
         Differential.Corpus
           (Argument (2), (if Argument_Count = 3 then Argument (3) else ""));
         Ghost_Ran := Differential.Ran;
      elsif Argument (1) = "heads" and then Argument_Count = 2 then
         Differential.Heads (Argument (2));
         Ghost_Ran := True;
      elsif Argument (1) = "exhaustive" and then Argument_Count = 2 then
         Differential.Exhaustive (Argument (2));
         Ghost_Ran := Differential.Ran;
      elsif Argument (1) = "verdict" and then Argument_Count in 2 .. 3 then
         Decoder_Tests.Verdict
           (Argument (2), Support.Library_Has_Contracts,
            (if Argument_Count = 3 then Integer'Value (Argument (3))
             else -1));
         Ghost_Ran := True;
      elsif Argument (1) = "verdict-exhaustive" and then Argument_Count = 2
      then
         Decoder_Tests.Verdict_Exhaustive (Argument (2));
         Ghost_Ran := True;
      elsif Argument (1) = "status" and then Argument_Count in 2 .. 3 then
         Decoder_Tests.Status
           (Argument (2),
            (if Argument_Count = 3 then Integer'Value (Argument (3))
             else -1));
         Ghost_Ran := True;
      else
         Put_Line ("usage: test_main [corpus FILE [TIMES] | heads FILE"
                   & " | exhaustive FILE | verdict FILE [ROWS]"
                   & " | verdict-exhaustive FILE | status FILE [ROWS]]");
         Set_Failed;
         return;
      end if;
      declare
         Contracts : constant Boolean := Support.Library_Has_Contracts;
      begin
         Put_Line ("library contracts: "
                   & (if Contracts then "on" else "off")
                   & "; checks of ghost code: "
                   & (if Ghost_Vectors.Ran then "run" else "not run"));
         if Contracts /= Ghost_Vectors.Ran
           or else Contracts /= Decoder_Vectors.Ran
           or else (Contracts and then not Ghost_Ran)
         then
            Put_Line ("FAIL: the checks of ghost code ran in a build"
                      & " that does not match the library's");
            Set_Failed;
         end if;
      end;
      Put_Line ("checks passed:" & Support.Passed'Image & ", failed:"
                & Support.Failed'Image);
      if Support.Failed > 0 then
         Set_Failed;
      end if;
   end Run_All;

   task Runner with Storage_Size => 512 * 1024 * 1024;
   task body Runner is
   begin
      Run_All;
   exception
      when E : others =>
         --  The name of the exception only: its message can hold a path
         --  given on the command line.
         Put_Line ("FAIL: an exception escaped the tests: "
                   & Ada.Exceptions.Exception_Name (E));
         Set_Failed;
   end Runner;

begin
   --  Test_Main returns only when Runner has completed.
   null;
end Test_Main;
