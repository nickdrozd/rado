import BB
import Machine
import Parse
import Program

%default total

Programs : Type
Programs = List String

FastHalt : Programs
FastHalt = [
  "1RB 1LB 1LA 1RH",
  "1RB 1RH 1LB 0RC 1LC 1LA",
  "1RB 1LB 1LA 0LC 1RH 1LD 1RD 0RA",
  "1RB 0LC 1RC 1RD 1LA 0RB 0RE 1RH 1LC 1RA",
  "1RB 3LA 1LA 1RA 2LA 1RH 3RA 3RB",
  "1RB 2LA 1RA 1RA 1LB 1LA 3RB 1RH",
  "1RB 3LA 1LA 1RA 2LA 1RH 3LA 3RB",
  "1RB 3LA 1LA 1RA 2LA 1RH 2RA 3RB",
  "1RB 2RB 3LA 2RA 1LA 3RB 1RH 1LB",
  "1RB 1LC 1RC 1RB 1RD 0LE 1LA 1LD 1RH 0LA"]

-- SlowHalt : Programs
-- SlowHalt = [TM33F, TM33S, TM33Q]

Blankers : Programs
Blankers = [
  "1RB 0RA 1LB 1LA",
  "1RB 1LB 1LA 1LC 1RC 0LC",
  "1RB 0LC 1LD 0LA 1RC 1RD 1LA 0LD"]

runPrograms : Machine _ -> Programs -> IO ()
runPrograms _ [] = do putStrLn ""
runPrograms machine (prog :: rest) = do
  program <- parseProgram prog
  case program of
    Nothing => runPrograms machine rest
    Just program => do
      result <- runOnBlankTape @{machine} program
      putStrLn $ "    " ++ show result
      runPrograms machine rest

runProgramSets : Machine _ -> List Programs -> IO ()
runProgramSets _ [] = pure ()
runProgramSets machine (progs :: rest) = do
  runPrograms machine progs
  runProgramSets machine rest

runMicro : IO ()
runMicro = do
  putStrLn "  Micro"
  runProgramSets MicroMachine [
    FastHalt,
    Blankers]

runMacro : IO ()
runMacro = do
  putStrLn "  Macro"
  runProgramSets MacroMachine [
    FastHalt,
    -- SlowHalt,
    Blankers]

main : IO ()
main = do
  runMicro
  runMacro
