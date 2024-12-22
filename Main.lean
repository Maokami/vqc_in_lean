import VqcInLean
import Mathlib.Data.Matrix.Basic

def testMatrix : Matrix (Fin 2) (Fin 2) ℤ :=
  ![![0, 1], ![2, -1]]

-- Print a matrix element and hello message
-- This is just a test
def main : IO Unit :=
  do
    IO.println "Hello, world!"
    IO.println "Matrix element at (0, 1):"
    IO.println (toString (testMatrix 0 1))
