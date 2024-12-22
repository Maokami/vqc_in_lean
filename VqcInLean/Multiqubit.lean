import VqcInLean.Qubit

import Mathlib.Tactic
import Mathlib.Data.Matrix.Kronecker

open Complex Matrix Kronecker Qubit

-- Multiqubit definition: 2ⁿx1 complex matrix
structure QState (n : ℕ) where
  mat : Matrix (Fin (2 ^ n)) (Fin 1) ℂ

instance : Repr (QState n) where
  reprPrec _ _ := s!"QState with {n} qubits"

namespace Multiqubit

-- Define coercion to Matrix
instance : Coe (QState n) (Matrix (Fin (2 ^ n)) (Fin 1) ℂ) where
  coe := QState.mat

-- Make Qubit callable as a function
instance : CoeFun (QState n) (λ _ => Fin n → Fin 1 → ℂ) where
  coe ϕ := λ i j => ϕ.mat i j

-- Coerce Qubit to QState 1
instance : Coe Qubit (QState 1) where
  coe q := { mat := q.mat }

-- Define Kronecker product for QState
@[simp]
def kronecker (ϕ : QState n) (ψ : QState m) : QState (n + m) :=
  -- Apply kronecker product to the underlying matrices
  let product := ϕ.mat ⊗ₖ ψ.mat
  -- Reindex the matrix to match the new dimensions
  let reindexed := product.reindex finProdFinEquiv finProdFinEquiv
  { mat := Eq.mp (by ring_nf) reindexed }

-- Add notation for Kronecker product
scoped infixl:100 " ⊗ₖ " => Multiqubit.kronecker

def fromVector : {n : ℕ} → Vector ℕ n → QState n
  | 0, _ => { mat := (1 : Matrix (Fin 1) (Fin 1) ℂ) } -- Identity for empty vector
  | n + 1, v =>
    let x := v.head
    let xs := v.tail
    let q : QState 1 := (qubit x : QState 1)
    let rest : QState n := fromVector xs
    Eq.mp (by simp [add_comm]) (q ⊗ₖ rest : QState (1 + n))

macro "∣" xs:term,* "⟩" : term => do
  `(fromVector (Vector.mk #[ $(xs),* ] rfl))

#eval ∣0, 1, 0⟩
