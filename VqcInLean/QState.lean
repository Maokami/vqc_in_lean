import VqcInLean.Qubit

import Mathlib.Tactic
import Mathlib.Data.Matrix.Kronecker

open Complex Matrix Kronecker Qubit Lean.Syntax

-- Multiqubit definition: 2ⁿx1 complex matrix
structure QState (n : ℕ) where
  mat : Matrix (Fin (2 ^ n)) (Fin 1) ℂ

namespace QState

@[ext]
lemma ext {n : ℕ} {ϕ ψ : QState n} (h : ϕ.mat = ψ.mat) : ϕ = ψ := by
  cases ϕ
  cases ψ
  simp_all

instance : Repr (QState n) where
  reprPrec _ _ := s!"QState with {n} qubits"

-- Define coercion to Matrix
instance : Coe (QState n) (Matrix (Fin (2 ^ n)) (Fin 1) ℂ) where
  coe := QState.mat

-- Make Qubit callable as a function
instance : CoeFun (QState n) (λ _ => Fin n → Fin 1 → ℂ) where
  coe ϕ := λ i j => ϕ.mat i j

-- Coerce Qubit to QState 1
instance : Coe Qubit (QState 1) where
  coe q := { mat := q.mat }

-- Scalar multiplication for QState
instance : HMul ℂ (QState n) (QState n) where
  hMul c ϕ := { mat := c • ϕ.mat }

-- Addition for QState
instance : HAdd (QState n) (QState n) (QState n) where
  hAdd ϕ ψ := { mat := ϕ.mat + ψ.mat }

-- Define Kronecker product for QState
@[simp]
def kronecker (ϕ : QState n) (ψ : QState m) : QState (n + m) :=
  -- Apply kronecker product to the underlying matrices
  let product := ϕ.mat ⊗ₖ ψ.mat
  -- Reindex the matrix to match the new dimensions
  let reindexed := product.reindex finProdFinEquiv finProdFinEquiv
  { mat := Eq.mp (by ring_nf) reindexed }

-- Add notation for Kronecker product
scoped infixl:100 " ⊗ₖ " => QState.kronecker

def fromVector : {n : ℕ} → Vector ℕ n → QState n
  | 0, _ => { mat := (1 : Matrix (Fin 1) (Fin 1) ℂ) } -- Identity for empty vector
  | n + 1, v =>
    let x := v.head
    let xs := v.tail
    let q : QState 1 := (qubit x : QState 1)
    let rest : QState n := fromVector xs
    Eq.mp (by simp [add_comm]) (q ⊗ₖ rest : QState (1 + n))

macro "∣" xs:term,* "⟩" : term => do
  -- Get the list of terms from `xs:term,*`
  let stxList := xs.getElems
  -- (For example, xs.getElems would return [Syntax| 0, Syntax| 1, Syntax| 2])

  -- Compute the size of the array
  let n := stxList.size

  -- Create a proof for “#[ $[ $stxList],* ].size = n”
  -- This uses `by decide` or `by native_decide` to handle the proof
  let sizeProof ← `((by decide : #[ $[ $stxList],* ].size = $(mkNumLit (toString n))))

  -- Final result: fromVector (Vector.mk #[…] sizeProof)
  `(fromVector (Vector.mk #[ $[ $stxList],* ] $sizeProof))

#eval ∣0, 0, 1, 0⟩

-- TODO
lemma test_qubits : ∣0, 1⟩ = ∣0⟩ ⊗ₖ ∣1⟩ := by sorry

/-- Lemma on decomposition of a 2-qubit state into basis states. -/
lemma qubit_decomposition2 (ϕ : QState 2) :
  ∃ (α β γ δ : ℂ), ϕ = α * ∣0, 0⟩ + β * ∣0, 1⟩ + γ * ∣1, 0⟩ + δ * ∣1, 1⟩ := by
  let α := ϕ 0 0   -- row=0, col=0
  let β := ϕ 1 0   -- row=1, col=0
  let γ := ϕ 2 0   -- row=2, col=0
  let δ := ϕ 3 0   -- row=3, col=0

  -- Provide them as witnesses in the existential statement.
  use α, β, γ, δ

  ext i j
  fin_cases j
  fin_cases i
  all_goals
    dsimp
    sorry

/-- Define the CNOT gate as a unitary matrix. -/
def CNOT : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![1, 0, 0, 0],
    ![0, 1, 0, 0],
    ![0, 0, 0, 1],
    ![0, 0, 1, 0]]


end QState
