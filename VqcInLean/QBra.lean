import VqcInLean.Qubit
import VqcInLean.QState

import Mathlib.Tactic
import Mathlib.Data.Matrix.Kronecker

open Complex Matrix Kronecker Qubit QState Lean.Syntax

-- Bra structure: 1x2ⁿ complex matrix (the conjugate transpose of QState n)
structure QBra (n : ℕ) where
  mat : Matrix (Fin 1) (Fin (2 ^ n)) ℂ

namespace QBra

instance : Repr (QBra n) where
  reprPrec _ _ := s!"QBra with {n} qubits"

-- Define coercion to Matrix
instance : Coe (QBra n) (Matrix (Fin 1) (Fin (2 ^ n)) ℂ) where
  coe := QBra.mat

-- Make QBra callable as a function
instance : CoeFun (QBra n) (λ _ => Fin 1 → Fin (2 ^ n) → ℂ) where
  coe ϕ := λ i j => ϕ.mat i j

-- Scalar multiplication for QBra
instance : HMul ℂ (QBra n) (QBra n) where
  hMul c ϕ := { mat := c • ϕ.mat }

-- Addition for QBra
instance : HAdd (QBra n) (QBra n) (QBra n) where
  hAdd ϕ ψ := { mat := ϕ.mat + ψ.mat }

-- Multiplication for QBra with matrices
noncomputable instance : HMul (Matrix (Fin 1) (Fin 1) ℂ) (QBra n) (QBra n) where
  hMul u ϕ := { mat := u * ϕ.mat }

@[ext]
lemma ext {n : ℕ} {ϕ ψ : QBra n} (h : ∀ i j, ϕ i j = ψ i j) : ϕ = ψ := by
  cases ϕ
  cases ψ
  simp_all
  ext i j
  exact h i j

@[simp]
lemma eq_coe (ϕ : QBra n) :
    ϕ.mat = (ϕ : Matrix (Fin 1) (Fin (2 ^ n)) ℂ) := rfl

@[simp]
lemma apply_eq_coe (ϕ : QBra n) (i j) :
    ϕ.mat i j = (ϕ : Matrix (Fin 1) (Fin (2 ^ n)) ℂ) i j := rfl

@[simp]
lemma smul_apply (c : ℂ) (ϕ : QBra n) (i j) : (c * ϕ) i j = c * ϕ i j := rfl

@[simp]
lemma add_apply (ϕ ψ : QBra n) (i j) : (ϕ + ψ) i j = ϕ i j + ψ i j := rfl

-- Define Kronecker product for QBra
@[simp]
def kronecker (ϕ : QBra n) (ψ : QBra m) : QBra (n + m) :=
  -- Apply kronecker product to the underlying matrices
  let product := ϕ.mat ⊗ₖ ψ.mat
  -- Reindex the matrix to match the new dimensions
  let reindexed := product.reindex finProdFinEquiv finProdFinEquiv
  { mat := Eq.mp (by ring_nf) reindexed }

def fromQState (ϕ : QState n) : QBra n :=
  { mat := ϕ.matᴴ }

def fromVector : {n : ℕ} → Vector ℕ n → QBra n
  | 0, _ => { mat := (1 : Matrix (Fin 1) (Fin 1) ℂ).conjTranspose }
  | n + 1, v =>
    let x := v.head
    let xs := v.tail
    let q : QState 1 := QState.fromVector (Vector.mk #[x] rfl)
    let rest : QState n := QState.fromVector xs
    let b' : QBra 1 := fromQState q
    let rest' : QBra n := fromQState rest
    Eq.mp (by simp [add_comm]) (kronecker b' rest')

-- TODO : I want to use "⟨" "∣" syntax for this, but it's not working.
-- So currently using "|" instead. I need to revise the syntax for QState and QBra.
macro "⟨" xs:term,* "|" : term => do
  let stxList := xs.getElems
  let n := stxList.size
  let sizeProof ← `((by rfl : #[ $[ $stxList],* ].size = $(mkNumLit (toString n))))
  `(QBra.fromVector (Vector.mk #[ $[ $stxList],* ] $sizeProof))

#eval ⟨0|
#eval ⟨0, 1, 1, 0, 1|

end QBra
