import VqcInLean.Qubit
import VqcInLean.QState
import VqcInLean.QMatrix

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
instance : SMul ℂ (QBra n) where
  smul c ϕ := { mat := c • ϕ.mat }

-- Addition for QBra
instance : Add (QBra n) where
  add ϕ ψ := { mat := ϕ.mat + ψ.mat }

-- Multiplication for QBra
noncomputable instance : HMul (QState n) (QBra n) (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) where
  hMul ϕ ψ := ϕ.mat * ψ.mat

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
lemma smul_apply (c : ℂ) (ϕ : QBra n) (i j) : (c • ϕ) i j = c * ϕ i j := rfl

@[simp]
lemma add_apply (ϕ ψ : QBra n) (i j) : (ϕ + ψ) i j = ϕ i j + ψ i j := rfl

-- Define Kronecker product for QBra
@[simp]
def kronecker (ϕ : QBra n) (ψ : QBra m) : QBra (n + m) :=
  -- Apply kronecker product to the underlying matrices
  let reindexed := QMatrix.reindexToFinMul (ϕ.mat ⊗ₖ ψ.mat)
  { mat := Eq.mp (by ring_nf) reindexed }

def fromVector : {n : ℕ} → Vector ℕ n → QBra n
  | 0, _ => { mat := (1 : Matrix (Fin 1) (Fin 1) ℂ).conjTranspose }
  | n + 1, v =>
    let x := v.head
    let xs := v.tail
    let q : QBra 1 := ⟨(qubit x).mat.conjTranspose⟩
    let rest : QBra n := QBra.fromVector xs
    Eq.mp (by simp [add_comm]) (kronecker q rest)

syntax "⟨" term,* "∣⟩" : term
macro_rules
| `(⟨ $xs:term,* ∣⟩) => do
  let stxList := xs.getElems
  let n := stxList.size
  let sizeProof ← `((by rfl : #[ $[ $stxList],* ].size = $(mkNumLit (toString n))))
  `(fromVector (Vector.mk #[ $[ $stxList],* ] $sizeProof))

#eval ⟨ 0 ∣⟩

#eval ⟨ 0, 1, 1, 0, 1 ∣⟩

@[simp]
lemma fromVectorBra0 : ⟨0∣⟩ = ⟨![![1, 0]]⟩ := by
  ext i j
  simp [QBra.fromVector, finProdFinEquiv, Fin.divNat, Fin.modNat]
  have h1 : ({ toArray := #[0], size_toArray := by rfl }: Vector ℕ 1).head = 0 := by rfl
  fin_cases j
  fin_cases i
  all_goals
    simp [h1]
    try norm_cast

lemma fromVectorBra1 : ⟨1∣⟩ = ⟨![![0, 1]]⟩ := by
  ext i j
  simp [QBra.fromVector, finProdFinEquiv, Fin.divNat, Fin.modNat]
  have h1 : ({ toArray := #[1], size_toArray := by rfl }: Vector ℕ 1).head = 1 := by rfl
  fin_cases j
  fin_cases i
  all_goals
    simp [h1]
    try norm_cast

end QBra
