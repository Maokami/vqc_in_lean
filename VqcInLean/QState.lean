import VqcInLean.Qubit
import VqcInLean.QMatrix

import Mathlib.Tactic
import Mathlib.Data.Matrix.Kronecker

open Complex Matrix Kronecker Qubit Lean.Syntax QMatrix

-- Multiqubit definition: 2ⁿx1 complex matrix
structure QState (n : ℕ) where
  mat : Matrix (Fin (2 ^ n)) (Fin 1) ℂ

namespace QState

instance : Repr (QState n) where
  reprPrec _ _ := s!"QState with {n} qubits"

-- Define coercion to Matrix
instance : Coe (QState n) (Matrix (Fin (2 ^ n)) (Fin 1) ℂ) where
  coe := QState.mat

-- Make Qubit callable as a function
instance : CoeFun (QState n) (λ _ => Fin (2 ^ n) → Fin 1 → ℂ) where
  coe ϕ := λ i j => ϕ.mat i j

-- Coerce Qubit to QState 1
instance : Coe Qubit (QState 1) where
  coe q := { mat := q.mat }

-- Scalar multiplication for QState
instance : SMul ℂ (QState n) where
  smul c ϕ := { mat := c • ϕ.mat }

-- Addition for QState
instance : Add (QState n) where
  add ϕ ψ := { mat := ϕ.mat + ψ.mat }

-- Multiplication for QState
noncomputable instance : HMul (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (QState n) (QState n) where
  hMul u ϕ := { mat := u * ϕ.mat }

@[ext]
lemma ext {n : ℕ} {ϕ ψ : QState n} (h : ∀ i j, ϕ i j = ψ i j) : ϕ = ψ := by
  cases ϕ
  cases ψ
  simp_all
  ext i j
  exact h i j

@[simp]
lemma eq_coe (ϕ : QState n) :
    ϕ.mat = (ϕ : Matrix (Fin (2 ^ n)) (Fin 1) ℂ) := rfl

@[simp]
lemma apply_eq_coe (ϕ : QState n) (i j) :
    ϕ.mat i j = (ϕ : Matrix (Fin (2 ^ n)) (Fin 1) ℂ) i j := rfl

@[simp]
lemma smul_apply (c : ℂ) (ϕ : QState n) (i j) : (c • ϕ) i j = c * ϕ i j := rfl

@[simp]
lemma add_apply (ϕ ψ : QState n) (i j) : (ϕ + ψ) i j = ϕ i j + ψ i j := rfl

-- Define Kronecker product for QState
@[simp]
def kronecker (ϕ : QState n) (ψ : QState m) : QState (n + m) :=
  -- Reindex the matrix to match the new dimensions
  let reindexed := QMatrix.reindexToFinMul (ϕ.mat ⊗ₖ ψ.mat)
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

macro "ket∣" xs:term,* "⟩": term => do
  let stxList := xs.getElems
  let n := stxList.size
  let sizeProof ← `((by rfl : #[ $[ $stxList],* ].size = $(mkNumLit (toString n))))
  `(fromVector (Vector.mk #[ $[ $stxList],* ] $sizeProof))

#eval ket∣ 0 ⟩
#eval ket∣ 0, 0, 1, 0 ⟩

lemma test_qubits : ket∣0, 1⟩ = ket∣0⟩ ⊗ₖ ket∣1⟩ := by
  ext i j
  simp [fromVector, finProdFinEquiv, Fin.divNat, Fin.modNat]
  have h1 : ({ toArray := #[0, 1], size_toArray := by rfl }: Vector ℕ 2).head = 0 := by rfl
  have h2 : ({ toArray := #[0, 1], size_toArray := by rfl }: Vector ℕ 2).tail.head = 1 := by rfl
  have hh1 : ({ toArray := #[0], size_toArray := by rfl }: Vector ℕ 1).head = 0 := by rfl
  have hh2 : ({ toArray := #[1], size_toArray := by rfl }: Vector ℕ 1).head = 1 := by rfl
  have fun_id_apply {α : Type} (x : α) : (fun i ↦ i) x = x := rfl
  have hone : ∀ x y : Fin 1, (1 : Matrix (Fin 1) (Fin 1) ℂ) x y = 1 := by
    intro x y
    fin_cases x
    fin_cases y
    rfl

  fin_cases j
  fin_cases i
  all_goals
    simp [h1, h2, hh1, hh2, if_true, if_false]

  rw [fun_id_apply]
  simp_all

-- TODO : How to unify the following lemmas into a single lemma?
-- fromVector00 = ![1,0,0,0]
lemma fromVector00:
    ket∣0, 0⟩ = ⟨![1,0,0,0]⟩  := by
  ext i j
  simp [fromVector, finProdFinEquiv, Fin.divNat, Fin.modNat]

  have h1 : ({ toArray := #[0, 0], size_toArray := by rfl }: Vector ℕ 2).head = 0 := by rfl
  have h2 : ({ toArray := #[0, 0], size_toArray := by rfl }: Vector ℕ 2).tail.head = 0 := by rfl

  fin_cases j
  fin_cases i
  all_goals
    simp [h1, h2]
    try norm_cast

lemma fromVector01:
    ket∣0, 1⟩ = ⟨![0,1,0,0]⟩  := by
  ext i j
  simp [fromVector, finProdFinEquiv, Fin.divNat, Fin.modNat]

  have h1 : ({ toArray := #[0, 1], size_toArray := by rfl }: Vector ℕ 2).head = 0 := by rfl
  have h2 : ({ toArray := #[0, 1], size_toArray := by rfl }: Vector ℕ 2).tail.head = 1 := by rfl

  fin_cases j
  fin_cases i
  all_goals
    simp [h1, h2]
    try norm_cast

lemma fromVector10 :
    ket∣1, 0⟩ = ⟨![0,0,1,0]⟩  := by
  ext i j
  simp [fromVector, finProdFinEquiv, Fin.divNat, Fin.modNat]

  have h1 : ({ toArray := #[1, 0], size_toArray := by rfl }: Vector ℕ 2).head = 1 := by rfl
  have h2 : ({ toArray := #[1, 0], size_toArray := by rfl }: Vector ℕ 2).tail.head = 0 := by rfl

  fin_cases i
  all_goals
    simp [h1, h2]
    try norm_cast

lemma fromVector11 :
    ket∣1, 1⟩ = ⟨![0,0,0,1]⟩  := by
  ext i j
  simp [fromVector, finProdFinEquiv, Fin.divNat, Fin.modNat]

  have h1 : ({ toArray := #[1, 1], size_toArray := by rfl }: Vector ℕ 2).head = 1 := by rfl
  have h2 : ({ toArray := #[1, 1], size_toArray := by rfl }: Vector ℕ 2).tail.head = 1 := by rfl

  fin_cases i
  all_goals
    simp [h1, h2]
    try norm_cast

/-- Lemma on decomposition of a 2-qubit state into basis states. -/
theorem qubit_decomposition2 (ϕ : QState 2) :
  ∃ (α β γ δ : ℂ), ϕ = α • ket∣0, 0⟩ + β • ket∣0, 1⟩ + γ • ket∣1, 0⟩ + δ • ket∣1, 1⟩ := by
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
    simp [fromVector00, fromVector01, fromVector10, fromVector11]

/-- Define the CNOT gate as a unitary matrix. -/
def CNOT : Matrix (Fin (2 ^ 2)) (Fin (2 ^ 2)) ℂ :=
  ![![1, 0, 0, 0],
    ![0, 1, 0, 0],
    ![0, 0, 0, 1],
    ![0, 0, 1, 0]]

-- Define the basis states for 2 qubits
def basis2 (i : Fin 4) : QState 2 :=
  match i with
  | 0 => ket∣0, 0⟩
  | 1 => ket∣0, 1⟩
  | 2 => ket∣1, 0⟩
  | 3 => ket∣1, 1⟩

-- Simplify the action of CNOT on basis states
lemma CNOT_basis_action (i : Fin 4) :
  CNOT * basis2 i =
    match i with
    | 0 => basis2 0
    | 1 => basis2 1
    | 2 => basis2 3
    | 3 => basis2 2
:= by
  fin_cases i
  all_goals
    simp [fromVector00, fromVector01, fromVector10, fromVector11,
    CNOT, basis2, instHMulMatrixFinHPowNatOfNatComplex]
    ext i j
    fin_cases j
    fin_cases i
    all_goals
      simp only [HMul.hMul]
      simp

lemma CNOT00 : CNOT * ket∣0, 0⟩ = ket∣0, 0⟩ :=
  CNOT_basis_action 0

lemma CNOT01 : CNOT * ket∣0, 1⟩ = ket∣0, 1⟩ :=
  CNOT_basis_action 1

lemma CNOT10 : CNOT * ket∣1, 0⟩ = ket∣1, 1⟩ :=
  CNOT_basis_action 2

lemma CNOT11 : CNOT * ket∣1, 1⟩ = ket∣1, 0⟩ :=
  CNOT_basis_action 3

-- Definition of a Bell state.
noncomputable def bell : QState 2 :=
   (1 / √2 : ℂ) • ket∣0, 0⟩ + (1 / √2 : ℂ) • ket∣1, 1⟩

-- -- Definition of a Bell state generated using CNOT and H gate.
-- def bell' : QState 2 :=
--   -- Define H ⊗ₖ 1
--   let H1: Matrix (Fin (2 ^ 2)) (Fin (2 ^ 2)) ℂ := H ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)
--   CNOT * H1 * ∣0, 0⟩
--
-- -- Prove that bell = bell'
-- lemma bell_bell' : bell = bell' := by
--   sorry

-- Define additional useful 2-qubit gates.
def NOTC : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![1, 0, 0, 0],
    ![0, 0, 0, 1],
    ![0, 0, 1, 0],
    ![0, 1, 0, 0]]

def CZ : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![1, 0, 0, 0],
    ![0, 1, 0, 0],
    ![0, 0, 1, 0],
    ![0, 0, 0, -1]]

def SWAP : Matrix (Fin (2 ^ 2)) (Fin (2 ^ 2)) ℂ :=
  ![![1, 0, 0, 0],
    ![0, 0, 1, 0],
    ![0, 1, 0, 0],
    ![0, 0, 0, 1]]

-- TODO
-- SWAP gate swaps qubits.
lemma SWAPxy : ∀ x y : Fin 2, SWAP * (ket∣x, y⟩ : QState 2) = ket∣y, x⟩ := by
  intros x y
  fin_cases x
  all_goals
    fin_cases y
    all_goals
      simp [fromVector00, fromVector01, fromVector10, fromVector11, SWAP]
      ext i j
      fin_cases i
      fin_cases j
      all_goals
        simp only [HMul.hMul]
        simp

-- Define total measurement on 1 qubit.
inductive measure' : QState 1 → ℝ × QState 1 → Prop
| measure0 (ϕ : QState 1) (α β : ℂ) :
    ϕ = α • ket∣0⟩ + β • ket∣1⟩ →
    measure' ϕ (normSq α, ket∣0⟩)
| measure1 (ϕ : QState 1) (α β : ℂ) :
    ϕ = α • ket∣0⟩ + β • ket∣1⟩ →
    measure' ϕ (normSq β, ket∣1⟩)

-- Define total measurement on 2 qubits.
inductive measure_total : QState 2 → ℝ × QState 2 → Prop
| measure00 (ϕ : QState 2) (α β γ δ : ℂ) :
    ϕ = α • ket∣0, 0⟩ + β • ket∣0, 1⟩ + γ • ket∣1, 0⟩ + δ • ket∣1, 1⟩ →
    measure_total ϕ (normSq α, ket∣0, 0⟩)
| measure01 (ϕ : QState 2) (α β γ δ : ℂ) :
    ϕ = α • ket∣0, 0⟩ + β • ket∣0, 1⟩ + γ • ket∣1, 0⟩ + δ • ket∣1, 1⟩ →
    measure_total ϕ (normSq β, ket∣0, 1⟩)
| measure10 (ϕ : QState 2) (α β γ δ : ℂ) :
    ϕ = α • ket∣0, 0⟩ + β • ket∣0, 1⟩ + γ • ket∣1, 0⟩ + δ • ket∣1, 1⟩ →
    measure_total ϕ (normSq γ, ket∣1, 0⟩)
| measure11 (ϕ : QState 2) (α β γ δ : ℂ) :
    ϕ = α • ket∣0, 0⟩ + β • ket∣0, 1⟩ + γ • ket∣1, 0⟩ + δ • ket∣1, 1⟩ →
    measure_total ϕ (normSq δ, ket∣1, 1⟩)

inductive measure_partial : ℕ → QState 2 → ℝ × QState 2 → Prop
| measure_p_1_0 (ϕ ϕ' : QState 2) (α β γ δ : ℂ) (p : ℝ) :
    ϕ = α • ket∣0, 0⟩ + β • ket∣0, 1⟩ + γ • ket∣1, 0⟩ + δ • ket∣1, 1⟩ →
    p = (normSq α + normSq β) →
    ϕ' = (1 / √p : ℂ) • (α • ket∣0, 0⟩ + β • ket∣0, 1⟩) →
    measure_partial 1 ϕ (p, ϕ')
| measure_p_1_1 (ϕ ϕ' : QState 2) (α β γ δ : ℂ) (p : ℝ) :
    ϕ = α • ket∣0, 0⟩ + β • ket∣0, 1⟩ + γ • ket∣1, 0⟩ + δ • ket∣1, 1⟩ →
    p = (normSq γ + normSq δ) →
    ϕ' = (1 / √p : ℂ) • (γ • ket∣1, 0⟩ + δ • ket∣1, 1⟩) →
    measure_partial 1 ϕ (p, ϕ')
| measure_p_2_0 (ϕ ϕ' : QState 2) (α β γ δ : ℂ) (p : ℝ) :
    ϕ = α • ket∣0, 0⟩ + β • ket∣0, 1⟩ + γ • ket∣1, 0⟩ + δ • ket∣1, 1⟩ →
    p = (normSq α + normSq γ) →
    ϕ' = (1 / √p : ℂ) • (α • ket∣0, 0⟩ + γ • ket∣1, 0⟩) →
    measure_partial 2 ϕ (p, ϕ')
| measure_p_2_1 (ϕ ϕ' : QState 2) (α β γ δ : ℂ) (p : ℝ) :
    ϕ = α • ket∣0, 0⟩ + β • ket∣0, 1⟩ + γ • ket∣1, 0⟩ + δ • ket∣1, 1⟩ →
    p = (normSq β + normSq δ) →
    ϕ' = (1 / √p : ℂ) • (β • ket∣0, 1⟩ + δ • ket∣1, 1⟩) →
    measure_partial 2 ϕ (p, ϕ')

end QState
