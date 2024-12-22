import Mathlib.Tactic

open Matrix Real Complex ComplexConjugate

-- Qubit definition: 2x1 complex matrix
structure Qubit where
  mat : Matrix (Fin 2) (Fin 1) ℂ

namespace Qubit

-- Define coercion to Matrix
instance : Coe Qubit (Matrix (Fin 2) (Fin 1) ℂ) where
  coe := Qubit.mat

-- Make Qubit callable as a function
instance : CoeFun Qubit (λ _ => Fin 2 → Fin 1 → ℂ) where
  coe ϕ := λ i j => ϕ.mat i j

-- Define standard basis Qubits
def qubit0 : Qubit :=
  ⟨!![1; 0]⟩

def qubit1 : Qubit :=
  ⟨!![0; 1]⟩

notation "∣0⟩" => qubit0
notation "∣1⟩" => qubit1
-- Any Qubit can be expressed as a linear combination of ∣0⟩ and ∣1⟩
theorem qubit_decomposition (ϕ : Qubit) : ∃ α β : ℂ, ∀ i, ϕ i 0 = α * qubit0 i 0 + β * qubit1 i 0 := by
  use ϕ 0 0, ϕ 1 0
  intro i
  fin_cases i
  all_goals
    simp [qubit0, qubit1]

-- Define Well-formed Qubit
def WF_Qubit (ϕ : Qubit) : Prop :=
  ∑ i : Fin 2, ‖ϕ i 0‖ ^ 2 = 1

-- Alternative definition of WF_Qubit
theorem WF_Qubit_alt (ϕ : Qubit) :
    WF_Qubit ϕ ↔ (ϕ.matᴴ * ϕ.mat) = (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  -- Expand the definitions on both sides
  unfold WF_Qubit
  -- simplify the sum expression
  constructor
  · -- Forward direction
    intro h_sum
    simp [sq_abs] at h_sum
    ext i j
    fin_cases i
    fin_cases j
    simp [conjTranspose, mul_apply, ←normSq_eq_conj_mul_self, ← ofReal_add]
    exact h_sum
  · -- Backward direction
    intro h_matrix
    simp [conjTranspose, mul_apply, ← ext_iff] at h_matrix
    specialize h_matrix 0 0
    simp [←normSq_eq_conj_mul_self, ← ofReal_add] at h_matrix
    simp [sq_abs]
    exact h_matrix

-- Prove that the basis Qubits are WF_Qubits
theorem WF_qubit0 : WF_Qubit ∣0⟩ := by
  simp [WF_Qubit, qubit0]

theorem WF_qubit1 : WF_Qubit ∣1⟩ := by
  simp [WF_Qubit, qubit1]

-- Define and verify Unitary
def WF_Unitary {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  (Uᴴ * U) = (1 : Matrix (Fin n) (Fin n) ℂ)

-- An operation that acts on a qubit is valid if it preserves the well-formedness of the qubit.
-- It turns out that an unitary operation is always valid by this proof.
theorem valid_qubit_function :
  ∃ P : Matrix (Fin 2) (Fin 2) ℂ → Prop,
    (∀ (A : Matrix (Fin 2) (Fin 2) ℂ) (ϕ : Qubit),
      P A → WF_Qubit ϕ → WF_Qubit ⟨A * ϕ.mat⟩) := by
  use WF_Unitary
  intro A ϕ h_unitary h_wf
  rw [WF_Qubit_alt] at h_wf ⊢
  rw [WF_Unitary] at h_unitary
  simp only at *
  have h_new : (A * ϕ.mat)ᴴ * (A * ϕ.mat) = ϕ.matᴴ * (Aᴴ * A) * ϕ.mat := by
    simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [h_new, h_unitary, Matrix.mul_one, h_wf]

-- Define Unitary operations (e.g., Pauli matrices)
def X : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![0, 1], ![1, 0]]

def Y : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![0, -I], ![I, 0]]

def Z : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![1, 0], ![0, -1]]

theorem WF_X : WF_Unitary X := by
  simp [WF_Unitary, X, conjTranspose, mul_apply, ← ext_iff]
  intro i j
  fin_cases i
  all_goals
    fin_cases j
    all_goals
      simp

theorem WF_Y : WF_Unitary Y := by
  simp [WF_Unitary, Y, conjTranspose, mul_apply, ← ext_iff]
  intro i j
  fin_cases i
  all_goals
    fin_cases j
    all_goals
      simp

theorem WF_Z : WF_Unitary Z := by
  simp [WF_Unitary, Z, conjTranspose, mul_apply, ← ext_iff]
  intro i j
  fin_cases i
  all_goals
    fin_cases j
    all_goals
      simp

-- Define Hadamard matrix
noncomputable def H : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / √ 2 : ℂ) • ![![1, 1], ![1, -1]]

theorem WF_H : WF_Unitary H := by
  simp [WF_Unitary, H, conjTranspose, mul_apply, ← ext_iff]
  intro i j
  fin_cases i
  all_goals
    fin_cases j
    all_goals
      simp [smul_apply, ofReal_div, ofReal_inv, ofReal_mul]
      simp only [starRingEnd_apply]
      repeat rw [smul_apply]
      field_simp
  all_goals
    ring_nf
    simp [ofReal, pow_two]
    apply Complex.ext
    all_goals
      repeat simp

-- Define Hermitian property
def Hermitian {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  Aᴴ = A

-- Prove that H is Hermitian
theorem H_Hermitian : Hermitian H := by
  simp [Hermitian, H, conjTranspose, mul_apply, ← ext_iff]
  -- Prove element-wise equality
  intro i j
  fin_cases i
  all_goals
    fin_cases j
    all_goals
      simp [smul_apply]
      simp only [starRingEnd_apply]
      repeat rw [smul_apply]
      field_simp

-- Prove that Hadamard applied twice returns the original state
theorem Htwice (ϕ : Qubit) : H * (H * ϕ.mat) = ϕ := by
  -- Use associativity of matrix multiplication
  rw [← Matrix.mul_assoc]
  -- Replace (H * H) with the identity matrix using unitary and Hermitian properties
  have HH_eq_I : H * H = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    -- H is Hermitian: Hᴴ = H
    have H_Herm : Hᴴ = H := H_Hermitian
    -- H is unitary: Hᴴ * H = I
    have H_unit : (Hᴴ * H) = (1 : Matrix (Fin 2) (Fin 2) ℂ) := WF_H
    -- Combine the two properties to get H * H = I
    rw [H_Herm] at H_unit
    exact H_unit
  -- Replace (H * H) in the goal with the identity matrix
  rw [HH_eq_I]
  -- Multiplying a matrix by the identity matrix leaves it unchanged
  rw [Matrix.one_mul]

-- Define measurement
inductive Measure : Qubit → ℝ × Qubit → Prop
| measure0 : ∀ ϕ : Qubit, Measure ϕ (‖ϕ 0 0‖ ^ 2, qubit0)
| measure1 : ∀ ϕ : Qubit, Measure ϕ (‖ϕ 1 0‖ ^ 2, qubit1)

-- Prove properties related to measurement
theorem measure0_idem (ϕ : Qubit) (p : ℝ) : Measure ∣0⟩ (p, ϕ) → p ≠ 0 → ϕ = ∣0⟩ := by
  intro h_meas h_nonzero
  cases h_meas
  · rfl
  · simp [qubit0] at h_nonzero

theorem measure1_idem (ϕ : Qubit) (p : ℝ) : Measure ∣1⟩ (p, ϕ) → p ≠ 0 → ϕ = ∣1⟩ := by
  intro h_meas h_nonzero
  cases h_meas
  · simp [qubit1] at h_nonzero
  · rfl

end Qubit
