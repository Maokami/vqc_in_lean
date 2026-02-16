import VqcInLean.Qubit
import VqcInLean.QState
import VqcInLean.QBra
import VqcInLean.QMatrix

import Mathlib.Tactic
import Mathlib.Data.Matrix.Kronecker
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Real.Basic

open Real Complex Matrix Kronecker Qubit QState QBra QMatrix Vector

namespace SQIR

-- Define Gates
inductive Gate : ℕ → Type where
  | G_I     : ℕ → Gate 1
  | G_H     : ℕ → Gate 1
  | G_X     : ℕ → Gate 1
  | G_Z     : ℕ → Gate 1
  | G_CNOT  : ℕ → ℕ → Gate 2

-- Define commands
inductive Com : Type where
  | skip : Com
  | seq  : Com → Com → Com
  | app  : {n : ℕ} → Gate n → Com

namespace Com

-- Add notation for sequences
scoped infixl:100 ";" => seq

-- Helper definitions for specific gates
def SKIP := skip
def _I_ (q : ℕ) := app (Gate.G_I q)
def _H_ (q : ℕ) := app (Gate.G_H q)
def _X_ (q : ℕ) := app (Gate.G_X q)
def _Z_ (q : ℕ) := app (Gate.G_Z q)
def _CNOT_ (q1 q2 : ℕ) := app (Gate.G_CNOT q1 q2)

-- Padding unitaries
def pad (n idx dim : ℕ) (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
    Matrix (Fin (2 ^ dim)) (Fin (2 ^ dim)) ℂ :=
  if h : idx + n ≤ dim then
    let left_size := 2 ^idx
    let rest : ℕ := dim - (idx + n)
    let right_size := 2 ^ rest
    have h1 : idx + n + rest = dim := by simp [rest, h]
    let left_id := (1 : Matrix (Fin left_size) (Fin left_size) ℂ)
    let right_id := (1 : Matrix (Fin right_size) (Fin right_size) ℂ)

    let fst : Matrix (Fin (2 ^ (idx + n))) (Fin (2 ^ (idx + n))) ℂ :=
      Eq.mp (by ring_nf) (reindexToFinMul (left_id ⊗ₖ U))
    let snd : Matrix (Fin (2 ^ (idx + n + rest))) (Fin (2 ^ (idx + n + rest))) ℂ :=
      Eq.mp (by ring_nf) (reindexToFinMul (fst ⊗ₖ right_id))
    Eq.mp (by simp [h1]) snd
  else
    (0 : Matrix (Fin (2 ^ dim)) (Fin (2 ^ dim)) ℂ)

-- Evaluate a CNOT gate
noncomputable def evalCNOT (dim m n : ℕ) : Matrix (Fin (2 ^ dim)) (Fin (2 ^ dim)) ℂ :=
  let proj0 := ⟨∣0⟩ * ⟨0∣⟩
  let proj1 := ⟨∣1⟩ * ⟨1∣⟩

  if m < n then
    let gap_size := n - m - 1
    let A := kroneckerPow2 proj1
      (kroneckerPow2 (1 : Matrix (Fin (2^gap_size)) (Fin (2^gap_size)) ℂ) X)
    let B := kroneckerPow2 proj0
      (kroneckerPow2 (1 : Matrix (Fin (2^gap_size)) (Fin (2^gap_size)) ℂ) (1 : Matrix (Fin (2^1)) (Fin (2^1)) ℂ))
    pad (1 + gap_size + 1) m dim (A + B)

  else if n < m then
    let gap_size := m - n - 1
    let A := kroneckerPow2 X
      (kroneckerPow2 (1 : Matrix (Fin (2^gap_size)) (Fin (2^gap_size)) ℂ) proj1)
    let B := kroneckerPow2 (1 : Matrix (Fin (2^1)) (Fin (2^1)) ℂ)
      (kroneckerPow2 (1 : Matrix (Fin (2^gap_size)) (Fin (2^gap_size)) ℂ) proj0)
    pad (1 + gap_size + 1) n dim (A + B)

  else
    (0 : Matrix (Fin (2 ^ dim)) (Fin (2 ^ dim)) ℂ)

-- Evaluate a gate
noncomputable def evalGate {n : ℕ} (dim : ℕ) (g : Gate n) : Matrix (Fin (2 ^ dim)) (Fin (2 ^ dim)) ℂ :=
  match g with
  | Gate.G_I j     => pad 1 j dim (1 : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ)
  | Gate.G_H j     => pad 1 j dim H
  | Gate.G_X j     => pad 1 j dim X
  | Gate.G_Z j     => pad 1 j dim Z
  | Gate.G_CNOT j k => evalCNOT dim j k

-- Evaluate a command
noncomputable def eval (dim : ℕ) : Com → Matrix (Fin (2 ^ dim)) (Fin (2 ^ dim)) ℂ
  | skip    => (1 : Matrix (Fin (2 ^ dim)) (Fin (2 ^ dim) ) ℂ)
  | app g   => evalGate dim g
  | seq c1 c2 => eval dim c2 * eval dim c1

-- Command equivalence
def comEquiv (c1 c2 : Com) := ∀ dim, eval dim c1 = eval dim c2

infix:80 "≡" => comEquiv

lemma _CNOT_CNOT : eval 2 (_CNOT_ 0 1) = CNOT := by
  simp [eval, evalGate, evalCNOT, pad, X, CNOT, Eq.mp, kroneckerMap, reindex, finProdFinEquiv, Fin.divNat, Fin.modNat, QBra.fromVector]
  simp [instHMulQStateMatrixFinHPowNatOfNatComplex, instHMulOfFintypeOfMulOfAddCommMonoid, dotProduct]
  simp only [Vector.head, getElem, Vector.get, Fin.cast, Array.get, List.get]
  simp
  ring_nf
  ext i j
  fin_cases i
  all_goals
    fin_cases j
    all_goals
      simp; try rfl
  left; right
  norm_cast

  left;left;right
  norm_cast

  sorry

-- Define basic programs
def BELL : Com := _H_ 0; _CNOT_ 0 1

def encode (b1 b2 : Bool) : Com :=
  (if b2 then _X_ 0 else SKIP);
  (if b1 then _Z_ 0 else SKIP)

def decode : Com := _CNOT_ 0 1; _H_ 0

def superdense (b1 b2 : Bool) := BELL; encode b1 b2; decode

-- SWAP definition
def _SWAP_ (q1 q2 : ℕ) : Com := _CNOT_ q1 q2; _CNOT_ q2 q1; _CNOT_ q1 q2

-- Circuit families
def par_n : ℕ → (ℕ → Com) → Com
  | 0, _ => SKIP
  | n + 1, c => c n; par_n n c

end Com

end SQIR
