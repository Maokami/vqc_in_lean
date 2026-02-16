import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Kronecker
import Mathlib.Tactic
import Mathlib.Data.Fin.Basic

namespace QMatrix

open Matrix Kronecker Complex ComplexConjugate

@[simp]
lemma pow_two_add (n m : ℕ) : 2^(n + m) = (2^n) * (2^m) := by
  rw [pow_add]

/--
  `reindexToFinMul A`

  Change the matrix index from `(a×b)×(c×d)` to `(a*c)×(b*d)` form.
  When `A : Matrix (Fin a × Fin b) (Fin c × Fin d) α`,
  `reindexToFinMul A : Matrix (Fin (a*b)) (Fin (c*d)) α` is returned.
-/
@[simp]
def reindexToFinMul {α : Type _} {a b c d : ℕ}
  (A : Matrix (Fin a × Fin b) (Fin c × Fin d) α) :
  Matrix (Fin (a * b)) (Fin (c * d)) α :=
  A.reindex finProdFinEquiv finProdFinEquiv

/--
  `kroneckerReindexed A B`

  Calculate the Kronecker product of `A` and `B`, then reindex the result.
  If you want to write `(A ⊗ₖ B) : Matrix (Fin (a×c)) (Fin (b×d)) α` in the usual way,
  you need to apply `reindexToFinMul` to change the index type to `(Fin (a*c))`, `(Fin (b*d))`.
-/
@[simp]
def kroneckerReindexed {α : Type _} [Mul α] [Add α] (A : Matrix (Fin a) (Fin b) α)
  (B : Matrix (Fin c) (Fin d) α) :
  Matrix (Fin (a*c)) (Fin (b*d)) α :=
  reindexToFinMul (A ⊗ₖ B)

/--
  `kroneckerPow2 A B`

  In particular, you can define a special version that reindexes the Kronecker product
  of `2^n`-dimensional and `2^m`-dimensional matrices to a `2^(n+m)`-dimensional matrix.
-/
@[simp]
def kroneckerPow2 {α : Type _} [Mul α] [Add α] (A : Matrix (Fin (2^n)) (Fin (2^n)) α)
  (B : Matrix (Fin (2^m)) (Fin (2^m)) α) :
  Matrix (Fin (2^(n+m))) (Fin (2^(n+m))) α :=
  Eq.mp (by simp) (kroneckerReindexed A B)

def qbraKronecker {n m : ℕ} (ϕ : Matrix (Fin 1) (Fin (2^n)) ℂ)
(ψ : Matrix (Fin 1) (Fin (2^m)) ℂ) : Matrix (Fin 1) (Fin (2^(n+m))) ℂ :=
  let product := ϕ ⊗ₖ ψ
  Eq.mp (by simp) (product.reindex finProdFinEquiv finProdFinEquiv)

end QMatrix
