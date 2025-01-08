import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Kronecker
import Mathlib.Tactic
import Mathlib.Data.Fin.Basic

namespace QMatrix

open Matrix Kronecker Complex ComplexConjugate

/--
  `pow_two_add n m : 2^(n + m) = (2^n) * (2^m)`
  Lean에서 `ring_nf`가 잘 쓸 수 있도록 제공하는 기본 보조정리.
-/
@[simp]
lemma pow_two_add (n m : ℕ) : 2^(n + m) = (2^n) * (2^m) := by
  rw [pow_add]

/--
  `reindexToFinMul A`
  (a×b)×(c×d) 형태의 행렬 인덱스를 (a*c)×(b*d) 형태로 바꿉니다.
  보통 `A : Matrix (Fin a × Fin b) (Fin c × Fin d) α` 일 때,
  `reindexToFinMul A : Matrix (Fin (a*b)) (Fin (c*d)) α` 가 됩니다.
-/
@[simp]
def reindexToFinMul {α : Type _} {a b c d : ℕ}
  (A : Matrix (Fin a × Fin b) (Fin c × Fin d) α) :
  Matrix (Fin (a * b)) (Fin (c * d)) α :=
  A.reindex finProdFinEquiv finProdFinEquiv

/--
  `kroneckerReindexed A B`
  보통 `(A ⊗ₖ B) : Matrix (Fin (a×c)) (Fin (b×d)) α` 로 쓰려면
  Lean 내부에서는 `(Fin a × Fin c) × (Fin b × Fin d)` 형태로 잡혀 있어
  곧바로 `(Fin (a*c)) × (Fin (b*d))` 로 인식하지 못합니다.

  따라서 아래 정의처럼, 우선 `A ⊗ₖ B`를 구한 뒤 `reindexToFinMul`을 적용하여
  인덱스 타입을 원하는 `(Fin (a*c))`, `(Fin (b*d))` 형태로 바꿔줍니다.
-/
def kroneckerReindexed {α : Type _} [Mul α] [Add α] (A : Matrix (Fin a) (Fin b) α)
  (B : Matrix (Fin c) (Fin d) α) :
  Matrix (Fin (a*c)) (Fin (b*d)) α :=
  reindexToFinMul (A ⊗ₖ B)

/--
  특히 `2^n` 차원과 `2^m` 차원에서의 크로네커 곱을
  `2^(n+m)` 차원으로 reindex해주는 특수 버전도 정의할 수 있습니다.
-/
def kroneckerPow2 {α : Type _} [Mul α] [Add α] (A : Matrix (Fin (2^n)) (Fin (2^n)) α)
  (B : Matrix (Fin (2^m)) (Fin (2^m)) α) :
  Matrix (Fin (2^(n+m))) (Fin (2^(n+m))) α :=
  -- 2^(n+m) = 2^n * 2^m를 이용하여 kroneckerReindexed에 직접 대입
  Eq.mp (by simp) (kroneckerReindexed A B)

/--
  예: bra(1)와 bra(2)를 크로네커 곱한 뒤 reindex하여 bra(1+2)를 만드는 식의
  ‘형식적’ 예시를 들자면 다음과 같이 쓸 수 있습니다.
  같은 꼴의 코드를 매번 직접 작성하지 않고, 이 파일에 모아두어
  필요하면 `QMatrix.kroneckerPow2 ϕ ψ` 같은 식으로 편히 호출하면 됩니다.
-/
def qbraKronecker {n m : ℕ} (ϕ : Matrix (Fin 1) (Fin (2^n)) ℂ)
(ψ : Matrix (Fin 1) (Fin (2^m)) ℂ) : Matrix (Fin 1) (Fin (2^(n+m))) ℂ :=
  let product := ϕ ⊗ₖ ψ
  Eq.mp (by simp) (product.reindex finProdFinEquiv finProdFinEquiv)

end QMatrix
