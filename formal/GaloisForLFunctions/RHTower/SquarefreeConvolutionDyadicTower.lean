import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfRigidity

/-!
# The automatic dyadic convolution-root tower

Iterating the unique normalized Dirichlet-convolution half gives every normalized complex
arithmetic function a unique coefficient-level dyadic root tower.  At depth `n`, its
`2^n`-fold convolution power is the original function.  At a prime, the coefficient is divided
by `2^n`; for the squarefree indicator it is exactly `2^(-n)`.

This formalizes the coefficient-level analogue of the report's proposed Clifford escalation.
It is automatic algebra: no zero, parity, or analytic continuation enters.  Therefore a claimed
analytic escalation must separately prove convergence/continuation of every stage.  Existence of
the first analytic square root does not make the next coefficient root analytic.
-/

open ArithmeticFunction
open scoped Moebius ArithmeticFunction.zeta

noncomputable section

namespace RHTower

/-- Iterated normalized Dirichlet-convolution halves. -/
def convolutionDyadicRootTower (f : ArithmeticFunction ℂ) : ℕ → ArithmeticFunction ℂ
  | 0 => f
  | n + 1 => convolutionHalf (convolutionDyadicRootTower f n)

@[simp] theorem convolutionDyadicRootTower_zero (f : ArithmeticFunction ℂ) :
    convolutionDyadicRootTower f 0 = f := rfl

@[simp] theorem convolutionDyadicRootTower_succ (f : ArithmeticFunction ℂ) (n : ℕ) :
    convolutionDyadicRootTower f (n + 1) =
      convolutionHalf (convolutionDyadicRootTower f n) := rfl

/-- Every stage remains normalized. -/
theorem convolutionDyadicRootTower_apply_one (f : ArithmeticFunction ℂ)
    (hf : f 1 = 1) (n : ℕ) : convolutionDyadicRootTower f n 1 = 1 := by
  induction n with
  | zero => exact hf
  | succ n ih => simp

/-- Each successor is exactly a convolution square root of its predecessor. -/
theorem convolutionDyadicRootTower_succ_mul_self (f : ArithmeticFunction ℂ)
    (hf : f 1 = 1) (n : ℕ) :
    convolutionDyadicRootTower f (n + 1) * convolutionDyadicRootTower f (n + 1) =
      convolutionDyadicRootTower f n := by
  rw [convolutionDyadicRootTower_succ]
  exact convolutionHalf_mul_self _ (convolutionDyadicRootTower_apply_one f hf n)

/-- Repeated squaring operation, written recursively to mirror the tower. -/
def dyadicConvolutionPower (f : ArithmeticFunction ℂ) : ℕ → ArithmeticFunction ℂ
  | 0 => f
  | n + 1 => dyadicConvolutionPower (f * f) n

@[simp] theorem dyadicConvolutionPower_zero (f : ArithmeticFunction ℂ) :
    dyadicConvolutionPower f 0 = f := rfl

@[simp] theorem dyadicConvolutionPower_succ (f : ArithmeticFunction ℂ) (n : ℕ) :
    dyadicConvolutionPower f (n + 1) = dyadicConvolutionPower (f * f) n := rfl

/-- Repeated squaring a depth-`n` tower stage returns the original coefficients. -/
theorem dyadicConvolutionPower_convolutionDyadicRootTower (f : ArithmeticFunction ℂ)
    (hf : f 1 = 1) (n : ℕ) :
    dyadicConvolutionPower (convolutionDyadicRootTower f n) n = f := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [dyadicConvolutionPower_succ, convolutionDyadicRootTower_succ_mul_self f hf n]
      exact ih

/-- Recursive repeated squaring is ordinary `2^n`-fold convolution power. -/
theorem dyadicConvolutionPower_eq_pow (f : ArithmeticFunction ℂ) (n : ℕ) :
    dyadicConvolutionPower f n = f ^ (2 ^ n) := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
      rw [dyadicConvolutionPower_succ, ih, mul_pow]
      rw [← pow_add]
      congr 1
      omega

/-- Depth `n` is the normalized coefficient-level `2^n`-th root. -/
theorem convolutionDyadicRootTower_pow (f : ArithmeticFunction ℂ)
    (hf : f 1 = 1) (n : ℕ) :
    convolutionDyadicRootTower f n ^ (2 ^ n) = f := by
  rw [← dyadicConvolutionPower_eq_pow]
  exact dyadicConvolutionPower_convolutionDyadicRootTower f hf n

/-- Any normalized coherent convolution-square tower is the canonical tower. -/
theorem convolutionDyadicRootTower_unique (f : ArithmeticFunction ℂ)
    (T : ℕ → ArithmeticFunction ℂ) (hzero : T 0 = f)
    (hone : ∀ n, T (n + 1) 1 = 1)
    (hsq : ∀ n, T (n + 1) * T (n + 1) = T n) :
    ∀ n, T n = convolutionDyadicRootTower f n := by
  intro n
  induction n with
  | zero => exact hzero
  | succ n ih =>
      rw [convolutionDyadicRootTower_succ, ← ih]
      exact convolutionHalf_unique (T n) (T (n + 1)) (hone n) (hsq n)

/-- At a prime, one convolution-half step divides the coefficient by two. -/
theorem convolutionHalf_apply_prime_of_normalized (f : ArithmeticFunction ℂ)
    (hf : f 1 = 1) {p : ℕ} (hp : p.Prime) :
    convolutionHalf f p = f p / 2 := by
  have h := congrArg (fun a : ArithmeticFunction ℂ => a p)
    (convolutionHalf_mul_self f hf)
  rw [arithmeticFunction_mul_apply_prime' (convolutionHalf f) (convolutionHalf f) hp] at h
  simp only [convolutionHalf_apply_one, one_mul, mul_one] at h
  linear_combination h / 2

/-- Prime coefficients record the formal dyadic depth exactly. -/
theorem convolutionDyadicRootTower_apply_prime (f : ArithmeticFunction ℂ)
    (hf : f 1 = 1) {p : ℕ} (hp : p.Prime) (n : ℕ) :
    convolutionDyadicRootTower f n p = f p / (2 : ℂ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [convolutionDyadicRootTower_succ,
        convolutionHalf_apply_prime_of_normalized _
          (convolutionDyadicRootTower_apply_one f hf n) hp,
        ih, pow_succ]
      ring

/-- Canonical dyadic coefficient roots of the squarefree Euler source. -/
def squarefreeConvolutionDyadicRootTower : ℕ → ArithmeticFunction ℂ :=
  convolutionDyadicRootTower squarefreeIndicator

/-- Its depth-`n` `2^n`-fold convolution power is the squarefree indicator. -/
theorem squarefreeConvolutionDyadicRootTower_pow (n : ℕ) :
    squarefreeConvolutionDyadicRootTower n ^ (2 ^ n) = squarefreeIndicator :=
  convolutionDyadicRootTower_pow squarefreeIndicator squarefreeIndicator_apply_one n

/-- Its prime coefficient is exactly `2^(-n)`. -/
theorem squarefreeConvolutionDyadicRootTower_apply_prime {p : ℕ} (hp : p.Prime) (n : ℕ) :
    squarefreeConvolutionDyadicRootTower n p = 1 / (2 : ℂ) ^ n := by
  rw [squarefreeConvolutionDyadicRootTower,
    convolutionDyadicRootTower_apply_prime squarefreeIndicator
      squarefreeIndicator_apply_one hp n,
    squarefreeIndicator_apply_prime hp]

end RHTower
