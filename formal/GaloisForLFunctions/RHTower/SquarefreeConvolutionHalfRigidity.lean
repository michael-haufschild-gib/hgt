import GaloisForLFunctions.RHTower.SelbergPairingPrimeSquare
import GaloisForLFunctions.RHTower.SquarefreeMoebiusNormalization

/-!
# Coefficient-level square roots of the squarefree Euler source

Dirichlet-convolution square roots over `ℂ` are purely recursive. Every arithmetic function with
unit coefficient one has exactly one normalized convolution half. Thus the nonlinear coefficient
step proposed as an RH multiplicity mechanism is unconditional algebra and contains no choice that
could force analytic continuation through a zeta zero.

The squarefree specialization has the expected first local coefficients `1/2` at `p` and `-1/8`
at `p²`. Its self-convolution is the squarefree indicator exactly. This is a coefficient identity,
not an analytic square root on `Re s > 1/2`; the latter remains the continuation problem isolated
by `XiPoleClearedFirstTraceRootReduction`.
-/

open ArithmeticFunction
open scoped Moebius ArithmeticFunction.zeta

noncomputable section

namespace RHTower

private noncomputable def convolutionHalfFun (f : ArithmeticFunction ℂ) : ℕ → ℂ :=
  Nat.strongRec fun n ih =>
    if hn0 : n = 0 then 0
    else if hn1 : n = 1 then 1
    else
      (f n - ∑ d : ↥(n.properDivisors.erase 1),
        ih d (by
          exact (Nat.mem_properDivisors.mp (Finset.mem_of_mem_erase d.property)).2) *
        ih (n / (d : ℕ)) (by
          have hdmem := Finset.mem_of_mem_erase d.property
          have hdvd := (Nat.mem_properDivisors.mp hdmem).1
          have hdpos : 0 < (d : ℕ) :=
            Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hn0)
          have hd1 : (d : ℕ) ≠ 1 := Finset.ne_of_mem_erase d.property
          exact Nat.div_lt_self (Nat.pos_of_ne_zero hn0) (by omega))) / 2

/-- Canonical normalized Dirichlet-convolution half of a complex arithmetic function. -/
def convolutionHalf (f : ArithmeticFunction ℂ) : ArithmeticFunction ℂ :=
  ⟨convolutionHalfFun f, by simp [convolutionHalfFun, Nat.strongRec_eq]⟩

@[simp] theorem convolutionHalf_apply_zero (f : ArithmeticFunction ℂ) :
    convolutionHalf f 0 = 0 := by
  simp [convolutionHalf]

@[simp] theorem convolutionHalf_apply_one (f : ArithmeticFunction ℂ) :
    convolutionHalf f 1 = 1 := by
  simp [convolutionHalf, convolutionHalfFun, Nat.strongRec_eq]

/-- Recursive coefficient equation away from zero and the convolution unit. -/
theorem convolutionHalf_apply_of_ne_zero_one (f : ArithmeticFunction ℂ) {n : ℕ}
    (hn0 : n ≠ 0) (hn1 : n ≠ 1) :
    convolutionHalf f n =
      (f n - ∑ d : ↥(n.properDivisors.erase 1),
        convolutionHalf f d * convolutionHalf f (n / d)) / 2 := by
  change convolutionHalfFun f n =
    (f n - ∑ d : ↥(n.properDivisors.erase 1),
      convolutionHalfFun f d * convolutionHalfFun f (n / d)) / 2
  unfold convolutionHalfFun
  rw [Nat.strongRec_eq]
  simp only [hn0, hn1, ↓reduceDIte]

/-- The canonical half squares to the original normalized coefficient system. -/
theorem convolutionHalf_mul_self (f : ArithmeticFunction ℂ) (hf : f 1 = 1) :
    convolutionHalf f * convolutionHalf f = f := by
  ext n
  by_cases hn0 : n = 0
  · subst n
    simp
  by_cases hn1 : n = 1
  · subst n
    simp [hf]
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal'
      (f := fun x y => convolutionHalf f x * convolutionHalf f y)]
  rw [← Nat.cons_self_properDivisors hn0, Finset.sum_cons]
  have h1mem : 1 ∈ n.properDivisors := by
    rw [Nat.mem_properDivisors]
    exact ⟨one_dvd n, by omega⟩
  rw [← Finset.sum_erase_add (s := n.properDivisors)
    (f := fun d => convolutionHalf f (n / d) * convolutionHalf f d) h1mem]
  rw [convolutionHalf_apply_of_ne_zero_one f hn0 hn1]
  simp only [Nat.div_self (Nat.pos_of_ne_zero hn0), Nat.div_one,
    convolutionHalf_apply_one, one_mul, mul_one]
  rw [Finset.sum_subtype (n.properDivisors.erase 1)
    (p := fun d => d ∈ n.properDivisors.erase 1) (fun _ => Iff.rfl)]
  simp_rw [mul_comm (convolutionHalf f (n / _))]
  rw [convolutionHalf_apply_of_ne_zero_one f hn0 hn1]
  ring

private theorem apply_eq_half_recursion_of_mul_self_eq
    (f g : ArithmeticFunction ℂ) (hg1 : g 1 = 1) (hsq : g * g = f)
    {n : ℕ} (hn0 : n ≠ 0) (hn1 : n ≠ 1) :
    g n = (f n - ∑ d : ↥(n.properDivisors.erase 1), g d * g (n / d)) / 2 := by
  have h := congrArg (fun a : ArithmeticFunction ℂ => a n) hsq
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal' (f := fun x y => g x * g y)] at h
  rw [← Nat.cons_self_properDivisors hn0, Finset.sum_cons] at h
  have h1mem : 1 ∈ n.properDivisors := by
    rw [Nat.mem_properDivisors]
    exact ⟨one_dvd n, by omega⟩
  rw [← Finset.sum_erase_add (s := n.properDivisors)
    (f := fun d => g (n / d) * g d) h1mem] at h
  simp only [Nat.div_self (Nat.pos_of_ne_zero hn0), Nat.div_one, hg1, one_mul, mul_one] at h
  rw [Finset.sum_subtype (n.properDivisors.erase 1)
    (p := fun d => d ∈ n.properDivisors.erase 1) (fun _ => Iff.rfl)] at h
  simp_rw [mul_comm (g (n / _))] at h
  linear_combination h / 2

/-- A normalized convolution square root is forced coefficient by coefficient. -/
theorem convolutionHalf_unique (f g : ArithmeticFunction ℂ)
    (hg1 : g 1 = 1) (hsq : g * g = f) : g = convolutionHalf f := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn0 : n = 0
      · subst n
        simp
      by_cases hn1 : n = 1
      · subst n
        simp [hg1]
      rw [apply_eq_half_recursion_of_mul_self_eq f g hg1 hsq hn0 hn1,
        convolutionHalf_apply_of_ne_zero_one f hn0 hn1]
      congr 2
      apply Finset.sum_congr rfl
      intro d _
      rw [ih d (Nat.mem_properDivisors.mp (Finset.mem_of_mem_erase d.property)).2]
      have hdmem := Finset.mem_of_mem_erase d.property
      have hdvd := (Nat.mem_properDivisors.mp hdmem).1
      have hdpos : 0 < (d : ℕ) := Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hn0)
      have hd1 : (d : ℕ) ≠ 1 := Finset.ne_of_mem_erase d.property
      rw [ih (n / d) (Nat.div_lt_self (Nat.pos_of_ne_zero hn0) (by omega))]

/-- Every normalized complex arithmetic function has exactly one normalized convolution half. -/
theorem existsUnique_convolutionHalf (f : ArithmeticFunction ℂ) (hf : f 1 = 1) :
    ∃! g : ArithmeticFunction ℂ, g 1 = 1 ∧ g * g = f := by
  refine ⟨convolutionHalf f, ⟨convolutionHalf_apply_one f, convolutionHalf_mul_self f hf⟩, ?_⟩
  intro g hg
  exact convolutionHalf_unique f g hg.1 hg.2

/-- Complex squarefree-indicator coefficients. -/
def squarefreeIndicator : ArithmeticFunction ℂ :=
  ((pmul (μ : ArithmeticFunction ℤ) μ : ArithmeticFunction ℤ) : ArithmeticFunction ℂ)

@[simp] theorem squarefreeIndicator_apply_one : squarefreeIndicator 1 = 1 := by
  simp [squarefreeIndicator, pmul_apply]

theorem squarefreeIndicator_apply_prime {p : ℕ} (hp : p.Prime) :
    squarefreeIndicator p = 1 := by
  simp [squarefreeIndicator, pmul_apply, ArithmeticFunction.moebius_apply_prime hp]

theorem squarefreeIndicator_apply_prime_sq {p : ℕ} (hp : p.Prime) :
    squarefreeIndicator (p ^ 2) = 0 := by
  simp [squarefreeIndicator, pmul_apply,
    ArithmeticFunction.moebius_apply_prime_pow (k := 2) hp (by norm_num)]

/-- Canonical coefficient-level half of the squarefree Euler source. -/
def squarefreeConvolutionHalf : ArithmeticFunction ℂ :=
  convolutionHalf squarefreeIndicator

theorem squarefreeConvolutionHalf_mul_self :
    squarefreeConvolutionHalf * squarefreeConvolutionHalf = squarefreeIndicator :=
  convolutionHalf_mul_self squarefreeIndicator squarefreeIndicator_apply_one

@[simp] theorem squarefreeConvolutionHalf_apply_one : squarefreeConvolutionHalf 1 = 1 := by
  simp [squarefreeConvolutionHalf]

theorem squarefreeConvolutionHalf_apply_prime {p : ℕ} (hp : p.Prime) :
    squarefreeConvolutionHalf p = 1 / 2 := by
  have h := congrArg (fun a : ArithmeticFunction ℂ => a p)
    squarefreeConvolutionHalf_mul_self
  rw [arithmeticFunction_mul_apply_prime' squarefreeConvolutionHalf
    squarefreeConvolutionHalf hp] at h
  rw [squarefreeIndicator_apply_prime hp] at h
  simp only [squarefreeConvolutionHalf_apply_one, one_mul, mul_one] at h
  linear_combination h / 2

theorem squarefreeConvolutionHalf_apply_prime_sq {p : ℕ} (hp : p.Prime) :
    squarefreeConvolutionHalf (p ^ 2) = -1 / 8 := by
  have h := congrArg (fun a : ArithmeticFunction ℂ => a (p ^ 2))
    squarefreeConvolutionHalf_mul_self
  rw [arithmeticFunction_mul_apply_prime_sq squarefreeConvolutionHalf
    squarefreeConvolutionHalf hp] at h
  rw [squarefreeIndicator_apply_prime_sq hp,
    squarefreeConvolutionHalf_apply_prime hp] at h
  simp only [squarefreeConvolutionHalf_apply_one, one_mul, mul_one] at h
  linear_combination h / 2

end RHTower
