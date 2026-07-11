import Mathlib.Algebra.Group.EvenFunction
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic

/-!
# Exact value relations from the Feigenbaum functional equation

This module isolates only the algebraic value content of the normalized equation

`g (g x) = lam * g (alpha * x)`, with `alpha * lam = -1` and `g` even.

It proves the dyadic iterate identity and its critical-orbit specialization.  No analyticity,
differential algebraicity, or hypertranscendence claim is used or obtained.
-/

namespace GaloisForLFunctions

variable {K : Type*} [CommRing K]

/-- Evenness removes every power of the sign `-1`. -/
theorem even_apply_negOne_pow_mul {g : K → K} (hEven : Function.Even g) :
    ∀ (n : ℕ) (x : K), g (((-1 : K) ^ n) * x) = g x := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      intro x
      calc
        g (((-1 : K) ^ (n + 1)) * x) = g (-(((-1 : K) ^ n) * x)) := by
          congr 1
          ring
        _ = g (((-1 : K) ^ n) * x) := hEven _
        _ = g x := ih x

/-- **Feigenbaum dyadic iterate value law.**  If an even function satisfies the normalized
Feigenbaum relation `g (g x) = lam * g (alpha * x)` and `alpha * lam = -1`, then its `2^n`-fold
iterate is exactly the rescaled value `lam^n * g (alpha^n * x)`. -/
theorem feigenbaum_dyadic_iterate
    {g : K → K} {alpha lam : K}
    (hEven : Function.Even g) (hscale : alpha * lam = -1)
    (hFE : ∀ x, g (g x) = lam * g (alpha * x)) :
    ∀ (n : ℕ) (x : K), (g^[2 ^ n]) x = lam ^ n * g (alpha ^ n * x) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      intro x
      rw [pow_succ]
      rw [show 2 ^ n * 2 = 2 ^ n + 2 ^ n by omega,
        Function.iterate_add_apply, ih, ih]
      have hpow : alpha ^ n * lam ^ n = (-1 : K) ^ n := by
        rw [← mul_pow, hscale]
      have harg : alpha ^ n * (lam ^ n * g (alpha ^ n * x)) =
          (-1 : K) ^ n * g (alpha ^ n * x) := by
        rw [← mul_assoc, hpow]
      rw [harg, even_apply_negOne_pow_mul hEven, hFE]
      ring_nf

/-- The normalization `g 0 = 1` makes the dyadic critical orbit a geometric sequence:
`g^[2^n](0) = lam^n`. -/
theorem feigenbaum_dyadic_critical_value
    {g : K → K} {alpha lam : K}
    (hEven : Function.Even g) (hscale : alpha * lam = -1)
    (hFE : ∀ x, g (g x) = lam * g (alpha * x)) (hg0 : g 0 = 1) :
    ∀ n : ℕ, (g^[2 ^ n]) 0 = lam ^ n := by
  intro n
  rw [feigenbaum_dyadic_iterate hEven hscale hFE]
  simp [hg0]

/-- Evaluating the normalized Feigenbaum relation at the critical point gives `g 1 = lam`. -/
theorem feigenbaum_critical_value
    {g : K → K} {alpha lam : K}
    (hFE : ∀ x, g (g x) = lam * g (alpha * x)) (hg0 : g 0 = 1) :
    g 1 = lam := by
  simpa [hg0] using hFE 0

private theorem contDiff_iterate_two {g : ℂ → ℂ} (hg : ContDiff ℂ 2 g) :
    ∀ N : ℕ, ContDiff ℂ 2 (g^[N]) := by
  intro N
  induction N with
  | zero => simpa using (contDiff_id : ContDiff ℂ 2 (id : ℂ → ℂ))
  | succ N ih =>
      rw [show g^[N + 1] = g ∘ g^[N] by
        funext x
        simp only [Function.comp_apply, Function.iterate_succ_apply']]
      exact hg.comp ih

/-- The derivative of an iterate is the product of the derivatives along its orbit. -/
theorem deriv_iterate_eq_orbitProduct {g : ℂ → ℂ}
    (hg : Differentiable ℂ g) : ∀ (N : ℕ) (x : ℂ),
    deriv (g^[N]) x = ∏ j ∈ Finset.range N, deriv g ((g^[j]) x) := by
  have hiter : ∀ N : ℕ, Differentiable ℂ (g^[N]) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
        rw [show g^[N + 1] = g ∘ g^[N] by
          funext x
          simp only [Function.comp_apply, Function.iterate_succ_apply']]
        exact hg.comp ih
  intro N
  induction N with
  | zero =>
      intro x
      simp
  | succ N ih =>
      intro x
      rw [show g^[N + 1] = g ∘ g^[N] by
        funext y
        simp only [Function.comp_apply, Function.iterate_succ_apply']]
      rw [deriv_comp x hg.differentiableAt (hiter N).differentiableAt, ih]
      rw [Finset.prod_range_succ]
      ring

/-- The second critical jet transports the derivative of the outer `2^n-1` iterates exactly.
For the quadratic Feigenbaum normalization this derivative is `(-alpha)^n`. -/
theorem feigenbaum_quadratic_postcritical_deriv
    {g : ℂ → ℂ} {alpha lam : ℂ}
    (hEven : Function.Even g) (hscale : alpha * lam = -1)
    (hFE : ∀ x, g (g x) = lam * g (alpha * x))
    (hg0 : g 0 = 1) (hg : ContDiff ℂ 2 g)
    (hcrit : deriv g 0 = 0)
    (hquad : iteratedDeriv 2 g 0 ≠ 0) :
    ∀ n : ℕ, deriv (g^[2 ^ n - 1]) 1 = (-alpha) ^ n := by
  intro n
  let N := 2 ^ n
  let h := g^[N - 1]
  have hNpos : 0 < N := by simp [N]
  have hN : N - 1 + 1 = N := Nat.sub_add_cancel hNpos
  have hcomp : g^[N] = h ∘ g := by
    funext x
    simp only [h, Function.comp_apply]
    have hs := Function.iterate_succ_apply g (N - 1) x
    rw [Nat.succ_eq_add_one, hN] at hs
    exact hs
  have hh : ContDiff ℂ 2 h := contDiff_iterate_two hg (N - 1)
  have hleft : iteratedDeriv 2 (g^[N]) 0 =
      deriv h 1 * iteratedDeriv 2 g 0 := by
    rw [hcomp]
    rw [iteratedDeriv_comp_two hh.contDiffAt hg.contDiffAt]
    simp [hg0, hcrit]
  have hfun : g^[N] = fun x => lam ^ n * g (alpha ^ n * x) := by
    funext x
    simpa only [N] using feigenbaum_dyadic_iterate hEven hscale hFE n x
  have hright : iteratedDeriv 2 (g^[N]) 0 =
      (lam ^ n * alpha ^ (2 * n)) * iteratedDeriv 2 g 0 := by
    rw [hfun]
    rw [iteratedDeriv_const_mul_field]
    rw [show iteratedDeriv 2 (fun x => g (alpha ^ n * x)) 0 =
        (alpha ^ n) ^ 2 * iteratedDeriv 2 g ((alpha ^ n) * 0) by
      exact congrFun (iteratedDeriv_comp_const_mul hg (alpha ^ n)) 0]
    simp only [mul_zero]
    ring
  have heq : deriv h 1 = lam ^ n * alpha ^ (2 * n) := by
    apply mul_right_cancel₀ hquad
    rw [← hleft, hright]
  have hbase : lam * alpha ^ 2 = -alpha := by
    calc
      lam * alpha ^ 2 = alpha * (alpha * lam) := by ring
      _ = -alpha := by rw [hscale]; ring
  calc
    deriv (g^[2 ^ n - 1]) 1 = lam ^ n * alpha ^ (2 * n) := by simpa [h, N] using heq
    _ = (lam * alpha ^ 2) ^ n := by rw [mul_pow]; ring
    _ = (-alpha) ^ n := by rw [hbase]

/-- **Quadratic Feigenbaum postcritical product law.**  The product of all derivative values
encountered after the critical value and before dyadic time `2^n` is exactly `(-alpha)^n`. -/
theorem feigenbaum_quadratic_postcritical_product
    {g : ℂ → ℂ} {alpha lam : ℂ}
    (hEven : Function.Even g) (hscale : alpha * lam = -1)
    (hFE : ∀ x, g (g x) = lam * g (alpha * x))
    (hg0 : g 0 = 1) (hg : ContDiff ℂ 2 g)
    (hcrit : deriv g 0 = 0)
    (hquad : iteratedDeriv 2 g 0 ≠ 0) :
    ∀ n : ℕ,
      (∏ j ∈ Finset.range (2 ^ n - 1),
        deriv g ((g^[j + 1]) 0)) = (-alpha) ^ n := by
  intro n
  have hd := deriv_iterate_eq_orbitProduct (hg.differentiable (by norm_num))
    (2 ^ n - 1) 1
  have horbit (j : ℕ) : (g^[j]) 1 = (g^[j + 1]) 0 := by
    simpa only [hg0, Nat.succ_eq_add_one] using
      (Function.iterate_succ_apply g j 0).symm
  rw [feigenbaum_quadratic_postcritical_deriv hEven hscale hFE hg0 hg hcrit hquad n] at hd
  simp_rw [horbit] at hd
  exact hd.symm

end GaloisForLFunctions
