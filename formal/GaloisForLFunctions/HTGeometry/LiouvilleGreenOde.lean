import Mathlib
import GaloisForLFunctions.HTGeometry.LiouvilleGreenPhaseErrorBound

/-!
# The Liouville–Green ratio of an exact solution obeys its Volterra equation

For `Φ'' = Q Φ` with `Q = A^{-4}` and `Ξ' = A^{-2}` — that is, `A = Q^{-1/4}` and `Ξ = ∫ √Q` — the
Liouville–Green approximant is `G = A e^{-Ξ}`, and

```text
G'  = (A' − 1/A) e^{−Ξ} ,        G'' = Q G + A'' e^{−Ξ} ,
```

the two middle terms cancelling identically because `A` and the phase speed are tied by
`A² · Ξ' = 1`.  Hence the Wronskian `H = Φ'G − ΦG'` satisfies `H' = −A'' e^{−Ξ} Φ`, and the ratio
`R = Φ/G` satisfies `R' = H e^{2Ξ}/A²`.

One integration by parts — against the primitive `(e^{2Ξ(t)} − e^{2Ξ(y)})/2` of `e^{2Ξ}/A²`, chosen
to vanish at `y` — collapses the resulting nested integral to a single Volterra equation with the
bounded kernel `lgPhaseKernel`.  No change of variable is performed anywhere: the phase enters only
as the explicit function `Ξ`.
-/

noncomputable section

open Set MeasureTheory intervalIntegral

namespace GaloisForLFunctions.HTGeometry

variable {a b : ℝ} {A A' A'' Φ Φ' Φ'' Ξ : ℝ → ℝ}

/-- The Liouville–Green approximant `A e^{−Ξ}`. -/
def lgApprox (A Ξ : ℝ → ℝ) (y : ℝ) : ℝ := A y * Real.exp (-(Ξ y))

/-- Its derivative. -/
def lgApproxDeriv (A A' Ξ : ℝ → ℝ) (y : ℝ) : ℝ := (A' y - 1 / A y) * Real.exp (-(Ξ y))

/-- The Wronskian of the exact solution against the approximant. -/
def lgWronskian (A A' Ξ Φ Φ' : ℝ → ℝ) (y : ℝ) : ℝ :=
  Φ' y * lgApprox A Ξ y - Φ y * lgApproxDeriv A A' Ξ y

theorem hasDerivAt_lgApprox (hA : ∀ x, HasDerivAt A (A' x) x)
    (hΞ : ∀ x, HasDerivAt Ξ (1 / A x ^ (2 : ℕ)) x) (hApos : ∀ x, 0 < A x) (y : ℝ) :
    HasDerivAt (lgApprox A Ξ) (lgApproxDeriv A A' Ξ y) y := by
  have hneg : HasDerivAt (fun x : ℝ => -(Ξ x)) (-(1 / A y ^ (2 : ℕ))) y := (hΞ y).neg
  have hexp : HasDerivAt (fun x => Real.exp (-(Ξ x)))
      (-(1 / A y ^ (2 : ℕ)) * Real.exp (-(Ξ y))) y := by
    have h := hneg.exp
    refine h.congr_deriv ?_
    ring
  have h := (hA y).mul hexp
  refine h.congr_deriv ?_
  rw [lgApproxDeriv]
  have hA0 : A y ≠ 0 := (hApos y).ne'
  field_simp
  ring

theorem hasDerivAt_lgApproxDeriv (hA : ∀ x, HasDerivAt A (A' x) x)
    (hA' : ∀ x, HasDerivAt A' (A'' x) x)
    (hΞ : ∀ x, HasDerivAt Ξ (1 / A x ^ (2 : ℕ)) x) (hApos : ∀ x, 0 < A x) (y : ℝ) :
    HasDerivAt (lgApproxDeriv A A' Ξ)
      ((A'' y + 1 / A y ^ (3 : ℕ)) * Real.exp (-(Ξ y))) y := by
  have hA0 : A y ≠ 0 := (hApos y).ne'
  have hinv : HasDerivAt (fun x => 1 / A x) ((0 * A y - 1 * A' y) / A y ^ (2 : ℕ)) y :=
    HasDerivAt.fun_div (hasDerivAt_const y (1 : ℝ)) (hA y) hA0
  have hbase : HasDerivAt (fun x => A' x - 1 / A x)
      (A'' y - (0 * A y - 1 * A' y) / A y ^ (2 : ℕ)) y := (hA' y).sub hinv
  have hneg : HasDerivAt (fun x : ℝ => -(Ξ x)) (-(1 / A y ^ (2 : ℕ))) y := (hΞ y).neg
  have hexp : HasDerivAt (fun x => Real.exp (-(Ξ x)))
      (-(1 / A y ^ (2 : ℕ)) * Real.exp (-(Ξ y))) y := by
    have h := hneg.exp
    refine h.congr_deriv ?_
    ring
  have h := hbase.mul hexp
  refine h.congr_deriv ?_
  field_simp
  ring

/-- **The Wronskian derivative is the error-control density.** -/
theorem hasDerivAt_lgWronskian (hA : ∀ x, HasDerivAt A (A' x) x)
    (hA' : ∀ x, HasDerivAt A' (A'' x) x)
    (hΞ : ∀ x, HasDerivAt Ξ (1 / A x ^ (2 : ℕ)) x) (hApos : ∀ x, 0 < A x)
    (hΦ : ∀ x, HasDerivAt Φ (Φ' x) x) (hΦ' : ∀ x, HasDerivAt Φ' (Φ'' x) x)
    (hode : ∀ x, Φ'' x = (1 / A x ^ (4 : ℕ)) * Φ x) (y : ℝ) :
    HasDerivAt (lgWronskian A A' Ξ Φ Φ')
      (-(Φ y * A'' y * Real.exp (-(Ξ y)))) y := by
  have hA0 : A y ≠ 0 := (hApos y).ne'
  have h1 := (hΦ' y).mul (hasDerivAt_lgApprox hA hΞ hApos y)
  have h2 := (hΦ y).mul (hasDerivAt_lgApproxDeriv hA hA' hΞ hApos y)
  have h := h1.sub h2
  refine h.congr_deriv ?_
  rw [hode y, lgApprox, lgApproxDeriv]
  field_simp
  ring

/-- The Liouville–Green ratio. -/
def lgRatio (A Ξ Φ : ℝ → ℝ) (y : ℝ) : ℝ := Φ y / lgApprox A Ξ y

theorem hasDerivAt_lgRatio (hA : ∀ x, HasDerivAt A (A' x) x)
    (hΞ : ∀ x, HasDerivAt Ξ (1 / A x ^ (2 : ℕ)) x) (hApos : ∀ x, 0 < A x)
    (hΦ : ∀ x, HasDerivAt Φ (Φ' x) x) (y : ℝ) :
    HasDerivAt (lgRatio A Ξ Φ)
      (lgWronskian A A' Ξ Φ Φ' y * Real.exp (2 * Ξ y) / A y ^ (2 : ℕ)) y := by
  have hA0 : A y ≠ 0 := (hApos y).ne'
  have hGpos : lgApprox A Ξ y ≠ 0 := by
    rw [lgApprox]
    have := Real.exp_pos (-(Ξ y))
    positivity
  have h := HasDerivAt.fun_div (hΦ y) (hasDerivAt_lgApprox hA hΞ hApos y) hGpos
  refine h.congr_deriv ?_
  have hsq : Real.exp (-(Ξ y)) ^ (2 : ℕ) * Real.exp (2 * Ξ y) = 1 := by
    have hpow : Real.exp (-(Ξ y)) ^ (2 : ℕ) = Real.exp (-(Ξ y)) * Real.exp (-(Ξ y)) := by ring
    rw [hpow, ← Real.exp_add, ← Real.exp_add,
      show -(Ξ y) + -(Ξ y) + 2 * Ξ y = 0 by ring, Real.exp_zero]
  have hG2 : lgApprox A Ξ y ^ (2 : ℕ) * Real.exp (2 * Ξ y) = A y ^ (2 : ℕ) := by
    rw [lgApprox, mul_pow]
    calc A y ^ (2 : ℕ) * Real.exp (-(Ξ y)) ^ (2 : ℕ) * Real.exp (2 * Ξ y)
        = A y ^ (2 : ℕ) * (Real.exp (-(Ξ y)) ^ (2 : ℕ) * Real.exp (2 * Ξ y)) := by ring
      _ = A y ^ (2 : ℕ) := by rw [hsq]; ring
  rw [lgWronskian, div_eq_div_iff (pow_ne_zero 2 hGpos) (pow_ne_zero 2 hA0), ← hG2]
  ring

/-! ## The Volterra equation -/

set_option maxHeartbeats 1600000 in
/-- **The Liouville–Green ratio obeys its Volterra equation.**  One integration by parts against the
primitive of `e^{2Ξ}/A²` vanishing at the left end. -/
theorem isPhaseLGSolution_lgRatio
    (hA : ∀ x, HasDerivAt A (A' x) x) (hA' : ∀ x, HasDerivAt A' (A'' x) x)
    (hA''c : Continuous A'')
    (hΞ : ∀ x, HasDerivAt Ξ (1 / A x ^ (2 : ℕ)) x) (hApos : ∀ x, 0 < A x)
    (hΦ : ∀ x, HasDerivAt Φ (Φ' x) x) (hΦ' : ∀ x, HasDerivAt Φ' (Φ'' x) x)
    (hode : ∀ x, Φ'' x = (1 / A x ^ (4 : ℕ)) * Φ x)
    (hRb : lgRatio A Ξ Φ b = 1)
    (hHb : lgWronskian A A' Ξ Φ Φ' b = 0) :
    IsPhaseLGSolution b Ξ (fun t => A t * A'' t) (lgRatio A Ξ Φ) a := by
  have hAc : Continuous A := continuous_iff_continuousAt.2 fun x => (hA x).continuousAt
  have hA'c : Continuous A' := continuous_iff_continuousAt.2 fun x => (hA' x).continuousAt
  have hΦc : Continuous Φ := continuous_iff_continuousAt.2 fun x => (hΦ x).continuousAt
  have hΦ'c : Continuous Φ' := continuous_iff_continuousAt.2 fun x => (hΦ' x).continuousAt
  have hΞc : Continuous Ξ := continuous_iff_continuousAt.2 fun x => (hΞ x).continuousAt
  have hAne : ∀ x, A x ≠ 0 := fun x => (hApos x).ne'
  have hGc : Continuous (lgApprox A Ξ) := by
    unfold lgApprox
    fun_prop
  have hExpc : Continuous fun x : ℝ => Real.exp (-(Ξ x)) := by fun_prop
  have hGdc : Continuous (lgApproxDeriv A A' Ξ) := by
    unfold lgApproxDeriv
    have hdiv : Continuous fun x : ℝ => 1 / A x := continuous_const.div hAc hAne
    exact (hA'c.sub hdiv).mul hExpc
  have hHc : Continuous (lgWronskian A A' Ξ Φ Φ') := by
    unfold lgWronskian
    exact (hΦ'c.mul hGc).sub (hΦc.mul hGdc)
  intro y hy
  have hyb : y ≤ b := hy.2
  set H : ℝ → ℝ := lgWronskian A A' Ξ Φ Φ' with hH
  set U : ℝ → ℝ := fun τ => (Real.exp (2 * Ξ τ) - Real.exp (2 * Ξ y)) / 2 with hU
  have hUd : ∀ t : ℝ, HasDerivAt U (Real.exp (2 * Ξ t) / A t ^ (2 : ℕ)) t := by
    intro t
    have hin : HasDerivAt (fun x : ℝ => 2 * Ξ x) (2 * (1 / A t ^ (2 : ℕ))) t := (hΞ t).const_mul 2
    have hexp : HasDerivAt (fun x : ℝ => Real.exp (2 * Ξ x))
        (Real.exp (2 * Ξ t) * (2 * (1 / A t ^ (2 : ℕ)))) t := hin.exp
    have h := (hexp.sub_const (Real.exp (2 * Ξ y))).div_const 2
    refine h.congr_deriv ?_
    field_simp
  have hUc : Continuous U := continuous_iff_continuousAt.2 fun t => (hUd t).continuousAt
  have hU'c : Continuous fun t : ℝ => Real.exp (2 * Ξ t) / A t ^ (2 : ℕ) := by
    refine Continuous.div (Real.continuous_exp.comp (by fun_prop)) (hAc.pow 2) ?_
    intro x
    exact pow_ne_zero 2 (hAne x)
  have hH'c : Continuous fun t : ℝ => -(Φ t * A'' t * Real.exp (-(Ξ t))) :=
    ((hΦc.mul hA''c).mul hExpc).neg
  -- integration by parts
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := H) (u' := fun t => -(Φ t * A'' t * Real.exp (-(Ξ t))))
    (v := U) (v' := fun t => Real.exp (2 * Ξ t) / A t ^ (2 : ℕ))
    (a := y) (b := b)
    (fun t _ => hasDerivAt_lgWronskian hA hA' hΞ hApos hΦ hΦ' hode t)
    (fun t _ => hUd t) (hH'c.intervalIntegrable y b) (hU'c.intervalIntegrable y b)
  have hUy : U y = 0 := by
    rw [hU]
    simp
  have hHbz : H b = 0 := hHb
  rw [hHbz, hUy] at hibp
  -- the ratio's derivative is the product
  have hRd : ∀ t : ℝ, HasDerivAt (lgRatio A Ξ Φ) (H t * (Real.exp (2 * Ξ t) / A t ^ (2 : ℕ))) t := by
    intro t
    have h := hasDerivAt_lgRatio (A' := A') (Φ' := Φ') hA hΞ hApos hΦ t
    refine h.congr_deriv ?_
    rw [hH]
    field_simp
  have hRint : IntervalIntegrable (fun t => H t * (Real.exp (2 * Ξ t) / A t ^ (2 : ℕ))) volume y b :=
    (hHc.mul hU'c).intervalIntegrable y b
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hRd t) hRint
  -- rewrite the two integrals
  have hkey : (∫ t in y..b, H t * (Real.exp (2 * Ξ t) / A t ^ (2 : ℕ)))
      = ∫ t in y..b, lgPhaseKernel Ξ y t * (A t * A'' t) * lgRatio A Ξ Φ t := by
    rw [hibp]
    simp only [zero_mul, mul_zero, sub_zero, zero_sub]
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun t _ => ?_
    show -(-(Φ t * A'' t * Real.exp (-(Ξ t))) * U t)
      = lgPhaseKernel Ξ y t * (A t * A'' t) * lgRatio A Ξ Φ t
    have hGne : lgApprox A Ξ t ≠ 0 := by
      rw [lgApprox]
      have := Real.exp_pos (-(Ξ t))
      have := hApos t
      positivity
    have hΦeq : Φ t = lgRatio A Ξ Φ t * (A t * Real.exp (-(Ξ t))) := by
      rw [lgRatio, lgApprox]
      field_simp
      rw [mul_div_assoc, div_self (hAne t), mul_one]
    have hker : lgPhaseKernel Ξ y t = U t * Real.exp (-(2 * Ξ t)) := by
      rw [lgPhaseKernel, hU]
      have h1 : Real.exp (2 * Ξ t) * Real.exp (-(2 * Ξ t)) = 1 := by
        rw [← Real.exp_add]
        simp
      have h2 : Real.exp (2 * Ξ y) * Real.exp (-(2 * Ξ t)) = Real.exp (-(2 * (Ξ t - Ξ y))) := by
        rw [← Real.exp_add]
        congr 1
        ring
      field_simp
      linarith [h1, h2]
    have hsplit : Real.exp (-(Ξ t)) * Real.exp (-(Ξ t)) = Real.exp (-(2 * Ξ t)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hker, hΦeq]
    calc -(-(lgRatio A Ξ Φ t * (A t * Real.exp (-(Ξ t))) * A'' t * Real.exp (-(Ξ t))) * U t)
        = U t * (A t * A'' t) * lgRatio A Ξ Φ t
            * (Real.exp (-(Ξ t)) * Real.exp (-(Ξ t))) := by ring
      _ = U t * Real.exp (-(2 * Ξ t)) * (A t * A'' t) * lgRatio A Ξ Φ t := by
          rw [hsplit]; ring
  rw [hkey] at hFTC
  rw [hRb] at hFTC
  linarith [hFTC]

/-! ## The two-sided Liouville–Green estimate -/

set_option maxHeartbeats 1600000 in
/-- **Olver's two-sided Liouville–Green estimate, in the original variable.**  The exact solution
normalized to the approximant at the right endpoint is trapped between `2 − E` and `E` times it,
with `E = exp(½ ∫ |A A''|)` and `A = Q^{−1/4}`. -/
theorem lgRatio_two_sided (hab : a ≤ b)
    (hA : ∀ x, HasDerivAt A (A' x) x) (hA' : ∀ x, HasDerivAt A' (A'' x) x)
    (hA''c : Continuous A'')
    (hΞ : ∀ x, HasDerivAt Ξ (1 / A x ^ (2 : ℕ)) x) (hApos : ∀ x, 0 < A x)
    (hΦ : ∀ x, HasDerivAt Φ (Φ' x) x) (hΦ' : ∀ x, HasDerivAt Φ' (Φ'' x) x)
    (hode : ∀ x, Φ'' x = (1 / A x ^ (4 : ℕ)) * Φ x)
    (hRb : lgRatio A Ξ Φ b = 1)
    (hHb : lgWronskian A A' Ξ Φ Φ' b = 0)
    {y : ℝ} (hy : y ∈ Icc a b) :
    2 - Real.exp ((1 / 2) * ∫ t in y..b, |A t * A'' t|) ≤ lgRatio A Ξ Φ y ∧
      lgRatio A Ξ Φ y ≤ Real.exp ((1 / 2) * ∫ t in y..b, |A t * A'' t|) := by
  have hAc : Continuous A := continuous_iff_continuousAt.2 fun x => (hA x).continuousAt
  have hΦc : Continuous Φ := continuous_iff_continuousAt.2 fun x => (hΦ x).continuousAt
  have hΞc : Continuous Ξ := continuous_iff_continuousAt.2 fun x => (hΞ x).continuousAt
  have hAne : ∀ x, A x ≠ 0 := fun x => (hApos x).ne'
  have hGne : ∀ x, lgApprox A Ξ x ≠ 0 := by
    intro x
    rw [lgApprox]
    have := Real.exp_pos (-(Ξ x))
    have := hApos x
    positivity
  have hRc : Continuous (lgRatio A Ξ Φ) := by
    unfold lgRatio
    refine hΦc.div ?_ hGne
    unfold lgApprox
    fun_prop
  have hmono : Monotone Ξ := by
    have hderiv : ∀ x : ℝ, 0 < deriv Ξ x := by
      intro x
      rw [(hΞ x).deriv]
      have := hApos x
      positivity
    have hdiff : Differentiable ℝ Ξ := fun x => (hΞ x).differentiableAt
    exact (StrictMono.monotone (strictMono_of_deriv_pos hderiv))
  have hψc : Continuous fun t : ℝ => A t * A'' t := hAc.mul hA''c
  exact phaseLG_two_sided hab hΞc hmono hRc hψc
    (isPhaseLGSolution_lgRatio hA hA' hA''c hΞ hApos hΦ hΦ' hode hRb hHb) hy

end GaloisForLFunctions.HTGeometry
