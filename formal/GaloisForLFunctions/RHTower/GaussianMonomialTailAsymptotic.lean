import GaloisForLFunctions.RHTower.FuchsProlateScale
import GaloisForLFunctions.HTGeometry.ExpSquareRayTail
import Mathlib.Analysis.Calculus.LHopital

/-!
# Sharp Gaussian monomial tail asymptotics

For every positive Gaussian rate `b`, the tail of `x^m exp (-b x^2)` has the exact leading
term

`a^(m-1) exp (-b a^2) / (2b)`.

The positive-degree theorem is proved by differentiating the moving tail and applying the
`0/0` form of L'Hôpital's rule.  Degree zero is handled separately because its natural leading
power is `a⁻¹`.  These exact constants are the scalar analytic input for polynomial-Gaussian and
Hermite leakage asymptotics.
-/

open MeasureTheory Set Filter Topology
open scoped Real

noncomputable section

namespace RHTower

/-- Every natural monomial is integrable against a positive-rate Gaussian on the positive ray. -/
theorem integrableOn_pow_mul_exp_neg_mul_sq_Ioi_zero
    (m : ℕ) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun x : ℝ => x ^ m * Real.exp (-(b * x ^ 2))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_sq (b := b) hb
    (s := (m : ℝ)) (by have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith)
  refine h.congr_fun ?_ measurableSet_Ioi
  intro x hx
  change x ^ (m : ℝ) * Real.exp (-b * x ^ 2) =
    x ^ m * Real.exp (-(b * x ^ 2))
  rw [Real.rpow_natCast]
  congr 2 <;> ring

/-- Differentiating a moving Gaussian-monomial tail gives minus its boundary density. -/
theorem hasDerivAt_gaussianMonomialTail
    (m : ℕ) {b : ℝ} (hb : 0 < b) {a : ℝ} (ha : 0 < a) :
    HasDerivAt
      (fun t : ℝ => ∫ x in Ioi t, x ^ m * Real.exp (-(b * x ^ 2)))
      (-(a ^ m * Real.exp (-(b * a ^ 2)))) a := by
  let f : ℝ → ℝ := fun x => x ^ m * Real.exp (-(b * x ^ 2))
  have hfcont : Continuous f := by
    dsimp [f]
    fun_prop
  have hfint : IntegrableOn f (Ioi 0) :=
    integrableOn_pow_mul_exp_neg_mul_sq_Ioi_zero m hb
  have hinterval : IntervalIntegrable f volume 0 a := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ha.le]
    exact hfint.mono_set Ioc_subset_Ioi_self
  have hprimitive : HasDerivAt (fun t : ℝ => ∫ x in 0..t, f x) (f a) a :=
    intervalIntegral.integral_hasDerivAt_right hinterval
      (hfcont.stronglyMeasurableAtFilter volume (nhds a)) hfcont.continuousAt
  have hmodel : HasDerivAt
      (fun t : ℝ => (∫ x in Ioi 0, f x) - ∫ x in 0..t, f x) (-f a) a := by
    exact hprimitive.const_sub (∫ x in Ioi 0, f x)
  have heq :
      (fun t : ℝ => ∫ x in Ioi t, f x) =ᶠ[nhds a]
        (fun t : ℝ => (∫ x in Ioi 0, f x) - ∫ x in 0..t, f x) := by
    filter_upwards [Ioi_mem_nhds ha] with t ht
    rw [← intervalIntegral.integral_Ioi_sub_Ioi hfint ht.le]
    ring
  simpa only [f] using hmodel.congr_of_eventuallyEq heq

/-- Sharp positive-degree Gaussian-monomial tail asymptotic. -/
theorem tendsto_gaussianMonomialTail_div_leading
    (m : ℕ) (hm : 2 ≤ m) {b : ℝ} (hb : 0 < b) :
    Tendsto
      (fun a : ℝ =>
        (∫ x in Ioi a, x ^ m * Real.exp (-(b * x ^ 2))) /
          (a ^ (m - 1) * Real.exp (-(b * a ^ 2))))
      atTop (nhds (1 / (2 * b))) := by
  let F : ℝ → ℝ := fun a => ∫ x in Ioi a, x ^ m * Real.exp (-(b * x ^ 2))
  let G : ℝ → ℝ := fun a => a ^ (m - 1) * Real.exp (-(b * a ^ 2))
  let F' : ℝ → ℝ := fun a => -(a ^ m * Real.exp (-(b * a ^ 2)))
  let G' : ℝ → ℝ := fun a =>
    ((m - 1 : ℕ) : ℝ) * a ^ (m - 2) * Real.exp (-(b * a ^ 2)) -
      2 * b * a ^ m * Real.exp (-(b * a ^ 2))
  have hF' : ∀ᶠ a : ℝ in atTop, HasDerivAt F (F' a) a := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
    exact hasDerivAt_gaussianMonomialTail m hb ha
  have hG' : ∀ᶠ a : ℝ in atTop, HasDerivAt G (G' a) a := by
    filter_upwards with a
    have hpow := hasDerivAt_pow (m - 1) a
    have hinner : HasDerivAt (fun x : ℝ => -(b * x ^ 2)) (-2 * b * a) a := by
      have hraw := ((hasDerivAt_pow 2 a).const_mul b).neg
      have hfun : -(fun x : ℝ => b * x ^ 2) = (fun x : ℝ => -(b * x ^ 2)) := by
        rfl
      rw [hfun] at hraw
      exact hraw.congr_deriv (by ring)
    have hexp := hinner.exp
    dsimp only [G, G']
    apply (hpow.mul hexp).congr_deriv
    have hpowa : a ^ (m - 1) = a ^ (m - 2) * a := by
      calc
        a ^ (m - 1) = a ^ ((m - 2) + 1) := by congr 1 <;> omega
        _ = a ^ (m - 2) * a := by rw [pow_succ]
    have hpowm : a ^ m = a ^ (m - 2) * a ^ 2 := by
      calc
        a ^ m = a ^ ((m - 2) + 2) := by congr 1 <;> omega
        _ = a ^ (m - 2) * a ^ 2 := by rw [pow_add]
    rw [show m - 1 - 1 = m - 2 by omega, hpowa, hpowm]
    ring
  have hG'ne : ∀ᶠ a : ℝ in atTop, G' a ≠ 0 := by
    have hquad : Tendsto (fun a : ℝ => 2 * b * a ^ 2) atTop atTop :=
      Tendsto.const_mul_atTop (by positivity)
        (Filter.tendsto_pow_atTop (by norm_num))
    filter_upwards [eventually_gt_atTop (0 : ℝ),
      hquad.eventually (eventually_gt_atTop (((m - 1 : ℕ) : ℝ)))] with a ha hlarge
    have hpowpos : 0 < a ^ (m - 2) := pow_pos ha _
    have hexppos : 0 < Real.exp (-(b * a ^ 2)) := Real.exp_pos _
    have hfactor : ((m - 1 : ℕ) : ℝ) - 2 * b * a ^ 2 < 0 := by linarith
    have hrewrite : G' a =
        a ^ (m - 2) * Real.exp (-(b * a ^ 2)) *
          (((m - 1 : ℕ) : ℝ) - 2 * b * a ^ 2) := by
      dsimp only [G']
      have hpowm : a ^ m = a ^ (m - 2) * a ^ 2 := by
        calc
          a ^ m = a ^ ((m - 2) + 2) := by congr 1 <;> omega
          _ = a ^ (m - 2) * a ^ 2 := by rw [pow_add]
      rw [hpowm]
      ring
    rw [hrewrite]
    exact mul_ne_zero (mul_ne_zero hpowpos.ne' hexppos.ne') hfactor.ne
  have hF0 : Tendsto F atTop (nhds 0) := by
    dsimp only [F]
    exact MeasureTheory.tendsto_integral_Ioi_zero tendsto_id
  have hG0 : Tendsto G atTop (nhds 0) := by
    dsimp only [G]
    exact tendsto_pow_mul_exp_neg_mul_sq_atTop_nhds_zero (m - 1) hb
  have hsqInv : Tendsto (fun a : ℝ => (a ^ 2)⁻¹) atTop (nhds 0) :=
    (Filter.tendsto_pow_atTop (by norm_num)).inv_tendsto_atTop
  have hden : Tendsto
      (fun a : ℝ => (((m - 1 : ℕ) : ℝ) * (a ^ 2)⁻¹ - 2 * b))
      atTop (nhds (0 - 2 * b)) :=
    by simpa using
      (hsqInv.const_mul (((m - 1 : ℕ) : ℝ))).sub (tendsto_const_nhds :
        Tendsto (fun _ : ℝ => 2 * b) atTop (nhds (2 * b)))
  have hratioModel : Tendsto
      (fun a : ℝ => (-1 : ℝ) /
        (((m - 1 : ℕ) : ℝ) * (a ^ 2)⁻¹ - 2 * b))
      atTop (nhds ((-1 : ℝ) / (0 - 2 * b))) :=
    tendsto_const_nhds.div hden (by linarith)
  have hratio : Tendsto (fun a => F' a / G' a) atTop (nhds (1 / (2 * b))) := by
    have hlim : (-1 : ℝ) / (0 - 2 * b) = 1 / (2 * b) := by
      field_simp [hb.ne']
      ring
    rw [hlim] at hratioModel
    refine hratioModel.congr' ?_
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with a ha
    dsimp only [F', G']
    have hpow : a ^ m = a ^ (m - 2) * a ^ 2 := by
      calc
        a ^ m = a ^ ((m - 2) + 2) := by congr 1 <;> omega
        _ = a ^ (m - 2) * a ^ 2 := by rw [pow_add]
    rw [hpow]
    field_simp [ha, Real.exp_ne_zero]
  exact HasDerivAt.lhopital_zero_atTop hF' hG' hG'ne hF0 hG0 hratio

/-- Sharp degree-zero Gaussian tail asymptotic. -/
theorem tendsto_gaussianTail_div_leading {b : ℝ} (hb : 0 < b) :
    Tendsto
      (fun a : ℝ =>
        (∫ x in Ioi a, Real.exp (-(b * x ^ 2))) /
          (a⁻¹ * Real.exp (-(b * a ^ 2))))
      atTop (nhds (1 / (2 * b))) := by
  let F : ℝ → ℝ := fun a => ∫ x in Ioi a, Real.exp (-(b * x ^ 2))
  let G : ℝ → ℝ := fun a => a⁻¹ * Real.exp (-(b * a ^ 2))
  let F' : ℝ → ℝ := fun a => -Real.exp (-(b * a ^ 2))
  let G' : ℝ → ℝ := fun a =>
    -((a ^ 2)⁻¹ + 2 * b) * Real.exp (-(b * a ^ 2))
  have hF' : ∀ᶠ a : ℝ in atTop, HasDerivAt F (F' a) a := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
    simpa only [pow_zero, one_mul] using hasDerivAt_gaussianMonomialTail 0 hb ha
  have hG' : ∀ᶠ a : ℝ in atTop, HasDerivAt G (G' a) a := by
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with a ha
    have hinv := hasDerivAt_inv ha
    have hinner : HasDerivAt (fun x : ℝ => -(b * x ^ 2)) (-2 * b * a) a := by
      have hraw := ((hasDerivAt_pow 2 a).const_mul b).neg
      have hfun : -(fun x : ℝ => b * x ^ 2) = (fun x : ℝ => -(b * x ^ 2)) := by
        rfl
      rw [hfun] at hraw
      exact hraw.congr_deriv (by ring)
    have hexp := hinner.exp
    dsimp only [G, G']
    apply (hinv.mul hexp).congr_deriv
    field_simp [ha]
    ring
  have hG'ne : ∀ᶠ a : ℝ in atTop, G' a ≠ 0 := by
    filter_upwards with a
    dsimp only [G']
    exact mul_ne_zero (neg_ne_zero.mpr (by positivity)) (Real.exp_ne_zero _)
  have hF0 : Tendsto F atTop (nhds 0) := by
    dsimp only [F]
    exact MeasureTheory.tendsto_integral_Ioi_zero tendsto_id
  have hG0 : Tendsto G atTop (nhds 0) := by
    dsimp only [G]
    have hinv : Tendsto (fun a : ℝ => a⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
    simpa using hinv.mul (GaloisForLFunctions.tendsto_expNegSq_atTop hb)
  have hsqInv : Tendsto (fun a : ℝ => (a ^ 2)⁻¹) atTop (nhds 0) :=
    (Filter.tendsto_pow_atTop (by norm_num)).inv_tendsto_atTop
  have hratioModel : Tendsto (fun a : ℝ => 1 / ((a ^ 2)⁻¹ + 2 * b))
      atTop (nhds (1 / (0 + 2 * b))) :=
    tendsto_const_nhds.div (hsqInv.add tendsto_const_nhds) (by positivity)
  have hratio : Tendsto (fun a => F' a / G' a) atTop (nhds (1 / (2 * b))) := by
    convert hratioModel using 1
    · apply funext
      intro a
      dsimp only [F', G']
      have hd : (a ^ 2)⁻¹ + 2 * b ≠ 0 := by positivity
      field_simp [Real.exp_ne_zero, hd]
    · ring
  exact HasDerivAt.lhopital_zero_atTop hF' hG' hG'ne hF0 hG0 hratio

end RHTower
