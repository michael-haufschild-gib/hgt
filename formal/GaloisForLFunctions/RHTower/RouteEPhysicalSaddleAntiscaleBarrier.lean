import GaloisForLFunctions.RHTower.RouteECriticalTerminalVarianceMinimax
import GaloisForLFunctions.RHTower.GibbsAntiscaleDeterminantOddCube
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Physical-saddle antiscale barrier: exact analytic core

This module proves exact identities behind Route E physical-saddle no-go.

* full-aperture exponential moments are factorial moments;
* antiscale quadratic has unique centered correction c = pi / a;
* sharp full-aperture residual is pi squared / a cubed;
* each finite Euler factor loses exactly transverse antiscale energy.

Prime-number-theorem transport from these continuous identities to moving finite prime products is
a separate analytic layer; no asymptotic or source hypothesis is hidden here.
-/

namespace RHTower

open MeasureTheory Set

noncomputable section

/-- Full-aperture exponential moment on logarithmic terminal distance. -/
def routeEFullApertureMoment (a : ℝ) (k : ℕ) : ℝ :=
  ∫ v : ℝ in Set.Ioi 0, Real.exp (-a * v) * v ^ k

private theorem integrableOn_routeEFullApertureMoment
    {a : ℝ} (ha : 0 < a) (k : ℕ) :
    IntegrableOn (fun v : ℝ => Real.exp (-a * v) * v ^ k) (Set.Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (s := (k : ℝ)) (p := (1 : ℝ)) (b := a)
    (by have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith) le_rfl ha
  simpa [Real.rpow_natCast, mul_comm] using h

/-- Exact exponential factorial-moment law. -/
theorem routeEFullApertureMoment_eq
    {a : ℝ} (ha : 0 < a) (k : ℕ) :
    routeEFullApertureMoment a k =
      (1 / a) ^ (k + 1) * (k.factorial : ℝ) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (k : ℝ) + 1) (r := a) (by positivity) ha
  unfold routeEFullApertureMoment
  convert h using 1
  · apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    simp [Real.rpow_natCast, mul_comm]
  · rw [Real.Gamma_nat_eq_factorial]
    rw [show (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]

@[simp] theorem routeEFullApertureMoment_zero
    {a : ℝ} (ha : 0 < a) :
    routeEFullApertureMoment a 0 = 1 / a := by
  rw [routeEFullApertureMoment_eq ha]
  simp

@[simp] theorem routeEFullApertureMoment_one
    {a : ℝ} (ha : 0 < a) :
    routeEFullApertureMoment a 1 = 1 / a ^ 2 := by
  rw [routeEFullApertureMoment_eq ha]
  norm_num

@[simp] theorem routeEFullApertureMoment_two
    {a : ℝ} (ha : 0 < a) :
    routeEFullApertureMoment a 2 = 2 / a ^ 3 := by
  rw [routeEFullApertureMoment_eq ha]
  norm_num
  ring

/-- Full-aperture first-resonance quadratic with correction c. -/
def routeEFullApertureQuadratic (a c : ℝ) : ℝ :=
  ∫ v : ℝ in Set.Ioi 0,
    Real.exp (-a * v) * (c - Real.pi * v) ^ 2

/-- Exact completed-square law for full aperture. -/
theorem routeEFullApertureQuadratic_eq
    {a : ℝ} (ha : 0 < a) (c : ℝ) :
    routeEFullApertureQuadratic a c =
      (c - Real.pi / a) ^ 2 / a + Real.pi ^ 2 / a ^ 3 := by
  have h0 := integrableOn_routeEFullApertureMoment ha 0
  have h1 := integrableOn_routeEFullApertureMoment ha 1
  have h2 := integrableOn_routeEFullApertureMoment ha 2
  have hfun :
      (fun v : ℝ => Real.exp (-a * v) * (c - Real.pi * v) ^ 2) =
        (fun v : ℝ =>
          c ^ 2 * (Real.exp (-a * v) * v ^ 0) -
            (2 * c * Real.pi) * (Real.exp (-a * v) * v ^ 1) +
            Real.pi ^ 2 * (Real.exp (-a * v) * v ^ 2)) := by
    funext v
    ring
  unfold routeEFullApertureQuadratic
  rw [hfun]
  calc
    (∫ v : ℝ in Set.Ioi 0,
      c ^ 2 * (Real.exp (-a * v) * v ^ 0) -
        (2 * c * Real.pi) * (Real.exp (-a * v) * v ^ 1) +
        Real.pi ^ 2 * (Real.exp (-a * v) * v ^ 2)) =
        (∫ v : ℝ in Set.Ioi 0,
          c ^ 2 * (Real.exp (-a * v) * v ^ 0) -
            (2 * c * Real.pi) * (Real.exp (-a * v) * v ^ 1)) +
        ∫ v : ℝ in Set.Ioi 0,
          Real.pi ^ 2 * (Real.exp (-a * v) * v ^ 2) :=
      MeasureTheory.integral_add
        ((h0.const_mul (c ^ 2)).sub (h1.const_mul (2 * c * Real.pi)))
        (h2.const_mul (Real.pi ^ 2))
    _ =
        c ^ 2 * routeEFullApertureMoment a 0 -
          (2 * c * Real.pi) * routeEFullApertureMoment a 1 +
          Real.pi ^ 2 * routeEFullApertureMoment a 2 := by
      rw [MeasureTheory.integral_sub
        (h0.const_mul (c ^ 2)) (h1.const_mul (2 * c * Real.pi))]
      rw [MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul]
      rfl
    _ = (c - Real.pi / a) ^ 2 / a + Real.pi ^ 2 / a ^ 3 := by
      rw [routeEFullApertureMoment_zero ha,
        routeEFullApertureMoment_one ha,
        routeEFullApertureMoment_two ha]
      field_simp [ha.ne']
      ring

/-- Sharp full-aperture lower bound. -/
theorem routeEFullApertureQuadratic_lower
    {a : ℝ} (ha : 0 < a) (c : ℝ) :
    Real.pi ^ 2 / a ^ 3 ≤ routeEFullApertureQuadratic a c := by
  rw [routeEFullApertureQuadratic_eq ha]
  have ha0 : 0 ≤ a := ha.le
  have hnonneg : 0 ≤ (c - Real.pi / a) ^ 2 / a := by positivity
  linarith

/-- Unique full-aperture correction is c = pi / a. -/
theorem routeEFullApertureQuadratic_eq_min_iff
    {a : ℝ} (ha : 0 < a) (c : ℝ) :
    routeEFullApertureQuadratic a c = Real.pi ^ 2 / a ^ 3 ↔
      c = Real.pi / a := by
  rw [routeEFullApertureQuadratic_eq ha]
  constructor
  · intro h
    have hzero : (c - Real.pi / a) ^ 2 / a = 0 := by linarith
    have hsquare : (c - Real.pi / a) ^ 2 = 0 := by
      exact (div_eq_zero_iff.1 hzero).resolve_right ha.ne'
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)
  · rintro rfl
    ring

/-- Sharp residual at source-selected full-aperture correction. -/
theorem routeEFullApertureQuadratic_centered
    {a : ℝ} (ha : 0 < a) :
    routeEFullApertureQuadratic a (Real.pi / a) =
      Real.pi ^ 2 / a ^ 3 :=
  (routeEFullApertureQuadratic_eq_min_iff ha _).2 rfl

/-- Exact local Euler deficit. Positive maximum and oscillatory factor differ by antiscale
transverse energy, with no Taylor approximation. -/
theorem routeE_eulerFactor_deficit
    (u phase : ℝ) :
    (1 + u) ^ 2 -
        Complex.normSq
          (1 - (u : ℂ) *
            Complex.exp (((-phase : ℝ) : ℂ) * Complex.I)) =
      u * Complex.normSq
        (1 + Complex.exp ((phase : ℂ) * Complex.I)) := by
  rw [GibbsGas.normSq_one_sub_radius_exp_eq]
  have hplus :
      Complex.normSq
          (1 + Complex.exp ((phase : ℂ) * Complex.I)) =
        (1 + (1 : ℝ) ^ 2) *
          (1 + GibbsGas.criticalEulerTransverseCoordinate 1 phase) := by
    simpa using
      (GibbsGas.normSq_one_add_radius_exp_eq
        (radius := (1 : ℝ)) (phase := phase))
  rw [hplus]
  unfold GibbsGas.criticalEulerTransverseCoordinate
  rw [Real.cos_neg]
  field_simp
  ring

/-- Normalized exact local deficit, denominator form used by logarithmic Euler product. -/
theorem routeE_eulerFactor_normalized_deficit
    {u phase : ℝ} (hu : u ≠ -1) :
    Complex.normSq
          (1 - (u : ℂ) *
            Complex.exp (((-phase : ℝ) : ℂ) * Complex.I)) /
        (1 + u) ^ 2 =
      1 -
        u * Complex.normSq
          (1 + Complex.exp ((phase : ℂ) * Complex.I)) /
            (1 + u) ^ 2 := by
  have h := routeE_eulerFactor_deficit u phase
  have hden : (1 + u) ^ 2 ≠ 0 := by
    apply pow_ne_zero
    intro hzero
    apply hu
    linarith
  have hfactor :
      Complex.normSq
          (1 - (u : ℂ) *
            Complex.exp (((-phase : ℝ) : ℂ) * Complex.I)) =
        (1 + u) ^ 2 -
          u * Complex.normSq
            (1 + Complex.exp ((phase : ℂ) * Complex.I)) := by
    linarith
  rw [hfactor]
  rw [sub_div, div_self hden]

/-- Finite product form of exact Euler deficit. -/
theorem routeE_finiteEuler_normalized_deficit
    {ι : Type*} (s : Finset ι) (radius phase : ι → ℝ)
    (hradius : ∀ i ∈ s, radius i ≠ -1) :
    (∏ i ∈ s,
        Complex.normSq
          (1 - (radius i : ℂ) *
            Complex.exp (((-phase i : ℝ) : ℂ) * Complex.I))) /
      (∏ i ∈ s, (1 + radius i) ^ 2) =
        ∏ i ∈ s,
          (1 -
            radius i * Complex.normSq
              (1 + Complex.exp ((phase i : ℂ) * Complex.I)) /
                (1 + radius i) ^ 2) := by
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  exact routeE_eulerFactor_normalized_deficit (hradius i hi)

end

end RHTower
