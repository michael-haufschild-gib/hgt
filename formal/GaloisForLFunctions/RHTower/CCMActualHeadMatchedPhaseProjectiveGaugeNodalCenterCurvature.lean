import GaloisForLFunctions.RHTower.CCMActualHeadMatchedPhaseProjectiveGaugeNodalSourceShear
import GaloisForLFunctions.RHTower.CCMActualHeadMatchedWallLightQuadraticJet
import Mathlib.Analysis.Calculus.DerivativeTest

/-!
# Center-frequency curvature of the chiral nodal determinant

The fixed source shear already turns each matched CCM source coordinate into determinant-line
crossing orientation. This module differentiates that operator-derived determinant in the spectral
frequency. At the reflection center, its first jet vanishes and its second jet is the negative of
a canonical positive source coefficient:

```text
-2 gauge(n)^(2 : ℕ) * (polar cosine moment(n) + 4π log(n) * oriented first moment(n)).
```

Both source terms are strictly positive at every actual prime-power wall. Consequently every
nonempty finite direct sum of these nodal blocks has strictly negative center curvature and a
local nonpositive determinant chamber. This is source-native: no Xi divisor, zero placement,
Weil-positivity premise, or RH hypothesis occurs.
-/

open Complex MeasureTheory Set Filter Topology Matrix
open scoped BigOperators ComplexConjugate

noncomputable section
namespace RHTower

/-- First spectral jet of the even matched polar cosine profile. -/
def ccmActualHeadMatchedCosinePhaseFirstJet (n : ℕ) (xi : ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..ccmActualHeadMatchedPrimePolarRadius n,
    4 * Real.pi * r * Real.exp (Real.log n / 2) * Real.cosh (r / 2) *
      Real.sin (2 * Real.pi * r * xi)

/-- Second spectral jet of the even matched polar cosine profile. -/
def ccmActualHeadMatchedCosinePhaseSecondJet (n : ℕ) (xi : ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..ccmActualHeadMatchedPrimePolarRadius n,
    8 * Real.pi ^ (2 : ℕ) * r ^ (2 : ℕ) * Real.exp (Real.log n / 2) * Real.cosh (r / 2) *
      Real.cos (2 * Real.pi * r * xi)

/-- Positive polar contribution to center-frequency curvature. -/
def ccmActualHeadMatchedCosinePhaseQuadraticMoment (n : ℕ) : ℝ :=
  ∫ r in (0 : ℝ)..ccmActualHeadMatchedPrimePolarRadius n,
    8 * Real.pi ^ (2 : ℕ) * r ^ (2 : ℕ) * Real.exp (Real.log n / 2) * Real.cosh (r / 2)

theorem hasDerivAt_ccmActualHeadMatchedCosinePhase_integrand
    (n : ℕ) (r xi : ℝ) :
    HasDerivAt
      (fun x : ℝ =>
        Real.exp (Real.log n / 2) * Real.cosh (r / 2) *
          (2 - 2 * Real.cos (2 * Real.pi * r * x)))
      (4 * Real.pi * r * Real.exp (Real.log n / 2) * Real.cosh (r / 2) *
        Real.sin (2 * Real.pi * r * xi)) xi := by
  have hlin : HasDerivAt (fun x : ℝ => 2 * Real.pi * r * x)
      (2 * Real.pi * r) xi := by
    simpa using (hasDerivAt_id xi).const_mul (2 * Real.pi * r)
  have hbase := ((hasDerivAt_const (x := xi) (2 : ℝ)).sub
    (hlin.cos.const_mul 2)).const_mul
      (Real.exp (Real.log n / 2) * Real.cosh (r / 2))
  apply hbase.congr_deriv
  ring

theorem hasDerivAt_ccmActualHeadMatchedCosinePhaseFirstJet_integrand
    (n : ℕ) (r xi : ℝ) :
    HasDerivAt
      (fun x : ℝ =>
        4 * Real.pi * r * Real.exp (Real.log n / 2) * Real.cosh (r / 2) *
          Real.sin (2 * Real.pi * r * x))
      (8 * Real.pi ^ (2 : ℕ) * r ^ (2 : ℕ) * Real.exp (Real.log n / 2) * Real.cosh (r / 2) *
        Real.cos (2 * Real.pi * r * xi)) xi := by
  have hlin : HasDerivAt (fun x : ℝ => 2 * Real.pi * r * x)
      (2 * Real.pi * r) xi := by
    simpa using (hasDerivAt_id xi).const_mul (2 * Real.pi * r)
  have hbase := hlin.sin.const_mul
    (4 * Real.pi * r * Real.exp (Real.log n / 2) * Real.cosh (r / 2))
  apply hbase.congr_deriv
  ring

theorem hasDerivAt_ccmActualHeadMatchedCosinePhaseProfile
    (n : ℕ) (xi : ℝ) :
    HasDerivAt (ccmActualHeadMatchedCosinePhaseProfile n)
      (ccmActualHeadMatchedCosinePhaseFirstJet n xi) xi := by
  let rho := ccmActualHeadMatchedPrimePolarRadius n
  let F : ℝ → ℝ → ℝ := fun x r =>
    Real.exp (Real.log n / 2) * Real.cosh (r / 2) *
      (2 - 2 * Real.cos (2 * Real.pi * r * x))
  let F' : ℝ → ℝ → ℝ := fun x r =>
    4 * Real.pi * r * Real.exp (Real.log n / 2) * Real.cosh (r / 2) *
      Real.sin (2 * Real.pi * r * x)
  let bound : ℝ → ℝ := fun r =>
    |4 * Real.pi * r * Real.exp (Real.log n / 2) * Real.cosh (r / 2)|
  have hFmeas : ∀ᶠ x : ℝ in nhds xi,
      AEStronglyMeasurable (F x) (volume.restrict (uIoc (0 : ℝ) rho)) :=
    Filter.Eventually.of_forall fun x =>
      (by fun_prop : Continuous (F x)).aestronglyMeasurable
  have hFint : IntervalIntegrable (F xi) volume 0 rho :=
    (by fun_prop : Continuous (F xi)).intervalIntegrable _ _
  have hF'meas : AEStronglyMeasurable (F' xi)
      (volume.restrict (uIoc (0 : ℝ) rho)) :=
    (by fun_prop : Continuous (F' xi)).aestronglyMeasurable
  have hbound : ∀ᵐ r : ℝ ∂volume, r ∈ uIoc (0 : ℝ) rho →
      ∀ x ∈ (Set.univ : Set ℝ), ‖F' x r‖ ≤ bound r := by
    filter_upwards with r
    intro hr x hx
    dsimp only [F', bound]
    rw [Real.norm_eq_abs, abs_mul]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _)
        (abs_nonneg
          (4 * Real.pi * r * Real.exp (Real.log n / 2) * Real.cosh (r / 2)))
  have hboundint : IntervalIntegrable bound volume 0 rho :=
    (by fun_prop : Continuous bound).intervalIntegrable _ _
  have hdiff : ∀ᵐ r : ℝ ∂volume, r ∈ uIoc (0 : ℝ) rho →
      ∀ x ∈ (Set.univ : Set ℝ),
        HasDerivAt (fun y => F y r) (F' x r) x := by
    filter_upwards with r
    intro hr x hx
    simpa only [F, F'] using
      hasDerivAt_ccmActualHeadMatchedCosinePhase_integrand n r x
  have hmain := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := bound) (x₀ := xi)
    (show (Set.univ : Set ℝ) ∈ nhds xi from univ_mem)
    hFmeas hFint hF'meas hbound hboundint hdiff).2
  unfold ccmActualHeadMatchedCosinePhaseProfile
    ccmActualHeadMatchedCosinePhaseFirstJet
  simpa only [F, F', rho] using hmain

theorem hasDerivAt_ccmActualHeadMatchedCosinePhaseFirstJet
    (n : ℕ) (xi : ℝ) :
    HasDerivAt (ccmActualHeadMatchedCosinePhaseFirstJet n)
      (ccmActualHeadMatchedCosinePhaseSecondJet n xi) xi := by
  let rho := ccmActualHeadMatchedPrimePolarRadius n
  let F : ℝ → ℝ → ℝ := fun x r =>
    4 * Real.pi * r * Real.exp (Real.log n / 2) * Real.cosh (r / 2) *
      Real.sin (2 * Real.pi * r * x)
  let F' : ℝ → ℝ → ℝ := fun x r =>
    8 * Real.pi ^ (2 : ℕ) * r ^ (2 : ℕ) * Real.exp (Real.log n / 2) * Real.cosh (r / 2) *
      Real.cos (2 * Real.pi * r * x)
  let bound : ℝ → ℝ := fun r =>
    |8 * Real.pi ^ (2 : ℕ) * r ^ (2 : ℕ) * Real.exp (Real.log n / 2) * Real.cosh (r / 2)|
  have hFmeas : ∀ᶠ x : ℝ in nhds xi,
      AEStronglyMeasurable (F x) (volume.restrict (uIoc (0 : ℝ) rho)) :=
    Filter.Eventually.of_forall fun x =>
      (by fun_prop : Continuous (F x)).aestronglyMeasurable
  have hFint : IntervalIntegrable (F xi) volume 0 rho :=
    (by fun_prop : Continuous (F xi)).intervalIntegrable _ _
  have hF'meas : AEStronglyMeasurable (F' xi)
      (volume.restrict (uIoc (0 : ℝ) rho)) :=
    (by fun_prop : Continuous (F' xi)).aestronglyMeasurable
  have hbound : ∀ᵐ r : ℝ ∂volume, r ∈ uIoc (0 : ℝ) rho →
      ∀ x ∈ (Set.univ : Set ℝ), ‖F' x r‖ ≤ bound r := by
    filter_upwards with r
    intro hr x hx
    dsimp only [F', bound]
    rw [Real.norm_eq_abs, abs_mul]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _)
        (abs_nonneg
          (8 * Real.pi ^ (2 : ℕ) * r ^ (2 : ℕ) * Real.exp (Real.log n / 2) * Real.cosh (r / 2)))
  have hboundint : IntervalIntegrable bound volume 0 rho :=
    (by fun_prop : Continuous bound).intervalIntegrable _ _
  have hdiff : ∀ᵐ r : ℝ ∂volume, r ∈ uIoc (0 : ℝ) rho →
      ∀ x ∈ (Set.univ : Set ℝ),
        HasDerivAt (fun y => F y r) (F' x r) x := by
    filter_upwards with r
    intro hr x hx
    simpa only [F, F'] using
      hasDerivAt_ccmActualHeadMatchedCosinePhaseFirstJet_integrand n r x
  have hmain := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := bound) (x₀ := xi)
    (show (Set.univ : Set ℝ) ∈ nhds xi from univ_mem)
    hFmeas hFint hF'meas hbound hboundint hdiff).2
  unfold ccmActualHeadMatchedCosinePhaseFirstJet
    ccmActualHeadMatchedCosinePhaseSecondJet
  simpa only [F, F', rho] using hmain

@[simp] theorem ccmActualHeadMatchedCosinePhaseFirstJet_zero (n : ℕ) :
    ccmActualHeadMatchedCosinePhaseFirstJet n 0 = 0 := by
  simp [ccmActualHeadMatchedCosinePhaseFirstJet]

theorem ccmActualHeadMatchedCosinePhaseSecondJet_zero (n : ℕ) :
    ccmActualHeadMatchedCosinePhaseSecondJet n 0 =
      ccmActualHeadMatchedCosinePhaseQuadraticMoment n := by
  simp [ccmActualHeadMatchedCosinePhaseSecondJet,
    ccmActualHeadMatchedCosinePhaseQuadraticMoment]

theorem ccmActualHeadMatchedCosinePhaseQuadraticMoment_pos_of_weight_pos
    {n : ℕ} (hn : 0 < criticalMellinAtomWeight n) :
    0 < ccmActualHeadMatchedCosinePhaseQuadraticMoment n := by
  let rho := ccmActualHeadMatchedPrimePolarRadius n
  have hrho : 0 < rho := ccmActualHeadMatchedPrimePolarRadius_pos_of_weight_pos hn
  unfold ccmActualHeadMatchedCosinePhaseQuadraticMoment
  apply intervalIntegral.integral_pos (a := (0 : ℝ)) (b := rho) hrho
  · fun_prop
  · intro r hr
    positivity
  · refine ⟨rho, Set.mem_Icc.2 ⟨hrho.le, le_rfl⟩, ?_⟩
    positivity

/-- First spectral jet of the source coordinate read by the chiral nodal line. -/
def ccmActualHeadMatchedOrientedPhaseSymbolRealFirstJet (n : ℕ) (xi : ℝ) : ℝ :=
  let L := 2 * Real.pi * Real.log n
  (-L * Real.sin (L * xi)) * ccmActualHeadMatchedCosinePhaseProfile n xi +
    Real.cos (L * xi) * ccmActualHeadMatchedCosinePhaseFirstJet n xi +
    (L * Real.cos (L * xi)) * ccmActualHeadMatchedSinePhaseProfile n xi +
    Real.sin (L * xi) * ccmActualHeadMatchedSinePhaseFirstJet n xi

theorem hasDerivAt_ccmActualHeadMatchedOrientedPhaseSymbol_re
    (n : ℕ) (xi : ℝ) :
    HasDerivAt (fun x : ℝ => (ccmActualHeadMatchedOrientedPhaseSymbol n x).re)
      (ccmActualHeadMatchedOrientedPhaseSymbolRealFirstJet n xi) xi := by
  let L := 2 * Real.pi * Real.log n
  have hlin : HasDerivAt (fun x : ℝ => L * x) L xi := by
    simpa using (hasDerivAt_id xi).const_mul L
  have hC := hasDerivAt_ccmActualHeadMatchedCosinePhaseProfile n xi
  have hP := hasDerivAt_ccmActualHeadMatchedSinePhaseProfile n xi
  have h := (hlin.cos.mul hC).add (hlin.sin.mul hP)
  rw [show (fun x : ℝ => (ccmActualHeadMatchedOrientedPhaseSymbol n x).re) =
      fun x : ℝ => Real.cos (L * x) * ccmActualHeadMatchedCosinePhaseProfile n x +
        Real.sin (L * x) * ccmActualHeadMatchedSinePhaseProfile n x by
    funext x
    simpa only [L] using ccmActualHeadMatchedOrientedPhaseSymbol_re n x]
  have hpointwise :
      ((fun x : ℝ => Real.cos (L * x)) * ccmActualHeadMatchedCosinePhaseProfile n +
        (fun x : ℝ => Real.sin (L * x)) * ccmActualHeadMatchedSinePhaseProfile n) =
      fun x : ℝ => Real.cos (L * x) * ccmActualHeadMatchedCosinePhaseProfile n x +
        Real.sin (L * x) * ccmActualHeadMatchedSinePhaseProfile n x := by
    funext x
    rfl
  rw [hpointwise] at h
  apply h.congr_deriv
  dsimp only [ccmActualHeadMatchedOrientedPhaseSymbolRealFirstJet, L]
  ring

@[simp] theorem ccmActualHeadMatchedOrientedPhaseSymbolRealFirstJet_zero (n : ℕ) :
    ccmActualHeadMatchedOrientedPhaseSymbolRealFirstJet n 0 = 0 := by
  simp [ccmActualHeadMatchedOrientedPhaseSymbolRealFirstJet,
    ccmActualHeadMatchedCosinePhaseProfile_zero,
    ccmActualHeadMatchedSinePhaseProfile_zero]

/-- Exact positive source coefficient governing the center-frequency determinant curvature. -/
def ccmActualHeadMatchedNodalSourceFrequencyCurvature (n : ℕ) : ℝ :=
  ccmActualHeadMatchedCosinePhaseQuadraticMoment n +
    4 * Real.pi * Real.log n * ccmActualHeadMatchedOrientedFirstMoment n

theorem hasDerivAt_ccmActualHeadMatchedOrientedPhaseSymbolRealFirstJet_zero
    (n : ℕ) :
    HasDerivAt (ccmActualHeadMatchedOrientedPhaseSymbolRealFirstJet n)
      (ccmActualHeadMatchedNodalSourceFrequencyCurvature n) 0 := by
  let L := 2 * Real.pi * Real.log n
  have hlin : HasDerivAt (fun x : ℝ => L * x) L 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul L
  have hC := hasDerivAt_ccmActualHeadMatchedCosinePhaseProfile n 0
  have hC1 := hasDerivAt_ccmActualHeadMatchedCosinePhaseFirstJet n 0
  have hP := hasDerivAt_ccmActualHeadMatchedSinePhaseProfile n 0
  have hP1 := hasDerivAt_ccmActualHeadMatchedSinePhaseFirstJet n 0
  have h := ((((hlin.sin.const_mul (-L)).mul hC).add
      (hlin.cos.mul hC1)).add
      ((hlin.cos.const_mul L).mul hP)).add
      (hlin.sin.mul hP1)
  apply h.congr_deriv
  simp only [ccmActualHeadMatchedNodalSourceFrequencyCurvature, L,
    mul_zero, Real.sin_zero, Real.cos_zero, neg_mul, zero_mul,
    ccmActualHeadMatchedCosinePhaseProfile_zero,
    ccmActualHeadMatchedCosinePhaseFirstJet_zero,
    ccmActualHeadMatchedCosinePhaseSecondJet_zero,
    ccmActualHeadMatchedSinePhaseProfile_zero,
    ccmActualHeadMatchedSinePhaseFirstJet_zero,
    ccmActualHeadMatchedSinePhaseSecondJet_zero,
    one_mul, add_zero, zero_add]
  ring

theorem deriv_deriv_ccmActualHeadMatchedOrientedPhaseSymbol_re_zero
    (n : ℕ) :
    deriv (deriv (fun x : ℝ =>
      (ccmActualHeadMatchedOrientedPhaseSymbol n x).re)) 0 =
        ccmActualHeadMatchedNodalSourceFrequencyCurvature n := by
  have hfirst :
      deriv (fun x : ℝ => (ccmActualHeadMatchedOrientedPhaseSymbol n x).re) =
        ccmActualHeadMatchedOrientedPhaseSymbolRealFirstJet n := by
    funext xi
    exact (hasDerivAt_ccmActualHeadMatchedOrientedPhaseSymbol_re n xi).deriv
  rw [hfirst]
  exact (hasDerivAt_ccmActualHeadMatchedOrientedPhaseSymbolRealFirstJet_zero n).deriv

theorem ccmActualHeadMatchedNodalSourceFrequencyCurvature_primePower_pos
    (p : Nat.Primes) (e : ℕ) :
    0 < ccmActualHeadMatchedNodalSourceFrequencyCurvature
      (xiGammaEulerValuationNat (p, e)) := by
  let n := xiGammaEulerValuationNat (p, e)
  have hn : 1 < n := one_lt_xiGammaEulerValuationNat p e
  have hw : 0 < criticalMellinAtomWeight n := by
    rw [criticalMellinAtomWeight_primePower_eq_sq_suzukiCriticalEntryWallBareAmplitude]
    exact sq_pos_of_pos (suzukiCriticalEntryWallBareAmplitude_pos p e)
  have hQ := ccmActualHeadMatchedCosinePhaseQuadraticMoment_pos_of_weight_pos hw
  have hM := ccmActualHeadMatchedOrientedFirstMoment_primePower_pos p e
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  unfold ccmActualHeadMatchedNodalSourceFrequencyCurvature
  positivity

theorem deriv_deriv_det_ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFamily_one_zero
    (n : ℕ) :
    deriv (deriv (fun xi : ℝ =>
      (ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFamily xi n 1).det.re)) 0 =
      -2 * ccmActualHeadMatchedPhaseProjectiveGauge n ^ (2 : ℕ) *
        ccmActualHeadMatchedNodalSourceFrequencyCurvature n := by
  let A := -2 * ccmActualHeadMatchedPhaseProjectiveGauge n ^ (2 : ℕ)
  have hfun :
      (fun xi : ℝ =>
        (ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFamily xi n 1).det.re) =
      fun xi : ℝ => A * (ccmActualHeadMatchedOrientedPhaseSymbol n xi).re := by
    funext xi
    rw [det_ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFamily]
    norm_cast
    dsimp only [A]
    ring
  have hfirst :
      deriv (fun xi : ℝ => A * (ccmActualHeadMatchedOrientedPhaseSymbol n xi).re) =
      fun xi : ℝ => A * ccmActualHeadMatchedOrientedPhaseSymbolRealFirstJet n xi := by
    funext xi
    exact ((hasDerivAt_ccmActualHeadMatchedOrientedPhaseSymbol_re n xi).const_mul A).deriv
  rw [hfun, hfirst]
  have hsecond :=
    (hasDerivAt_ccmActualHeadMatchedOrientedPhaseSymbolRealFirstJet_zero n).const_mul A
  simpa only [A] using hsecond.deriv

theorem hasDerivAt_det_ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFamily_one
    (n : ℕ) (xi : ℝ) :
    HasDerivAt
      (fun x : ℝ =>
        (ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFamily x n 1).det.re)
      (-2 * ccmActualHeadMatchedPhaseProjectiveGauge n ^ (2 : ℕ) *
        ccmActualHeadMatchedOrientedPhaseSymbolRealFirstJet n xi) xi := by
  let A := -2 * ccmActualHeadMatchedPhaseProjectiveGauge n ^ (2 : ℕ)
  have hfun :
      (fun x : ℝ =>
        (ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFamily x n 1).det.re) =
      fun x : ℝ => A * (ccmActualHeadMatchedOrientedPhaseSymbol n x).re := by
    funext x
    rw [det_ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFamily]
    norm_cast
    dsimp only [A]
    ring
  rw [hfun]
  simpa only [A] using
    (hasDerivAt_ccmActualHeadMatchedOrientedPhaseSymbol_re n xi).const_mul A

@[simp]
theorem det_ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFamily_one_zero
    (n : ℕ) :
    (ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFamily 0 n 1).det.re = 0 := by
  rw [det_ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFamily]
  simp

theorem deriv_det_ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFamily_one_zero
    (n : ℕ) :
    deriv (fun xi : ℝ =>
      (ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFamily xi n 1).det.re) 0 = 0 := by
  exact
    (hasDerivAt_det_ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFamily_one n 0).deriv.trans
      (by simp)

theorem ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingCurvature_primePower_neg
    (p : Nat.Primes) (e : ℕ) :
    -2 * ccmActualHeadMatchedPhaseProjectiveGauge
        (xiGammaEulerValuationNat (p, e)) ^ (2 : ℕ) *
      ccmActualHeadMatchedNodalSourceFrequencyCurvature
        (xiGammaEulerValuationNat (p, e)) < 0 := by
  have hw : 0 < criticalMellinAtomWeight (xiGammaEulerValuationNat (p, e)) := by
    rw [criticalMellinAtomWeight_primePower_eq_sq_suzukiCriticalEntryWallBareAmplitude]
    exact sq_pos_of_pos (suzukiCriticalEntryWallBareAmplitude_pos p e)
  have hgauge :=
    ccmActualHeadMatchedPhaseProjectiveGauge_ne_zero_of_criticalMellinAtomWeight_ne_zero
      (xiGammaEulerValuationNat (p, e)) hw.ne'
  have hsq :
      0 < ccmActualHeadMatchedPhaseProjectiveGauge
          (xiGammaEulerValuationNat (p, e)) ^ (2 : ℕ) :=
    sq_pos_of_ne_zero hgauge
  have hcurv := ccmActualHeadMatchedNodalSourceFrequencyCurvature_primePower_pos p e
  exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) hsq) hcurv

theorem deriv_deriv_det_ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFamily_one_zero_primePower_neg
    (p : Nat.Primes) (e : ℕ) :
    deriv (deriv (fun xi : ℝ =>
      (ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFamily xi
        (xiGammaEulerValuationNat (p, e)) 1).det.re)) 0 < 0 := by
  rw [deriv_deriv_det_ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFamily_one_zero]
  exact
    ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingCurvature_primePower_neg p e

theorem ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFamily_one_primePower_isLocalMax_zero
    (p : Nat.Primes) (e : ℕ) :
    IsLocalMax
      (fun xi : ℝ =>
        (ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFamily xi
          (xiGammaEulerValuationNat (p, e)) 1).det.re) 0 := by
  let n := xiGammaEulerValuationNat (p, e)
  let A := -2 * ccmActualHeadMatchedPhaseProjectiveGauge n ^ (2 : ℕ)
  have hfun :
      (fun xi : ℝ =>
        (ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFamily xi n 1).det.re) =
      fun xi : ℝ => A * (ccmActualHeadMatchedOrientedPhaseSymbol n xi).re := by
    funext xi
    rw [det_ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFamily]
    norm_cast
    dsimp only [A]
    ring
  change IsLocalMax
    (fun xi : ℝ =>
      (ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFamily xi n 1).det.re) 0
  rw [hfun]
  apply isLocalMax_of_deriv_deriv_neg
  · have hneg :=
      deriv_deriv_det_ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFamily_one_zero_primePower_neg
        p e
    change deriv (deriv (fun xi : ℝ =>
      (ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFamily xi n 1).det.re)) 0 < 0
      at hneg
    rw [hfun] at hneg
    exact hneg
  ·
    exact (((hasDerivAt_ccmActualHeadMatchedOrientedPhaseSymbol_re n 0).const_mul A).deriv.trans
      (by simp))
  · exact
      ((hasDerivAt_ccmActualHeadMatchedOrientedPhaseSymbol_re n 0).const_mul A).continuousAt

theorem eventually_ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFamily_one_primePower_det_nonpos
    (p : Nat.Primes) (e : ℕ) :
    ∀ᶠ xi : ℝ in nhds 0,
      (ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFamily xi
        (xiGammaEulerValuationNat (p, e)) 1).det.re ≤ 0 := by
  simpa only [IsLocalMax, IsMaxFilter,
    det_ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFamily_one_zero] using
      ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFamily_one_primePower_isLocalMax_zero
        p e

/-- Finite direct-sum determinant response of actual prime-power nodal blocks. -/
def ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFinitePrimePowerResponse
    (S : Finset (Nat.Primes × ℕ)) (xi : ℝ) : ℝ :=
  ∑ pe ∈ S,
    (ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFamily xi
      (xiGammaEulerValuationNat pe) 1).det.re

def ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFinitePrimePowerFirstJet
    (S : Finset (Nat.Primes × ℕ)) (xi : ℝ) : ℝ :=
  ∑ pe ∈ S,
    -2 * ccmActualHeadMatchedPhaseProjectiveGauge (xiGammaEulerValuationNat pe) ^ (2 : ℕ) *
      ccmActualHeadMatchedOrientedPhaseSymbolRealFirstJet
        (xiGammaEulerValuationNat pe) xi

def ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFinitePrimePowerCurvature
    (S : Finset (Nat.Primes × ℕ)) : ℝ :=
  ∑ pe ∈ S,
    -2 * ccmActualHeadMatchedPhaseProjectiveGauge (xiGammaEulerValuationNat pe) ^ (2 : ℕ) *
      ccmActualHeadMatchedNodalSourceFrequencyCurvature (xiGammaEulerValuationNat pe)

theorem hasDerivAt_ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFinitePrimePowerResponse
    (S : Finset (Nat.Primes × ℕ)) (xi : ℝ) :
    HasDerivAt
      (ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFinitePrimePowerResponse S)
      (ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFinitePrimePowerFirstJet S xi)
      xi := by
  unfold ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFinitePrimePowerResponse
    ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFinitePrimePowerFirstJet
  apply HasDerivAt.fun_sum
  intro pe hpe
  exact
    hasDerivAt_det_ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFamily_one
      (xiGammaEulerValuationNat pe) xi

theorem hasDerivAt_ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFinitePrimePowerFirstJet_zero
    (S : Finset (Nat.Primes × ℕ)) :
    HasDerivAt
      (ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFinitePrimePowerFirstJet S)
      (ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFinitePrimePowerCurvature S)
      0 := by
  unfold ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFinitePrimePowerFirstJet
    ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFinitePrimePowerCurvature
  apply HasDerivAt.fun_sum
  intro pe hpe
  exact
    (hasDerivAt_ccmActualHeadMatchedOrientedPhaseSymbolRealFirstJet_zero
      (xiGammaEulerValuationNat pe)).const_mul
        (-2 * ccmActualHeadMatchedPhaseProjectiveGauge
          (xiGammaEulerValuationNat pe) ^ (2 : ℕ))

@[simp]
theorem ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFinitePrimePowerFirstJet_zero
    (S : Finset (Nat.Primes × ℕ)) :
    ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFinitePrimePowerFirstJet S 0 = 0 := by
  simp [ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFinitePrimePowerFirstJet]

theorem deriv_deriv_ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFinitePrimePowerResponse_zero
    (S : Finset (Nat.Primes × ℕ)) :
    deriv (deriv
      (ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFinitePrimePowerResponse S)) 0 =
      ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFinitePrimePowerCurvature S := by
  have hfirst :
      deriv
          (ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFinitePrimePowerResponse S) =
        ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFinitePrimePowerFirstJet S := by
    funext xi
    exact
      (hasDerivAt_ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFinitePrimePowerResponse
        S xi).deriv
  rw [hfirst]
  exact
    (hasDerivAt_ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFinitePrimePowerFirstJet_zero
      S).deriv

theorem ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFinitePrimePowerCurvature_neg
    {S : Finset (Nat.Primes × ℕ)} (hS : S.Nonempty) :
    ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFinitePrimePowerCurvature S < 0 := by
  obtain ⟨pe, hpe⟩ := hS
  unfold ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFinitePrimePowerCurvature
  have hlt :
      (∑ pe ∈ S,
        -2 * ccmActualHeadMatchedPhaseProjectiveGauge (xiGammaEulerValuationNat pe) ^ (2 : ℕ) *
          ccmActualHeadMatchedNodalSourceFrequencyCurvature (xiGammaEulerValuationNat pe)) <
        ∑ _pe ∈ S, (0 : ℝ) := by
    apply Finset.sum_lt_sum
    · intro x hx
      exact
        (ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingCurvature_primePower_neg
          x.1 x.2).le
    · exact ⟨pe, hpe,
        ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingCurvature_primePower_neg
          pe.1 pe.2⟩
  simpa using hlt

theorem ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFinitePrimePowerResponse_isLocalMax_zero
    {S : Finset (Nat.Primes × ℕ)} (hS : S.Nonempty) :
    IsLocalMax
      (ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFinitePrimePowerResponse S) 0 := by
  apply isLocalMax_of_deriv_deriv_neg
  · rw [deriv_deriv_ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFinitePrimePowerResponse_zero]
    exact
      ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFinitePrimePowerCurvature_neg hS
  · exact
      (hasDerivAt_ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFinitePrimePowerResponse
        S 0).deriv.trans (by simp)
  · exact
      (hasDerivAt_ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFinitePrimePowerResponse
        S 0).continuousAt

end RHTower
