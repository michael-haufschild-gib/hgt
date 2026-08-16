import GaloisForLFunctions.RHTower.SuzukiWallFieldLightConeKernelCompletion
import GaloisForLFunctions.RHTower.SuzukiCriticalEntryWallQuarterShiftGreenLaw
import GaloisForLFunctions.RHTower.EulerFisherCurvature

/-!
# Suzuki aperture-dressed wall light completion

The raw critical wall field has the correct reflected phase but divergent all-prime diagonal.
The actual cubically normalized dyadic aperture innovation acts before the reflected light split.
This file proves that the resulting source field is square summable over all primes and valuation
depths.  Its positive and negative reflected parts therefore define genuine `ell^2` vectors and
completed positive-semidefinite Gram kernels, with the exact Ward identity

`reflected current + negative light = positive light`.

This is a pre-split completion: each dressed light coordinate is exactly the corresponding raw
wall-light coordinate times the real aperture innovation.  It is not an RH proof.  The completed
diagonal is exactly height-independent, so this carrier alone cannot create the height-dependent
rectangular Xi curvature.  Restricted-Weil resolvent, marked Robin, Gamma, and holonomy assembly
remain necessary.

No RH premise, numerical computation, infinite subtraction, or post-split counterterm is used.
-/

open Complex
open scoped BigOperators ComplexConjugate ComplexOrder
open GaloisForLFunctions GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-! ## All-prime square summability -/

private theorem criticalBoundaryDensity_le_log
    (t : ℝ) (p : Nat.Primes) (e : ℕ) :
    Complex.normSq (xiGammaEulerHeightBoundaryFeature (-1 / 2) t (p, e)) ≤
      Real.log (p : ℝ) := by
  rw [normSq_xiGammaEulerHeightBoundaryFeature]
  simp only [show -(-1 / 2 : ℝ) = 1 / 2 by norm_num]
  let n : ℝ := xiGammaEulerValuationNat (p, e)
  have hnNat : 0 < xiGammaEulerValuationNat (p, e) := by
    exact pow_pos p.property.pos _
  have hn : 0 < n := by
    change 0 < (xiGammaEulerValuationNat (p, e) : ℝ)
    exact_mod_cast hnNat
  have hn1 : 1 ≤ n := by
    change (1 : ℝ) ≤ (xiGammaEulerValuationNat (p, e) : ℝ)
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hnNat))
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hexp : Real.exp ((1 / 2 : ℝ) * Real.log n) ≤ n := by
    calc
      Real.exp ((1 / 2 : ℝ) * Real.log n) ≤ Real.exp (Real.log n) :=
        Real.exp_le_exp.mpr (by nlinarith)
      _ = n := Real.exp_log hn
  have hlogp : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast p.property.one_le)
  change Real.log (p : ℝ) / n * Real.exp ((1 / 2 : ℝ) * Real.log n) ≤ _
  rw [div_mul_eq_mul_div, div_le_iff₀ hn]
  exact mul_le_mul_of_nonneg_left hexp hlogp

private theorem summable_cubicInnovation_sq_depth
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (p : Nat.Primes) :
    Summable (fun e : ℕ =>
      xiMobiusCubicNormalizedInnovationFeature h a (p, e) ^ 2) := by
  let q := xiTransversePrimeApertureDiskNode 1 p
  let r := xiMobiusContinuousApertureDiskNode ((h / 2) * a) p
  have hra : 0 < (h / 2) * a := mul_pos (half_pos hh) ha
  have hr0 : 0 ≤ r := (xiMobiusContinuousApertureDiskNode_pos _ p).le
  have hr1 : r < 1 := xiMobiusContinuousApertureDiskNode_lt_one hra p
  have hrpow0 : 0 ≤ r ^ 4 := pow_nonneg hr0 _
  have hrpow1 : r ^ 4 < 1 := pow_lt_one₀ hr0 hr1 (by norm_num)
  refine ((summable_geometric_of_lt_one hrpow0 hrpow1).mul_left
    (((h * Real.sqrt h)⁻¹ * (q / (1 + q)) * (1 - r) ^ 2) ^ 2)).congr ?_
  intro e
  simp only [xiMobiusCubicNormalizedInnovationFeature,
    xiMobiusContinuousApertureDyadicInnovationFeature,
    xiMobiusPrimeContinuousApertureDyadicInnovationFeature, q, r]
  have hrpow : (r ^ 4) ^ e = ((r ^ 2) ^ e) ^ 2 := by
    calc
      (r ^ 4) ^ e = r ^ (4 * e) := (pow_mul r 4 e).symm
      _ = r ^ (2 * (e * 2)) := by congr 1; omega
      _ = (r ^ 2) ^ (e * 2) := pow_mul r 2 (e * 2)
      _ = ((r ^ 2) ^ e) ^ 2 := pow_mul (r ^ 2) e 2
  rw [hrpow]
  ring

private theorem summable_normSq_boundaryAtom_depth
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (t : ℝ) (p : Nat.Primes) :
    Summable (fun e : ℕ =>
      Complex.normSq (suzukiCriticalApertureBoundaryAtom h a t p e)) := by
  have hcubic := summable_cubicInnovation_sq_depth hh ha p
  refine Summable.of_nonneg_of_le
    (fun e => Complex.normSq_nonneg _)
    (fun e => ?_)
    (hcubic.mul_left (Real.log (p : ℝ)))
  rw [suzukiCriticalApertureBoundaryAtom, Complex.normSq_mul]
  have hstar : Complex.normSq
      (star (xiGammaEulerHeightBoundaryFeature (-1 / 2) t (p, e))) =
        Complex.normSq (xiGammaEulerHeightBoundaryFeature (-1 / 2) t (p, e)) := by
    rw [Complex.normSq_eq_norm_sq, norm_star, Complex.normSq_eq_norm_sq]
  rw [hstar, Complex.normSq_ofReal, ← pow_two]
  exact mul_le_mul_of_nonneg_right (criticalBoundaryDensity_le_log t p e) (sq_nonneg _)

private theorem tsum_cubicInnovation_sq_depth_eq
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (p : Nat.Primes) :
    (∑' e : ℕ, xiMobiusCubicNormalizedInnovationFeature h a (p, e) ^ 2) =
      ((h * Real.sqrt h)⁻¹) ^ 2 *
        xiMobiusPrimeContinuousApertureDyadicInnovation h a a p := by
  rw [← tsum_xiMobiusPrimeContinuousApertureDyadicInnovationFeature_mul_eq
    hh ha ha p, ← tsum_mul_left]
  apply tsum_congr
  intro e
  simp only [xiMobiusCubicNormalizedInnovationFeature,
    xiMobiusContinuousApertureDyadicInnovationFeature]
  ring

private theorem dyadicInnovation_self_le_two_invSq
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (p : Nat.Primes) :
    xiMobiusPrimeContinuousApertureDyadicInnovation h a a p ≤
      2 * ((p : ℝ) ^ 2)⁻¹ := by
  have hfull : 0 ≤ xiMobiusPrimeContinuousApertureSzegoMetric (h * a) (h * a) p :=
    xiMobiusPrimeContinuousApertureSzegoMetric_self_nonneg (mul_pos hh ha) p
  have hhalf := xiMobiusPrimeContinuousApertureSzegoMetric_self_le_invSq
    (mul_pos (half_pos hh) ha) p
  rw [xiMobiusPrimeContinuousApertureDyadicInnovation]
  rw [xiTransversePrimeApertureDiskNode_one_eq_inv, inv_pow] at hhalf
  linarith

private theorem tsum_normSq_boundaryAtom_depth_le
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (t : ℝ) (p : Nat.Primes) :
    (∑' e : ℕ,
      Complex.normSq (suzukiCriticalApertureBoundaryAtom h a t p e)) ≤
      2 * ((h * Real.sqrt h)⁻¹) ^ 2 *
        Real.log (p : ℝ) * ((p : ℝ) ^ 2)⁻¹ := by
  have hcubic := summable_cubicInnovation_sq_depth hh ha p
  have hatom := summable_normSq_boundaryAtom_depth hh ha t p
  have hpoint : ∀ e : ℕ,
      Complex.normSq (suzukiCriticalApertureBoundaryAtom h a t p e) ≤
        Real.log (p : ℝ) *
          xiMobiusCubicNormalizedInnovationFeature h a (p, e) ^ 2 := by
    intro e
    rw [suzukiCriticalApertureBoundaryAtom, Complex.normSq_mul]
    have hstar : Complex.normSq
        (star (xiGammaEulerHeightBoundaryFeature (-1 / 2) t (p, e))) =
          Complex.normSq (xiGammaEulerHeightBoundaryFeature (-1 / 2) t (p, e)) := by
      rw [Complex.normSq_eq_norm_sq, norm_star, Complex.normSq_eq_norm_sq]
    rw [hstar, Complex.normSq_ofReal, ← pow_two]
    exact mul_le_mul_of_nonneg_right (criticalBoundaryDensity_le_log t p e)
      (sq_nonneg _)
  calc
    (∑' e : ℕ,
        Complex.normSq (suzukiCriticalApertureBoundaryAtom h a t p e)) ≤
        ∑' e : ℕ, Real.log (p : ℝ) *
          xiMobiusCubicNormalizedInnovationFeature h a (p, e) ^ 2 :=
      hatom.tsum_le_tsum hpoint (hcubic.mul_left _)
    _ = Real.log (p : ℝ) * ((h * Real.sqrt h)⁻¹) ^ 2 *
        xiMobiusPrimeContinuousApertureDyadicInnovation h a a p := by
      rw [tsum_mul_left, tsum_cubicInnovation_sq_depth_eq hh ha]
      ring
    _ ≤ Real.log (p : ℝ) * ((h * Real.sqrt h)⁻¹) ^ 2 *
        (2 * ((p : ℝ) ^ 2)⁻¹) := by
      exact mul_le_mul_of_nonneg_left
        (dyadicInnovation_self_le_two_invSq hh ha p)
        (mul_nonneg (Real.log_nonneg (by exact_mod_cast p.property.one_le)) (sq_nonneg _))
    _ = 2 * ((h * Real.sqrt h)⁻¹) ^ 2 *
        Real.log (p : ℝ) * ((p : ℝ) ^ 2)⁻¹ := by ring

private theorem summable_prime_log_mul_invSq :
    Summable (fun p : Nat.Primes => Real.log (p : ℝ) * ((p : ℝ) ^ 2)⁻¹) := by
  have hnat := summable_abs_log_natCast_pow_mul_rpow_neg 1 2 (by norm_num)
  have hprime : Summable (fun p : Nat.Primes =>
      |Real.log (p : ℕ)| ^ 1 * ((p : ℕ) : ℝ) ^ (-2 : ℝ)) :=
    hnat.comp_injective Subtype.val_injective
  refine hprime.congr fun p => ?_
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.property.pos
  have hlog : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.property.one_lt)
  rw [abs_of_pos hlog, pow_one, Real.rpow_neg hp.le]
  congr 2
  exact Real.rpow_natCast (p : ℝ) 2

/-- **All-prime pre-split completion.**  The critical Gamma wall field becomes square summable
after multiplication by the actual cubically normalized aperture innovation. -/
theorem summable_normSq_suzukiCriticalApertureBoundaryAtom_allPrime
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (t : ℝ) :
    Summable (fun pe : Nat.Primes × ℕ =>
      Complex.normSq (suzukiCriticalApertureBoundaryAtom h a t pe.1 pe.2)) := by
  rw [summable_prod_of_nonneg (fun _ => Complex.normSq_nonneg _)]
  constructor
  · exact fun p => summable_normSq_boundaryAtom_depth hh ha t p
  · refine Summable.of_nonneg_of_le
      (fun p => tsum_nonneg fun _ => Complex.normSq_nonneg _)
      (fun p => tsum_normSq_boundaryAtom_depth_le hh ha t p)
      ((summable_prime_log_mul_invSq.mul_left
        (2 * ((h * Real.sqrt h)⁻¹) ^ 2)).congr ?_)
    intro p
    ring

/-- The complete dressed wall mass has one explicit ceiling independent of observer aperture and
spectral height.  This is the uniform form needed when a fixed source scale is carried along a
cofinal aperture family. -/
theorem tsum_normSq_suzukiCriticalApertureBoundaryAtom_allPrime_le
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (t : ℝ) :
    (∑' pe : Nat.Primes × ℕ,
      Complex.normSq (suzukiCriticalApertureBoundaryAtom h a t pe.1 pe.2)) ≤
      2 * ((h * Real.sqrt h)⁻¹) ^ 2 *
        (∑' p : Nat.Primes,
          Real.log (p : ℝ) * ((p : ℝ) ^ 2)⁻¹) := by
  have hall :=
    summable_normSq_suzukiCriticalApertureBoundaryAtom_allPrime hh ha t
  have hnonneg : 0 ≤ fun pe : Nat.Primes × ℕ =>
      Complex.normSq (suzukiCriticalApertureBoundaryAtom h a t pe.1 pe.2) :=
    fun _ => Complex.normSq_nonneg _
  have hsplit := (summable_prod_of_nonneg hnonneg).mp hall
  rw [hall.tsum_prod]
  calc
    (∑' p : Nat.Primes, ∑' e : ℕ,
        Complex.normSq (suzukiCriticalApertureBoundaryAtom h a t p e)) ≤
        ∑' p : Nat.Primes,
          2 * ((h * Real.sqrt h)⁻¹) ^ 2 *
            Real.log (p : ℝ) * ((p : ℝ) ^ 2)⁻¹ := by
      exact hsplit.2.tsum_le_tsum
        (fun p => tsum_normSq_boundaryAtom_depth_le hh ha t p)
        ((summable_prime_log_mul_invSq.mul_left
          (2 * ((h * Real.sqrt h)⁻¹) ^ 2)).congr (fun p => by ring))
    _ = 2 * ((h * Real.sqrt h)⁻¹) ^ 2 *
        (∑' p : Nat.Primes,
          Real.log (p : ℝ) * ((p : ℝ) ^ 2)⁻¹) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro p
      ring

/-! ## Exact source dressing and reflection -/

/-- Observer dressing multiplies the wall field before any light projection. -/
theorem suzukiCriticalApertureBoundaryAtom_eq_wallField_mul_innovation
    (h a t : ℝ) (p : Nat.Primes) (e : ℕ) :
    suzukiCriticalApertureBoundaryAtom h a t p e =
      suzukiCriticalWallField t p e *
        (xiMobiusCubicNormalizedInnovationFeature h a (p, e) : ℂ) := by
  rfl

/-- Functional-equation reflection survives pre-split innovation dressing. -/
theorem suzukiCriticalApertureBoundaryAtom_neg_eq_star
    (h a t : ℝ) (p : Nat.Primes) (e : ℕ) :
    suzukiCriticalApertureBoundaryAtom h a (-t) p e =
      star (suzukiCriticalApertureBoundaryAtom h a t p e) := by
  rw [suzukiCriticalApertureBoundaryAtom_eq_wallField_mul_innovation,
    suzukiCriticalApertureBoundaryAtom_eq_wallField_mul_innovation,
    suzukiCriticalWallField_neg_eq_star, star_mul]
  have hreal : star
      (xiMobiusCubicNormalizedInnovationFeature h a (p, e) : ℂ) =
        (xiMobiusCubicNormalizedInnovationFeature h a (p, e) : ℂ) := by
    exact Complex.conj_ofReal _
  rw [hreal]
  ring

/-- Innovation changes summability but not the wall energy's height-flat diagonal. -/
theorem normSq_suzukiCriticalApertureBoundaryAtom_height_independent
    (h a t u : ℝ) (p : Nat.Primes) (e : ℕ) :
    Complex.normSq (suzukiCriticalApertureBoundaryAtom h a t p e) =
      Complex.normSq (suzukiCriticalApertureBoundaryAtom h a u p e) := by
  rw [suzukiCriticalApertureBoundaryAtom, suzukiCriticalApertureBoundaryAtom,
    Complex.normSq_mul, Complex.normSq_mul]
  have hstar (v : ℝ) : Complex.normSq
      (star (xiGammaEulerHeightBoundaryFeature (-1 / 2) v (p, e))) =
        Complex.normSq (xiGammaEulerHeightBoundaryFeature (-1 / 2) v (p, e)) := by
    rw [Complex.normSq_eq_norm_sq, norm_star, Complex.normSq_eq_norm_sq]
  rw [hstar, hstar, normSq_xiGammaEulerHeightBoundaryFeature,
    normSq_xiGammaEulerHeightBoundaryFeature]

/-! ## Completed light vectors and kernels -/

/-- All-prime aperture-dressed critical wall field. -/
def suzukiCriticalApertureBoundaryFieldLp
    (h a t : ℝ) (hh : 0 < h) (ha : 0 < a) :
    lp (fun _ : Nat.Primes × ℕ => ℂ) 2 :=
  ⟨fun pe => suzukiCriticalApertureBoundaryAtom h a t pe.1 pe.2,
    HilbertSchmidt.memℓp_of_sq (by
      simpa only [Complex.sq_norm] using
        summable_normSq_suzukiCriticalApertureBoundaryAtom_allPrime hh ha t)⟩

@[simp] theorem suzukiCriticalApertureBoundaryFieldLp_apply
    (h a t : ℝ) (hh : 0 < h) (ha : 0 < a) (pe : Nat.Primes × ℕ) :
    suzukiCriticalApertureBoundaryFieldLp h a t hh ha pe =
      suzukiCriticalApertureBoundaryAtom h a t pe.1 pe.2 := rfl

/-- Positive reflected light vector after pre-split innovation dressing. -/
def suzukiCriticalAperturePositiveLightLp
    (h a t : ℝ) (hh : 0 < h) (ha : 0 < a) :
    lp (fun _ : Nat.Primes × ℕ => ℂ) 2 :=
  ((2 : ℂ)⁻¹) •
    (suzukiCriticalApertureBoundaryFieldLp h a t hh ha +
      I • suzukiCriticalApertureBoundaryFieldLp h a (-t) hh ha)

/-- Negative reflected light vector after pre-split innovation dressing. -/
def suzukiCriticalApertureNegativeLightLp
    (h a t : ℝ) (hh : 0 < h) (ha : 0 < a) :
    lp (fun _ : Nat.Primes × ℕ => ℂ) 2 :=
  ((2 : ℂ)⁻¹) •
    (suzukiCriticalApertureBoundaryFieldLp h a t hh ha -
      I • suzukiCriticalApertureBoundaryFieldLp h a (-t) hh ha)

@[simp] theorem suzukiCriticalAperturePositiveLightLp_apply
    (h a t : ℝ) (hh : 0 < h) (ha : 0 < a) (pe : Nat.Primes × ℕ) :
    suzukiCriticalAperturePositiveLightLp h a t hh ha pe =
      (suzukiCriticalApertureBoundaryAtom h a t pe.1 pe.2 +
        I * suzukiCriticalApertureBoundaryAtom h a (-t) pe.1 pe.2) / 2 := by
  change (2 : ℂ)⁻¹ *
      (suzukiCriticalApertureBoundaryAtom h a t pe.1 pe.2 +
        I * suzukiCriticalApertureBoundaryAtom h a (-t) pe.1 pe.2) = _
  ring

@[simp] theorem suzukiCriticalApertureNegativeLightLp_apply
    (h a t : ℝ) (hh : 0 < h) (ha : 0 < a) (pe : Nat.Primes × ℕ) :
    suzukiCriticalApertureNegativeLightLp h a t hh ha pe =
      (suzukiCriticalApertureBoundaryAtom h a t pe.1 pe.2 -
        I * suzukiCriticalApertureBoundaryAtom h a (-t) pe.1 pe.2) / 2 := by
  change (2 : ℂ)⁻¹ *
      (suzukiCriticalApertureBoundaryAtom h a t pe.1 pe.2 -
        I * suzukiCriticalApertureBoundaryAtom h a (-t) pe.1 pe.2) = _
  ring

/-- Positive dressed light is exactly raw wall positive light times the innovation. -/
theorem suzukiCriticalAperturePositiveLightLp_apply_eq_wallLight_mul_innovation
    (h a t : ℝ) (hh : 0 < h) (ha : 0 < a) (pe : Nat.Primes × ℕ) :
    suzukiCriticalAperturePositiveLightLp h a t hh ha pe =
      suzukiCriticalWallPositiveLightAmplitude t pe.1 pe.2 *
        (xiMobiusCubicNormalizedInnovationFeature h a pe : ℂ) := by
  rw [suzukiCriticalAperturePositiveLightLp_apply,
    suzukiCriticalApertureBoundaryAtom_eq_wallField_mul_innovation,
    suzukiCriticalApertureBoundaryAtom_eq_wallField_mul_innovation]
  unfold suzukiCriticalWallPositiveLightAmplitude
  ring

/-- Negative dressed light is exactly the forced wall completion times the innovation. -/
theorem suzukiCriticalApertureNegativeLightLp_apply_eq_wallLight_mul_innovation
    (h a t : ℝ) (hh : 0 < h) (ha : 0 < a) (pe : Nat.Primes × ℕ) :
    suzukiCriticalApertureNegativeLightLp h a t hh ha pe =
      suzukiCriticalWallNegativeLightAmplitude t pe.1 pe.2 *
        (xiMobiusCubicNormalizedInnovationFeature h a pe : ℂ) := by
  rw [suzukiCriticalApertureNegativeLightLp_apply,
    suzukiCriticalApertureBoundaryAtom_eq_wallField_mul_innovation,
    suzukiCriticalApertureBoundaryAtom_eq_wallField_mul_innovation]
  unfold suzukiCriticalWallNegativeLightAmplitude
  ring

/-- Completed positive-light all-prime Gram kernel. -/
def suzukiCriticalAperturePositiveLightKernel
    (h a t u : ℝ) (hh : 0 < h) (ha : 0 < a) : ℂ :=
  inner ℂ (suzukiCriticalAperturePositiveLightLp h a u hh ha)
    (suzukiCriticalAperturePositiveLightLp h a t hh ha)

/-- Completed negative-light all-prime Gram kernel. -/
def suzukiCriticalApertureNegativeLightKernel
    (h a t u : ℝ) (hh : 0 < h) (ha : 0 < a) : ℂ :=
  inner ℂ (suzukiCriticalApertureNegativeLightLp h a u hh ha)
    (suzukiCriticalApertureNegativeLightLp h a t hh ha)

/-- Completed aperture-dressed wall Gram. -/
def suzukiCriticalApertureBoundaryFieldKernel
    (h a t u : ℝ) (hh : 0 < h) (ha : 0 < a) : ℂ :=
  inner ℂ (suzukiCriticalApertureBoundaryFieldLp h a u hh ha)
    (suzukiCriticalApertureBoundaryFieldLp h a t hh ha)

/-- FE-reflected dressed current formed after pre-split Hilbert completion. -/
def suzukiCriticalApertureReflectedCurrentKernel
    (h a t u : ℝ) (hh : 0 < h) (ha : 0 < a) : ℂ :=
  I / 2 *
    (suzukiCriticalApertureBoundaryFieldKernel h a (-t) u hh ha -
      suzukiCriticalApertureBoundaryFieldKernel h a t (-u) hh ha)

/-- Completed dressed wall energy remains exactly height-flat. -/
theorem suzukiCriticalApertureBoundaryFieldKernel_diagonal_height_independent
    (h a t u : ℝ) (hh : 0 < h) (ha : 0 < a) :
    suzukiCriticalApertureBoundaryFieldKernel h a t t hh ha =
      suzukiCriticalApertureBoundaryFieldKernel h a u u hh ha := by
  rw [suzukiCriticalApertureBoundaryFieldKernel,
    suzukiCriticalApertureBoundaryFieldKernel,
    lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro pe
  simp only [suzukiCriticalApertureBoundaryFieldLp_apply, RCLike.inner_apply]
  change suzukiCriticalApertureBoundaryAtom h a t pe.1 pe.2 *
      conj (suzukiCriticalApertureBoundaryAtom h a t pe.1 pe.2) =
    suzukiCriticalApertureBoundaryAtom h a u pe.1 pe.2 *
      conj (suzukiCriticalApertureBoundaryAtom h a u pe.1 pe.2)
  rw [Complex.mul_conj, Complex.mul_conj]
  exact_mod_cast normSq_suzukiCriticalApertureBoundaryAtom_height_independent
    h a t u pe.1 pe.2

/-- **Global reflected-current factorization.** -/
theorem suzukiCriticalAperturePositiveLightKernel_sub_negative_eq_reflected
    (h a t u : ℝ) (hh : 0 < h) (ha : 0 < a) :
    suzukiCriticalAperturePositiveLightKernel h a t u hh ha -
        suzukiCriticalApertureNegativeLightKernel h a t u hh ha =
      suzukiCriticalApertureReflectedCurrentKernel h a t u hh ha := by
  simp only [suzukiCriticalAperturePositiveLightKernel,
    suzukiCriticalApertureNegativeLightKernel,
    suzukiCriticalApertureReflectedCurrentKernel,
    suzukiCriticalApertureBoundaryFieldKernel,
    suzukiCriticalAperturePositiveLightLp,
    suzukiCriticalApertureNegativeLightLp,
    inner_smul_left, inner_smul_right, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right]
  simp only [map_inv₀, map_ofNat, starRingEnd_apply]
  have hstarI : star I = -I := Complex.conj_I
  rw [hstarI]
  ring

/-- **Exact all-prime Ward completion.** -/
theorem suzukiCriticalApertureReflectedCurrentKernel_add_negative_eq_positive
    (h a t u : ℝ) (hh : 0 < h) (ha : 0 < a) :
    suzukiCriticalApertureReflectedCurrentKernel h a t u hh ha +
        suzukiCriticalApertureNegativeLightKernel h a t u hh ha =
      suzukiCriticalAperturePositiveLightKernel h a t u hh ha := by
  rw [← suzukiCriticalAperturePositiveLightKernel_sub_negative_eq_reflected]
  ring

/-! ## Finite height packet positivity -/

/-- Transposed kernel convention matches `Matrix.gram`'s inner-product orientation. -/
def suzukiCriticalAperturePositiveLightMatrix {N : ℕ}
    (h a : ℝ) (height : Fin N → ℝ) (hh : 0 < h) (ha : 0 < a) :
    Matrix (Fin N) (Fin N) ℂ := fun i j =>
  suzukiCriticalAperturePositiveLightKernel h a (height j) (height i) hh ha

theorem suzukiCriticalAperturePositiveLightMatrix_posSemidef {N : ℕ}
    (h a : ℝ) (height : Fin N → ℝ) (hh : 0 < h) (ha : 0 < a) :
    (suzukiCriticalAperturePositiveLightMatrix h a height hh ha).PosSemidef := by
  have hgram : suzukiCriticalAperturePositiveLightMatrix h a height hh ha =
      Matrix.gram ℂ
        (fun i => suzukiCriticalAperturePositiveLightLp h a (height i) hh ha) := by
    ext i j
    simp [suzukiCriticalAperturePositiveLightMatrix,
      suzukiCriticalAperturePositiveLightKernel, Matrix.gram_apply]
  rw [hgram]
  exact Matrix.posSemidef_gram ℂ _

/-- Transposed kernel convention matches `Matrix.gram`'s inner-product orientation. -/
def suzukiCriticalApertureNegativeLightMatrix {N : ℕ}
    (h a : ℝ) (height : Fin N → ℝ) (hh : 0 < h) (ha : 0 < a) :
    Matrix (Fin N) (Fin N) ℂ := fun i j =>
  suzukiCriticalApertureNegativeLightKernel h a (height j) (height i) hh ha

theorem suzukiCriticalApertureNegativeLightMatrix_posSemidef {N : ℕ}
    (h a : ℝ) (height : Fin N → ℝ) (hh : 0 < h) (ha : 0 < a) :
    (suzukiCriticalApertureNegativeLightMatrix h a height hh ha).PosSemidef := by
  have hgram : suzukiCriticalApertureNegativeLightMatrix h a height hh ha =
      Matrix.gram ℂ
        (fun i => suzukiCriticalApertureNegativeLightLp h a (height i) hh ha) := by
    ext i j
    simp [suzukiCriticalApertureNegativeLightMatrix,
      suzukiCriticalApertureNegativeLightKernel, Matrix.gram_apply]
  rw [hgram]
  exact Matrix.posSemidef_gram ℂ _

end

end RHTower
