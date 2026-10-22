import GaloisForLFunctions.HTGeometry.GeometricPhaseLightCoercivity
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCoherentCausalDepthFusion

/-!
# Suzuki valuation-depth light coercivity

One bare Suzuki wall atom can have zero negative-light energy at a phase-aligned height.  This file
proves that the actual aperture-dressed source cannot retain that hole through all prime-power
valuation depths.

For each prime, its complete negative-light depth energy is an exact geometric phase-orbit energy.
It therefore has a strictly positive, phase-independent, optimal lower bound.  The result uses the
actual Gamma quarter-shift, true-aperture innovation, and Xi-real/functional-equation light split.
No RH premise, Xi zero, numerical computation, or target positivity assumption is used.
-/

open Complex
open scoped ComplexConjugate

namespace RHTower

noncomputable section

/-- Exact negative-light energy of one bare critical wall atom. -/
theorem normSq_suzukiCriticalWallNegativeLightAmplitude_eq
    (t : ℝ) (p : Nat.Primes) (e : ℕ) :
    Complex.normSq (suzukiCriticalWallNegativeLightAmplitude t p e) =
      (ArithmeticFunction.vonMangoldt (xiGammaEulerValuationNat (p, e)) /
          Real.sqrt (xiGammaEulerValuationNat (p, e) : ℝ)) / 2 *
        (1 - Real.sin
          (t * Real.log (xiGammaEulerValuationNat (p, e) : ℝ))) := by
  have hsum :=
    normSq_suzukiCriticalWallLightAmplitudes_eq_vonMangoldt_div_sqrt t p e
  have hdiff :=
    normSq_suzukiCriticalWallPositiveLightAmplitude_sub_negative t p e
  have hkernel :
      (suzukiOscillatoryKernel (t : ℂ)
        (Real.log (xiGammaEulerValuationNat (p, e) : ℝ))).im =
          Real.sin
            (t * Real.log (xiGammaEulerValuationNat (p, e) : ℝ)) := by
    unfold suzukiOscillatoryKernel
    rw [show
      ((Real.log (xiGammaEulerValuationNat (p, e) : ℝ) : ℝ) : ℂ) *
          (I * (t : ℂ)) =
        ((t * Real.log (xiGammaEulerValuationNat (p, e) : ℝ) : ℝ) : ℂ) * I by
          push_cast
          ring]
    exact Complex.exp_ofReal_mul_I_im _
  have hsq := congrArg Complex.im
    (sq_suzukiCriticalWallField_eq_farHingeNumerator t p e)
  rw [Complex.mul_im] at hsq
  rw [hkernel] at hsq
  simp at hsq
  nlinarith

private theorem normSq_pow (z : ℂ) (e : ℕ) :
    Complex.normSq (z ^ e) = Complex.normSq z ^ e := by
  induction e with
  | zero => simp [Complex.normSq_apply]
  | succ e ih =>
      rw [pow_succ, Complex.normSq_mul, ih, pow_succ]

/-- Squared complex depth ratio is the square of the source-selected positive fusion radius. -/
theorem normSq_suzukiCriticalApertureDepthRatio_eq_radius_sq
    (h a t : ℝ) (p : Nat.Primes) :
    Complex.normSq (suzukiCriticalApertureDepthRatio h a t p) =
      suzukiCriticalApertureDepthFusionRadius h a p ^ (2 : ℕ) := by
  rw [suzukiCriticalApertureDepthRatio_eq_radius_mul_phase,
    Complex.normSq_mul, Complex.normSq_ofReal]
  have hphase :
      Complex.normSq (suzukiCriticalApertureDepthFusionPhase t p) = 1 := by
    rw [Complex.normSq_eq_norm_sq,
      norm_suzukiCriticalApertureDepthFusionPhase]
    norm_num
  rw [hphase, mul_one]
  ring

theorem normSq_suzukiCriticalApertureDepthRatio_eq_exp_mul_diskNode_fourth
    (h a t : ℝ) (p : Nat.Primes) :
    Complex.normSq (suzukiCriticalApertureDepthRatio h a t p) =
      Real.exp (-(1 / 2 : ℝ) * Real.log (p : ℝ)) *
        xiMobiusContinuousApertureDiskNode ((h / 2) * a) p ^ (4 : ℕ) := by
  rw [normSq_suzukiCriticalApertureDepthRatio_eq_radius_sq,
    suzukiCriticalApertureDepthFusionRadius]
  rw [mul_pow]
  have hExp :
      Real.exp (-(1 / 4 : ℝ) * Real.log (p : ℝ)) ^ (2 : ℕ) =
        Real.exp (-(1 / 2 : ℝ) * Real.log (p : ℝ)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hExp]
  ring

/-- Depth-zero wall norm is exactly the square of the positive calibrated endpoint amplitude. -/
theorem normSq_suzukiCriticalApertureBoundaryAtom_zero_eq_endpoint_sq
    (h a t : ℝ) (p : Nat.Primes) :
    Complex.normSq (suzukiCriticalApertureBoundaryAtom h a t p 0) =
      suzukiCriticalEntryWallEndpointAmplitude h a p 0 ^ (2 : ℕ) := by
  rw [suzukiCriticalApertureBoundaryAtom_zero_eq_endpoint_mul_phase,
    Complex.normSq_mul, Complex.normSq_ofReal]
  have hphase :
      Complex.normSq (suzukiCriticalApertureDepthFusionPhase t p) = 1 := by
    rw [Complex.normSq_eq_norm_sq,
      norm_suzukiCriticalApertureDepthFusionPhase]
    norm_num
  rw [hphase, mul_one]
  ring

theorem normSq_suzukiCriticalApertureBoundaryAtom_eq_geometricDepth
    (h a t : ℝ) (p : Nat.Primes) (e : ℕ) :
    Complex.normSq (suzukiCriticalApertureBoundaryAtom h a t p e) =
      suzukiCriticalEntryWallEndpointAmplitude h a p 0 ^ (2 : ℕ) *
        (suzukiCriticalApertureDepthFusionRadius h a p ^ (2 : ℕ)) ^ e := by
  rw [suzukiCriticalApertureBoundaryAtom_eq_base_mul_ratio_pow,
    Complex.normSq_mul, normSq_pow,
    normSq_suzukiCriticalApertureBoundaryAtom_zero_eq_endpoint_sq,
    normSq_suzukiCriticalApertureDepthRatio_eq_radius_sq]

/-- One actual dressed negative-light coordinate is the universal geometric light term. -/
theorem normSq_suzukiCriticalApertureNegativeLightLp_eq_geometricTerm
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a)
    (t : ℝ) (p : Nat.Primes) (e : ℕ) :
    Complex.normSq
        (suzukiCriticalApertureNegativeLightLp h a t hh ha (p, e)) =
      suzukiCriticalEntryWallEndpointAmplitude h a p 0 ^ (2 : ℕ) / 2 *
        HTGeometry.geometricNegativeLightTerm
          (suzukiCriticalApertureDepthFusionRadius h a p ^ (2 : ℕ))
          (t * Real.log (p : ℝ)) e := by
  have hlog :
      Real.log (xiGammaEulerValuationNat (p, e) : ℝ) =
        ((e : ℝ) + 1) * Real.log (p : ℝ) := by
    rw [xiGammaEulerValuationNat]
    push_cast
    rw [Real.log_pow]
    norm_num
  have hraw := normSq_suzukiCriticalWallNegativeLightAmplitude_eq t p e
  rw [hlog] at hraw
  have hwall :
      Complex.normSq (suzukiCriticalWallField t p e) =
        ArithmeticFunction.vonMangoldt (xiGammaEulerValuationNat (p, e)) /
          Real.sqrt (xiGammaEulerValuationNat (p, e) : ℝ) := by
    calc
      _ = Complex.normSq (suzukiCriticalWallPositiveLightAmplitude t p e) +
          Complex.normSq (suzukiCriticalWallNegativeLightAmplitude t p e) :=
        (normSq_suzukiCriticalWallPositiveLightAmplitude_add_negative t p e).symm
      _ = _ :=
        normSq_suzukiCriticalWallLightAmplitudes_eq_vonMangoldt_div_sqrt t p e
  have hboundary :
      Complex.normSq (suzukiCriticalApertureBoundaryAtom h a t p e) =
        (ArithmeticFunction.vonMangoldt (xiGammaEulerValuationNat (p, e)) /
            Real.sqrt (xiGammaEulerValuationNat (p, e) : ℝ)) *
          xiMobiusCubicNormalizedInnovationFeature h a (p, e) ^ (2 : ℕ) := by
    rw [suzukiCriticalApertureBoundaryAtom_eq_wallField_mul_innovation,
      Complex.normSq_mul, hwall, Complex.normSq_ofReal]
    ring
  have hdepth :
      Complex.normSq (suzukiCriticalApertureBoundaryAtom h a t p e) =
        Complex.normSq (suzukiCriticalApertureBoundaryAtom h a t p 0) *
          Complex.normSq (suzukiCriticalApertureDepthRatio h a t p) ^ e := by
    rw [suzukiCriticalApertureBoundaryAtom_eq_base_mul_ratio_pow,
      Complex.normSq_mul, normSq_pow]
  rw [suzukiCriticalApertureNegativeLightLp_apply_eq_wallLight_mul_innovation,
    Complex.normSq_mul, Complex.normSq_ofReal, hraw,
    HTGeometry.geometricNegativeLightTerm_eq]
  calc
    _ = Complex.normSq (suzukiCriticalApertureBoundaryAtom h a t p e) / 2 *
        (1 - Real.sin (((e : ℝ) + 1) * (t * Real.log (p : ℝ)))) := by
          rw [hboundary]
          ring
    _ = _ := by
      rw [hdepth,
        normSq_suzukiCriticalApertureBoundaryAtom_zero_eq_endpoint_sq,
        normSq_suzukiCriticalApertureDepthRatio_eq_radius_sq]
      ring

/-- At each depth the actual dressed light split partitions the complete boundary-atom energy. -/
theorem normSq_suzukiCriticalApertureLightLp_add
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a)
    (t : ℝ) (p : Nat.Primes) (e : ℕ) :
    Complex.normSq
        (suzukiCriticalAperturePositiveLightLp h a t hh ha (p, e)) +
      Complex.normSq
        (suzukiCriticalApertureNegativeLightLp h a t hh ha (p, e)) =
      Complex.normSq (suzukiCriticalApertureBoundaryAtom h a t p e) := by
  rw [suzukiCriticalAperturePositiveLightLp_apply_eq_wallLight_mul_innovation,
    suzukiCriticalApertureNegativeLightLp_apply_eq_wallLight_mul_innovation,
    suzukiCriticalApertureBoundaryAtom_eq_wallField_mul_innovation]
  repeat rw [Complex.normSq_mul]
  simp only [Complex.normSq_ofReal]
  have hsum :=
    normSq_suzukiCriticalWallPositiveLightAmplitude_add_negative t p e
  nlinarith

/-- One actual dressed positive-light coordinate is the companion universal geometric term. -/
theorem normSq_suzukiCriticalAperturePositiveLightLp_eq_geometricTerm
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a)
    (t : ℝ) (p : Nat.Primes) (e : ℕ) :
    Complex.normSq
        (suzukiCriticalAperturePositiveLightLp h a t hh ha (p, e)) =
      suzukiCriticalEntryWallEndpointAmplitude h a p 0 ^ (2 : ℕ) / 2 *
        HTGeometry.geometricPositiveLightTerm
          (suzukiCriticalApertureDepthFusionRadius h a p ^ (2 : ℕ))
          (t * Real.log (p : ℝ)) e := by
  have hsum := normSq_suzukiCriticalApertureLightLp_add hh ha t p e
  rw [normSq_suzukiCriticalApertureBoundaryAtom_eq_geometricDepth] at hsum
  have hminus :=
    normSq_suzukiCriticalApertureNegativeLightLp_eq_geometricTerm hh ha t p e
  rw [HTGeometry.geometricNegativeLightTerm_eq] at hminus
  unfold HTGeometry.geometricPositiveLightTerm
  nlinarith

/-- Negative-light energy on one actual prime ray after all valuation depths are summed. -/
def suzukiCriticalApertureNegativeLightDepthEnergy
    (h a t : ℝ) (hh : 0 < h) (ha : 0 < a) (p : Nat.Primes) : ℝ :=
  ∑' e : ℕ,
    Complex.normSq
      (suzukiCriticalApertureNegativeLightLp h a t hh ha (p, e))

/-- Positive-light energy on one actual prime ray after all valuation depths are summed. -/
def suzukiCriticalAperturePositiveLightDepthEnergy
    (h a t : ℝ) (hh : 0 < h) (ha : 0 < a) (p : Nat.Primes) : ℝ :=
  ∑' e : ℕ,
    Complex.normSq
      (suzukiCriticalAperturePositiveLightLp h a t hh ha (p, e))

/-- Exact Suzuki depth-resummed negative-light law. -/
theorem suzukiCriticalApertureNegativeLightDepthEnergy_eq
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a)
    (t : ℝ) (p : Nat.Primes) :
    suzukiCriticalApertureNegativeLightDepthEnergy h a t hh ha p =
      suzukiCriticalEntryWallEndpointAmplitude h a p 0 ^ (2 : ℕ) / 2 *
        HTGeometry.geometricNegativeLightEnergy
          (suzukiCriticalApertureDepthFusionRadius h a p ^ (2 : ℕ))
          (t * Real.log (p : ℝ)) := by
  let R := suzukiCriticalApertureDepthFusionRadius h a p ^ (2 : ℕ)
  have hr0 := suzukiCriticalApertureDepthFusionRadius_pos h a p
  have hr1 := suzukiCriticalApertureDepthFusionRadius_lt_one hh ha p
  have hR0 : 0 ≤ R := sq_nonneg _
  have hR1 : R < 1 := by
    dsimp [R]
    nlinarith
  rw [suzukiCriticalApertureNegativeLightDepthEnergy]
  rw [show (∑' e : ℕ,
      Complex.normSq
        (suzukiCriticalApertureNegativeLightLp h a t hh ha (p, e))) =
      ∑' e : ℕ,
        suzukiCriticalEntryWallEndpointAmplitude h a p 0 ^ (2 : ℕ) / 2 *
          HTGeometry.geometricNegativeLightTerm
            R (t * Real.log (p : ℝ)) e by
        apply tsum_congr
        intro e
        exact
          normSq_suzukiCriticalApertureNegativeLightLp_eq_geometricTerm
            hh ha t p e]
  rw [tsum_mul_left,
    HTGeometry.tsum_geometricNegativeLightTerm_eq hR0 hR1]

/-- Exact positive-light companion law. -/
theorem suzukiCriticalAperturePositiveLightDepthEnergy_eq
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a)
    (t : ℝ) (p : Nat.Primes) :
    suzukiCriticalAperturePositiveLightDepthEnergy h a t hh ha p =
      suzukiCriticalEntryWallEndpointAmplitude h a p 0 ^ (2 : ℕ) / 2 *
        HTGeometry.geometricPositiveLightEnergy
          (suzukiCriticalApertureDepthFusionRadius h a p ^ (2 : ℕ))
          (t * Real.log (p : ℝ)) := by
  let R := suzukiCriticalApertureDepthFusionRadius h a p ^ (2 : ℕ)
  have hr0 := suzukiCriticalApertureDepthFusionRadius_pos h a p
  have hr1 := suzukiCriticalApertureDepthFusionRadius_lt_one hh ha p
  have hR0 : 0 ≤ R := sq_nonneg _
  have hR1 : R < 1 := by
    dsimp [R]
    nlinarith
  rw [suzukiCriticalAperturePositiveLightDepthEnergy]
  rw [show (∑' e : ℕ,
      Complex.normSq
        (suzukiCriticalAperturePositiveLightLp h a t hh ha (p, e))) =
      ∑' e : ℕ,
        suzukiCriticalEntryWallEndpointAmplitude h a p 0 ^ (2 : ℕ) / 2 *
          HTGeometry.geometricPositiveLightTerm
            R (t * Real.log (p : ℝ)) e by
        apply tsum_congr
        intro e
        exact
          normSq_suzukiCriticalAperturePositiveLightLp_eq_geometricTerm
            hh ha t p e]
  rw [tsum_mul_left,
    HTGeometry.tsum_geometricPositiveLightTerm_eq hR0 hR1]

/-- **Actual-source sharp floor.**  Every prime ray carries a uniform negative-light channel. -/
theorem suzukiCriticalApertureNegativeLightDepthEnergy_ge_sharpFloor
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a)
    (t : ℝ) (p : Nat.Primes) :
    suzukiCriticalEntryWallEndpointAmplitude h a p 0 ^ (2 : ℕ) / 2 *
          ((suzukiCriticalApertureDepthFusionRadius h a p ^ (2 : ℕ)) /
            (1 - (suzukiCriticalApertureDepthFusionRadius h a p ^ (2 : ℕ)) ^ (2 : ℕ))) ≤
      suzukiCriticalApertureNegativeLightDepthEnergy h a t hh ha p := by
  let R := suzukiCriticalApertureDepthFusionRadius h a p ^ (2 : ℕ)
  have hr0 := suzukiCriticalApertureDepthFusionRadius_pos h a p
  have hr1 := suzukiCriticalApertureDepthFusionRadius_lt_one hh ha p
  have hR0 : 0 ≤ R := sq_nonneg _
  have hR1 : R < 1 := by
    dsimp [R]
    nlinarith
  rw [suzukiCriticalApertureNegativeLightDepthEnergy_eq hh ha]
  exact mul_le_mul_of_nonneg_left
    (HTGeometry.geometricNegativeLightEnergy_ge_sharpFloor hR0 hR1)
    (div_nonneg (sq_nonneg _) (by norm_num))

theorem suzukiCriticalAperturePositiveLightDepthEnergy_ge_sharpFloor
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a)
    (t : ℝ) (p : Nat.Primes) :
    suzukiCriticalEntryWallEndpointAmplitude h a p 0 ^ (2 : ℕ) / 2 *
          ((suzukiCriticalApertureDepthFusionRadius h a p ^ (2 : ℕ)) /
            (1 - (suzukiCriticalApertureDepthFusionRadius h a p ^ (2 : ℕ)) ^ (2 : ℕ))) ≤
      suzukiCriticalAperturePositiveLightDepthEnergy h a t hh ha p := by
  let R := suzukiCriticalApertureDepthFusionRadius h a p ^ (2 : ℕ)
  have hr0 := suzukiCriticalApertureDepthFusionRadius_pos h a p
  have hr1 := suzukiCriticalApertureDepthFusionRadius_lt_one hh ha p
  have hR0 : 0 ≤ R := sq_nonneg _
  have hR1 : R < 1 := by
    dsimp [R]
    nlinarith
  rw [suzukiCriticalAperturePositiveLightDepthEnergy_eq hh ha]
  exact mul_le_mul_of_nonneg_left
    (HTGeometry.geometricPositiveLightEnergy_ge_sharpFloor hR0 hR1)
    (div_nonneg (sq_nonneg _) (by norm_num))

/-- Both actual completed light channels exactly partition the geometric source mass. -/
theorem suzukiCriticalApertureLightDepthEnergies_add
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a)
    (t : ℝ) (p : Nat.Primes) :
    suzukiCriticalApertureNegativeLightDepthEnergy h a t hh ha p +
        suzukiCriticalAperturePositiveLightDepthEnergy h a t hh ha p =
      suzukiCriticalEntryWallEndpointAmplitude h a p 0 ^ (2 : ℕ) /
        (1 - suzukiCriticalApertureDepthFusionRadius h a p ^ (2 : ℕ)) := by
  have hr0 := suzukiCriticalApertureDepthFusionRadius_pos h a p
  have hr1 := suzukiCriticalApertureDepthFusionRadius_lt_one hh ha p
  rw [suzukiCriticalApertureNegativeLightDepthEnergy_eq hh ha,
    suzukiCriticalAperturePositiveLightDepthEnergy_eq hh ha]
  have hsum :
      HTGeometry.geometricNegativeLightEnergy
          (suzukiCriticalApertureDepthFusionRadius h a p ^ (2 : ℕ))
          (t * Real.log (p : ℝ)) +
        HTGeometry.geometricPositiveLightEnergy
          (suzukiCriticalApertureDepthFusionRadius h a p ^ (2 : ℕ))
          (t * Real.log (p : ℝ)) =
        2 / (1 - suzukiCriticalApertureDepthFusionRadius h a p ^ (2 : ℕ)) :=
    HTGeometry.geometricLightEnergies_add
      (by nlinarith [mul_pos hr0 (sub_pos.mpr hr1)])
  calc
    _ = suzukiCriticalEntryWallEndpointAmplitude h a p 0 ^ (2 : ℕ) / 2 *
        (HTGeometry.geometricNegativeLightEnergy
            (suzukiCriticalApertureDepthFusionRadius h a p ^ (2 : ℕ))
            (t * Real.log (p : ℝ)) +
          HTGeometry.geometricPositiveLightEnergy
            (suzukiCriticalApertureDepthFusionRadius h a p ^ (2 : ℕ))
            (t * Real.log (p : ℝ))) := by ring
    _ = suzukiCriticalEntryWallEndpointAmplitude h a p 0 ^ (2 : ℕ) / 2 *
        (2 / (1 - suzukiCriticalApertureDepthFusionRadius h a p ^ (2 : ℕ))) := by
          rw [hsum]
    _ = _ := by ring

/-- The sharp actual-source floor is strictly positive at every positive aperture. -/
theorem suzukiCriticalApertureNegativeLightDepthEnergy_pos
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a)
    (t : ℝ) (p : Nat.Primes) :
    0 < suzukiCriticalApertureNegativeLightDepthEnergy h a t hh ha p := by
  have hr0 := suzukiCriticalApertureDepthFusionRadius_pos h a p
  have hr1 := suzukiCriticalApertureDepthFusionRadius_lt_one hh ha p
  have hA0 := suzukiCriticalEntryWallEndpointAmplitude_zero_pos hh ha p
  have hfloor :
      0 <
        suzukiCriticalEntryWallEndpointAmplitude h a p 0 ^ (2 : ℕ) / 2 *
          ((suzukiCriticalApertureDepthFusionRadius h a p ^ (2 : ℕ)) /
            (1 - (suzukiCriticalApertureDepthFusionRadius h a p ^ (2 : ℕ)) ^ (2 : ℕ))) := by
    apply mul_pos
    · exact div_pos (sq_pos_of_pos hA0) (by norm_num)
    · apply div_pos
      · exact sq_pos_of_pos hr0
      · have hrSq :
            suzukiCriticalApertureDepthFusionRadius h a p ^ (2 : ℕ) < 1 := by
          nlinarith [mul_pos hr0 (sub_pos.mpr hr1)]
        nlinarith [mul_pos (sq_pos_of_pos hr0) (sub_pos.mpr hrSq)]
  exact hfloor.trans_le
    (suzukiCriticalApertureNegativeLightDepthEnergy_ge_sharpFloor hh ha t p)

theorem suzukiCriticalAperturePositiveLightDepthEnergy_pos
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a)
    (t : ℝ) (p : Nat.Primes) :
    0 < suzukiCriticalAperturePositiveLightDepthEnergy h a t hh ha p := by
  have hr0 := suzukiCriticalApertureDepthFusionRadius_pos h a p
  have hr1 := suzukiCriticalApertureDepthFusionRadius_lt_one hh ha p
  have hA0 := suzukiCriticalEntryWallEndpointAmplitude_zero_pos hh ha p
  have hfloor :
      0 <
        suzukiCriticalEntryWallEndpointAmplitude h a p 0 ^ (2 : ℕ) / 2 *
          ((suzukiCriticalApertureDepthFusionRadius h a p ^ (2 : ℕ)) /
            (1 - (suzukiCriticalApertureDepthFusionRadius h a p ^ (2 : ℕ)) ^ (2 : ℕ))) := by
    apply mul_pos
    · exact div_pos (sq_pos_of_pos hA0) (by norm_num)
    · apply div_pos
      · exact sq_pos_of_pos hr0
      · have hrSq :
            suzukiCriticalApertureDepthFusionRadius h a p ^ (2 : ℕ) < 1 := by
          nlinarith [mul_pos hr0 (sub_pos.mpr hr1)]
        nlinarith [mul_pos (sq_pos_of_pos hr0) (sub_pos.mpr hrSq)]
  exact hfloor.trans_le
    (suzukiCriticalAperturePositiveLightDepthEnergy_ge_sharpFloor hh ha t p)

/-- Optimality: for every prime and aperture, one height attains the universal floor exactly. -/
theorem exists_suzukiCriticalApertureNegativeLightDepthEnergy_eq_sharpFloor
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (p : Nat.Primes) :
    ∃ t : ℝ,
      suzukiCriticalApertureNegativeLightDepthEnergy h a t hh ha p =
        suzukiCriticalEntryWallEndpointAmplitude h a p 0 ^ (2 : ℕ) / 2 *
          ((suzukiCriticalApertureDepthFusionRadius h a p ^ (2 : ℕ)) /
            (1 - (suzukiCriticalApertureDepthFusionRadius h a p ^ (2 : ℕ)) ^ (2 : ℕ))) := by
  let R := suzukiCriticalApertureDepthFusionRadius h a p ^ (2 : ℕ)
  have hr0 := suzukiCriticalApertureDepthFusionRadius_pos h a p
  have hr1 := suzukiCriticalApertureDepthFusionRadius_lt_one hh ha p
  have hR0 : 0 ≤ R := sq_nonneg _
  have hR1 : R < 1 := by
    dsimp [R]
    nlinarith
  obtain ⟨θ, hθ⟩ :=
    HTGeometry.exists_geometricNegativeLightEnergy_eq_sharpFloor hR0 hR1
  have hlogp : Real.log (p : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast p.property.one_lt)).ne'
  refine ⟨θ / Real.log (p : ℝ), ?_⟩
  rw [suzukiCriticalApertureNegativeLightDepthEnergy_eq hh ha]
  have hphase :
      θ / Real.log (p : ℝ) * Real.log (p : ℝ) = θ :=
    div_mul_cancel₀ θ hlogp
  rw [hphase, hθ]

end

end RHTower
