import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeatureCanonicalLatticeSummedDisplacement
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeatureUniformLatticeCharge
import GaloisForLFunctions.RHTower.XiWardEdgeL2CrossKernel
import GaloisForLFunctions.HTGeometry.CauchyKernelStripDecay
import GaloisForLFunctions.RHTower.ExteriorProfileBounds
import GaloisForLFunctions.HTGeometry.ExponentialPolynomialLatticeWeight
import Mathlib.Analysis.Fourier.PoissonSummation
import GaloisForLFunctions.RHTower.MobiusLaplaceAdditiveTriangle
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodEighthFockSector

/-!
# Sharp Poisson envelope for the HCF height lattice

The real-axis HCF profile `4 / (1 + x²)²` has total mass `2π` and Fourier transform
`2π (1 + 2π|ξ|) exp(-2π|ξ|)`.  This module derives that transform from the corpus mass-derivative
calculus, applies the general Poisson summation theorem, and obtains a uniform full-lattice charge
ceiling of `9`.  Every finite HCF center set, and therefore every fused compact-cutoff weight used
by the finite-displacement source gate, inherits the same ceiling.

This replaces the earlier quartic-majorant constant `1024 * intNatAbsPowTotal 4` for domination.
It is source-independent analytic infrastructure; it does not assert the remaining prime--Gamma
covariance ceiling required for the `75%` zero-density endpoint.
-/

open Complex Filter Topology Set MeasureTheory
open GaloisForLFunctions.HTGeometry
open scoped BigOperators

namespace RHTower

noncomputable section

theorem integrable_criticalFeatureRealBoundaryWeight (t : ℝ) :
    Integrable (criticalFeatureRealBoundaryWeight t) := by
  have h := (integrable_sq_lorentzianHalf (x := (1 : ℝ)) (by norm_num) (-t)).const_mul 4
  apply h.congr
  filter_upwards with x
  change 4 * ((1 : ℝ) / (1 ^ 2 + (x + (-t)) ^ 2)) ^ 2 =
    4 / (1 + (x - t) ^ 2) ^ 2
  have hD : 1 + (x - t) ^ 2 ≠ 0 := by positivity
  field_simp
  ring

theorem integral_criticalFeatureRealBoundaryWeight (t : ℝ) :
    ∫ x : ℝ, criticalFeatureRealBoundaryWeight t x = 2 * Real.pi := by
  rw [show criticalFeatureRealBoundaryWeight t =
      fun x : ℝ => 4 * ((1 : ℝ) / (1 ^ 2 + (x + (-t)) ^ 2)) ^ 2 by
    funext x
    change 4 / (1 + (x - t) ^ 2) ^ 2 =
      4 * ((1 : ℝ) / (1 ^ 2 + (x + (-t)) ^ 2)) ^ 2
    have hD : 1 + (x - t) ^ 2 ≠ 0 := by positivity
    field_simp
    ring]
  rw [MeasureTheory.integral_const_mul,
    integral_sq_lorentzianHalf (x := (1 : ℝ)) (by norm_num) (-t)]
  ring

theorem criticalFeatureLatticeBoundaryCutoffWeight_eq
    (K : Finset ℤ) (cutoff : ℕ) (x : ℝ) :
    criticalFeatureLatticeBoundaryCutoffWeight K cutoff x =
      (∑ k ∈ K, criticalFeatureRealBoundaryWeight (k : ℝ) x) *
        SchwartzMap.realCompactIntervalCutoff (cutoff : ℝ) x := by
  simp only [criticalFeatureLatticeBoundaryCutoffWeight,
    criticalFeatureBoundaryCutoffWeight, Finset.sum_mul]

theorem criticalFeatureLatticeBoundaryCutoffWeight_nonnegative
    (K : Finset ℤ) (cutoff : ℕ) (x : ℝ) :
    0 ≤ criticalFeatureLatticeBoundaryCutoffWeight K cutoff x := by
  rw [criticalFeatureLatticeBoundaryCutoffWeight_eq]
  exact mul_nonneg
    (Finset.sum_nonneg fun k hk => by
      unfold criticalFeatureRealBoundaryWeight
      exact div_nonneg (by norm_num) (sq_nonneg _))
    (SchwartzMap.realCompactIntervalCutoff_nonnegative _ _)

theorem criticalFeatureLatticeBoundaryCutoffWeight_le_uncut
    (K : Finset ℤ) (cutoff : ℕ) (x : ℝ) :
    criticalFeatureLatticeBoundaryCutoffWeight K cutoff x ≤
      ∑ k ∈ K, criticalFeatureRealBoundaryWeight (k : ℝ) x := by
  rw [criticalFeatureLatticeBoundaryCutoffWeight_eq]
  apply mul_le_of_le_one_right
  · exact Finset.sum_nonneg fun k hk => by
      unfold criticalFeatureRealBoundaryWeight
      positivity
  · exact SchwartzMap.realCompactIntervalCutoff_le_one _ _

open GaloisForLFunctions.HTGeometry

/-- First mass derivative of the Fourier-phase Cauchy pairing. -/
theorem massPairing_cauchyFourierWeight_one (L : ℝ) :
    massPairing (cauchyFourierWeight L) 1 1 =
      (((Real.pi / 2) * (1 + |L|) * Real.exp (-|L|) : ℝ) : ℂ) := by
  let F : ℝ → ℝ := fun Z =>
    Real.pi * (Real.sqrt Z)⁻¹ * Real.exp (-(Real.sqrt Z * |L|))
  have hsqrt : HasDerivAt Real.sqrt (1 / 2) 1 := by
    convert Real.hasDerivAt_sqrt (by norm_num : (1 : ℝ) ≠ 0) using 1
    all_goals norm_num
  have hinv : HasDerivAt (fun Z : ℝ => (Real.sqrt Z)⁻¹) (-1 / 2) 1 := by
    have h := hasDerivAt_inv_sqrt (x := (1 : ℝ)) (by norm_num)
    convert h using 1
    all_goals norm_num
  have hexp : HasDerivAt (fun Z : ℝ => Real.exp (-(Real.sqrt Z * |L|)))
      ((-|L| / 2) * Real.exp (-|L|)) 1 := by
    have hinner : HasDerivAt (fun Z : ℝ => -(Real.sqrt Z * |L|)) (-|L| / 2) 1 := by
      have hmul : HasDerivAt (fun Z : ℝ => (-|L|) * Real.sqrt Z) (-|L| / 2) 1 := by
        have h := hsqrt.const_mul (-|L|)
        refine h.congr_deriv ?_
        ring
      refine hmul.congr_of_eventuallyEq ?_
      filter_upwards with Z
      ring
    have h := hinner.exp
    simpa [mul_comm] using h
  have hF : HasDerivAt F
      (-(Real.pi / 2) * (1 + |L|) * Real.exp (-|L|)) 1 := by
    have h := (hinv.const_mul Real.pi).mul hexp
    change HasDerivAt
      (fun Z : ℝ => Real.pi * (Real.sqrt Z)⁻¹ *
        Real.exp (-(Real.sqrt Z * |L|)))
      (-(Real.pi / 2) * (1 + |L|) * Real.exp (-|L|)) 1
    refine h.congr_deriv ?_
    norm_num
    ring
  have hFc : HasDerivAt (fun Z : ℝ => ((F Z : ℝ) : ℂ))
      ((-(Real.pi / 2) * (1 + |L|) * Real.exp (-|L|) : ℝ) : ℂ) 1 :=
    hF.ofReal_comp
  have heq : massPairing (cauchyFourierWeight L) 0 =ᶠ[𝓝 (1 : ℝ)]
      fun Z : ℝ => ((F Z : ℝ) : ℂ) := by
    filter_upwards [Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)] with Z hZ
    rw [massPairing_cauchyFourierWeight_zero hZ L]
    simp only [F]
    push_cast
    ring
  have hmass := hasDerivAt_massPairing
    (continuous_cauchyFourierWeight L) (cauchyFourierWeight_bound L) 0
    (by norm_num : (0 : ℝ) < 1)
  have hderiv :
      -massPairing (cauchyFourierWeight L) 1 1 =
        ((-(Real.pi / 2) * (1 + |L|) * Real.exp (-|L|) : ℝ) : ℂ) := by
    have heqDeriv := heq.deriv_eq
    rw [hmass.deriv, hFc.deriv] at heqDeriv
    simpa using heqDeriv
  have hneg := congrArg Neg.neg hderiv
  simpa using hneg

open scoped FourierTransform

/-- Exact Fourier transform of the centered real HCF energy profile. -/
theorem fourier_criticalFeatureRealBoundaryWeight_zero (xi : ℝ) :
    𝓕 (fun x : ℝ => (criticalFeatureRealBoundaryWeight 0 x : ℂ)) xi =
      (((2 * Real.pi) * (1 + 2 * Real.pi * |xi|) *
        Real.exp (-(2 * Real.pi * |xi|)) : ℝ) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  change (∫ x : ℝ,
      Complex.exp (((-2 * Real.pi * x * xi : ℝ) : ℂ) * Complex.I) *
        (criticalFeatureRealBoundaryWeight 0 x : ℂ)) = _
  rw [show (∫ x : ℝ,
      Complex.exp (((-2 * Real.pi * x * xi : ℝ) : ℂ) * Complex.I) *
        (criticalFeatureRealBoundaryWeight 0 x : ℂ)) =
      4 * massPairing (cauchyFourierWeight (2 * Real.pi * xi)) 1 1 by
    rw [massPairing, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [criticalFeatureRealBoundaryWeight, cauchyFourierWeight]
    push_cast
    have hD : (1 + x ^ 2) ^ 2 ≠ 0 := by positivity
    field_simp
    ring]
  rw [massPairing_cauchyFourierWeight_one]
  rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  have hreal :
      (4 : ℝ) * ((Real.pi / 2) * (1 + 2 * Real.pi * |xi|) *
        Real.exp (-(2 * Real.pi * |xi|))) =
      (2 * Real.pi) * (1 + 2 * Real.pi * |xi|) *
        Real.exp (-(2 * Real.pi * |xi|)) := by ring
  have hc := congrArg (fun r : ℝ => (r : ℂ)) hreal
  simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using hc

open Asymptotics

set_option maxHeartbeats 50000 in
theorem criticalFeatureRealBoundaryWeight_zero_isBigO :
    (fun x : ℝ => (criticalFeatureRealBoundaryWeight 0 x : ℂ))
      =O[cocompact ℝ] fun x : ℝ => |x| ^ (-(2 : ℝ)) := by
  refine IsBigO.of_bound 4 ?_
  have hev : {x : ℝ | 1 < |x|} ∈ cocompact ℝ := by
    simp only [Filter.mem_cocompact]
    refine ⟨Icc (-1 : ℝ) 1, isCompact_Icc, ?_⟩
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hx
    simp only [Set.mem_setOf_eq, lt_abs]
    rcases hx with hx | hx
    · exact Or.inr (by linarith)
    · exact Or.inl hx
  filter_upwards [hev] with x hx
  have hxabs : 0 < |x| := lt_trans zero_lt_one hx
  have hrpowPos : 0 < |x| ^ (-(2 : ℝ)) := Real.rpow_pos_of_pos hxabs _
  rw [Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (by
    unfold criticalFeatureRealBoundaryWeight
    positivity)]
  rw [Real.norm_eq_abs, abs_of_pos hrpowPos]
  have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero (abs_pos.mp hxabs)
  have hden : x ^ 2 ≤ (1 + x ^ 2) ^ 2 := by
    have hbase0 : 0 ≤ 1 + x ^ 2 := by positivity
    have hbase1 : 1 ≤ 1 + x ^ 2 := by
      nlinarith only [sq_nonneg x]
    calc
      x ^ 2 ≤ 1 + x ^ 2 := by linarith
      _ = 1 * (1 + x ^ 2) := by ring
      _ ≤ (1 + x ^ 2) * (1 + x ^ 2) :=
        mul_le_mul_of_nonneg_right hbase1 hbase0
      _ = (1 + x ^ 2) ^ 2 := by ring
  have hrpow : |x| ^ (-(2 : ℝ)) = (x ^ 2)⁻¹ := by
    calc
      |x| ^ (-(2 : ℝ)) = (|x| ^ (2 : ℝ))⁻¹ :=
        Real.rpow_neg (abs_nonneg x) 2
      _ = (|x| ^ (2 : ℕ))⁻¹ :=
        congrArg Inv.inv (Real.rpow_natCast |x| 2)
      _ = (x ^ 2)⁻¹ := by rw [sq_abs]
  rw [criticalFeatureRealBoundaryWeight, sub_zero, hrpow]
  rw [show 4 * (x ^ 2)⁻¹ = 4 / x ^ 2 by ring]
  exact div_le_div_of_nonneg_left (by norm_num) hx2 hden

set_option maxHeartbeats 100000 in
theorem summable_fourier_criticalFeatureRealBoundaryWeight_zero :
    Summable fun n : ℤ =>
      𝓕 (fun x : ℝ => (criticalFeatureRealBoundaryWeight 0 x : ℂ)) (n : ℝ) := by
  let r : ℝ := Real.exp (-(2 * Real.pi))
  let C : ℝ := (2 * Real.pi) ^ 2
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r < 1 := by
    dsimp [r]
    rw [Real.exp_lt_one_iff]
    nlinarith [Real.pi_pos]
  have hmajorant : Summable fun n : ℤ =>
      C * ((1 + ((n.natAbs : ℕ) : ℝ)) ^ 1 * r ^ n.natAbs) :=
    (GaloisForLFunctions.HTGeometry.summable_int_polyGeom 1 hr0 hr1).mul_left C
  refine Summable.of_norm_bounded hmajorant fun n => ?_
  rw [fourier_criticalFeatureRealBoundaryWeight_zero]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have habs : |(n : ℝ)| = (n.natAbs : ℝ) := by
    symm
    exact natAbs_cast_eq_abs n
  have hexp : Real.exp (-(2 * Real.pi * |(n : ℝ)|)) = r ^ n.natAbs := by
    rw [habs, ← Real.exp_nat_mul]
    congr 1
    ring
  rw [hexp, habs]
  dsimp [C]
  simp only [pow_one]
  have hpi : 1 ≤ 2 * Real.pi := by
    have hp := Real.pi_gt_three
    linarith
  have hn : 0 ≤ (n.natAbs : ℝ) := by positivity
  have hcoef :
      2 * Real.pi * (1 + 2 * Real.pi * (n.natAbs : ℝ)) ≤
        (2 * Real.pi) ^ 2 * (1 + (n.natAbs : ℝ)) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hpi) hn]
  simpa [mul_assoc] using
    mul_le_mul_of_nonneg_right hcoef (pow_nonneg hr0 n.natAbs)

/-- Translated Poisson summation for the HCF profile, with every Fourier mode explicit. -/
theorem poisson_criticalFeatureRealBoundaryWeight (x : ℝ) :
    ∑' n : ℤ, (criticalFeatureRealBoundaryWeight 0 (x + n) : ℂ) =
      ∑' n : ℤ,
        (((2 * Real.pi) * (1 + 2 * Real.pi * |(n : ℝ)|) *
          Real.exp (-(2 * Real.pi * |(n : ℝ)|)) : ℝ) : ℂ) *
            fourier n (x : UnitAddCircle) := by
  have hc : Continuous fun y : ℝ =>
      (criticalFeatureRealBoundaryWeight 0 y : ℂ) :=
    Complex.continuous_ofReal.comp
      (continuous_criticalFeatureRealBoundaryWeight 0)
  have h := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable
    hc one_lt_two criticalFeatureRealBoundaryWeight_zero_isBigO
    summable_fourier_criticalFeatureRealBoundaryWeight_zero x
  simpa only [fourier_criticalFeatureRealBoundaryWeight_zero] using h

def criticalFeatureFourierMode (n : ℤ) : ℝ :=
  (2 * Real.pi) * (1 + 2 * Real.pi * |(n : ℝ)|) *
    Real.exp (-(2 * Real.pi * |(n : ℝ)|))

theorem criticalFeatureFourierMode_nonnegative (n : ℤ) :
    0 ≤ criticalFeatureFourierMode n := by
  unfold criticalFeatureFourierMode
  positivity

theorem summable_criticalFeatureFourierMode :
    Summable criticalFeatureFourierMode := by
  have h := summable_fourier_criticalFeatureRealBoundaryWeight_zero.norm
  refine h.congr fun n => ?_
  rw [fourier_criticalFeatureRealBoundaryWeight_zero,
    Complex.norm_real, Real.norm_eq_abs]
  change |criticalFeatureFourierMode n| = criticalFeatureFourierMode n
  exact abs_of_nonneg (criticalFeatureFourierMode_nonnegative n)

set_option maxHeartbeats 100000 in
theorem summable_criticalFeatureRealBoundaryWeight_lattice (x : ℝ) :
    Summable fun n : ℤ => criticalFeatureRealBoundaryWeight 0 (x + n) := by
  let j : ℤ := nearestInteger x
  have hweight : Summable fun k : ℤ => criticalFeatureQuarticLatticeMajorant j k := by
    have hbase := summable_one_div_one_add_natAbs_rpow (s := (4 : ℝ)) (by norm_num)
    have hshift := hbase.comp_injective (Equiv.subLeft j).injective
    have hshift' : Summable
        (fun k : ℤ => 1 / (1 + (((j - k : ℤ)).natAbs : ℝ)) ^ (4 : ℝ)) := by
      simpa [Function.comp_def] using hshift
    simpa [criticalFeatureQuarticLatticeMajorant, Real.rpow_natCast,
      div_eq_mul_inv] using hshift'.mul_left 1024
  have hmajorant : Summable fun n : ℤ =>
      criticalFeatureQuarticLatticeMajorant j (-n) := by
    exact hweight.comp_injective neg_injective
  refine Summable.of_nonneg_of_le
    (fun n => by unfold criticalFeatureRealBoundaryWeight; positivity)
    (fun n => ?_) hmajorant
  have hle := normSq_criticalFeatureCauchyKernelTest_le_quarticLatticeMajorant
    (-n) (z := (x : ℂ)) (by simp)
  rw [← criticalFeatureRealBoundaryWeight_eq_normSq ((-n : ℤ) : ℝ) x] at hle
  calc
    criticalFeatureRealBoundaryWeight 0 (x + n) =
        criticalFeatureRealBoundaryWeight ((-n : ℤ) : ℝ) x := by
      unfold criticalFeatureRealBoundaryWeight
      push_cast
      congr 2
      ring
    _ ≤ criticalFeatureQuarticLatticeMajorant j (-n) := hle

/-- Absolute Fourier-mode envelope for the full integer HCF lattice. -/
def criticalFeatureFourierLatticeEnvelope : ℝ :=
  ∑' n : ℤ, criticalFeatureFourierMode n

set_option maxHeartbeats 100000 in
/-- Every translated full HCF lattice is bounded by the positive Fourier envelope. -/
theorem tsum_criticalFeatureRealBoundaryWeight_le_fourierEnvelope (x : ℝ) :
    (∑' n : ℤ, criticalFeatureRealBoundaryWeight 0 (x + n)) ≤
      criticalFeatureFourierLatticeEnvelope := by
  let p : ℤ → ℂ := fun n =>
    (criticalFeatureFourierMode n : ℂ) * fourier n (x : UnitAddCircle)
  have hnorm (n : ℤ) : ‖p n‖ = criticalFeatureFourierMode n := by
    change ‖(criticalFeatureFourierMode n : ℂ) *
      fourier n (x : UnitAddCircle)‖ = criticalFeatureFourierMode n
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (criticalFeatureFourierMode_nonnegative n), fourier_apply,
      Circle.norm_coe, mul_one]
  have hnormSummable : Summable fun n => ‖p n‖ :=
    summable_criticalFeatureFourierMode.congr fun n => (hnorm n).symm
  have hnormTsum : ‖∑' n, p n‖ ≤ ∑' n, ‖p n‖ :=
    norm_tsum_le_tsum_norm hnormSummable
  have hphaseBound : ‖∑' n, p n‖ ≤ criticalFeatureFourierLatticeEnvelope := by
    rw [criticalFeatureFourierLatticeEnvelope]
    simpa only [hnorm] using hnormTsum
  have hphysical := summable_criticalFeatureRealBoundaryWeight_lattice x
  have hcoe := Complex.ofRealCLM.map_tsum hphysical
  have hpois :
      (∑' n : ℤ, (criticalFeatureRealBoundaryWeight 0 (x + n) : ℂ)) =
        ∑' n : ℤ, p n := by
    simpa only [p, criticalFeatureFourierMode] using
      poisson_criticalFeatureRealBoundaryWeight x
  have hsumNonneg :
      0 ≤ ∑' n : ℤ, criticalFeatureRealBoundaryWeight 0 (x + n) :=
    tsum_nonneg fun n => by unfold criticalFeatureRealBoundaryWeight; positivity
  calc
    (∑' n : ℤ, criticalFeatureRealBoundaryWeight 0 (x + n)) =
        ‖((∑' n : ℤ, criticalFeatureRealBoundaryWeight 0 (x + n) : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsumNonneg]
    _ = ‖∑' n : ℤ, (criticalFeatureRealBoundaryWeight 0 (x + n) : ℂ)‖ := by
      have hcoenorm := congrArg norm hcoe
      simpa using hcoenorm
    _ = ‖∑' n : ℤ, p n‖ := by rw [hpois]
    _ ≤ criticalFeatureFourierLatticeEnvelope := hphaseBound

set_option maxHeartbeats 200000 in
/-- Closed geometric-series form of the Fourier lattice envelope. -/
theorem criticalFeatureFourierLatticeEnvelope_eq :
    criticalFeatureFourierLatticeEnvelope =
      2 * Real.pi + 4 * Real.pi * Real.exp (-(2 * Real.pi)) *
        ((1 - Real.exp (-(2 * Real.pi)))⁻¹ +
          2 * Real.pi * (1 - Real.exp (-(2 * Real.pi)))⁻¹ ^ 2) := by
  let q : ℝ := Real.exp (-(2 * Real.pi))
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q < 1 := by
    dsimp [q]
    rw [Real.exp_lt_one_iff]
    nlinarith [Real.pi_pos]
  have hqabs : |q| < 1 := by rwa [abs_of_nonneg hq0]
  have hgeom : Summable fun n : ℕ => q ^ n :=
    summable_geometric_of_lt_one hq0 hq1
  have hsucc : Summable fun n : ℕ => ((n : ℝ) + 1) * q ^ n := by
    simpa only [pow_one, add_comm] using
      (GaloisForLFunctions.HTGeometry.summable_nat_polyGeom 1 hq0 hq1)
  have hpos : Summable fun n : ℕ =>
      criticalFeatureFourierMode ((n : ℤ) + 1) := by
    exact summable_criticalFeatureFourierMode.comp_injective (by
      intro a b h
      exact_mod_cast (add_right_cancel h))
  have hneg : Summable fun n : ℕ =>
      criticalFeatureFourierMode (-((n : ℤ) + 1)) := by
    exact summable_criticalFeatureFourierMode.comp_injective (by
      intro a b h
      have h' := neg_injective h
      exact_mod_cast (add_right_cancel h'))
  have hmodePos (n : ℕ) :
      criticalFeatureFourierMode ((n : ℤ) + 1) =
        2 * Real.pi * q *
          (q ^ n + 2 * Real.pi * (((n : ℝ) + 1) * q ^ n)) := by
    have habs : |((((n : ℤ) + 1 : ℤ) : ℝ))| = (n : ℝ) + 1 := by
      push_cast
      rw [abs_of_nonneg]
      positivity
    have hexp : Real.exp (-(2 * Real.pi * ((n : ℝ) + 1))) = q ^ (n + 1) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [criticalFeatureFourierMode, habs, hexp, pow_succ]
    ring
  have hposTsum :
      (∑' n : ℕ, criticalFeatureFourierMode ((n : ℤ) + 1)) =
        2 * Real.pi * q *
          ((1 - q)⁻¹ + 2 * Real.pi * (1 - q)⁻¹ ^ 2) := by
    calc
      (∑' n : ℕ, criticalFeatureFourierMode ((n : ℤ) + 1)) =
          ∑' n : ℕ, 2 * Real.pi * q *
            (q ^ n + 2 * Real.pi * (((n : ℝ) + 1) * q ^ n)) :=
        tsum_congr hmodePos
      _ = 2 * Real.pi * q *
          ∑' n : ℕ, (q ^ n + 2 * Real.pi * (((n : ℝ) + 1) * q ^ n)) := by
        rw [tsum_mul_left]
      _ = 2 * Real.pi * q *
          ((∑' n : ℕ, q ^ n) +
            ∑' n : ℕ, 2 * Real.pi * (((n : ℝ) + 1) * q ^ n)) := by
        rw [hgeom.tsum_add (hsucc.mul_left _)]
      _ = 2 * Real.pi * q *
          ((1 - q)⁻¹ + 2 * Real.pi * (1 - q)⁻¹ ^ 2) := by
        rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hqabs,
          tsum_natSucc_mul_pow_eq_inv_sq hqabs]
  have hnegTsum :
      (∑' n : ℕ, criticalFeatureFourierMode (-((n : ℤ) + 1))) =
        ∑' n : ℕ, criticalFeatureFourierMode ((n : ℤ) + 1) := by
    apply tsum_congr
    intro n
    unfold criticalFeatureFourierMode
    rw [Int.cast_neg, abs_neg]
  have hsplit := tsum_of_add_one_of_neg_add_one hpos hneg
  rw [criticalFeatureFourierLatticeEnvelope, hsplit, hposTsum,
    hnegTsum, hposTsum]
  change
    2 * Real.pi * q * ((1 - q)⁻¹ + 2 * Real.pi * (1 - q)⁻¹ ^ 2) +
      criticalFeatureFourierMode 0 +
      2 * Real.pi * q * ((1 - q)⁻¹ + 2 * Real.pi * (1 - q)⁻¹ ^ 2) = _
  rw [criticalFeatureFourierMode]
  norm_num
  dsimp [q]
  ring

set_option maxHeartbeats 100000 in
/-- The entire nonzero-frequency charge lies below `37/200`.  This is the quantitative gain hidden
by the earlier quartic majorant: after removing the zero Fourier mode `2π`, the remaining HCF
height-lattice ripple is already below the direct-three-center endpoint constant `21/100`. -/
theorem criticalFeatureFourierLatticeEnvelope_sub_two_pi_le_thirtySeven_twoHundred :
    criticalFeatureFourierLatticeEnvelope - 2 * Real.pi ≤ (37 : ℝ) / 200 := by
  rw [criticalFeatureFourierLatticeEnvelope_eq]
  let q : ℝ := Real.exp (-(2 * Real.pi))
  rw [show Real.exp (-(2 * Real.pi)) = q by rfl]
  ring_nf
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq : q ≤ (1 : ℝ) / 500 := by
    simpa [q] using (exp_neg_two_pi_lt_one_div_fiveHundred).le
  have hdenPos : 0 < 1 - q := by linarith
  have hinv0 : 0 ≤ (1 - q)⁻¹ := inv_nonneg.mpr hdenPos.le
  have hinv : (1 - q)⁻¹ ≤ (500 : ℝ) / 499 := by
    rw [inv_le_comm₀ hdenPos (by norm_num : (0 : ℝ) < 500 / 499)]
    norm_num
    nlinarith
  have hinvSq : (1 - q)⁻¹ ^ 2 ≤ ((500 : ℝ) / 499) ^ 2 := by
    exact (sq_le_sq₀ hinv0 (by norm_num)).2 hinv
  calc
    Real.pi * q * (1 - q)⁻¹ * 4 +
        Real.pi ^ 2 * q * (1 - q)⁻¹ ^ 2 * 8 ≤
      (31416 / 10000 : ℝ) * ((1 : ℝ) / 500) *
          ((500 : ℝ) / 499) * 4 +
        (31416 / 10000 : ℝ) ^ 2 * ((1 : ℝ) / 500) *
          ((500 : ℝ) / 499) ^ 2 * 8 := by
      gcongr <;> nlinarith [Real.pi_lt_d4]
    _ ≤ (37 : ℝ) / 200 := by norm_num

set_option maxHeartbeats 150000 in
/-- Uniform zero-mode separation for the periodized HCF profile.  The `2π` main mass is exact;
every height-dependent aliasing mode together costs at most `37/200`. -/
theorem abs_tsum_criticalFeatureRealBoundaryWeight_sub_two_pi_le_thirtySeven_twoHundred (x : ℝ) :
    |(∑' n : ℤ, criticalFeatureRealBoundaryWeight 0 (x + n)) -
        2 * Real.pi| ≤ (37 : ℝ) / 200 := by
  let p : ℤ → ℂ := fun n =>
    (criticalFeatureFourierMode n : ℂ) * fourier n (x : UnitAddCircle)
  let c : ℤ → ℂ := fun n => if n = 0 then p 0 else 0
  let r : ℤ → ℂ := fun n => p n - c n
  have hnorm (n : ℤ) : ‖p n‖ = criticalFeatureFourierMode n := by
    change ‖(criticalFeatureFourierMode n : ℂ) *
      fourier n (x : UnitAddCircle)‖ = criticalFeatureFourierMode n
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (criticalFeatureFourierMode_nonnegative n), fourier_apply,
      Circle.norm_coe, mul_one]
  have hpNorm : Summable fun n => ‖p n‖ :=
    summable_criticalFeatureFourierMode.congr fun n => (hnorm n).symm
  have hp : Summable p := summable_norm_iff.mp hpNorm
  have hc : Summable c := by
    exact (hasSum_ite_eq (0 : ℤ) (p 0)).summable
  have hr : Summable r := hp.sub hc
  have hcTsum : ∑' n : ℤ, c n = p 0 := by
    exact tsum_ite_eq (0 : ℤ) (fun _ => p 0)
  have hrTsum : ∑' n : ℤ, r n = (∑' n : ℤ, p n) - p 0 := by
    rw [show (∑' n : ℤ, r n) = (∑' n : ℤ, p n) - ∑' n : ℤ, c n by
      exact hp.tsum_sub hc]
    rw [hcTsum]
  have hnormr (n : ℤ) :
      ‖r n‖ = if n = 0 then 0 else criticalFeatureFourierMode n := by
    by_cases hn : n = 0
    · subst n
      simp [r, c]
    · simp [r, c, hn, hnorm]
  have htailSum :
      (∑' n : ℤ, if n = 0 then 0 else criticalFeatureFourierMode n) =
        criticalFeatureFourierLatticeEnvelope - 2 * Real.pi := by
    let cMode : ℤ → ℝ := fun n =>
      if n = 0 then criticalFeatureFourierMode 0 else 0
    have hcMode : Summable cMode :=
      (hasSum_ite_eq (0 : ℤ) (criticalFeatureFourierMode 0)).summable
    have hcModeTsum : (∑' n : ℤ, cMode n) = criticalFeatureFourierMode 0 :=
      tsum_ite_eq (0 : ℤ) (fun _ => criticalFeatureFourierMode 0)
    have hsub := summable_criticalFeatureFourierMode.tsum_sub hcMode
    rw [hcModeTsum, criticalFeatureFourierMode] at hsub
    norm_num at hsub
    change (∑' n : ℤ, if n = 0 then 0 else criticalFeatureFourierMode n) =
      (∑' n : ℤ, criticalFeatureFourierMode n) - 2 * Real.pi
    rw [← hsub]
    apply tsum_congr
    intro n
    by_cases hn : n = 0
    · simp [hn, cMode]
    · simp [hn, cMode]
  have hnormTsum :
      ‖∑' n : ℤ, r n‖ ≤ criticalFeatureFourierLatticeEnvelope - 2 * Real.pi := by
    calc
      ‖∑' n : ℤ, r n‖ ≤ ∑' n : ℤ, ‖r n‖ :=
        norm_tsum_le_tsum_norm hr.norm
      _ = ∑' n : ℤ,
          if n = 0 then 0 else criticalFeatureFourierMode n :=
        tsum_congr hnormr
      _ = criticalFeatureFourierLatticeEnvelope - 2 * Real.pi := htailSum
  have hphysical := summable_criticalFeatureRealBoundaryWeight_lattice x
  have hcoe := Complex.ofRealCLM.map_tsum hphysical
  have hpois :
      (∑' n : ℤ, (criticalFeatureRealBoundaryWeight 0 (x + n) : ℂ)) =
        ∑' n : ℤ, p n := by
    simpa only [p, criticalFeatureFourierMode] using
      poisson_criticalFeatureRealBoundaryWeight x
  have hrealToFourier :
      (((∑' n : ℤ, criticalFeatureRealBoundaryWeight 0 (x + n)) : ℝ) : ℂ) =
        ∑' n : ℤ, p n := by
    exact hcoe.trans hpois
  have hpzero : p 0 = ((2 * Real.pi : ℝ) : ℂ) := by
    simp [p, criticalFeatureFourierMode, fourier_apply]
  calc
    |(∑' n : ℤ, criticalFeatureRealBoundaryWeight 0 (x + n)) -
        2 * Real.pi| =
      ‖((((∑' n : ℤ, criticalFeatureRealBoundaryWeight 0 (x + n)) -
        2 * Real.pi : ℝ) : ℂ))‖ := by
          rw [Complex.norm_real, Real.norm_eq_abs]
    _ = ‖(∑' n : ℤ, p n) - p 0‖ := by
      simp only [Complex.ofReal_sub, hrealToFourier, hpzero]
    _ = ‖∑' n : ℤ, r n‖ := by rw [hrTsum]
    _ ≤ criticalFeatureFourierLatticeEnvelope - 2 * Real.pi := hnormTsum
    _ ≤ (37 : ℝ) / 200 :=
      criticalFeatureFourierLatticeEnvelope_sub_two_pi_le_thirtySeven_twoHundred

/-- Coarse total-charge corollary retained for finite-cutoff domination. -/
theorem criticalFeatureFourierLatticeEnvelope_le_nine :
    criticalFeatureFourierLatticeEnvelope ≤ 9 := by
  have htail :=
    criticalFeatureFourierLatticeEnvelope_sub_two_pi_le_thirtySeven_twoHundred
  nlinarith [Real.pi_le_four]

theorem sum_criticalFeatureRealBoundaryWeight_zero_le_nine
    (K : Finset ℤ) (x : ℝ) :
    ∑ n ∈ K, criticalFeatureRealBoundaryWeight 0 (x + n) ≤ 9 := by
  calc
    ∑ n ∈ K, criticalFeatureRealBoundaryWeight 0 (x + n) ≤
        ∑' n : ℤ, criticalFeatureRealBoundaryWeight 0 (x + n) := by
      exact (summable_criticalFeatureRealBoundaryWeight_lattice x).sum_le_tsum K
        (fun n hn => by unfold criticalFeatureRealBoundaryWeight; positivity)
    _ ≤ criticalFeatureFourierLatticeEnvelope :=
      tsum_criticalFeatureRealBoundaryWeight_le_fourierEnvelope x
    _ ≤ 9 := criticalFeatureFourierLatticeEnvelope_le_nine

/-- Uniform charge ceiling for every finite set of integer HCF centers. -/
theorem sum_criticalFeatureRealBoundaryWeight_le_nine
    (K : Finset ℤ) (x : ℝ) :
    ∑ k ∈ K, criticalFeatureRealBoundaryWeight (k : ℝ) x ≤ 9 := by
  have hpoint (k : ℤ) :
      criticalFeatureRealBoundaryWeight (k : ℝ) x =
        criticalFeatureRealBoundaryWeight 0 (x + (-k : ℤ)) := by
    unfold criticalFeatureRealBoundaryWeight
    push_cast
    congr 2
    ring
  rw [Finset.sum_congr rfl (fun k hk => hpoint k)]
  have himage :
      (∑ n ∈ K.image (fun k : ℤ => -k),
          criticalFeatureRealBoundaryWeight 0 (x + n)) =
        ∑ k ∈ K, criticalFeatureRealBoundaryWeight 0 (x + (-k : ℤ)) := by
    exact Finset.sum_image neg_injective.injOn
  rw [← himage]
  exact sum_criticalFeatureRealBoundaryWeight_zero_le_nine
    (K.image fun k : ℤ => -k) x

/-- The fused finite-displacement cutoff weight inherits the same uniform ceiling. -/
theorem criticalFeatureLatticeBoundaryCutoffWeight_le_nine
    (K : Finset ℤ) (cutoff : ℕ) (x : ℝ) :
    criticalFeatureLatticeBoundaryCutoffWeight K cutoff x ≤ 9 :=
  (criticalFeatureLatticeBoundaryCutoffWeight_le_uncut K cutoff x).trans
    (sum_criticalFeatureRealBoundaryWeight_le_nine K x)

end

end RHTower
