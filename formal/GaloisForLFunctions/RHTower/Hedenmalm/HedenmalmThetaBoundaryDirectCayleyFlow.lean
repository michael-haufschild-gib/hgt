import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaCayleyTools
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaMetricCommutator
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaSourceCompressedInverseDeterminant
import GaloisForLFunctions.RHTower.PrimeArchBernsteinExponentialPhase
import GaloisForLFunctions.RHTower.XiWeilPolarization
import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonGrowthRate
import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonFloquetTrichotomy
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

/-!
# Direct Cayley flow of the compact theta source inverse

RH is already equivalent to reality of the nonzero spectrum of the fixed compact source inverse
`B`; squaring it is unnecessary.  This file applies a norm-safe Cayley transform directly to `B`.
The rank-two pinned boundary map observes every divisor eigenline, so subexponential observed
growth is exactly RH.

In the canonical singular theta metric the direct clock has an exact one-in/one-out Green balance.
Unlike the rotated-square clock, its metric defect is the original rank-two boundary form itself.
-/

open Complex Filter MeasureTheory Topology

namespace RHTower.HedenmalmThetaSource

noncomputable section

open GaloisForLFunctions.HTGeometry
open HedenmalmQuantile

private abbrev ThetaH := Lp ℂ 2 unitIntervalMeasure

/-- Norm-safe step for the direct source Cayley transform. -/
def thetaBoundaryDirectCayleyStep : ℝ :=
  (4 * (1 + ‖thetaKernelOperator‖))⁻¹

/-- Imaginary rotation of the compact source inverse. -/
def thetaBoundaryDirectScaledGenerator : ThetaH →L[ℂ] ThetaH :=
  (Complex.I * thetaBoundaryDirectCayleyStep) • thetaKernelOperator

/-- Direct bounded Cayley clock of the fixed theta source inverse. -/
def thetaBoundaryDirectCayleyClock : ThetaH →L[ℂ] ThetaH :=
  (1 + thetaBoundaryDirectScaledGenerator) *
    Ring.inverse (1 - thetaBoundaryDirectScaledGenerator)

/-- Rank-two observation after `n` direct Cayley steps. -/
def thetaBoundaryDirectCayleyObservation (n : ℕ) : ThetaH →L[ℂ] ThetaH :=
  pinnedBoundaryCLM * thetaBoundaryDirectCayleyClock ^ n

/-- Norm of the direct observed orbit. -/
def thetaBoundaryDirectCayleyGrowth (n : ℕ) : ℝ :=
  ‖thetaBoundaryDirectCayleyObservation n‖

/-- Direct scaled eigenvalue on one canonical Xi divisor line. -/
def thetaXiBoundaryDirectScaledEigenvalue (q : XiZeroCopy) : ℂ :=
  (Complex.I * thetaBoundaryDirectCayleyStep) * thetaXiReciprocalEigenvalue q

/-- Direct Cayley multiplier on one canonical Xi divisor line. -/
def thetaXiBoundaryDirectCayleyMultiplier (q : XiZeroCopy) : ℂ :=
  (1 + thetaXiBoundaryDirectScaledEigenvalue q) /
    (1 - thetaXiBoundaryDirectScaledEigenvalue q)

theorem thetaBoundaryDirectCayleyStep_pos : 0 < thetaBoundaryDirectCayleyStep := by
  rw [thetaBoundaryDirectCayleyStep]
  positivity

theorem thetaBoundaryDirectCayleyStep_ne_zero : thetaBoundaryDirectCayleyStep ≠ 0 :=
  thetaBoundaryDirectCayleyStep_pos.ne'

theorem norm_thetaBoundaryDirectScaledGenerator_lt_one :
    ‖thetaBoundaryDirectScaledGenerator‖ < 1 := by
  let a : ℝ := ‖thetaKernelOperator‖
  have ha : 0 ≤ a := norm_nonneg _
  have hden : 0 < 4 * (1 + a) := by positivity
  have hfrac : a / (4 * (1 + a)) < 1 := by
    rw [div_lt_iff₀ hden]
    nlinarith
  rw [thetaBoundaryDirectScaledGenerator, norm_smul, norm_mul,
    norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos thetaBoundaryDirectCayleyStep_pos]
  change thetaBoundaryDirectCayleyStep * a < 1
  simpa [thetaBoundaryDirectCayleyStep, div_eq_mul_inv, mul_comm] using hfrac

/-- Direct clock lies strictly inside complex-resolvent endpoint-decay strip. -/
theorem thetaBoundaryDirectCayleyStep_lt_one_half :
    thetaBoundaryDirectCayleyStep < 1 / 2 := by
  rw [thetaBoundaryDirectCayleyStep]
  have hnorm : 0 ≤ ‖thetaKernelOperator‖ := norm_nonneg _
  have hden : 0 < 4 * (1 + ‖thetaKernelOperator‖) := by positivity
  rw [inv_lt_iff_one_lt_mul₀' hden]
  nlinarith

theorem isUnit_thetaBoundaryDirectCayleyDenominator :
    IsUnit (1 - thetaBoundaryDirectScaledGenerator) :=
  isUnit_one_sub_of_norm_lt_one norm_thetaBoundaryDirectScaledGenerator_lt_one

theorem thetaBoundaryDirectScaledGenerator_thetaXi_eigen (q : XiZeroCopy) :
    thetaBoundaryDirectScaledGenerator (thetaXiDivisorEigenvector q) =
      thetaXiBoundaryDirectScaledEigenvalue q • thetaXiDivisorEigenvector q := by
  rw [thetaBoundaryDirectScaledGenerator, ContinuousLinearMap.smul_apply,
    thetaKernelOperator_eq_thetaCompactSourceInverse,
    thetaCompactSourceInverse_thetaXi_eigen, smul_smul]
  rfl

theorem norm_thetaXiBoundaryDirectScaledEigenvalue_lt_one (q : XiZeroCopy) :
    ‖thetaXiBoundaryDirectScaledEigenvalue q‖ < 1 :=
  norm_eigenvalue_lt_one_of_strict_contraction
    norm_thetaBoundaryDirectScaledGenerator_lt_one
    (thetaXiDivisorEigenvector_ne_zero q)
    (thetaBoundaryDirectScaledGenerator_thetaXi_eigen q)

theorem one_sub_thetaXiBoundaryDirectScaledEigenvalue_ne_zero (q : XiZeroCopy) :
    1 - thetaXiBoundaryDirectScaledEigenvalue q ≠ 0 := by
  intro hzero
  have hone : thetaXiBoundaryDirectScaledEigenvalue q = 1 := (sub_eq_zero.mp hzero).symm
  have hlt := norm_thetaXiBoundaryDirectScaledEigenvalue_lt_one q
  rw [hone, norm_one] at hlt
  exact (lt_irrefl 1) hlt

theorem thetaBoundaryDirectCayleyClock_thetaXi_eigen (q : XiZeroCopy) :
    thetaBoundaryDirectCayleyClock (thetaXiDivisorEigenvector q) =
      thetaXiBoundaryDirectCayleyMultiplier q • thetaXiDivisorEigenvector q := by
  rw [thetaBoundaryDirectCayleyClock, ContinuousLinearMap.mul_apply,
    ringInverse_one_sub_apply_of_eigen
      isUnit_thetaBoundaryDirectCayleyDenominator
      (thetaXiDivisorEigenvector_ne_zero q)
      (thetaBoundaryDirectScaledGenerator_thetaXi_eigen q)]
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply, map_smul,
    thetaBoundaryDirectScaledGenerator_thetaXi_eigen, smul_smul]
  simp only [one_smul, thetaXiBoundaryDirectCayleyMultiplier]
  rw [← add_smul]
  congr 1
  field_simp [one_sub_thetaXiBoundaryDirectScaledEigenvalue_ne_zero q]

theorem thetaBoundaryDirectCayleyObservation_thetaXi_eigen
    (q : XiZeroCopy) (n : ℕ) :
    thetaBoundaryDirectCayleyObservation n (thetaXiDivisorEigenvector q) =
      thetaXiBoundaryDirectCayleyMultiplier q ^ n •
        pinnedBoundaryCLM (thetaXiDivisorEigenvector q) := by
  rw [thetaBoundaryDirectCayleyObservation, ContinuousLinearMap.mul_apply,
    pow_apply_of_complex_eigen (thetaBoundaryDirectCayleyClock_thetaXi_eigen q) n,
    map_smul]

theorem norm_thetaBoundaryDirectCayleyObservation_thetaXi_eigen
    (q : XiZeroCopy) (n : ℕ) :
    ‖thetaBoundaryDirectCayleyObservation n (thetaXiDivisorEigenvector q)‖ =
      ‖thetaXiBoundaryDirectCayleyMultiplier q‖ ^ n *
        ‖pinnedBoundaryCLM (thetaXiDivisorEigenvector q)‖ := by
  rw [thetaBoundaryDirectCayleyObservation_thetaXi_eigen, norm_smul, norm_pow]

/-! ## Compact Cayley perturbation and spectral transport -/

theorem isCompactOperator_thetaBoundaryDirectScaledGenerator :
    IsCompactOperator thetaBoundaryDirectScaledGenerator := by
  rw [thetaBoundaryDirectScaledGenerator]
  exact IsCompactOperator.smul isCompactOperator_thetaKernelOperator
    (Complex.I * thetaBoundaryDirectCayleyStep : ℂ)

theorem thetaBoundaryDirectCayleyDenominator_mul_inverse :
    (1 - thetaBoundaryDirectScaledGenerator) *
        Ring.inverse (1 - thetaBoundaryDirectScaledGenerator) = 1 :=
  Ring.mul_inverse_cancel _ isUnit_thetaBoundaryDirectCayleyDenominator

theorem thetaBoundaryDirectCayleyClock_sub_one :
    thetaBoundaryDirectCayleyClock - 1 =
      (thetaBoundaryDirectScaledGenerator + thetaBoundaryDirectScaledGenerator) *
        Ring.inverse (1 - thetaBoundaryDirectScaledGenerator) := by
  rw [thetaBoundaryDirectCayleyClock]
  calc
    (1 + thetaBoundaryDirectScaledGenerator) *
          Ring.inverse (1 - thetaBoundaryDirectScaledGenerator) - 1 =
        (1 + thetaBoundaryDirectScaledGenerator) *
            Ring.inverse (1 - thetaBoundaryDirectScaledGenerator) -
          (1 - thetaBoundaryDirectScaledGenerator) *
            Ring.inverse (1 - thetaBoundaryDirectScaledGenerator) := by
              rw [thetaBoundaryDirectCayleyDenominator_mul_inverse]
    _ = (thetaBoundaryDirectScaledGenerator + thetaBoundaryDirectScaledGenerator) *
          Ring.inverse (1 - thetaBoundaryDirectScaledGenerator) := by
            noncomm_ring

theorem isCompactOperator_thetaBoundaryDirectCayleyClock_sub_one :
    IsCompactOperator (thetaBoundaryDirectCayleyClock -
      (1 : ThetaH →L[ℂ] ThetaH)) := by
  rw [thetaBoundaryDirectCayleyClock_sub_one]
  exact (isCompactOperator_thetaBoundaryDirectScaledGenerator.add
    isCompactOperator_thetaBoundaryDirectScaledGenerator).comp_clm _

theorem thetaBoundaryDirectScaledGenerator_eigen_of_cayley_eigen
    {k : ℂ} {f : ThetaH} (hf0 : f ≠ 0)
    (hf : thetaBoundaryDirectCayleyClock f = k • f) :
    k ≠ -1 ∧
      ∃ g : ThetaH, g ≠ 0 ∧
        thetaBoundaryDirectScaledGenerator g = ((k - 1) / (k + 1)) • g := by
  let D : ThetaH →L[ℂ] ThetaH := 1 - thetaBoundaryDirectScaledGenerator
  let g : ThetaH := Ring.inverse D f
  have hDunit : IsUnit D := by
    simpa only [D] using isUnit_thetaBoundaryDirectCayleyDenominator
  have hDg : D g = f := by
    dsimp only [g]
    rw [← ContinuousLinearMap.mul_apply, Ring.mul_inverse_cancel D hDunit,
      ContinuousLinearMap.one_apply]
  have hg0 : g ≠ 0 := by
    intro hg
    apply hf0
    rw [← hDg, hg, map_zero]
  have hclock :
      (1 + thetaBoundaryDirectScaledGenerator) g = k • D g := by
    rw [hDg]
    simpa only [thetaBoundaryDirectCayleyClock, ContinuousLinearMap.mul_apply, g, D] using hf
  have hlinear :
      g + thetaBoundaryDirectScaledGenerator g =
        k • g - k • thetaBoundaryDirectScaledGenerator g := by
    simpa only [D, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.one_apply, smul_sub] using hclock
  have hkneg : k ≠ -1 := by
    intro hk
    apply hg0
    rw [hk] at hlinear
    have hneg : g = -g := by
      apply add_right_cancel (b := thetaBoundaryDirectScaledGenerator g)
      simpa only [neg_smul, one_smul, sub_neg_eq_add] using hlinear
    have hadd : g + g = 0 := eq_neg_iff_add_eq_zero.mp hneg
    have htwo : (2 : ℂ) • g = 0 := by simpa [two_smul] using hadd
    exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  have hkp : k + 1 ≠ 0 := by
    intro hzero
    apply hkneg
    linear_combination hzero
  have hscale :
      (k + 1) • thetaBoundaryDirectScaledGenerator g = (k - 1) • g := by
    rw [add_smul, sub_smul, one_smul]
    apply eq_sub_iff_add_eq.mpr
    have hsum := (eq_sub_iff_add_eq).mp hlinear
    simpa only [one_smul, add_assoc, add_left_comm, add_comm] using hsum
  refine ⟨hkneg, g, hg0, ?_⟩
  rw [div_eq_mul_inv, mul_comm, mul_smul]
  exact (eq_inv_smul_iff₀ hkp).2 hscale

theorem thetaBoundaryDirectScaledGenerator_eigenvalue_re_eq_zero_of_rh
    (hRH : RiemannHypothesis) {x : ℂ} {v : ThetaH}
    (hx0 : x ≠ 0) (hv0 : v ≠ 0)
    (hv : thetaBoundaryDirectScaledGenerator v = x • v) :
    x.re = 0 := by
  let c : ℂ := Complex.I * thetaBoundaryDirectCayleyStep
  have hc0 : c ≠ 0 := by
    exact mul_ne_zero Complex.I_ne_zero
      (by exact_mod_cast thetaBoundaryDirectCayleyStep_ne_zero)
  let y : ℂ := c⁻¹ * x
  have hscaled : c • thetaKernelOperator v = x • v := by
    simpa only [thetaBoundaryDirectScaledGenerator, ContinuousLinearMap.smul_apply, c] using hv
  have hB : thetaKernelOperator v = y • v := by
    have h := (eq_inv_smul_iff₀ hc0).2 hscaled
    simpa only [y, smul_smul] using h
  have hy0 : y ≠ 0 := mul_ne_zero (inv_ne_zero hc0) hx0
  have hevec : Module.End.HasEigenvector
      (thetaKernelOperator : Module.End ℂ ThetaH) y v :=
    ⟨Module.End.mem_eigenspace_iff.mpr hB, hv0⟩
  have hspec : y ∈ spectrum ℂ thetaKernelOperator :=
    (IsCompactOperator.hasEigenvalue_iff_mem_spectrum
      isCompactOperator_thetaKernelOperator hy0).1 hevec.hasUnifEigenvalue
  obtain ⟨t, ht⟩ :=
    (riemannHypothesis_iff_thetaKernelOperator_nonzero_spectrum_real.mp hRH)
      y hspec hy0
  have hxy : x = c * y := by
    change x = c * (c⁻¹ * x)
    rw [← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
  rw [hxy, ht]
  dsimp only [c]
  simp [Complex.mul_re]

theorem norm_eq_one_of_mem_spectrum_thetaBoundaryDirectCayleyClock_of_rh
    (hRH : RiemannHypothesis) {k : ℂ}
    (hk : k ∈ spectrum ℂ thetaBoundaryDirectCayleyClock) :
    ‖k‖ = 1 := by
  by_cases hk1 : k = 1
  · rw [hk1, norm_one]
  · have hshift :
        k - 1 ∈ spectrum ℂ (thetaBoundaryDirectCayleyClock - 1) := by
      have h := (spectrum.add_mem_add_iff
        (a := thetaBoundaryDirectCayleyClock) (r := k) (s := (-1 : ℂ))).2 hk
      simpa [sub_eq_add_neg, Algebra.algebraMap_eq_smul_one, add_comm] using h
    have hdelta : k - 1 ≠ 0 := sub_ne_zero.mpr hk1
    have heig : Module.End.HasEigenvalue
        ((thetaBoundaryDirectCayleyClock - 1 : ThetaH →L[ℂ] ThetaH) : Module.End ℂ ThetaH)
        (k - 1) :=
      (IsCompactOperator.hasEigenvalue_iff_mem_spectrum
        isCompactOperator_thetaBoundaryDirectCayleyClock_sub_one hdelta).2 hshift
    obtain ⟨f, hfvec⟩ := heig.exists_hasEigenvector
    have hUf : thetaBoundaryDirectCayleyClock f = k • f := by
      have hraw := hfvec.apply_eq_smul
      change (thetaBoundaryDirectCayleyClock -
        (1 : ThetaH →L[ℂ] ThetaH)) f = (k - 1) • f at hraw
      apply sub_left_inj.mp
      simpa only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
        sub_smul, one_smul] using hraw
    obtain ⟨hkneg, g, hg0, hXg⟩ :=
      thetaBoundaryDirectScaledGenerator_eigen_of_cayley_eigen hfvec.2 hUf
    have hkp : k + 1 ≠ 0 := by
      intro hzero
      apply hkneg
      linear_combination hzero
    have hx0 : (k - 1) / (k + 1) ≠ 0 := div_ne_zero hdelta hkp
    have hxre : ((k - 1) / (k + 1)).re = 0 :=
      thetaBoundaryDirectScaledGenerator_eigenvalue_re_eq_zero_of_rh
        hRH hx0 hg0 hXg
    have hxnorm : ‖(k - 1) / (k + 1)‖ < 1 :=
      norm_eigenvalue_lt_one_of_strict_contraction
        norm_thetaBoundaryDirectScaledGenerator_lt_one hg0 hXg
    have hxden : 1 - (k - 1) / (k + 1) ≠ 0 := by
      intro hzero
      have hone : (k - 1) / (k + 1) = 1 := (sub_eq_zero.mp hzero).symm
      rw [hone, norm_one] at hxnorm
      exact (lt_irrefl 1) hxnorm
    have hkCayley :
        k = (1 + (k - 1) / (k + 1)) / (1 - (k - 1) / (k + 1)) := by
      field_simp [hkp]
      ring
    rw [hkCayley]
    exact norm_cayley_eq_one_of_re_eq_zero hxre hxden

theorem spectralRadius_thetaBoundaryDirectCayleyClock_le_one_of_rh
    (hRH : RiemannHypothesis) :
    spectralRadius ℂ thetaBoundaryDirectCayleyClock ≤ 1 :=
  spectralRadius_le_one_of_forall fun _ hk =>
    le_of_eq (norm_eq_one_of_mem_spectrum_thetaBoundaryDirectCayleyClock_of_rh hRH hk)

theorem thetaBoundaryDirectCayleyGrowth_subexponential_of_rh
    (hRH : RiemannHypothesis) :
    SubexponentialAtNatInfinity thetaBoundaryDirectCayleyGrowth := by
  intro r hr
  have hrpos : 0 < r := lt_trans zero_lt_one hr
  have hsr := spectralRadius_thetaBoundaryDirectCayleyClock_le_one_of_rh hRH
  have hfin : spectralRadius ℂ thetaBoundaryDirectCayleyClock ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hsr
  have hsrReal : (spectralRadius ℂ thetaBoundaryDirectCayleyClock).toReal ≤ 1 := by
    have h := (ENNReal.toReal_le_toReal hfin ENNReal.one_ne_top).2 hsr
    simpa using h
  let eps : ℝ := (r - 1) / 2
  let s : ℝ := (spectralRadius ℂ thetaBoundaryDirectCayleyClock).toReal + eps
  have heps : 0 < eps := by dsimp only [eps]; linarith
  have hsr0 : 0 ≤ (spectralRadius ℂ thetaBoundaryDirectCayleyClock).toReal :=
    ENNReal.toReal_nonneg
  have hspos : 0 < s := by dsimp only [s]; linarith
  have hslt : s < r := by dsimp only [s, eps]; linarith
  have hpow : ∀ᶠ n : ℕ in atTop, ‖thetaBoundaryDirectCayleyClock ^ n‖ ≤ s ^ n := by
    simpa only [s] using
      (eventually_norm_pow_le_of_spectralRadius
        (a := thetaBoundaryDirectCayleyClock) hfin heps)
  have hupper : ∀ᶠ n : ℕ in atTop,
      thetaBoundaryDirectCayleyGrowth n / r ^ n ≤
        ‖pinnedBoundaryCLM‖ * (s / r) ^ n := by
    filter_upwards [hpow] with n hn
    have hobs : thetaBoundaryDirectCayleyGrowth n ≤
        ‖pinnedBoundaryCLM‖ * ‖thetaBoundaryDirectCayleyClock ^ n‖ := by
      rw [thetaBoundaryDirectCayleyGrowth, thetaBoundaryDirectCayleyObservation]
      exact norm_mul_le _ _
    have hscaled : thetaBoundaryDirectCayleyGrowth n ≤
        ‖pinnedBoundaryCLM‖ * s ^ n :=
      hobs.trans (mul_le_mul_of_nonneg_left hn (norm_nonneg _))
    have hrpow : 0 ≤ r ^ n := (pow_pos hrpos n).le
    calc
      thetaBoundaryDirectCayleyGrowth n / r ^ n ≤
          (‖pinnedBoundaryCLM‖ * s ^ n) / r ^ n :=
        div_le_div_of_nonneg_right hscaled hrpow
      _ = ‖pinnedBoundaryCLM‖ * (s / r) ^ n := by rw [div_pow]; ring
  have hratio0 : 0 ≤ s / r := div_nonneg hspos.le hrpos.le
  have hratio1 : s / r < 1 := (div_lt_one hrpos).2 hslt
  have hmajor : Tendsto (fun n : ℕ => ‖pinnedBoundaryCLM‖ * (s / r) ^ n)
      atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hratio0 hratio1).const_mul
      ‖pinnedBoundaryCLM‖
  exact squeeze_zero'
    (Eventually.of_forall fun n =>
      div_nonneg (norm_nonneg _) (pow_nonneg hrpos.le n))
    hupper hmajor

/-! ## Off-RH expanding direct mode -/

theorem thetaXiReciprocalEigenvalue_lineConj (q : XiZeroCopy) :
    thetaXiReciprocalEigenvalue (xiZeroCopyLineConjEquiv q) =
      (starRingEnd ℂ) (thetaXiReciprocalEigenvalue q) := by
  simp [thetaXiReciprocalEigenvalue, xiSpectralPoint_lineConj, map_inv₀]

theorem thetaXiReciprocalEigenvalue_im_eq_spectral (q : XiZeroCopy) :
    (thetaXiReciprocalEigenvalue q).im =
      (xiSpectralPoint q).im / Complex.normSq (xiSpectralPoint q) := by
  rw [thetaXiReciprocalEigenvalue, Complex.neg_im, Complex.inv_im]
  ring

theorem exists_thetaXiReciprocalEigenvalue_im_neg_of_not_riemannHypothesis
    (hRH : ¬ RiemannHypothesis) :
    ∃ q : XiZeroCopy, (thetaXiReciprocalEigenvalue q).im < 0 := by
  have hex : ∃ q : XiZeroCopy, (xiSpectralPoint q).im ≠ 0 := by
    by_contra hnone
    have hall : ∀ q : XiZeroCopy, (xiSpectralPoint q).im = 0 := by
      intro q
      by_contra hq
      exact hnone ⟨q, hq⟩
    apply hRH
    apply riemannHypothesis_of_xiSpectralPoint_real
    intro q
    refine ⟨(xiSpectralPoint q).re, Complex.ext ?_ ?_⟩
    · simp
    · simpa using hall q
  obtain ⟨q, hq⟩ := hex
  rcases lt_or_gt_of_ne hq with hneg | hpos
  · refine ⟨q, ?_⟩
    rw [thetaXiReciprocalEigenvalue_im_eq_spectral]
    exact div_neg_of_neg_of_pos hneg (Complex.normSq_pos.mpr (xiSpectralPoint_ne_zero q))
  · refine ⟨xiZeroCopyLineConjEquiv q, ?_⟩
    rw [thetaXiReciprocalEigenvalue_lineConj, Complex.conj_im]
    rw [thetaXiReciprocalEigenvalue_im_eq_spectral]
    exact neg_neg_of_pos (div_pos hpos
      (Complex.normSq_pos.mpr (xiSpectralPoint_ne_zero q)))

theorem thetaXiBoundaryDirectScaledEigenvalue_re (q : XiZeroCopy) :
    (thetaXiBoundaryDirectScaledEigenvalue q).re =
      -thetaBoundaryDirectCayleyStep * (thetaXiReciprocalEigenvalue q).im := by
  rw [thetaXiBoundaryDirectScaledEigenvalue]
  simp [Complex.mul_re]

theorem one_lt_norm_thetaXiBoundaryDirectCayleyMultiplier_of_reciprocal_im_neg
    {q : XiZeroCopy} (hq : (thetaXiReciprocalEigenvalue q).im < 0) :
    1 < ‖thetaXiBoundaryDirectCayleyMultiplier q‖ := by
  apply one_lt_norm_cayley_of_re_pos
  · rw [thetaXiBoundaryDirectScaledEigenvalue_re]
    nlinarith [thetaBoundaryDirectCayleyStep_pos]
  · exact one_sub_thetaXiBoundaryDirectScaledEigenvalue_ne_zero q

theorem not_thetaBoundaryDirectCayleyGrowth_subexponential_of_expanding_mode
    {q : XiZeroCopy}
    (hq : 1 < ‖thetaXiBoundaryDirectCayleyMultiplier q‖) :
    ¬ SubexponentialAtNatInfinity thetaBoundaryDirectCayleyGrowth := by
  intro hsub
  let a : ℝ := ‖thetaXiBoundaryDirectCayleyMultiplier q‖
  let f : ThetaH := thetaXiDivisorEigenvector q
  let b : ℝ := ‖pinnedBoundaryCLM f‖
  let d : ℝ := b / ‖f‖
  have ha : 1 < a := by simpa only [a] using hq
  have hapos : 0 < a := lt_trans zero_lt_one ha
  have hf0 : f ≠ 0 := thetaXiDivisorEigenvector_ne_zero q
  have hfnorm : 0 < ‖f‖ := norm_pos_iff.mpr hf0
  have hbpos : 0 < b := by
    exact norm_pos_iff.mpr (pinnedBoundaryCLM_thetaXiDivisorEigenvector_ne_zero q)
  have hdpos : 0 < d := div_pos hbpos hfnorm
  have hlower (n : ℕ) : d ≤ thetaBoundaryDirectCayleyGrowth n / a ^ n := by
    have hop := (thetaBoundaryDirectCayleyObservation n).le_opNorm f
    rw [norm_thetaBoundaryDirectCayleyObservation_thetaXi_eigen] at hop
    have hop' : a ^ n * b ≤ thetaBoundaryDirectCayleyGrowth n * ‖f‖ := by
      simpa only [a, b, f, thetaBoundaryDirectCayleyGrowth] using hop
    have hmul : d * a ^ n * ‖f‖ ≤ thetaBoundaryDirectCayleyGrowth n * ‖f‖ := by
      calc
        d * a ^ n * ‖f‖ = a ^ n * b := by
          dsimp only [d]
          field_simp
        _ ≤ thetaBoundaryDirectCayleyGrowth n * ‖f‖ := hop'
    have hbase : d * a ^ n ≤ thetaBoundaryDirectCayleyGrowth n :=
      le_of_mul_le_mul_right hmul hfnorm
    exact (le_div_iff₀ (pow_pos hapos n)).2 hbase
  have hlim := hsub a ha
  have hevent : ∀ᶠ n : ℕ in atTop, thetaBoundaryDirectCayleyGrowth n / a ^ n < d :=
    (tendsto_order.1 hlim).2 d hdpos
  obtain ⟨n, hn⟩ := hevent.exists
  exact (not_lt_of_ge (hlower n)) hn

theorem not_thetaBoundaryDirectCayleyGrowth_subexponential_of_not_rh
    (hRH : ¬ RiemannHypothesis) :
    ¬ SubexponentialAtNatInfinity thetaBoundaryDirectCayleyGrowth := by
  obtain ⟨q, hq⟩ := exists_thetaXiReciprocalEigenvalue_im_neg_of_not_riemannHypothesis hRH
  exact not_thetaBoundaryDirectCayleyGrowth_subexponential_of_expanding_mode
    (one_lt_norm_thetaXiBoundaryDirectCayleyMultiplier_of_reciprocal_im_neg hq)

/-- Exact direct-Cayley source growth criterion for RH. -/
theorem riemannHypothesis_iff_thetaBoundaryDirectCayleyGrowth_subexponential :
    RiemannHypothesis ↔
      SubexponentialAtNatInfinity thetaBoundaryDirectCayleyGrowth := by
  constructor
  · exact thetaBoundaryDirectCayleyGrowth_subexponential_of_rh
  · intro hsub
    by_contra hRH
    exact not_thetaBoundaryDirectCayleyGrowth_subexponential_of_not_rh hRH hsub

/-! ## Exact singular-metric one-in/one-out balance -/

theorem thetaMetric_directScaledGenerator_greenSource :
    thetaMetricOperator * thetaBoundaryDirectScaledGenerator +
        thetaBoundaryDirectScaledGenerator.adjoint * thetaMetricOperator =
      (-thetaBoundaryDirectCayleyStep : ℂ) • pinnedBoundaryCLM := by
  let B : ThetaH →L[ℂ] ThetaH := thetaKernelOperator
  let G : ThetaH →L[ℂ] ThetaH := thetaMetricOperator
  let C : ThetaH →L[ℂ] ThetaH := pinnedBoundaryCLM
  have hcomm : G * B - B.adjoint * G = Complex.I • C := by
    simpa only [B, G, C] using thetaMetric_commutator_thetaKernelOperator
  rw [thetaBoundaryDirectScaledGenerator]
  change G * ((Complex.I * thetaBoundaryDirectCayleyStep) • B) +
      (((Complex.I * thetaBoundaryDirectCayleyStep) • B).adjoint) * G =
        (-thetaBoundaryDirectCayleyStep : ℂ) • C
  rw [ContinuousLinearMap.adjoint.map_smulₛₗ]
  simp only [map_mul, Complex.conj_ofReal]
  have hI : (starRingEnd ℂ) Complex.I = -Complex.I := by
    simpa using Complex.conj_I
  rw [hI]
  rw [mul_smul_comm, smul_mul_assoc]
  calc
    (Complex.I * thetaBoundaryDirectCayleyStep) • (G * B) +
        (-Complex.I * thetaBoundaryDirectCayleyStep) • (B.adjoint * G) =
        (Complex.I * thetaBoundaryDirectCayleyStep) •
          (G * B - B.adjoint * G) := by module
    _ = (Complex.I * thetaBoundaryDirectCayleyStep) • (Complex.I • C) := by rw [hcomm]
    _ = (-thetaBoundaryDirectCayleyStep : ℂ) • C := by
      rw [smul_smul]
      congr 1
      calc
        (Complex.I * thetaBoundaryDirectCayleyStep) * Complex.I =
            thetaBoundaryDirectCayleyStep * (Complex.I * Complex.I) := by ring
        _ = (-thetaBoundaryDirectCayleyStep : ℂ) := by
          rw [Complex.I_mul_I]
          ring

/-- Direct Cayley clock has exactly the rank-two pinned boundary form as metric defect. -/
theorem thetaBoundaryDirectCayley_metric_green :
    thetaBoundaryDirectCayleyClock.adjoint * thetaMetricOperator *
          thetaBoundaryDirectCayleyClock - thetaMetricOperator =
      (-2 * thetaBoundaryDirectCayleyStep : ℂ) •
        (Ring.inverse (1 - thetaBoundaryDirectScaledGenerator)).adjoint *
          pinnedBoundaryCLM * Ring.inverse (1 - thetaBoundaryDirectScaledGenerator) := by
  let X : ThetaH →L[ℂ] ThetaH := thetaBoundaryDirectScaledGenerator
  let R : ThetaH →L[ℂ] ThetaH := Ring.inverse (1 - X)
  let U : ThetaH →L[ℂ] ThetaH := (1 + X) * R
  let G : ThetaH →L[ℂ] ThetaH := thetaMetricOperator
  let C : ThetaH →L[ℂ] ThetaH := pinnedBoundaryCLM
  have hunit : IsUnit (1 - X) := by
    simpa only [X] using isUnit_thetaBoundaryDirectCayleyDenominator
  have hDR : (1 - X) * R = 1 := by
    simpa only [R] using Ring.mul_inverse_cancel (1 - X) hunit
  have hRadjDadj : R.adjoint * (1 - X.adjoint) = 1 := by
    have h := congrArg ContinuousLinearMap.adjoint hDR
    simpa only [ContinuousLinearMap.mul_def, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint.map_sub, ContinuousLinearMap.adjoint_one,
      ContinuousLinearMap.adjoint_adjoint] using h
  have hUadj : U.adjoint = R.adjoint * (1 + X.adjoint) := by
    simp only [U, ContinuousLinearMap.mul_def, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint.map_add, ContinuousLinearMap.adjoint_one]
  have hGfactor : G = R.adjoint * ((1 - X.adjoint) * G * (1 - X)) * R := by
    calc
      G = 1 * G * 1 := by simp
      _ = (R.adjoint * (1 - X.adjoint)) * G * ((1 - X) * R) := by
        rw [hRadjDadj, hDR]
      _ = R.adjoint * ((1 - X.adjoint) * G * (1 - X)) * R := by
        noncomm_ring
  have hsource : G * X + X.adjoint * G =
      (-thetaBoundaryDirectCayleyStep : ℂ) • C := by
    simpa only [X, G, C] using thetaMetric_directScaledGenerator_greenSource
  change U.adjoint * G * U - G =
      (-2 * thetaBoundaryDirectCayleyStep : ℂ) • R.adjoint * C * R
  rw [hUadj]
  change (R.adjoint * (1 + X.adjoint)) * G * ((1 + X) * R) - G =
      (-2 * thetaBoundaryDirectCayleyStep : ℂ) • R.adjoint * C * R
  nth_rewrite 2 [hGfactor]
  calc
    (R.adjoint * (1 + X.adjoint)) * G * ((1 + X) * R) -
        R.adjoint * ((1 - X.adjoint) * G * (1 - X)) * R =
        R.adjoint *
          (2 • (G * X + X.adjoint * G)) * R := by noncomm_ring
    _ = R.adjoint *
          (2 • ((-thetaBoundaryDirectCayleyStep : ℂ) • C)) * R := by rw [hsource]
    _ = (-2 * thetaBoundaryDirectCayleyStep : ℂ) • R.adjoint * C * R := by
      simp only [smul_smul, smul_mul_assoc, mul_smul_comm]
      module

/-- Exact positive one-in/one-out balance for the singular-metric direct Cayley clock. -/
theorem thetaBoundaryDirectCayley_in_out_balance (f : ThetaH) :
    (inner ℂ
        (thetaMetricOperator (thetaBoundaryDirectCayleyClock f))
        (thetaBoundaryDirectCayleyClock f) : ℂ) +
        (2 * thetaBoundaryDirectCayleyStep : ℂ) *
          (‖pinnedInAmplitude
            (Ring.inverse (1 - thetaBoundaryDirectScaledGenerator) f)‖ : ℂ) ^ 2 =
      (inner ℂ (thetaMetricOperator f) f : ℂ) +
        (2 * thetaBoundaryDirectCayleyStep : ℂ) *
          (‖pinnedOutAmplitude
            (Ring.inverse (1 - thetaBoundaryDirectScaledGenerator) f)‖ : ℂ) ^ 2 := by
  let R : ThetaH →L[ℂ] ThetaH := Ring.inverse (1 - thetaBoundaryDirectScaledGenerator)
  have hgreen := congrArg (fun T : ThetaH →L[ℂ] ThetaH =>
      (inner ℂ (T f) f : ℂ)) thetaBoundaryDirectCayley_metric_green
  have hleft :
      (inner ℂ
        ((thetaBoundaryDirectCayleyClock.adjoint * thetaMetricOperator *
          thetaBoundaryDirectCayleyClock - thetaMetricOperator) f) f : ℂ) =
        (inner ℂ
          (thetaMetricOperator (thetaBoundaryDirectCayleyClock f))
          (thetaBoundaryDirectCayleyClock f) : ℂ) -
        (inner ℂ (thetaMetricOperator f) f : ℂ) := by
    rw [ContinuousLinearMap.sub_apply, inner_sub_left,
      ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.adjoint_inner_left]
  have hright :
      (inner ℂ
        (((-2 * thetaBoundaryDirectCayleyStep : ℂ) • R.adjoint *
          pinnedBoundaryCLM * R) f) f : ℂ) =
        (-2 * thetaBoundaryDirectCayleyStep : ℂ) *
          (inner ℂ (pinnedBoundaryCLM (R f)) (R f) : ℂ) := by
    have hstarTwo : (starRingEnd ℂ) (2 : ℂ) = 2 := by
      simpa using Complex.conj_ofNat 2
    rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.smul_apply, inner_smul_left,
      ContinuousLinearMap.adjoint_inner_left]
    simp only [map_neg, map_mul, Complex.conj_ofReal, hstarTwo]
  rw [hleft, hright, inner_pinnedBoundaryCLM_eq_amplitudes] at hgreen
  dsimp only [R] at hgreen ⊢
  linear_combination hgreen

end

end RHTower.HedenmalmThetaSource
