import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaCompactFluxEnergy
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaCayleyTools
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaSourceCompressedInverseDeterminant
import GaloisForLFunctions.RHTower.PrimeArchBernsteinExponentialPhase
import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonGrowthRate
import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonFloquetTrichotomy
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

/-!
# Rank-two boundary observation of the theta square Cayley flow

The fixed compact theta-source inverse `B` has nonzero eigenvalues `-alpha⁻¹` at the centered Xi
divisor.  We square, rotate by `-i`, and apply a source-sized Cayley transform.  Its denominator is
unconditionally invertible by a strict operator-norm estimate.  The rank-two pinned boundary map
sees every canonical divisor eigenvector through its nonzero monopole.

The resulting source-only sequence `‖C Uⁿ‖` is subexponential exactly when RH holds.  The proof uses
compactness and Gelfand's formula; it assumes neither spectral simplicity nor completeness.
-/

open Complex Filter MeasureTheory Topology

namespace RHTower.HedenmalmThetaSource

noncomputable section

open GaloisForLFunctions.HTGeometry
open HedenmalmQuantile

private abbrev ThetaH := Lp ℂ 2 unitIntervalMeasure

/-- Rotated square of the fixed compact theta-source inverse. -/
def thetaBoundarySquareGenerator : ThetaH →L[ℂ] ThetaH :=
  (-Complex.I) • (thetaKernelOperator * thetaKernelOperator)

/-- Source-sized Cayley step.  The factor two leaves a strict Neumann margin. -/
def thetaBoundaryCayleyStep : ℝ :=
  (2 * (1 + ‖thetaBoundarySquareGenerator‖))⁻¹

/-- Strictly contractive algebra element entering the Cayley denominator. -/
def thetaBoundaryScaledSquareGenerator : ThetaH →L[ℂ] ThetaH :=
  (thetaBoundaryCayleyStep : ℂ) • thetaBoundarySquareGenerator

/-- Bounded discrete Cayley clock built solely from the theta source. -/
def thetaBoundaryCayleyClock : ThetaH →L[ℂ] ThetaH :=
  (1 + thetaBoundaryScaledSquareGenerator) *
    Ring.inverse (1 - thetaBoundaryScaledSquareGenerator)

/-- Rank-two boundary observation after `n` Cayley steps. -/
def thetaBoundaryCayleyObservation (n : ℕ) : ThetaH →L[ℂ] ThetaH :=
  pinnedBoundaryCLM * thetaBoundaryCayleyClock ^ n

/-- Operator norm of the rank-two observed Cayley orbit. -/
def thetaBoundaryCayleyGrowth (n : ℕ) : ℝ :=
  ‖thetaBoundaryCayleyObservation n‖

/-- Scaled generator eigenvalue attached to one multiplicity-exact Xi copy. -/
def thetaXiBoundaryScaledEigenvalue (q : XiZeroCopy) : ℂ :=
  (thetaBoundaryCayleyStep : ℂ) *
    (-Complex.I * thetaXiReciprocalEigenvalue q ^ 2)

/-- Cayley multiplier of one multiplicity-exact Xi copy. -/
def thetaXiBoundaryCayleyMultiplier (q : XiZeroCopy) : ℂ :=
  (1 + thetaXiBoundaryScaledEigenvalue q) /
    (1 - thetaXiBoundaryScaledEigenvalue q)

theorem thetaBoundaryCayleyStep_pos : 0 < thetaBoundaryCayleyStep := by
  rw [thetaBoundaryCayleyStep]
  positivity

theorem thetaBoundaryCayleyStep_ne_zero : thetaBoundaryCayleyStep ≠ 0 :=
  thetaBoundaryCayleyStep_pos.ne'

/-- The scaled generator lies strictly inside the operator unit ball. -/
theorem norm_thetaBoundaryScaledSquareGenerator_lt_one :
    ‖thetaBoundaryScaledSquareGenerator‖ < 1 := by
  let a : ℝ := ‖thetaBoundarySquareGenerator‖
  have ha : 0 ≤ a := norm_nonneg _
  have hden : 0 < 2 * (1 + a) := by positivity
  have hfrac : a / (2 * (1 + a)) < 1 := by
    rw [div_lt_iff₀ hden]
    nlinarith
  rw [thetaBoundaryScaledSquareGenerator, norm_smul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos thetaBoundaryCayleyStep_pos]
  change thetaBoundaryCayleyStep * a < 1
  simpa [thetaBoundaryCayleyStep, div_eq_mul_inv, mul_comm] using hfrac

/-- An eigenvalue of a bounded operator lies in its spectrum. -/
theorem mem_spectrum_of_eigen {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (T : H →L[ℂ] H) {mu : ℂ} {v : H} (hv : v ≠ 0) (h : T v = mu • v) :
    mu ∈ spectrum ℂ T := by
  rw [spectrum.mem_iff]
  intro hu
  obtain ⟨u, hueq⟩ := hu
  have h0 : (algebraMap ℂ (H →L[ℂ] H) mu - T) v = 0 := by
    simp [Algebra.algebraMap_eq_smul_one, h]
  have hinv : ((↑u⁻¹ : H →L[ℂ] H) * (algebraMap ℂ (H →L[ℂ] H) mu - T)) v = v := by
    rw [← hueq, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      ContinuousLinearMap.one_apply]
  rw [ContinuousLinearMap.mul_apply, h0, map_zero] at hinv
  exact hv hinv.symm

/-- The Cayley denominator is a unit before any spectral information is used. -/
theorem isUnit_thetaBoundaryCayleyDenominator :
    IsUnit (1 - thetaBoundaryScaledSquareGenerator) :=
  isUnit_one_sub_of_norm_lt_one norm_thetaBoundaryScaledSquareGenerator_lt_one

theorem thetaBoundaryCayleyDenominator_mul_inverse :
    (1 - thetaBoundaryScaledSquareGenerator) *
        Ring.inverse (1 - thetaBoundaryScaledSquareGenerator) = 1 :=
  Ring.mul_inverse_cancel _ isUnit_thetaBoundaryCayleyDenominator

/-- The square generator acts on the canonical divisor line by `-i mu²`. -/
theorem thetaBoundarySquareGenerator_thetaXi_eigen (q : XiZeroCopy) :
    thetaBoundarySquareGenerator (thetaXiDivisorEigenvector q) =
      (-Complex.I * thetaXiReciprocalEigenvalue q ^ 2) •
        thetaXiDivisorEigenvector q := by
  rw [thetaBoundarySquareGenerator, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.mul_apply,
    thetaKernelOperator_eq_thetaCompactSourceInverse,
    thetaCompactSourceInverse_sq_thetaXi_eigen, smul_smul]

/-- The scaled square generator has the advertised divisor eigenvalue. -/
theorem thetaBoundaryScaledSquareGenerator_thetaXi_eigen (q : XiZeroCopy) :
    thetaBoundaryScaledSquareGenerator (thetaXiDivisorEigenvector q) =
      thetaXiBoundaryScaledEigenvalue q • thetaXiDivisorEigenvector q := by
  rw [thetaBoundaryScaledSquareGenerator, ContinuousLinearMap.smul_apply,
    thetaBoundarySquareGenerator_thetaXi_eigen, smul_smul]
  rfl

theorem norm_thetaXiBoundaryScaledEigenvalue_lt_one (q : XiZeroCopy) :
    ‖thetaXiBoundaryScaledEigenvalue q‖ < 1 :=
  norm_eigenvalue_lt_one_of_strict_contraction
    norm_thetaBoundaryScaledSquareGenerator_lt_one
    (thetaXiDivisorEigenvector_ne_zero q)
    (thetaBoundaryScaledSquareGenerator_thetaXi_eigen q)

theorem one_sub_thetaXiBoundaryScaledEigenvalue_ne_zero (q : XiZeroCopy) :
    1 - thetaXiBoundaryScaledEigenvalue q ≠ 0 := by
  intro hzero
  have hone : thetaXiBoundaryScaledEigenvalue q = 1 := (sub_eq_zero.mp hzero).symm
  have hlt := norm_thetaXiBoundaryScaledEigenvalue_lt_one q
  rw [hone, norm_one] at hlt
  exact lt_irrefl 1 hlt

/-- The source Cayley clock acts diagonally on every canonical theta divisor mode. -/
theorem thetaBoundaryCayleyClock_thetaXi_eigen (q : XiZeroCopy) :
    thetaBoundaryCayleyClock (thetaXiDivisorEigenvector q) =
      thetaXiBoundaryCayleyMultiplier q • thetaXiDivisorEigenvector q := by
  rw [thetaBoundaryCayleyClock, ContinuousLinearMap.mul_apply,
    ringInverse_one_sub_apply_of_eigen
      isUnit_thetaBoundaryCayleyDenominator
      (thetaXiDivisorEigenvector_ne_zero q)
      (thetaBoundaryScaledSquareGenerator_thetaXi_eigen q)]
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply, map_smul,
    thetaBoundaryScaledSquareGenerator_thetaXi_eigen, smul_smul, ← add_smul]
  simp only [one_smul, thetaXiBoundaryCayleyMultiplier]
  congr 1
  field_simp [one_sub_thetaXiBoundaryScaledEigenvalue_ne_zero q]

/-- Exact vector-valued rank-two observed Cayley mode law. -/
theorem thetaBoundaryCayleyObservation_thetaXi_eigen (q : XiZeroCopy) (n : ℕ) :
    thetaBoundaryCayleyObservation n (thetaXiDivisorEigenvector q) =
      thetaXiBoundaryCayleyMultiplier q ^ n •
        pinnedBoundaryCLM (thetaXiDivisorEigenvector q) := by
  rw [thetaBoundaryCayleyObservation, ContinuousLinearMap.mul_apply,
    pow_apply_of_complex_eigen (thetaBoundaryCayleyClock_thetaXi_eigen q) n,
    map_smul]

/-- Exact norm growth on every observed divisor line. -/
theorem norm_thetaBoundaryCayleyObservation_thetaXi_eigen (q : XiZeroCopy) (n : ℕ) :
    ‖thetaBoundaryCayleyObservation n (thetaXiDivisorEigenvector q)‖ =
      ‖thetaXiBoundaryCayleyMultiplier q‖ ^ n *
        ‖pinnedBoundaryCLM (thetaXiDivisorEigenvector q)‖ := by
  rw [thetaBoundaryCayleyObservation_thetaXi_eigen, norm_smul, norm_pow]

/-! ## Compact Cayley perturbation -/

/-- The rotated square remains compact. -/
theorem isCompactOperator_thetaBoundarySquareGenerator :
    IsCompactOperator thetaBoundarySquareGenerator := by
  rw [thetaBoundarySquareGenerator]
  exact (isCompactOperator_thetaKernelOperator.comp_clm thetaKernelOperator).smul
    (-Complex.I)

/-- The source-scaled square remains compact. -/
theorem isCompactOperator_thetaBoundaryScaledSquareGenerator :
    IsCompactOperator thetaBoundaryScaledSquareGenerator := by
  rw [thetaBoundaryScaledSquareGenerator]
  exact isCompactOperator_thetaBoundarySquareGenerator.smul
    (thetaBoundaryCayleyStep : ℂ)

/-- The Cayley clock differs from the identity by a compact operator. -/
theorem thetaBoundaryCayleyClock_sub_one :
    thetaBoundaryCayleyClock - 1 =
      (thetaBoundaryScaledSquareGenerator + thetaBoundaryScaledSquareGenerator) *
        Ring.inverse (1 - thetaBoundaryScaledSquareGenerator) := by
  calc thetaBoundaryCayleyClock - 1
      = (1 + thetaBoundaryScaledSquareGenerator) *
            Ring.inverse (1 - thetaBoundaryScaledSquareGenerator) -
          (1 - thetaBoundaryScaledSquareGenerator) *
            Ring.inverse (1 - thetaBoundaryScaledSquareGenerator) := by
        rw [thetaBoundaryCayleyClock, thetaBoundaryCayleyDenominator_mul_inverse]
    _ = (thetaBoundaryScaledSquareGenerator + thetaBoundaryScaledSquareGenerator) *
          Ring.inverse (1 - thetaBoundaryScaledSquareGenerator) := by
        noncomm_ring

theorem isCompactOperator_thetaBoundaryCayleyClock_sub_one :
    IsCompactOperator (⇑(thetaBoundaryCayleyClock - 1)) := by
  rw [thetaBoundaryCayleyClock_sub_one]
  exact (isCompactOperator_thetaBoundaryScaledSquareGenerator.add
    isCompactOperator_thetaBoundaryScaledSquareGenerator).comp_clm
    (Ring.inverse (1 - thetaBoundaryScaledSquareGenerator))

/-- A nonzero Cayley eigenline transports through the unit denominator to the corresponding
scaled square eigenline. -/
theorem thetaBoundaryScaledSquareGenerator_eigen_of_cayley_eigen
    {k : ℂ} {f : ThetaH} (hf0 : f ≠ 0)
    (hf : thetaBoundaryCayleyClock f = k • f) :
    k ≠ -1 ∧
      ∃ g : ThetaH, g ≠ 0 ∧
        thetaBoundaryScaledSquareGenerator g =
          ((k - 1) / (k + 1)) • g := by
  let D : ThetaH →L[ℂ] ThetaH := 1 - thetaBoundaryScaledSquareGenerator
  let g : ThetaH := Ring.inverse D f
  have hDunit : IsUnit D := by
    simpa only [D] using isUnit_thetaBoundaryCayleyDenominator
  have hDg : D g = f := by
    dsimp only [g]
    rw [← ContinuousLinearMap.mul_apply, Ring.mul_inverse_cancel D hDunit,
      ContinuousLinearMap.one_apply]
  have hg0 : g ≠ 0 := by
    intro hg
    apply hf0
    rw [← hDg, hg, map_zero]
  have hclock :
      (1 + thetaBoundaryScaledSquareGenerator) g = k • D g := by
    rw [hDg]
    simpa only [thetaBoundaryCayleyClock, g, D, ContinuousLinearMap.mul_apply] using hf
  have hlinear :
      g + thetaBoundaryScaledSquareGenerator g =
        k • g - k • thetaBoundaryScaledSquareGenerator g := by
    simpa only [D, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.one_apply, smul_sub] using hclock
  have hkneg : k ≠ -1 := by
    intro hk
    apply hg0
    rw [hk] at hlinear
    linear_combination (norm := module) (2⁻¹ : ℂ) • hlinear
  have hkp : k + 1 ≠ 0 := by
    intro hzero
    apply hkneg
    linear_combination hzero
  have hscale :
      (k + 1) • thetaBoundaryScaledSquareGenerator g = (k - 1) • g := by
    linear_combination (norm := module) hlinear
  refine ⟨hkneg, g, hg0, ?_⟩
  rw [div_eq_mul_inv, mul_comm, mul_smul]
  exact (eq_inv_smul_iff₀ hkp).2 hscale

/-- Under RH every nonzero eigenvalue of the scaled rotated square lies on the imaginary axis. -/
theorem thetaBoundaryScaledSquareGenerator_eigenvalue_re_eq_zero_of_rh
    (hRH : RiemannHypothesis) {x : ℂ} {v : ThetaH}
    (hx0 : x ≠ 0) (hv0 : v ≠ 0)
    (hv : thetaBoundaryScaledSquareGenerator v = x • v) :
    x.re = 0 := by
  let c : ℂ := (thetaBoundaryCayleyStep : ℂ) * (-Complex.I)
  have hc0 : c ≠ 0 := by
    exact mul_ne_zero (by exact_mod_cast thetaBoundaryCayleyStep_ne_zero)
      (neg_ne_zero.mpr Complex.I_ne_zero)
  let y : ℂ := c⁻¹ * x
  have hscaled :
      c • thetaKernelOperator (thetaKernelOperator v) = x • v := by
    simpa only [thetaBoundaryScaledSquareGenerator, thetaBoundarySquareGenerator,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.mul_apply, smul_smul, c] using hv
  have hsq : thetaKernelOperator (thetaKernelOperator v) = y • v := by
    have h := (eq_inv_smul_iff₀ hc0).2 hscaled
    simpa only [y, smul_smul] using h
  have hy0 : y ≠ 0 := by
    exact mul_ne_zero (inv_ne_zero hc0) hx0
  obtain ⟨mu, hmu⟩ : ∃ mu : ℂ, mu ^ 2 = y :=
    IsAlgClosed.exists_pow_nat_eq y (by norm_num : 0 < 2)
  have hmu0 : mu ≠ 0 := by
    intro hzero
    apply hy0
    rw [← hmu, hzero, zero_pow (by norm_num : 2 ≠ 0)]
  have hsqmu : thetaKernelOperator (thetaKernelOperator v) = mu ^ 2 • v := by
    rw [hmu]
    exact hsq
  let w : ThetaH := thetaKernelOperator v + mu • v
  have hmuReal : ∃ t : ℝ, mu = (t : ℂ) := by
    by_cases hw : w = 0
    · have hneg : thetaKernelOperator v = (-mu) • v := by
        dsimp only [w] at hw
        linear_combination (norm := module) hw
      have hspec : -mu ∈ spectrum ℂ thetaKernelOperator :=
        mem_spectrum_of_eigen thetaKernelOperator hv0 hneg
      obtain ⟨t, ht⟩ :=
        (riemannHypothesis_iff_thetaKernelOperator_nonzero_spectrum_real.mp hRH)
          (-mu) hspec (neg_ne_zero.mpr hmu0)
      refine ⟨-t, ?_⟩
      have hnegated := congrArg Neg.neg ht
      simpa using hnegated
    · have hpos : thetaKernelOperator w = mu • w := by
        dsimp only [w]
        rw [map_add, map_smul, hsqmu, smul_add, smul_smul]
        module
      have hspec : mu ∈ spectrum ℂ thetaKernelOperator :=
        mem_spectrum_of_eigen thetaKernelOperator hw hpos
      exact (riemannHypothesis_iff_thetaKernelOperator_nonzero_spectrum_real.mp hRH)
        mu hspec hmu0
  obtain ⟨t, ht⟩ := hmuReal
  have hyReal : y = ((t ^ 2 : ℝ) : ℂ) := by
    rw [← hmu, ht]
    push_cast
    ring
  have hxy : x = c * y := by
    show x = c * (c⁻¹ * x)
    field_simp
  rw [hxy, hyReal]
  dsimp only [c]
  simp [Complex.mul_re, ← Complex.ofReal_pow]

/-! ## RH upper spectral bound -/

/-- Under RH the entire Cayley spectrum lies on the unit circle.  Compactness is used only for
the perturbation `U-I`; no reverse holomorphic spectral-mapping theorem is needed. -/
theorem norm_eq_one_of_mem_spectrum_thetaBoundaryCayleyClock_of_rh
    (hRH : RiemannHypothesis) {k : ℂ}
    (hk : k ∈ spectrum ℂ thetaBoundaryCayleyClock) :
    ‖k‖ = 1 := by
  by_cases hk1 : k = 1
  · rw [hk1, norm_one]
  · have hshift :
        k - 1 ∈ spectrum ℂ (thetaBoundaryCayleyClock - 1) := by
      have h := (spectrum.add_mem_add_iff
        (a := thetaBoundaryCayleyClock) (r := k) (s := (-1 : ℂ))).2 hk
      simpa [sub_eq_add_neg, Algebra.algebraMap_eq_smul_one, add_comm] using h
    have hdelta : k - 1 ≠ 0 := sub_ne_zero.mpr hk1
    have heig : Module.End.HasEigenvalue
        ((thetaBoundaryCayleyClock - 1 : ThetaH →L[ℂ] ThetaH) : Module.End ℂ ThetaH)
        (k - 1) :=
      (isCompactOperator_thetaBoundaryCayleyClock_sub_one.hasEigenvalue_iff_mem_spectrum
        hdelta).2 hshift
    obtain ⟨f, hfvec⟩ := heig.exists_hasEigenvector
    have hUf : thetaBoundaryCayleyClock f = k • f := by
      have hap := hfvec.apply_eq_smul
      simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.one_apply, sub_smul, one_smul] at hap
      exact sub_left_inj.mp hap
    obtain ⟨hkneg, g, hg0, hXg⟩ :=
      thetaBoundaryScaledSquareGenerator_eigen_of_cayley_eigen hfvec.2 hUf
    have hkp : k + 1 ≠ 0 := by
      intro hzero
      apply hkneg
      linear_combination hzero
    have hx0 : (k - 1) / (k + 1) ≠ 0 :=
      div_ne_zero hdelta hkp
    have hxre : ((k - 1) / (k + 1)).re = 0 :=
      thetaBoundaryScaledSquareGenerator_eigenvalue_re_eq_zero_of_rh
        hRH hx0 hg0 hXg
    have hxnorm : ‖(k - 1) / (k + 1)‖ < 1 :=
      norm_eigenvalue_lt_one_of_strict_contraction
        norm_thetaBoundaryScaledSquareGenerator_lt_one hg0 hXg
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

theorem spectralRadius_thetaBoundaryCayleyClock_le_one_of_rh
    (hRH : RiemannHypothesis) :
    spectralRadius ℂ thetaBoundaryCayleyClock ≤ 1 :=
  spectralRadius_le_one_of_forall fun _ hk =>
    le_of_eq (norm_eq_one_of_mem_spectrum_thetaBoundaryCayleyClock_of_rh hRH hk)

/-- RH gives subexponential growth of the rank-two observed Cayley orbit. -/
theorem thetaBoundaryCayleyGrowth_subexponential_of_rh
    (hRH : RiemannHypothesis) :
    SubexponentialAtNatInfinity thetaBoundaryCayleyGrowth := by
  intro r hr
  have hrpos : 0 < r := lt_trans zero_lt_one hr
  have hsr := spectralRadius_thetaBoundaryCayleyClock_le_one_of_rh hRH
  have hfin : spectralRadius ℂ thetaBoundaryCayleyClock ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hsr
  have hsrReal : (spectralRadius ℂ thetaBoundaryCayleyClock).toReal ≤ 1 := by
    have h := (ENNReal.toReal_le_toReal hfin ENNReal.one_ne_top).2 hsr
    simpa using h
  let eps : ℝ := (r - 1) / 2
  let s : ℝ := (spectralRadius ℂ thetaBoundaryCayleyClock).toReal + eps
  have heps : 0 < eps := by
    dsimp only [eps]
    linarith
  have hspos : 0 < s := by
    dsimp only [s]
    have h0 : 0 ≤ (spectralRadius ℂ thetaBoundaryCayleyClock).toReal :=
      ENNReal.toReal_nonneg
    linarith
  have hslt : s < r := by
    dsimp only [s, eps]
    linarith
  have hpow : ∀ᶠ n : ℕ in atTop, ‖thetaBoundaryCayleyClock ^ n‖ ≤ s ^ n := by
    simpa only [s] using
      (eventually_norm_pow_le_of_spectralRadius
        (a := thetaBoundaryCayleyClock) hfin heps)
  have hupper : ∀ᶠ n : ℕ in atTop,
      thetaBoundaryCayleyGrowth n / r ^ n ≤
        ‖pinnedBoundaryCLM‖ * (s / r) ^ n := by
    filter_upwards [hpow] with n hn
    have hobs : thetaBoundaryCayleyGrowth n ≤
        ‖pinnedBoundaryCLM‖ * ‖thetaBoundaryCayleyClock ^ n‖ := by
      rw [thetaBoundaryCayleyGrowth, thetaBoundaryCayleyObservation]
      exact norm_mul_le _ _
    have hscaled : thetaBoundaryCayleyGrowth n ≤
        ‖pinnedBoundaryCLM‖ * s ^ n :=
      hobs.trans (mul_le_mul_of_nonneg_left hn (norm_nonneg _))
    have hrpow : 0 ≤ r ^ n := (pow_pos hrpos n).le
    calc
      thetaBoundaryCayleyGrowth n / r ^ n ≤
          (‖pinnedBoundaryCLM‖ * s ^ n) / r ^ n :=
        div_le_div_of_nonneg_right hscaled hrpow
      _ = ‖pinnedBoundaryCLM‖ * (s / r) ^ n := by
        rw [div_pow]
        ring
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

/-- Real part of the scaled generator eigenvalue is the positive step times reciprocal-square
imaginary part. -/
theorem thetaXiBoundaryScaledEigenvalue_re (q : XiZeroCopy) :
    (thetaXiBoundaryScaledEigenvalue q).re =
      thetaBoundaryCayleyStep * (xiZeroCopyReciprocalSquare q).im := by
  rw [thetaXiBoundaryScaledEigenvalue,
    thetaXiReciprocalEigenvalue_sq_eq_reciprocalSquare]
  simp [Complex.mul_re]

theorem xiZeroCopyReciprocalSquare_boundaryLineConj (q : XiZeroCopy) :
    xiZeroCopyReciprocalSquare (xiZeroCopyLineConjEquiv q) =
      (starRingEnd ℂ) (xiZeroCopyReciprocalSquare q) := by
  simp [xiZeroCopyReciprocalSquare, xiSpectralPoint_lineConj, map_inv₀]

/-- Failure of RH has a divisor copy on the expanding side of the Cayley clock. -/
theorem exists_xiZeroCopyReciprocalSquare_im_pos_of_not_riemannHypothesis
    (hRH : ¬ RiemannHypothesis) :
    ∃ q : XiZeroCopy, 0 < (xiZeroCopyReciprocalSquare q).im := by
  obtain ⟨q, hq⟩ :=
    exists_xiZeroCopyReciprocalSquare_im_ne_zero_of_not_riemannHypothesis hRH
  rcases lt_or_gt_of_ne hq with hneg | hpos
  · refine ⟨xiZeroCopyLineConjEquiv q, ?_⟩
    rw [xiZeroCopyReciprocalSquare_boundaryLineConj, Complex.conj_im]
    exact neg_pos.mpr hneg
  · exact ⟨q, hpos⟩

theorem norm_thetaXiBoundaryCayleyMultiplier_eq_one_of_im_eq_zero
    {q : XiZeroCopy} (hq : (xiZeroCopyReciprocalSquare q).im = 0) :
    ‖thetaXiBoundaryCayleyMultiplier q‖ = 1 := by
  apply norm_cayley_eq_one_of_re_eq_zero
  · rw [thetaXiBoundaryScaledEigenvalue_re, hq, mul_zero]
  · exact one_sub_thetaXiBoundaryScaledEigenvalue_ne_zero q

theorem one_lt_norm_thetaXiBoundaryCayleyMultiplier_of_im_pos
    {q : XiZeroCopy} (hq : 0 < (xiZeroCopyReciprocalSquare q).im) :
    1 < ‖thetaXiBoundaryCayleyMultiplier q‖ := by
  apply one_lt_norm_cayley_of_re_pos
  · rw [thetaXiBoundaryScaledEigenvalue_re]
    exact mul_pos thetaBoundaryCayleyStep_pos hq
  · exact one_sub_thetaXiBoundaryScaledEigenvalue_ne_zero q

/-- One expanding observed divisor mode rules out subexponential operator growth. -/
theorem not_thetaBoundaryCayleyGrowth_subexponential_of_expanding_mode
    {q : XiZeroCopy}
    (hq : 1 < ‖thetaXiBoundaryCayleyMultiplier q‖) :
    ¬ SubexponentialAtNatInfinity thetaBoundaryCayleyGrowth := by
  intro hsub
  let a : ℝ := ‖thetaXiBoundaryCayleyMultiplier q‖
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
  have hlower (n : ℕ) : d ≤ thetaBoundaryCayleyGrowth n / a ^ n := by
    have hop := (thetaBoundaryCayleyObservation n).le_opNorm f
    rw [norm_thetaBoundaryCayleyObservation_thetaXi_eigen] at hop
    have hop' : a ^ n * b ≤ thetaBoundaryCayleyGrowth n * ‖f‖ := by
      simpa only [a, b, f, thetaBoundaryCayleyGrowth] using hop
    have hmul : d * a ^ n * ‖f‖ ≤ thetaBoundaryCayleyGrowth n * ‖f‖ := by
      calc
        d * a ^ n * ‖f‖ = a ^ n * b := by
          dsimp only [d]
          field_simp
        _ ≤ thetaBoundaryCayleyGrowth n * ‖f‖ := hop'
    have hbase : d * a ^ n ≤ thetaBoundaryCayleyGrowth n :=
      le_of_mul_le_mul_right hmul hfnorm
    exact (le_div_iff₀ (pow_pos hapos n)).2 hbase
  have hlim := hsub a ha
  have hevent : ∀ᶠ n : ℕ in atTop, thetaBoundaryCayleyGrowth n / a ^ n < d :=
    (tendsto_order.1 hlim).2 d hdpos
  obtain ⟨n, hn⟩ := hevent.exists
  exact (not_lt_of_ge (hlower n)) hn

theorem not_thetaBoundaryCayleyGrowth_subexponential_of_not_rh
    (hRH : ¬ RiemannHypothesis) :
    ¬ SubexponentialAtNatInfinity thetaBoundaryCayleyGrowth := by
  obtain ⟨q, hq⟩ :=
    exists_xiZeroCopyReciprocalSquare_im_pos_of_not_riemannHypothesis hRH
  exact not_thetaBoundaryCayleyGrowth_subexponential_of_expanding_mode
    (one_lt_norm_thetaXiBoundaryCayleyMultiplier_of_im_pos hq)

/-- Exact source-defined Cayley growth criterion for RH. -/
theorem riemannHypothesis_iff_thetaBoundaryCayleyGrowth_subexponential :
    RiemannHypothesis ↔
      SubexponentialAtNatInfinity thetaBoundaryCayleyGrowth := by
  constructor
  · exact thetaBoundaryCayleyGrowth_subexponential_of_rh
  · intro hsub
    by_contra hRH
    exact not_thetaBoundaryCayleyGrowth_subexponential_of_not_rh hRH hsub

end

end RHTower.HedenmalmThetaSource
