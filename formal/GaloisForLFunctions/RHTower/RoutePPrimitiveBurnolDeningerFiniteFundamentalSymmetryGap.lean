import GaloisForLFunctions.RHTower.RoutePPrimitiveBurnolDeningerFiniteOrientationWitness
import GaloisForLFunctions.RHTower.XiWardCubicPrimeGammaSecantFundamentalSymmetryGap

/-!
# Route P finite fundamental-symmetry gap

P-G204 constructs finite mixed upper/conjugate-lower secants converging to the four-leg
orientation defect.  This file proves a stronger pre-limit classification.  At every finite
index, the conjugate-lower leg is exactly the critical-line reflection of the upper leg, and the
mixed vector is exactly amplitude times the conjugate of W-H206's lower-sector pair difference.

Consequently every raw finite Weil energy is nonpositive.  For nonzero amplitude, its vanishing
or nonnegativity at any single fixed index is equivalent to RH, while failure of RH makes every
index strictly negative.  The missing positive mass is exactly twice the W-H206
fundamental-symmetry gap, giving an unconditional zero augmented balance.  Thus raw finite-source
passivity cannot be an intermediate proof of RH: any viable completion must retain and dominate
this explicit positive correction rather than erase it.

No RH, zero-location, positivity, simplicity, or closure hypothesis is used.
-/

open Complex

namespace RHTower

noncomputable section

/-- Lower reflected endpoint of the finite Route P upper secant. -/
def routePDeningerLowerReflectedSecantPoint
    (w : DeningerPrimeGammaUpperPoint) (n : ℕ) :
    DeningerPrimeGammaLowerPoint :=
  deningerPrimeGammaPointConjEquiv.symm
    (routePDeningerUpperSecantPoint w n)

theorem routePDeningerLowerReflectedSecantPoint_ne
    (w : DeningerPrimeGammaUpperPoint) (n : ℕ) :
    deningerPrimeGammaPointConjEquiv.symm w ≠
      routePDeningerLowerReflectedSecantPoint w n := by
  intro h
  apply routePDeningerUpperSecantPoint_ne w n
  simpa [routePDeningerLowerReflectedSecantPoint] using
    (congrArg deningerPrimeGammaPointConjEquiv h).symm

/-- The upper finite Route P secant, viewed in the common Xi `ell²` carrier. -/
def routePDeningerFiniteUpperSecantJet
    (A : ℂ) (w : DeningerPrimeGammaUpperPoint) (n : ℕ) :
    lp (fun _ : XiZeroCopy => ℂ) 2 :=
  deningerPrimeGammaUpperToJetHilbert
    (routePDeningerUpperSecantPacket A w n)

@[simp] theorem routePDeningerFiniteUpperSecantJet_apply
    (A : ℂ) (w : DeningerPrimeGammaUpperPoint) (n : ℕ) (q : XiZeroCopy) :
    routePDeningerFiniteUpperSecantJet A w n q =
      deningerPrimeGammaUpperCauchyTest
        (routePDeningerUpperSecantPacket A w n) (xiSpectralPoint q) := by
  exact deningerPrimeGammaUpperToJetHilbert_apply _ _

/-- Pair-difference `ell²` vector of the reflected lower Route P secant. -/
def routePDeningerFiniteLowerPairDifJet
    (w : DeningerPrimeGammaUpperPoint) (n : ℕ) :
    lp (fun _ : XiZeroCopy => ℂ) 2 :=
  let F := xiWardCubicPrimeGammaLowerSecantTest
    (deningerPrimeGammaPointConjEquiv.symm w)
    (routePDeningerLowerReflectedSecantPoint w n)
  ⟨xiWeilPairDif F,
    HilbertSchmidt.memℓp_of_sq
      (xiWeilPairDif_squareSummable
        (xiWardCubicPrimeGammaLowerSecant_squareSummable _ _))⟩

@[simp] theorem routePDeningerFiniteLowerPairDifJet_apply
    (w : DeningerPrimeGammaUpperPoint) (n : ℕ) (q : XiZeroCopy) :
    routePDeningerFiniteLowerPairDifJet w n q =
      xiWeilPairDif
        (xiWardCubicPrimeGammaLowerSecantTest
          (deningerPrimeGammaPointConjEquiv.symm w)
      (routePDeningerLowerReflectedSecantPoint w n)) q := rfl

/-- Conjugating a lower reflected secant gives the upper secant at the conjugate argument. -/
theorem star_xiWardCubicPrimeGammaLowerSecantTest_reflected
    (w0 w1 : DeningerPrimeGammaUpperPoint) (a : ℂ) :
    (starRingEnd ℂ)
        (xiWardCubicPrimeGammaLowerSecantTest
          (deningerPrimeGammaPointConjEquiv.symm w0)
          (deningerPrimeGammaPointConjEquiv.symm w1) a) =
      xiWardCubicPrimeGammaUpperSecantTest w0 w1 ((starRingEnd ℂ) a) := by
  simp [xiWardCubicPrimeGammaLowerSecantTest,
    xiWardCubicPrimeGammaUpperSecantTest, xiWeilCauchyTest,
    deningerPrimeGammaPointConjEquiv]

theorem xiWardCubicPrimeGammaUpperSecantTest_factorization
    {w0 w1 : DeningerPrimeGammaUpperPoint} (hw : w0 ≠ w1)
    {a : ℂ} (ha0 : a ≠ (w0 : ℂ)) (ha1 : a ≠ (w1 : ℂ)) :
    xiWardCubicPrimeGammaUpperSecantTest w0 w1 a =
      (a - (w1 : ℂ))⁻¹ * (a - (w0 : ℂ))⁻¹ := by
  let z0 := deningerPrimeGammaPointConjEquiv.symm w0
  let z1 := deningerPrimeGammaPointConjEquiv.symm w1
  have hz : z0 ≠ z1 := by
    intro h
    apply hw
    simpa [z0, z1] using congrArg deningerPrimeGammaPointConjEquiv h
  have hca0 : (starRingEnd ℂ) a ≠ (z0 : ℂ) := by
    intro h
    apply ha0
    have hc := congrArg (starRingEnd ℂ) h
    simpa [z0, deningerPrimeGammaPointConjEquiv] using hc
  have hca1 : (starRingEnd ℂ) a ≠ (z1 : ℂ) := by
    intro h
    apply ha1
    have hc := congrArg (starRingEnd ℂ) h
    simpa [z1, deningerPrimeGammaPointConjEquiv] using hc
  have href := star_xiWardCubicPrimeGammaLowerSecantTest_reflected
    w0 w1 ((starRingEnd ℂ) a)
  simp only [starRingEnd_self_apply] at href
  rw [← href]
  rw [xiWardCubicPrimeGammaLowerSecantTest_factorization hz hca0 hca1]
  simp [z0, z1, deningerPrimeGammaPointConjEquiv]

/-- The Route P packet realizes amplitude times the normalized upper secant. -/
theorem deningerPrimeGammaUpperCauchyTest_routePDeningerUpperSecantPacket_eq_smul_secant
    (A : ℂ) (w : DeningerPrimeGammaUpperPoint) (n : ℕ) (q : XiZeroCopy) :
    deningerPrimeGammaUpperCauchyTest
        (routePDeningerUpperSecantPacket A w n) (xiSpectralPoint q) =
      A * xiWardCubicPrimeGammaUpperSecantTest w
        (routePDeningerUpperSecantPoint w n) (xiSpectralPoint q) := by
  rw [deningerPrimeGammaUpperCauchyTest_routePDeningerUpperSecantPacket
      A w n (xiSpectralPoint_ne_deningerPrimeGammaUpperPoint q w)
      (xiSpectralPoint_ne_deningerPrimeGammaUpperPoint q
        (routePDeningerUpperSecantPoint w n))]
  have hqw := xiSpectralPoint_ne_deningerPrimeGammaUpperPoint q w
  have hqu := xiSpectralPoint_ne_deningerPrimeGammaUpperPoint q
    (routePDeningerUpperSecantPoint w n)
  rw [xiWardCubicPrimeGammaUpperSecantTest_factorization
    ((routePDeningerUpperSecantPoint_ne w n).symm) hqw hqu]
  rw [xiWeilCauchyTest, xiWeilCauchyTest]
  ring

/-- At every finite secant index, the conjugate-lower leg is exactly the line-reflection of the
upper leg. -/
theorem routePDeningerFiniteConjugateLowerSecant_eq_lineConj
    (A : ℂ) (w : DeningerPrimeGammaUpperPoint) (n : ℕ) :
    (show lp (fun _ : XiZeroCopy => ℂ) 2 from
      star (deningerPrimeGammaLowerToJetHilbert
        (routePDeningerLowerSecantPacket ((starRingEnd ℂ) A)
          (deningerPrimeGammaPointConjEquiv.symm w) n))) =
      xiWeilLineConjLinearIsometry
        (routePDeningerFiniteUpperSecantJet A w n) := by
  simp only [routePDeningerLowerSecantPacket,
    starRingEnd_self_apply, Equiv.apply_symm_apply,
    deningerPrimeGammaLowerToJetHilbert_upperPacketConjToLower,
    xiWeilLineConjLinearIsometry_apply,
    routePDeningerFiniteUpperSecantJet]
  exact star_star _

/-- Every finite P-G204 vector is already the reflection-odd part of one upper source secant. -/
theorem routePDeningerFiniteFourLegOrientationDefectJet_eq_sub_lineConj
    (A : ℂ) (w : DeningerPrimeGammaUpperPoint) (n : ℕ) :
    routePDeningerFiniteFourLegOrientationDefectJet A w n =
      routePDeningerFiniteUpperSecantJet A w n -
      xiWeilLineConjLinearIsometry
        (routePDeningerFiniteUpperSecantJet A w n) := by
  unfold routePDeningerFiniteFourLegOrientationDefectJet
  rw [routePDeningerFiniteConjugateLowerSecant_eq_lineConj]
  rfl

/-- Exact coefficient-faithful bridge from the finite Route P orientation defect to W-H206's
lower-sector pair difference. -/
theorem routePDeningerFiniteFourLegOrientationDefectJet_eq_neg_smul_star_pairDif
    (A : ℂ) (w : DeningerPrimeGammaUpperPoint) (n : ℕ) :
    routePDeningerFiniteFourLegOrientationDefectJet A w n =
      (-A) • star (routePDeningerFiniteLowerPairDifJet w n) := by
  ext q
  rw [routePDeningerFiniteFourLegOrientationDefectJet_eq_sub_lineConj,
    lp.coeFn_sub, Pi.sub_apply, xiWeilLineConjLinearIsometry_apply,
    xiWeilLineConjLp_apply, routePDeningerFiniteUpperSecantJet_apply,
    routePDeningerFiniteUpperSecantJet_apply,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.star_apply,
    routePDeningerFiniteLowerPairDifJet_apply]
  change
    deningerPrimeGammaUpperCauchyTest
          (routePDeningerUpperSecantPacket A w n) (xiSpectralPoint q) -
        deningerPrimeGammaUpperCauchyTest
          (routePDeningerUpperSecantPacket A w n)
            (xiSpectralPoint (xiZeroCopyLineConjEquiv q)) =
      (-A) * (starRingEnd ℂ)
        (xiWeilPairDif
          (xiWardCubicPrimeGammaLowerSecantTest
            (deningerPrimeGammaPointConjEquiv.symm w)
            (routePDeningerLowerReflectedSecantPoint w n)) q)
  rw [deningerPrimeGammaUpperCauchyTest_routePDeningerUpperSecantPacket_eq_smul_secant,
    deningerPrimeGammaUpperCauchyTest_routePDeningerUpperSecantPacket_eq_smul_secant]
  rw [xiWeilPairDif, map_sub]
  simp only [routePDeningerLowerReflectedSecantPoint]
  rw [star_xiWardCubicPrimeGammaLowerSecantTest_reflected,
    star_xiWardCubicPrimeGammaLowerSecantTest_reflected,
    xiSpectralPoint_lineConj, starRingEnd_self_apply]
  ring

/-- Finite Route P orientation defects are exactly anti-fixed, before taking any closure. -/
theorem xiWeilLineConj_finiteFourLegOrientationDefectJet
    (A : ℂ) (w : DeningerPrimeGammaUpperPoint) (n : ℕ) :
    xiWeilLineConjLinearIsometry
        (routePDeningerFiniteFourLegOrientationDefectJet A w n) =
      -routePDeningerFiniteFourLegOrientationDefectJet A w n := by
  rw [routePDeningerFiniteFourLegOrientationDefectJet_eq_sub_lineConj,
    map_sub, xiWeilLineConjLinearIsometry_twice]
  module

/-- Exact finite sign law: raw source energy is the negative Hilbert square at every index. -/
theorem xiWeilHilbertQuadratic_finiteFourLegOrientationDefectJet
    (A : ℂ) (w : DeningerPrimeGammaUpperPoint) (n : ℕ) :
    xiWeilHilbertQuadratic
        (routePDeningerFiniteFourLegOrientationDefectJet A w n) =
      -‖routePDeningerFiniteFourLegOrientationDefectJet A w n‖ ^ (2 : ℕ) := by
  rw [xiWeilHilbertQuadratic,
    xiWeilLineConj_finiteFourLegOrientationDefectJet,
    inner_neg_left, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- Exact W-H206 correction size seen by the finite Route P packet. -/
theorem norm_sq_finiteFourLegOrientationDefectJet_eq_amplitude_pairDifEnergy
    (A : ℂ) (w : DeningerPrimeGammaUpperPoint) (n : ℕ) :
    ‖routePDeningerFiniteFourLegOrientationDefectJet A w n‖ ^ (2 : ℕ) =
      ‖A‖ ^ (2 : ℕ) *
        ∑' q : XiZeroCopy,
          ‖xiWeilPairDif
            (xiWardCubicPrimeGammaLowerSecantTest
              (deningerPrimeGammaPointConjEquiv.symm w)
              (routePDeningerLowerReflectedSecantPoint w n)) q‖ ^ (2 : ℕ) := by
  rw [routePDeningerFiniteFourLegOrientationDefectJet_eq_neg_smul_star_pairDif,
    norm_smul, norm_neg, norm_star]
  have hnorm : ‖routePDeningerFiniteLowerPairDifJet w n‖ ^ (2 : ℕ) =
      ∑' q : XiZeroCopy,
        ‖xiWeilPairDif
          (xiWardCubicPrimeGammaLowerSecantTest
            (deningerPrimeGammaPointConjEquiv.symm w)
            (routePDeningerLowerReflectedSecantPoint w n)) q‖ ^ (2 : ℕ) := by
    rw [HilbertSchmidt.lp_norm_sq_eq]
    rfl
  rw [← hnorm]
  ring

/-- W-H206 positive-metric correction specialized to the reflected lower Route P secant. -/
def routePDeningerFiniteLowerFundamentalSymmetryGap
    (w : DeningerPrimeGammaUpperPoint) (n : ℕ) : ℝ :=
  let F := xiWardCubicPrimeGammaLowerSecantTest
    (deningerPrimeGammaPointConjEquiv.symm w)
    (routePDeningerLowerReflectedSecantPoint w n)
  (xiWeilPolarization F (xiWeilParityFlip F)).re -
    (xiWeilPolarization F F).re

/-- Exact positive correction: one half of the lower reflection-difference energy. -/
theorem routePDeningerFiniteLowerFundamentalSymmetryGap_eq_half_pairDifEnergy
    (w : DeningerPrimeGammaUpperPoint) (n : ℕ) :
    routePDeningerFiniteLowerFundamentalSymmetryGap w n =
      (1 / 2 : ℝ) *
        ∑' q : XiZeroCopy,
          ‖xiWeilPairDif
            (xiWardCubicPrimeGammaLowerSecantTest
              (deningerPrimeGammaPointConjEquiv.symm w)
              (routePDeningerLowerReflectedSecantPoint w n)) q‖ ^ (2 : ℕ) := by
  exact xiWeilParityFlip_energy_sub_weil_eq_half_pairDifEnergy
    (xiWardCubicPrimeGammaLowerSecant_squareSummable _ _)

/-- At every finite index, vanishing of the Route P correction is already exactly RH. -/
theorem routePDeningerFiniteLowerFundamentalSymmetryGap_eq_zero_iff_riemannHypothesis
    (w : DeningerPrimeGammaUpperPoint) (n : ℕ) :
    routePDeningerFiniteLowerFundamentalSymmetryGap w n = 0 ↔
      RiemannHypothesis := by
  simpa [routePDeningerFiniteLowerFundamentalSymmetryGap] using
    (riemannHypothesis_iff_fixedPrimeGammaSecant_fundamentalSymmetryGap_zero
      (deningerPrimeGammaPointConjEquiv.symm w)
      (routePDeningerLowerReflectedSecantPoint w n)
      (routePDeningerLowerReflectedSecantPoint_ne w n)).symm

/-- Exact finite raw-energy formula in W-H206 coordinates. -/
theorem xiWeilHilbertQuadratic_finiteFourLegOrientationDefectJet_eq_neg_amplitude_pairDifEnergy
    (A : ℂ) (w : DeningerPrimeGammaUpperPoint) (n : ℕ) :
    xiWeilHilbertQuadratic
        (routePDeningerFiniteFourLegOrientationDefectJet A w n) =
      -‖A‖ ^ (2 : ℕ) *
        ∑' q : XiZeroCopy,
          ‖xiWeilPairDif
            (xiWardCubicPrimeGammaLowerSecantTest
              (deningerPrimeGammaPointConjEquiv.symm w)
              (routePDeningerLowerReflectedSecantPoint w n)) q‖ ^ (2 : ℕ) := by
  rw [xiWeilHilbertQuadratic_finiteFourLegOrientationDefectJet,
    norm_sq_finiteFourLegOrientationDefectJet_eq_amplitude_pairDifEnergy]
  ring

/-- Raw P-G204 finite source energy is unconditionally nonpositive at every index. -/
theorem xiWeilHilbertQuadratic_finiteFourLegOrientationDefectJet_nonpos
    (A : ℂ) (w : DeningerPrimeGammaUpperPoint) (n : ℕ) :
    xiWeilHilbertQuadratic
        (routePDeningerFiniteFourLegOrientationDefectJet A w n) ≤ 0 := by
  rw [xiWeilHilbertQuadratic_finiteFourLegOrientationDefectJet]
  exact neg_nonpos.mpr (sq_nonneg _)

/-- Every nonzero-amplitude finite Route P orientation defect vanishes exactly under RH. -/
theorem routePDeningerFiniteFourLegOrientationDefectJet_eq_zero_iff_riemannHypothesis
    {A : ℂ} (hA : A ≠ 0) (w : DeningerPrimeGammaUpperPoint) (n : ℕ) :
    routePDeningerFiniteFourLegOrientationDefectJet A w n = 0 ↔
      RiemannHypothesis := by
  let E : ℝ :=
    ∑' q : XiZeroCopy,
      ‖xiWeilPairDif
        (xiWardCubicPrimeGammaLowerSecantTest
          (deningerPrimeGammaPointConjEquiv.symm w)
          (routePDeningerLowerReflectedSecantPoint w n)) q‖ ^ (2 : ℕ)
  have hcriterion : RiemannHypothesis ↔ E = 0 := by
    exact riemannHypothesis_iff_fixedPrimeGammaSecant_pairDifEnergy_zero
      (deningerPrimeGammaPointConjEquiv.symm w)
      (routePDeningerLowerReflectedSecantPoint w n)
      (routePDeningerLowerReflectedSecantPoint_ne w n)
  have hnorm :
      ‖routePDeningerFiniteFourLegOrientationDefectJet A w n‖ ^ (2 : ℕ) =
        ‖A‖ ^ (2 : ℕ) * E := by
    exact norm_sq_finiteFourLegOrientationDefectJet_eq_amplitude_pairDifEnergy A w n
  constructor
  · intro hzero
    have hprod : ‖A‖ ^ (2 : ℕ) * E = 0 := by
      rw [← hnorm, hzero, norm_zero]
      norm_num
    have hnormA : ‖A‖ ^ (2 : ℕ) ≠ 0 :=
      pow_ne_zero 2 (norm_ne_zero_iff.mpr hA)
    exact hcriterion.mpr ((mul_eq_zero.mp hprod).resolve_left hnormA)
  · intro hRH
    apply norm_eq_zero.mp
    have hsq :
        ‖routePDeningerFiniteFourLegOrientationDefectJet A w n‖ ^ (2 : ℕ) = 0 := by
      rw [hnorm, hcriterion.mp hRH, mul_zero]
    nlinarith [norm_nonneg
      (routePDeningerFiniteFourLegOrientationDefectJet A w n)]

/-- At each fixed finite index, raw source nonnegativity is not an available intermediate lemma:
for nonzero amplitude it is exactly RH. -/
theorem xiWeilHilbertQuadratic_finiteFourLegOrientationDefectJet_nonneg_iff_riemannHypothesis
    {A : ℂ} (hA : A ≠ 0) (w : DeningerPrimeGammaUpperPoint) (n : ℕ) :
    0 ≤ xiWeilHilbertQuadratic
        (routePDeningerFiniteFourLegOrientationDefectJet A w n) ↔
      RiemannHypothesis := by
  rw [xiWeilHilbertQuadratic_finiteFourLegOrientationDefectJet]
  constructor
  · intro h
    have hnorm : ‖routePDeningerFiniteFourLegOrientationDefectJet A w n‖ = 0 := by
      nlinarith [norm_nonneg
        (routePDeningerFiniteFourLegOrientationDefectJet A w n)]
    exact
      (routePDeningerFiniteFourLegOrientationDefectJet_eq_zero_iff_riemannHypothesis
        hA w n).mp (norm_eq_zero.mp hnorm)
  · intro hRH
    have hzero :=
      (routePDeningerFiniteFourLegOrientationDefectJet_eq_zero_iff_riemannHypothesis
        hA w n).mpr hRH
    simp [hzero]

/-- Off RH every member of the explicit Route P finite sequence, not merely an eventual member,
has strictly negative raw Weil energy. -/
theorem xiWeilHilbertQuadratic_finiteFourLegOrientationDefectJet_neg_iff_not_riemannHypothesis
    {A : ℂ} (hA : A ≠ 0) (w : DeningerPrimeGammaUpperPoint) (n : ℕ) :
    xiWeilHilbertQuadratic
        (routePDeningerFiniteFourLegOrientationDefectJet A w n) < 0 ↔
      ¬RiemannHypothesis := by
  rw [xiWeilHilbertQuadratic_finiteFourLegOrientationDefectJet]
  constructor
  · intro hneg hRH
    have hzero :=
      (routePDeningerFiniteFourLegOrientationDefectJet_eq_zero_iff_riemannHypothesis
        hA w n).mpr hRH
    simp [hzero] at hneg
  · intro hnot
    have hne : routePDeningerFiniteFourLegOrientationDefectJet A w n ≠ 0 := by
      intro hzero
      exact hnot
        ((routePDeningerFiniteFourLegOrientationDefectJet_eq_zero_iff_riemannHypothesis
          hA w n).mp hzero)
    nlinarith [norm_pos_iff.mpr hne]

/-- **P-G205 exact augmented balance.**  W-H206's positive fundamental-symmetry correction is
precisely the missing mass of the raw finite Route P defect.  The corrected energy is identically
zero, while erasing the correction is RH-equivalent. -/
theorem xiWeilHilbertQuadratic_add_twice_amplitude_fundamentalSymmetryGap_eq_zero
    (A : ℂ) (w : DeningerPrimeGammaUpperPoint) (n : ℕ) :
    xiWeilHilbertQuadratic
          (routePDeningerFiniteFourLegOrientationDefectJet A w n) +
        2 * ‖A‖ ^ (2 : ℕ) *
          routePDeningerFiniteLowerFundamentalSymmetryGap w n = 0 := by
  rw [xiWeilHilbertQuadratic_finiteFourLegOrientationDefectJet_eq_neg_amplitude_pairDifEnergy,
    routePDeningerFiniteLowerFundamentalSymmetryGap_eq_half_pairDifEnergy]
  ring

end

end RHTower
