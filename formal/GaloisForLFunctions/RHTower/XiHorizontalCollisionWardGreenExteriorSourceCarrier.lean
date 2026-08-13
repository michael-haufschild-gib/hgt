import GaloisForLFunctions.RHTower.XiHorizontalCollisionWardGreenCayleyQuantum
import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureExteriorPrimeGammaSource
import GaloisForLFunctions.RHTower.XiSpectralSupportCriterion

/-!
# Ward--Green exterior source carrier for horizontal Xi collision

This module splices three independent corpus mechanisms:

* adjacent real critical features give a literal two-evaluation exterior determinant;
* division by the transverse spectral coordinate removes its quadratic collapse without charging
  critical-line copies;
* the fixed prime labels `2,3` and the source-horizontal Cayley phase dephase the resulting finite
  packet without identifying the two reflection orientations.

The normalized pair of adjacent determinants carries a uniform off-line quantum
`4 * (96 / 145)^2`.  Its coefficients are built from the critical-feature Cauchy tests whose full
polarizations have the explicit prime--Gamma source formula in
`HedenmalmCriticalFeatureExteriorPrimeGammaSource`.

All results are unconditional.  The remaining analytic producer is an absolute bound on the
explicit dephased exterior source carrier, not another zero-side detector.
-/

open Complex Set Metric Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

open HedenmalmThetaSource

/-- Every divisor-indexed centered spectral point lies in the critical feature strip. -/
theorem abs_xiSpectralPointSupport_im_lt_half_exteriorCarrier
    (rho : XiDivisorSupport) :
    |(xiSpectralPointSupport rho).im| < 1 / 2 := by
  rw [xiSpectralPointSupport_im]
  have hstrip := xi_divisor_support_re_mem_open_unit rho
  rw [abs_lt]
  constructor <;> linarith

/-- Fixed nearest-integer reporter center, depending only on height and hence unchanged by
critical-line reflection. -/
def xiExteriorReporterCenter (rho : XiDivisorSupport) : ℝ :=
  ((round (xiSpectralPointSupport rho).re : ℤ) : ℝ)

/-- Forward adjacent exterior coefficient after the forced transverse Green normalization. -/
def xiWardGreenExteriorPlusCoefficient (rho : XiDivisorSupport) : ℂ :=
  let z := xiSpectralPointSupport rho
  let hz : |z.im| < 1 / 2 :=
    abs_xiSpectralPointSupport_im_lt_half_exteriorCarrier rho
  (((z.im)⁻¹ : ℝ) : ℂ) *
    adjacentCriticalFeatureEvaluationDet (xiExteriorReporterCenter rho) z hz

/-- Backward adjacent exterior coefficient.  Both predeclared orientations are retained; no
zero-dependent branch is chosen. -/
def xiWardGreenExteriorMinusCoefficient (rho : XiDivisorSupport) : ℂ :=
  let z := xiSpectralPointSupport rho
  let hz : |z.im| < 1 / 2 :=
    abs_xiSpectralPointSupport_im_lt_half_exteriorCarrier rho
  (((z.im)⁻¹ : ℝ) : ℂ) *
    adjacentCriticalFeatureEvaluationDet (xiExteriorReporterCenter rho - 1) z hz

/-- The forward coefficient is literally the exterior square of two critical-feature Cauchy
tests.  Each of these tests has the explicit absolute-Euler prime--Gamma polarization formula. -/
theorem xiWardGreenExteriorPlusCoefficient_eq_cauchyExterior
    (rho : XiDivisorSupport) :
    let z := xiSpectralPointSupport rho
    let t := xiExteriorReporterCenter rho
    xiWardGreenExteriorPlusCoefficient rho =
      (((z.im)⁻¹ : ℝ) : ℂ) *
        (criticalFeatureCauchyKernelTest t z *
            criticalFeatureCauchyKernelTest (t + 1) ((starRingEnd ℂ) z) -
          criticalFeatureCauchyKernelTest t ((starRingEnd ℂ) z) *
            criticalFeatureCauchyKernelTest (t + 1) z) := by
  dsimp only
  rw [xiWardGreenExteriorPlusCoefficient,
    adjacentCriticalFeatureEvaluationDet]
  rw [criticalEvaluation_realCriticalFeature_eq_hardyCauchySum,
    criticalEvaluation_realCriticalFeature_eq_hardyCauchySum,
    criticalEvaluation_realCriticalFeature_eq_hardyCauchySum,
    criticalEvaluation_realCriticalFeature_eq_hardyCauchySum]
  rfl

/-- The backward coefficient is the second predeclared prime--Gamma Cauchy exterior channel. -/
theorem xiWardGreenExteriorMinusCoefficient_eq_cauchyExterior
    (rho : XiDivisorSupport) :
    let z := xiSpectralPointSupport rho
    let t := xiExteriorReporterCenter rho
    xiWardGreenExteriorMinusCoefficient rho =
      (((z.im)⁻¹ : ℝ) : ℂ) *
        (criticalFeatureCauchyKernelTest (t - 1) z *
            criticalFeatureCauchyKernelTest t ((starRingEnd ℂ) z) -
          criticalFeatureCauchyKernelTest (t - 1) ((starRingEnd ℂ) z) *
            criticalFeatureCauchyKernelTest t z) := by
  dsimp only
  rw [xiWardGreenExteriorMinusCoefficient,
    adjacentCriticalFeatureEvaluationDet]
  simp only [sub_add_cancel]
  rw [criticalEvaluation_realCriticalFeature_eq_hardyCauchySum,
    criticalEvaluation_realCriticalFeature_eq_hardyCauchySum,
    criticalEvaluation_realCriticalFeature_eq_hardyCauchySum,
    criticalEvaluation_realCriticalFeature_eq_hardyCauchySum]
  rfl

/-- Complete two-orientation local exterior energy. -/
def xiWardGreenExteriorLocalEnergy (rho : XiDivisorSupport) : ℝ :=
  Complex.normSq (xiWardGreenExteriorPlusCoefficient rho) +
    Complex.normSq (xiWardGreenExteriorMinusCoefficient rho)

/-- The two normalized determinant coefficients are exactly four times the fixed
three-feature transverse energy. -/
theorem xiWardGreenExteriorLocalEnergy_eq_transverseEnergy
    (rho : XiDivisorSupport) :
    xiWardGreenExteriorLocalEnergy rho =
      4 * orientedAdjacentCriticalFeatureTransverseEnergy
        (xiExteriorReporterCenter rho) (xiSpectralPointSupport rho)
        (abs_xiSpectralPointSupport_im_lt_half_exteriorCarrier rho) := by
  let z := xiSpectralPointSupport rho
  let t := xiExteriorReporterCenter rho
  let hz : |z.im| < 1 / 2 :=
    abs_xiSpectralPointSupport_im_lt_half_exteriorCarrier rho
  rw [xiWardGreenExteriorLocalEnergy, xiWardGreenExteriorPlusCoefficient,
    xiWardGreenExteriorMinusCoefficient]
  change Complex.normSq ((((z.im)⁻¹ : ℝ) : ℂ) *
      adjacentCriticalFeatureEvaluationDet t z hz) +
    Complex.normSq ((((z.im)⁻¹ : ℝ) : ℂ) *
      adjacentCriticalFeatureEvaluationDet (t - 1) z hz) = _
  rw [Complex.normSq_mul, Complex.normSq_mul]
  simp only [Complex.normSq_ofReal]
  rw [← mul_add]
  rw [← four_mul_orientedAdjacentCriticalFeatureExteriorEnergy_eq t z hz]
  rw [orientedAdjacentCriticalFeatureTransverseEnergy]
  ring

/-- Critical-line copies cost exactly zero before any averaging. -/
theorem xiWardGreenExteriorLocalEnergy_eq_zero_of_onLine
    (rho : XiDivisorSupport) (hline : (rho : ℂ).re = 1 / 2) :
    xiWardGreenExteriorLocalEnergy rho = 0 := by
  have hy : (xiSpectralPointSupport rho).im = 0 := by
    exact (xiSpectralPointSupport_im_eq_zero_iff rho).2 hline
  rw [xiWardGreenExteriorLocalEnergy_eq_transverseEnergy]
  rw [orientedAdjacentCriticalFeatureTransverseEnergy_eq_zero_of_im_eq_zero
    (xiExteriorReporterCenter rho)
    (abs_xiSpectralPointSupport_im_lt_half_exteriorCarrier rho) hy]
  ring

/-- Every off-line support point carries a uniform two-orientation exterior quantum. -/
theorem four_mul_transverseQuantum_le_xiWardGreenExteriorLocalEnergy_of_offLine
    (rho : XiDivisorSupport) (hoff : (rho : ℂ).re ≠ 1 / 2) :
    4 * (96 / 145 : ℝ) ^ 2 ≤ xiWardGreenExteriorLocalEnergy rho := by
  have hy : (xiSpectralPointSupport rho).im ≠ 0 := by
    exact fun h => hoff ((xiSpectralPointSupport_im_eq_zero_iff rho).1 h)
  have hquantum := orientedAdjacentCriticalFeatureTransverseEnergy_ge
    (xiExteriorReporterCenter rho)
    (abs_xiSpectralPointSupport_im_lt_half_exteriorCarrier rho)
    (abs_sub_round (xiSpectralPointSupport rho).re) hy
  rw [xiWardGreenExteriorLocalEnergy_eq_transverseEnergy]
  nlinarith

/-- Multiplicity-square local energy of a finite divisor packet. -/
def xiWardGreenExteriorPacketEnergy (S : Finset XiDivisorSupport) : ℝ :=
  ∑ rho ∈ S, (xiSupportMultiplicity rho : ℝ) ^ 2 *
    xiWardGreenExteriorLocalEnergy rho

/-- Packet energy dominates the complete multiplicity-square off-line census. -/
theorem four_mul_transverseQuantum_mul_offLineSquare_le_packetEnergy
    (S : Finset XiDivisorSupport) :
    4 * (96 / 145 : ℝ) ^ 2 *
        (∑ rho ∈ S.filter (fun rho : XiDivisorSupport => (rho : ℂ).re ≠ 1 / 2),
          (xiSupportMultiplicity rho : ℝ) ^ 2) ≤
      xiWardGreenExteriorPacketEnergy S := by
  rw [xiWardGreenExteriorPacketEnergy]
  calc
    4 * (96 / 145 : ℝ) ^ 2 *
          (∑ rho ∈ S.filter (fun rho : XiDivisorSupport => (rho : ℂ).re ≠ 1 / 2),
            (xiSupportMultiplicity rho : ℝ) ^ 2) =
        ∑ rho ∈ S.filter (fun rho : XiDivisorSupport => (rho : ℂ).re ≠ 1 / 2),
          (xiSupportMultiplicity rho : ℝ) ^ 2 *
            (4 * (96 / 145 : ℝ) ^ 2) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro rho hrho
          ring
    _ ≤ ∑ rho ∈ S.filter (fun rho : XiDivisorSupport => (rho : ℂ).re ≠ 1 / 2),
          (xiSupportMultiplicity rho : ℝ) ^ 2 *
            xiWardGreenExteriorLocalEnergy rho := by
          apply Finset.sum_le_sum
          intro rho hrho
          exact mul_le_mul_of_nonneg_left
            (four_mul_transverseQuantum_le_xiWardGreenExteriorLocalEnergy_of_offLine
              rho (Finset.mem_filter.mp hrho).2)
            (sq_nonneg _)
    _ ≤ ∑ rho ∈ S, (xiSupportMultiplicity rho : ℝ) ^ 2 *
          xiWardGreenExteriorLocalEnergy rho := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro rho hrhoS hrhoNotFilter
          have hline : (rho : ℂ).re = 1 / 2 := by
            by_contra hoff
            exact hrhoNotFilter (Finset.mem_filter.mpr ⟨hrhoS, hoff⟩)
          rw [xiWardGreenExteriorLocalEnergy_eq_zero_of_onLine rho hline, mul_zero]

/-- Vanishing of every finite packet energy is already equivalent to RH. -/
theorem riemannHypothesis_iff_forall_xiWardGreenExteriorPacketEnergy_eq_zero :
    RiemannHypothesis ↔
      ∀ S : Finset XiDivisorSupport, xiWardGreenExteriorPacketEnergy S = 0 := by
  constructor
  · intro hRH S
    rw [xiWardGreenExteriorPacketEnergy, Finset.sum_eq_zero]
    intro rho hrho
    rw [xiWardGreenExteriorLocalEnergy_eq_zero_of_onLine rho
      (xi_divisor_support_re_eq_half_of_rh hRH rho), mul_zero]
  · intro henergy
    apply riemannHypothesis_of_xiSpectralPointSupport_im_eq_zero
    intro rho
    have hzero := henergy ({rho} : Finset XiDivisorSupport)
    rw [xiWardGreenExteriorPacketEnergy, Finset.sum_singleton] at hzero
    by_contra hy
    have hoff : (rho : ℂ).re ≠ 1 / 2 := by
      exact fun hline => hy ((xiSpectralPointSupport_im_eq_zero_iff rho).2 hline)
    have hquantum :=
      four_mul_transverseQuantum_le_xiWardGreenExteriorLocalEnergy_of_offLine rho hoff
    have hmpos : 0 < (xiSupportMultiplicity rho : ℝ) ^ 2 := by
      positivity [xiSupportMultiplicity_pos rho]
    have hlocalZero : xiWardGreenExteriorLocalEnergy rho = 0 := by
      exact (mul_eq_zero.mp hzero).resolve_left (ne_of_gt hmpos)
    rw [hlocalZero] at hquantum
    norm_num at hquantum

/-! ## Exact prime/Cayley dephasing -/

/-- Select one of the two fixed adjacent exterior orientations. -/
def xiWardGreenExteriorCoefficient (forward : Bool) (rho : XiDivisorSupport) : ℂ :=
  if forward then xiWardGreenExteriorPlusCoefficient rho
  else xiWardGreenExteriorMinusCoefficient rho

/-- Horizontal Cayley pencil inside one exact ordinate fibre. -/
def xiWardGreenExteriorFiberPencil (forward : Bool)
    (S : Finset XiDivisorSupport) (gamma : ℝ) (c : ℕ) : ℂ :=
  finiteExponentialPencil
    (S.filter (fun rho : XiDivisorSupport => (rho : ℂ).im = gamma))
    (fun rho => ((xiSupportMultiplicity rho : ℕ) : ℂ) *
      xiWardGreenExteriorCoefficient forward rho)
    (fun rho => xiHorizontalSourceCayleyPhase (rho : ℂ)) c

/-- Energy after the fixed prime clocks have separated ordinates at one Cayley depth. -/
def xiWardGreenExteriorResolvedEnergy (forward : Bool)
    (S : Finset XiDivisorSupport) (c : ℕ) : ℝ :=
  ∑ gamma ∈ S.image (fun rho : XiDivisorSupport => (rho : ℂ).im),
    ‖xiWardGreenExteriorFiberPencil forward S gamma c‖ ^ 2

/-- Literal coefficient-faithful exterior source pencil.  Prime labels `2,3`, both factors of
critical-line reflection, analytic multiplicity, adjacent determinant orientation, and Cayley
depth are all present before scalarization. -/
def xiWardGreenExteriorPrimeCayleySourcePencil (forward : Bool)
    (S : Finset XiDivisorSupport) (a b c : ℕ) : ℂ :=
  ∑ rho ∈ S,
    ((xiSupportMultiplicity rho : ℕ) : ℂ) *
      xiWardGreenExteriorCoefficient forward rho *
      (burnolPrimeCharacter 2 (rho : ℂ) *
        burnolPrimeCharacter 2 (lineReflect (rho : ℂ))) ^ a *
      (burnolPrimeCharacter 3 (rho : ℂ) *
        burnolPrimeCharacter 3 (lineReflect (rho : ℂ))) ^ b *
      xiHorizontalSourceCayleyPhase (rho : ℂ) ^ c

def xiWardGreenExteriorPrimeCayleyPhasePencil (forward : Bool)
    (S : Finset XiDivisorSupport) (a b c : ℕ) : ℂ :=
  ∑ rho ∈ S,
    ((xiSupportMultiplicity rho : ℕ) : ℂ) *
      xiWardGreenExteriorCoefficient forward rho *
      xiHorizontalPrimePhase 2 (rho : ℂ).im ^ a *
      xiHorizontalPrimePhase 3 (rho : ℂ).im ^ b *
      xiHorizontalSourceCayleyPhase (rho : ℂ) ^ c

def xiWardGreenExteriorPrimeCayleyGroupedPencil (forward : Bool)
    (S : Finset XiDivisorSupport) (a b c : ℕ) : ℂ :=
  finiteTwoPhasePencil
    (S.image (fun rho : XiDivisorSupport => (rho : ℂ).im))
    (fun gamma => xiWardGreenExteriorFiberPencil forward S gamma c)
    (xiHorizontalPrimePhase 2) (xiHorizontalPrimePhase 3) a b

/-- The displayed prime factors are exactly the two unit ordinate phases. -/
theorem xiWardGreenExteriorPrimeCayleySourcePencil_eq_phasePencil
    (forward : Bool) (S : Finset XiDivisorSupport) (a b c : ℕ) :
    xiWardGreenExteriorPrimeCayleySourcePencil forward S a b c =
      xiWardGreenExteriorPrimeCayleyPhasePencil forward S a b c := by
  apply Finset.sum_congr rfl
  intro rho hrho
  rw [burnolPrimeCharacter_mul_lineReflect_eq_horizontalPrimePhase (by norm_num),
    burnolPrimeCharacter_mul_lineReflect_eq_horizontalPrimePhase (by norm_num)]
  rfl

/-- Exact grouping of the source pencil by ordinate before horizontal Cayley resolution. -/
theorem xiWardGreenExteriorPrimeCayleyPhasePencil_eq_groupedPencil
    (forward : Bool) (S : Finset XiDivisorSupport) (a b c : ℕ) :
    xiWardGreenExteriorPrimeCayleyPhasePencil forward S a b c =
      xiWardGreenExteriorPrimeCayleyGroupedPencil forward S a b c := by
  classical
  let G := S.image (fun rho : XiDivisorSupport => (rho : ℂ).im)
  let A : XiDivisorSupport → ℂ := fun rho =>
    ((xiSupportMultiplicity rho : ℕ) : ℂ) *
      xiWardGreenExteriorCoefficient forward rho
  unfold xiWardGreenExteriorPrimeCayleyPhasePencil
    xiWardGreenExteriorPrimeCayleyGroupedPencil
    xiWardGreenExteriorFiberPencil finiteTwoPhasePencil finiteExponentialPencil
  change (∑ rho ∈ S,
      A rho * xiHorizontalPrimePhase 2 (rho : ℂ).im ^ a *
        xiHorizontalPrimePhase 3 (rho : ℂ).im ^ b *
        xiHorizontalSourceCayleyPhase (rho : ℂ) ^ c) =
    ∑ gamma ∈ G,
      (∑ rho ∈ S.filter (fun rho : XiDivisorSupport => (rho : ℂ).im = gamma),
        A rho * xiHorizontalSourceCayleyPhase (rho : ℂ) ^ c) *
          xiHorizontalPrimePhase 2 gamma ^ a *
          xiHorizontalPrimePhase 3 gamma ^ b
  rw [eq_comm]
  calc
    (∑ gamma ∈ G,
        (∑ rho ∈ S.filter
          (fun rho : XiDivisorSupport => (rho : ℂ).im = gamma),
          A rho * xiHorizontalSourceCayleyPhase (rho : ℂ) ^ c) *
            xiHorizontalPrimePhase 2 gamma ^ a *
            xiHorizontalPrimePhase 3 gamma ^ b) =
      ∑ gamma ∈ G, ∑ rho ∈ S.filter
          (fun rho : XiDivisorSupport => (rho : ℂ).im = gamma),
        (A rho * xiHorizontalSourceCayleyPhase (rho : ℂ) ^ c) *
          xiHorizontalPrimePhase 2 gamma ^ a *
          xiHorizontalPrimePhase 3 gamma ^ b := by
            apply Finset.sum_congr rfl
            intro gamma hgamma
            rw [Finset.sum_mul, Finset.sum_mul]
    _ = ∑ gamma ∈ G, ∑ rho ∈ S.filter
          (fun rho : XiDivisorSupport => (rho : ℂ).im = gamma),
        (A rho * xiHorizontalSourceCayleyPhase (rho : ℂ) ^ c) *
          xiHorizontalPrimePhase 2 (rho : ℂ).im ^ a *
          xiHorizontalPrimePhase 3 (rho : ℂ).im ^ b := by
            apply Finset.sum_congr rfl
            intro gamma hgamma
            apply Finset.sum_congr rfl
            intro rho hrho
            rw [(Finset.mem_filter.mp hrho).2]
    _ = ∑ rho ∈ S,
        (A rho * xiHorizontalSourceCayleyPhase (rho : ℂ) ^ c) *
          xiHorizontalPrimePhase 2 (rho : ℂ).im ^ a *
          xiHorizontalPrimePhase 3 (rho : ℂ).im ^ b := by
            exact Finset.sum_fiberwise_of_maps_to
              (fun rho hrho => Finset.mem_image.mpr ⟨rho, hrho, rfl⟩)
              (fun rho =>
                (A rho * xiHorizontalSourceCayleyPhase (rho : ℂ) ^ c) *
                  xiHorizontalPrimePhase 2 (rho : ℂ).im ^ a *
                  xiHorizontalPrimePhase 3 (rho : ℂ).im ^ b)
    _ = ∑ rho ∈ S,
        A rho * xiHorizontalPrimePhase 2 (rho : ℂ).im ^ a *
          xiHorizontalPrimePhase 3 (rho : ℂ).im ^ b *
          xiHorizontalSourceCayleyPhase (rho : ℂ) ^ c := by
            apply Finset.sum_congr rfl
            intro rho hrho
            ring

theorem xiWardGreenExteriorPrimeCayleySourcePencil_eq_groupedPencil
    (forward : Bool) (S : Finset XiDivisorSupport) (a b c : ℕ) :
    xiWardGreenExteriorPrimeCayleySourcePencil forward S a b c =
      xiWardGreenExteriorPrimeCayleyGroupedPencil forward S a b c := by
  rw [xiWardGreenExteriorPrimeCayleySourcePencil_eq_phasePencil,
    xiWardGreenExteriorPrimeCayleyPhasePencil_eq_groupedPencil]

/-- At fixed Cayley depth, the literal prime source pencil dephases exactly to its complete
ordinate-fibre energy. -/
theorem tendsto_xiWardGreenExteriorPrimeCayleySourcePencil_resolvedEnergy
    (forward : Bool) (S : Finset XiDivisorSupport) (c : ℕ) :
    Tendsto
      (fun N : ℕ => ((N : ℝ)⁻¹ ^ 2) *
        ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N,
          ‖xiWardGreenExteriorPrimeCayleySourcePencil forward S a b c‖ ^ 2)
      atTop (nhds (xiWardGreenExteriorResolvedEnergy forward S c)) := by
  let G := S.image (fun rho : XiDivisorSupport => (rho : ℂ).im)
  have hlim := tendsto_finiteTwoPhasePencil_cesaro_norm_sq G
    (fun gamma => xiWardGreenExteriorFiberPencil forward S gamma c)
    (xiHorizontalPrimePhase 2) (xiHorizontalPrimePhase 3)
    (fun gamma _ => xiHorizontalPrimePhase_norm 2 gamma)
    (fun gamma _ => xiHorizontalPrimePhase_norm 3 gamma)
    xiHorizontalPrimePhase_pair_injective.injOn
  convert hlim using 1
  · funext N
    congr 1
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    rw [xiWardGreenExteriorPrimeCayleySourcePencil_eq_groupedPencil]
    rfl
  · rfl

/-- One orientation's exact multiplicity-square packet energy. -/
def xiWardGreenExteriorOrientationPacketEnergy (forward : Bool)
    (S : Finset XiDivisorSupport) : ℝ :=
  ∑ rho ∈ S,
    ‖((xiSupportMultiplicity rho : ℕ) : ℂ) *
      xiWardGreenExteriorCoefficient forward rho‖ ^ 2

/-- Cayley averaging separates every distinct support point inside one ordinate fibre. -/
theorem tendsto_xiWardGreenExteriorFiberPencil_cesaro_norm_sq
    (forward : Bool) (S : Finset XiDivisorSupport) {gamma : ℝ}
    (_hgamma : gamma ∈ S.image (fun rho : XiDivisorSupport => (rho : ℂ).im)) :
    Tendsto
      (fun M : ℕ => (M : ℝ)⁻¹ * ∑ c ∈ Finset.range M,
        ‖xiWardGreenExteriorFiberPencil forward S gamma c‖ ^ 2)
      atTop
      (nhds (∑ rho ∈ S.filter
        (fun rho : XiDivisorSupport => (rho : ℂ).im = gamma),
        ‖((xiSupportMultiplicity rho : ℕ) : ℂ) *
          xiWardGreenExteriorCoefficient forward rho‖ ^ 2)) := by
  let F := S.filter
    (fun rho : XiDivisorSupport => (rho : ℂ).im = gamma)
  have hinj : Set.InjOn
      (fun rho : XiDivisorSupport =>
        xiHorizontalSourceCayleyPhase (rho : ℂ)) (F : Set XiDivisorSupport) := by
    intro rho hrho sigma hsigma hphase
    apply Subtype.ext
    apply eq_of_im_eq_of_horizontalSourceCayleyPhase_eq
    · exact (Finset.mem_filter.mp hrho).2.trans
        (Finset.mem_filter.mp hsigma).2.symm
    · exact hphase
  have hlim := tendsto_finiteExponentialPencil_cesaro_norm_sq F
    (fun rho => ((xiSupportMultiplicity rho : ℕ) : ℂ) *
      xiWardGreenExteriorCoefficient forward rho)
    (fun rho => xiHorizontalSourceCayleyPhase (rho : ℂ))
    (fun rho _ => xiHorizontalSourceCayleyPhase_norm (rho : ℂ)) hinj
  exact hlim

/-- Averaging one resolved orientation over Cayley depth returns its exact local packet energy. -/
theorem tendsto_xiWardGreenExteriorResolvedEnergy_cesaro
    (forward : Bool) (S : Finset XiDivisorSupport) :
    Tendsto
      (fun M : ℕ => (M : ℝ)⁻¹ * ∑ c ∈ Finset.range M,
        xiWardGreenExteriorResolvedEnergy forward S c)
      atTop (nhds (xiWardGreenExteriorOrientationPacketEnergy forward S)) := by
  let G := S.image (fun rho : XiDivisorSupport => (rho : ℂ).im)
  have hsum := tendsto_finsetSum G
    (fun gamma hgamma =>
      tendsto_xiWardGreenExteriorFiberPencil_cesaro_norm_sq
        forward S hgamma)
  convert hsum using 1
  · funext M
    simp only [xiWardGreenExteriorResolvedEnergy]
    rw [Finset.mul_sum]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
  · apply congrArg nhds
    rw [xiWardGreenExteriorOrientationPacketEnergy]
    symm
    change (∑ gamma ∈ G, ∑ rho ∈ S.filter
      (fun rho : XiDivisorSupport => (rho : ℂ).im = gamma),
        ‖((xiSupportMultiplicity rho : ℕ) : ℂ) *
          xiWardGreenExteriorCoefficient forward rho‖ ^ 2) =
      ∑ rho ∈ S,
        ‖((xiSupportMultiplicity rho : ℕ) : ℂ) *
          xiWardGreenExteriorCoefficient forward rho‖ ^ 2
    exact Finset.sum_fiberwise_of_maps_to
      (fun rho hrho => Finset.mem_image.mpr ⟨rho, hrho, rfl⟩)
      (fun rho => ‖((xiSupportMultiplicity rho : ℕ) : ℂ) *
        xiWardGreenExteriorCoefficient forward rho‖ ^ 2)

/-- The sum of the two orientation energies is the local Ward--Green packet energy. -/
theorem xiWardGreenExteriorOrientationPacketEnergy_add_eq_packetEnergy
    (S : Finset XiDivisorSupport) :
    xiWardGreenExteriorOrientationPacketEnergy true S +
        xiWardGreenExteriorOrientationPacketEnergy false S =
      xiWardGreenExteriorPacketEnergy S := by
  rw [xiWardGreenExteriorOrientationPacketEnergy,
    xiWardGreenExteriorOrientationPacketEnergy,
    xiWardGreenExteriorPacketEnergy, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro rho hrho
  simp only [xiWardGreenExteriorCoefficient, if_true, norm_mul,
    norm_natCast, mul_pow, Complex.normSq_eq_norm_sq,
    xiWardGreenExteriorLocalEnergy]
  push_cast
  ring

/-- Finite Cayley-depth average after exact two-prime dephasing, retaining both adjacent
orientations. -/
def xiWardGreenExteriorDephasedSourceEnergy
    (S : Finset XiDivisorSupport) (M : ℕ) : ℝ :=
  (M : ℝ)⁻¹ * ∑ c ∈ Finset.range M,
    (xiWardGreenExteriorResolvedEnergy true S c +
      xiWardGreenExteriorResolvedEnergy false S c)

/-- Complete dephasing returns exactly the multiplicity-square Ward--Green exterior packet
energy. -/
theorem tendsto_xiWardGreenExteriorDephasedSourceEnergy
    (S : Finset XiDivisorSupport) :
    Tendsto (xiWardGreenExteriorDephasedSourceEnergy S) atTop
      (nhds (xiWardGreenExteriorPacketEnergy S)) := by
  have hp := tendsto_xiWardGreenExteriorResolvedEnergy_cesaro true S
  have hm := tendsto_xiWardGreenExteriorResolvedEnergy_cesaro false S
  have hadd := hp.add hm
  rw [xiWardGreenExteriorOrientationPacketEnergy_add_eq_packetEnergy S] at hadd
  convert hadd using 1
  funext M
  rw [xiWardGreenExteriorDephasedSourceEnergy]
  simp_rw [Finset.mul_sum, mul_add]
  rw [Finset.sum_add_distrib]

/-- A strict sub-quantum bound for every finite dephased source packet proves RH. -/
theorem riemannHypothesis_of_dephasedWardGreenExteriorSourceEnergy_lt_quantum
    (hsource : ∀ S : Finset XiDivisorSupport, ∃ C : ℝ,
      C < 4 * (96 / 145 : ℝ) ^ 2 ∧
        ∀ᶠ M : ℕ in atTop,
          xiWardGreenExteriorDephasedSourceEnergy S M ≤ C) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_xiSpectralPointSupport_im_eq_zero
  intro rho
  by_contra hy
  have hoff : (rho : ℂ).re ≠ 1 / 2 := by
    exact fun hline => hy ((xiSpectralPointSupport_im_eq_zero_iff rho).2 hline)
  obtain ⟨C, hC, hbound⟩ := hsource ({rho} : Finset XiDivisorSupport)
  have hle : xiWardGreenExteriorPacketEnergy ({rho} : Finset XiDivisorSupport) ≤ C :=
    le_of_tendsto
      (tendsto_xiWardGreenExteriorDephasedSourceEnergy
        ({rho} : Finset XiDivisorSupport)) hbound
  have hlocal :=
    four_mul_transverseQuantum_le_xiWardGreenExteriorLocalEnergy_of_offLine rho hoff
  have hm : (1 : ℝ) ≤ (xiSupportMultiplicity rho : ℝ) ^ 2 := by
    have hmpos : 0 < xiSupportMultiplicity rho := xiSupportMultiplicity_pos rho
    have hm1 : (1 : ℝ) ≤ (xiSupportMultiplicity rho : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hmpos.ne'
    nlinarith
  rw [xiWardGreenExteriorPacketEnergy, Finset.sum_singleton] at hle
  have hnonneg : 0 ≤ xiWardGreenExteriorLocalEnergy rho := by
    rw [xiWardGreenExteriorLocalEnergy]
    positivity
  have hlower : 4 * (96 / 145 : ℝ) ^ 2 ≤
      (xiSupportMultiplicity rho : ℝ) ^ 2 *
        xiWardGreenExteriorLocalEnergy rho := by
    calc
      4 * (96 / 145 : ℝ) ^ 2 ≤ xiWardGreenExteriorLocalEnergy rho := hlocal
      _ ≤ (xiSupportMultiplicity rho : ℝ) ^ 2 *
          xiWardGreenExteriorLocalEnergy rho := by
        nlinarith
  linarith

theorem riemannHypothesis_iff_dephasedWardGreenExteriorSourceEnergy_tendsto_zero :
    RiemannHypothesis ↔
      ∀ S : Finset XiDivisorSupport,
        Tendsto (xiWardGreenExteriorDephasedSourceEnergy S) atTop (nhds 0) := by
  constructor
  · intro hRH S
    simpa [(riemannHypothesis_iff_forall_xiWardGreenExteriorPacketEnergy_eq_zero.mp
      hRH) S] using tendsto_xiWardGreenExteriorDephasedSourceEnergy S
  · intro hsource
    apply riemannHypothesis_iff_forall_xiWardGreenExteriorPacketEnergy_eq_zero.mpr
    intro S
    exact tendsto_nhds_unique
      (tendsto_xiWardGreenExteriorDephasedSourceEnergy S) (hsource S)

end

end RHTower
