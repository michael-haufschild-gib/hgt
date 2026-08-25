import GaloisForLFunctions.HTGeometry.ConstitutiveAntisymmetricWallResponse
import GaloisForLFunctions.RHTower.ArithmeticResonanceCofinalTemperedness
import GaloisForLFunctions.RHTower.DeningerMeyerHalfDensityXiGraphClosure
import GaloisForLFunctions.RHTower.HedenmalmThetaKakutaniFluxPolarization
import GaloisForLFunctions.RHTower.XiSourceMarkedGibbsSplitting

/-!
# Xi relative-completion stability wall

The centered dilation weight `Re rho - 1/2` places every multiplicity-labelled Xi mode in the
minimal `A₂` stability wall.  This is not a relabelling by zero set alone: the exact scale is fixed
by the normalized compact-theta Green flux, while the same wall coordinate governs closability in
the canonical Meyer half-density completion.

The resulting dictionary is exact:

* right-half modes are stable and carry negative theta flux;
* critical modes are semistable, have zero purity curvature, and are sequentially closable;
* left-half modes are unstable and carry positive theta flux;
* functional-equation reflection exchanges the stable and unstable chambers while preserving the
  whole passive positive packet;
* global semistability is both RH and vanishing of the source-marked tropical free energy.

Thus functional-equation symmetry supplies degree zero only after opposite slopes are aggregated;
it does not prove componentwise semistability.  A producer must establish source-derived
semistability before that reflection-even quotient.
-/

open Complex Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

open HedenmalmThetaSource

/-- Signed transverse slope of one multiplicity-labelled Xi mode in the comparison between the
compact divisor semantics and the Meyer half-density completion. -/
def xiRelativeCompletionSlope (q : XiZeroCopy) : ℝ :=
  deningerMeyerHalfDensityXiHorizontalRate q.1

/-- Positive chamber of the minimal two-orientation stability object. -/
def XiRelativeCompletionStable (q : XiZeroCopy) : Prop :=
  (wallCharge₂ (xiRelativeCompletionSlope q)).arg <
    (wallCharge₁ (xiRelativeCompletionSlope q) +
      wallCharge₂ (xiRelativeCompletionSlope q)).arg

/-- Wall locus of the minimal two-orientation stability object. -/
def XiRelativeCompletionSemistable (q : XiZeroCopy) : Prop :=
  (wallCharge₁ (xiRelativeCompletionSlope q) +
      wallCharge₂ (xiRelativeCompletionSlope q)).arg =
    (wallCharge₂ (xiRelativeCompletionSlope q)).arg

/-- Negative chamber of the minimal two-orientation stability object. -/
def XiRelativeCompletionUnstable (q : XiZeroCopy) : Prop :=
  (wallCharge₁ (xiRelativeCompletionSlope q) +
      wallCharge₂ (xiRelativeCompletionSlope q)).arg <
    (wallCharge₂ (xiRelativeCompletionSlope q)).arg

/-- Every Xi slope lies in the injective phase window of the explicit stability wall. -/
theorem abs_xiRelativeCompletionSlope_lt_pi_div_two (q : XiZeroCopy) :
    |xiRelativeCompletionSlope q| < Real.pi / 2 := by
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hhalf : |(q.1 : ℂ).re - 1 / 2| < (1 / 2 : ℝ) := by
    rw [abs_lt]
    constructor <;> linarith
  have hpi : (1 / 2 : ℝ) < Real.pi / 2 := by
    nlinarith [Real.pi_gt_three]
  exact (show |(q.1 : ℂ).re - 1 / 2| < Real.pi / 2 from hhalf.trans hpi)

/-- Stability is precisely positive transverse slope. -/
theorem xiRelativeCompletionStable_iff_re_gt_half (q : XiZeroCopy) :
    XiRelativeCompletionStable q ↔ 1 / 2 < (q.1 : ℂ).re := by
  rw [XiRelativeCompletionStable,
    wallFamily_stable_iff_pos (abs_xiRelativeCompletionSlope_lt_pi_div_two q)]
  simp only [xiRelativeCompletionSlope,
    deningerMeyerHalfDensityXiHorizontalRate]
  constructor <;> intro h <;> linarith

/-- Semistability is precisely zero transverse slope. -/
theorem xiRelativeCompletionSemistable_iff_re_eq_half (q : XiZeroCopy) :
    XiRelativeCompletionSemistable q ↔ (q.1 : ℂ).re = 1 / 2 := by
  rw [XiRelativeCompletionSemistable,
    wallFamily_semistable_iff_zero
      (abs_xiRelativeCompletionSlope_lt_pi_div_two q)]
  simp only [xiRelativeCompletionSlope,
    deningerMeyerHalfDensityXiHorizontalRate]
  constructor <;> intro h <;> linarith

/-- Instability is precisely negative transverse slope. -/
theorem xiRelativeCompletionUnstable_iff_re_lt_half (q : XiZeroCopy) :
    XiRelativeCompletionUnstable q ↔ (q.1 : ℂ).re < 1 / 2 := by
  rw [XiRelativeCompletionUnstable,
    wallFamily_unstable_iff_neg
      (abs_xiRelativeCompletionSlope_lt_pi_div_two q)]
  simp only [xiRelativeCompletionSlope,
    deningerMeyerHalfDensityXiHorizontalRate]
  constructor <;> intro h <;> linarith

/-- Stability-wall semistability is exactly sequential closability of the actual Xi evaluation
in the canonical half-density completion. -/
theorem xiRelativeCompletionSemistable_iff_sequentiallyClosable
    (q : XiZeroCopy) :
    XiRelativeCompletionSemistable q ↔
      DeningerMeyerHalfDensityXiSequentiallyClosable q.1 := by
  rw [xiRelativeCompletionSemistable_iff_re_eq_half,
    deningerMeyerHalfDensityXiSequentiallyClosable_iff]

/-- The stability-wall moment vanishes exactly with weight-one purity curvature. -/
theorem xiRelativeCompletionSemistable_iff_purityCurvature_zero
    (q : XiZeroCopy) :
    XiRelativeCompletionSemistable q ↔
      weightOnePurityCurvature (q.1 : ℂ) = 0 := by
  rw [xiRelativeCompletionSemistable_iff_re_eq_half,
    weightOnePurityCurvature_eq_zero_iff_re_eq_half]

/-- Exact moment-map normalization: stability slope is minus compact-theta Green flux divided by
twice its positive mass-energy calibration. -/
theorem xiRelativeCompletionSlope_eq_neg_normalizedThetaFlux
    (q : XiZeroCopy) :
    xiRelativeCompletionSlope q =
      -(thetaXiRankTwoBoundaryFlux q /
        (2 * (thetaSource.mass * thetaXiRootEnergy q))) := by
  rw [xiRelativeCompletionSlope,
    deningerMeyerHalfDensityXiHorizontalRate,
    thetaXiRankTwoBoundaryFlux_eq_neg_massEnergy_mul_centeredRate,
    primeDepthBVWoldXiCenteredRate]
  have hmass : thetaSource.mass ≠ 0 := thetaSource.mass_ne_zero
  have henergy : thetaXiRootEnergy q ≠ 0 :=
    (thetaXiRootEnergy_pos q).ne'
  field_simp [hmass, henergy]

/-- Functional-equation reflection reverses relative-completion slope. -/
theorem xiRelativeCompletionSlope_copyReflect (q : XiZeroCopy) :
    xiRelativeCompletionSlope (xiZeroCopyReflectEquiv q) =
      -xiRelativeCompletionSlope q := by
  rw [xiRelativeCompletionSlope, xiRelativeCompletionSlope,
    deningerMeyerHalfDensityXiHorizontalRate,
    deningerMeyerHalfDensityXiHorizontalRate]
  change (1 - (q.1 : ℂ)).re - 1 / 2 =
    -((q.1 : ℂ).re - 1 / 2)
  simp
  ring

/-- The full passive positive packet is blind to functional-equation chamber exchange. -/
theorem xiRelativeCompletionPositivePacket_copyReflect (q : XiZeroCopy) :
    wallPositivePacket
        (xiRelativeCompletionSlope (xiZeroCopyReflectEquiv q)) =
      wallPositivePacket (xiRelativeCompletionSlope q) := by
  rw [xiRelativeCompletionSlope_copyReflect, wallPositivePacket_even]

/-- Functional-equation reflection exchanges strict stability and strict instability. -/
theorem xiRelativeCompletionStable_reflect_iff_unstable (q : XiZeroCopy) :
    XiRelativeCompletionStable (xiZeroCopyReflectEquiv q) ↔
      XiRelativeCompletionUnstable q := by
  rw [xiRelativeCompletionStable_iff_re_gt_half,
    xiRelativeCompletionUnstable_iff_re_lt_half]
  change 1 / 2 < (1 - (q.1 : ℂ)).re ↔ (q.1 : ℂ).re < 1 / 2
  simp
  constructor <;> intro h <;> linarith

/-- Stable chamber equals negative compact-theta moment map. -/
theorem xiRelativeCompletionStable_iff_thetaFlux_neg
    (q : XiZeroCopy) :
    XiRelativeCompletionStable q ↔ thetaXiRankTwoBoundaryFlux q < 0 := by
  rw [XiRelativeCompletionStable,
    wallFamily_stable_iff_pos (abs_xiRelativeCompletionSlope_lt_pi_div_two q),
    xiRelativeCompletionSlope_eq_neg_normalizedThetaFlux]
  have hden : 0 < 2 * (thetaSource.mass * thetaXiRootEnergy q) := by
    exact mul_pos (by norm_num)
      (mul_pos thetaSource.mass_pos (thetaXiRootEnergy_pos q))
  constructor
  · intro h
    rw [neg_pos] at h
    rcases div_neg_iff.mp h with hbad | hgood
    · exact absurd hbad.2 (not_lt_of_ge hden.le)
    · exact hgood.1
  · intro h
    rw [neg_pos]
    exact div_neg_iff.mpr (Or.inr ⟨h, hden⟩)

/-- Semistable wall equals zero compact-theta moment map. -/
theorem xiRelativeCompletionSemistable_iff_thetaFlux_zero
    (q : XiZeroCopy) :
    XiRelativeCompletionSemistable q ↔ thetaXiRankTwoBoundaryFlux q = 0 := by
  rw [XiRelativeCompletionSemistable,
    wallFamily_semistable_iff_zero
      (abs_xiRelativeCompletionSlope_lt_pi_div_two q),
    xiRelativeCompletionSlope_eq_neg_normalizedThetaFlux]
  have hden : 2 * (thetaSource.mass * thetaXiRootEnergy q) ≠ 0 := by
    exact (mul_pos (by norm_num)
      (mul_pos thetaSource.mass_pos (thetaXiRootEnergy_pos q))).ne'
  simp [hden]

/-- Unstable chamber equals positive compact-theta moment map. -/
theorem xiRelativeCompletionUnstable_iff_thetaFlux_pos
    (q : XiZeroCopy) :
    XiRelativeCompletionUnstable q ↔ 0 < thetaXiRankTwoBoundaryFlux q := by
  rw [XiRelativeCompletionUnstable,
    wallFamily_unstable_iff_neg
      (abs_xiRelativeCompletionSlope_lt_pi_div_two q),
    xiRelativeCompletionSlope_eq_neg_normalizedThetaFlux]
  have hden : 0 < 2 * (thetaSource.mass * thetaXiRootEnergy q) := by
    exact mul_pos (by norm_num)
      (mul_pos thetaSource.mass_pos (thetaXiRootEnergy_pos q))
  constructor
  · intro h
    rw [neg_lt] at h
    simp only [neg_zero] at h
    rcases div_pos_iff.mp h with hgood | hbad
    · exact hgood.1
    · exact absurd hbad.2 (not_lt_of_ge hden.le)
  · intro h
    rw [neg_lt]
    simpa only [neg_zero] using
      (div_pos_iff.mpr (Or.inl ⟨h, hden⟩))

/-- Pointwise stability dictionary: theta moment-map sign, Meyer closability, and Hodge purity are
one relative-completion condition. -/
theorem xiRelativeCompletionStabilityPackage (q : XiZeroCopy) :
    (XiRelativeCompletionStable q ↔ thetaXiRankTwoBoundaryFlux q < 0) ∧
    (XiRelativeCompletionSemistable q ↔ thetaXiRankTwoBoundaryFlux q = 0) ∧
    (XiRelativeCompletionUnstable q ↔ 0 < thetaXiRankTwoBoundaryFlux q) ∧
    (XiRelativeCompletionSemistable q ↔
      DeningerMeyerHalfDensityXiSequentiallyClosable q.1) ∧
    (XiRelativeCompletionSemistable q ↔
      weightOnePurityCurvature (q.1 : ℂ) = 0) := by
  exact ⟨xiRelativeCompletionStable_iff_thetaFlux_neg q,
    xiRelativeCompletionSemistable_iff_thetaFlux_zero q,
    xiRelativeCompletionUnstable_iff_thetaFlux_pos q,
    xiRelativeCompletionSemistable_iff_sequentiallyClosable q,
    xiRelativeCompletionSemistable_iff_purityCurvature_zero q⟩

/-- Global componentwise semistability of the multiplicity-exact Xi divisor is RH. -/
theorem all_xiRelativeCompletionSemistable_iff_riemannHypothesis :
    (∀ q : XiZeroCopy, XiRelativeCompletionSemistable q) ↔
      RiemannHypothesis := by
  constructor
  · intro h
    rw [riemannHypothesis_iff_deningerMeyerHalfDensityXiSequentiallyClosable]
    intro rho
    let q : XiZeroCopy :=
      ⟨rho, ⟨0, xiSupportMultiplicity_pos rho⟩⟩
    exact
      (xiRelativeCompletionSemistable_iff_sequentiallyClosable q).mp (h q)
  · intro h q
    have hclose :=
      (riemannHypothesis_iff_deningerMeyerHalfDensityXiSequentiallyClosable.mp h) q.1
    exact
      (xiRelativeCompletionSemistable_iff_sequentiallyClosable q).mpr hclose

/-- Global componentwise semistability is equivalent to collapse of the source-marked tropical
free energy, hence identifies that free energy with maximal destabilizing slope. -/
theorem all_xiRelativeCompletionSemistable_iff_tropicalFreeEnergy_zero :
    (∀ q : XiZeroCopy, XiRelativeCompletionSemistable q) ↔
      Tendsto
        (fun k : ℕ =>
          Real.log (xiThermalProjectiveColdPartition k) / (k : ℝ))
        atTop (nhds 0) := by
  rw [all_xiRelativeCompletionSemistable_iff_riemannHypothesis,
    xi_sourceMarkedGibbs_freeEnergy_zero_iff_rh]

end

end RHTower
