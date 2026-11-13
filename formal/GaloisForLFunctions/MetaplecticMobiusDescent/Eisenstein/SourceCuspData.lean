/-
Source cusp data adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.AffineLowerCuspBranches

/-!
# Source cusp data

The cusp datum `SourceCuspDatum` with its matrix, point and dual point. The primitive
ramified cusps have no constant mode and equal their Bessel series; arbitrarily low compact
strips force subexponential growth there. The cusp Mellin transforms are entire and reflect.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified
open scoped NNReal Pointwise
open RationalSource
open scoped Manifold ContDiff
open scoped Matrix
open UniqueFactorizationMonoid

lemma ramifiedSource_height_fourier_average (u t : Oˣ)
    (hu : (u : O) ^ 2 + (u : O) + 1 = 0) (ht : -(u : O) * (1 + 2 * (u : O)) = onceCuspScale t)
    (a b : ℝ) (ha : 0 < a) (ρ : BoundedContinuousFunction ℝ ℂ) (s : ℂ) (hs : 2 < s.re) (h : O) :
    (∫ w in cuspPeriodStrip a b, rationalSourceEisenstein s (scaledRamifiedCuspMatrix u • w) *
      cuspWeightedFourierPhase ρ h w ∂hyperbolicVolume) =
      (3 : ℂ) ^ s * ramifiedCuspGaussSeries u t h s * cuspIntervalWhittakerFactor a b ρ s h := by
  let g : HyperbolicSpace → ℂ := fun w => rationalSourceEisenstein s (scaledRamifiedCuspMatrix u • w) *
    cuspWeightedFourierPhase ρ h w
  have hg : Continuous g := ((rationalSourceProjection_continuous _
    (hyperbolicEisenstein_continuous s hs)).comp (continuous_hyperbolic_action _)).mul
      (cuspWeightedFourierPhase_continuous ρ h)
  rw [cuspInterval_integral_coordinates a b ha g hg.aestronglyMeasurable
    (cuspInterval_continuous_integrable a b ha g hg)]
  have hinner (v : ℝ) (hv : 0 < v) : (∫ z in periodDomain, g (cuspCoordinateLift (v, z))) =
      ρ v * ((3 : ℂ) ^ s * ((v : ℂ) ^ (2 - s) * sourceFourierKernel s (cuspFrequency h * v)) *
        ramifiedCuspGaussSeries u t h s) := by
    simp_rw [g, cuspCoordinateLift_positive v _ hv, scaledRamifiedCuspMatrix_action,
      cuspWeightedFourierPhase, hyperbolicHeight_upperPoint, cuspFourierPhase, hyperbolicHorizontal_upperPoint]
    rw [← ramifiedSourceEisenstein_scaled_fourier u t hu ht v hv s hs h, ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall (fun z => by ring))
  rw [cuspIntervalWhittakerFactor, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  have hv0 := Complex.ofReal_ne_zero.mpr (ha.trans_le hv.1).ne'
  dsimp only
  rw [hinner v (ha.trans_le hv.1)]
  have hp : (v : ℂ) ^ (-s - 1) = (v : ℂ) ^ (2 - s) / (v : ℂ) ^ 3 := by
    rw [show -s - 1 = (2 - s) - 3 by ring, Complex.cpow_sub _ _ hv0]
    congr 1
    exact Complex.cpow_natCast _ 3
  rw [hp]
  ring

/-- The six arithmetic residues determine every compact height test of the actual ramified source. -/
theorem ramifiedSource_height_residue (u t : Oˣ)
    (hu : (u : O) ^ 2 + (u : O) + 1 = 0) (ht : -(u : O) * (1 + 2 * (u : O)) = onceCuspScale t)
    (a b : ℝ) (ha : 0 < a) (ρ : BoundedContinuousFunction ℝ ℂ) (h : O) :
    sourceArbitraryHeightFourier (scaledRamifiedCuspMatrix u) a b ha ρ h cubicEisensteinResidue =
      (3 : ℂ) ^ (4 / 3 : ℂ) * ramifiedArithmeticResidue u t h * cuspIntervalWhittakerFactor a b ρ (4 / 3) h := by
  let coeff : RamifiedSixBranch → ℂ → ℂ := fun i s =>
    (3 : ℂ) ^ s * ramifiedSixWeight u t h i s * cuspIntervalWhittakerFactor a b ρ s h
  have h3 (s : ℂ) : AnalyticAt ℂ (fun z : ℂ => (3 : ℂ) ^ z) s := by
    apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
    exact Eventually.of_forall (fun z => differentiableAt_id.const_cpow (Or.inl (by norm_num)))
  have hc (i : RamifiedSixBranch) (s : ℂ) (hs : 1 < s.re) : AnalyticAt ℂ (coeff i) s :=
    ((h3 s).mul (ramifiedSixWeight_analyticAt u t h i s)).mul
      (cuspIntervalWhittakerFactor_analyticAt a b ha ρ h s hs)
  have he := finite_unramified_residue (ramifiedSixIndex u t h) coeff hc
    (sourceArbitraryHeightFamily (scaledRamifiedCuspMatrix u) a b ha ρ h)
    (sourceArbitraryHeightFourier (scaledRamifiedCuspMatrix u) a b ha ρ h cubicEisensteinResidue)
    (sourceArbitraryHeightFamily_analyticAt _ a b ha ρ h)
    (sourceArbitraryHeightFamily_residue_limit _ a b ha ρ h) (by
      intro s hs hi
      rw [sourceArbitraryHeightFamily_initial _ a b ha ρ h s hs hi,
        ramifiedSource_height_fourier_average u t hu ht a b ha ρ s (by linarith) h,
        ramifiedCuspGaussSeries_eq_six, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi'
      dsimp only [coeff]
      ring)
  refine he.trans ?_
  rw [ramifiedArithmeticResidue, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only [coeff]
  ring

theorem ramifiedSource_height_residue_integral (u t : Oˣ)
    (hu : (u : O) ^ 2 + (u : O) + 1 = 0) (ht : -(u : O) * (1 + 2 * (u : O)) = onceCuspScale t)
    (a b : ℝ) (ha : 0 < a) (ρ : BoundedContinuousFunction ℝ ℂ) (h : O) :
    (∫ w in cuspPeriodStrip a b, cubicSourceResidualFunction (scaledRamifiedCuspMatrix u • w) *
      cuspWeightedFourierPhase ρ h w ∂hyperbolicVolume) =
      (3 : ℂ) ^ (4 / 3 : ℂ) * ramifiedArithmeticResidue u t h * cuspIntervalWhittakerFactor a b ρ (4 / 3) h := by
  rw [← sourceArbitraryHeightFourier_residual_integral]
  exact ramifiedSource_height_residue u t hu ht a b ha ρ h

def ramifiedResidualFourierCoefficient (u t : Oˣ) (h : O) : ℂ :=
  ((3 : ℂ) ^ (4 / 3 : ℂ) * ramifiedArithmeticResidue u t h / ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ)) *
    ((2 * Real.pi : ℂ) / Complex.Gamma (4 / 3) * (2 * Real.pi * ‖cuspFrequency h‖ : ℂ) ^ (1 / 3 : ℂ))

theorem ramifiedSource_height_bessel (u t : Oˣ)
    (hu : (u : O) ^ 2 + (u : O) + 1 = 0) (ht : -(u : O) * (1 + 2 * (u : O)) = onceCuspScale t)
    (a b : ℝ) (ha : 0 < a) (ρ : BoundedContinuousFunction ℝ ℂ) (h : O) (hh : h ≠ 0) :
    (∫ w in cuspPeriodStrip a b, cubicSourceResidualFunction (scaledRamifiedCuspMatrix u • w) *
      cuspWeightedFourierPhase ρ h w ∂hyperbolicVolume) =
      ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ) * ramifiedResidualFourierCoefficient u t h *
        ∫ v in Set.Icc a b, ρ v *
          (schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency h‖ * v) / (v : ℂ) ^ 2) := by
  rw [ramifiedSource_height_residue_integral u t hu ht a b ha ρ h,
    cuspIntervalWhittakerFactor_center_bessel a b ha ρ h hh, ramifiedResidualFourierCoefficient]
  field_simp [cusp_volume_ne_zero]

lemma ramifiedResidualFourierCoefficient_interval_bound (u t : Oˣ)
    (hu : (u : O) ^ 2 + (u : O) + 1 = 0) (ht : -(u : O) * (1 + 2 * (u : O)) = onceCuspScale t)
    (a b : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : O, h ≠ 0 →
      ‖ramifiedResidualFourierCoefficient u t h‖ * ‖∫ v in Set.Icc a b,
        schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency h‖ * v) / (v : ℂ) ^ 2‖ ≤ C := by
  let f : HyperbolicSpace → ℂ := fun w => cubicSourceResidualFunction (scaledRamifiedCuspMatrix u • w)
  let B : ℝ := ∫ w in cuspPeriodStrip a b, ‖f w‖ ∂hyperbolicVolume
  have hB : 0 ≤ B := integral_nonneg (fun w => norm_nonneg (f w))
  let area : ℂ := ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ)
  have harea : 0 < ‖area‖ := norm_pos_iff.mpr cusp_volume_ne_zero
  refine ⟨B / ‖area‖, div_nonneg hB harea.le, ?_⟩
  intro h hh
  have hb := norm_integral_le_integral_norm (μ := hyperbolicVolume.restrict (cuspPeriodStrip a b)) (fun w => f w *
    cuspWeightedFourierPhase (BoundedContinuousFunction.const ℝ 1) h w)
  change ‖∫ w in cuspPeriodStrip a b, f w * cuspWeightedFourierPhase _ h w ∂hyperbolicVolume‖ ≤ _ at hb
  rw [ramifiedSource_height_bessel u t hu ht a b ha _ h hh] at hb
  simp only [BoundedContinuousFunction.const_apply, one_mul, norm_mul, cuspWeightedFourierPhase,
    cuspFourierPhase, tracePhase_norm, norm_one, mul_one] at hb
  apply (le_div_iff₀ harea).mpr
  calc
    _ = ‖area‖ * ‖ramifiedResidualFourierCoefficient u t h‖ * ‖∫ v in Set.Icc a b,
        schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency h‖ * v) / (v : ℂ) ^ 2‖ := by ring
    _ ≤ _ := hb

/-- Arbitrarily low compact strips force subexponential growth at the ramified cusps. -/
theorem ramifiedResidualFourierCoefficient_subexponential (u t : Oˣ)
    (hu : (u : O) ^ 2 + (u : O) + 1 = 0) (ht : -(u : O) * (1 + 2 * (u : O)) = onceCuspScale t)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : O, h ≠ 0 →
      ‖ramifiedResidualFourierCoefficient u t h‖ ≤ C * Real.exp (ε * ‖cuspFrequency h‖) :=
  cubicBesselCoefficient_subexponential (ramifiedResidualFourierCoefficient u t)
    (ramifiedResidualFourierCoefficient_interval_bound u t hu ht) ε hε

theorem ramifiedSource_fourier_all_heights (u t : Oˣ)
    (hu : (u : O) ^ 2 + (u : O) + 1 = 0) (ht : -(u : O) * (1 + 2 * (u : O)) = onceCuspScale t)
    (v : ℝ) (hv : 0 < v) (h : O) :
    (∫ z in periodDomain, cubicSourceResidualFunction (scaledRamifiedCuspMatrix u • upperPoint z v hv) *
      tracePhase (-cuspFrequency h * z)) =
      ((3 : ℂ) ^ (4 / 3 : ℂ) * ramifiedArithmeticResidue u t h) *
        ((v : ℂ) ^ (2 / 3 : ℂ) * sourceFourierKernel (4 / 3) (cuspFrequency h * v)) := by
  let f : HyperbolicSpace → ℂ := fun w => cubicSourceResidualFunction (scaledRamifiedCuspMatrix u • w)
  have hf : Continuous f := cubicSourceResidualFunction_continuous.comp (continuous_hyperbolic_action _)
  let R := (3 : ℂ) ^ (4 / 3 : ℂ) * ramifiedArithmeticResidue u t h
  let D : ℝ → ℂ := fun v => R *
    ((v : ℂ) ^ (-(4 / 3 : ℂ) - 1) * sourceFourierKernel (4 / 3) (cuspFrequency h * v))
  have hD : ContinuousOn D (Set.Ioi 0) := by
    intro v hv
    exact (continuousAt_const.mul
      ((Complex.continuousAt_ofReal_cpow_const v _ (Or.inr hv.ne')).mul
        (((sourceFourierKernel_continuous_freq (4 / 3) (by norm_num)).comp
          (Complex.continuous_ofReal.const_mul (cuspFrequency h))).continuousAt))).continuousWithinAt
  have he := continuousCuspSlice_eq_of_interval_tests f hf h D hD (by
    intro a b ha ρ
    rw [ramifiedSource_height_residue_integral u t hu ht a b ha ρ h,
      cuspIntervalWhittakerFactor, ← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall (fun v => by dsimp only [D, R]; ring)) v hv
  have hv0 : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
  have hpow : (v : ℂ) ^ (-(4 / 3 : ℂ) - 1) * (v : ℂ) ^ 3 = (v : ℂ) ^ (2 / 3 : ℂ) := by
    rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ hv0]
    congr 1
    norm_num
  dsimp only [continuousCuspSlice, f, D] at he
  simp_rw [cuspCoordinateLift_positive v _ hv] at he
  rw [div_eq_iff (pow_ne_zero 3 hv0)] at he
  rw [he]
  linear_combination R * sourceFourierKernel (4 / 3) (cuspFrequency h * v) * hpow

theorem ramifiedSource_fourier_bessel (u t : Oˣ)
    (hu : (u : O) ^ 2 + (u : O) + 1 = 0) (ht : -(u : O) * (1 + 2 * (u : O)) = onceCuspScale t)
    (v : ℝ) (hv : 0 < v) (h : O) (hh : h ≠ 0) :
    (∫ z in periodDomain, cubicSourceResidualFunction (scaledRamifiedCuspMatrix u • upperPoint z v hv) *
      tracePhase (-cuspFrequency h * z)) =
      ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ) * ramifiedResidualFourierCoefficient u t h * (v : ℂ) *
        schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency h‖ * v) := by
  rw [ramifiedSource_fourier_all_heights u t hu ht]
  have hv0 : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
  have hp : (v : ℂ) ^ (-(4 / 3 : ℂ) - 1) * (v : ℂ) ^ 3 = (v : ℂ) ^ (2 / 3 : ℂ) := by
    rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ hv0]
    congr 1
    norm_num
  rw [← hp]
  calc
    _ = ((3 : ℂ) ^ (4 / 3 : ℂ) * ramifiedArithmeticResidue u t h) *
        (((v : ℂ) ^ (-(4 / 3 : ℂ) - 1) * sourceFourierKernel (4 / 3) (cuspFrequency h * v)) * (v : ℂ) ^ 3) := by ring
    _ = _ := by
      rw [sourceFourierKernel_residual_height h hh v hv, ramifiedResidualFourierCoefficient]
      field_simp [hv0, cusp_volume_ne_zero]

/-- The two primitive cubic cusps and their once-ramified scale units. -/
def ramifiedCuspRoot : Bool → Oˣ
  | false => cuspOmegaUnit
  | true => cuspOmegaUnit ^ 2

def ramifiedCuspScaleUnit : Bool → Oˣ
  | false => -cuspOmegaUnit
  | true => cuspOmegaUnit ^ 2

lemma ramifiedCuspRoot_relation (side : Bool) :
    (ramifiedCuspRoot side : O) ^ 2 + (ramifiedCuspRoot side : O) + 1 = 0 := by
  cases side
  · exact cusp_omega_relation
  · simp only [ramifiedCuspRoot, Units.val_pow_eq_pow_val, cuspOmegaUnit_val]
    linear_combination (omega ^ 2 - omega + 1) * cusp_omega_relation

lemma ramifiedCuspScaleUnit_spec (side : Bool) :
    -(ramifiedCuspRoot side : O) * (1 + 2 * (ramifiedCuspRoot side : O)) =
      onceCuspScale (ramifiedCuspScaleUnit side) := by
  cases side
  · simp only [ramifiedCuspRoot, ramifiedCuspScaleUnit, onceCuspScale,
      Units.val_neg, cuspOmegaUnit_val, traceLambda]
  · simp only [ramifiedCuspRoot, ramifiedCuspScaleUnit, onceCuspScale,
      Units.val_pow_eq_pow_val, cuspOmegaUnit_val, traceLambda]
    linear_combination -2 * omega ^ 2 * cusp_omega_relation

def ramifiedBesselCoefficient (side : Bool) : O → ℂ :=
  ramifiedResidualFourierCoefficient (ramifiedCuspRoot side) (ramifiedCuspScaleUnit side)

theorem ramifiedBesselCoefficient_subexponential (side : Bool) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : O, h ≠ 0 →
      ‖ramifiedBesselCoefficient side h‖ ≤ C * Real.exp (ε * ‖cuspFrequency h‖) :=
  ramifiedResidualFourierCoefficient_subexponential _ _
    (ramifiedCuspRoot_relation side) (ramifiedCuspScaleUnit_spec side) ε hε

lemma ramifiedScaledRow_continuous (t : O) (v : ℝ) (hv : 0 < v) :
    Continuous (ramifiedScaledRow t v) := by
  have hp : 0 < 3 * v := by positivity
  have he : ramifiedScaledRow t v = fun z => ramifiedSourceFunction t (upperPoint (3 * z) (3 * v) hp) := by
    funext z
    rw [ramifiedScaledRow, cuspCoordinateLift_positive _ _ hp]
  rw [he]
  exact (ramifiedSourceFunction_continuous t).comp
    (upperCoordinatesHomeomorph.continuous.comp
      (show Continuous (fun z : ℂ => (⟨(3 * z, 3 * v), hp⟩ : UpperCoordinates)) by fun_prop))

lemma ramifiedScaledRow_zero (side : Bool) (v : ℝ) (hv : 0 < v) :
    (∫ z in periodDomain, ramifiedScaledRow (ramifiedCuspRoot side : O) v z) = 0 := by
  have hp : 0 < 3 * v := by positivity
  simp only [ramifiedScaledRow, cuspCoordinateLift_positive _ _ hp]
  cases side
  · exact ramifiedSourceFunction_omega_constant_zero (3 * v) hp
  · exact ramifiedSourceFunction_omega_sq_constant_zero (3 * v) hp

theorem ramifiedScaledRow_fourier (side : Bool) (v : ℝ) (hv : 0 < v) (h : O) :
    (∫ z in periodDomain, ramifiedScaledRow (ramifiedCuspRoot side : O) v z *
      tracePhase (-cuspFrequency h * z)) =
      ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ) * cubicBesselAmplitude (ramifiedBesselCoefficient side) v h := by
  by_cases hh : h = 0
  · subst h
    simp only [cuspFrequency, map_zero, zero_div, neg_zero, zero_mul,
      AddChar.map_zero_eq_one, mul_one, cubicBesselAmplitude, if_true]
    rw [ramifiedScaledRow_zero side v hv, mul_zero]
  have he := ramifiedSource_fourier_bessel _ _ (ramifiedCuspRoot_relation side)
    (ramifiedCuspScaleUnit_spec side) v hv h hh
  simp_rw [scaledRamifiedCuspMatrix_action] at he
  simpa only [ramifiedScaledRow, cuspCoordinateLift_positive _ _ (show 0 < 3 * v by positivity),
    ramifiedSourceFunction, cubicBesselAmplitude, if_neg hh, ramifiedBesselCoefficient, mul_assoc] using he

lemma cubicBesselAmplitude_summable (c : O → ℂ)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ h : O, h ≠ 0 →
      ‖c h‖ ≤ C * Real.exp (ε * ‖cuspFrequency h‖)) (v : ℝ) (hv : 0 < v) :
    Summable (fun h => ‖cubicBesselAmplitude c v h‖) := by
  simpa only [cubicBesselTerm, norm_mul, tracePhase_norm, mul_one] using
    cubicBesselTerm_summable_norm c hsub (v, 0) hv

/-- The primitive ramified cusps have no constant mode and equal their Bessel series pointwise. -/
theorem ramifiedScaledRow_eq_bessel (side : Bool) (v : ℝ) (hv : 0 < v) (z : ℂ) :
    ramifiedScaledRow (ramifiedCuspRoot side : O) v z =
      cuspCharacterSeries (cubicBesselAmplitude (ramifiedBesselCoefficient side) v) z := by
  have hs := cubicBesselAmplitude_summable _ (ramifiedBesselCoefficient_subexponential side) v hv
  exact congrFun (periodDomain_continuous_ext _ _ (ramifiedScaledRow_continuous _ v hv)
    (cuspCharacterSeries_continuous _ hs) (ramifiedScaledRow_period _ v hv)
    (fun n z => cuspCharacterSeries_period _ z n) (fun h => by
      rw [ramifiedScaledRow_fourier side v hv h, cuspCharacterSeries_fourier _ hs h])) z

theorem ramifiedSource_bessel (side : Bool) (v : ℝ) (hv : 0 < v) (z : ℂ) :
    ramifiedSourceFunction (ramifiedCuspRoot side : O) (upperPoint z v hv) =
      ∑' h : O, cubicBesselTerm (ramifiedBesselCoefficient side) h (v / 3, z / 3) := by
  have he := ramifiedScaledRow_eq_bessel side (v / 3) (by positivity) (z / 3)
  simpa only [ramifiedScaledRow, mul_div_cancel₀ _ (by norm_num : (3 : ℝ) ≠ 0),
    show (3 : ℂ) * (z / 3) = z by ring, show 3 * (v / 3) = v by ring,
    cuspCoordinateLift_positive v z hv, cuspCharacterSeries, cubicBesselTerm] using he

theorem ramifiedSource_bessel_normal (side : Bool) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∃ g : O → ℝ, Summable g ∧ ∀ h : O, ∀ v : ℝ, v ∈ Set.Icc a b → ∀ z : ℂ,
      ‖cubicBesselTerm (ramifiedBesselCoefficient side) h (v / 3, z / 3)‖ ≤ g h := by
  obtain ⟨C, hC, hb⟩ := cubicBesselTerm_strip_bound _ (ramifiedBesselCoefficient_subexponential side)
    (a / 3) (b / 3) (by positivity) (by linarith only [hab])
  refine ⟨fun h => C * Real.exp (-(Real.pi * (a / 3)) * ‖cuspFrequency h‖),
    (summable_exp_neg_cuspFrequency_norm _ (by positivity)).mul_left C, ?_⟩
  intro h v hv z
  exact hb h (v / 3, z / 3) ⟨by dsimp only; linarith only [hv.1], by dsimp only; linarith only [hv.2]⟩

def residualBesselDecayRate : ℝ := Real.pi * ‖(3 : ℂ) * ringComplex traceLambda‖⁻¹ / 2

lemma residualBesselDecayRate_pos : 0 < residualBesselDecayRate := by
  have hd := norm_pos_iff.mpr (mul_ne_zero (by norm_num : (3 : ℂ) ≠ 0)
    (ringComplex_ne_zero traceLambda_ne_zero))
  unfold residualBesselDecayRate
  positivity

/-- The frequency gap leaves exponential decay in height after summing all horizontal modes. -/
theorem cubicBesselAmplitude_exponential_bound (c : O → ℂ)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ h : O, h ≠ 0 →
      ‖c h‖ ≤ C * Real.exp (ε * ‖cuspFrequency h‖)) (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : O, ∀ v : ℝ, a ≤ v →
      ‖cubicBesselAmplitude c v h‖ ≤ C * Real.exp (-(Real.pi * a / 2) * ‖cuspFrequency h‖) *
        Real.exp (-residualBesselDecayRate * v) := by
  let d : ℝ := ‖(3 : ℂ) * ringComplex traceLambda‖⁻¹
  have hd : 0 < d := inv_pos.mpr (norm_pos_iff.mpr
    (mul_ne_zero (by norm_num) (ringComplex_ne_zero traceLambda_ne_zero)))
  obtain ⟨B, hB, hb⟩ := schlafliBesselK_one_third_exp_upper (4 * Real.pi * d * a) (by positivity)
  obtain ⟨A, hA, hc⟩ := hsub (Real.pi * a / 2) (by positivity)
  refine ⟨A * B * (2 / (Real.pi * d)), by positivity, ?_⟩
  intro h v hv
  by_cases hh : h = 0
  · simp only [cubicBesselAmplitude, if_pos hh, norm_zero]
    positivity
  have hvp := ha.trans_le hv
  have hgap : d ≤ ‖cuspFrequency h‖ := cuspFrequency_norm_lower h hh
  have hrv := mul_le_mul_of_nonneg_left hv (norm_nonneg (cuspFrequency h))
  have hdv := mul_le_mul_of_nonneg_right hgap hvp.le
  have hx : 4 * Real.pi * d * a ≤ 4 * Real.pi * ‖cuspFrequency h‖ * v := by
    have hm := mul_le_mul hgap hv ha.le (norm_nonneg (cuspFrequency h))
    nlinarith only [mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ 4 * Real.pi)]
  have hexp : (Real.pi * a / 2) * ‖cuspFrequency h‖ -
      (4 * Real.pi * ‖cuspFrequency h‖ * v) / 2 ≤
      -(Real.pi * a / 2) * ‖cuspFrequency h‖ + -(Real.pi * d) * v := by
    nlinarith only [mul_le_mul_of_nonneg_left (add_le_add hrv hdv) Real.pi_pos.le]
  rw [cubicBesselAmplitude, if_neg hh, norm_mul, norm_mul, Complex.norm_of_nonneg hvp.le]
  calc
    _ ≤ (A * Real.exp ((Real.pi * a / 2) * ‖cuspFrequency h‖)) * v *
        (B * Real.exp (-(4 * Real.pi * ‖cuspFrequency h‖ * v) / 2)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right (hc h hh) hvp.le) (hb _ hx) (norm_nonneg _) (by positivity)
    _ = (A * B * v) * Real.exp ((Real.pi * a / 2) * ‖cuspFrequency h‖ -
        (4 * Real.pi * ‖cuspFrequency h‖ * v) / 2) := by
      rw [show -(4 * Real.pi * ‖cuspFrequency h‖ * v) / 2 =
        -((4 * Real.pi * ‖cuspFrequency h‖ * v) / 2) by ring, Real.exp_neg, Real.exp_sub]
      ring
    _ ≤ (A * B * v) * Real.exp (-(Real.pi * a / 2) * ‖cuspFrequency h‖ + -(Real.pi * d) * v) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity)
    _ = (A * B * Real.exp (-(Real.pi * a / 2) * ‖cuspFrequency h‖)) *
        (v * Real.exp (-(Real.pi * d) * v)) := by rw [Real.exp_add]; ring
    _ ≤ (A * B * Real.exp (-(Real.pi * a / 2) * ‖cuspFrequency h‖)) *
        ((2 / (Real.pi * d)) * Real.exp (-(Real.pi * d / 2) * v)) :=
      mul_le_mul_of_nonneg_left (frequency_exp_absorption (Real.pi * d) v (by positivity)) (by positivity)
    _ = _ := by dsimp only [residualBesselDecayRate, d]; ring

theorem cubicBesselSeries_exponential_decay (c : O → ℂ)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ h : O, h ≠ 0 →
      ‖c h‖ ≤ C * Real.exp (ε * ‖cuspFrequency h‖)) (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, a ≤ v → ∀ z : ℂ,
      ‖∑' h : O, cubicBesselTerm c h (v, z)‖ ≤ C * Real.exp (-residualBesselDecayRate * v) := by
  obtain ⟨C, hC, hb⟩ := cubicBesselAmplitude_exponential_bound c hsub a ha
  let w : O → ℝ := fun h => Real.exp (-(Real.pi * a / 2) * ‖cuspFrequency h‖)
  have hw : Summable w := summable_exp_neg_cuspFrequency_norm _ (by positivity)
  refine ⟨C * ∑' h, w h, mul_nonneg hC (tsum_nonneg (fun h => (Real.exp_pos _).le)), ?_⟩
  intro v hv z
  have hs := cubicBesselTerm_summable_norm c hsub (v, z) (ha.trans_le hv)
  have hm (h : O) : ‖cubicBesselTerm c h (v, z)‖ ≤
      C * w h * Real.exp (-residualBesselDecayRate * v) := by
    simpa only [cubicBesselTerm, norm_mul, tracePhase_norm, mul_one] using hb h v hv
  have he := (norm_tsum_le_tsum_norm hs).trans
    (Summable.tsum_le_tsum hm hs ((hw.mul_left C).mul_right _))
  simpa only [tsum_mul_right, tsum_mul_left] using he

theorem ramifiedSource_exponential_decay (side : Bool) (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, ∀ hv : 0 < v, a ≤ v → ∀ z : ℂ,
      ‖ramifiedSourceFunction (ramifiedCuspRoot side : O) (upperPoint z v hv)‖ ≤
        C * Real.exp (-(residualBesselDecayRate / 3) * v) := by
  obtain ⟨C, hC, hb⟩ := cubicBesselSeries_exponential_decay _ (ramifiedBesselCoefficient_subexponential side)
    (a / 3) (by positivity)
  refine ⟨C, hC, ?_⟩
  intro v hv hav z
  rw [ramifiedSource_bessel side v hv z]
  convert hb (v / 3) (by linarith only [hav]) (z / 3) using 1 <;> ring

lemma cubicBesselAmplitude_firstMoment_summable (c : O → ℂ)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ h : O, h ≠ 0 →
      ‖c h‖ ≤ C * Real.exp (ε * ‖cuspFrequency h‖)) (v : ℝ) (hv : 0 < v) :
    Summable (fun h => ‖cuspFrequency h‖ * ‖cubicBesselAmplitude c v h‖) := by
  obtain ⟨C, hC, hb⟩ := cubicBesselTerm_strip_bound c hsub v v hv le_rfl
  apply Summable.of_nonneg_of_le (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (fun h => ?_) ((cuspFrequency_firstMoment_exp_summable (Real.pi * v) (by positivity)).mul_left C)
  have he := mul_le_mul_of_nonneg_left (hb h (v, 0) ⟨le_rfl, le_rfl⟩) (norm_nonneg (cuspFrequency h))
  simpa only [cubicBesselTerm, norm_mul, tracePhase_norm, mul_one, mul_left_comm] using he

lemma ninthCuspFrequency_eq_third (h : O) : ninthCuspFrequency h = cuspFrequency h / 3 := by
  unfold ninthCuspFrequency cuspFrequency
  ring

theorem ramifiedSource_wirtingerBar (side : Bool) (v : ℝ) (hv : 0 < v) (z : ℂ) :
    horizontalWirtingerBar (fun w => ramifiedSourceFunction (ramifiedCuspRoot side : O)
      (upperPoint w v hv)) z =
      ∑' h : O, (2 * Real.pi * Complex.I * star (ninthCuspFrequency h)) *
        cubicBesselTerm (ramifiedBesselCoefficient side) h (v / 3, z / 3) := by
  have hp : 0 < v / 3 := by positivity
  have hs := cubicBesselAmplitude_summable _ (ramifiedBesselCoefficient_subexponential side) (v / 3) hp
  have hfirst := cubicBesselAmplitude_firstMoment_summable _
    (ramifiedBesselCoefficient_subexponential side) (v / 3) hp
  have hn : Summable (fun h => ‖ninthCuspFrequency h‖ *
      ‖cubicBesselAmplitude (ramifiedBesselCoefficient side) (v / 3) h‖) := by
    simpa only [ninthCuspFrequency_eq_third, norm_div,
      show ‖(3 : ℂ)‖ = (3 : ℝ) by norm_num, div_mul_eq_mul_div] using hfirst.div_const 3
  have hphase (h : O) (w : ℂ) : cuspFrequency h * (w / 3) = ninthCuspFrequency h * w := by
    rw [ninthCuspFrequency_eq_third]
    ring
  have he : (fun w => ramifiedSourceFunction (ramifiedCuspRoot side : O) (upperPoint w v hv)) =
      fun w => ∑' h : O, cubicBesselAmplitude (ramifiedBesselCoefficient side) (v / 3) h *
        tracePhase (ninthCuspFrequency h * w) := by
    funext w
    rw [ramifiedSource_bessel side v hv w]
    simp only [cubicBesselTerm, hphase]
  rw [he, traceFourierSeries_wirtingerBar _ _ hs hn]
  simp only [cubicBesselTerm, hphase]

/-- Multiplying subexponential Fourier coefficients by a linear frequency weight preserves growth. -/
lemma cubicBesselCoefficient_linearWeight_subexponential (c m : O → ℂ)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ h : O, h ≠ 0 →
      ‖c h‖ ≤ C * Real.exp (ε * ‖cuspFrequency h‖))
    (L : ℝ) (hL : 0 ≤ L) (hm : ∀ h : O, h ≠ 0 → ‖m h‖ ≤ L * ‖cuspFrequency h‖)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : O, h ≠ 0 →
      ‖m h * c h‖ ≤ C * Real.exp (ε * ‖cuspFrequency h‖) := by
  obtain ⟨C, hC, hc⟩ := hsub (ε / 2) (by positivity)
  refine ⟨L * C * (2 / ε), by positivity, ?_⟩
  intro h hh
  have hr : ‖cuspFrequency h‖ ≤ (2 / ε) * Real.exp ((ε / 2) * ‖cuspFrequency h‖) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hε).mpr
    nlinarith only [Real.add_one_le_exp ((ε / 2) * ‖cuspFrequency h‖)]
  rw [norm_mul]
  calc
    _ ≤ (L * ‖cuspFrequency h‖) * (C * Real.exp ((ε / 2) * ‖cuspFrequency h‖)) :=
      mul_le_mul (hm h hh) (hc h hh) (norm_nonneg _) (mul_nonneg hL (norm_nonneg _))
    _ ≤ (L * ((2 / ε) * Real.exp ((ε / 2) * ‖cuspFrequency h‖))) *
        (C * Real.exp ((ε / 2) * ‖cuspFrequency h‖)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr hL) (by positivity)
    _ = _ := by
      rw [show ε * ‖cuspFrequency h‖ = (ε / 2) * ‖cuspFrequency h‖ +
        (ε / 2) * ‖cuspFrequency h‖ by ring, Real.exp_add]
      ring

lemma cubicBesselTerm_weight (c m : O → ℂ) (h : O) (p : ℝ × ℂ) :
    cubicBesselTerm (fun k => m k * c k) h p = m h * cubicBesselTerm c h p := by
  by_cases hh : h = 0 <;> simp only [cubicBesselTerm, cubicBesselAmplitude, hh,
    if_true, if_false, zero_mul, mul_zero, mul_assoc]

def ramifiedBarBesselCoefficient (side : Bool) (h : O) : ℂ :=
  (2 * Real.pi * Complex.I * star (ninthCuspFrequency h)) * ramifiedBesselCoefficient side h

lemma ramifiedBarBesselCoefficient_subexponential (side : Bool) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : O, h ≠ 0 →
      ‖ramifiedBarBesselCoefficient side h‖ ≤ C * Real.exp (ε * ‖cuspFrequency h‖) := by
  apply cubicBesselCoefficient_linearWeight_subexponential _ _
    (ramifiedBesselCoefficient_subexponential side) (2 * Real.pi / 3) (by positivity) _ ε hε
  intro h hh
  simp only [norm_mul, norm_star, Complex.norm_I, mul_one, ninthCuspFrequency_eq_third,
    norm_div, show ‖(3 : ℂ)‖ = (3 : ℝ) by norm_num,
    show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  exact le_of_eq (by ring)

theorem ramifiedSource_wirtingerBar_bessel (side : Bool) (v : ℝ) (hv : 0 < v) (z : ℂ) :
    horizontalWirtingerBar (fun w => ramifiedSourceFunction (ramifiedCuspRoot side : O)
      (upperPoint w v hv)) z =
      ∑' h : O, cubicBesselTerm (ramifiedBarBesselCoefficient side) h (v / 3, z / 3) := by
  rw [ramifiedSource_wirtingerBar side v hv z]
  exact tsum_congr (fun h => (cubicBesselTerm_weight (ramifiedBesselCoefficient side)
    (fun k => 2 * Real.pi * Complex.I * star (ninthCuspFrequency k)) h (v / 3, z / 3)).symm)

/-- The differentiated ramified cusp row has the same exponential height rate. -/
theorem ramifiedSource_wirtingerBar_exponential_decay (side : Bool) (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, ∀ hv : 0 < v, a ≤ v → ∀ z : ℂ,
      ‖horizontalWirtingerBar (fun w => ramifiedSourceFunction (ramifiedCuspRoot side : O)
        (upperPoint w v hv)) z‖ ≤ C * Real.exp (-(residualBesselDecayRate / 3) * v) := by
  obtain ⟨C, hC, hb⟩ := cubicBesselSeries_exponential_decay _
    (ramifiedBarBesselCoefficient_subexponential side) (a / 3) (by positivity)
  refine ⟨C, hC, ?_⟩
  intro v hv hav z
  rw [ramifiedSource_wirtingerBar_bessel side v hv z]
  convert hb (v / 3) (by linarith only [hav]) (z / 3) using 1 <;> ring

def cuspBarProfile (f : HyperbolicSpace → ℂ) (z : ℂ) (v : ℝ) : ℂ :=
  horizontalWirtingerBar (fun w => f (cuspCoordinateLift (v, w))) z

def cuspZProfile (f : HyperbolicSpace → ℂ) (z : ℂ) (v : ℝ) : ℂ :=
  horizontalWirtingerZ (fun w => f (cuspCoordinateLift (v, w))) z

lemma cuspBarProfile_positive (f : HyperbolicSpace → ℂ) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    cuspBarProfile f z v = horizontalWirtingerBar (fun w => f (upperPoint w v hv)) z := by
  simp only [cuspBarProfile, cuspCoordinateLift_positive v _ hv]

lemma cuspZProfile_positive (f : HyperbolicSpace → ℂ) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    cuspZProfile f z v = horizontalWirtingerZ (fun w => f (upperPoint w v hv)) z := by
  simp only [cuspZProfile, cuspCoordinateLift_positive v _ hv]

theorem ramifiedSource_barProfile_continuousOn (side : Bool) (z : ℂ) :
    ContinuousOn (cuspBarProfile (ramifiedSourceFunction (ramifiedCuspRoot side : O)) z) (Set.Ioi 0) := by
  intro v hv
  change 0 < v at hv
  have hs := (cubicBesselSeries_hasFDerivAt _ (ramifiedBarBesselCoefficient_subexponential side)
    (v / 3, z / 3) (by positivity)).differentiableAt
  have hp : DifferentiableAt ℝ (fun y : ℝ => (y / 3, z / 3)) v := by fun_prop
  apply ContinuousAt.continuousWithinAt
  apply (hs.comp v hp).continuousAt.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hv] with y hy
  rw [cuspBarProfile_positive _ _ _ hy, ramifiedSource_wirtingerBar_bessel side y hy z]
  rfl

def reflectedCuspProfile (A : ℂ) (Q : ℝ) (f : ℝ → ℂ) (v : ℝ) : ℂ :=
  A * ((v : ℂ) ^ (-2 : ℂ) * f ((Q * v)⁻¹))

/-- Inverting a finite cusp reflects its horizontal derivative profile with weight two. -/
theorem cubicSource_barProfile_reflection (g : SL(2, ℂ)) (hc : g 1 0 ≠ 0) (v : ℝ) (hv : 0 < v) :
    cuspBarProfile cubicSourceResidualFunction (g 0 0 / g 1 0) v =
      reflectedCuspProfile (-1 / (g 1 0) ^ 2) (‖g 1 0‖ ^ 2)
        (cuspZProfile (fun w => cubicSourceResidualFunction (g • w)) (-g 1 1 / g 1 0)) v := by
  have hd : 0 < (‖g 1 0‖ ^ 2 * v)⁻¹ := by positivity
  rw [cuspBarProfile_positive _ _ _ hv, reflectedCuspProfile, cuspZProfile_positive _ _ _ hd,
    cubicSourceResidualFunction_cusp_derivative g hc v hv]
  have hp : (v : ℂ) ^ (-2 : ℂ) = ((v : ℂ) ^ 2)⁻¹ := by
    rw [Complex.cpow_neg, Complex.cpow_ofNat]
  rw [hp]
  simp only [one_div]
  ring

theorem conjugateSource_barProfile_reflection (g : SL(2, ℂ)) (hc : g 1 0 ≠ 0) (v : ℝ) (hv : 0 < v) :
    cuspBarProfile (fun w => star (cubicSourceResidualFunction w)) (g 0 0 / g 1 0) v =
      reflectedCuspProfile (-1 / (g 1 0) ^ 2) (‖g 1 0‖ ^ 2)
        (cuspZProfile (fun w => star (cubicSourceResidualFunction (g • w))) (-g 1 1 / g 1 0)) v := by
  have hd : 0 < (‖g 1 0‖ ^ 2 * v)⁻¹ := by positivity
  rw [cuspBarProfile_positive _ _ _ hv, reflectedCuspProfile, cuspZProfile_positive _ _ _ hd,
    conjugate_cubicSourceResidualFunction_cusp_derivative g hc v hv]
  have hp : (v : ℂ) ^ (-2 : ℂ) = ((v : ℂ) ^ 2)⁻¹ := by
    rw [Complex.cpow_neg, Complex.cpow_ofNat]
  rw [hp]
  simp only [one_div]
  ring

/-- Complex conjugation exchanges the two real-coordinate Wirtinger derivatives. -/
lemma horizontalWirtingerZ_conjugate (f : ℂ → ℂ) (z : ℂ) (hf : DifferentiableAt ℝ f z) :
    horizontalWirtingerZ (fun w => star (f w)) z = star (horizontalWirtingerBar f z) := by
  have hline (direction : ℂ) : DifferentiableAt ℝ
      (fun t : ℝ => f (z + (t : ℂ) * direction)) 0 := by
    have hp : DifferentiableAt ℝ (fun t : ℝ => z + (t : ℂ) * direction) 0 := by fun_prop
    have hf' : DifferentiableAt ℝ f (z + (0 : ℂ) * direction) := by simpa only [zero_mul, add_zero] using hf
    exact hf'.comp 0 hp
  have hstar (direction : ℂ) :
      deriv (fun t : ℝ => star (f (z + (t : ℂ) * direction))) 0 =
        star (deriv (fun t : ℝ => f (z + (t : ℂ) * direction)) 0) :=
    (Complex.conjCLE.hasFDerivAt.comp_hasDerivAt 0 (hline direction).hasDerivAt).deriv
  have h1 := hstar 1
  simp only [mul_one] at h1
  rw [horizontalWirtingerZ, horizontalWirtingerBar, h1, hstar Complex.I]
  have hhalf : star (1 / 2 : ℂ) = (1 / 2 : ℂ) := by norm_num
  have hI : star Complex.I = -Complex.I := Complex.conj_I
  rw [star_mul, star_add, star_mul, hhalf, hI]
  ring

lemma ramifiedSource_horizontal_differentiableAt (t : O) (v : ℝ) (hv : 0 < v) (z : ℂ) :
    DifferentiableAt ℝ (fun w => ramifiedSourceFunction t (upperPoint w v hv)) z := by
  have hf := cubicSourceResidualFunction_translate_coordinate_differentiableAt
    (integralComplexMatrix (lowerCuspMatrix t)) (v, z) hv
  have hp : DifferentiableAt ℝ (fun w : ℂ => (v, w)) z := by fun_prop
  simpa only [Function.comp_def, ramifiedSourceFunction, cuspCoordinateLift_positive v _ hv] using hf.comp z hp

lemma conjugateRamifiedSource_zProfile (side : Bool) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    cuspZProfile (fun w => star (ramifiedSourceFunction (ramifiedCuspRoot side : O) w)) z v =
      star (cuspBarProfile (ramifiedSourceFunction (ramifiedCuspRoot side : O)) z v) := by
  rw [cuspZProfile_positive _ _ _ hv, cuspBarProfile_positive _ _ _ hv]
  exact horizontalWirtingerZ_conjugate _ z (ramifiedSource_horizontal_differentiableAt _ v hv z)

theorem conjugateRamifiedSource_zProfile_continuousOn (side : Bool) (z : ℂ) :
    ContinuousOn (cuspZProfile (fun w => star (ramifiedSourceFunction (ramifiedCuspRoot side : O) w)) z)
      (Set.Ioi 0) := by
  apply (ramifiedSource_barProfile_continuousOn side z).star.congr
  intro v hv
  exact conjugateRamifiedSource_zProfile side z v hv

theorem conjugateRamifiedSource_zProfile_exponential_decay (side : Bool) (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, a ≤ v → ∀ z : ℂ,
      ‖cuspZProfile (fun w => star (ramifiedSourceFunction (ramifiedCuspRoot side : O) w)) z v‖ ≤
        C * Real.exp (-(residualBesselDecayRate / 3) * v) := by
  obtain ⟨C, hC, hb⟩ := ramifiedSource_wirtingerBar_exponential_decay side a ha
  refine ⟨C, hC, ?_⟩
  intro v hv z
  rw [conjugateRamifiedSource_zProfile side z v (ha.trans_le hv), norm_star,
    cuspBarProfile_positive _ _ _ (ha.trans_le hv)]
  exact hb v (ha.trans_le hv) hv z

open Asymptotics

lemma reflectedCuspProfile_mellin (f : ℝ → ℂ) (A s : ℂ) (Q : ℝ) (hQ : 0 < Q) :
    mellin (reflectedCuspProfile A Q f) s = A * (Q : ℂ) ^ (2 - s) * mellin f (2 - s) := by
  change mellin (fun v => A • ((v : ℂ) ^ (-2 : ℂ) • f ((Q * v)⁻¹))) s = _
  rw [mellin_const_smul, mellin_cpow_smul,
    mellin_comp_mul_left (fun v => f v⁻¹) _ hQ, mellin_comp_inv]
  simp only [smul_eq_mul, show -(s + (-2 : ℂ)) = 2 - s by ring]
  ring

lemma reflectedCuspProfile_mellinConvergent (f : ℝ → ℂ) (A s : ℂ) (Q : ℝ)
    (hQ : 0 < Q) (hf : MellinConvergent f (2 - s)) :
    MellinConvergent (reflectedCuspProfile A Q f) s := by
  have hinv : MellinConvergent (fun v : ℝ => f v⁻¹) (s - 2) := by
    have he := (MellinConvergent.comp_rpow (f := f) (s := s - 2) (a := -1) (by norm_num)).mpr
      (show MellinConvergent f ((s - 2) / (-1 : ℝ)) by
        simpa only [show ((s - 2) / (-1 : ℝ) : ℂ) = 2 - s by push_cast; ring] using hf)
    simpa only [Real.rpow_neg_one] using he
  have hscale := (MellinConvergent.comp_mul_left (f := fun v : ℝ => f v⁻¹) (s := s - 2) hQ).mpr hinv
  have hpow := (MellinConvergent.cpow_smul (f := fun v : ℝ => f (Q * v)⁻¹) (s := s) (a := -2)).mpr
    (by simpa only [sub_eq_add_neg] using hscale)
  unfold reflectedCuspProfile
  convert! hpow.const_smul A using 1

def truncatedCuspProfile (a : ℝ) (f : ℝ → ℂ) (v : ℝ) : ℂ := if a < v then f v else 0

lemma truncatedCuspProfile_eventually_top (a : ℝ) (f : ℝ → ℂ) :
    truncatedCuspProfile a f =ᶠ[atTop] f := by
  filter_upwards [eventually_gt_atTop a] with v hv
  exact if_pos hv

lemma truncatedCuspProfile_eventually_zero (a : ℝ) (ha : 0 < a) (f : ℝ → ℂ) :
    truncatedCuspProfile a f =ᶠ[𝓝[>] 0] 0 := by
  filter_upwards [(eventually_lt_nhds ha).filter_mono nhdsWithin_le_nhds] with v hv
  exact if_neg (not_lt_of_ge hv.le)

lemma truncatedCuspProfile_locallyIntegrable (a : ℝ) (ha : 0 < a) (f : ℝ → ℂ)
    (hf : ContinuousOn f (Set.Ioi 0)) : LocallyIntegrable (truncatedCuspProfile a f) volume := by
  have hc : Continuous (fun v : ℝ => f (max a v)) := hf.comp_continuous
    (continuous_const.max continuous_id) (fun v => ha.trans_le (le_max_left a v))
  have he : truncatedCuspProfile a f = (Set.Ioi a).indicator (fun v : ℝ => f (max a v)) := by
    funext v
    by_cases hv : a < v
    · simp [truncatedCuspProfile, Set.indicator, hv, max_eq_right hv.le]
    · simp [truncatedCuspProfile, Set.indicator, hv]
  rw [he]
  exact hc.locallyIntegrable.indicator measurableSet_Ioi

lemma truncatedCuspProfile_mellin_entire (a decay : ℝ) (ha : 0 < a) (hd : 0 < decay)
    (f : ℝ → ℂ) (hf : ContinuousOn f (Set.Ioi 0))
    (hbound : f =O[atTop] (fun v : ℝ => Real.exp (-decay * v))) :
    (∀ s : ℂ, MellinConvergent (truncatedCuspProfile a f) s) ∧
      Differentiable ℂ (mellin (truncatedCuspProfile a f)) := by
  have hlocal := (truncatedCuspProfile_locallyIntegrable a ha f hf).locallyIntegrableOn (Set.Ioi 0)
  have htop : truncatedCuspProfile a f =O[atTop] (fun v : ℝ => Real.exp (-decay * v)) :=
    hbound.congr' (truncatedCuspProfile_eventually_top a f).symm EventuallyEq.rfl
  have hzero (b : ℝ) : truncatedCuspProfile a f =O[𝓝[>] 0] (fun v : ℝ => v ^ (-b)) :=
    (Asymptotics.isBigO_zero (fun v : ℝ => v ^ (-b)) (𝓝[>] 0)).congr'
      (truncatedCuspProfile_eventually_zero a ha f).symm EventuallyEq.rfl
  exact ⟨fun s => mellinConvergent_of_isBigO_rpow_exp hd hlocal htop (hzero (s.re - 1)) (by linarith),
    fun s => mellin_differentiableAt_of_isBigO_rpow_exp hd hlocal htop (hzero (s.re - 1)) (by linarith)⟩

/-- A cusp and its reflected cusp split into two exponentially decaying tails. -/
lemma cusp_truncation_reflection_ae (f g : ℝ → ℂ) (A : ℂ) (Q : ℝ) (hQ : 0 < Q)
    (hfg : ∀ v : ℝ, 0 < v → f v = reflectedCuspProfile A Q g v) :
    f =ᵐ[volume.restrict (Set.Ioi 0)] (fun v => truncatedCuspProfile 1 f v +
      reflectedCuspProfile A Q (truncatedCuspProfile (1 / Q) g) v) := by
  have hn : ∀ᵐ v : ℝ ∂volume.restrict (Set.Ioi 0), v ≠ 1 := ae_restrict_of_ae (Measure.ae_ne volume 1)
  filter_upwards [ae_restrict_mem measurableSet_Ioi, hn] with v hv hv1
  have hrel : 1 / Q < (Q * v)⁻¹ ↔ v < 1 := by
    rw [inv_eq_one_div, div_lt_div_iff₀ hQ (mul_pos hQ hv)]
    simp only [one_mul]
    constructor
    · intro he
      by_contra hn
      have hm := mul_le_mul_of_nonneg_left (le_of_not_gt hn) hQ.le
      linarith only [he, hm]
    · intro he
      simpa only [mul_one] using mul_lt_mul_of_pos_left he hQ
  by_cases hhi : 1 < v
  · have hlo : ¬ 1 / Q < (Q * v)⁻¹ := fun hh => not_lt_of_ge hhi.le (hrel.mp hh)
    simp only [truncatedCuspProfile, if_pos hhi, reflectedCuspProfile, if_neg hlo, mul_zero, add_zero]
  · have hlo : 1 / Q < (Q * v)⁻¹ := hrel.mpr (lt_of_le_of_ne (le_of_not_gt hhi) hv1)
    simp only [truncatedCuspProfile, if_neg hhi, reflectedCuspProfile, if_pos hlo, zero_add]
    exact hfg v hv

/-- Exponential decay at both reflected cusps gives an entire Mellin transform. -/
theorem cusp_mellin_entire (f g : ℝ → ℂ) (A : ℂ) (Q decayF decayG : ℝ)
    (hQ : 0 < Q) (hF : 0 < decayF) (hG : 0 < decayG)
    (hf : ContinuousOn f (Set.Ioi 0)) (hg : ContinuousOn g (Set.Ioi 0))
    (hfbound : f =O[atTop] (fun v : ℝ => Real.exp (-decayF * v)))
    (hgbound : g =O[atTop] (fun v : ℝ => Real.exp (-decayG * v)))
    (hfg : ∀ v : ℝ, 0 < v → f v = reflectedCuspProfile A Q g v) :
    (∀ s : ℂ, MellinConvergent f s) ∧ Differentiable ℂ (mellin f) := by
  obtain ⟨hfc, hfd⟩ := truncatedCuspProfile_mellin_entire 1 decayF (by norm_num) hF f hf hfbound
  obtain ⟨hgc, hgd⟩ := truncatedCuspProfile_mellin_entire (1 / Q) decayG (by positivity) hG g hg hgbound
  have hae := cusp_truncation_reflection_ae f g A Q hQ hfg
  have hm (s : ℂ) : HasMellin f s
      (mellin (truncatedCuspProfile 1 f) s +
        A * (Q : ℂ) ^ (2 - s) * mellin (truncatedCuspProfile (1 / Q) g) (2 - s)) := by
    have hr := reflectedCuspProfile_mellinConvergent (truncatedCuspProfile (1 / Q) g) A s Q hQ (hgc (2 - s))
    have hsum := hasMellin_add (hfc s) hr
    constructor
    · apply hsum.1.congr
      filter_upwards [hae] with v hv
      exact congrArg (fun z : ℂ => (v : ℂ) ^ (s - 1) • z) hv.symm
    · have he : mellin f s = mellin (fun v => truncatedCuspProfile 1 f v +
          reflectedCuspProfile A Q (truncatedCuspProfile (1 / Q) g) v) s := by
        unfold mellin
        apply integral_congr_ae
        filter_upwards [hae] with v hv
        rw [hv]
      rw [he, hsum.2, reflectedCuspProfile_mellin _ _ _ _ hQ]
  refine ⟨fun s => (hm s).1, ?_⟩
  have he : mellin f = fun s : ℂ => mellin (truncatedCuspProfile 1 f) s +
      A * (Q : ℂ) ^ (2 - s) * mellin (truncatedCuspProfile (1 / Q) g) (2 - s) :=
    funext (fun s => (hm s).2)
  rw [he]
  letI : NeZero (Q : ℂ) := ⟨Complex.ofReal_ne_zero.mpr hQ.ne'⟩
  have hp := (differentiable_const_cpow_of_neZero (Q : ℂ)).comp
    ((differentiable_const (2 : ℂ)).sub differentiable_id)
  exact hfd.add (((differentiable_const A).mul hp).mul
    (hgd.comp ((differentiable_const (2 : ℂ)).sub differentiable_id)))

lemma horizontalPhaseMultiplier_wirtingerZ (freq : ℂ) :
    (1 / 2 : ℂ) * (horizontalPhaseMultiplier freq 1 -
      Complex.I * horizontalPhaseMultiplier freq Complex.I) = 2 * Real.pi * Complex.I * freq := by
  simp only [horizontalPhaseMultiplier, mul_one, star_mul, Complex.star_def, Complex.conj_I]
  ring_nf
  norm_num [Complex.I_sq, Complex.I_pow_three]
  ring

theorem traceFourierSeries_wirtingerZ {ι : Type*} (freq a : ι → ℂ)
    (ha : Summable (fun i => ‖a i‖)) (hfa : Summable (fun i => ‖freq i‖ * ‖a i‖)) (z : ℂ) :
    horizontalWirtingerZ (fun w => ∑' i, a i * tracePhase (freq i * w)) z =
      ∑' i, (2 * Real.pi * Complex.I * freq i) * (a i * tracePhase (freq i * z)) := by
  have h1 := (traceFourierSeries_hasDerivAt freq a ha hfa z 1 0).deriv
  have hI := (traceFourierSeries_hasDerivAt freq a ha hfa z Complex.I 0).deriv
  simp only [mul_one, Complex.ofReal_zero, zero_mul, add_zero] at h1 hI
  rw [horizontalWirtingerZ, h1, hI]
  have hs1 := traceFourierSeries_directional_summable freq a hfa z 1
  have hsI := (traceFourierSeries_directional_summable freq a hfa z Complex.I).mul_left Complex.I
  rw [← tsum_mul_left, ← hs1.tsum_sub hsI, ← tsum_mul_left]
  apply tsum_congr
  intro i
  linear_combination (a i * tracePhase (freq i * z)) * horizontalPhaseMultiplier_wirtingerZ (freq i)

lemma horizontalWirtingerBar_conjugate (f : ℂ → ℂ) (z : ℂ) (hf : DifferentiableAt ℝ f z) :
    horizontalWirtingerBar (fun w => star (f w)) z = star (horizontalWirtingerZ f z) := by
  have he := congrArg star (horizontalWirtingerZ_conjugate (fun w => star (f w)) z
    (Complex.conjCLE.differentiableAt.comp z hf))
  simpa only [star_star] using he.symm

def sourceZBesselCoefficient (h : O) : ℂ :=
  (2 * Real.pi * Complex.I * cuspFrequency h) * rationalSourceResidualFourierCoefficient h

lemma sourceZBesselCoefficient_subexponential (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : O, h ≠ 0 →
      ‖sourceZBesselCoefficient h‖ ≤ C * Real.exp (ε * ‖cuspFrequency h‖) := by
  apply cubicBesselCoefficient_linearWeight_subexponential _ _
    rationalSourceResidualFourierCoefficient_subexponential (2 * Real.pi) (by positivity) _ ε hε
  intro h hh
  exact le_of_eq (by norm_num [norm_mul, abs_of_pos Real.pi_pos])

theorem cubicSource_wirtingerZ_bessel (v : ℝ) (hv : 0 < v) (z : ℂ) :
    horizontalWirtingerZ (fun w => cubicSourceResidualFunction (upperPoint w v hv)) z =
      ∑' h : O, cubicBesselTerm sourceZBesselCoefficient h (v, z) := by
  have he : (fun w => cubicSourceResidualFunction (upperPoint w v hv)) =
      fun w => ∑' h : O, rationalSourceModeAmplitude v h * tracePhase (cuspFrequency h * w) :=
    funext (cubicSourceResidualFunction_fourier_expansion v hv)
  rw [he, traceFourierSeries_wirtingerZ _ _ (rationalSourceModeAmplitude_summable v hv)
    (rationalSourceModeAmplitude_frequency_summable v hv)]
  apply tsum_congr
  intro h
  by_cases hh : h = 0
  · subst h
    simp only [cuspFrequency, map_zero, zero_div, mul_zero, zero_mul,
      cubicBesselTerm, cubicBesselAmplitude, if_true]
  · rw [rationalSourceModeAmplitude_bessel v hv h hh]
    simp only [cubicBesselTerm, cubicBesselAmplitude, if_neg hh, sourceZBesselCoefficient, mul_assoc]

lemma cubicSource_horizontal_differentiableAt (v : ℝ) (hv : 0 < v) (z : ℂ) :
    DifferentiableAt ℝ (fun w => cubicSourceResidualFunction (upperPoint w v hv)) z := by
  have hf := cubicSourceResidualFunction_coordinate_differentiableAt (v, z) hv
  have hp : DifferentiableAt ℝ (fun w : ℂ => (v, w)) z := by fun_prop
  simpa only [Function.comp_def, cuspCoordinateLift_positive v _ hv] using hf.comp z hp

theorem cubicSource_zProfile_continuousOn (z : ℂ) :
    ContinuousOn (cuspZProfile cubicSourceResidualFunction z) (Set.Ioi 0) := by
  intro v hv
  change 0 < v at hv
  have hs := (cubicBesselSeries_hasFDerivAt sourceZBesselCoefficient
    sourceZBesselCoefficient_subexponential (v, z) hv).differentiableAt
  have hp : DifferentiableAt ℝ (fun y : ℝ => (y, z)) v := by fun_prop
  apply ContinuousAt.continuousWithinAt
  apply (hs.comp v hp).continuousAt.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hv] with y hy
  rw [cuspZProfile_positive _ _ _ hy, cubicSource_wirtingerZ_bessel y hy z]
  rfl

theorem cubicSource_zProfile_exponential_decay (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, a ≤ v → ∀ z : ℂ,
      ‖cuspZProfile cubicSourceResidualFunction z v‖ ≤ C * Real.exp (-residualBesselDecayRate * v) := by
  obtain ⟨C, hC, hb⟩ := cubicBesselSeries_exponential_decay sourceZBesselCoefficient
    sourceZBesselCoefficient_subexponential a ha
  refine ⟨C, hC, ?_⟩
  intro v hv z
  rw [cuspZProfile_positive _ _ _ (ha.trans_le hv), cubicSource_wirtingerZ_bessel v (ha.trans_le hv) z]
  exact hb v hv z

lemma conjugateSource_barProfile (z : ℂ) (v : ℝ) (hv : 0 < v) :
    cuspBarProfile (fun w => star (cubicSourceResidualFunction w)) z v =
      star (cuspZProfile cubicSourceResidualFunction z v) := by
  rw [cuspBarProfile_positive _ _ _ hv, cuspZProfile_positive _ _ _ hv]
  exact horizontalWirtingerBar_conjugate _ z (cubicSource_horizontal_differentiableAt v hv z)

theorem conjugateSource_barProfile_continuousOn (z : ℂ) :
    ContinuousOn (cuspBarProfile (fun w => star (cubicSourceResidualFunction w)) z) (Set.Ioi 0) := by
  apply (cubicSource_zProfile_continuousOn z).star.congr
  intro v hv
  exact conjugateSource_barProfile z v hv

theorem conjugateSource_barProfile_exponential_decay (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, a ≤ v → ∀ z : ℂ,
      ‖cuspBarProfile (fun w => star (cubicSourceResidualFunction w)) z v‖ ≤
        C * Real.exp (-residualBesselDecayRate * v) := by
  obtain ⟨C, hC, hb⟩ := cubicSource_zProfile_exponential_decay a ha
  refine ⟨C, hC, ?_⟩
  intro v hv z
  rw [conjugateSource_barProfile z v (ha.trans_le hv), norm_star]
  exact hb v hv z

theorem conjugateSource_barProfile_isBigO (z : ℂ) :
    cuspBarProfile (fun w => star (cubicSourceResidualFunction w)) z =O[atTop]
      (fun v : ℝ => Real.exp (-residualBesselDecayRate * v)) := by
  obtain ⟨C, hC, hb⟩ := conjugateSource_barProfile_exponential_decay 1 (by norm_num)
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with v hv
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hb v hv z

theorem conjugateRamifiedSource_zProfile_isBigO (side : Bool) (z : ℂ) :
    cuspZProfile (fun w => star (ramifiedSourceFunction (ramifiedCuspRoot side : O) w)) z =O[atTop]
      (fun v : ℝ => Real.exp (-(residualBesselDecayRate / 3) * v)) := by
  obtain ⟨C, hC, hb⟩ := conjugateRamifiedSource_zProfile_exponential_decay side 1 (by norm_num)
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with v hv
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hb v hv z

/-- The two primitive ramified cusp derivative profiles have entire Mellin transforms. -/
theorem conjugateSource_primitive_cusp_mellin_entire (side : Bool) :
    (∀ s : ℂ, MellinConvergent (cuspBarProfile (fun w => star (cubicSourceResidualFunction w))
      (ringComplex (ramifiedCuspRoot side : O))⁻¹) s) ∧
    Differentiable ℂ (mellin (cuspBarProfile (fun w => star (cubicSourceResidualFunction w))
      (ringComplex (ramifiedCuspRoot side : O))⁻¹)) := by
  let g := integralComplexMatrix (lowerCuspMatrix (ramifiedCuspRoot side : O))
  have hg0 : g 0 0 = 1 := by change ringComplex 1 = 1; exact map_one _
  have hgc : g 1 0 = ringComplex (ramifiedCuspRoot side : O) := rfl
  have hc : g 1 0 ≠ 0 := by rw [hgc]; exact ringComplex_ne_zero (Units.ne_zero _)
  have he := cusp_mellin_entire
    (cuspBarProfile (fun w => star (cubicSourceResidualFunction w)) (g 0 0 / g 1 0))
    (cuspZProfile (fun w => star (ramifiedSourceFunction (ramifiedCuspRoot side : O) w)) (-g 1 1 / g 1 0))
    (-1 / (g 1 0) ^ 2) (‖g 1 0‖ ^ 2) residualBesselDecayRate (residualBesselDecayRate / 3)
    (sq_pos_of_pos (norm_pos_iff.mpr hc)) residualBesselDecayRate_pos
    (div_pos residualBesselDecayRate_pos (by norm_num))
    (conjugateSource_barProfile_continuousOn _) (conjugateRamifiedSource_zProfile_continuousOn side _)
    (conjugateSource_barProfile_isBigO _) (conjugateRamifiedSource_zProfile_isBigO side _)
    (fun v hv => conjugateSource_barProfile_reflection g hc v hv)
  simpa only [hg0, hgc, one_div] using he

/-- Coordinates modulo three retain the nilpotent direction of the ramified residue ring. -/
def cuspResidue (x : O) : ZMod 3 × ZMod 3 :=
  ((Coordinates.coords x).1, (Coordinates.coords x).2)

def cuspResidueMul (x y : ZMod 3 × ZMod 3) : ZMod 3 × ZMod 3 :=
  (x.1 * y.1 - x.2 * y.2, x.1 * y.2 + x.2 * y.1 - x.2 * y.2)

lemma cuspResidue_eval (a b : ℤ) : cuspResidue (Coordinates.eval a b) = ((a : ZMod 3), (b : ZMod 3)) := by
  simp only [cuspResidue, Coordinates.coords_eval]

lemma cuspResidue_intCast (a : ℤ) : cuspResidue (a : O) = ((a : ZMod 3), 0) := by
  simpa only [Coordinates.eval, Int.cast_zero, zero_mul, add_zero] using cuspResidue_eval a 0

lemma cuspResidue_zero : cuspResidue (0 : O) = (0, 0) := by simpa only [Int.cast_zero] using cuspResidue_intCast 0

lemma cuspResidue_one : cuspResidue (1 : O) = (1, 0) := by simpa only [Int.cast_one] using cuspResidue_intCast 1

lemma cuspResidue_add (x y : O) : cuspResidue (x + y) =
    ((cuspResidue x).1 + (cuspResidue y).1, (cuspResidue x).2 + (cuspResidue y).2) := by
  have he : x + y = Coordinates.eval ((Coordinates.coords x).1 + (Coordinates.coords y).1)
      ((Coordinates.coords x).2 + (Coordinates.coords y).2) := by
    nth_rw 1 [← Coordinates.eval_coords x, ← Coordinates.eval_coords y]
    simp only [Coordinates.eval, Int.cast_add]
    ring
  rw [he, cuspResidue_eval]
  simp only [cuspResidue, Int.cast_add]

lemma cuspResidue_neg (x : O) : cuspResidue (-x) = (-(cuspResidue x).1, -(cuspResidue x).2) := by
  have he : -x = Coordinates.eval (-(Coordinates.coords x).1) (-(Coordinates.coords x).2) := by
    nth_rw 1 [← Coordinates.eval_coords x]
    simp only [Coordinates.eval, Int.cast_neg]
    ring
  rw [he, cuspResidue_eval]
  simp only [cuspResidue, Int.cast_neg]

lemma cuspResidue_mul (x y : O) : cuspResidue (x * y) = cuspResidueMul (cuspResidue x) (cuspResidue y) := by
  calc
    _ = cuspResidue (Coordinates.eval (Coordinates.coords x).1 (Coordinates.coords x).2 *
        Coordinates.eval (Coordinates.coords y).1 (Coordinates.coords y).2) := by rw [Coordinates.eval_coords, Coordinates.eval_coords]
    _ = _ := by
      rw [Coordinates.eval_mul, cuspResidue_eval]
      simp only [cuspResidue, cuspResidueMul, Int.cast_add, Int.cast_sub, Int.cast_mul]

def cuspResidueAugmentation (x : O) : ZMod 3 := (cuspResidue x).1 + (cuspResidue x).2

lemma cuspResidueAugmentation_add (x y : O) :
    cuspResidueAugmentation (x + y) = cuspResidueAugmentation x + cuspResidueAugmentation y := by
  simp only [cuspResidueAugmentation, cuspResidue_add]
  ring

lemma cuspResidueAugmentation_neg (x : O) : cuspResidueAugmentation (-x) = -cuspResidueAugmentation x := by
  simp only [cuspResidueAugmentation, cuspResidue_neg]
  ring

lemma cuspResidueAugmentation_mul (x y : O) :
    cuspResidueAugmentation (x * y) = cuspResidueAugmentation x * cuspResidueAugmentation y := by
  simp only [cuspResidueAugmentation, cuspResidue_mul, cuspResidueMul]
  have h3 : (3 : ZMod 3) = 0 := rfl
  linear_combination -(cuspResidue x).2 * (cuspResidue y).2 * h3

lemma cuspResidueAugmentation_one : cuspResidueAugmentation (1 : O) = 1 := by
  simp only [cuspResidueAugmentation, cuspResidue_one, add_zero]

/-- A determinant-one column stays nonzero after reduction modulo the ramified prime. -/
lemma cuspResidue_first_column_primitive (M : SL(2, O)) :
    ¬ (cuspResidueAugmentation (M 0 0) = 0 ∧ cuspResidueAugmentation (M 1 0) = 0) := by
  rintro ⟨ha, hc⟩
  have hd : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by simpa only [Matrix.det_fin_two] using M.property
  have he := congrArg cuspResidueAugmentation hd
  simp only [sub_eq_add_neg, cuspResidueAugmentation_add, cuspResidueAugmentation_neg,
    cuspResidueAugmentation_mul, cuspResidueAugmentation_one, ha, hc, zero_mul, mul_zero, neg_zero, add_zero] at he
  exact zero_ne_one he

lemma cuspResidue_omega : cuspResidue omega = (0, 1) := by
  simpa only [Coordinates.eval, Int.cast_zero, Int.cast_one, zero_add, one_mul] using cuspResidue_eval 0 1

lemma cuspResidue_omega_sq : cuspResidue (omega ^ 2) = (-1, -1) := by
  rw [pow_two, cuspResidue_mul, cuspResidue_omega]
  norm_num [cuspResidueMul]

lemma cuspResidue_eq_three_dvd {x y : O} (h : cuspResidue x = cuspResidue y) : (3 : O) ∣ x - y := by
  have ha : (3 : ℤ) ∣ (Coordinates.coords x).1 - (Coordinates.coords y).1 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub (Coordinates.coords y).1 (Coordinates.coords x).1 3).mp
      (congrArg Prod.fst h).symm
  have hb : (3 : ℤ) ∣ (Coordinates.coords x).2 - (Coordinates.coords y).2 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub (Coordinates.coords y).2 (Coordinates.coords x).2 3).mp
      (congrArg Prod.snd h).symm
  obtain ⟨a, ha⟩ := ha
  obtain ⟨b, hb⟩ := hb
  refine ⟨Coordinates.eval a b, ?_⟩
  nth_rw 1 [← Coordinates.eval_coords x, ← Coordinates.eval_coords y]
  have hx : (Coordinates.coords x).1 = (Coordinates.coords y).1 + 3 * a := by omega
  have hy : (Coordinates.coords x).2 = (Coordinates.coords y).2 + 3 * b := by omega
  simp only [Coordinates.eval, hx, hy]
  push_cast
  ring

lemma cuspResidue_intCast_mul (n : ℤ) (x : O) : cuspResidue ((n : O) * x) =
    ((n : ZMod 3) * (cuspResidue x).1, (n : ZMod 3) * (cuspResidue x).2) := by
  rw [cuspResidue_mul, cuspResidue_intCast]
  simp only [cuspResidueMul, zero_mul, sub_zero, add_zero]

def cuspParameter (j : Fin 3) : O := if j = 0 then 0 else if j = 1 then omega else omega ^ 2

def cuspRepresentative (j : Fin 3) : SL(2, O) := lowerCuspMatrix (cuspParameter j)

def cuspResidueParameter (j : Fin 3) : ZMod 3 × ZMod 3 :=
  if j = 0 then (0, 0) else if j = 1 then (0, 1) else (-1, -1)

lemma cuspParameter_residue (j : Fin 3) : cuspResidue (cuspParameter j) = cuspResidueParameter j := by
  fin_cases j <;> simp [cuspParameter, cuspResidueParameter, cuspResidue_zero, cuspResidue_omega, cuspResidue_omega_sq]

def cuspNilpotentUnit (q : ZMod 3) : Oˣ := cuspOmegaUnit ^ q.val

lemma cuspNilpotentUnit_residue (q : ZMod 3) :
    cuspResidue (cuspNilpotentUnit q : O) = (1 - q, q) := by
  fin_cases q
  · change cuspResidue ((cuspOmegaUnit : O) ^ 0) = (1, 0)
    rw [pow_zero]
    exact cuspResidue_one
  · change cuspResidue ((cuspOmegaUnit : O) ^ 1) = (0, 1)
    rw [pow_one, cuspOmegaUnit_val]
    exact cuspResidue_omega
  · change cuspResidue (omega ^ 2) = _
    rw [cuspResidue_omega_sq]
    rfl

def cuspResidueColumn (g : SL(2, ZMod 3)) (j : Fin 3) (q : ZMod 3) (i : Fin 2) : ZMod 3 × ZMod 3 :=
  cuspResidueMul (g i 0 + g i 1 * (cuspResidueParameter j).1, g i 1 * (cuspResidueParameter j).2) (1 - q, q)

lemma cuspModThree_nonzero (x : ZMod 3) (hx : x ≠ 0) : x = 1 ∨ x = -1 := by
  fin_cases x
  · exact (hx rfl).elim
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The coordinate determinant gives three orbits of primitive columns modulo three. -/
theorem cuspResidue_column_classify (a c : ZMod 3 × ZMod 3)
    (hp : ¬ (a.1 + a.2 = 0 ∧ c.1 + c.2 = 0)) :
    ∃ g : SL(2, ZMod 3), ∃ j : Fin 3, ∃ q : ZMod 3,
      cuspResidueColumn g j q 0 = a ∧ cuspResidueColumn g j q 1 = c := by
  by_cases hd : a.1 * c.2 - a.2 * c.1 = 0
  · have hxy : a.1 + a.2 ≠ 0 ∨ c.1 + c.2 ≠ 0 := by
      by_cases hx : a.1 + a.2 = 0
      · exact Or.inr (fun hy => hp ⟨hx, hy⟩)
      · exact Or.inl hx
    have hcop : IsCoprime (a.1 + a.2) (c.1 + c.2) := by
      rcases hxy with hx | hy
      · exact ⟨(a.1 + a.2)⁻¹, 0, by rw [inv_mul_cancel₀ hx, zero_mul, add_zero]⟩
      · exact ⟨0, (c.1 + c.2)⁻¹, by rw [zero_mul, inv_mul_cancel₀ hy, zero_add]⟩
    obtain ⟨g, hg0, hg1, _⟩ := primitiveColumn_congruent_completion (1 : SL(2, ZMod 3))
      (a.1 + a.2) (c.1 + c.2) 1 hcop (one_dvd _) (one_dvd _)
    have hq : ∃ q : ZMod 3, (a.1 + a.2) * q = a.2 ∧ (c.1 + c.2) * q = c.2 := by
      rcases hxy with hx | hy
      · refine ⟨a.2 / (a.1 + a.2), ?_, ?_⟩
        · field_simp
        · field_simp
          linear_combination -hd
      · refine ⟨c.2 / (c.1 + c.2), ?_, ?_⟩
        · field_simp
          linear_combination hd
        · field_simp
    obtain ⟨q, hq0, hq1⟩ := hq
    refine ⟨g, 0, q, ?_, ?_⟩
    · simp only [cuspResidueColumn, cuspResidueParameter, if_true, hg0, mul_zero, add_zero,
        cuspResidueMul, zero_mul, sub_zero]
      apply Prod.ext
      · change (a.1 + a.2) * (1 - q) = a.1
        linear_combination -hq0
      · exact hq0
    · simp only [cuspResidueColumn, cuspResidueParameter, if_true, hg1, mul_zero, add_zero,
        cuspResidueMul, zero_mul, sub_zero]
      apply Prod.ext
      · change (c.1 + c.2) * (1 - q) = c.1
        linear_combination -hq1
      · exact hq1
  · rcases cuspModThree_nonzero _ hd with hdet | hdet
    · let g : SL(2, ZMod 3) := ⟨!![a.1, a.2; c.1, c.2], by
        rw [Matrix.det_fin_two]
        change a.1 * c.2 - a.2 * c.1 = 1
        exact hdet⟩
      refine ⟨g, 1, 0, ?_, ?_⟩ <;> apply Prod.ext <;>
        simp [cuspResidueColumn, cuspResidueParameter, cuspResidueMul, g]
    · let g : SL(2, ZMod 3) := ⟨!![a.1 - a.2, -a.2; c.1 - c.2, -c.2], by
        rw [Matrix.det_fin_two]
        change (a.1 - a.2) * -c.2 - -a.2 * (c.1 - c.2) = 1
        linear_combination -hdet⟩
      refine ⟨g, 2, 0, ?_, ?_⟩ <;> apply Prod.ext <;>
        simp [cuspResidueColumn, cuspResidueParameter, cuspResidueMul, g] <;> ring

lemma sameColumn_inverse_mul {R : Type*} [CommRing R] (M N : SL(2, R))
    (h0 : N 0 0 = M 0 0) (h1 : N 1 0 = M 1 0) :
    (N⁻¹ * M) 0 0 = 1 ∧ (N⁻¹ * M) 1 0 = 0 := by
  have hd : N 0 0 * N 1 1 - N 0 1 * N 1 0 = 1 := by simpa only [Matrix.det_fin_two] using N.property
  have hi00 : (N⁻¹) 0 0 = N 1 1 := by simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  have hi01 : (N⁻¹) 0 1 = -N 0 1 := by simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  have hi10 : (N⁻¹) 1 0 = -N 1 0 := by simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  have hi11 : (N⁻¹) 1 1 = N 0 0 := by simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  constructor
  · change (∑ k : Fin 2, (N⁻¹) 0 k * M k 0) = 1
    rw [Fin.sum_univ_two, hi00, hi01, ← h0, ← h1]
    linear_combination hd
  · change (∑ k : Fin 2, (N⁻¹) 1 k * M k 0) = 0
    rw [Fin.sum_univ_two, hi10, hi11, ← h0, ← h1]
    ring

def rationalReductionThree : SL(2, ℤ) →* SL(2, ZMod 3) :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 3))

lemma rationalReductionThree_apply (r : SL(2, ℤ)) (i j : Fin 2) :
    rationalReductionThree r i j = (r i j : ZMod 3) := rfl

def rationalCuspTranslation (n : ℤ) : SL(2, ℤ) := ⟨!![1, n; 0, 1], by simp [Matrix.det_fin_two]⟩

lemma cuspModThree_unit_lift (x : ZMod 3) (hx : x ≠ 0) :
    ∃ n : ℤ, n ^ 2 = 1 ∧ (n : ZMod 3) = x := by
  rcases cuspModThree_nonzero x hx with h | h
  · exact ⟨1, by norm_num, by simpa only [Int.cast_one] using h.symm⟩
  · exact ⟨-1, by norm_num, by simpa only [Int.cast_neg, Int.cast_one] using h.symm⟩

/-- A signed lift of one nonzero entry lifts the first column; one translation lifts the matrix. -/
theorem rationalReductionThree_surjective : Function.Surjective rationalReductionThree := by
  intro g
  have hcol : ∃ r : SL(2, ℤ), rationalReductionThree r 0 0 = g 0 0 ∧
      rationalReductionThree r 1 0 = g 1 0 := by
    by_cases ha : g 0 0 = 0
    · have hc : g 1 0 ≠ 0 := by
        intro hc
        have hd := g.property
        simp only [Matrix.det_fin_two, ha, hc, zero_mul, mul_zero, sub_zero] at hd
        exact zero_ne_one hd
      obtain ⟨n, hn, hnc⟩ := cuspModThree_unit_lift _ hc
      let r : SL(2, ℤ) := ⟨!![0, -n; n, 0], by
        rw [Matrix.det_fin_two]
        change 0 * 0 - -n * n = 1
        linear_combination hn⟩
      refine ⟨r, ?_, hnc⟩
      change ((0 : ℤ) : ZMod 3) = g 0 0
      simpa only [Int.cast_zero] using ha.symm
    · obtain ⟨n, hn, hnc⟩ := cuspModThree_unit_lift _ ha
      let r : SL(2, ℤ) := ⟨!![n, 0; ((g 1 0).val : ℤ), n], by
        rw [Matrix.det_fin_two]
        change n * n - 0 * ((g 1 0).val : ℤ) = 1
        linear_combination hn⟩
      refine ⟨r, hnc, ?_⟩
      change (((g 1 0).val : ℤ) : ZMod 3) = g 1 0
      simpa only [Int.cast_natCast] using ZMod.natCast_zmod_val (g 1 0)
  obtain ⟨r, hr0, hr1⟩ := hcol
  let K : SL(2, ZMod 3) := (rationalReductionThree r)⁻¹ * g
  obtain ⟨hK0, hK1⟩ := sameColumn_inverse_mul g (rationalReductionThree r) hr0 hr1
  have hK11 : K 1 1 = 1 := by
    have h0 : K 0 0 = 1 := hK0
    have h1 : K 1 0 = 0 := hK1
    have hd : K 0 0 * K 1 1 - K 0 1 * K 1 0 = 1 := by simpa only [Matrix.det_fin_two] using K.property
    rwa [h0, h1, one_mul, mul_zero, sub_zero] at hd
  let T : SL(2, ℤ) := rationalCuspTranslation ((K 0 1).val : ℤ)
  have hT : rationalReductionThree T = K := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j
    · exact hK0.symm
    · change (((K 0 1).val : ℤ) : ZMod 3) = K 0 1
      simpa only [Int.cast_natCast] using ZMod.natCast_zmod_val (K 0 1)
    · exact hK1.symm
    · exact hK11.symm
  refine ⟨r * T, ?_⟩
  rw [map_mul, hT]
  dsimp only [K]
  group

def columnCuspRepresentative (r : SL(2, ℤ)) (j : Fin 3) (q : ZMod 3) : SL(2, O) :=
  rationalEmbedding r * cuspRepresentative j * unitCuspDiagonal (cuspNilpotentUnit q)

lemma columnCuspRepresentative_entry (r : SL(2, ℤ)) (j : Fin 3) (q : ZMod 3) (i : Fin 2) :
    columnCuspRepresentative r j q i 0 =
      ((r i 0 : O) + (r i 1 : O) * cuspParameter j) * (cuspNilpotentUnit q : O) := by
  change (((r : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom O) * !![1, 0; cuspParameter j, 1]) *
    !![(cuspNilpotentUnit q : O), 0; 0, (↑(cuspNilpotentUnit q)⁻¹ : O)]) i 0 = _
  simp [Matrix.mul_apply, Fin.sum_univ_two]

lemma columnCuspRepresentative_residue (r : SL(2, ℤ)) (j : Fin 3) (q : ZMod 3) (i : Fin 2) :
    cuspResidue (columnCuspRepresentative r j q i 0) = cuspResidueColumn (rationalReductionThree r) j q i := by
  rw [columnCuspRepresentative_entry, cuspResidue_mul, cuspResidue_add, cuspResidue_intCast,
    cuspResidue_intCast_mul, cuspParameter_residue, cuspNilpotentUnit_residue]
  simp only [cuspResidueColumn, rationalReductionThree_apply, zero_add]

/-- Every integral cusp belongs to the rational class or one of the two primitive ramified classes. -/
theorem three_cusp_decomposition (M : SL(2, O)) :
    ∃ G : rationalExtension, ∃ j : Fin 3, ∃ T : SL(2, O),
      T 1 0 = 0 ∧ IsUnit (T 0 0) ∧ IsUnit (T 1 1) ∧
        M = (G : SL(2, O)) * cuspRepresentative j * T := by
  obtain ⟨g, j, q, hg0, hg1⟩ := cuspResidue_column_classify (cuspResidue (M 0 0))
    (cuspResidue (M 1 0)) (cuspResidue_first_column_primitive M)
  obtain ⟨r, hr⟩ := rationalReductionThree_surjective g
  let B := columnCuspRepresentative r j q
  have hB0 : cuspResidue (B 0 0) = cuspResidue (M 0 0) := by
    rw [columnCuspRepresentative_residue, hr]
    exact hg0
  have hB1 : cuspResidue (B 1 0) = cuspResidue (M 1 0) := by
    rw [columnCuspRepresentative_residue, hr]
    exact hg1
  have hcop : IsCoprime (M 0 0) (M 1 0) := by
    refine ⟨M 1 1, -M 0 1, ?_⟩
    have hd := M.property
    rw [Matrix.det_fin_two] at hd
    linear_combination hd
  obtain ⟨N, hN0, hN1, hNB⟩ := exists_congruent_cusp_completion B (M 0 0) (M 1 0) hcop
    (cuspResidue_eq_three_dvd hB0.symm) (cuspResidue_eq_three_dvd hB1.symm)
  let G : rationalExtension := ⟨(N * B⁻¹) * rationalEmbedding r, ⟨⟨N * B⁻¹, hNB⟩, r, rfl⟩⟩
  let T : SL(2, O) := unitCuspDiagonal (cuspNilpotentUnit q) * (N⁻¹ * M)
  have hT : T 1 0 = 0 := by
    have hz := (sameColumn_inverse_mul M N hN0 hN1).2
    change (∑ k : Fin 2, unitCuspDiagonal (cuspNilpotentUnit q) 1 k * (N⁻¹ * M) k 0) = 0
    rw [Fin.sum_univ_two]
    change 0 * (N⁻¹ * M) 0 0 + (↑(cuspNilpotentUnit q)⁻¹ : O) * (N⁻¹ * M) 1 0 = 0
    rw [hz, mul_zero, zero_mul, add_zero]
  have hd : T 0 0 * T 1 1 = 1 := by
    simpa only [Matrix.det_fin_two, hT, mul_zero, sub_zero] using T.property
  refine ⟨G, j, T, hT, IsUnit.of_mul_eq_one _ hd,
    IsUnit.of_mul_eq_one _ (show T 1 1 * T 0 0 = 1 by simpa only [mul_comm] using hd), ?_⟩
  dsimp only [G, T, B, columnCuspRepresentative]
  group

def sourceBarBesselCoefficient (h : O) : ℂ :=
  (2 * Real.pi * Complex.I * star (cuspFrequency h)) * rationalSourceResidualFourierCoefficient h

lemma sourceBarBesselCoefficient_subexponential (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : O, h ≠ 0 →
      ‖sourceBarBesselCoefficient h‖ ≤ C * Real.exp (ε * ‖cuspFrequency h‖) := by
  apply cubicBesselCoefficient_linearWeight_subexponential _ _
    rationalSourceResidualFourierCoefficient_subexponential (2 * Real.pi) (by positivity) _ ε hε
  intro h hh
  exact le_of_eq (by norm_num [norm_mul, norm_star, abs_of_pos Real.pi_pos])

theorem cubicSource_wirtingerBar_bessel (v : ℝ) (hv : 0 < v) (z : ℂ) :
    horizontalWirtingerBar (fun w => cubicSourceResidualFunction (upperPoint w v hv)) z =
      ∑' h : O, cubicBesselTerm sourceBarBesselCoefficient h (v, z) := by
  have he : (fun w => cubicSourceResidualFunction (upperPoint w v hv)) =
      fun w => ∑' h : O, rationalSourceModeAmplitude v h * tracePhase (cuspFrequency h * w) :=
    funext (cubicSourceResidualFunction_fourier_expansion v hv)
  rw [he, traceFourierSeries_wirtingerBar _ _ (rationalSourceModeAmplitude_summable v hv)
    (rationalSourceModeAmplitude_frequency_summable v hv)]
  apply tsum_congr
  intro h
  by_cases hh : h = 0
  · subst h
    simp only [cuspFrequency, map_zero, zero_div, star_zero, mul_zero, zero_mul,
      cubicBesselTerm, cubicBesselAmplitude, if_true]
  · rw [rationalSourceModeAmplitude_bessel v hv h hh]
    simp only [cubicBesselTerm, cubicBesselAmplitude, if_neg hh, sourceBarBesselCoefficient, mul_assoc]

theorem cubicSource_barProfile_continuousOn (z : ℂ) :
    ContinuousOn (cuspBarProfile cubicSourceResidualFunction z) (Set.Ioi 0) := by
  intro v hv
  change 0 < v at hv
  have hs := (cubicBesselSeries_hasFDerivAt sourceBarBesselCoefficient
    sourceBarBesselCoefficient_subexponential (v, z) hv).differentiableAt
  have hp : DifferentiableAt ℝ (fun y : ℝ => (y, z)) v := by fun_prop
  apply ContinuousAt.continuousWithinAt
  apply (hs.comp v hp).continuousAt.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hv] with y hy
  rw [cuspBarProfile_positive _ _ _ hy, cubicSource_wirtingerBar_bessel y hy z]
  rfl

lemma conjugateSource_zProfile (z : ℂ) (v : ℝ) (hv : 0 < v) :
    cuspZProfile (fun w => star (cubicSourceResidualFunction w)) z v =
      star (cuspBarProfile cubicSourceResidualFunction z v) := by
  rw [cuspZProfile_positive _ _ _ hv, cuspBarProfile_positive _ _ _ hv]
  exact horizontalWirtingerZ_conjugate _ z (cubicSource_horizontal_differentiableAt v hv z)

theorem conjugateSource_zProfile_continuousOn (z : ℂ) :
    ContinuousOn (cuspZProfile (fun w => star (cubicSourceResidualFunction w)) z) (Set.Ioi 0) := by
  apply (cubicSource_barProfile_continuousOn z).star.congr
  intro v hv
  exact conjugateSource_zProfile z v hv

theorem conjugateSource_zProfile_isBigO (z : ℂ) :
    cuspZProfile (fun w => star (cubicSourceResidualFunction w)) z =O[atTop]
      (fun v : ℝ => Real.exp (-residualBesselDecayRate * v)) := by
  obtain ⟨C, hC, hb⟩ := cubicBesselSeries_exponential_decay sourceBarBesselCoefficient
    sourceBarBesselCoefficient_subexponential 1 (by norm_num)
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with v hv
  have hp : 0 < v := zero_lt_one.trans_le hv
  rw [conjugateSource_zProfile z v hp, norm_star, cuspBarProfile_positive _ _ _ hp,
    cubicSource_wirtingerBar_bessel v hp z]
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hb v hv z

lemma horizontalWirtingerZ_const_mul (a : ℂ) (f : ℂ → ℂ) (z : ℂ) (hf : DifferentiableAt ℝ f z) :
    horizontalWirtingerZ (fun w => a * f w) z = a * horizontalWirtingerZ f z := by
  have hline (direction : ℂ) : DifferentiableAt ℝ (fun t : ℝ => f (z + (t : ℂ) * direction)) 0 := by
    have hp : DifferentiableAt ℝ (fun t : ℝ => z + (t : ℂ) * direction) 0 := by fun_prop
    have hf' : DifferentiableAt ℝ f (z + (0 : ℂ) * direction) := by simpa only [zero_mul, add_zero] using hf
    exact hf'.comp 0 hp
  have h1 := ((hline 1).hasDerivAt.const_mul a).deriv
  have hI := ((hline Complex.I).hasDerivAt.const_mul a).deriv
  simp only [mul_one] at h1
  rw [horizontalWirtingerZ, h1, hI, horizontalWirtingerZ]
  ring

lemma conjugateSource_translate_horizontal_differentiableAt (g : SL(2, ℂ))
    (v : ℝ) (hv : 0 < v) (z : ℂ) :
    DifferentiableAt ℝ (fun w => star (cubicSourceResidualFunction (g • upperPoint w v hv))) z := by
  have hf := cubicSourceResidualFunction_translate_coordinate_differentiableAt g (v, z) hv
  have hp : DifferentiableAt ℝ (fun w : ℂ => (v, w)) z := by fun_prop
  have hh := Complex.conjCLE.differentiableAt.comp z (hf.comp z hp)
  have he : (fun w => star (cubicSourceResidualFunction (g • upperPoint w v hv))) =
      fun w => Complex.conjCLE (cubicSourceResidualFunction (g • cuspCoordinateLift (v, w))) := by
    funext w
    rw [cuspCoordinateLift_positive v w hv]
    rfl
  rw [he]
  convert! hh using 1

lemma conjugateSource_zProfile_transform (G : rationalExtension) (H : SL(2, ℂ))
    (z : ℂ) (v : ℝ) (hv : 0 < v) :
    cuspZProfile (fun w => star (cubicSourceResidualFunction
      ((integralComplexMatrix (G : SL(2, O)) * H) • w))) z v =
      star (extendedComplexCharacter G) * cuspZProfile (fun w => star (cubicSourceResidualFunction (H • w))) z v := by
  rw [cuspZProfile_positive _ _ _ hv, cuspZProfile_positive _ _ _ hv]
  have he : (fun w : ℂ => star (cubicSourceResidualFunction
      ((integralComplexMatrix (G : SL(2, O)) * H) • upperPoint w v hv))) =
      fun w => star (extendedComplexCharacter G) * star (cubicSourceResidualFunction (H • upperPoint w v hv)) := by
    funext w
    rw [mul_smul, cubicSourceResidualFunction_automorphy G, star_mul]
    exact mul_comm _ _
  rw [he]
  exact horizontalWirtingerZ_const_mul (star (extendedComplexCharacter G))
    (fun w : ℂ => star (cubicSourceResidualFunction (H • upperPoint w v hv))) z
    (conjugateSource_translate_horizontal_differentiableAt H v hv z)

lemma conjugateSource_barProfile_reflection_rational (G : rationalExtension)
    (g H : SL(2, ℂ)) (hfactor : g = integralComplexMatrix (G : SL(2, O)) * H)
    (hc : g 1 0 ≠ 0) (v : ℝ) (hv : 0 < v) :
    cuspBarProfile (fun w => star (cubicSourceResidualFunction w)) (g 0 0 / g 1 0) v =
      reflectedCuspProfile (-star (extendedComplexCharacter G) / (g 1 0) ^ 2) (‖g 1 0‖ ^ 2)
        (cuspZProfile (fun w => star (cubicSourceResidualFunction (H • w))) (-g 1 1 / g 1 0)) v := by
  have hd : 0 < (‖g 1 0‖ ^ 2 * v)⁻¹ := by positivity
  have he : cuspZProfile (fun w => star (cubicSourceResidualFunction (g • w))) (-g 1 1 / g 1 0)
      ((‖g 1 0‖ ^ 2 * v)⁻¹) = star (extendedComplexCharacter G) *
        cuspZProfile (fun w => star (cubicSourceResidualFunction (H • w))) (-g 1 1 / g 1 0)
          ((‖g 1 0‖ ^ 2 * v)⁻¹) := by
    conv_lhs => arg 1; rw [hfactor]
    exact conjugateSource_zProfile_transform G H _ _ hd
  rw [conjugateSource_barProfile_reflection g hc v hv, reflectedCuspProfile, reflectedCuspProfile, he]
  ring

lemma lowerCuspMatrix_zero : lowerCuspMatrix 0 = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

lemma conjugateSource_cuspRepresentative_zProfile_continuousOn (j : Fin 3) (z : ℂ) :
    ContinuousOn (cuspZProfile (fun w => star (cubicSourceResidualFunction
      (integralComplexMatrix (cuspRepresentative j) • w))) z) (Set.Ioi 0) := by
  fin_cases j
  · simpa [cuspRepresentative, cuspParameter, lowerCuspMatrix_zero] using conjugateSource_zProfile_continuousOn z
  · simpa [cuspRepresentative, cuspParameter, ramifiedSourceFunction, ramifiedCuspRoot, cuspOmegaUnit_val] using
      conjugateRamifiedSource_zProfile_continuousOn false z
  · simpa [cuspRepresentative, cuspParameter, ramifiedSourceFunction, ramifiedCuspRoot, cuspOmegaUnit_val] using
      conjugateRamifiedSource_zProfile_continuousOn true z

lemma conjugateSource_cuspRepresentative_zProfile_decay (j : Fin 3) (z : ℂ) :
    ∃ δ : ℝ, 0 < δ ∧ cuspZProfile (fun w => star (cubicSourceResidualFunction
      (integralComplexMatrix (cuspRepresentative j) • w))) z =O[atTop]
        (fun v : ℝ => Real.exp (-δ * v)) := by
  fin_cases j
  · refine ⟨residualBesselDecayRate, residualBesselDecayRate_pos, ?_⟩
    simpa [cuspRepresentative, cuspParameter, lowerCuspMatrix_zero] using conjugateSource_zProfile_isBigO z
  · refine ⟨residualBesselDecayRate / 3, div_pos residualBesselDecayRate_pos (by norm_num), ?_⟩
    simpa [cuspRepresentative, cuspParameter, ramifiedSourceFunction, ramifiedCuspRoot, cuspOmegaUnit_val] using
      conjugateRamifiedSource_zProfile_isBigO false z
  · refine ⟨residualBesselDecayRate / 3, div_pos residualBesselDecayRate_pos (by norm_num), ?_⟩
    simpa [cuspRepresentative, cuspParameter, ramifiedSourceFunction, ramifiedCuspRoot, cuspOmegaUnit_val] using
      conjugateRamifiedSource_zProfile_isBigO true z

theorem conjugateSource_three_cusp_mellin_entire (G : rationalExtension) (j : Fin 3)
    (g : SL(2, ℂ)) (hfactor : g = integralComplexMatrix (G : SL(2, O)) * integralComplexMatrix (cuspRepresentative j))
    (hc : g 1 0 ≠ 0) :
    (∀ s : ℂ, MellinConvergent (cuspBarProfile (fun w => star (cubicSourceResidualFunction w)) (g 0 0 / g 1 0)) s) ∧
      Differentiable ℂ (mellin (cuspBarProfile (fun w => star (cubicSourceResidualFunction w)) (g 0 0 / g 1 0))) := by
  obtain ⟨δ, hδ, hb⟩ := conjugateSource_cuspRepresentative_zProfile_decay j (-g 1 1 / g 1 0)
  exact cusp_mellin_entire _ _ (-star (extendedComplexCharacter G) / (g 1 0) ^ 2)
    (‖g 1 0‖ ^ 2) residualBesselDecayRate δ (sq_pos_of_pos (norm_pos_iff.mpr hc)) residualBesselDecayRate_pos hδ
    (conjugateSource_barProfile_continuousOn _) (conjugateSource_cuspRepresentative_zProfile_continuousOn j _)
    (conjugateSource_barProfile_isBigO _) hb
    (fun v hv => conjugateSource_barProfile_reflection_rational G g _ hfactor hc v hv)

lemma upperTriangular_right_cusp_ratio (g T : SL(2, ℂ)) (hT : T 1 0 = 0)
    (hc : (g * T) 1 0 ≠ 0) :
    g 1 0 ≠ 0 ∧ (g * T) 0 0 / (g * T) 1 0 = g 0 0 / g 1 0 := by
  have hcol (i : Fin 2) : (g * T) i 0 = g i 0 * T 0 0 := by
    change (∑ k : Fin 2, g i k * T k 0) = _
    rw [Fin.sum_univ_two, hT, mul_zero, add_zero]
  have hn : g 1 0 * T 0 0 ≠ 0 := by rwa [hcol] at hc
  have hg := (mul_ne_zero_iff.mp hn).1
  have ht := (mul_ne_zero_iff.mp hn).2
  refine ⟨hg, ?_⟩
  rw [hcol, hcol]
  field_simp

/-- Every integral finite cusp has an entire derivative Mellin transform. -/
theorem conjugateSource_integral_cusp_mellin_entire (M : SL(2, O)) (hc : M 1 0 ≠ 0) :
    (∀ s : ℂ, MellinConvergent (cuspBarProfile (fun w => star (cubicSourceResidualFunction w))
      (ringComplex (M 0 0) / ringComplex (M 1 0))) s) ∧
      Differentiable ℂ (mellin (cuspBarProfile (fun w => star (cubicSourceResidualFunction w))
        (ringComplex (M 0 0) / ringComplex (M 1 0)))) := by
  obtain ⟨G, j, T, hT, _, _, hM⟩ := three_cusp_decomposition M
  let g := integralComplexMatrix (G : SL(2, O)) * integralComplexMatrix (cuspRepresentative j)
  have he : integralComplexMatrix M = g * integralComplexMatrix T := by rw [hM, map_mul, map_mul]
  have ht : integralComplexMatrix T 1 0 = 0 := by
    change ringComplex (T 1 0) = 0
    rw [hT, map_zero]
  have hmc : (g * integralComplexMatrix T) 1 0 ≠ 0 := by
    rw [← he]
    exact ringComplex_ne_zero hc
  obtain ⟨hg, hratio⟩ := upperTriangular_right_cusp_ratio g (integralComplexMatrix T) ht hmc
  have hh := conjugateSource_three_cusp_mellin_entire G j g rfl hg
  rw [← hratio, ← he] at hh
  exact hh

theorem cusp_mellin_reflection_of_identity (f g : ℝ → ℂ) (A s : ℂ) (Q : ℝ) (hQ : 0 < Q)
    (hfg : ∀ v : ℝ, 0 < v → f v = reflectedCuspProfile A Q g v) :
    mellin f s = A * (Q : ℂ) ^ (2 - s) * mellin g (2 - s) := by
  rw [← reflectedCuspProfile_mellin g A s Q hQ]
  unfold mellin
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  dsimp only
  rw [hfg v hv]

lemma reflectedCuspProfile_involution (f : ℝ → ℂ) (A : ℂ) (hA : A ≠ 0)
    (Q : ℝ) (hQ : 0 < Q) (v : ℝ) (hv : 0 < v) :
    reflectedCuspProfile (A⁻¹ / (Q : ℂ) ^ 2) Q (reflectedCuspProfile A Q f) v = f v := by
  have harg : (Q * (Q * v)⁻¹)⁻¹ = v := by field_simp
  have hp (t : ℝ) : (t : ℂ) ^ (-2 : ℂ) = ((t : ℂ) ^ 2)⁻¹ := by
    rw [Complex.cpow_neg, Complex.cpow_ofNat]
  rw [reflectedCuspProfile, reflectedCuspProfile, harg, hp, hp]
  simp only [Complex.ofReal_inv, Complex.ofReal_mul]
  field_simp [hA, Complex.ofReal_ne_zero.mpr hQ.ne', Complex.ofReal_ne_zero.mpr hv.ne']

theorem cusp_mellin_entire_both (f g : ℝ → ℂ) (A : ℂ) (hA : A ≠ 0) (Q decayF decayG : ℝ)
    (hQ : 0 < Q) (hF : 0 < decayF) (hG : 0 < decayG)
    (hf : ContinuousOn f (Set.Ioi 0)) (hg : ContinuousOn g (Set.Ioi 0))
    (hfbound : f =O[atTop] (fun v : ℝ => Real.exp (-decayF * v)))
    (hgbound : g =O[atTop] (fun v : ℝ => Real.exp (-decayG * v)))
    (hfg : ∀ v : ℝ, 0 < v → f v = reflectedCuspProfile A Q g v) :
    ((∀ s : ℂ, MellinConvergent f s) ∧ Differentiable ℂ (mellin f)) ∧
      ((∀ s : ℂ, MellinConvergent g s) ∧ Differentiable ℂ (mellin g)) := by
  have hgf (v : ℝ) (hv : 0 < v) : g v = reflectedCuspProfile (A⁻¹ / (Q : ℂ) ^ 2) Q f v := by
    calc
      _ = reflectedCuspProfile (A⁻¹ / (Q : ℂ) ^ 2) Q (reflectedCuspProfile A Q g) v :=
        (reflectedCuspProfile_involution g A hA Q hQ v hv).symm
      _ = _ := by
        change (A⁻¹ / (Q : ℂ) ^ 2) * ((v : ℂ) ^ (-2 : ℂ) * reflectedCuspProfile A Q g ((Q * v)⁻¹)) =
          (A⁻¹ / (Q : ℂ) ^ 2) * ((v : ℂ) ^ (-2 : ℂ) * f ((Q * v)⁻¹))
        rw [hfg _ (by positivity)]
  exact ⟨cusp_mellin_entire f g A Q decayF decayG hQ hF hG hf hg hfbound hgbound hfg,
    cusp_mellin_entire g f (A⁻¹ / (Q : ℂ) ^ 2) Q decayG decayF hQ hG hF hg hf hgbound hfbound hgf⟩

/-- Both profiles in the reflected three-cusp identity have entire Mellin transforms. -/
theorem conjugateSource_three_cusp_mellin_entire_both (G : rationalExtension) (j : Fin 3)
    (g : SL(2, ℂ)) (hfactor : g = integralComplexMatrix (G : SL(2, O)) * integralComplexMatrix (cuspRepresentative j))
    (hc : g 1 0 ≠ 0) :
    ((∀ s : ℂ, MellinConvergent (cuspBarProfile (fun w => star (cubicSourceResidualFunction w)) (g 0 0 / g 1 0)) s) ∧
      Differentiable ℂ (mellin (cuspBarProfile (fun w => star (cubicSourceResidualFunction w)) (g 0 0 / g 1 0)))) ∧
    ((∀ s : ℂ, MellinConvergent (cuspZProfile (fun w => star (cubicSourceResidualFunction
      (integralComplexMatrix (cuspRepresentative j) • w))) (-g 1 1 / g 1 0)) s) ∧
      Differentiable ℂ (mellin (cuspZProfile (fun w => star (cubicSourceResidualFunction
        (integralComplexMatrix (cuspRepresentative j) • w))) (-g 1 1 / g 1 0)))) := by
  have hchar : extendedComplexCharacter G ≠ 0 := by
    intro hz
    have he : extendedComplexCharacter G * extendedComplexCharacter G⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    rw [hz, zero_mul] at he
    exact zero_ne_one he
  have hA : -star (extendedComplexCharacter G) / (g 1 0) ^ 2 ≠ 0 :=
    div_ne_zero (neg_ne_zero.mpr (star_ne_zero.mpr hchar)) (pow_ne_zero 2 hc)
  obtain ⟨δ, hδ, hb⟩ := conjugateSource_cuspRepresentative_zProfile_decay j (-g 1 1 / g 1 0)
  exact cusp_mellin_entire_both _ _ (-star (extendedComplexCharacter G) / (g 1 0) ^ 2) hA
    (‖g 1 0‖ ^ 2) residualBesselDecayRate δ (sq_pos_of_pos (norm_pos_iff.mpr hc)) residualBesselDecayRate_pos hδ
    (conjugateSource_barProfile_continuousOn _) (conjugateSource_cuspRepresentative_zProfile_continuousOn j _)
    (conjugateSource_barProfile_isBigO _) hb
    (fun v hv => conjugateSource_barProfile_reflection_rational G g _ hfactor hc v hv)

theorem conjugateSource_cusp_mellin_reflection (G : rationalExtension)
    (g H : SL(2, ℂ)) (hfactor : g = integralComplexMatrix (G : SL(2, O)) * H)
    (hc : g 1 0 ≠ 0) (s : ℂ) :
    mellin (cuspBarProfile (fun w => star (cubicSourceResidualFunction w)) (g 0 0 / g 1 0)) (2 * s) =
      (-star (extendedComplexCharacter G) / (g 1 0) ^ 2) * ((‖g 1 0‖ ^ 2 : ℝ) : ℂ) ^ (2 - 2 * s) *
        mellin (cuspZProfile (fun w => star (cubicSourceResidualFunction (H • w))) (-g 1 1 / g 1 0)) (2 - 2 * s) :=
  cusp_mellin_reflection_of_identity _ _ _ (2 * s) _ (sq_pos_of_pos (norm_pos_iff.mpr hc))
    (fun v hv => conjugateSource_barProfile_reflection_rational G g H hfactor hc v hv)

lemma exists_integral_matrix_cusp_ratio (a c : O) (hc : c ≠ 0) :
    ∃ M : SL(2, O), M 1 0 ≠ 0 ∧ ringComplex (M 0 0) / ringComplex (M 1 0) = ringComplex a / ringComplex c := by
  let d := IsBezout.gcd a c
  obtain ⟨a', ha⟩ := IsBezout.gcd_dvd_left a c
  obtain ⟨c', hcc⟩ := IsBezout.gcd_dvd_right a c
  change a = d * a' at ha
  change c = d * c' at hcc
  have hd : d ≠ 0 := by intro hz; exact hc (by rw [hcc, hz, zero_mul])
  have hc' : c' ≠ 0 := by intro hz; exact hc (by rw [hcc, hz, mul_zero])
  obtain ⟨u, v, huv⟩ := IsBezout.gcd_eq_sum a c
  change u * a + v * c = d at huv
  have hred : u * a' + v * c' = 1 := by
    apply mul_left_cancel₀ hd
    calc
      d * (u * a' + v * c') = u * a + v * c := by rw [ha, hcc]; ring
      _ = d := huv
      _ = d * 1 := (mul_one d).symm
  let M : SL(2, O) := ⟨!![a', -v; c', u], by
    rw [Matrix.det_fin_two]
    change a' * u - -v * c' = 1
    linear_combination hred⟩
  refine ⟨M, hc', ?_⟩
  change ringComplex a' / ringComplex c' = ringComplex a / ringComplex c
  rw [ha, hcc, map_mul, map_mul]
  have hde := ringComplex_ne_zero hd
  have hce := ringComplex_ne_zero hc'
  field_simp

/-- Every Eisenstein rational cusp has an entire horizontal-derivative Mellin transform. -/
theorem conjugateSource_rational_cusp_mellin_entire (a c : O) (hc : c ≠ 0) :
    (∀ s : ℂ, MellinConvergent (cuspBarProfile (fun w => star (cubicSourceResidualFunction w))
      (ringComplex a / ringComplex c)) s) ∧
      Differentiable ℂ (mellin (cuspBarProfile (fun w => star (cubicSourceResidualFunction w))
        (ringComplex a / ringComplex c))) := by
  obtain ⟨M, hM, he⟩ := exists_integral_matrix_cusp_ratio a c hc
  simpa only [he] using conjugateSource_integral_cusp_mellin_entire M hM

theorem conjugateSource_finite_twist_cusp_mellin_entire (h c : O) (hc : c ≠ 0) :
    (∀ s : ℂ, MellinConvergent (cuspBarProfile (fun w => star (cubicSourceResidualFunction w))
      (-3 * ringComplex h / ringComplex c)) s) ∧
      Differentiable ℂ (mellin (cuspBarProfile (fun w => star (cubicSourceResidualFunction w))
        (-3 * ringComplex h / ringComplex c))) := by
  simpa only [map_mul, map_neg, map_ofNat] using conjugateSource_rational_cusp_mellin_entire (-3 * h) c hc

lemma finiteMellin_linearCombination_entire {ι : Type*} [Fintype ι]
    (weight : ι → ℂ) (f : ι → ℝ → ℂ)
    (hc : ∀ i s, MellinConvergent (f i) s) (hd : ∀ i, Differentiable ℂ (mellin (f i))) :
    (∀ s : ℂ, MellinConvergent (fun v => ∑ i, weight i * f i v) s) ∧
      Differentiable ℂ (mellin (fun v => ∑ i, weight i * f i v)) := by
  have hi (i : ι) (s : ℂ) : Integrable (fun v : ℝ => (v : ℂ) ^ (s - 1) * (weight i * f i v))
      (volume.restrict (Set.Ioi 0)) := by
    have hh := (hc i s).const_smul (weight i)
    simp only [MellinConvergent, smul_eq_mul, IntegrableOn] at hh
    convert! hh using 1
  have hs (s : ℂ) : MellinConvergent (fun v => ∑ i, weight i * f i v) s := by
    unfold MellinConvergent
    simp only [smul_eq_mul, Finset.mul_sum]
    exact integrable_finset_sum _ (fun i _ => hi i s)
  have he (s : ℂ) : mellin (fun v => ∑ i, weight i * f i v) s = ∑ i, weight i * mellin (f i) s := by
    unfold mellin
    simp only [smul_eq_mul, Finset.mul_sum]
    rw [integral_finset_sum _ (fun i _ => hi i s)]
    apply Finset.sum_congr rfl
    intro i hmem
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall (fun v => by ring))
  refine ⟨hs, ?_⟩
  rw [funext he]
  intro s
  apply AnalyticAt.differentiableAt
  apply Finset.analyticAt_fun_sum
  intro i hmem
  exact analyticAt_const.mul ((hd i).analyticAt s)

/-- The derivative profile of a finite residue-class twist, expressed at rational cusps. -/
def traceTwistedBarProfile (c : O) (hc : c ≠ 0) [Fintype (O ⧸ Ideal.span {c})]
    (φ : (O ⧸ Ideal.span {c}) → ℂ) (v : ℝ) : ℂ :=
  ∑ h, finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 c hc) φ h *
    cuspBarProfile (fun w => star (cubicSourceResidualFunction w)) (thetaFourierTranslation c h) v

theorem traceTwistedBarProfile_mellin_entire (c : O) (hc : c ≠ 0) [Fintype (O ⧸ Ideal.span {c})]
    (φ : (O ⧸ Ideal.span {c}) → ℂ) :
    (∀ s : ℂ, MellinConvergent (traceTwistedBarProfile c hc φ) s) ∧
      Differentiable ℂ (mellin (traceTwistedBarProfile c hc φ)) := by
  apply finiteMellin_linearCombination_entire
  · intro h s
    exact (conjugateSource_finite_twist_cusp_mellin_entire (Quotient.out h) c hc).1 s
  · intro h
    exact (conjugateSource_finite_twist_cusp_mellin_entire (Quotient.out h) c hc).2

lemma horizontalWirtingerBar_finiteCombination {ι : Type*} [Fintype ι]
    (weight : ι → ℂ) (f : ι → ℂ → ℂ) (z : ℂ)
    (hf : ∀ i, DifferentiableAt ℝ (f i) z) :
    horizontalWirtingerBar (fun w => ∑ i, weight i * f i w) z =
      ∑ i, weight i * horizontalWirtingerBar (f i) z := by
  have hline (i : ι) (direction : ℂ) :
      DifferentiableAt ℝ (fun t : ℝ => f i (z + (t : ℂ) * direction)) 0 := by
    have hp : DifferentiableAt ℝ (fun t : ℝ => z + (t : ℂ) * direction) 0 := by fun_prop
    have hi : DifferentiableAt ℝ (f i) (z + (0 : ℂ) * direction) := by
      simpa only [zero_mul, add_zero] using hf i
    exact hi.comp 0 hp
  have h1 := (HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => ((hline i 1).hasDerivAt.const_mul (weight i)))).deriv
  have hI := (HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => ((hline i Complex.I).hasDerivAt.const_mul (weight i)))).deriv
  simp only [mul_one] at h1
  rw [horizontalWirtingerBar, h1, hI]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  unfold horizontalWirtingerBar
  ring

lemma conjugateSource_shift_horizontal_differentiableAt (a z : ℂ) (v : ℝ) (hv : 0 < v) :
    DifferentiableAt ℝ (fun w => star (cubicSourceResidualFunction (upperPoint (w + a) v hv))) z := by
  have hf := conjugateSource_translate_horizontal_differentiableAt (complexTranslation a) v hv z
  have he : (fun w => star (cubicSourceResidualFunction (complexTranslation a • upperPoint w v hv))) =
      fun w => star (cubicSourceResidualFunction (upperPoint (w + a) v hv)) := by
    funext w
    rw [complexTranslation_action]
  rw [he] at hf
  exact hf

lemma conjugateSource_shift_barProfile (a : ℂ) (v : ℝ) (hv : 0 < v) :
    cuspBarProfile (fun w => star (cubicSourceResidualFunction w)) a v =
      horizontalWirtingerBar (fun w => star (cubicSourceResidualFunction (upperPoint (w + a) v hv))) 0 := by
  rw [cuspBarProfile_positive _ _ _ hv]
  exact (horizontalWirtingerBar_translate
    (fun w => star (cubicSourceResidualFunction (upperPoint w v hv))) a).symm

theorem traceTwistedBarProfile_positive (c : O) (hc : c ≠ 0)
    [Fintype (O ⧸ Ideal.span {c})] (φ : (O ⧸ Ideal.span {c}) → ℂ)
    (v : ℝ) (hv : 0 < v) :
    traceTwistedBarProfile c hc φ v =
      horizontalWirtingerBar (traceTwistedConjugateSource c hc φ v hv) 0 := by
  let weight := finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 c hc) φ
  let f : (O ⧸ Ideal.span {c}) → ℂ → ℂ :=
    fun h z => star (cubicSourceResidualFunction (upperPoint (z + thetaFourierTranslation c h) v hv))
  have hd (h : O ⧸ Ideal.span {c}) : DifferentiableAt ℝ (f h) 0 :=
    conjugateSource_shift_horizontal_differentiableAt (thetaFourierTranslation c h) 0 v hv
  have he := horizontalWirtingerBar_finiteCombination weight f 0 hd
  refine Eq.trans ?_ he.symm
  apply Finset.sum_congr rfl
  intro h hh
  exact congrArg (fun q : ℂ => weight h * q)
    (conjugateSource_shift_barProfile (thetaFourierTranslation c h) v hv)

/-- The normalized theta derivative is an entire Mellin profile. -/
def finiteThetaBarProfile (c : O) (hc : c ≠ 0)
    [Fintype (O ⧸ Ideal.span {9 * c})] (Ψ : (O ⧸ Ideal.span {c}) →* ℂ) (v : ℝ) : ℂ :=
  rationalSourceThetaScalar⁻¹ *
    traceTwistedBarProfile (9 * c) (mul_ne_zero (by norm_num) hc) (finiteThetaTwist c Ψ) v

theorem finiteThetaBarProfile_mellin_entire (c : O) (hc : c ≠ 0)
    [Fintype (O ⧸ Ideal.span {9 * c})] (Ψ : (O ⧸ Ideal.span {c}) →* ℂ) :
    (∀ s : ℂ, MellinConvergent (finiteThetaBarProfile c hc Ψ) s) ∧
      Differentiable ℂ (mellin (finiteThetaBarProfile c hc Ψ)) := by
  have hf := traceTwistedBarProfile_mellin_entire (9 * c) (mul_ne_zero (by norm_num) hc) (finiteThetaTwist c Ψ)
  constructor
  · intro s
    unfold finiteThetaBarProfile
    have hh := (hf.1 s).const_smul rationalSourceThetaScalar⁻¹
    simp only [smul_eq_mul] at hh
    convert! hh using 1
  · have he : mellin (finiteThetaBarProfile c hc Ψ) =
        fun s => rationalSourceThetaScalar⁻¹ * mellin
          (traceTwistedBarProfile (9 * c) (mul_ne_zero (by norm_num) hc) (finiteThetaTwist c Ψ)) s := by
      funext s
      unfold finiteThetaBarProfile
      have hh := mellin_const_smul
        (traceTwistedBarProfile (9 * c) (mul_ne_zero (by norm_num) hc) (finiteThetaTwist c Ψ)) s
        rationalSourceThetaScalar⁻¹
      simp only [smul_eq_mul] at hh
      convert! hh using 1
    rw [he]
    exact hf.2.const_mul _

/-- The squarefree-times-cube Gauss series with its horizontal frequency weight. -/
def thetaDerivativeBesselProfile (Ψ : O →* ℂ) (v : ℝ) : ℂ :=
  ∑' p : ({I : Ideal O // Squarefree I ∧ primaryIdealGenerator I ≠ 0} ×
    {J : Ideal O // primaryIdealGenerator J ≠ 0}),
    ((‖ringComplex (primaryIdealGenerator p.2.val)‖ : ℂ) *
      normalizedCubicUnitGauss (primaryIdealGenerator p.1.val) *
      Ψ (primaryIdealGenerator p.1.val) * (Ψ (primaryIdealGenerator p.2.val)) ^ 3) *
      ((-2 * Real.pi * Complex.I * star (cuspFrequency (primaryIdealGenerator p.1.val *
        (primaryIdealGenerator p.2.val) ^ 3))) * (v : ℂ) * schlafliBesselK (1 / 3)
        (4 * Real.pi * ‖cuspFrequency (primaryIdealGenerator p.1.val *
          (primaryIdealGenerator p.2.val) ^ 3)‖ * v))

theorem finiteThetaBarProfile_eq_bessel (c : O) (hc : c ≠ 0)
    [Fintype (O ⧸ Ideal.span {9 * c})] (Ψ : (O ⧸ Ideal.span {c}) →* ℂ)
    (v : ℝ) (hv : 0 < v) :
    finiteThetaBarProfile c hc Ψ v =
      thetaDerivativeBesselProfile (Ψ.comp (Ideal.Quotient.mk (Ideal.span {c})).toMonoidHom) v := by
  rw [finiteThetaBarProfile, traceTwistedBarProfile_positive _ _ _ _ hv]
  exact finiteThetaTwist_source_wirtingerBar c hc Ψ v hv

lemma mellin_entire_of_positive_eq (f g : ℝ → ℂ) (he : ∀ v, 0 < v → f v = g v)
    (hf : (∀ s : ℂ, MellinConvergent f s) ∧ Differentiable ℂ (mellin f)) :
    (∀ s : ℂ, MellinConvergent g s) ∧ Differentiable ℂ (mellin g) := by
  have hae : f =ᵐ[volume.restrict (Set.Ioi 0)] g := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact he v hv
  have hm : mellin f = mellin g := by
    funext s
    apply integral_congr_ae
    filter_upwards [hae] with v hv
    rw [hv]
  refine ⟨?_, hm ▸ hf.2⟩
  intro s
  apply (hf.1 s).congr
  filter_upwards [hae] with v hv
  rw [hv]

/-- Finite arithmetic twists of the theta Gauss series have entire Mellin transforms. -/
theorem thetaDerivativeBesselProfile_mellin_entire (c : O) (hc : c ≠ 0)
    [Fintype (O ⧸ Ideal.span {9 * c})] (Ψ : (O ⧸ Ideal.span {c}) →* ℂ) :
    (∀ s : ℂ, MellinConvergent
      (thetaDerivativeBesselProfile (Ψ.comp (Ideal.Quotient.mk (Ideal.span {c})).toMonoidHom)) s) ∧
      Differentiable ℂ (mellin
        (thetaDerivativeBesselProfile (Ψ.comp (Ideal.Quotient.mk (Ideal.span {c})).toMonoidHom))) :=
  mellin_entire_of_positive_eq _ _ (finiteThetaBarProfile_eq_bessel c hc Ψ)
    (finiteThetaBarProfile_mellin_entire c hc Ψ)

/-- A finite cusp, its representative, and the matrix relating their coordinates. -/
structure SourceCuspDatum where
  gamma : rationalExtension
  index : Fin 3
  lower_ne_zero :
    (integralComplexMatrix (gamma : SL(2, O)) * integralComplexMatrix (cuspRepresentative index)) 1 0 ≠ 0

namespace SourceCuspDatum

def matrix (d : SourceCuspDatum) : SL(2, ℂ) :=
  integralComplexMatrix (d.gamma : SL(2, O)) * integralComplexMatrix (cuspRepresentative d.index)

def point (d : SourceCuspDatum) : ℂ := d.matrix 0 0 / d.matrix 1 0
def dualPoint (d : SourceCuspDatum) : ℂ := -d.matrix 1 1 / d.matrix 1 0
def heightScale (d : SourceCuspDatum) : ℝ := ‖d.matrix 1 0‖ ^ 2
def multiplier (d : SourceCuspDatum) : ℂ := -star (extendedComplexCharacter d.gamma) / (d.matrix 1 0) ^ 2

lemma heightScale_pos (d : SourceCuspDatum) : 0 < d.heightScale :=
  sq_pos_of_pos (norm_pos_iff.mpr d.lower_ne_zero)

lemma multiplier_norm (d : SourceCuspDatum) : ‖d.multiplier‖ = d.heightScale⁻¹ := by
  rw [multiplier, norm_div, norm_neg, norm_star, norm_extendedComplexCharacter, norm_pow, one_div]
  rfl

lemma multiplier_ne_zero (d : SourceCuspDatum) : d.multiplier ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [d.multiplier_norm]
  exact inv_ne_zero d.heightScale_pos.ne'

end SourceCuspDatum

lemma exists_sourceCuspDatum (a c : O) (hc : c ≠ 0) :
    ∃ d : SourceCuspDatum, d.point = ringComplex a / ringComplex c := by
  obtain ⟨M, hMc, hratio⟩ := exists_integral_matrix_cusp_ratio a c hc
  obtain ⟨G, j, T, hT, _, _, hM⟩ := three_cusp_decomposition M
  let g := integralComplexMatrix (G : SL(2, O)) * integralComplexMatrix (cuspRepresentative j)
  have he : integralComplexMatrix M = g * integralComplexMatrix T := by rw [hM, map_mul, map_mul]
  have ht : integralComplexMatrix T 1 0 = 0 := by
    change ringComplex (T 1 0) = 0
    rw [hT, map_zero]
  have hmc : (g * integralComplexMatrix T) 1 0 ≠ 0 := by
    rw [← he]
    exact ringComplex_ne_zero hMc
  obtain ⟨hg, hr⟩ := upperTriangular_right_cusp_ratio g (integralComplexMatrix T) ht hmc
  refine ⟨⟨G, j, hg⟩, ?_⟩
  change g 0 0 / g 1 0 = _
  rw [← hr, ← he]
  exact hratio

def rationalSourceCusp (a c : O) (hc : c ≠ 0) : SourceCuspDatum :=
  (exists_sourceCuspDatum a c hc).choose

lemma rationalSourceCusp_point (a c : O) (hc : c ≠ 0) :
    (rationalSourceCusp a c hc).point = ringComplex a / ringComplex c :=
  (exists_sourceCuspDatum a c hc).choose_spec

def sourceCuspZFamily (j : Fin 3) (z : ℂ) : ℝ → ℂ :=
  cuspZProfile (fun w => star (cubicSourceResidualFunction
    (integralComplexMatrix (cuspRepresentative j) • w))) z

theorem SourceCuspDatum.reflection (d : SourceCuspDatum) (v : ℝ) (hv : 0 < v) :
    cuspBarProfile (fun w => star (cubicSourceResidualFunction w)) d.point v =
      d.multiplier / (v : ℂ) ^ 2 * sourceCuspZFamily d.index d.dualPoint ((d.heightScale * v)⁻¹) := by
  have he := conjugateSource_barProfile_reflection_rational d.gamma d.matrix
    (integralComplexMatrix (cuspRepresentative d.index)) rfl d.lower_ne_zero v hv
  rw [reflectedCuspProfile, Complex.cpow_neg, Complex.cpow_ofNat] at he
  change _ = d.multiplier * (((v : ℂ) ^ 2)⁻¹ *
    sourceCuspZFamily d.index d.dualPoint ((d.heightScale * v)⁻¹)) at he
  exact he.trans (by ring)

theorem SourceCuspDatum.mellin_entire (d : SourceCuspDatum) :
    ((∀ s : ℂ, MellinConvergent
      (cuspBarProfile (fun w => star (cubicSourceResidualFunction w)) d.point) s) ∧
      Differentiable ℂ (mellin (cuspBarProfile (fun w => star (cubicSourceResidualFunction w)) d.point))) ∧
    ((∀ s : ℂ, MellinConvergent (sourceCuspZFamily d.index d.dualPoint) s) ∧
      Differentiable ℂ (mellin (sourceCuspZFamily d.index d.dualPoint))) :=
  conjugateSource_three_cusp_mellin_entire_both d.gamma d.index d.matrix rfl d.lower_ne_zero

theorem SourceCuspDatum.mellin_reflection (d : SourceCuspDatum) (s : ℂ) :
    mellin (cuspBarProfile (fun w => star (cubicSourceResidualFunction w)) d.point) (2 * s) =
      d.multiplier * (d.heightScale : ℂ) ^ (2 - 2 * s) *
        mellin (sourceCuspZFamily d.index d.dualPoint) (2 - 2 * s) :=
  conjugateSource_cusp_mellin_reflection d.gamma d.matrix
    (integralComplexMatrix (cuspRepresentative d.index)) rfl d.lower_ne_zero s

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
