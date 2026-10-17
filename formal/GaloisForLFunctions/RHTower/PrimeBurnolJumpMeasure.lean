import GaloisForLFunctions.RHTower.PrimeBurnolPositiveMeasureClassification
import GaloisForLFunctions.RHTower.BurnolGraphActionFiltration

/-! Removing the zero atom gives unique finite-jump and killing coordinates on the literal Burnol space. -/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ComplexOrder NNReal
namespace RHTower
open GaloisForLFunctions.HTGeometry _root_.HTGeometry

def burnolJumpMeasure (τ : Measure ℝ≥0) : Measure ℝ≥0 := τ.restrict {0}ᶜ

instance (τ : Measure ℝ≥0) [IsFiniteMeasure τ] : IsFiniteMeasure (burnolJumpMeasure τ) :=
  inferInstanceAs (IsFiniteMeasure (τ.restrict {0}ᶜ))

lemma burnolJumpMeasure_zero (τ : Measure ℝ≥0) : burnolJumpMeasure τ {0} = 0 := by
  simp [burnolJumpMeasure, Measure.restrict_apply]

lemma burnolJumpMeasure_split (τ : Measure ℝ≥0) [IsFiniteMeasure τ] :
    τ = burnolJumpMeasure τ + (τ {0}).toNNReal • Measure.dirac 0 := by
  change τ = burnolJumpMeasure τ + ((τ {0}).toNNReal : ENNReal) • Measure.dirac 0
  rw [ENNReal.coe_toNNReal (measure_ne_top τ {0})]
  rw [← Measure.restrict_singleton, burnolJumpMeasure,
    Measure.restrict_compl_add_restrict (measurableSet_singleton (0 : ℝ≥0))]

lemma burnolPositiveShiftMixture_add (τ σ : Measure ℝ≥0)
    [IsFiniteMeasure τ] [IsFiniteMeasure σ] :
    burnolPositiveShiftMixture (τ+σ) =
      burnolPositiveShiftMixture τ + burnolPositiveShiftMixture σ := by
  apply ContinuousLinearMap.ext
  intro f
  exact integral_add_measure (integrable_burnolWeightedShift τ f)
    (integrable_burnolWeightedShift σ f)

lemma burnolPositiveShiftMixture_atom (c : ℝ≥0) :
    burnolPositiveShiftMixture (c • Measure.dirac 0) = ((c : ℝ) : ℂ) • 1 := by
  apply ContinuousLinearMap.ext
  intro f
  change (∫ h, burnolWeightedShift h f ∂c • Measure.dirac 0) = ((c : ℝ) : ℂ) • f
  rw [integral_smul_nnreal_measure, integral_dirac, burnolWeightedShift_zero,
    one_apply_eq_self]
  exact (IsScalarTower.algebraMap_smul ℂ (c : ℝ) f).symm

lemma burnolJumpMeasure_mass_split (τ : Measure ℝ≥0) [IsFiniteMeasure τ] :
    (τ univ).toReal = ((burnolJumpMeasure τ) univ).toReal + (τ {0}).toReal := by
  have h : τ univ = (burnolJumpMeasure τ) univ + τ {0} := by
    conv_lhs => rw [burnolJumpMeasure_split τ]
    simp
  rw [h, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]

lemma burnolPositiveShiftMixture_jump_split (τ : Measure ℝ≥0) [IsFiniteMeasure τ] :
    burnolPositiveShiftMixture τ = burnolPositiveShiftMixture (burnolJumpMeasure τ) +
      ((τ {0}).toReal : ℂ) • 1 := by
  have he := congrArg (fun μ : Measure ℝ≥0 =>
    fun f : BurnolHalfLineL2 => ∫ h, burnolWeightedShift h f ∂μ) (burnolJumpMeasure_split τ)
  apply ContinuousLinearMap.ext
  intro f
  change (∫ h, burnolWeightedShift h f ∂τ) = _
  rw [congrFun he f]
  change burnolPositiveShiftMixture (burnolJumpMeasure τ + (τ {0}).toNNReal • Measure.dirac 0) f = _
  rw [burnolPositiveShiftMixture_add, burnolPositiveShiftMixture_atom]
  rfl

/-- A canonical finite jump measure and independent nonnegative killing rate. -/
structure BurnolJumpData where
  measure : Measure ℝ≥0
  finite : IsFiniteMeasure measure
  zero_atom : measure {0} = 0
  killing : ℝ≥0

attribute [instance] BurnolJumpData.finite

def BurnolJumpData.generator (D : BurnolJumpData) : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2 :=
  burnolPositiveShiftMixture D.measure - (((D.killing : ℝ) + (D.measure univ).toReal : ℝ) : ℂ) • 1

lemma burnolJumpRepresentation_unique (τ σ : Measure ℝ≥0)
    [IsFiniteMeasure τ] [IsFiniteMeasure σ] (hτ : τ {0} = 0) (hσ : σ {0} = 0)
    {κ η : ℝ} (hκ : 0 ≤ κ) (hη : 0 ≤ η)
    (he : burnolPositiveShiftMixture τ - ((κ + (τ univ).toReal : ℝ) : ℂ) • 1 =
      burnolPositiveShiftMixture σ - ((η + (σ univ).toReal : ℝ) : ℂ) • 1) :
    τ = σ ∧ κ = η := by
  let c : ℝ≥0 := ⟨κ + (τ univ).toReal, add_nonneg hκ ENNReal.toReal_nonneg⟩
  let d : ℝ≥0 := ⟨η + (σ univ).toReal, add_nonneg hη ENNReal.toReal_nonneg⟩
  have hmix : burnolPositiveShiftMixture (τ + d • Measure.dirac 0) =
      burnolPositiveShiftMixture (σ + c • Measure.dirac 0) := by
    rw [burnolPositiveShiftMixture_add, burnolPositiveShiftMixture_add,
      burnolPositiveShiftMixture_atom, burnolPositiveShiftMixture_atom]
    exact sub_eq_sub_iff_add_eq_add.mp he
  have hm := burnolPositiveShiftMixture_injective _ _ hmix
  have h0 := congrArg (fun μ : Measure ℝ≥0 => μ {0}) hm
  have hcd : d = c := by
    simpa [Measure.add_apply, Measure.smul_apply, hτ, hσ] using h0
  have hreal : η + (σ univ).toReal = κ + (τ univ).toReal := congrArg (fun r : ℝ≥0 => (r : ℝ)) hcd
  have hgen : burnolPositiveShiftMixture τ = burnolPositiveShiftMixture σ := by
    rw [hreal] at he
    exact sub_left_inj.mp he
  have hτσ := burnolPositiveShiftMixture_injective _ _ hgen
  refine ⟨hτσ, ?_⟩
  rw [hτσ] at hreal
  linarith

lemma BurnolJumpData.generator_injective : Function.Injective BurnolJumpData.generator := by
  intro D E he
  obtain ⟨hm, hk⟩ := burnolJumpRepresentation_unique D.measure E.measure D.zero_atom E.zero_atom
    D.killing.coe_nonneg E.killing.coe_nonneg he
  have hk' : D.killing = E.killing := NNReal.coe_injective hk
  cases D
  cases E
  cases hm
  cases hk'
  rfl

end RHTower
