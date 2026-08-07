import GaloisForLFunctions.RHTower.GibbsAntiscaleFirstTraceFrame
import GaloisForLFunctions.HTGeometry.ThermodynamicAffinityHolonomy

/-!
# Thermodynamic lift of Route E batch dispersion

A positive weighted finite batch has a canonical Hermitian KMS amplitude whose edge entropy
production is strictly positive exactly across unequal batch values. Consequently total entropy
production and Route E's order-free pairwise dispersion have the same exact nullspace.
-/

open scoped BigOperators
open GaloisForLFunctions.HTGeometry

namespace RHTower.GibbsGas

noncomputable section

/-- At inverse temperature one, equality of finite Gibbs populations is exactly equality of the
underlying energy values. -/
theorem finiteGibbsStateWeight_one_eq_iff
    {α : Type*} [Fintype α] [Nonempty α]
    (value : α → ℝ) (a b : α) :
    _root_.HTGeometry.finiteGibbsStateWeight 1 value a =
        _root_.HTGeometry.finiteGibbsStateWeight 1 value b ↔
      value a = value b := by
  have hZ : _root_.HTGeometry.finiteGibbsPartition 1 value ≠ 0 :=
    (_root_.HTGeometry.finiteGibbsPartition_pos 1 value).ne'
  rw [_root_.HTGeometry.finiteGibbsStateWeight,
    _root_.HTGeometry.finiteGibbsStateWeight]
  constructor
  · intro h
    have hexp : Real.exp (-1 * value a) = Real.exp (-1 * value b) := by
      apply (div_left_inj' hZ).mp
      exact h
    have hneg := Real.exp_injective hexp
    linarith
  · intro hav
    rw [hav]

/-- Canonical Hermitian amplitude attached to positive batch weights. -/
def routeEBatchEntropyAmplitude
    {α : Type*} (w : α → ℝ) (a b : α) : ℂ :=
  (Real.sqrt (w a * w b) : ℝ)

theorem routeEBatchEntropyAmplitude_hermitian
    {α : Type*} (w : α → ℝ) (a b : α) :
    routeEBatchEntropyAmplitude w b a =
      star (routeEBatchEntropyAmplitude w a b) := by
  simp [routeEBatchEntropyAmplitude, mul_comm]

theorem normSq_routeEBatchEntropyAmplitude_pos
    {α : Type*} (w : α → ℝ) (hw : ∀ i, 0 < w i) (a b : α) :
    0 < Complex.normSq (routeEBatchEntropyAmplitude w a b) := by
  rw [routeEBatchEntropyAmplitude, Complex.normSq_ofReal,
    Real.mul_self_sqrt (mul_nonneg (hw a).le (hw b).le)]
  exact mul_pos (hw a) (hw b)

/-- One lifted thermodynamic edge is strictly positive exactly when its two batch values differ. -/
theorem finiteKMS_routeEBatchEntropyIntensity_pos_iff
    {α : Type*} [Fintype α] [Nonempty α]
    (w value : α → ℝ) (hw : ∀ i, 0 < w i) (a b : α) :
    0 < finiteKMSEntropyProductionTransitionIntensity
        1 value (routeEBatchEntropyAmplitude w) a b ↔
      value a ≠ value b := by
  rw [finiteKMSEntropyProductionTransitionIntensity_eq_entropyProductionValue_mul_normSq
    1 value (routeEBatchEntropyAmplitude w)
    (routeEBatchEntropyAmplitude_hermitian w)]
  rw [mul_pos_iff]
  have hnorm : 0 < Complex.normSq (routeEBatchEntropyAmplitude w a b) :=
    normSq_routeEBatchEntropyAmplitude_pos w hw a b
  have hpa := _root_.HTGeometry.finiteGibbsStateWeight_pos 1 value a
  have hpb := _root_.HTGeometry.finiteGibbsStateWeight_pos 1 value b
  have hent :
      0 < entropyProductionValue
          (_root_.HTGeometry.finiteGibbsStateWeight 1 value b)
          (_root_.HTGeometry.finiteGibbsStateWeight 1 value a) ↔
        value a ≠ value b := by
    rw [entropyProductionValue_pos_iff_ne hpb hpa]
    simpa [ne_comm] using not_congr (finiteGibbsStateWeight_one_eq_iff value b a)
  constructor
  · rintro (hpos | hneg)
    · exact hent.mp hpos.1
    · linarith
  · intro hne
    exact Or.inl ⟨hent.mpr hne, hnorm⟩

/-- Total KMS entropy production of the canonical weighted batch lift. -/
def routeEBatchTotalEntropyProduction
    {α : Type*} [Fintype α] (w value : α → ℝ) : ℝ :=
  ∑ a, ∑ b, finiteKMSEntropyProductionTransitionIntensity
    1 value (routeEBatchEntropyAmplitude w) a b

/-- Total lifted entropy production vanishes exactly on constant batch values. -/
theorem routeEBatchTotalEntropyProduction_eq_zero_iff_constant
    {α : Type*} [Fintype α] [Nonempty α]
    (w value : α → ℝ) (hw : ∀ i, 0 < w i) :
    routeEBatchTotalEntropyProduction w value = 0 ↔
      ∀ a b, value a = value b := by
  have hnonneg : ∀ a b,
      0 ≤ finiteKMSEntropyProductionTransitionIntensity
        1 value (routeEBatchEntropyAmplitude w) a b := by
    exact fun a b => finiteKMSEntropyProductionTransitionIntensity_nonneg
      1 value (routeEBatchEntropyAmplitude w)
      (routeEBatchEntropyAmplitude_hermitian w) a b
  constructor
  · intro hzero a b
    unfold routeEBatchTotalEntropyProduction at hzero
    have houter : ∀ i ∈ Finset.univ,
        0 ≤ ∑ j, finiteKMSEntropyProductionTransitionIntensity
          1 value (routeEBatchEntropyAmplitude w) i j := by
      intro i hi
      exact Finset.sum_nonneg fun j hj => hnonneg i j
    have haZero := (Finset.sum_eq_zero_iff_of_nonneg houter).mp hzero a
      (Finset.mem_univ a)
    have habZero := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j hj => hnonneg a j)).mp haZero b (Finset.mem_univ b)
    by_contra hne
    exact (ne_of_gt ((finiteKMS_routeEBatchEntropyIntensity_pos_iff
      w value hw a b).mpr hne)) habZero
  · intro hconstant
    unfold routeEBatchTotalEntropyProduction
    apply Finset.sum_eq_zero
    intro a ha
    apply Finset.sum_eq_zero
    intro b hb
    have hnonpos : ¬ 0 < finiteKMSEntropyProductionTransitionIntensity
        1 value (routeEBatchEntropyAmplitude w) a b := by
      rw [finiteKMS_routeEBatchEntropyIntensity_pos_iff w value hw]
      exact not_ne_iff.mpr (hconstant a b)
    exact le_antisymm (not_lt.mp hnonpos) (hnonneg a b)

/-- **Gibbs/KMS nullspace lift.** The canonical total entropy production and Route E's weighted
pairwise dispersion vanish on exactly the same finite batches. -/
theorem routeEBatchTotalEntropyProduction_eq_zero_iff_pairwiseDispersion
    {α : Type*} [Fintype α] [Nonempty α]
    (w value : α → ℝ) (hw : ∀ i, 0 < w i) :
    routeEBatchTotalEntropyProduction w value = 0 ↔
      routeEBatchPairwiseDispersion Finset.univ w value = 0 := by
  rw [routeEBatchTotalEntropyProduction_eq_zero_iff_constant w value hw,
    routeEBatchPairwiseDispersion_eq_zero_iff_constant Finset.univ w value]
  · simp
  · intro i hi
    exact hw i

end

end RHTower.GibbsGas
