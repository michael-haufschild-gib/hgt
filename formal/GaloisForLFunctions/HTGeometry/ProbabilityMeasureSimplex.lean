import Mathlib.MeasureTheory.Measure.Typeclasses.ZeroOne
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Elementary probability-simplex geometry

Mathlib supplies probability measures and zero-one measures but does not package the convex
simplex laws on `ProbabilityMeasure`.  This file builds the exact two-point mixture, conditional
restrictions, and the characterization of the extreme probability laws as Dirac masses.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The probability mixture `t mu + (1-t) nu` for an extended nonnegative weight in `[0,1]`. -/
noncomputable def probabilityMixture {X : Type*} [MeasurableSpace X]
    (t : ℝ≥0∞) (ht : t ≤ 1)
    (mu nu : ProbabilityMeasure X) : ProbabilityMeasure X := by
  refine ⟨t • (mu : Measure X) + (1 - t) • (nu : Measure X), ?_⟩
  rw [isProbabilityMeasure_iff, Measure.add_apply, Measure.smul_apply,
    Measure.smul_apply]
  have hmu : (mu : Measure X) Set.univ = 1 := mu.prop.measure_univ
  have hnu : (nu : Measure X) Set.univ = 1 := nu.prop.measure_univ
  rw [hmu, hnu]
  simp only [smul_eq_mul, mul_one]
  exact add_tsub_cancel_of_le ht

@[simp]
theorem probabilityMixture_toMeasure {X : Type*} [MeasurableSpace X]
    (t : ℝ≥0∞) (ht : t ≤ 1)
    (mu nu : ProbabilityMeasure X) :
    (probabilityMixture t ht mu nu : Measure X) =
      t • (mu : Measure X) + (1 - t) • (nu : Measure X) := rfl

/-- A probability law conditioned on a positive-measure measurable set. -/
noncomputable def conditionalProbability {X : Type*} [MeasurableSpace X]
    (mu : ProbabilityMeasure X) (A : Set X) (_hA : MeasurableSet A)
    (hpos : (mu : Measure X) A ≠ 0) : ProbabilityMeasure X := by
  refine ⟨((mu : Measure X) A)⁻¹ • (mu : Measure X).restrict A, ?_⟩
  rw [isProbabilityMeasure_iff, Measure.smul_apply,
    Measure.restrict_apply_univ]
  simp only [smul_eq_mul]
  exact ENNReal.inv_mul_cancel hpos (measure_ne_top (mu : Measure X) A)

@[simp]
theorem conditionalProbability_toMeasure {X : Type*} [MeasurableSpace X]
    (mu : ProbabilityMeasure X) (A : Set X) (hA : MeasurableSet A)
    (hpos : (mu : Measure X) A ≠ 0) :
    (conditionalProbability mu A hA hpos : Measure X) =
      ((mu : Measure X) A)⁻¹ • (mu : Measure X).restrict A := rfl

/-- A conull singleton determines a probability measure uniquely. -/
theorem probabilityMeasure_eq_dirac_of_compl_singleton_zero
    {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (mu : ProbabilityMeasure X) (x : X)
    (hzero : (mu : Measure X) {x}ᶜ = 0) :
    mu = ⟨Measure.dirac x, Measure.dirac.isProbabilityMeasure⟩ := by
  apply ProbabilityMeasure.toMeasure_injective
  ext A hA
  by_cases hx : x ∈ A
  · have hAc : (mu : Measure X) Aᶜ = 0 :=
      measure_mono_null (compl_subset_compl.mpr (singleton_subset_iff.mpr hx)) hzero
    have hmass := measure_of_measure_compl_eq_zero hAc
    have huniv : (mu : Measure X) Set.univ = 1 := mu.prop.measure_univ
    rw [hmass, huniv]
    change 1 = Measure.dirac x A
    rw [Measure.dirac_apply' _ hA]
    simp [hx]
  · have hsub : A ⊆ {x}ᶜ := fun y hy hyx => hx (hyx ▸ hy)
    rw [measure_mono_null hsub hzero]
    change 0 = Measure.dirac x A
    rw [Measure.dirac_apply' _ hA]
    simp [hx]

/-- Extreme point in a subset of the probability simplex, expressed with genuine probability
mixtures rather than an ambient signed-measure vector space. -/
def IsExtremeProbabilityLaw {X : Type*} [MeasurableSpace X]
    (C : Set (ProbabilityMeasure X)) (mu : ProbabilityMeasure X) : Prop :=
  mu ∈ C ∧
    ∀ (t : ℝ≥0∞) (ht : t ≤ 1), 0 < t → t < 1 →
      ∀ nu theta, nu ∈ C → theta ∈ C →
        probabilityMixture t ht nu theta = mu → nu = mu ∧ theta = mu

/-- Every Dirac probability is extreme in the full probability simplex. -/
theorem isExtremeProbabilityLaw_dirac
    {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (x : X) :
    IsExtremeProbabilityLaw Set.univ
      (⟨Measure.dirac x, Measure.dirac.isProbabilityMeasure⟩ : ProbabilityMeasure X) := by
  refine ⟨Set.mem_univ _, ?_⟩
  intro t ht ht0 ht1 mu nu _ _ hmix
  have hmeasure := congrArg ProbabilityMeasure.toMeasure hmix
  have hzero := congrArg (fun m : Measure X => m {x}ᶜ) hmeasure
  change (t • (mu : Measure X) + (1 - t) • (nu : Measure X)) {x}ᶜ =
    Measure.dirac x {x}ᶜ at hzero
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply] at hzero
  have hdiraczero : Measure.dirac x {x}ᶜ = 0 := by
    rw [Measure.dirac_apply' _ (measurableSet_singleton x).compl]
    simp
  rw [hdiraczero] at hzero
  simp only [smul_eq_mul] at hzero
  have hparts : t * (mu : Measure X) {x}ᶜ = 0 ∧
      (1 - t) * (nu : Measure X) {x}ᶜ = 0 :=
    add_eq_zero.mp hzero
  have htne : t ≠ 0 := ne_of_gt ht0
  have hctne : 1 - t ≠ 0 := ne_of_gt (tsub_pos_iff_lt.mpr ht1)
  have hmu0 : (mu : Measure X) {x}ᶜ = 0 :=
    (mul_eq_zero.mp hparts.1).resolve_left htne
  have hnu0 : (nu : Measure X) {x}ᶜ = 0 :=
    (mul_eq_zero.mp hparts.2).resolve_left hctne
  exact ⟨probabilityMeasure_eq_dirac_of_compl_singleton_zero mu x hmu0,
    probabilityMeasure_eq_dirac_of_compl_singleton_zero nu x hnu0⟩

/-- If a probability law is not Dirac on a standard Borel space, some measurable set has mass
strictly between zero and one. -/
theorem exists_measurableSet_measure_ne_zero_ne_one_of_not_dirac
    {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    (mu : ProbabilityMeasure X)
    (hmu : ∀ x, mu ≠
      (⟨Measure.dirac x, Measure.dirac.isProbabilityMeasure⟩ : ProbabilityMeasure X)) :
    ∃ A : Set X, MeasurableSet A ∧
      (mu : Measure X) A ≠ 0 ∧ (mu : Measure X) A ≠ 1 := by
  by_contra h
  push_neg at h
  letI : IsZeroOneMeasure (mu : Measure X) :=
    ⟨fun {A} hA => by
      by_cases h0 : (mu : Measure X) A = 0
      · exact Or.inl h0
      · exact Or.inr (h A hA h0)⟩
  haveI : NeZero (mu : Measure X) :=
    ⟨fun hzero => by
      have huniv := congrArg (fun m : Measure X => m Set.univ) hzero
      simpa [mu.prop.measure_univ] using huniv⟩
  obtain ⟨x, hx⟩ := IsZeroOneMeasure.exists_eq_dirac (μ := (mu : Measure X))
  exact hmu x (ProbabilityMeasure.toMeasure_injective hx)

/-- A positive-measure set and its positive-measure complement reconstruct a probability law as
the corresponding two conditional laws. -/
theorem probabilityMixture_conditionals
    {X : Type*} [MeasurableSpace X]
    (mu : ProbabilityMeasure X) (A : Set X) (hA : MeasurableSet A)
    (hA0 : (mu : Measure X) A ≠ 0)
    (hAc0 : (mu : Measure X) Aᶜ ≠ 0) :
    probabilityMixture ((mu : Measure X) A)
      (by
        rw [← mu.prop.measure_univ]
        exact measure_mono (subset_univ A))
      (conditionalProbability mu A hA hA0)
      (conditionalProbability mu Aᶜ hA.compl hAc0) =
      mu := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [probabilityMixture_toMeasure, conditionalProbability_toMeasure]
  have hAle : (mu : Measure X) A ≤ 1 := by
    rw [← mu.prop.measure_univ]
    exact measure_mono (subset_univ A)
  have hAc : (mu : Measure X) Aᶜ = 1 - (mu : Measure X) A := by
    have huniv : (mu : Measure X) Set.univ = 1 := mu.prop.measure_univ
    rw [measure_compl hA (measure_ne_top _ _), huniv]
  rw [smul_smul, smul_smul,
    ENNReal.mul_inv_cancel hA0 (measure_ne_top _ _), one_smul,
    ← hAc, ENNReal.mul_inv_cancel hAc0
      (measure_ne_top (mu : Measure X) Aᶜ), one_smul]
  exact Measure.restrict_add_restrict_compl hA

/-- On a standard Borel space, the extreme probability laws are exactly the Dirac masses. -/
theorem isExtremeProbabilityLaw_univ_iff_dirac
    {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    (mu : ProbabilityMeasure X) :
    IsExtremeProbabilityLaw Set.univ mu ↔
      ∃ x, mu = ⟨Measure.dirac x, Measure.dirac.isProbabilityMeasure⟩ := by
  constructor
  · intro hextreme
    by_contra hdirac
    push_neg at hdirac
    obtain ⟨A, hA, hA0, hA1⟩ :=
      exists_measurableSet_measure_ne_zero_ne_one_of_not_dirac mu hdirac
    have hAle : (mu : Measure X) A ≤ 1 := by
      rw [← mu.prop.measure_univ]
      exact measure_mono (subset_univ A)
    have hAlt : (mu : Measure X) A < 1 := lt_of_le_of_ne hAle hA1
    let muA := conditionalProbability mu A hA hA0
    have hAc0 : (mu : Measure X) Aᶜ ≠ 0 := by
      have huniv : (mu : Measure X) Set.univ = 1 := mu.prop.measure_univ
      rw [measure_compl hA (measure_ne_top _ _), huniv]
      exact ne_of_gt (tsub_pos_iff_lt.mpr hAlt)
    let muAc := conditionalProbability mu Aᶜ hA.compl hAc0
    have hdecomp : probabilityMixture ((mu : Measure X) A) hAle muA muAc = mu :=
      probabilityMixture_conditionals mu A hA hA0 hAc0
    have hparts := hextreme.2 ((mu : Measure X) A) hAle
      (pos_iff_ne_zero.mpr hA0) hAlt muA muAc (Set.mem_univ _) (Set.mem_univ _) hdecomp
    have hmuAcompl : (muA : Measure X) Aᶜ = 0 := by
      simp [muA, conditionalProbability_toMeasure, Measure.restrict_apply hA.compl]
    have hmucompl : (mu : Measure X) Aᶜ ≠ 0 := by
      have huniv : (mu : Measure X) Set.univ = 1 := mu.prop.measure_univ
      rw [measure_compl hA (measure_ne_top _ _), huniv]
      exact ne_of_gt (tsub_pos_iff_lt.mpr hAlt)
    have := congrArg (fun rho : ProbabilityMeasure X => (rho : Measure X) Aᶜ) hparts.1
    exact hmucompl (by simpa [hmuAcompl] using this.symm)
  · rintro ⟨x, rfl⟩
    exact isExtremeProbabilityLaw_dirac x

end

end GaloisForLFunctions.HTGeometry
