import GaloisForLFunctions.RHTower.FieldOneFiniteStageHaarScaling
import GaloisForLFunctions.RHTower.FieldOneFiniteAdeleCompactOpenBasis
import GaloisForLFunctions.RHTower.CCM.CCMRationalFiniteAdeleDenominator
import GaloisForLFunctions.RHTower.FieldOneFiniteAdeleIntegralBruhatTest

/-!
# Adelic structural premises: Haar, measurability, compactness

Three standing premises of the adelic layer had no producer: an additive Haar measure on the
finite-stage adeles, measurability of the test set in the `L²` density theorems, and compactness of
the set carrying a common integer denominator.

None of them is an analytic input.  The finite-stage adeles are a finite product of locally compact
abelian groups, so they carry the canonical Haar measure.  The finite adeles have a basis of
compact open sets, and open sets are Borel measurable, so measurable test sets refine every
neighbourhood.  Compact sets of finite adeles are of course plentiful.
-/

open MeasureTheory MeasureTheory.Measure IsDedekindDomain Topology

namespace GaloisForLFunctions.RHTower

noncomputable section

/-! ## Haar measure on the finite-stage adeles -/

/-- The finite-stage adele group carries an additive Haar measure: it is a finite product of
locally compact abelian groups. -/
theorem exists_isAddHaarMeasure_fieldOneFiniteStageAdele
    (S : Finset (HeightOneSpectrum ℤ)) :
    ∃ μ : Measure (FieldOneFiniteStageAdele S), IsAddHaarMeasure μ :=
  ⟨addHaar, inferInstance⟩

/-- The canonical Haar measure, named for use as the witness. -/
theorem isAddHaarMeasure_fieldOneFiniteStageAdele_addHaar
    (S : Finset (HeightOneSpectrum ℤ)) :
    IsAddHaarMeasure (addHaar : Measure (FieldOneFiniteStageAdele S)) :=
  inferInstance

/-! ## Measurable test sets on the finite adeles -/

/-- Compact open sets of finite adeles are measurable. -/
theorem measurableSet_of_isOpen_fieldOneFiniteAdele {s : Set FieldOneFiniteAdele}
    (hs : IsOpen s) : MeasurableSet s :=
  hs.measurableSet

/-- **Measurable test sets refine every neighbourhood.**  The compact open basis of the finite
adeles consists of measurable sets, so the measurability hypothesis of the `L²` density theorems is
satisfied by a basis of the topology. -/
theorem exists_compactOpen_measurableSet_subset
    {x : FieldOneFiniteAdele} {U : Set FieldOneFiniteAdele} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ s : Set FieldOneFiniteAdele,
      x ∈ s ∧ s ⊆ U ∧ IsCompact s ∧ IsOpen s ∧ MeasurableSet s := by
  obtain ⟨s, hs, hxs, hsU⟩ :=
    fieldOneFiniteAdele_compactOpen_basis.exists_subset_of_mem_open hxU hU
  exact ⟨s, hxs, hsU, hs.1, hs.2, hs.2.measurableSet⟩

/-! ## Compact sets of rational finite adeles -/

/-- The compactness hypothesis of the common-denominator theorems is not vacuous. -/
theorem exists_isCompact_nonempty_ccmRationalFiniteAdele :
    ∃ K : Set CCMRationalFiniteAdele, IsCompact K ∧ K.Nonempty :=
  ⟨{0}, isCompact_singleton, Set.singleton_nonempty 0⟩

/-- Every finite set of rational finite adeles is compact, so the hypothesis holds on arbitrarily
large finite configurations. -/
theorem isCompact_of_finite_ccmRationalFiniteAdele {K : Set CCMRationalFiniteAdele}
    (hK : K.Finite) : IsCompact K :=
  hK.isCompact

/-- **The substantive witness.**  `CCMRationalFiniteAdele` and `FieldOneFiniteAdele` are two names
for the finite adele ring of `ℚ`, so the recorded compactness of the integral adeles is a
compactness statement about the former: the compactness hypothesis is satisfied by an open compact
subgroup, not merely by finite configurations. -/
theorem isCompact_integralAdeles_ccmRationalFiniteAdele :
    IsCompact
      (fieldOneFiniteAdeleIntegralAddSubgroup : Set CCMRationalFiniteAdele) :=
  fieldOneFiniteAdeleIntegralAddSubgroup_isCompact

/-- The common-denominator theorem applied to the integral adeles. -/
theorem exists_commonIntegerDenominator_integralAdeles :
    ∃ d : ℤ, d ≠ 0 ∧
      (fieldOneFiniteAdeleIntegralAddSubgroup : Set CCMRationalFiniteAdele) ⊆
        ccmRationalFiniteAdeleIntegerDenominatorSet d :=
  ccmRationalFiniteAdele_isCompact_exists_commonIntegerDenominator
    isCompact_integralAdeles_ccmRationalFiniteAdele

end

end GaloisForLFunctions.RHTower
