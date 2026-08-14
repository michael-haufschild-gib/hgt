import GaloisForLFunctions.RHTower.FieldOneFiniteStageMultiplicativeHaarFromAdditive
import GaloisForLFunctions.HTGeometry.WeightedDensityL2

/-!
# Additive quotient measure on the finite-stage class space

For a finite set `S` of rational finite places, the literal semilocal class
space is

`X_S = Q_S^* \\ A_S`.

Its open coordinatewise-invertible locus is the image of the canonical
injection `C_S → X_S`.  Additive Haar and multiplicative Haar are related on
that locus by `da = |a| d*a`.  We therefore define the source-normalized
measure on `X_S` by pushing `|c| d*c` through this injection.  The complement
of the idele locus is null by construction, while the measure itself remains
on the literal additive orbit quotient rather than replacing `X_S` by the
idele-class group.

This closes the quotient-measure gate needed before constructing the source
unitary `w_S : L²(X_S)^{K_S} → L²(R_+^*, d*u)`.
-/

open scoped ENNReal NNReal

namespace GaloisForLFunctions.RHTower

noncomputable section

open IsDedekindDomain MeasureTheory Set

/-! ### Borel structure and the open idele-class locus -/

/-- The additive class space carries the Borel measurable structure of its
quotient topology.  This is the measurable space used by the source
`L²(X_S)` construction. -/
noncomputable instance fieldOneFiniteStageClassMeasurableSpace
    (S : Finset (HeightOneSpectrum ℤ)) :
    MeasurableSpace (FieldOneFiniteStageClassSpace S) :=
  borel (FieldOneFiniteStageClassSpace S)

noncomputable instance fieldOneFiniteStageClassBorelSpace
    (S : Finset (HeightOneSpectrum ℤ)) :
    BorelSpace (FieldOneFiniteStageClassSpace S) :=
  ⟨rfl⟩

/-- The canonical parametrization of the idele locus is open. -/
theorem fieldOneFiniteStageIdeleClassToClassSpace_isOpenMap
    (S : Finset (HeightOneSpectrum ℤ)) :
    IsOpenMap (fieldOneFiniteStageIdeleClassToClassSpace S) := by
  intro U hU
  let qI : FieldOneFiniteStageIdele S →
      FieldOneFiniteStageIdeleClassGroup S := QuotientGroup.mk
  let qA : FieldOneFiniteStageAdele S →
      FieldOneFiniteStageClassSpace S := Quotient.mk _
  have hpre : IsOpen (qI ⁻¹' U) := by
    exact QuotientGroup.continuous_mk.isOpen_preimage U hU
  have hval : IsOpen (fieldOneFiniteStageIdeleVal S '' (qI ⁻¹' U)) :=
    (fieldOneFiniteStageIdeleVal_isOpenEmbedding S).isOpenMap _ hpre
  have hquot :
      IsOpen (qA '' (fieldOneFiniteStageIdeleVal S '' (qI ⁻¹' U))) :=
    (fieldOneFiniteStageClassQuotient_isOpenQuotientMap S).isOpenMap _ hval
  convert hquot using 1
  ext x
  constructor
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective c
    exact ⟨fieldOneFiniteStageIdeleVal S u, ⟨u, hc, rfl⟩, rfl⟩
  · rintro ⟨a, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨QuotientGroup.mk u, hu, rfl⟩

/-- The idele-class group is an open subspace of the literal additive class
space. -/
theorem fieldOneFiniteStageIdeleClassToClassSpace_isOpenEmbedding
    (S : Finset (HeightOneSpectrum ℤ)) :
    Topology.IsOpenEmbedding (fieldOneFiniteStageIdeleClassToClassSpace S) :=
  Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (fieldOneFiniteStageIdeleClassToClassSpace_continuous S)
    (fieldOneFiniteStageIdeleClassToClassSpace_injective S)
    (fieldOneFiniteStageIdeleClassToClassSpace_isOpenMap S)

/-- The idele-class module is everywhere strictly nonzero. -/
theorem fieldOneFiniteStageIdeleClassModule_ne_zero
    (S : Finset (HeightOneSpectrum ℤ))
    (c : FieldOneFiniteStageIdeleClassGroup S) :
    fieldOneFiniteStageIdeleClassModule S c ≠ 0 := by
  refine Quotient.inductionOn' c ?_
  intro u
  change fieldOneFiniteStageModule S u ≠ 0
  exact fieldOneFiniteStageModule_ne_zero S u

/-- Real-valued modulus on the idele class group. -/
def fieldOneFiniteStageIdeleClassModuleReal
    (S : Finset (HeightOneSpectrum ℤ))
    (c : FieldOneFiniteStageIdeleClassGroup S) : ℝ :=
  fieldOneFiniteStageIdeleClassModule S c

theorem fieldOneFiniteStageIdeleClassModuleReal_measurable
    (S : Finset (HeightOneSpectrum ℤ)) :
    Measurable (fieldOneFiniteStageIdeleClassModuleReal S) := by
  exact (NNReal.continuous_coe.comp
    (fieldOneFiniteStageIdeleClassModule_continuous S)).measurable

theorem fieldOneFiniteStageIdeleClassModuleReal_pos
    (S : Finset (HeightOneSpectrum ℤ))
    (c : FieldOneFiniteStageIdeleClassGroup S) :
    0 < fieldOneFiniteStageIdeleClassModuleReal S c := by
  exact_mod_cast (pos_iff_ne_zero.mpr
    (fieldOneFiniteStageIdeleClassModule_ne_zero S c))

/-- The additive density on the idele-class locus: `|c| d*c`. -/
def fieldOneFiniteStageIdeleClassAdditiveMeasure
    (S : Finset (HeightOneSpectrum ℤ)) :
    Measure (FieldOneFiniteStageIdeleClassGroup S) :=
  (fieldOneFiniteStageSplitHaarMeasure S).withDensity
    (GaloisForLFunctions.HTGeometry.realDensity
      (fieldOneFiniteStageIdeleClassModuleReal S))

/-- Source-normalized additive quotient measure on the literal class space
`X_S`. -/
def fieldOneFiniteStageClassAdditiveMeasure
    (S : Finset (HeightOneSpectrum ℤ)) :
    Measure (FieldOneFiniteStageClassSpace S) :=
  Measure.map (fieldOneFiniteStageIdeleClassToClassSpace S)
    (fieldOneFiniteStageIdeleClassAdditiveMeasure S)

/-- The orbit-of-one injection is measure preserving from `|c| d*c` to the
additive quotient measure on `X_S`. -/
theorem fieldOneFiniteStageIdeleClassToClassSpace_measurePreserving
    (S : Finset (HeightOneSpectrum ℤ)) :
    MeasurePreserving (fieldOneFiniteStageIdeleClassToClassSpace S)
      (fieldOneFiniteStageIdeleClassAdditiveMeasure S)
      (fieldOneFiniteStageClassAdditiveMeasure S) := by
  refine ⟨(fieldOneFiniteStageIdeleClassToClassSpace_continuous S).measurable, ?_⟩
  rfl

/-- The non-invertible part of `X_S` is null for the source additive quotient
measure. -/
theorem fieldOneFiniteStageClassAdditiveMeasure_compl_ideleClassRange
    (S : Finset (HeightOneSpectrum ℤ)) :
    fieldOneFiniteStageClassAdditiveMeasure S
        ((Set.range (fieldOneFiniteStageIdeleClassToClassSpace S))ᶜ) = 0 := by
  rw [fieldOneFiniteStageClassAdditiveMeasure,
    Measure.map_apply
      (fieldOneFiniteStageIdeleClassToClassSpace_continuous S).measurable
      (fieldOneFiniteStageIdeleClassToClassSpace_range_isOpen S).measurableSet.compl]
  simp

/-- The descended adelic module is positive almost everywhere on `X_S`.
Its zero locus is precisely confined to the null non-idele stratum. -/
theorem fieldOneFiniteStageClassModule_ne_zero_ae
    (S : Finset (HeightOneSpectrum ℤ)) :
    ∀ᵐ x ∂fieldOneFiniteStageClassAdditiveMeasure S,
      fieldOneFiniteStageClassModule S x ≠ 0 := by
  rw [ae_iff]
  apply measure_mono_null
    (t := (Set.range (fieldOneFiniteStageIdeleClassToClassSpace S))ᶜ)
  · intro x hx
    simp only [mem_compl_iff, mem_range, not_exists]
    intro c hc
    subst x
    apply hx
    rw [fieldOneFiniteStageClassModule_ideleClass]
    exact fieldOneFiniteStageIdeleClassModule_ne_zero S c
  · exact fieldOneFiniteStageClassAdditiveMeasure_compl_ideleClassRange S

/-- Literal source Hilbert space `L²(X_S)` for the finite semilocal stage. -/
abbrev FieldOneFiniteStageClassL2
    (S : Finset (HeightOneSpectrum ℤ)) :=
  Lp ℂ 2 (fieldOneFiniteStageClassAdditiveMeasure S)

end

end GaloisForLFunctions.RHTower
