import GaloisForLFunctions.RHTower.FieldOneFiniteStageClassModule
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The conull idele locus at a finite adelic stage

For a finite set `S` of rational finite places, the coordinatewise
invertible adeles form an open subset of

`A_S = ℝ × ∏_{v ∈ S} ℚ_v`.

This file identifies that subset with the range of the idele-value map,
proves its image in the additive orbit quotient `X_S` is open, and proves
that its complement in `A_S` has measure zero for the explicit product of
local additive Haar measures.

The last statement is the prequotient conullness used in the semilocal
idele-locus comparison.  It does not construct a measure on `X_S`: passing
conullness through the orbit quotient still requires a genuine
fundamental-domain or disintegration measure, not direct pushforward through
the infinite orbit map.
-/

open MeasureTheory Set
open MeasureTheory.Measure

namespace GaloisForLFunctions.RHTower

noncomputable section

open IsDedekindDomain

/-- Coordinatewise invertible finite-stage additive adeles. -/
def fieldOneFiniteStageIdeleLocus
    (S : Finset (HeightOneSpectrum ℤ)) :
    Set (FieldOneFiniteStageAdele S) :=
  {x | x.1 ≠ 0 ∧ ∀ v, x.2 v ≠ 0}

/-- The idele locus is exactly the range of the coordinatewise value map. -/
theorem fieldOneFiniteStageIdeleVal_range
    (S : Finset (HeightOneSpectrum ℤ)) :
    Set.range (fieldOneFiniteStageIdeleVal S) =
      fieldOneFiniteStageIdeleLocus S := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨Units.ne_zero _, fun v => Units.ne_zero _⟩
  · rintro ⟨hxreal, hxfinite⟩
    let u : FieldOneFiniteStageIdele S :=
      (Units.mk0 x.1 hxreal,
        fun v => Units.mk0 (x.2 v) (hxfinite v))
    exact ⟨u, rfl⟩

/-- Coordinatewise invertibility is an open condition at a finite stage. -/
theorem fieldOneFiniteStageIdeleLocus_isOpen
    (S : Finset (HeightOneSpectrum ℤ)) :
    IsOpen (fieldOneFiniteStageIdeleLocus S) := by
  change IsOpen {x : FieldOneFiniteStageAdele S |
    x.1 ≠ 0 ∧ ∀ v, x.2 v ≠ 0}
  have hreal :
      IsOpen {x : FieldOneFiniteStageAdele S | x.1 ≠ 0} :=
    isOpen_compl_singleton.preimage continuous_fst
  have hfinite :
      IsOpen {x : FieldOneFiniteStageAdele S | ∀ v, x.2 v ≠ 0} := by
    have heq :
        {x : FieldOneFiniteStageAdele S | ∀ v, x.2 v ≠ 0} =
          ⋂ v, {x : FieldOneFiniteStageAdele S | x.2 v ≠ 0} := by
      ext x
      simp
    rw [heq]
    apply isOpen_iInter_of_finite
    intro v
    exact isOpen_compl_singleton.preimage
      ((continuous_apply v).comp continuous_snd)
  exact hreal.inter hfinite

/-- The image of idele classes in the additive orbit quotient is exactly the
orbit projection of the coordinatewise idele locus. -/
theorem fieldOneFiniteStageIdeleClassToClassSpace_range
    (S : Finset (HeightOneSpectrum ℤ)) :
    Set.range (fieldOneFiniteStageIdeleClassToClassSpace S) =
      Quotient.mk
          (MulAction.orbitRel
            (fieldOneFiniteStageSUnitImage S)
            (FieldOneFiniteStageAdele S)) ''
        fieldOneFiniteStageIdeleLocus S := by
  ext x
  constructor
  · rintro ⟨c, rfl⟩
    refine Quotient.inductionOn' c ?_
    intro u
    refine ⟨fieldOneFiniteStageIdeleVal S u, ?_, rfl⟩
    rw [← fieldOneFiniteStageIdeleVal_range S]
    exact ⟨u, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    rw [← fieldOneFiniteStageIdeleVal_range S] at ha
    obtain ⟨u, rfl⟩ := ha
    exact ⟨QuotientGroup.mk u, rfl⟩

/-- The idele-class orbit is open in the additive orbit quotient. -/
theorem fieldOneFiniteStageIdeleClassToClassSpace_range_isOpen
    (S : Finset (HeightOneSpectrum ℤ)) :
    IsOpen
      (Set.range (fieldOneFiniteStageIdeleClassToClassSpace S)) := by
  rw [fieldOneFiniteStageIdeleClassToClassSpace_range S]
  exact
    (fieldOneFiniteStageClassQuotient_isOpenQuotientMap S).isOpenMap
      (fieldOneFiniteStageIdeleLocus S)
      (fieldOneFiniteStageIdeleLocus_isOpen S)

/-! ### Product additive Haar measure -/

/-- Explicit product of local additive Haar measures on the finite-stage
additive adeles. -/
noncomputable def fieldOneFiniteStageProductAddHaar
    (S : Finset (HeightOneSpectrum ℤ)) :
    Measure (FieldOneFiniteStageAdele S) :=
  (addHaar : Measure ℝ).prod
    (Measure.pi fun v : ↥S =>
      (addHaar : Measure (v.1.adicCompletion ℚ)))

/-- Almost every finite-stage additive adele is coordinatewise invertible. -/
theorem fieldOneFiniteStageIdeleLocus_ae
    (S : Finset (HeightOneSpectrum ℤ)) :
    ∀ᵐ x ∂fieldOneFiniteStageProductAddHaar S,
      x ∈ fieldOneFiniteStageIdeleLocus S := by
  change
    ∀ᵐ x ∂(addHaar : Measure ℝ).prod
        (Measure.pi fun v : ↥S =>
          (addHaar : Measure (v.1.adicCompletion ℚ))),
      x ∈ fieldOneFiniteStageIdeleLocus S
  rw [Measure.ae_prod_mem_iff_ae_ae_mem
    (fieldOneFiniteStageIdeleLocus_isOpen S).measurableSet]
  have hreal :
      ∀ᵐ r ∂(addHaar : Measure ℝ), r ≠ 0 :=
    compl_mem_ae_iff.2 (measure_singleton 0)
  filter_upwards [hreal] with r hr
  have hfinite :
      ∀ᵐ x ∂Measure.pi
          (fun v : ↥S =>
            (addHaar : Measure (v.1.adicCompletion ℚ))),
        ∀ v, x v ≠ 0 := by
    rw [eventually_countable_forall]
    intro v
    exact Measure.ae_eval_ne
      (fun w : ↥S =>
        (addHaar : Measure (w.1.adicCompletion ℚ))) v 0
  filter_upwards [hfinite] with x hx
  exact ⟨hr, hx⟩

/-- The non-idele coordinate hyperplanes have product additive Haar measure
zero. -/
theorem fieldOneFiniteStageIdeleLocus_compl_null
    (S : Finset (HeightOneSpectrum ℤ)) :
    fieldOneFiniteStageProductAddHaar S
      (fieldOneFiniteStageIdeleLocus S)ᶜ = 0 := by
  rw [← compl_mem_ae_iff]
  simpa only [compl_compl] using
    (fieldOneFiniteStageIdeleLocus_ae S)

end

end GaloisForLFunctions.RHTower
