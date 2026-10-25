import GaloisForLFunctions.HTGeometry.InfiniteHilbertImagesHaveContinuumRank
import Mathlib.Analysis.Complex.Cardinality
import GaloisForLFunctions.ArithmeticDefectRigidity.TheCofactorLimitIsAWienerModule
import GaloisForLFunctions.HTGeometry.CountableAlgebraicDimensionForcesFiniteDimension
import GaloisForLFunctions.HTGeometry.CountableGramHilbertSpacesAreSeparable
import Mathlib.Analysis.Normed.Group.Quotient

/-!
# The algebraic index of the closed cofactor annihilator

The Wiener quotient is Banach. Its algebraic dimension is finite or continuum.
It is finite-dimensional exactly when the cyclic Hilbert module is, and their
finite dimensions agree.
-/
noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit

open ArithmeticOrientationTheory
open WienerAlgebraAt

/-- The algebraic index of the closed actual annihilator is never countably infinite. -/
theorem annihilator_quotient_rank_ne_aleph0 {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) :
    Module.rank ℂ (WienerAlgebraAt (1 / 2) ⧸ annihilator L) ≠ Cardinal.aleph0 := by
  letI : IsClosed (annihilator L : Set (WienerAlgebraAt (1 / 2))) := annihilator_closed L
  exact HTGeometry.banach_rank_ne_aleph0

/-- The Wiener quotient has either finite dimension or uncountable Hamel dimension. -/
theorem annihilator_quotient_finite_or_uncountable {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) :
    FiniteDimensional ℂ (WienerAlgebraAt (1 / 2) ⧸ annihilator L) ∨
      Cardinal.aleph0 < Module.rank ℂ (WienerAlgebraAt (1 / 2) ⧸ annihilator L) := by
  letI : IsClosed (annihilator L : Set (WienerAlgebraAt (1 / 2))) := annihilator_closed L
  exact HTGeometry.banach_finite_or_uncountable

/-- The continuous orbit map of the actual cyclic receiver. -/
def cyclicLinear {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) : WienerAlgebraAt (1 / 2) →L[ℂ] Hilbert L :=
  (ContinuousLinearMap.apply ℂ (Hilbert L) (vector L 1)).comp (wienerLinear L)

theorem cyclicLinear_apply {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) (a : WienerAlgebraAt (1 / 2)) :
    cyclicLinear L a = wienerRepresentation L a (vector L 1) := rfl

theorem cyclicLinear_ker {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) :
    (cyclicLinear L).ker = (annihilator L).restrictScalars ℂ := by
  ext a
  exact (mem_annihilator_iff L a).symm

/-- The algebraic quotient identifies with the dense cyclic image. -/
def quotientEquivCyclicRange {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) :
    (WienerAlgebraAt (1 / 2) ⧸ annihilator L) ≃ₗ[ℂ] (cyclicLinear L).range := by
  have h := (cyclicLinear L).toLinearMap.quotKerEquivRange
  change (WienerAlgebraAt (1 / 2) ⧸ (cyclicLinear L).ker) ≃ₗ[ℂ]
    (cyclicLinear L).range at h
  rw [cyclicLinear_ker] at h
  exact h

theorem cyclicLinear_dense_range {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) :
    Dense ((cyclicLinear L).range : Set (Hilbert L)) := by
  apply (HTGeometry.KernelHilbert.dense_span_vectors (complexKernel L)).mono
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  refine ⟨pointMass j, ?_⟩
  change wienerRepresentation L (pointMass j) (vector L 1) = vector L j
  rw [wienerRepresentation_pointMass, dilation_vector, mul_one]

theorem cyclicLinear_range_eq_top_of_finite {ε : SubcriticalDamping} (L : ActualCofactorLimit ε)
    [FiniteDimensional ℂ (cyclicLinear L).range] : (cyclicLinear L).range = ⊤ := by
  apply SetLike.coe_injective
  change ((cyclicLinear L).range : Set (Hilbert L)) = Set.univ
  exact (cyclicLinear L).range.closed_of_finiteDimensional.closure_eq.symm.trans
    (cyclicLinear_dense_range L).closure_eq

/-- Finite quotient index and finite Hilbert dimension are equivalent. -/
theorem finiteDimensional_quotient_iff {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) :
    FiniteDimensional ℂ (WienerAlgebraAt (1 / 2) ⧸ annihilator L) ↔
      FiniteDimensional ℂ (Hilbert L) := by
  constructor
  · intro h
    letI := h
    letI : FiniteDimensional ℂ (cyclicLinear L).range :=
      FiniteDimensional.of_injective (quotientEquivCyclicRange L).symm.toLinearMap
        (quotientEquivCyclicRange L).symm.injective
    apply FiniteDimensional.of_surjective (cyclicLinear L).range.subtype
    intro x
    refine ⟨⟨x, ?_⟩, rfl⟩
    rw [cyclicLinear_range_eq_top_of_finite]
    trivial
  · intro h
    letI := h
    exact FiniteDimensional.of_injective (quotientEquivCyclicRange L).toLinearMap
      (quotientEquivCyclicRange L).injective

/-- When the cyclic module is finite-dimensional, its algebraic quotient is the whole module. -/
def quotientEquivHilbert {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) [FiniteDimensional ℂ (Hilbert L)] :
    (WienerAlgebraAt (1 / 2) ⧸ annihilator L) ≃ₗ[ℂ] Hilbert L :=
  (quotientEquivCyclicRange L).trans
    (LinearEquiv.ofTop (cyclicLinear L).range (cyclicLinear_range_eq_top_of_finite L))

theorem finrank_quotient_eq_of_finite {ε : SubcriticalDamping} (L : ActualCofactorLimit ε)
    [FiniteDimensional ℂ (Hilbert L)] :
    Module.finrank ℂ (WienerAlgebraAt (1 / 2) ⧸ annihilator L) =
      Module.finrank ℂ (Hilbert L) := (quotientEquivHilbert L).finrank_eq


end GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit

namespace GaloisForLFunctions.ArithmeticDefectRigidity.CofactorLimit

open ArithmeticOrientationTheory
open WienerAlgebraAt

theorem annihilator_quotient_rank_ne_aleph0 (ε : SubcriticalDamping) :
    Module.rank ℂ (WienerAlgebraAt (1 / 2) ⧸ annihilator ε) ≠ Cardinal.aleph0 :=
  ActualCofactorLimit.annihilator_quotient_rank_ne_aleph0 (ActualCofactorLimit.chosen ε)

theorem annihilator_quotient_finite_or_uncountable (ε : SubcriticalDamping) :
    FiniteDimensional ℂ (WienerAlgebraAt (1 / 2) ⧸ annihilator ε) ∨
      Cardinal.aleph0 < Module.rank ℂ (WienerAlgebraAt (1 / 2) ⧸ annihilator ε) :=
  ActualCofactorLimit.annihilator_quotient_finite_or_uncountable (ActualCofactorLimit.chosen ε)

abbrev cyclicLinear (ε : SubcriticalDamping) : WienerAlgebraAt (1 / 2) →L[ℂ] Hilbert ε :=
  ActualCofactorLimit.cyclicLinear (ActualCofactorLimit.chosen ε)

theorem cyclicLinear_apply (ε : SubcriticalDamping) (a : WienerAlgebraAt (1 / 2)) :
    cyclicLinear ε a = wienerRepresentation ε a (vector ε 1) :=
  ActualCofactorLimit.cyclicLinear_apply (ActualCofactorLimit.chosen ε) a

theorem cyclicLinear_ker (ε : SubcriticalDamping) :
    (cyclicLinear ε).ker = (annihilator ε).restrictScalars ℂ :=
  ActualCofactorLimit.cyclicLinear_ker (ActualCofactorLimit.chosen ε)

abbrev quotientEquivCyclicRange (ε : SubcriticalDamping) :
    (WienerAlgebraAt (1 / 2) ⧸ annihilator ε) ≃ₗ[ℂ] (cyclicLinear ε).range :=
  ActualCofactorLimit.quotientEquivCyclicRange (ActualCofactorLimit.chosen ε)

theorem cyclicLinear_dense_range (ε : SubcriticalDamping) :
    Dense ((cyclicLinear ε).range : Set (Hilbert ε)) :=
  ActualCofactorLimit.cyclicLinear_dense_range (ActualCofactorLimit.chosen ε)

theorem cyclicLinear_range_eq_top_of_finite (ε : SubcriticalDamping)
    [FiniteDimensional ℂ (cyclicLinear ε).range] : (cyclicLinear ε).range = ⊤ :=
  ActualCofactorLimit.cyclicLinear_range_eq_top_of_finite (ActualCofactorLimit.chosen ε)

theorem finiteDimensional_quotient_iff (ε : SubcriticalDamping) :
    FiniteDimensional ℂ (WienerAlgebraAt (1 / 2) ⧸ annihilator ε) ↔
      FiniteDimensional ℂ (Hilbert ε) :=
  ActualCofactorLimit.finiteDimensional_quotient_iff (ActualCofactorLimit.chosen ε)

abbrev quotientEquivHilbert (ε : SubcriticalDamping) [FiniteDimensional ℂ (Hilbert ε)] :
    (WienerAlgebraAt (1 / 2) ⧸ annihilator ε) ≃ₗ[ℂ] Hilbert ε :=
  ActualCofactorLimit.quotientEquivHilbert (ActualCofactorLimit.chosen ε)

theorem finrank_quotient_eq_of_finite (ε : SubcriticalDamping)
    [FiniteDimensional ℂ (Hilbert ε)] :
    Module.finrank ℂ (WienerAlgebraAt (1 / 2) ⧸ annihilator ε) =
      Module.finrank ℂ (Hilbert ε) :=
  ActualCofactorLimit.finrank_quotient_eq_of_finite (ActualCofactorLimit.chosen ε)

end GaloisForLFunctions.ArithmeticDefectRigidity.CofactorLimit

namespace GaloisForLFunctions.ArithmeticOrientationTheory.WienerAlgebraAt

/-- Wiener coefficients inject into a countable complex sequence. -/
theorem cardinal_le_continuum (σ : ℝ) :
    Cardinal.mk (WienerAlgebraAt σ) ≤ Cardinal.continuum := by
  have hinj : Function.Injective
      (fun a : WienerAlgebraAt σ => fun n : ℕ => a.toFn n) := by
    intro a b hab
    apply toFn_injective
    ext n
    exact congrFun hab n
  have h := Cardinal.mk_le_of_injective hinj
  simpa only [Cardinal.mk_arrow, Cardinal.mk_complex, Cardinal.mk_nat,
    Cardinal.lift_id, Cardinal.continuum_power_aleph0] using h

end GaloisForLFunctions.ArithmeticOrientationTheory.WienerAlgebraAt

namespace GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit

open ArithmeticOrientationTheory

/-- An infinite actual cyclic module has exactly continuum algebraic quotient index. -/
theorem annihilator_quotient_rank_eq_continuum_of_infinite {ε : SubcriticalDamping}
    (L : ActualCofactorLimit ε) (hH : ¬ FiniteDimensional ℂ (Hilbert L)) :
    Module.rank ℂ (WienerAlgebraAt (1 / 2) ⧸ annihilator L) = Cardinal.continuum := by
  have hrange : ¬ FiniteDimensional ℂ (cyclicLinear L).range := by
    intro h
    letI := h
    apply hH
    apply (finiteDimensional_quotient_iff L).mp
    exact FiniteDimensional.of_injective (quotientEquivCyclicRange L).toLinearMap
      (quotientEquivCyclicRange L).injective
  rw [(quotientEquivCyclicRange L).rank_eq]
  exact HTGeometry.rank_hilbert_image_eq_continuum (cyclicLinear L)
    (WienerAlgebraAt.cardinal_le_continuum (1 / 2)) hrange

/-- Every actual quotient index is finite with its Hilbert dimension, or exactly continuum. -/
theorem annihilator_quotient_finite_or_continuum {ε : SubcriticalDamping}
    (L : ActualCofactorLimit ε) :
    (FiniteDimensional ℂ (Hilbert L) ∧
      Module.finrank ℂ (WienerAlgebraAt (1 / 2) ⧸ annihilator L) =
        Module.finrank ℂ (Hilbert L)) ∨
      Module.rank ℂ (WienerAlgebraAt (1 / 2) ⧸ annihilator L) = Cardinal.continuum := by
  by_cases h : FiniteDimensional ℂ (Hilbert L)
  · letI := h
    exact Or.inl ⟨h, finrank_quotient_eq_of_finite L⟩
  · exact Or.inr (annihilator_quotient_rank_eq_continuum_of_infinite L h)

end GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit
