import GaloisForLFunctions.HTGeometry.PositiveDimensionalInvariantGeneration
import Mathlib.RingTheory.Nullstellensatz

/-!
# Rational-point separation for affine torsors

The Nullstellensatz makes evaluation on all rational points jointly injective for every reduced
finite-type affine algebra over an algebraically closed field.  A reduced finite presentation of
the base-changed coordinate algebra therefore constructs the point-separating action required by
positive-dimensional invariant generation; joint injectivity is proved, not assumed.
-/

open scoped TensorProduct

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v w

section Nullstellensatz

variable {C : Type u} [Field C] [IsAlgClosed C]
variable {sigma : Type v} [Finite sigma]
variable (I : Ideal (MvPolynomial sigma C))

/-- Rational points of a reduced finite-type affine presentation. -/
abbrev AffineVarietyPoint :=
  {x : sigma → C // x ∈ MvPolynomial.zeroLocus C I}

/-- Evaluation of a quotient coordinate ring at a point of its zero locus. -/
def affineVarietyPointEvaluation (x : AffineVarietyPoint I) :
    MvPolynomial sigma C ⧸ I →ₐ[C] C :=
  Ideal.Quotient.liftₐ I (MvPolynomial.aeval x.1) fun p hp ↦
    MvPolynomial.mem_zeroLocus_iff.mp x.2 p hp

omit [IsAlgClosed C] [Finite sigma] in
@[simp]
theorem affineVarietyPointEvaluation_mk (x : AffineVarietyPoint I)
    (p : MvPolynomial sigma C) :
    affineVarietyPointEvaluation I x (Ideal.Quotient.mk I p) =
      MvPolynomial.aeval x.1 p := rfl

/-- Nullstellensatz point separation: all rational-point evaluations jointly inject into the
function algebra on the zero locus. -/
theorem affineVarietyPointEvaluation_jointlyInjective (hI : I.IsRadical) :
    Function.Injective
      (fun z : MvPolynomial sigma C ⧸ I ↦
        fun x : AffineVarietyPoint I ↦ affineVarietyPointEvaluation I x z) := by
  intro z w hzw
  rw [← sub_eq_zero]
  obtain ⟨p, hp⟩ := Ideal.Quotient.mkₐ_surjective C I (z - w)
  rw [← hp]
  have hpv : p ∈ MvPolynomial.vanishingIdeal C (MvPolynomial.zeroLocus C I) := by
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    intro x hx
    have he := congrFun hzw ⟨x, hx⟩
    change affineVarietyPointEvaluation I ⟨x, hx⟩ z =
      affineVarietyPointEvaluation I ⟨x, hx⟩ w at he
    have hz : affineVarietyPointEvaluation I ⟨x, hx⟩ (z - w) = 0 := by
      rw [map_sub, he, sub_self]
    rw [← hp] at hz
    simpa using hz
  rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical I, hI.radical] at hpv
  simpa only [Ideal.Quotient.mkₐ_eq_mk] using
    (Ideal.Quotient.eq_zero_iff_mem.mpr hpv)

end Nullstellensatz

section TorsorConstructor

variable {E : Type u} {L : Type v} {A : Type w}
variable [Field E] [Field L] [Algebra E L] [CommRing A] [Algebra E A]
variable [IsAlgClosed L]
variable {sigma : Type w} [Finite sigma]
variable (I : Ideal (MvPolynomial sigma L))

/-- A reduced finite-type presentation of the base-changed acting coordinate algebra gives a
canonical point-separating torsor action. -/
def PointSeparatingTorsorAction.ofReducedFinitePresentation
    (T : AffineTorsorCoaction E L A)
    (hI : I.IsRadical)
    (presentation : L ⊗[E] A ≃ₐ[L] MvPolynomial sigma L ⧸ I) :
    PointSeparatingTorsorAction E L A where
  toAffineTorsorCoaction := T
  Point := ULift.{max u v w} (AffineVarietyPoint I)
  evaluation x := (affineVarietyPointEvaluation I x.down).comp presentation.toAlgHom
  evaluation_jointlyInjective := by
    intro z w hzw
    apply presentation.injective
    apply affineVarietyPointEvaluation_jointlyInjective I hI
    funext x
    exact congrFun hzw (ULift.up x)

/-- For a reduced finite-type presentation, rational-point invariants of an affine torsor are
exactly base scalars. -/
theorem AffineTorsorCoaction.fixedByPresentedPoints_eq_range
    (T : AffineTorsorCoaction E L A)
    (hI : I.IsRadical)
    (presentation : L ⊗[E] A ≃ₐ[L] MvPolynomial sigma L ⧸ I) :
    {x : L | ∀ p : ULift.{max u v w} (AffineVarietyPoint I),
      ((affineVarietyPointEvaluation I p.down).comp presentation.toAlgHom) (T.coaction x) = x} =
      Set.range (algebraMap E L) := by
  exact (PointSeparatingTorsorAction.ofReducedFinitePresentation I T hI presentation)
    |>.fixedByPoints_eq_range

end TorsorConstructor

end

end GaloisForLFunctions.HTGeometry
