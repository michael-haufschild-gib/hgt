import GaloisForLFunctions.HTGeometry.KaehlerAnnihilatorDeterminant

/-!
# Invertible Jacobian determinant implies formal unramifiedness

This module packages the Kähler-annihilator determinant criterion into the corresponding
formal-unramifiedness statement.  It is useful after localization, where a Jacobian determinant
becomes a unit.
-/

namespace GaloisForLFunctions.HTGeometry

open KaehlerDifferential

variable {k A B : Type*} [CommRing k] [CommRing A] [CommRing B]
variable [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- If a coordinate Jacobian determinant is a unit, the relative Kähler module vanishes. -/
theorem formallyUnramified_of_isUnit_det
    (b : Module.Basis ι B Ω[B⁄k]) (y : ι → A) (P : Matrix ι ι B)
    (hgen : ∀ a : A, KaehlerDifferential.D k B (algebraMap A B a)
      ∈ Submodule.span B (Set.range fun j =>
        KaehlerDifferential.D k B (algebraMap A B (y j))))
    (hvw : ∀ j, KaehlerDifferential.D k B (algebraMap A B (y j)) =
      ∑ i, P i j • b i)
    (hunit : IsUnit P.det) :
    Algebra.FormallyUnramified A B := by
  rw [Algebra.formallyUnramified_iff]
  have htop : Module.annihilator B Ω[B⁄A] = ⊤ :=
    Ideal.eq_top_of_isUnit_mem (Module.annihilator B Ω[B⁄A])
      (det_mem_annihilator_kaehler b y P hgen hvw) hunit
  exact (Module.annihilator_eq_top_iff (R := B) (M := Ω[B⁄A])).mp htop

end GaloisForLFunctions.HTGeometry
