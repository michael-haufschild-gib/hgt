import GaloisForLFunctions.HTGeometry.FracXTranscendental
import GaloisForLFunctions.HTGeometry.CriticalGeometricFieldPrimitivity

/-!
# The critical tower keeps its primitivity over a free parameter

Adjoining an independent transcendental to the observation field does not create an intermediate
field below the source: the base-change lattice theorem applies to the critical normal closure, whose
Galois group is full by monodromy.

This is the third input of the one-step rigidity assembly, the other two being that the postcritical
reciprocal coordinate lies in the source extended by the new raw coordinate, and that it escapes the
observation field extended by it.
-/

open IntermediateField

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Pulling an intermediate field back along an embedding and pushing it forward again returns it,
provided it sits inside the range. -/
theorem map_comap_eq_of_le_fieldRange {F L L' : Type*} [Field F] [Field L] [Field L']
    [Algebra F L] [Algebra F L'] (f : L →ₐ[F] L') (P : IntermediateField F L')
    (hP : P ≤ f.fieldRange) : (P.comap f).map f = P := by
  refine le_antisymm ?_ ?_
  · rintro y ⟨x, hx, rfl⟩
    exact hx
  · intro y hy
    obtain ⟨x, rfl⟩ := hP hy
    exact ⟨x, hy, rfl⟩

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]

/-- The embedded critical source field, inside the rational functions over the normal closure. -/
def criticalSourceFracRange (m n : ℕ) :
    IntermediateField (criticalObservationField K m n)
      (FractionRing (Polynomial (criticalNormalClosure K m n))) :=
  ((criticalSourceNormalClosureEmbedding K m n).fieldRange).map
    (IsScalarTower.toAlgHom (criticalObservationField K m n) (criticalNormalClosure K m n)
      (FractionRing (Polynomial (criticalNormalClosure K m n))))

/-- **Primitivity survives the free parameter.**  Given full geometric monodromy, no field lies
strictly between the observation field extended by a free parameter and the source field extended by
it. -/
theorem eq_bot_or_eq_adjoin_criticalSourceFracRange_of_full_monodromy
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hfull : criticalGeometricMonodromy K m n = ⊤)
    (M : IntermediateField
      (↥(criticalObservationField K m n)⟮fracX (criticalNormalClosure K m n)⟯)
      (FractionRing (Polynomial (criticalNormalClosure K m n))))
    (hM : M ≤ IntermediateField.adjoin
      (↥(criticalObservationField K m n)⟮fracX (criticalNormalClosure K m n)⟯)
      (criticalSourceFracRange K m n : Set (FractionRing
        (Polynomial (criticalNormalClosure K m n))))) :
    M = ⊥ ∨ M = IntermediateField.adjoin
      (↥(criticalObservationField K m n)⟮fracX (criticalNormalClosure K m n)⟯)
      (criticalSourceFracRange K m n : Set (FractionRing
        (Polynomial (criticalNormalClosure K m n)))) := by
  classical
  letI : FiniteDimensional (criticalObservationField K m n)
      (criticalSourceField K m n) :=
    criticalSourceField_finiteDimensional_criticalObservationField K hm hn
  letI : FiniteDimensional (criticalObservationField K m n)
      (criticalNormalClosure K m n) :=
    criticalNormalClosure_finiteDimensional K hm hn
  letI : Algebra.IsSeparable (criticalObservationField K m n)
      (criticalSourceField K m n) := inferInstance
  letI : IsScalarTower (criticalObservationField K m n)
      (criticalSourceField K m n) (criticalSourceAlgebraicClosure K m n) :=
    AlgebraicClosure.instIsScalarTower (criticalSourceField K m n)
  letI : Algebra.IsAlgebraic (criticalObservationField K m n)
      (criticalSourceAlgebraicClosure K m n) :=
    Algebra.IsAlgebraic.trans (criticalObservationField K m n)
      (criticalSourceField K m n) (criticalSourceAlgebraicClosure K m n)
  letI : Normal (criticalObservationField K m n)
      (criticalSourceAlgebraicClosure K m n) :=
    { splits' _ := IsAlgClosed.splits _ }
  letI : Normal (criticalObservationField K m n)
      (criticalNormalClosure K m n) :=
    normalClosure.normal (criticalObservationField K m n)
      (criticalSourceField K m n) (criticalSourceAlgebraicClosure K m n)
  letI : IsGalois (criticalObservationField K m n)
      (criticalNormalClosure K m n) := inferInstance
  set F := criticalObservationField K m n
  set E := criticalNormalClosure K m n
  set f := IsScalarTower.toAlgHom (↥F) E (FractionRing (Polynomial E)) with hf
  have hJle : criticalSourceFracRange K m n ≤ fracCoeffField (↥F) E := by
    rintro y ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩
  have hprim : ∀ P : IntermediateField (↥F) (FractionRing (Polynomial E)),
      P ≤ criticalSourceFracRange K m n → P = ⊥ ∨ P = criticalSourceFracRange K m n := by
    intro P hP
    have hPrange : P ≤ f.fieldRange := by
      refine le_trans hP ?_
      rintro y ⟨x, -, rfl⟩
      exact ⟨x, rfl⟩
    have hmapcomap : (P.comap f).map f = P := map_comap_eq_of_le_fieldRange f P hPrange
    have hP'le : P.comap f ≤ (criticalSourceNormalClosureEmbedding K m n).fieldRange := by
      intro x hx
      have hfx : f x ∈ criticalSourceFracRange K m n := hP hx
      obtain ⟨z, hz, hzeq⟩ := hfx
      have hinj : Function.Injective f := f.toRingHom.injective
      have : x = z := hinj hzeq.symm
      rw [this]
      exact hz
    rcases eq_bot_or_eq_criticalSourceNormalClosureFieldRange_of_full_monodromy K hm hn hfull
      (P.comap f) hP'le with h | h
    · left
      rw [← hmapcomap, h, IntermediateField.map_bot]
    · right
      rw [← hmapcomap, h]
      rfl
  exact eq_bot_or_eq_adjoin_fracX_of_primitive (criticalSourceFracRange K m n) hJle hprim M hM

end GaloisForLFunctions.HTGeometry

end
