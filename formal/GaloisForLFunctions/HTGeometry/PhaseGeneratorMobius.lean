import GaloisForLFunctions.HTGeometry.ScalarDifferentialRationalOrder
import GaloisForLFunctions.HTGeometry.RationalGeneratorMobius
import GaloisForLFunctions.HTGeometry.SchwarzianProjectiveInvariant

/-!
# A differential automorphism moves the generator by a Möbius transform

A differential automorphism of a scalar free differential field carries the generator into the
*ordinary* rational function field it generates, in both directions.  So the generator and its image
generate the same simple extension, and a change of generator of a simple purely transcendental
extension is projective.

Hence the transition of a scalar protocol acts on the phase generator by an element of `PGL₂` over the
constants — the projective transition of a nonautonomous tail.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open IntermediateField

noncomputable section

/-- **The projective transition.**  A differential automorphism of a scalar free differential field
sends the generator to a Möbius transform of it, with invertible coefficient matrix over the
constants. -/
theorem exists_mobius_of_differentialAlgEquiv {C E : Type*} [Field C] [Field E] [CharZero E]
    [Differential C] [Differential E] [Algebra C E] [DifferentialAlgebra C E]
    (σ : E ≃ₐ[C] E) {y : E} (hy : HypertranscendentalOver C y)
    (hytop : differentialAdjoin C ({y} : Set E) = ⊤)
    (hderiv : ∀ w : E, σ w′ = (σ w)′) :
    ∃ a b c d : C, a * d - b * c ≠ 0 ∧
      σ y * (algebraMap C E c * y + algebraMap C E d)
        = algebraMap C E a * y + algebraMap C E b := by
  obtain ⟨hmem, hmem'⟩ := differentialAlgEquiv_generator_mem_adjoin_singleton σ hy hytop hderiv
  have hty : Transcendental C y := by
    simpa using hypertranscendentalOver_jet_transcendental hy 0
  -- the automorphism carries the generator's field to the image's field
  have hmapEq : IntermediateField.map (σ : E →ₐ[C] E) C⟮y⟯ = C⟮σ y⟯ := by
    rw [IntermediateField.adjoin_map]
    congr 1
    simp
  have hymem : y ∈ C⟮σ y⟯ := by
    rw [← hmapEq]
    exact ⟨σ.symm y, hmem', by simp⟩
  exact exists_mobius_of_mutual_adjoin hty hmem hymem

/-- **The Schwarzian of the generator is fixed by every differential automorphism.**  The transition
is projective, and the Schwarzian is a projective invariant, so the observable is transported
unchanged. -/
theorem schwarzian_fixed_of_differentialAlgEquiv {C E : Type*} [Field C] [Field E] [CharZero E]
    [Differential C] [Differential E] [Algebra C E] [DifferentialAlgebra C E]
    (σ : E ≃ₐ[C] E) {y : E} (hy : HypertranscendentalOver C y)
    (hytop : differentialAdjoin C ({y} : Set E) = ⊤)
    (hderiv : ∀ w : E, σ w′ = (σ w)′)
    (hconst : ∀ t : C, (algebraMap C E t)′ = 0) :
    σ (schwarzian y) = schwarzian y := by
  obtain ⟨a, b, c, d, hdet, hmob⟩ :=
    exists_mobius_of_differentialAlgEquiv σ hy hytop hderiv
  have hty : Transcendental C y := by
    simpa using hypertranscendentalOver_jet_transcendental hy 0
  have hinj : Function.Injective (algebraMap C E) := (algebraMap C E).injective
  -- the determinant stays invertible downstairs
  have hdetE : algebraMap C E a * algebraMap C E d - algebraMap C E b * algebraMap C E c ≠ 0 := by
    have : algebraMap C E (a * d - b * c) ≠ 0 := by
      simpa using fun h => hdet (hinj (by simpa using h))
    simpa using this
  -- the denominator cannot vanish
  have hden : algebraMap C E c * y + algebraMap C E d ≠ 0 := by
    intro h0
    by_cases hc : c = 0
    · have hd : d = 0 := by
        rw [hc] at h0
        simpa using hinj (by simpa using h0)
      exact hdet (by rw [hc, hd]; ring)
    · refine hty ?_
      refine ⟨Polynomial.C c * Polynomial.X + Polynomial.C d, ?_, ?_⟩
      · intro hpoly
        exact hc (by simpa using congrArg (fun p => Polynomial.coeff p 1) hpoly)
      · simpa using h0
  -- the derivative of the generator is nonzero
  have hdu : y′ ≠ 0 := by
    intro h0
    have hjet : Transcendental C (differentialJet 1 y) :=
      hypertranscendentalOver_jet_transcendental hy 1
    rw [show differentialJet 1 y = y′ from by simp [differentialJet_succ], h0] at hjet
    exact hjet (isAlgebraic_zero)
  have htrans : (σ : E →ₐ[C] E) y
      = (algebraMap C E a * y + algebraMap C E b) / (algebraMap C E c * y + algebraMap C E d) := by
    rw [eq_div_iff hden]
    exact hmob
  exact schwarzian_fixed_of_projective_semiconjugacy (σ : E →ₐ[C] E) hderiv y
    (algebraMap C E a) (algebraMap C E b) (algebraMap C E c) (algebraMap C E d)
    (hconst a) (hconst b) (hconst c) (hconst d) hdetE hden hdu htrans

end

end GaloisForLFunctions.HTGeometry
