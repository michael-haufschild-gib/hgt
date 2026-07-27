import GaloisForLFunctions.HTGeometry.SemilinearJetCovariance
import GaloisForLFunctions.HTGeometry.TranscendentalMobius

/-!
# The semilinear clock acts by a Möbius transform on the generator

A semilinear clock dilation `σ` (`σ(w′) = λ·(σ w)′`, `λ ≠ 0` a differential constant) of a scalar
free differential field preserves exact differential order (`SemilinearJetCovariance`).  Running the
same order-balance argument as for a differential automorphism, `σ` sends the generator — in both
directions — by an *order-zero* differential rational function: `σ y, σ⁻¹ y ∈ C(y)`.  The degree-one
Lüroth transport `algEquiv_generator_mobius_of_mem` then makes `σ` act by an explicit `PGL₂` element:

`σ y · (c y + d) = a y + b`,  `a d − b c ≠ 0`,  `a, b, c, d ∈ C`.

This is step §3(a) of the clock-character classification for the *clock* (the semilinear cocharacter),
the exact analogue of §1 for the constraint.  It discharges the Möbius hypothesis of the family
diagonalization `commuting_family_scaling_character`.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- **Semilinear order-zero rigidity.**  A semilinear clock dilation of a scalar free differential
field sends its generator, and the inverse sends the generator, by exact order-zero differential
rational functions. -/
theorem clockSemilinearAlgEquiv_generator_order_zero
    {C E : Type*} [Field C] [Field E] [CharZero E]
    [Differential C] [Differential E] [Algebra C E] [DifferentialAlgebra C E]
    (σ : E ≃ₐ[C] E) {y : E} {lam : C} (hlam : lam ≠ 0)
    (hconst : (algebraMap C E lam)′ = 0)
    (hy : HypertranscendentalOver C y)
    (hytop : differentialAdjoin C ({y} : Set E) = ⊤)
    (hsemi : ∀ w : E, σ.toAlgHom w′ = algebraMap C E lam * (σ.toAlgHom w)′) :
    HasScalarDifferentialOrder C y (σ y) 0 ∧
      HasScalarDifferentialOrder C y (σ.symm y) 0 := by
  refine algEquiv_generator_order_zero σ hy hytop (fun m hm => ?_)
  simpa using hm.map_semilinear σ.toAlgHom hlam hconst hsemi

/-- **§3(a): the clock is Möbius on the generator.**  A semilinear clock dilation of a scalar free
differential field acts on its generator by a fractional-linear transform with base-field
coefficients. -/
theorem clockSemilinearAlgEquiv_generator_mobius
    {C E : Type*} [Field C] [Field E] [CharZero E]
    [Differential C] [Differential E] [Algebra C E] [DifferentialAlgebra C E]
    (σ : E ≃ₐ[C] E) {y : E} {lam : C} (hlam : lam ≠ 0)
    (hconst : (algebraMap C E lam)′ = 0)
    (hy : HypertranscendentalOver C y)
    (hytop : differentialAdjoin C ({y} : Set E) = ⊤)
    (hsemi : ∀ w : E, σ.toAlgHom w′ = algebraMap C E lam * (σ.toAlgHom w)′) :
    ∃ a b c d : C, a * d - b * c ≠ 0 ∧
      σ y * (algebraMap C E c * y + algebraMap C E d)
        = algebraMap C E a * y + algebraMap C E b := by
  obtain ⟨hz0, hsymm0⟩ :=
    clockSemilinearAlgEquiv_generator_order_zero σ hlam hconst hy hytop hsemi
  have hz : σ y ∈ IntermediateField.adjoin C ({y} : Set E) :=
    (hasScalarDifferentialOrder_zero_iff.mp hz0).1
  have hsymm : σ.symm y ∈ IntermediateField.adjoin C ({y} : Set E) :=
    (hasScalarDifferentialOrder_zero_iff.mp hsymm0).1
  have htrans : Transcendental C y := by
    simpa using hypertranscendentalOver_jet_transcendental hy 0
  exact algEquiv_generator_mobius_of_mem σ htrans hz hsymm

end

end GaloisForLFunctions.HTGeometry
