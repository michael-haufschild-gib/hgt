import GaloisForLFunctions.HTGeometry.ScalarDifferentialRationalOrder
import GaloisForLFunctions.HTGeometry.TranscendentalMobius
import GaloisForLFunctions.HTGeometry.ClockChargeProjectiveLinearization

/-!
# The constraint acts by a Möbius transform on the persistent generator

Combining the differential order-zero rigidity
(`differentialAlgEquiv_generator_mem_adjoin_singleton`: a differential automorphism `σ` of a scalar
free differential field sends the generator, in both directions, into the ordinary rational
subfield) with the abstract degree-one Lüroth transport (`adjoin_generator_mobius`) shows that `σ`
acts on the generator by an explicit `PGL₂` element:

`σ y · (c y + d) = a y + b`,  `a d - b c ≠ 0`,  `a, b, c, d ∈ C`.

This is step §1 of the clock-character classification, formalized in the differential framework, and
supplies the Möbius hypothesis of the charged-phase rigidity `charged_clock_forces_multiplicative`.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

/-- **§1: the constraint is Möbius on the generator.**  A differential automorphism of a scalar
free differential field acts on its generator by a fractional-linear transform with base-field
coefficients. -/
theorem differentialAlgEquiv_generator_mobius
    {C E : Type*} [Field C] [Field E] [CharZero E]
    [Differential C] [Differential E] [Algebra C E] [DifferentialAlgebra C E]
    (σ : E ≃ₐ[C] E) {y : E} (hy : HypertranscendentalOver C y)
    (hytop : differentialAdjoin C ({y} : Set E) = ⊤)
    (hderiv : ∀ w : E, σ w′ = (σ w)′) :
    ∃ a b c d : C, a * d - b * c ≠ 0 ∧
      σ y * (algebraMap C E c * y + algebraMap C E d)
        = algebraMap C E a * y + algebraMap C E b := by
  obtain ⟨hz, hsymm⟩ :=
    differentialAlgEquiv_generator_mem_adjoin_singleton σ hy hytop hderiv
  have htrans : Transcendental C y := by
    simpa using hypertranscendentalOver_jet_transcendental hy 0
  exact algEquiv_generator_mobius_of_mem σ htrans hz hsymm

/-- **§1→§4: charged-phase rigidity in the differential framework.**  Let `σ` be a differential
automorphism of the scalar free field (the persistent constraint) and `ρ` a `C`-algebra
endomorphism (the clock) that acts on the generator by a nontrivial pure scaling `ρ y = μ y`
(`μ ≠ 0, 1, -1` — the diagonalized positive-charge cocharacter) and commutes with `σ` at `y`.  Then
`σ` acts on the generator by multiplication by a single constant: `σ y = e · y`.

The pure-scaling hypothesis `ρ y = μ y` is the output of the `PGL₂`-cocharacter diagonalization
(step §3); everything else is discharged from the differential order-zero rigidity and degree-one
Lüroth. -/
theorem differentialAlgEquiv_generator_multiplicative
    {C E : Type*} [Field C] [Field E] [CharZero E]
    [Differential C] [Differential E] [Algebra C E] [DifferentialAlgebra C E]
    (σ : E ≃ₐ[C] E) (ρ : E →ₐ[C] E) {y : E} {μ : C}
    (hy : HypertranscendentalOver C y)
    (hytop : differentialAdjoin C ({y} : Set E) = ⊤)
    (hderiv : ∀ w : E, σ w′ = (σ w)′)
    (hμ0 : μ ≠ 0) (hμ1 : μ ≠ 1) (hμm1 : μ ≠ -1)
    (hρy : ρ y = algebraMap C E μ * y)
    (hcomm : σ.toAlgHom (ρ y) = ρ (σ.toAlgHom y)) :
    ∃ e : C, σ y = algebraMap C E e * y := by
  obtain ⟨a, b, c, d, hdet, hΦq⟩ :=
    differentialAlgEquiv_generator_mobius σ hy hytop hderiv
  have htrans : Transcendental C y := by
    simpa using hypertranscendentalOver_jet_transcendental hy 0
  -- `1, y, y²` are linearly independent over `C`
  have hlin : ∀ x y' z : C, algebraMap C E x + algebraMap C E y' * y
      + algebraMap C E z * y ^ (2 : ℕ) = 0 → x = 0 ∧ y' = 0 ∧ z = 0 := by
    intro x y' z heq
    have hinj := transcendental_iff_injective.mp htrans
    have hP : (Polynomial.aeval y)
        (Polynomial.C x + Polynomial.C y' * Polynomial.X
          + Polynomial.C z * Polynomial.X ^ (2 : ℕ)) = 0 := by
      simp only [map_add, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
      exact heq
    have hP0 : Polynomial.C x + Polynomial.C y' * Polynomial.X
        + Polynomial.C z * Polynomial.X ^ (2 : ℕ) = 0 :=
      hinj (by rw [hP, map_zero])
    refine ⟨?_, ?_, ?_⟩
    · have := congrArg (Polynomial.coeff · 0) hP0; simpa using this
    · have := congrArg (Polynomial.coeff · 1) hP0; simpa using this
    · have := congrArg (Polynomial.coeff · 2) hP0; simpa using this
  -- apply the charged no-go
  have hΦ := charged_clock_forces_multiplicative σ.toAlgHom ρ y
    hμ0 hμ1 hμm1 hdet hlin hρy hΦq hcomm
  exact ⟨a / d, hΦ⟩

end GaloisForLFunctions.HTGeometry
