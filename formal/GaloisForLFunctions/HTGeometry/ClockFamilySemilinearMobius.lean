import GaloisForLFunctions.HTGeometry.ClockSemilinearOrderZeroMobius
import GaloisForLFunctions.HTGeometry.ClockScalingCharacterNonzero

/-!
# The semilinear clock family diagonalizes to a `C^*`-character

Assembling §3(a) into the family diagonalization: a clock cocharacter presented as a family of
semilinear automorphisms `ρ_λ` (`ρ_λ(w′) = λ·(ρ_λ w)′`, `λ` a differential constant) of a scalar
free differential field, homomorphic at the generator on `C^*` and commuting with an anchor scaling
`ρ_{ν₀} q = ν q` (`ν ≠ 0, 1, -1`), diagonalizes: there is a character `e : C → C` with
`ρ_λ q = e(λ)·q` and `e(λμ) = e(λ)e(μ)` on `C^*`.

The Möbius hypothesis `hmob` — the last geometric input of `commuting_family_scaling_character_of_nonzero`
— is discharged here from the semilinear order-zero rigidity `clockSemilinearAlgEquiv_generator_mobius`,
so the character is produced from clock hypotheses alone.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

/-- **The commuting semilinear clock family is a `C^*`-character.**  Each nonzero clock member is
Möbius on the generator (semilinear order-zero rigidity), so the commuting family diagonalizes to a
multiplicative scaling character. -/
theorem clock_family_scaling_character_from_semilinear
    {C E : Type*} [Field C] [Field E] [CharZero E]
    [Differential C] [Differential E] [Algebra C E] [DifferentialAlgebra C E]
    (ρ : C → (E ≃ₐ[C] E)) (ν₀ : C) {q : E} {ν : C}
    (hν0 : ν ≠ 0) (hν1 : ν ≠ 1) (hνm1 : ν ≠ -1)
    (hy : HypertranscendentalOver C q)
    (hytop : differentialAdjoin C ({q} : Set E) = ⊤)
    (hconst : ∀ lam : C, (algebraMap C E lam)′ = 0)
    (hsemi : ∀ lam : C, lam ≠ 0 →
      ∀ w : E, (ρ lam).toAlgHom w′ = algebraMap C E lam * ((ρ lam).toAlgHom w)′)
    (hanchor : (ρ ν₀).toAlgHom q = algebraMap C E ν * q)
    (hlin : ∀ x y z : C, algebraMap C E x + algebraMap C E y * q
        + algebraMap C E z * q ^ (2 : ℕ) = 0 → x = 0 ∧ y = 0 ∧ z = 0)
    (hcomm : ∀ lam, lam ≠ 0 →
      (ρ lam).toAlgHom ((ρ ν₀).toAlgHom q) = (ρ ν₀).toAlgHom ((ρ lam).toAlgHom q))
    (hmul : ∀ lam mu, lam ≠ 0 → mu ≠ 0 →
      (ρ (lam * mu)).toAlgHom q = (ρ lam).toAlgHom ((ρ mu).toAlgHom q)) :
    ∃ e : C → C, (∀ lam, lam ≠ 0 → (ρ lam).toAlgHom q = algebraMap C E (e lam) * q)
      ∧ (∀ lam mu, lam ≠ 0 → mu ≠ 0 → e (lam * mu) = e lam * e mu) := by
  have hq : q ≠ 0 := by
    have htrans : Transcendental C q := by
      simpa using hypertranscendentalOver_jet_transcendental hy 0
    rintro rfl; exact htrans isAlgebraic_zero
  have hmob : ∀ lam, lam ≠ 0 → ∃ a b c d : C, a * d - b * c ≠ 0 ∧
      (ρ lam).toAlgHom q * (algebraMap C E c * q + algebraMap C E d)
        = algebraMap C E a * q + algebraMap C E b := by
    intro lam hlam
    exact clockSemilinearAlgEquiv_generator_mobius (ρ lam) hlam (hconst lam) hy hytop
      (hsemi lam hlam)
  exact commuting_family_scaling_character_of_nonzero
    (fun lam => (ρ lam).toAlgHom) ν₀ hq hν0 hν1 hνm1 hanchor hlin hmob hcomm hmul

end GaloisForLFunctions.HTGeometry
