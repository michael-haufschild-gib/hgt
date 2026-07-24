import GaloisForLFunctions.HTGeometry.StableCoreClockCharacter

/-!
# Equation (2) at the persistent core from an algebraic clock character

If the restricted clock family acts on a core generator `q` by a *polynomial* scaling character
`ρ_λ(q) = P(λ)·q` (the algebraicity of the cocharacter), then it acts by `ρ_λ(q) = λ^k·q`
(equation (2)).  This is the monomial classification of algebraic `G_m`-characters
(`charged_clock_family_pow_of_nonzero`) transported to the core; it discharges the equation-(2)
hypothesis of the core dichotomy from the algebraicity input alone.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **Equation (2) at the core.**  A restricted clock family whose scaling character at a core
generator `q` is a nonzero polynomial acts by `ρ_λ(q) = λ^k·q`. -/
theorem stableRangeCoreSymmetry_family_pow
    {C F : Type*} [Field C] [IsAlgClosed C] [Field F] [Algebra C F]
    (φ : F →ₐ[C] F) (ρ : C → (F ≃ₐ[C] F)) (hcommφ : ∀ lam : C, ∀ x, φ (ρ lam x) = ρ lam (φ x))
    {q : stableRangeCore φ} (hq : q ≠ 0) {P : Polynomial C} (hP : P ≠ 0)
    (hpoly : ∀ lam : C, lam ≠ 0 →
      (stableRangeCoreClockFamily φ ρ hcommφ lam).toAlgHom q
        = algebraMap C (stableRangeCore φ) (P.eval lam) * q)
    (hmul : ∀ lam mu : C, lam ≠ 0 → mu ≠ 0 →
      (stableRangeCoreClockFamily φ ρ hcommφ (lam * mu)).toAlgHom q
        = (stableRangeCoreClockFamily φ ρ hcommφ lam).toAlgHom
          ((stableRangeCoreClockFamily φ ρ hcommφ mu).toAlgHom q)) :
    ∃ k : ℕ, ∀ lam : C, lam ≠ 0 →
      (stableRangeCoreClockFamily φ ρ hcommφ lam).toAlgHom q
        = algebraMap C (stableRangeCore φ) (lam ^ k) * q :=
  charged_clock_family_pow_of_nonzero
    (fun lam => (stableRangeCoreClockFamily φ ρ hcommφ lam).toAlgHom) hq hP hpoly hmul

end GaloisForLFunctions.HTGeometry
