import GaloisForLFunctions.HTGeometry.ClockScalingCharacterNonzero

/-!
# Charged phase of the clock-character law (equation (4))

Assembling the abstract charged chain into the card's charged-phase conclusion at the persistent core
`T`.  With `T = C⟨q⟩` a scalar free differential field on a single differential-transcendental
generator `q` (the output of the Ritt–Kolchin differential Lüroth theorem for the nonconstant core),
a persistent constraint `Φ` (a differential automorphism of the core) commuting with the clock
cocharacter that acts on `q` by positive charge `ρ_λ(q) = λ^k q` (`k > 0`) is multiplication by a
single constant:

`Φ(q) = a · q`   (equation (4)).

The hypotheses `HypertranscendentalOver C q` and `differentialAdjoin C {q} = ⊤` encode `T = C⟨q⟩`;
the hypothesis `ρ_λ(q) = λ^k q` is equation (2), the diagonalized `PGL₂`-cocharacter of positive
charge.  Everything else is the abstract charged rigidity proved in `ClockScalingCharacterNonzero`.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

/-- **Charged phase (equation (4)).**  On the nonconstant persistent core `T = C⟨q⟩`, a differential
automorphism `Φ` commuting with a clock cocharacter of positive charge `k` is multiplication by a
single constant on the homogeneous generator: `Φ(q) = a·q`. -/
theorem persistent_clock_charged_forces_multiplicative
    {C T : Type*} [Field C] [IsAlgClosed C] [Field T] [CharZero T]
    [Differential C] [Differential T] [Algebra C T] [DifferentialAlgebra C T]
    (Φ : T ≃ₐ[C] T) (ρ : C → (T →ₐ[C] T)) {q : T} {k : ℕ} (hk : 0 < k)
    (hq : HypertranscendentalOver C q)
    (hqtop : differentialAdjoin C ({q} : Set T) = ⊤)
    (hΦderiv : ∀ w : T, Φ w′ = (Φ w)′)
    (hcharge : ∀ lam : C, lam ≠ 0 → ρ lam q = algebraMap C T (lam ^ k) * q)
    (hmulρ : ∀ lam mu : C, lam ≠ 0 → mu ≠ 0 → ρ (lam * mu) q = ρ lam (ρ mu q))
    (hcomm : ∀ lam : C, lam ≠ 0 → Φ.toAlgHom ((ρ lam) q) = (ρ lam) (Φ.toAlgHom q)) :
    ∃ a : C, Φ q = algebraMap C T a * q := by
  refine charged_clock_polynomial_forces_multiplicative_of_nonzero Φ ρ hq hqtop hΦderiv
    (P := Polynomial.X ^ k) ?_ ?_ hmulρ hcomm
  · rw [Polynomial.natDegree_X_pow]; exact hk
  · intro lam hlam
    rw [hcharge lam hlam, Polynomial.eval_pow, Polynomial.eval_X]

end GaloisForLFunctions.HTGeometry
