import GaloisForLFunctions.HTGeometry.ScalarClockCharacterCharged
import GaloisForLFunctions.HTGeometry.ClockCharacterSigmaMobius

/-!
# The two clock phases (equations (3) and (4))

The clock-character law splits the persistent constraint on a nonconstant core `T = C⟨q⟩` into two
phases according to the projective charge `k`:

* **Neutral / general** (`k = 0` allowed): `Φ` acts on the generator by an arbitrary `PGL₂(C)`
  element — a Möbius transform (equation (3)).  This holds unconditionally for every differential
  automorphism.
* **Charged** (`k > 0`): the Möbius action collapses to multiplication by a single constant,
  `Φ(q) = a·q` (equation (4)).

This file states the full dichotomy, assembling §1 (`differentialAlgEquiv_generator_mobius`) with the
charged rigidity (`persistent_clock_charged_forces_multiplicative`).
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

/-- **The clock-character dichotomy (equations (3) and (4)).**  On the nonconstant core `T = C⟨q⟩`,
a differential automorphism `Φ` commuting with a clock cocharacter that acts on `q` by charge `k`:
always acts by a Möbius transform (eq. 3), and when the charge is positive it is multiplication by a
single constant (eq. 4). -/
theorem persistent_clock_character_dichotomy
    {C T : Type*} [Field C] [IsAlgClosed C] [Field T] [CharZero T]
    [Differential C] [Differential T] [Algebra C T] [DifferentialAlgebra C T]
    (Φ : T ≃ₐ[C] T) (ρ : C → (T →ₐ[C] T)) {q : T} {k : ℕ}
    (hq : HypertranscendentalOver C q)
    (hqtop : differentialAdjoin C ({q} : Set T) = ⊤)
    (hΦderiv : ∀ w : T, Φ w′ = (Φ w)′)
    (hcharge : ∀ lam : C, lam ≠ 0 → ρ lam q = algebraMap C T (lam ^ k) * q)
    (hmulρ : ∀ lam mu : C, lam ≠ 0 → mu ≠ 0 → ρ (lam * mu) q = ρ lam (ρ mu q))
    (hcomm : ∀ lam : C, lam ≠ 0 → Φ.toAlgHom ((ρ lam) q) = (ρ lam) (Φ.toAlgHom q)) :
    (∃ a b c d : C, a * d - b * c ≠ 0 ∧
        Φ q * (algebraMap C T c * q + algebraMap C T d) = algebraMap C T a * q + algebraMap C T b)
      ∧ (0 < k → ∃ a : C, Φ q = algebraMap C T a * q) := by
  refine ⟨differentialAlgEquiv_generator_mobius Φ hq hqtop hΦderiv, fun hk => ?_⟩
  exact persistent_clock_charged_forces_multiplicative Φ ρ hk hq hqtop hΦderiv hcharge hmulρ hcomm

end GaloisForLFunctions.HTGeometry
