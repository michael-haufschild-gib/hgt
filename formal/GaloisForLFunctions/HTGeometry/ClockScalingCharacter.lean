import GaloisForLFunctions.HTGeometry.ClockChargeProjectiveLinearization

/-!
# The commuting clock family is a multiplicative scaling character

Once a single element of the clock cocharacter is diagonalized to a nontrivial scaling
`ρ_{ν₀} q = ν · q` (`ν ≠ 0, 1, -1`, produced by the fixed-point diagonalization
`mobius_two_fixed_points_scaling`), the projective-drift no-go
(`charged_clock_forces_multiplicative`) forces *every* commuting member `ρ_λ`, which a priori acts by
a Möbius transform on the generator, to be a pure scaling in the *same* coordinate:
`ρ_λ q = e(λ) · q`.  This is the common-fixed-point / shared-coordinate step of §3: the whole family
diagonalizes simultaneously.

The resulting scaling map `χ = e : C → C` is multiplicative, `e(λμ) = e(λ) e(μ)`, because the family
is a homomorphism `ρ_{λμ} = ρ_λ ∘ ρ_μ`.  Multiplicativity is exactly the hypothesis of
`multiplicative_polynomial_eq_X_pow`, which identifies the character with `λ ↦ λ^k`, completing the
`PGL₂`-cocharacter classification and delivering equation (2) of the clock-character law.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {C E : Type*} [Field C] [Field E] [Algebra C E]

/-- **Shared-coordinate scaling.**  A `C`-algebra endomorphism `Ψ` (another clock member) that acts
by a Möbius transform on `q` and commutes with an anchor scaling `ρ₀ q = ν q` (`ν ≠ 0, 1, -1`) is
itself a pure scaling on `q`: `∃ e, Ψ q = e · q`.  The common-fixed-point step packaged from the
projective-drift no-go. -/
theorem commuting_with_scaling_is_scaling
    (Ψ ρ₀ : E →ₐ[C] E) {a b c d ν : C} (q : E)
    (hν0 : ν ≠ 0) (hν1 : ν ≠ 1) (hνm1 : ν ≠ -1)
    (hinv : a * d - b * c ≠ 0)
    (hlin : ∀ x y z : C, algebraMap C E x + algebraMap C E y * q
        + algebraMap C E z * q ^ (2 : ℕ) = 0 → x = 0 ∧ y = 0 ∧ z = 0)
    (hρ0q : ρ₀ q = algebraMap C E ν * q)
    (hΨq : Ψ q * (algebraMap C E c * q + algebraMap C E d)
        = algebraMap C E a * q + algebraMap C E b)
    (hcomm : Ψ (ρ₀ q) = ρ₀ (Ψ q)) :
    ∃ e : C, Ψ q = algebraMap C E e * q :=
  ⟨a / d, charged_clock_forces_multiplicative Ψ ρ₀ q hν0 hν1 hνm1 hinv hlin hρ0q hΨq hcomm⟩

/-- **The scaling character is multiplicative.**  If a family `ρ : C → End` acts on `q` by scalings
`ρ_λ q = e(λ) q` and is a homomorphism at `q` (`ρ_{λμ} q = ρ_λ (ρ_μ q)`), then the scaling factors
form a multiplicative character: `e(λμ) = e(λ) e(μ)`. -/
theorem scaling_character_multiplicative
    (ρ : C → (E →ₐ[C] E)) {q : E} (hq : q ≠ 0) (e : C → C)
    (hscale : ∀ lam, ρ lam q = algebraMap C E (e lam) * q)
    (hmul : ∀ lam mu, ρ (lam * mu) q = ρ lam (ρ mu q)) :
    ∀ lam mu, e (lam * mu) = e lam * e mu := by
  intro lam mu
  have h := hmul lam mu
  rw [hscale (lam * mu), hscale mu] at h
  rw [map_mul, AlgHom.commutes, hscale lam, ← mul_assoc, ← map_mul] at h
  have h2 : algebraMap C E (e (lam * mu)) = algebraMap C E (e mu * e lam) :=
    mul_right_cancel₀ hq h
  have h4 : e (lam * mu) - e mu * e lam = 0 := by
    rw [← map_eq_zero (f := algebraMap C E), map_sub, h2, sub_self]
  exact (sub_eq_zero.mp h4).trans (mul_comm _ _)

/-- **§3(b): the commuting clock family is a multiplicative scaling character.**  Given a clock
family `ρ` that is a homomorphism at `q`, whose members each act on the generator by a Möbius
transform and commute with an anchor scaling `ρ_{ν₀} q = ν q` (`ν ≠ 0, 1, -1`), and with `1, q, q²`
linearly independent over `C`, there is a multiplicative character `e : C → C` with
`ρ_λ q = e(λ) · q` for every `λ`.

This is the simultaneous diagonalization of the whole cocharacter: the shared fixed-point coordinate
turns the family into a single character, the input to the monomial classification `e(λ) = λ^k`. -/
theorem commuting_family_scaling_character
    (ρ : C → (E →ₐ[C] E)) (ν₀ : C) {q : E} (hq : q ≠ 0) {ν : C}
    (hν0 : ν ≠ 0) (hν1 : ν ≠ 1) (hνm1 : ν ≠ -1)
    (hanchor : ρ ν₀ q = algebraMap C E ν * q)
    (hlin : ∀ x y z : C, algebraMap C E x + algebraMap C E y * q
        + algebraMap C E z * q ^ (2 : ℕ) = 0 → x = 0 ∧ y = 0 ∧ z = 0)
    (hmob : ∀ lam, ∃ a b c d : C, a * d - b * c ≠ 0 ∧
      ρ lam q * (algebraMap C E c * q + algebraMap C E d)
        = algebraMap C E a * q + algebraMap C E b)
    (hcomm : ∀ lam, ρ lam (ρ ν₀ q) = ρ ν₀ (ρ lam q))
    (hmul : ∀ lam mu, ρ (lam * mu) q = ρ lam (ρ mu q)) :
    ∃ e : C → C, (∀ lam, ρ lam q = algebraMap C E (e lam) * q)
      ∧ (∀ lam mu, e (lam * mu) = e lam * e mu) := by
  have hscale : ∀ lam, ∃ elam : C, ρ lam q = algebraMap C E elam * q := by
    intro lam
    obtain ⟨a, b, c, d, hinv, hΨq⟩ := hmob lam
    exact commuting_with_scaling_is_scaling (ρ lam) (ρ ν₀) q hν0 hν1 hνm1 hinv hlin
      hanchor hΨq (hcomm lam)
  choose e he using hscale
  exact ⟨e, he, scaling_character_multiplicative ρ hq e he hmul⟩

end GaloisForLFunctions.HTGeometry
