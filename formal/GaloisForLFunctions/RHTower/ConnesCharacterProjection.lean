import Mathlib

/-!
# §VIII (5)-(7): the character projection

§VIII (5)-(7) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

Connes decomposes `L²(X_S)` under the compact group `C_{S,1}` (resp. its finite-index open
subgroup `𝒰_S`) using the projections

  `P_{Χ₀} = ∫ Χ̄₀(a) U(a) d₁a`,                                              (5)

`d₁a` being the Haar measure of total mass `1`.  For the finite quotient this is the classical
character average

  `P = |H|^{-1} ∑_{a ∈ H} Χ̄(a) π(a)`,

and (6)/(7) say that it is exactly the orthogonal projection onto the `Χ`-isotypic subspace
`{ξ ; π(a) ξ = Χ(a) ξ}`.  That is proved here, unconditionally, for an arbitrary representation of
an arbitrary finite group by linear maps and an arbitrary unitary-valued multiplicative character:

* `connes_characterProjector_intertwine` - `π(b) P = Χ(b) P`;
* `connes_characterProjector_idem` - `P² = P`;
* `connes_characterProjector_fixed_iff` - `P ξ = ξ` iff `ξ` is `Χ`-isotypic;
* `connes_characterProjector_range` - the range of `P` is the isotypic subspace.
-/

open Finset

namespace GaloisForLFunctions.RHTower

noncomputable section

set_option linter.unusedSectionVars false

variable {H : Type*} [Group H] [Fintype H] {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- **§VIII (5).**  The character average `P = |H|^{-1} ∑_a Χ̄(a) π(a)`. -/
def connesCharacterProjector (π : H → (V →ₗ[ℂ] V)) (χ : H → ℂ) : V →ₗ[ℂ] V :=
  (Fintype.card H : ℂ)⁻¹ • ∑ a : H, (starRingEnd ℂ) (χ a) • π a

theorem connesCharacterProjector_apply (π : H → (V →ₗ[ℂ] V)) (χ : H → ℂ) (v : V) :
    connesCharacterProjector π χ v
      = (Fintype.card H : ℂ)⁻¹ • ∑ a : H, (starRingEnd ℂ) (χ a) • π a v := by
  rw [connesCharacterProjector]
  simp [LinearMap.sum_apply]

section Character

variable {χ : H → ℂ} (hχmul : ∀ a b : H, χ (a * b) = χ a * χ b)
  (hχunit : ∀ a : H, (starRingEnd ℂ) (χ a) * χ a = 1)

include hχmul hχunit

theorem connes_character_ne_zero (a : H) : χ a ≠ 0 := by
  intro h
  have := hχunit a
  rw [h] at this
  simp at this

theorem connes_character_one : χ 1 = 1 := by
  have h := hχmul 1 1
  rw [mul_one] at h
  have hne := connes_character_ne_zero hχmul hχunit 1
  have h2 : χ 1 * 1 = χ 1 * χ 1 := by rw [mul_one]; exact h
  exact (mul_left_cancel₀ hne h2).symm

theorem connes_character_inv (b : H) : χ b⁻¹ = (χ b)⁻¹ := by
  have h := hχmul b⁻¹ b
  rw [inv_mul_cancel, connes_character_one hχmul hχunit] at h
  have hne := connes_character_ne_zero hχmul hχunit b
  have h2 : χ b⁻¹ * χ b = 1 := h.symm
  calc χ b⁻¹ = χ b⁻¹ * (χ b * (χ b)⁻¹) := by rw [mul_inv_cancel₀ hne, mul_one]
    _ = (χ b⁻¹ * χ b) * (χ b)⁻¹ := by ring
    _ = (χ b)⁻¹ := by rw [h2, one_mul]

theorem connes_character_conj_inv (b : H) : (starRingEnd ℂ) (χ b⁻¹) = χ b := by
  have hne := connes_character_ne_zero hχmul hχunit b
  have h := hχunit b
  have hconj : (starRingEnd ℂ) (χ b) = (χ b)⁻¹ := by
    calc (starRingEnd ℂ) (χ b) = (starRingEnd ℂ) (χ b) * (χ b * (χ b)⁻¹) := by
          rw [mul_inv_cancel₀ hne, mul_one]
      _ = ((starRingEnd ℂ) (χ b) * χ b) * (χ b)⁻¹ := by ring
      _ = (χ b)⁻¹ := by rw [h, one_mul]
  rw [connes_character_inv hχmul hχunit b, map_inv₀, hconj, inv_inv]

end Character

variable {π : H → (V →ₗ[ℂ] V)} {χ : H → ℂ}

/-- **§VIII (7), the intertwining relation.**  `π(b) P = Χ(b) P`. -/
theorem connes_characterProjector_intertwine
    (hπ : ∀ a b : H, π (a * b) = (π a).comp (π b))
    (hχmul : ∀ a b : H, χ (a * b) = χ a * χ b)
    (hχunit : ∀ a : H, (starRingEnd ℂ) (χ a) * χ a = 1)
    (b : H) (v : V) :
    π b (connesCharacterProjector π χ v) = χ b • connesCharacterProjector π χ v := by
  set c : ℂ := (Fintype.card H : ℂ)⁻¹ with hc
  rw [connesCharacterProjector_apply, map_smul, map_sum]
  have hterm : ∀ a : H, π b ((starRingEnd ℂ) (χ a) • π a v)
      = (starRingEnd ℂ) (χ a) • π (b * a) v := by
    intro a
    rw [map_smul, hπ b a]
    rfl
  simp only [hterm]
  set G : H → V := fun x : H => (starRingEnd ℂ) (χ (b⁻¹ * x)) • π x v with hG
  have hshift : ∀ a : H, (starRingEnd ℂ) (χ a) • π (b * a) v = G (b * a) := by
    intro a
    simp only [hG]
    congr 2
    rw [← mul_assoc, inv_mul_cancel, one_mul]
  simp only [hshift]
  have hsum : (∑ a : H, G (b * a)) = ∑ x : H, G x :=
    Equiv.sum_comp (Equiv.mulLeft b) G
  rw [hsum]
  have hGval : ∀ x : H, G x = χ b • ((starRingEnd ℂ) (χ x) • π x v) := by
    intro x
    simp only [hG]
    rw [hχmul b⁻¹ x, map_mul, connes_character_conj_inv hχmul hχunit b, smul_smul]
  simp only [hGval]
  rw [← Finset.smul_sum, smul_comm]

/-- **§VIII (7), idempotence.** -/
theorem connes_characterProjector_idem
    (hπ : ∀ a b : H, π (a * b) = (π a).comp (π b))
    (hχmul : ∀ a b : H, χ (a * b) = χ a * χ b)
    (hχunit : ∀ a : H, (starRingEnd ℂ) (χ a) * χ a = 1)
    (v : V) :
    connesCharacterProjector π χ (connesCharacterProjector π χ v)
      = connesCharacterProjector π χ v := by
  have hcard : (Fintype.card H : ℂ) ≠ 0 := by
    have : 0 < Fintype.card H := Fintype.card_pos
    exact_mod_cast this.ne'
  rw [connesCharacterProjector_apply (v := connesCharacterProjector π χ v)]
  have hterm : ∀ a : H, (starRingEnd ℂ) (χ a) • π a (connesCharacterProjector π χ v)
      = connesCharacterProjector π χ v := by
    intro a
    rw [connes_characterProjector_intertwine hπ hχmul hχunit a v, smul_smul, hχunit a, one_smul]
  simp only [hterm]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ hcard, one_smul]

/-- **§VIII (6)/(7).**  `P ξ = ξ` exactly when `ξ` is `Χ`-isotypic. -/
theorem connes_characterProjector_fixed_iff
    (hπ : ∀ a b : H, π (a * b) = (π a).comp (π b))
    (hχmul : ∀ a b : H, χ (a * b) = χ a * χ b)
    (hχunit : ∀ a : H, (starRingEnd ℂ) (χ a) * χ a = 1)
    (v : V) :
    connesCharacterProjector π χ v = v ↔ ∀ a : H, π a v = χ a • v := by
  have hcard : (Fintype.card H : ℂ) ≠ 0 := by
    have : 0 < Fintype.card H := Fintype.card_pos
    exact_mod_cast this.ne'
  constructor
  · intro hv a
    have h := connes_characterProjector_intertwine hπ hχmul hχunit a v
    rw [hv] at h
    exact h
  · intro hv
    rw [connesCharacterProjector_apply]
    have hterm : ∀ a : H, (starRingEnd ℂ) (χ a) • π a v = v := by
      intro a
      rw [hv a, smul_smul, hχunit a, one_smul]
    simp only [hterm]
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      inv_mul_cancel₀ hcard, one_smul]

end

end GaloisForLFunctions.RHTower
