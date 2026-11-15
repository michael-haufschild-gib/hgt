import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.FrobeniusTracePolynomials
import Mathlib.Tactic.Linarith

/-!
# Rigidity of the Kummer residue progression

For `c≥2` and `R≥3`, the residues of `τ(1+cj)` modulo `cR+1`
cannot all lie in `[0,R+1]` through `j=⌊R/2⌋+1`, with
`1≤τ≤R+1`, unless `τ=R`. Positive steps overshoot the interval;
negative steps reach zero too soon. The only possible overlap of the
two step sizes is excluded by the first residue.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

private theorem residue_rigidity (c R τ : ℕ) (hc : 2 ≤ c) (hR : 3 ≤ R)
    (hτ0 : 1 ≤ τ) (hτ1 : τ ≤ R + 1)
    (hb : ∀ j ≤ R / 2 + 1, τ * (1 + c * j) % (c * R + 1) ≤ R + 1) : τ = R := by
  let A := c * R + 1
  let ℓ := R / 2 + 1
  let Δ := c * τ
  let b := fun j : ℕ => τ * (1 + c * j) % A
  have hprodR : 2 * R ≤ c * R := Nat.mul_le_mul_right R hc
  have hprodC : 2 * c ≤ c * R := by
    simpa only [Nat.mul_comm c 2] using Nat.mul_le_mul_left c (show 2 ≤ R by omega)
  have hA : R + 1 < A := by dsimp only [A]; omega
  have hτA : τ < A := lt_of_le_of_lt hτ1 hA
  have hb0 : b 0 = τ := by
    simp only [b, Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.mod_eq_of_lt hτA]
  have hbone := hb 1 (by omega)
  change τ * (1 + c * 1) % A ≤ R + 1 at hbone
  have hτ : τ ≤ R := by
    by_contra hn
    have he : τ = R + 1 := by omega
    have hsmall : R + c < A := by
      dsimp only [A]
      nlinarith only [hprodR, hprodC]
    have hex : (R + 1) * (1 + c * 1) = A + (R + c) := by dsimp only [A]; ring
    rw [he, hex] at hbone
    change (A + (R + c)) % A ≤ R + 1 at hbone
    simp only [Nat.add_mod, Nat.mod_self, Nat.zero_add,
      Nat.mod_eq_of_lt hsmall] at hbone
    omega
  have hΔA : Δ < A := by
    have h := Nat.mul_le_mul_left c hτ
    dsimp only [Δ, A]
    omega
  have hgrowth : R < c * ℓ := by
    have hdiv := Nat.mod_add_div R 2
    have hmod := Nat.mod_lt R (by omega : 0 < 2)
    have h := Nat.mul_le_mul_right ℓ hc
    dsimp only [ℓ] at h ⊢
    nlinarith only [hdiv, hmod, h]
  have hstep (j : ℕ) : b (j + 1) = (b j + Δ) % A := by
    have he : τ * (1 + c * (j + 1)) = τ * (1 + c * j) + Δ := by
      dsimp only [Δ]
      ring
    simp only [b, he, Nat.add_mod, Nat.mod_mod]
  have hoverlap : ¬(Δ ≤ R + 1 ∧ A - Δ ≤ R + 1) := by
    rintro ⟨hlo, hhi⟩
    have hsum : A ≤ 2 * (R + 1) := by omega
    have hc2 : c = 2 := by
      dsimp only [A] at hsum
      by_contra hne
      have hc3 : 3 ≤ c := by omega
      have hp := Nat.mul_le_mul_right R hc3
      omega
    have hbound : R ≤ 2 * τ ∧ 2 * τ ≤ R + 1 := by
      dsimp only [A, Δ] at hlo hhi
      rw [hc2] at hlo hhi
      omega
    have hsmall : 3 * τ < A := by
      dsimp only [A]
      rw [hc2]
      nlinarith only [hbound.2, hR]
    have hlarge : R + 1 < 3 * τ := by nlinarith only [hbound.1, hR]
    rw [hc2, show τ * (1 + 2 * 1) = 3 * τ by ring,
      Nat.mod_eq_of_lt hsmall] at hbone
    omega
  by_cases hpos : Δ ≤ R + 1
  · have hneg : R + 1 < A - Δ := by omega
    have hlift : ∀ j ≤ ℓ, b j = τ + j * Δ := by
      intro j hj
      induction j with
      | zero => simpa only [Nat.zero_mul, Nat.add_zero] using hb0
      | succ j ih =>
        have hj' : j ≤ ℓ := by omega
        have hbj := hb j hj'
        change b j ≤ R + 1 at hbj
        have hsum : b j + Δ < A := by omega
        rw [hstep, Nat.mod_eq_of_lt hsum, ih hj']
        ring
    have he := hb ℓ le_rfl
    change b ℓ ≤ R + 1 at he
    rw [hlift ℓ le_rfl] at he
    have hΔ : c ≤ Δ := by
      simpa only [Nat.mul_one, Δ] using Nat.mul_le_mul_left c hτ0
    have hm := Nat.mul_le_mul_left ℓ hΔ
    nlinarith only [he, hgrowth, hm, hτ0]
  · have hnegative (j : ℕ) (hj : j < ℓ) : b (j + 1) + (A - Δ) = b j := by
      have hbj : b j < A := Nat.mod_lt _ (by dsimp only [A]; omega)
      have hnext := hb (j + 1) (by omega)
      change b (j + 1) ≤ R + 1 at hnext
      have hsum : A ≤ b j + Δ := by
        by_contra hn
        have he := hstep j
        rw [Nat.mod_eq_of_lt (by omega : b j + Δ < A)] at he
        omega
      have hsmall : b j + Δ - A < A := by omega
      have heq : b j + Δ = A + (b j + Δ - A) := by omega
      have he := hstep j
      rw [heq] at he
      simp only [Nat.add_mod, Nat.mod_self, Nat.zero_add,
        Nat.mod_eq_of_lt hsmall] at he
      omega
    have hlift : ∀ j ≤ ℓ, b j + j * (A - Δ) = τ := by
      intro j hj
      induction j with
      | zero => simpa only [Nat.zero_mul, Nat.add_zero] using hb0
      | succ j ih =>
        have h1 := hnegative j (by omega)
        have h2 := ih (by omega)
        nlinarith only [h1, h2]
    have hlast := hlift ℓ le_rfl
    by_contra hne
    have hstrict : τ < R := by omega
    have hbig : c ≤ A - Δ := by
      dsimp only [A, Δ]
      have hm := Nat.mul_le_mul_left c (show τ + 1 ≤ R by omega)
      have hm' : c * τ + c ≤ c * R := by nlinarith only [hm]
      omega
    have hm := Nat.mul_le_mul_left ℓ hbig
    nlinarith only [hlast, hm, hgrowth, hτ]

/-- The short Kummer residue condition classifies its initial multiplier exactly. -/
theorem kummer_residue_progression_iff (c R τ : ℕ) (hc : 2 ≤ c) (hR : 3 ≤ R) :
    (1 ≤ τ ∧ τ ≤ R + 1 ∧
      ∀ j ≤ R / 2 + 1, τ * (1 + c * j) % (c * R + 1) ≤ R + 1) ↔ τ = R := by
  constructor
  · rintro ⟨h0, h1, hb⟩
    exact residue_rigidity c R τ hc hR h0 h1 hb
  · intro heq
    subst τ
    refine ⟨by omega, by omega, ?_⟩
    intro j hj
    have hjR : j ≤ R := by omega
    have he : R * (1 + c * j) = (c * R + 1) * j + (R - j) := by
      have hsub := Nat.sub_add_cancel hjR
      nlinarith only [hsub]
    have hprod := Nat.mul_le_mul_right R hc
    have hsmall : R - j < c * R + 1 := by omega
    rw [he]
    simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod,
      Nat.zero_add, Nat.mod_eq_of_lt hsmall]
    omega

/-- For every geometric exponent with `q≥3` and exponent length at least two,
the prescribed bounded residue progression singles out that exponent. -/
theorem geometricExponent_residue_progression_iff (b r τ : ℕ) :
    let R := kummerExponent (b + 3) (r + 2)
    (1 ≤ τ ∧ τ ≤ R + 1 ∧
      ∀ j ≤ R / 2 + 1, τ * (1 + (b + 2) * j) % ((b + 2) * R + 1) ≤ R + 1) ↔ τ = R := by
  dsimp only
  apply kummer_residue_progression_iff _ _ _ (by omega)
  have hsum : kummerExponent (b + 3) 2 ≤ kummerExponent (b + 3) (r + 2) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
    intro i _ _
    exact Nat.zero_le _
  have htwo : kummerExponent (b + 3) 2 = b + 4 := by
    simp only [kummerExponent, Finset.sum_range_succ, Finset.sum_range_zero,
      Nat.pow_zero, Nat.pow_one]
    omega
  rw [htwo] at hsum
  omega

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
