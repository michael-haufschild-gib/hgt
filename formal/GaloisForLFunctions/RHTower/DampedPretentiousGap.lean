import GaloisForLFunctions.RHTower.MoebiusPretentiousGap

/-!
# The damped Möbius function is unpretentious too

The multiplicative function `m ↦ μ(m)·t^{ω_P(m)}` differs from `μ` only at the designated primes,
where its value is `−t` rather than `−1`.  Its squared pretentious distance to an archimedean
character therefore differs from that of `μ` by at most `∑_{p ∈ P} 1/p`, so the uniform bound
`log log x − 11 log log|τ| − C` survives with that one subtraction.

At the Route E parameters `∑_{p ∈ P} 1/p ≍ (β − γβ)·log log x` with `β − γβ` small, so the damped
distance is still a positive multiple of `log log x`.  This is the input a Halász argument needs for
the damped cofactor, and it holds uniformly in the damping.
-/

namespace RHTower

open Finset

noncomputable section

/-- The positive prime cosine sum of the damped Möbius function. -/
def dampedCosPlusSum (P : Finset ℕ) (t τ x : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE ⌊x⌋₊,
    (1 + (if p ∈ P then t else 1) * Real.cos (τ * Real.log p)) / p

/-- **Damping costs at most the harmonic mass of the designated primes.** -/
theorem dampedCosPlusSum_ge (P : Finset ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (τ x : ℝ) :
    primeCosPlusSum τ x - ∑ p ∈ {p ∈ Nat.primesLE ⌊x⌋₊ | p ∈ P}, (1 : ℝ) / p
      ≤ dampedCosPlusSum P t τ x := by
  classical
  have hdiff : ∀ p ∈ Nat.primesLE ⌊x⌋₊,
      (1 + (if p ∈ P then t else 1) * Real.cos (τ * Real.log p)) / p
          - (1 + Real.cos (τ * Real.log p)) / p
        = if p ∈ P then ((t - 1) * Real.cos (τ * Real.log p)) / p else 0 := by
    intro p _
    by_cases hp : p ∈ P
    · rw [if_pos hp, if_pos hp]
      ring
    · rw [if_neg hp, if_neg hp]
      ring
  have hsum : dampedCosPlusSum P t τ x - primeCosPlusSum τ x
      = ∑ p ∈ {p ∈ Nat.primesLE ⌊x⌋₊ | p ∈ P},
          ((t - 1) * Real.cos (τ * Real.log p)) / p := by
    rw [dampedCosPlusSum, primeCosPlusSum, ← Finset.sum_sub_distrib, Finset.sum_filter]
    exact Finset.sum_congr rfl hdiff
  have hlow : ∀ p ∈ {p ∈ Nat.primesLE ⌊x⌋₊ | p ∈ P},
      -((1 : ℝ) / p) ≤ ((t - 1) * Real.cos (τ * Real.log p)) / p := by
    intro p hp
    have hpp : p ∈ Nat.primesLE ⌊x⌋₊ := (Finset.mem_filter.1 hp).1
    have hprime : p.Prime := Nat.prime_of_mem_primesLE hpp
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
    rw [show -((1 : ℝ) / (p : ℝ)) = (-1 : ℝ) / (p : ℝ) by ring,
      div_le_div_iff_of_pos_right hp0]
    have hcos := Real.neg_one_le_cos (τ * Real.log p)
    have hcos' := Real.cos_le_one (τ * Real.log p)
    nlinarith [hcos, hcos', ht0, ht1]
  have hbound : -∑ p ∈ {p ∈ Nat.primesLE ⌊x⌋₊ | p ∈ P}, (1 : ℝ) / p
      ≤ ∑ p ∈ {p ∈ Nat.primesLE ⌊x⌋₊ | p ∈ P},
          ((t - 1) * Real.cos (τ * Real.log p)) / p := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum hlow
  linarith [hsum.le, hsum.ge, hbound]

/-- **The damped Möbius function is quantitatively unpretentious.** -/
theorem exists_dampedCosPlusSum_ge_logLog :
    ∃ C t₀ : ℝ, 9 ≤ t₀ ∧ ∀ (P : Finset ℕ) (t x τ : ℝ), 0 ≤ t → t ≤ 1 →
      Real.exp 4 ≤ x → t₀ ≤ |τ| →
      Real.log (Real.log x) - 11 * Real.log (Real.log |τ|) - C
          - ∑ p ∈ {p ∈ Nat.primesLE ⌊x⌋₊ | p ∈ P}, (1 : ℝ) / p
        ≤ dampedCosPlusSum P t τ x := by
  obtain ⟨C, t₀, ht₀, hbound⟩ := exists_primeCosPlusSum_ge_logLog
  refine ⟨C, t₀, ht₀, ?_⟩
  intro P t x τ ht0 ht1 hx hτ
  have hplain := hbound x τ hx hτ
  have hdamp := dampedCosPlusSum_ge P ht0 ht1 τ x
  linarith [hplain, hdamp]

end

end RHTower
