import GaloisForLFunctions.RHTower.Sieve.PrimeWindow

/-!
# Fibres of the reciprocal map

The reciprocal marker construction sends a prime `p` to the start `⌊X/p⌋` of its cofactor window.
That map is not bounded-to-one: `⌊X/p⌋ = t` says exactly

`X/(t+1) < p ≤ X/t`,

so the fibre over `t` has at most `X/(t(t+1)) + 1` members.  For a start scale `t ≍ A` the fibre
size is therefore `≍ X/A²`, which is what must be charged against a bad-start count when the marker
blocks grow.

The bound is exact arithmetic: no asymptotics, and it holds for every `X` and every `t ≥ 1`.
-/

namespace RHTower.Sieve

open Finset Nat

/-- The reciprocal fibre sits inside the window it defines. -/
theorem reciprocalFibre_subset (X t : ℕ) (ht : 1 ≤ t) :
    {p ∈ Finset.Icc 1 X | X / p = t} ⊆ Finset.Ioc (X / (t + 1)) (X / t) := by
  intro p hp
  obtain ⟨hmem, hdiv⟩ := Finset.mem_filter.1 hp
  obtain ⟨hp1, hpX⟩ := Finset.mem_Icc.1 hmem
  have hppos : 0 < p := hp1
  have hlow : t * p ≤ X := by
    have h := Nat.div_mul_le_self X p
    rw [hdiv] at h
    exact h
  have hhigh : X < (t + 1) * p := by
    have hdm := Nat.div_add_mod X p
    have hmod := Nat.mod_lt X hppos
    rw [hdiv] at hdm
    have hexp : (t + 1) * p = p * t + p := by ring
    omega
  refine Finset.mem_Ioc.2 ⟨?_, ?_⟩
  · rw [Nat.div_lt_iff_lt_mul (by omega)]
    have hexp : p * (t + 1) = (t + 1) * p := by ring
    omega
  · rw [Nat.le_div_iff_mul_le (by omega)]
    have hexp : p * t = t * p := by ring
    omega

/-- **Reciprocal fibre bound.**  The fibre of `p ↦ ⌊X/p⌋` over `t` has at most
`X/(t(t+1)) + 1` members. -/
theorem card_reciprocalFibre_le (X t : ℕ) (ht : 1 ≤ t) :
    ((#{p ∈ Finset.Icc 1 X | X / p = t} : ℕ) : ℝ)
      ≤ (X : ℝ) / ((t : ℝ) * ((t : ℝ) + 1)) + 1 := by
  classical
  have hcard : (#{p ∈ Finset.Icc 1 X | X / p = t}) ≤ X / t - X / (t + 1) := by
    refine le_trans (Finset.card_le_card (reciprocalFibre_subset X t ht)) ?_
    rw [Nat.card_Ioc]
  have htpos : 0 < t := ht
  have ht1pos : 0 < t + 1 := by omega
  have hmono : X / (t + 1) ≤ X / t := Nat.div_le_div_left (by omega) htpos
  have hcast : ((#{p ∈ Finset.Icc 1 X | X / p = t} : ℕ) : ℝ)
      ≤ ((X / t : ℕ) : ℝ) - ((X / (t + 1) : ℕ) : ℝ) := by
    have : ((X / t - X / (t + 1) : ℕ) : ℝ) = ((X / t : ℕ) : ℝ) - ((X / (t + 1) : ℕ) : ℝ) := by
      push_cast [Nat.cast_sub hmono]
      ring
    rw [← this]
    exact_mod_cast hcard
  obtain ⟨hA, -⟩ := cast_div_bounds (d := t) (n := X) htpos
  obtain ⟨-, hB⟩ := cast_div_bounds (d := t + 1) (n := X) ht1pos
  have htR : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hcastt : (((t + 1 : ℕ)) : ℝ) = (t : ℝ) + 1 := by push_cast; ring
  rw [hcastt] at hB
  have hsplit : (X : ℝ) / (t : ℝ) - (X : ℝ) / ((t : ℝ) + 1)
      = (X : ℝ) / ((t : ℝ) * ((t : ℝ) + 1)) := by
    field_simp
    ring
  linarith [hA, hB, hcast, hsplit.le, hsplit.ge]

end RHTower.Sieve
