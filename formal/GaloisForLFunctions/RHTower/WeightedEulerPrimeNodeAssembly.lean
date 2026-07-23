import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Prime.Basic

/-!
# Assembly of separated prime-log node families from short windows

Combinatorial half of the prime-log node supply: if every window
`[y, y + η]` at the `4η`-spaced targets `y_i = R + 4η·i` contains a prime
logarithm, then the unit interval `[R, R+1]` carries `N + 1` prime
logarithms with pairwise separation `≥ η`, where `η = 1/(4(N+1))`.

The windows are disjoint with `3η` clearance, so one prime log per window is
automatically separated and stays inside the unit interval.  The arithmetic
content — a prime in every short window — is the sole remaining input,
supplied by a prime number theorem with power-log error.
-/

noncomputable section

namespace RHTower

open Finset

/-- **Node assembly from short prime windows**: one prime log per `η`-window
at `4η`-spaced targets yields `N + 1` pairwise `η`-separated prime logs in
the unit interval. -/
theorem exists_separated_primeLog_nodes
    {R : ℝ} {N : ℕ}
    (hwin : ∀ i : Fin (N + 1), ∃ p : ℕ, p.Prime ∧
      R + 4 * (1 / (4 * ((N : ℝ) + 1))) * (i : ℕ) ≤ Real.log p ∧
      Real.log p ≤ R + 4 * (1 / (4 * ((N : ℝ) + 1))) * (i : ℕ)
        + 1 / (4 * ((N : ℝ) + 1))) :
    ∃ s : Finset ℝ, s.card = N + 1 ∧ ↑s ⊆ Set.Icc R (R + 1) ∧
      (∀ t ∈ s, ∀ u ∈ s, t ≠ u → 1 / (4 * ((N : ℝ) + 1)) ≤ |t - u|) ∧
      (∀ t ∈ s, ∃ p : ℕ, p.Prime ∧ t = Real.log p) := by
  set η : ℝ := 1 / (4 * ((N : ℝ) + 1)) with hη
  have hη0 : 0 < η := by positivity
  have hηN : 4 * η * ((N : ℝ) + 1) = 1 := by
    rw [hη]
    field_simp
  choose P hP hlo hhi using hwin
  set ℓ : Fin (N + 1) → ℝ := fun i => Real.log (P i) with hℓ
  -- pairwise separation of the chosen logs
  have hsep : ∀ i j : Fin (N + 1), (i : ℕ) < (j : ℕ) →
      3 * η ≤ ℓ j - ℓ i := by
    intro i j hij
    have hcast : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by
      exact_mod_cast hij
    have h1 := hhi i
    have h2 := hlo j
    have h3 : R + 4 * η * (i : ℕ) + η + 3 * η
        ≤ R + 4 * η * (j : ℕ) := by
      have : 4 * η * (((i : ℕ) : ℝ) + 1) ≤ 4 * η * ((j : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hcast (by positivity)
      nlinarith
    simp only [hℓ]
    linarith
  have hinj : Function.Injective ℓ := by
    intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_iff.2 hne) with h | h
    · have := hsep i j h
      rw [hij] at this
      nlinarith
    · have := hsep j i h
      rw [hij] at this
      nlinarith
  refine ⟨Finset.image ℓ Finset.univ, ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ,
      Fintype.card_fin]
  · intro t ht
    rw [Finset.coe_image] at ht
    obtain ⟨i, _, rfl⟩ := ht
    constructor
    · have := hlo i
      have hpos : (0:ℝ) ≤ 4 * η * (i : ℕ) := by positivity
      simp only [hℓ]
      linarith
    · have := hhi i
      have hiN : ((i : ℕ) : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast Fin.is_le i
      have hbound : 4 * η * ((i : ℕ) : ℝ) + η ≤ 1 := by
        have h1 : 4 * η * ((i : ℕ) : ℝ) ≤ 4 * η * (N : ℝ) :=
          mul_le_mul_of_nonneg_left hiN (by positivity)
        nlinarith
      simp only [hℓ]
      linarith
  · intro t ht u hu htu
    rw [Finset.mem_image] at ht hu
    obtain ⟨i, _, rfl⟩ := ht
    obtain ⟨j, _, rfl⟩ := hu
    have hij : i ≠ j := fun h => htu (by rw [h])
    rcases lt_or_gt_of_ne (Fin.val_ne_iff.2 hij) with h | h
    · have := hsep i j h
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      linarith
    · have := hsep j i h
      rw [abs_of_nonneg (by linarith)]
      linarith
  · intro t ht
    rw [Finset.mem_image] at ht
    obtain ⟨i, _, rfl⟩ := ht
    exact ⟨P i, hP i, rfl⟩

end RHTower
