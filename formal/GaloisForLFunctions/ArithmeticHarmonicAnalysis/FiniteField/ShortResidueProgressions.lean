import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Short residue progressions

Congruent increments of a sequence in `[0,D]` are equal when the modulus
exceeds `2D`. Thus a modular progression in such an interval has a unique
integer lift, and a closed progression is constant.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

/-- Two congruent differences in `[-D,D]` agree below the half-modulus threshold. -/
theorem short_congruent_differences {D k u v : ℤ}
    (hk : 2 * D < k) (hu : -D ≤ u ∧ u ≤ D) (hv : -D ≤ v ∧ v ≤ D)
    (h : u ≡ v [ZMOD k]) : u = v := by
  have he := (h.add_right D).eq
  rw [Int.emod_eq_of_lt (by omega) (by omega),
    Int.emod_eq_of_lt (by omega) (by omega)] at he
  omega

/-- Equal modular increments in a short interval lift to an integer arithmetic progression. -/
theorem short_modular_progression {D k : ℤ} {h : ℕ} (b : ℕ → ℤ)
    (hk : 2 * D < k) (hb : ∀ j ≤ h, 0 ≤ b j ∧ b j ≤ D)
    (hd : ∀ j < h, b (j + 1) - b j ≡ b 1 - b 0 [ZMOD k]) :
    ∀ j ≤ h, b j = b 0 + (j : ℤ) * (b 1 - b 0) := by
  intro j hj
  induction j with
  | zero => simp
  | succ j ih =>
    have hstep := short_congruent_differences hk
      (show -D ≤ b (j + 1) - b j ∧ b (j + 1) - b j ≤ D by
        have := hb (j + 1) hj
        have := hb j (by omega)
        omega)
      (show -D ≤ b 1 - b 0 ∧ b 1 - b 0 ≤ D by
        have := hb 1 (by omega)
        have := hb 0 (by omega)
        omega) (hd j (by omega))
    rw [Nat.cast_add, Nat.cast_one]
    have hi := ih (by omega)
    linear_combination hi + hstep

/-- A closed short modular progression is constant; this removes possible
wrapping in periodic residue and ramification constraints. -/
theorem short_modular_progression_closed {D k : ℤ} {h : ℕ} (b : ℕ → ℤ)
    (hk : 2 * D < k) (hb : ∀ j ≤ h, 0 ≤ b j ∧ b j ≤ D)
    (hd : ∀ j < h, b (j + 1) - b j ≡ b 1 - b 0 [ZMOD k])
    (hc : b h = b 0) : ∀ j ≤ h, b j = b 0 := by
  have hp := short_modular_progression b hk hb hd
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · intro j hj
    have : j = 0 := by omega
    simp [this]
  · have he := hp h le_rfl
    rw [hc] at he
    have hm : (h : ℤ) * (b 1 - b 0) = 0 := by omega
    have hs : b 1 - b 0 = 0 :=
      (mul_eq_zero.mp hm).resolve_left (by exact_mod_cast Nat.ne_of_gt hh)
    intro j hj
    simpa only [hs, mul_zero, add_zero] using hp j hj

/-- Actual affine residues satisfy the modular increment condition. -/
theorem affine_residue_increment (a s k : ℤ) (j : ℕ) :
    ((a + (j + 1 : ℕ) * s) % k - (a + (j : ℤ) * s) % k) ≡ s [ZMOD k] := by
  have he := (Int.mod_modEq (a + (j + 1 : ℕ) * s) k).sub
    (Int.mod_modEq (a + (j : ℤ) * s) k)
  convert he using 1
  push_cast
  ring

/-- A closed affine residue orbit confined below half its modulus is constant. -/
theorem affine_residue_closed {D k : ℤ} {h : ℕ} (a s : ℤ)
    (hk : 0 < k) (hD : 2 * D < k)
    (hb : ∀ j ≤ h, (a + (j : ℤ) * s) % k ≤ D)
    (hc : (a + (h : ℤ) * s) % k = a % k) :
    ∀ j ≤ h, (a + (j : ℤ) * s) % k = a % k := by
  suffices hs : ∀ j ≤ h, (a + (j : ℤ) * s) % k = (a + (0 : ℤ) * s) % k by
    simpa only [zero_mul, add_zero] using hs
  apply short_modular_progression_closed (fun j => (a + (j : ℤ) * s) % k) hD
  · intro j hj
    exact ⟨Int.emod_nonneg _ (ne_of_gt hk), hb j hj⟩
  · intro j _
    exact (affine_residue_increment a s k j).trans (affine_residue_increment a s k 0).symm
  · simpa only [Nat.cast_zero, zero_mul, add_zero] using hc

/-- At twice the interval width, opposite endpoint differences are congruent
and distinct. Hence the strict half-modulus threshold cannot be weakened. -/
theorem short_difference_threshold_sharp (D : ℕ) :
    ((D + 1 : ℕ) : ℤ) ≡ -((D + 1 : ℕ) : ℤ) [ZMOD 2 * ((D + 1 : ℕ) : ℤ)] ∧
      ((D + 1 : ℕ) : ℤ) ≠ -((D + 1 : ℕ) : ℤ) := by
  constructor
  · apply Int.modEq_iff_dvd.mpr
    exact ⟨-1, by ring⟩
  · omega

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
