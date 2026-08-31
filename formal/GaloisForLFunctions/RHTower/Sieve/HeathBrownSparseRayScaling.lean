import GaloisForLFunctions.RHTower.Sieve.AlmostPrimeGlobalCount
import Mathlib.Data.PNat.Prime

/-!
# Scale transport on a primitive positive ray

This is the exact one-dimensional rescaling step in the bad-lattice branch of Heath--Brown's
sparse collision lemma.  A positive direction `(u₁,u₂)` contributes the positive integer scales
`lambda` for which both coordinates stay below the height.  Their number is the floor of
`N / max(u₁,u₂)`, and shrinking from `N` to `N₀` loses at most the source factor
`N/N₀` and one endpoint.
-/

namespace RHTower.Sieve

open Finset

/-- Positive integer scales whose two coordinates on a fixed ray do not exceed `N`. -/
def heathBrownRayScales (u : ℕ+ × ℕ+) (N : ℕ) : Finset ℕ :=
  Finset.Icc 1 (N / max (u.1 : ℕ) (u.2 : ℕ))

/-- Membership is exactly positivity together with both coordinate bounds. -/
theorem mem_heathBrownRayScales {u : ℕ+ × ℕ+} {N lambda : ℕ} :
    lambda ∈ heathBrownRayScales u N ↔
      0 < lambda ∧ lambda * (u.1 : ℕ) ≤ N ∧ lambda * (u.2 : ℕ) ≤ N := by
  rw [heathBrownRayScales, Finset.mem_Icc]
  have hu : 0 < max (u.1 : ℕ) (u.2 : ℕ) :=
    lt_of_lt_of_le u.1.pos (le_max_left _ _)
  rw [Nat.le_div_iff_mul_le hu]
  constructor
  · rintro ⟨hlam, hmax⟩
    refine ⟨hlam, ?_, ?_⟩
    · exact le_trans (Nat.mul_le_mul_left lambda (le_max_left _ _)) hmax
    · exact le_trans (Nat.mul_le_mul_left lambda (le_max_right _ _)) hmax
  · rintro ⟨hlam, h1, h2⟩
    refine ⟨hlam, ?_⟩
    rcases le_total (u.1 : ℕ) (u.2 : ℕ) with hle | hle
    · simpa [max_eq_right hle] using h2
    · simpa [max_eq_left hle] using h1

/-- The number of scales on a ray is the expected floor. -/
@[simp]
theorem card_heathBrownRayScales (u : ℕ+ × ℕ+) (N : ℕ) :
    #(heathBrownRayScales u N) = N / max (u.1 : ℕ) (u.2 : ℕ) := by
  simp [heathBrownRayScales]

/-- Distinct positive scales give distinct lattice pairs on a positive ray. -/
theorem heathBrownRayScale_injective (u : ℕ+ × ℕ+) :
    Function.Injective (fun lambda : ℕ =>
      (lambda * (u.1 : ℕ), lambda * (u.2 : ℕ))) := by
  intro a b hab
  have hfirst := congrArg Prod.fst hab
  simpa using hfirst

/-- Common positive scaling preserves the logarithmic collision displacement exactly. -/
theorem abs_log_mul_rayScale_sub_log_mul_rayScale
    (m₁ m₂ u₁ u₂ lambda : ℕ+) :
    |Real.log (((m₁ : ℕ) * ((lambda : ℕ) * (u₁ : ℕ)) : ℕ) : ℝ) -
        Real.log (((m₂ : ℕ) * ((lambda : ℕ) * (u₂ : ℕ)) : ℕ) : ℝ)| =
      |Real.log (((m₁ : ℕ) * (u₁ : ℕ) : ℕ) : ℝ) -
        Real.log (((m₂ : ℕ) * (u₂ : ℕ) : ℕ) : ℝ)| := by
  have hm₁ : (0 : ℝ) < (m₁ : ℕ) := by exact_mod_cast m₁.pos
  have hm₂ : (0 : ℝ) < (m₂ : ℕ) := by exact_mod_cast m₂.pos
  have hu₁ : (0 : ℝ) < (u₁ : ℕ) := by exact_mod_cast u₁.pos
  have hu₂ : (0 : ℝ) < (u₂ : ℕ) := by exact_mod_cast u₂.pos
  have hlam : (0 : ℝ) < (lambda : ℕ) := by exact_mod_cast lambda.pos
  push_cast
  rw [Real.log_mul hm₁.ne' (mul_ne_zero hlam.ne' hu₁.ne'),
    Real.log_mul hlam.ne' hu₁.ne',
    Real.log_mul hm₂.ne' (mul_ne_zero hlam.ne' hu₂.ne'),
    Real.log_mul hlam.ne' hu₂.ne',
    Real.log_mul hm₁.ne' hu₁.ne', Real.log_mul hm₂.ne' hu₂.ne']
  congr 1
  ring

/-- **Heath--Brown bad-ray rescaling.**  Shrinking a positive ray from height `N` to positive
height `N₀` costs at most `N/N₀` and one endpoint. -/
theorem card_heathBrownRayScales_le_mul_succ
    (u : ℕ+ × ℕ+) {N N₀ : ℕ} (hN₀ : 0 < N₀) :
    (#(heathBrownRayScales u N) : ℝ) ≤
      (N : ℝ) / (N₀ : ℝ) * (1 + #(heathBrownRayScales u N₀)) := by
  let U : ℕ := max (u.1 : ℕ) (u.2 : ℕ)
  have hU : 0 < U := lt_of_lt_of_le u.1.pos (le_max_left _ _)
  have hUR : (0 : ℝ) < U := by exact_mod_cast hU
  have hN₀R : (0 : ℝ) < N₀ := by exact_mod_cast hN₀
  have hupper : ((N / U : ℕ) : ℝ) ≤ (N : ℝ) / (U : ℝ) := by
    rw [le_div_iff₀ hUR]
    exact_mod_cast Nat.div_mul_le_self N U
  have hlower := cast_natDiv_ge_sub_one N₀ U hU
  have hscaled : (N : ℝ) / (U : ℝ) =
      (N : ℝ) / (N₀ : ℝ) * ((N₀ : ℝ) / (U : ℝ)) := by
    field_simp
  rw [card_heathBrownRayScales, card_heathBrownRayScales]
  calc
    ((N / U : ℕ) : ℝ) ≤ (N : ℝ) / (U : ℝ) := hupper
    _ = (N : ℝ) / (N₀ : ℝ) * ((N₀ : ℝ) / (U : ℝ)) := hscaled
    _ ≤ (N : ℝ) / (N₀ : ℝ) * (1 + ((N₀ / U : ℕ) : ℝ)) := by
      have hfac : 0 ≤ (N : ℝ) / (N₀ : ℝ) := by positivity
      gcongr
      linarith

end RHTower.Sieve
