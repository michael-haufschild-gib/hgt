import GaloisForLFunctions.RenormalizedBiarithmeticGeometry.TheDyadicAmplificationOfTheHeckeDefect
import GaloisForLFunctions.RenormalizedBiarithmeticGeometry.TheHeckeMomentProblem
import GaloisForLFunctions.ConjugateDiagonalGeometry.FiniteThetaMetric

/-!
# Integer theta prefixes read the defect without loss

CDG computes every depth moment `m_j(L)` of the collided zeta form from a finite prefix of integer
theta data: the reading `R_n(f, L, j)` built from the integers `≤ n` satisfies
`|R_n(f, L, j) − m_j(L)| < ε` uniformly for `j|L| ≤ 2 log(n + 1)`, `n ≥ N(ε)`
(`finiteThetaSource_uniform_moving_moments`). Dyadic amplification turns one such reading at a large
dyadic scale into a bound at the base scale with no loss.

* **Readings compute the moment problem** (`reading_depthMoment`, `reading_hankelForm`). The Hankel
  forms of the depth moments are read from finite integer prefixes, with error `ε (Σ|c_i|)²`.
* **Source-side lossless transfer** (`heckeDefect_le_of_readings`). If at one prefix length `n` and
  one dyadic scale `2^k L ≤ 2 log(n + 1)` the readings satisfy
  `R_n(f, 2^k L, 1) + ε ≤ (R_n(f, 0, 0) − ε)(2cosh(2^k φ) − 2)`, then
  `E_f(L) ≤ D(f)(2cosh φ − 2)`: the depth seen by `f` at scale `L` is at most `φ/(2L)`.
* **Readings detect depth** (`reading_ge_of_heckeDefect_ge`). Conversely an effective angle `θ` at
  scale `L` forces `R_n(f, 2^k L, 1) > D(f)(2cosh(2^k θ) − 2) − ε` at every admissible dyadic scale.

Both sides of the transfer are finite computations with integers; the logarithmic range
`2^k|L| ≤ 2 log(n + 1)` is the only place where the prefix length enters.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.RenormalizedBiarithmeticGeometry

open Zeta23 GaloisForLFunctions.ConjugateDiagonalGeometry GaloisForLFunctions.ArithmeticPolarization

/-- The finite integer theta reading of the `j`-th depth moment at prefix length `n`. -/
abbrev reading (f : CompactTest) (L : ℝ) (j n : ℕ) : ℝ := finiteThetaSourceMomentReading f L j n

/-- **Readings compute the depth moments**, uniformly on the logarithmic window. -/
theorem reading_depthMoment (f : CompactTest) (j : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ L : ℝ, (j : ℝ) * |L| ≤ 2 * Real.log ((n : ℝ) + 1) →
      |reading f L j n - depthMoment f L j| < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := finiteThetaSource_uniform_moving_moments f j ε hε
  refine ⟨N, fun n hn L hL => ?_⟩
  have h := hN n hn L 0 (by simp; positivity) hL
  rw [sourceTwist_zero] at h
  exact h

/-- The reading at `j = 0` computes the collided mass. -/
theorem reading_mass (f : CompactTest) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, |reading f 0 0 n - mass f| < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := reading_depthMoment f 0 ε hε
  refine ⟨N, fun n hn => ?_⟩
  have hlog : 0 ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_nonneg (by have := n.cast_nonneg (α := ℝ); linarith)
  have h := hN n hn 0 (by rw [Nat.cast_zero, zero_mul]; linarith)
  rwa [depthMoment_zero] at h

/-- The reading at `j = 1` computes the Hecke defect. -/
theorem reading_heckeDefect (f : CompactTest) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ L : ℝ, |L| ≤ 2 * Real.log ((n : ℝ) + 1) →
      |reading f L 1 n - heckeDefect f L| < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := reading_depthMoment f 1 ε hε
  refine ⟨N, fun n hn L hL => ?_⟩
  have h := hN n hn L (by simpa using hL)
  rwa [depthMoment_one] at h

/-- **Readings compute the Hankel forms** of the moment problem, with error `ε (Σ|c_i|)²`. -/
theorem reading_hankelForm (f : CompactTest) (m : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ L : ℝ,
      (2 * m : ℝ) * |L| ≤ 2 * Real.log ((n : ℝ) + 1) → ∀ c : Fin m → ℝ,
        |∑ i, ∑ j, c i * c j * reading f L (i + j) n - hankelForm f L 0 c| ≤
          ε * (∑ i, |c i|) ^ 2 := by
  intro ε hε
  -- One prefix length for all moments of order `< 2m`.
  have hN : ∀ j : Fin (2 * m), ∃ N : ℕ, ∀ n ≥ N, ∀ L : ℝ,
      ((j : ℕ) : ℝ) * |L| ≤ 2 * Real.log ((n : ℝ) + 1) →
        |reading f L j n - depthMoment f L j| < ε := fun j => reading_depthMoment f j ε hε
  choose N hN using hN
  refine ⟨univ.sup N, fun n hn L hL c => ?_⟩
  have herr : ∀ i j : Fin m, |reading f L (i + j) n - depthMoment f L (i + j)| ≤ ε := by
    intro i j
    have hij : (i : ℕ) + j < 2 * m := by omega
    have h := hN ⟨_, hij⟩ n (le_trans (Finset.le_sup (mem_univ _)) hn) L (by
      calc (((i : ℕ) + j : ℕ) : ℝ) * |L| ≤ (2 * m : ℝ) * |L| := by
            apply mul_le_mul_of_nonneg_right _ (abs_nonneg L)
            exact_mod_cast hij.le
        _ ≤ _ := hL)
    exact h.le
  rw [hankelForm, ← sum_sub_distrib, sq, sum_mul_sum, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  rw [← sum_sub_distrib, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
  rw [Nat.add_zero, ← mul_sub, abs_mul, abs_mul]
  calc |c i| * |c j| * |reading f L (↑i + ↑j) n - depthMoment f L (↑i + ↑j)|
      ≤ |c i| * |c j| * ε := mul_le_mul_of_nonneg_left (herr i j) (by positivity)
    _ = ε * (|c i| * |c j|) := by ring

/-- **Source-side lossless transfer.** One pair of integer-prefix readings at a single dyadic scale
`2^k L` bounds the Hecke defect at the base scale `L`. -/
theorem heckeDefect_le_of_readings (f : CompactTest) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ (L φ : ℝ) (k : ℕ),
      (2 : ℝ) ^ k * |L| ≤ 2 * Real.log ((n : ℝ) + 1) →
      reading f ((2 : ℝ) ^ k * L) 1 n + ε ≤
        (reading f 0 0 n - ε) * (2 * Real.cosh ((2 : ℝ) ^ k * φ) - 2) →
      heckeDefect f L ≤ mass f * (2 * Real.cosh φ - 2) := by
  intro ε hε
  obtain ⟨N₁, h₁⟩ := reading_heckeDefect f ε hε
  obtain ⟨N₀, h₀⟩ := reading_mass f ε hε
  refine ⟨max N₁ N₀, fun n hn L φ k hL hread => ?_⟩
  have hE := h₁ n (le_of_max_le_left hn) ((2 : ℝ) ^ k * L) (by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ k)]; exact hL)
  have hD := h₀ n (le_of_max_le_right hn)
  have hc : 0 ≤ 2 * Real.cosh ((2 : ℝ) ^ k * φ) - 2 := two_mul_cosh_sub_two_nonneg _
  have hDle : reading f 0 0 n - ε ≤ mass f := by linarith [(abs_lt.mp hD).2]
  apply heckeDefect_le_of_dyadic_le f L φ k
  calc heckeDefect f ((2 : ℝ) ^ k * L) ≤ reading f ((2 : ℝ) ^ k * L) 1 n + ε := by
        linarith [(abs_lt.mp hE).1]
    _ ≤ (reading f 0 0 n - ε) * (2 * Real.cosh ((2 : ℝ) ^ k * φ) - 2) := hread
    _ ≤ mass f * (2 * Real.cosh ((2 : ℝ) ^ k * φ) - 2) := mul_le_mul_of_nonneg_right hDle hc

/-- **Readings detect depth.** An effective angle `θ` at scale `L` is visible in the integer-prefix
reading at every admissible dyadic scale. -/
theorem reading_ge_of_heckeDefect_ge (f : CompactTest) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ (L θ : ℝ) (k : ℕ),
      (2 : ℝ) ^ k * |L| ≤ 2 * Real.log ((n : ℝ) + 1) →
      mass f * (2 * Real.cosh θ - 2) ≤ heckeDefect f L →
      mass f * (2 * Real.cosh ((2 : ℝ) ^ k * θ) - 2) - ε < reading f ((2 : ℝ) ^ k * L) 1 n := by
  intro ε hε
  obtain ⟨N, hN⟩ := reading_heckeDefect f ε hε
  refine ⟨N, fun n hn L θ k hL hθ => ?_⟩
  have hE := hN n hn ((2 : ℝ) ^ k * L) (by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ k)]; exact hL)
  have hamp := heckeDefect_dyadic_ge f L θ hθ k
  linarith [(abs_lt.mp hE).1]

end GaloisForLFunctions.RenormalizedBiarithmeticGeometry
