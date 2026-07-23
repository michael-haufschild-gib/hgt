import GaloisForLFunctions.HTGeometry.ShiftStableSuperlacunaryDominationUniversalityLaw
import GaloisForLFunctions.HTGeometry.SuperexponentialGrowth
import GaloisForLFunctions.HTGeometry.SuperlacunaryExists

/-!
# Finite-difference superlacunary domination universality

Increment explosion iterates: every finite forward-difference layer of an eventually positive
divergent-ratio sequence remains eventually positive with divergent successive ratio.  Each layer
therefore tends to infinity, survives every fixed nonnegative residual shift, and exponentially
dominates every fixed positive polynomial scale.
-/

open Filter

namespace GaloisForLFunctions

/-- The `k`-fold forward-difference layer of a real sequence. -/
def iteratedSuccessiveIncrement (b : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0 => b
  | k + 1 => fun n =>
      iteratedSuccessiveIncrement b k (n + 1) -
        iteratedSuccessiveIncrement b k n

@[simp]
theorem iteratedSuccessiveIncrement_zero (b : ℕ → ℝ) :
    iteratedSuccessiveIncrement b 0 = b := rfl

@[simp]
theorem iteratedSuccessiveIncrement_succ (b : ℕ → ℝ) (k n : ℕ) :
    iteratedSuccessiveIncrement b (k + 1) n =
      iteratedSuccessiveIncrement b k (n + 1) -
        iteratedSuccessiveIncrement b k n := rfl

/-- Every finite forward-difference layer of an eventually positive divergent-ratio sequence is
again eventually positive with divergent successive ratio. -/
theorem iteratedSuccessiveIncrement_superlacunary {b : ℕ → ℝ}
    (hpos : ∀ᶠ n in atTop, 0 < b n)
    (hratio : Tendsto (fun n => b (n + 1) / b n) atTop atTop) :
    ∀ k : ℕ,
      (∀ᶠ n in atTop, 0 < iteratedSuccessiveIncrement b k n) ∧
        Tendsto
          (fun n =>
            iteratedSuccessiveIncrement b k (n + 1) /
              iteratedSuccessiveIncrement b k n)
          atTop atTop := by
  intro k
  induction k with
  | zero =>
      exact ⟨hpos, hratio⟩
  | succ k ih =>
      simpa only [iteratedSuccessiveIncrement_succ, Nat.add_assoc, Nat.reduceAdd] using
        (increments_ratio_tendsto_atTop ih.1 ih.2)

/-- Every finite forward-difference layer tends to infinity. -/
theorem iteratedSuccessiveIncrement_tendsto_atTop {b : ℕ → ℝ}
    (hpos : ∀ᶠ n in atTop, 0 < b n)
    (hratio : Tendsto (fun n => b (n + 1) / b n) atTop atTop)
    (k : ℕ) :
    Tendsto (iteratedSuccessiveIncrement b k) atTop atTop := by
  have hk := iteratedSuccessiveIncrement_superlacunary hpos hratio k
  have hquot :=
    tendsto_div_natCast_atTop_of_ratio_tendsto_atTop hk.1 hk.2
  refine tendsto_atTop_mono' atTop ?_ hquot
  filter_upwards [hk.1, eventually_ge_atTop 1] with n hbn hn
  have hnReal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnPos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le zero_lt_one hnReal
  rw [div_le_iff₀ hnPos]
  nlinarith

/-- **Finite-difference superlacunary domination universality law.**  At every finite difference
depth and after every fixed nonnegative residual shift, positivity, divergent ratio, and universal
polynomial exponential domination hold simultaneously. -/
theorem finiteDifferenceSuperlacunaryDominationUniversality {b : ℕ → ℝ}
    (hpos : ∀ᶠ n in atTop, 0 < b n)
    (hratio : Tendsto (fun n => b (n + 1) / b n) atTop atTop)
    (k : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    (∀ᶠ n in atTop, 0 < iteratedSuccessiveIncrement b k n - c) ∧
      Tendsto
        (fun n =>
          (iteratedSuccessiveIncrement b k (n + 1) - c) /
            (iteratedSuccessiveIncrement b k n - c))
        atTop atTop ∧
      ∀ (A : ℝ), 0 < A → ∀ (C E R : ℕ), 0 < C →
        ∃ M₀ : ℕ, ∀ m ≥ M₀,
          A * ((C : ℝ) * ((m : ℝ) + 1)) ^ E <
            Real.exp
              ((iteratedSuccessiveIncrement b k m - c) /
                ((R : ℝ) + 1)) := by
  have hk := iteratedSuccessiveIncrement_superlacunary hpos hratio k
  exact shiftStableSuperlacunaryDominationUniversality
    (iteratedSuccessiveIncrement_tendsto_atTop hpos hratio k) hk.2 hc

/-- The universal finite-difference hierarchy is inhabited by a strictly increasing positive real
sequence: one may cast the corpus factorial superlacunary sequence to `ℝ`. -/
theorem exists_strictMono_allFiniteDifferences_superlacunary :
    ∃ b : ℕ → ℝ,
      StrictMono b ∧
        (∀ n, 0 < b n) ∧
        ∀ k : ℕ,
          (∀ᶠ n in atTop, 0 < iteratedSuccessiveIncrement b k n) ∧
            Tendsto
              (fun n =>
                iteratedSuccessiveIncrement b k (n + 1) /
                  iteratedSuccessiveIncrement b k n)
              atTop atTop := by
  obtain ⟨bnat, hmono, hpos, hratio⟩ := exists_superlacunary_sequence
  let b : ℕ → ℝ := fun n => bnat n
  have hmonoReal : StrictMono b := by
    intro m n hmn
    change (bnat m : ℝ) < (bnat n : ℝ)
    exact_mod_cast hmono hmn
  have hposReal : ∀ n, 0 < b n := by
    intro n
    change (0 : ℝ) < (bnat n : ℝ)
    exact_mod_cast hpos n
  refine ⟨b, hmonoReal, hposReal, ?_⟩
  exact iteratedSuccessiveIncrement_superlacunary
    (Filter.Eventually.of_forall hposReal) hratio

end GaloisForLFunctions
