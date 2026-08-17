import GaloisForLFunctions.HTGeometry.ExponentialSumZeros

/-!
# Exponential sums at `-∞`: the dominant term

At `-∞` an exponential sum is governed by its **smallest** exponent: dividing by `e^{a i₀ t}`, where
`a i₀` is the strict minimum, kills every other term and leaves the coefficient `c i₀`.  In
particular the sum eventually has the sign of that coefficient.

This is the ingredient that upgrades a Rolle-descent count to the sharp Descartes/Laguerre bound: in
the case where the two lowest coefficients share a sign, the sum has a definite sign near `-∞`, so
between `-∞` and any zero the derivative must itself vanish, supplying the extra zero that the naive
Rolle count misses.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- A single exponential with positive exponent vanishes at `-∞`. -/
theorem tendsto_exp_mul_atBot {α : ℝ} (hα : 0 < α) :
    Tendsto (fun t : ℝ => Real.exp (α * t)) atBot (𝓝 0) := by
  have h : Tendsto (fun t : ℝ => α * t) atBot atBot :=
    Filter.Tendsto.const_mul_atBot hα tendsto_id
  exact Real.tendsto_exp_atBot.comp h

/-- **The dominant term at `-∞`.**  If the exponent indexed by `i₀` is zero and every other exponent
is positive, the exponential sum tends to `c i₀` at `-∞`. -/
theorem tendsto_expSum_atBot {m : ℕ} (c a : Fin m → ℝ) (i₀ : Fin m)
    (h₀ : a i₀ = 0) (hpos : ∀ i, i ≠ i₀ → 0 < a i) :
    Tendsto (expSum c a) atBot (𝓝 (c i₀)) := by
  have hterm : ∀ i : Fin m, i ∈ Finset.univ →
      Tendsto (fun t : ℝ => c i * Real.exp (a i * t)) atBot
        (𝓝 (if i = i₀ then c i else 0)) := by
    intro i _
    by_cases hi : i = i₀
    · subst hi
      simp only [h₀, zero_mul, Real.exp_zero, mul_one, if_pos]
      exact tendsto_const_nhds
    · simp only [if_neg hi]
      have := (tendsto_exp_mul_atBot (hpos i hi)).const_mul (c i)
      simpa using this
  have hsum := tendsto_finsetSum Finset.univ hterm
  have hval : (∑ i : Fin m, if i = i₀ then c i else 0) = c i₀ := by
    simp
  rw [hval] at hsum
  exact hsum.congr (fun t => rfl)

/-- The sum is eventually positive at `-∞` when the dominant coefficient is positive. -/
theorem eventually_expSum_pos_atBot {m : ℕ} (c a : Fin m → ℝ) (i₀ : Fin m)
    (h₀ : a i₀ = 0) (hpos : ∀ i, i ≠ i₀ → 0 < a i) (hc : 0 < c i₀) :
    ∀ᶠ t in atBot, 0 < expSum c a t :=
  (tendsto_expSum_atBot c a i₀ h₀ hpos).eventually (eventually_gt_nhds hc)

/-- The sum is eventually negative at `-∞` when the dominant coefficient is negative. -/
theorem eventually_expSum_neg_atBot {m : ℕ} (c a : Fin m → ℝ) (i₀ : Fin m)
    (h₀ : a i₀ = 0) (hpos : ∀ i, i ≠ i₀ → 0 < a i) (hc : c i₀ < 0) :
    ∀ᶠ t in atBot, expSum c a t < 0 :=
  (tendsto_expSum_atBot c a i₀ h₀ hpos).eventually (eventually_lt_nhds hc)

/-- **The general dominant-term statement.**  Normalising by the strictly smallest exponent, an
exponential sum tends to the corresponding coefficient at `-∞`. -/
theorem tendsto_expSum_shift_atBot {m : ℕ} (c a : Fin m → ℝ) (i₀ : Fin m)
    (hmin : ∀ i, i ≠ i₀ → a i₀ < a i) :
    Tendsto (expSum c (fun i => a i - a i₀)) atBot (𝓝 (c i₀)) := by
  refine tendsto_expSum_atBot c (fun i => a i - a i₀) i₀ (by simp) ?_
  intro i hi
  have := hmin i hi
  simp only [sub_pos]
  exact this

end GaloisForLFunctions.HTGeometry
