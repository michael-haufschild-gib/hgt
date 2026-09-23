import GaloisForLFunctions.RHTower.Sieve.SupportMeanSquare

/-!
# An affine majorant from a single head bound

Gallagher's dyadic split asks for an affine majorant `∫_{|w| ≤ T}‖A‖² ≤ αT + β` valid at **every**
height above the cutoff, but the mean square is monotone in the height and the mean value theorem
already majorises it above any fixed `T₀`.  So one bound, at one height, suffices: take the constant
to be that bound and load the mean value theorem's height-free term onto the slope, divided by `T₀`.

This is what turns the whole Matomäki–Radziwiłł input into a single inequality
`∫_{|w| ≤ T₀}‖A‖² ≤ β`, with `T₀` only slightly above the Gallagher cutoff.
-/

namespace RHTower.Sieve

open MeasureTheory Finset

noncomputable section

/-- **An affine majorant at every height, from one bound at height `T₀`.** -/
theorem integral_Icc_normSq_logPoly_affine_of_head (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) {N : ℕ}
    {s : Finset ℕ} (hs0 : (0 : ℕ) ∉ s) (hsN : ∀ n ∈ s, n ≤ N)
    {G T₀ B : ℝ} (hG : 1 ≤ G) (hGT₀ : G ≤ T₀) (hB0 : 0 ≤ B)
    (hB : (∫ w in Set.Icc (-T₀) T₀, ‖logPoly a s w‖ ^ (2 : ℕ)) ≤ B) :
    ∀ T : ℝ, G ≤ T →
      (∫ w in Set.Icc (-T) T, ‖logPoly a s w‖ ^ (2 : ℕ))
        ≤ (5 * Real.pi / 2 * (s.card : ℝ)
            + 5 * Real.exp 1 / 2 * (N : ℝ) * (s.card : ℝ) / T₀) * T + B := by
  intro T hT
  have hT0 : (1 : ℝ) ≤ T := le_trans hG hT
  have hT₀0 : (0 : ℝ) < T₀ := lt_of_lt_of_le zero_lt_one (le_trans hG hGT₀)
  have hcard : (0 : ℝ) ≤ (s.card : ℝ) := Nat.cast_nonneg _
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have hslope : (0 : ℝ) ≤ 5 * Real.pi / 2 * (s.card : ℝ)
      + 5 * Real.exp 1 / 2 * (N : ℝ) * (s.card : ℝ) / T₀ := by
    have := Real.pi_pos
    have := (Real.exp_pos 1).le
    positivity
  rcases le_or_gt T T₀ with hle | hgt
  · have hmono : (∫ w in Set.Icc (-T) T, ‖logPoly a s w‖ ^ (2 : ℕ))
        ≤ ∫ w in Set.Icc (-T₀) T₀, ‖logPoly a s w‖ ^ (2 : ℕ) := by
      have hcont : Continuous fun w : ℝ => ‖logPoly a s w‖ ^ (2 : ℕ) :=
        ((continuous_logPoly a s).norm).pow 2
      refine MeasureTheory.setIntegral_mono_set
        (hcont.integrableOn_Icc (a := -T₀) (b := T₀))
        (Filter.Eventually.of_forall fun w => by positivity)
        (Filter.Eventually.of_forall fun u hu => ?_)
      have hu' : -T ≤ u ∧ u ≤ T := Set.mem_Icc.1 hu
      exact Set.mem_Icc.2 ⟨by linarith [hu'.1], by linarith [hu'.2]⟩
    nlinarith [hmono, hB, hslope, hT0]
  · have hmvt := integral_Icc_normSq_logPoly_le_support a hs0 hsN ha hT0
    have hbase : (0 : ℝ) ≤ 5 * Real.exp 1 / 2 * (N : ℝ) * (s.card : ℝ) := by
      have := (Real.exp_pos 1).le
      positivity
    have hratio : (1 : ℝ) ≤ T / T₀ := (one_le_div hT₀0).2 hgt.le
    have hstep : 5 * Real.exp 1 / 2 * (N : ℝ) * (s.card : ℝ)
        ≤ 5 * Real.exp 1 / 2 * (N : ℝ) * (s.card : ℝ) / T₀ * T := by
      calc 5 * Real.exp 1 / 2 * (N : ℝ) * (s.card : ℝ)
          = 5 * Real.exp 1 / 2 * (N : ℝ) * (s.card : ℝ) * 1 := by ring
        _ ≤ 5 * Real.exp 1 / 2 * (N : ℝ) * (s.card : ℝ) * (T / T₀) :=
            mul_le_mul_of_nonneg_left hratio hbase
        _ = 5 * Real.exp 1 / 2 * (N : ℝ) * (s.card : ℝ) / T₀ * T := by
            field_simp
    nlinarith [hmvt, hstep, hB0]

end

end RHTower.Sieve
