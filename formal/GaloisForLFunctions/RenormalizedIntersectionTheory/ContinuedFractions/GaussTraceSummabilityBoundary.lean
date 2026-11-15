import GaloisForLFunctions.RenormalizedIntersectionTheory.ContinuedFractions.GaussWordCylinderEstimates

/-!
# The exact absolute-convergence boundary for the full Gauss alphabet

At and below exponent two, each even-word level has at least half the total
cylinder probability. Above two, denominator growth gives geometric decay.
Thus the full family of even-word trace norms is summable exactly on `Re w>2`.
The unit-parameter even-word logarithm has the same boundary: its endpoint
mass dominates a divergent harmonic series.
-/

open Filter Topology
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerWords
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerWordProbability

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerTraceBoundary
noncomputable section

private theorem multiplier_le_denominator_sum (k : ℕ) (a : Word (k + 1)) :
    wordMultiplier k a ≤ (wordMatrix (k + 1) a 1 0 : ℝ) + wordMatrix (k + 1) a 1 1 := by
  have h := mul_le_mul_of_nonneg_left (fixedPoint_real_interval k a).2.le
    (Nat.cast_nonneg (wordMatrix (k + 1) a 1 0))
  unfold wordMultiplier
  linarith only [h]

/-- Half the exact cylinder probability is bounded by the inverse multiplier square. -/
theorem half_probability_le_multiplier (k : ℕ) (a : Word (k + 1)) :
    probability (k + 1) a / 2 ≤ wordMultiplier k a ^ (-(2 : ℝ)) := by
  have hl : 0 < wordMultiplier k a := zero_lt_one.trans (one_lt_wordMultiplier k a)
  have hd : (0 : ℝ) < wordMatrix (k + 1) a 1 1 := by
    exact_mod_cast (wordMatrix_denominator_row (k + 1) a).2
  have hc : (0 : ℝ) ≤ wordMatrix (k + 1) a 1 0 := Nat.cast_nonneg _
  have hcd : (wordMatrix (k + 1) a 1 0 : ℝ) ≤ wordMatrix (k + 1) a 1 1 := by
    exact_mod_cast (wordMatrix_denominator_row (k + 1) a).1
  have hs : wordMultiplier k a ^ 2 ≤
      ((wordMatrix (k + 1) a 1 0 : ℝ) + wordMatrix (k + 1) a 1 1) ^ 2 :=
    pow_le_pow_left₀ hl.le (multiplier_le_denominator_sum k a) 2
  have hb : wordMultiplier k a ^ 2 ≤
      2 * ((wordMatrix (k + 1) a 1 1 : ℝ) *
        (wordMatrix (k + 1) a 1 0 + wordMatrix (k + 1) a 1 1)) := by
    have h := mul_nonneg (sub_nonneg.mpr hcd) (add_nonneg hc hd.le)
    nlinarith only [hs, h]
  calc
    _ = 1 / (2 * ((wordMatrix (k + 1) a 1 1 : ℝ) *
        (wordMatrix (k + 1) a 1 0 + wordMatrix (k + 1) a 1 1))) := by
      simp only [probability, div_eq_mul_inv, mul_inv_rev, one_mul]
    _ ≤ 1 / wordMultiplier k a ^ 2 := one_div_le_one_div_of_le (sq_pos_of_pos hl) hb
    _ = wordMultiplier k a ^ (-(2 : ℝ)) := by
      symm
      calc
        _ = (wordMultiplier k a ^ (2 : ℝ))⁻¹ := Real.rpow_neg hl.le 2
        _ = (wordMultiplier k a ^ (2 : ℕ))⁻¹ :=
          congrArg (fun x : ℝ => x⁻¹) (Real.rpow_two (wordMultiplier k a))
        _ = _ := (one_div _).symm

/-- The even-word trace norm depends only on the real exponent and its expanding multiplier. -/
theorem norm_even_wordTrace_eq (w : ℂ) (k : ℕ) (a : Word (2 * k + 2)) :
    ‖wordTrace w (2 * k + 1) a‖ =
      wordMultiplier (2 * k + 1) a ^ (-w.re) /
        (1 - 1 / wordMultiplier (2 * k + 1) a ^ 2) := by
  have hl := one_lt_wordMultiplier (2 * k + 1) a
  have hl0 : 0 < wordMultiplier (2 * k + 1) a := zero_lt_one.trans hl
  have hsq : 1 < wordMultiplier (2 * k + 1) a ^ 2 := by
    nlinarith only [hl, sq_nonneg (wordMultiplier (2 * k + 1) a - 1)]
  have hi : 1 / wordMultiplier (2 * k + 1) a ^ 2 < (1 : ℝ) :=
    (div_lt_one (sq_pos_of_pos hl0)).mpr hsq
  have hC : (1 - (-1 : ℂ) ^ (2 * k + 1 + 1) /
      (wordMultiplier (2 * k + 1) a : ℂ) ^ 2) =
      ((1 - 1 / wordMultiplier (2 * k + 1) a ^ 2 : ℝ) : ℂ) := by
    push_cast
    simp only [show 2 * k + 1 + 1 = 2 * k + 2 by omega, pow_add, pow_mul]
    norm_num
  rw [wordTrace_eq_multiplier, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hl0,
    Complex.neg_re, hC, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hi)]

/-- Below the threshold, every even trace carries half its exact cylinder probability. -/
theorem half_probability_le_trace {w : ℂ} (hw : w.re ≤ 2) (k : ℕ) (a : Word (2 * k + 2)) :
    probability (2 * k + 2) a / 2 ≤ ‖wordTrace w (2 * k + 1) a‖ := by
  have hl := one_lt_wordMultiplier (2 * k + 1) a
  have hl0 : 0 < wordMultiplier (2 * k + 1) a := zero_lt_one.trans hl
  have hsq : 1 < wordMultiplier (2 * k + 1) a ^ 2 := by
    nlinarith only [hl, sq_nonneg (wordMultiplier (2 * k + 1) a - 1)]
  have hi : 1 / wordMultiplier (2 * k + 1) a ^ 2 < (1 : ℝ) :=
    (div_lt_one (sq_pos_of_pos hl0)).mpr hsq
  calc
    _ ≤ wordMultiplier (2 * k + 1) a ^ (-(2 : ℝ)) :=
      half_probability_le_multiplier (2 * k + 1) a
    _ ≤ wordMultiplier (2 * k + 1) a ^ (-w.re) :=
      Real.rpow_le_rpow_of_exponent_le hl.le (neg_le_neg hw)
    _ ≤ ‖wordTrace w (2 * k + 1) a‖ := by
      rw [norm_even_wordTrace_eq]
      apply (le_div_iff₀ (sub_pos.mpr hi)).mpr
      have hp := mul_nonneg (Real.rpow_nonneg hl0.le (-w.re))
        (show 0 ≤ 1 / wordMultiplier (2 * k + 1) a ^ 2 by positivity)
      nlinarith only [hp]

/-- Absolute convergence of all even-word traces holds exactly above real exponent two. -/
theorem summable_even_traces_iff (w : ℂ) :
    Summable (fun p : Σ k : ℕ, Word (2 * k + 2) =>
      ‖wordTrace w (2 * p.1 + 1) p.2‖) ↔ 2 < w.re := by
  constructor
  · intro hs
    by_contra h
    have hw : w.re ≤ 2 := le_of_not_gt h
    have hf := (summable_sigma_of_nonneg (fun p : Σ k : ℕ, Word (2 * k + 2) =>
      norm_nonneg (wordTrace w (2 * p.1 + 1) p.2))).mp hs
    have hlevel (k : ℕ) : (1 / 2 : ℝ) ≤
        ∑' a : Word (2 * k + 2), ‖wordTrace w (2 * k + 1) a‖ := by
      have hp := (hasSum_probability (2 * k + 2)).div_const (2 : ℝ)
      rw [← hp.tsum_eq]
      exact hp.summable.tsum_le_tsum (half_probability_le_trace hw k) (hf.1 k)
    have hc : Summable (fun _ : ℕ => (1 / 2 : ℝ)) :=
      hf.2.of_nonneg_of_le (fun _ => by norm_num) hlevel
    have hz : (1 / 2 : ℝ) = 0 := (summable_const_iff (1 / 2 : ℝ)).mp hc
    norm_num at hz
  · intro hw
    have hr := decayRate_bounds hw
    have habs : |decayRate w| < 1 := by rw [abs_of_pos hr.1]; exact hr.2
    have hs := (summable_geometric_of_abs_lt_one habs).mul_left ((8 / 3 : ℝ) * decayRate w)
    have hlength : Summable (fun k : ℕ =>
        ∑' a : Word (2 * k + 2), ‖wordTrace w (2 * k + 1) a‖) := by
      apply hs.of_nonneg_of_le (fun k => tsum_nonneg (fun a => norm_nonneg _))
      intro k
      calc
        _ ≤ (8 / 3 : ℝ) * decayRate w ^ (k + 1) := tsum_norm_even_wordTrace_le hw k
        _ = ((8 / 3 : ℝ) * decayRate w) * decayRate w ^ k := by rw [pow_succ]; ring
    apply (summable_sigma_of_nonneg (fun p => norm_nonneg _)).mpr
    exact ⟨fun k => (summable_wordTrace (w := w) (lt_trans (by norm_num) hw) (2 * k + 1)).norm,
      hlength⟩

private theorem summable_even_log_weights_iff (w : ℂ) :
    Summable (fun p : Σ k : ℕ, Word (2 * k + 2) =>
      ‖wordTrace w (2 * p.1 + 1) p.2‖ / ((p.1 : ℝ) + 1)) ↔ 2 < w.re := by
  constructor
  · intro hs
    by_contra h
    have hw : w.re ≤ 2 := le_of_not_gt h
    have hf := (summable_sigma_of_nonneg (fun p : Σ k : ℕ, Word (2 * k + 2) =>
      div_nonneg (norm_nonneg (wordTrace w (2 * p.1 + 1) p.2)) (by positivity))).mp hs
    have hlevel (k : ℕ) : (1 / 2 : ℝ) / ((k : ℝ) + 1) ≤
        ∑' a : Word (2 * k + 2), ‖wordTrace w (2 * k + 1) a‖ / ((k : ℝ) + 1) := by
      have hp := ((hasSum_probability (2 * k + 2)).div_const (2 : ℝ)).div_const ((k : ℝ) + 1)
      rw [← hp.tsum_eq]
      exact hp.summable.tsum_le_tsum (fun a => div_le_div_of_nonneg_right
        (half_probability_le_trace hw k a) (by positivity)) (hf.1 k)
    have hh : Summable (fun k : ℕ => (1 / 2 : ℝ) / ((k : ℝ) + 1)) :=
      hf.2.of_nonneg_of_le (fun _ => by positivity) hlevel
    have hone : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1)) :=
      (hh.mul_left (2 : ℝ)).congr (fun k => by ring)
    apply Real.not_summable_one_div_natCast
    apply (summable_nat_add_iff (f := fun k : ℕ => 1 / (k : ℝ)) 1).mp
    simpa only [Nat.cast_add, Nat.cast_one] using hone
  · intro hw
    apply ((summable_even_traces_iff w).mpr hw).of_nonneg_of_le
      (fun p => div_nonneg (norm_nonneg _) (by positivity))
    intro p
    have hn : (0 : ℝ) ≤ p.1 := Nat.cast_nonneg p.1
    exact div_le_self (norm_nonneg _) (by linarith only [hn])

/-- The actual countable even-word logarithm at the unit spectral parameter converges
absolutely exactly on `Re w>2`; the endpoint obstruction is harmonic. -/
theorem summable_unit_evenWordSeries_iff (w : ℂ) :
    Summable (fun p : Σ k : ℕ, Word (2 * k + 2) =>
      ‖(1 : ℂ) ^ (2 * p.1 + 2) / ((p.1 + 1 : ℕ) : ℂ) *
        wordTrace w (2 * p.1 + 1) p.2‖) ↔ 2 < w.re := by
  have he : (fun p : Σ k : ℕ, Word (2 * k + 2) =>
      ‖(1 : ℂ) ^ (2 * p.1 + 2) / ((p.1 + 1 : ℕ) : ℂ) *
        wordTrace w (2 * p.1 + 1) p.2‖) =
      (fun p : Σ k : ℕ, Word (2 * k + 2) =>
        ‖wordTrace w (2 * p.1 + 1) p.2‖ / ((p.1 : ℝ) + 1)) := by
    funext p
    rw [one_pow, norm_mul, norm_div, norm_one, Complex.norm_natCast,
      Nat.cast_add, Nat.cast_one]
    ring
  rw [he]
  exact summable_even_log_weights_iff w

#print axioms half_probability_le_multiplier
#print axioms norm_even_wordTrace_eq
#print axioms half_probability_le_trace
#print axioms summable_even_traces_iff
#print axioms summable_unit_evenWordSeries_iff

end
end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerTraceBoundary

