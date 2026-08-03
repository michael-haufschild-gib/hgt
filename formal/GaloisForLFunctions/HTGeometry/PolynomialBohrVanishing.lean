import GaloisForLFunctions.HTGeometry.BohrExponentialSeriesCoefficient

/-!
# Polynomial combinations of almost periodic functions

A differential relation has coefficients in `C[z]`, so on the real line it presents an almost
periodic identity with polynomial coefficients, and the Bohr mean of `t^d e^{i nu t}` diverges once
`d >= 1`.

The way past this is the top-degree term: dividing by `t^D` sends every lower term to zero, so the
top coefficient function tends to zero at `+infinity`, and an almost periodic function which does
that vanishes identically.  Downward induction then kills every coefficient.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **A polynomial combination of bounded almost periodic functions vanishes coefficientwise.** -/
theorem eq_zero_of_polynomialCombination_bohr (G : ℕ → ℝ → ℂ)
    (hap : ∀ d, HTGeometry.IsBohrAlmostPeriodic (G d))
    (hbdd : ∀ d, ∃ C : ℝ, ∀ t : ℝ, ‖G d t‖ ≤ C) :
    ∀ (D : ℕ), (∀ t : ℝ, ∑ d ∈ Finset.range (D + 1), (t : ℂ) ^ d * G d t = 0) →
      ∀ d ≤ D, G d = 0 := by
  intro D
  induction D with
  | zero =>
      intro hsum d hd
      have hd0 : d = 0 := Nat.le_zero.mp hd
      subst hd0
      funext t
      have h := hsum t
      simpa using h
  | succ D ih =>
      intro hsum
      -- the top coefficient tends to zero
      choose C hC using hbdd
      set B : ℝ := ∑ d ∈ Finset.range (D + 1), C d with hB
      have hbound : ∀ t : ℝ, 1 ≤ t → ‖G (D + 1) t‖ ≤ B / t := by
        intro t ht
        have htpos : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
        have hsplit := hsum t
        rw [Finset.sum_range_succ] at hsplit
        have htop : ((t : ℂ)) ^ (D + 1) * G (D + 1) t
            = -∑ d ∈ Finset.range (D + 1), (t : ℂ) ^ d * G d t := by
          linear_combination hsplit
        have hnorm : ‖((t : ℂ)) ^ (D + 1) * G (D + 1) t‖
            ≤ ∑ d ∈ Finset.range (D + 1), t ^ d * C d := by
          rw [htop, norm_neg]
          refine le_trans (norm_sum_le _ _) ?_
          refine Finset.sum_le_sum fun d hd => ?_
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg htpos.le]
          exact mul_le_mul_of_nonneg_left (hC d t) (by positivity)
        have hlhs : ‖((t : ℂ)) ^ (D + 1) * G (D + 1) t‖ = t ^ (D + 1) * ‖G (D + 1) t‖ := by
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg htpos.le]
        have hstep : ∀ d ∈ Finset.range (D + 1), t ^ d * C d ≤ t ^ D * C d := by
          intro d hd
          rw [Finset.mem_range] at hd
          have hle : t ^ d ≤ t ^ D := pow_le_pow_right₀ ht (by omega)
          have hCnn : 0 ≤ C d := le_trans (norm_nonneg _) (hC d 0)
          exact mul_le_mul_of_nonneg_right hle hCnn
        have hsum2 : ∑ d ∈ Finset.range (D + 1), t ^ d * C d ≤ t ^ D * B := by
          refine le_trans (Finset.sum_le_sum hstep) ?_
          rw [hB, Finset.mul_sum]
        have hkey : t ^ (D + 1) * ‖G (D + 1) t‖ ≤ t ^ D * B := by
          rw [← hlhs]
          exact le_trans hnorm hsum2
        have htD : (0 : ℝ) < t ^ D := by positivity
        have hpow : t ^ (D + 1) * ‖G (D + 1) t‖ = t ^ D * (t * ‖G (D + 1) t‖) := by
          rw [pow_succ]
          ring
        rw [hpow] at hkey
        have hfinal : t * ‖G (D + 1) t‖ ≤ B := le_of_mul_le_mul_left hkey htD
        rw [le_div_iff₀ htpos]
        linarith
      have htend : Tendsto (fun t : ℝ => G (D + 1) t) atTop (nhds 0) := by
        have hBt : Tendsto (fun t : ℝ => B / t) atTop (nhds 0) :=
          tendsto_const_nhds.div_atTop tendsto_id
        refine squeeze_zero_norm' ?_ hBt
        filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
        exact hbound t ht
      have htop0 : ∀ t, G (D + 1) t = 0 :=
        HTGeometry.eq_zero_of_isBohrAlmostPeriodic_of_tendsto_zero (hap (D + 1)) htend
      have hrest : ∀ t : ℝ, ∑ d ∈ Finset.range (D + 1), (t : ℂ) ^ d * G d t = 0 := by
        intro t
        have h := hsum t
        rw [Finset.sum_range_succ, htop0 t, mul_zero, add_zero] at h
        exact h
      intro d hd
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hd) with hlt | heq
      · exact ih hrest d (Nat.lt_succ_iff.mp hlt)
      · subst heq
        funext t
        exact htop0 t

end

end GaloisForLFunctions.HTGeometry
