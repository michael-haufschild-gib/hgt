import GaloisForLFunctions.RHTower.Sieve.GhsHeightChoice

/-!
# The mean value, eventually

`ghsHeight N = ⌊(log N)⁶⌋ + 1` satisfies every condition of `norm_sum_Icc_le_ghs_window` for all
large `N`, so the Granville–Harper–Soundararajan bound holds eventually with no hypothesis except
the multiplicative distance.

The distance data is quantified *inside* the eventual statement, and that is not an accident.  The
damping `δ` bounds `𝔻(f, n^{iy})` on `|y| ≤ ghsHeight N`, a range that grows with `N`; a `δ` fixed
before `N` would have to bound the distance on the whole line, which no useful `δ` does.  Halász's
theorem has the same shape: the quantity `m` in `(1+m)e^{−m}` depends on both `x` and the height.
-/

noncomputable section

namespace RHTower.Sieve

open Complex Filter Asymptotics Finset

/-- `e⁴ ≤ 81`. -/
theorem exp_four_le : Real.exp 4 ≤ 81 := by
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h4 : Real.exp 4 = (Real.exp 1) ^ (4 : ℕ) := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [h4]
  calc (Real.exp 1) ^ (4 : ℕ) ≤ (2.7182818286 : ℝ) ^ (4 : ℕ) :=
        pow_le_pow_left₀ (Real.exp_pos 1).le h1.le 4
    _ ≤ 81 := by norm_num

/-- **The height is admissible for all large `N`.** -/
theorem eventually_ghsHeight_admissible :
    ∀ᶠ N : ℕ in Filter.atTop,
      16 ≤ N ∧ (3 : ℝ) ≤ Real.log N ∧ Real.exp 4 ≤ ((ghsHeight N : ℕ) : ℝ)
        ∧ (ghsHeight N) ^ 2 ≤ N ∧ 2 ≤ N / (ghsHeight N) ^ 2
        ∧ (ghsHeight N) ^ 2 ≤ ghsScale N 1 := by
  have hlog3 : ∀ᶠ N : ℕ in Filter.atTop, (3 : ℝ) ≤ Real.log N :=
    tendsto_natCast_atTop_atTop.eventually (Real.tendsto_log_atTop.eventually_ge_atTop 3)
  filter_upwards [hlog3, eventually_pow_log_le_ghsScale, Filter.eventually_ge_atTop 16]
    with N hlog hscale hN16
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2' : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hL0 : (0 : ℝ) < Real.log N := by linarith
  have hsq9 : (9 : ℝ) ≤ (Real.log N) ^ 2 := by nlinarith [hlog]
  have hlog1 : (1 : ℝ) ≤ Real.log N := by linarith
  have h81 : (81 : ℝ) ≤ (Real.log N) ^ 4 := by nlinarith [hsq9, sq_nonneg ((Real.log N) ^ 2 - 9)]
  have h46 : (Real.log N) ^ 4 ≤ (Real.log N) ^ 6 := pow_le_pow_right₀ hlog1 (by norm_num)
  have hone : (1 : ℝ) ≤ (Real.log N) ^ 6 := by linarith
  have hhlow := log_pow_le_ghsHeight N
  have hhup := ghsHeight_le hone
  -- the square of the height is below the square root scale
  have hsq : ((ghsHeight N ^ 2 : ℕ) : ℝ) ≤ ((ghsScale N 1 : ℕ) : ℝ) := by
    have h0 : (0 : ℝ) ≤ ((ghsHeight N : ℕ) : ℝ) := Nat.cast_nonneg _
    have hstep : ((ghsHeight N : ℕ) : ℝ) ^ 2 ≤ 4 * (Real.log N) ^ 12 := by
      nlinarith [hhup, h0, hone]
    push_cast
    linarith [hstep, hscale]
  have hsqN : ghsHeight N ^ 2 ≤ ghsScale N 1 := by exact_mod_cast hsq
  -- the scale is at least two
  have hk1 : (2 : ℝ) ^ (1 : ℕ) * Real.log 2 ≤ Real.log N := by
    norm_num
    linarith
  have hs2 : 2 ≤ ghsScale N 1 := ghsScale_pos (by omega) hk1
  have hcomp : ghsScale N 1 ≤ N / ghsScale N 1 := by
    have := ghsScale_le_ghsBlockRight_zero (N := N) (by omega)
    have hrw : ghsBlockRight N 0 = N / ghsScale N 1 := by norm_num [ghsBlockRight]
    rwa [hrw] at this
  have hhpos : 0 < ghsHeight N := by rw [ghsHeight]; omega
  have hdiv : N / ghsScale N 1 ≤ N / ghsHeight N ^ 2 :=
    Nat.div_le_div_left hsqN (pow_pos hhpos 2)
  refine ⟨hN16, hlog, ?_, ?_, ?_, hsqN⟩
  · exact le_trans exp_four_le (by linarith [hhlow, h81, h46])
  · exact le_trans hsqN (ghsScale_le (by omega))
  · exact le_trans (le_trans hs2 hcomp) hdiv

/-- The fourth power of the logarithm is below the sixth. -/
theorem ghs_log_pow_four_le (N : ℕ) (h : (3 : ℝ) ≤ Real.log N) :
    (Real.log N) ^ 4 ≤ (Real.log N) ^ 6 :=
  pow_le_pow_right₀ (by linarith) (by norm_num)

/-- **The Granville–Harper–Soundararajan mean value, eventually.** -/
theorem eventually_norm_sum_Icc_le_ghs
    {f : ℕ → ℂ} (hf1 : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hcm : ∀ p q : ℕ, f (p * q) = f p * f q)
    (hf : ∀ i : ℕ, ‖f i‖ ≤ 1) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (z : ℕ) (σ δ : ℝ), 1 < σ → 1 ≤ z → 0 ≤ δ →
      (∀ y : ℝ, |y| ≤ ((ghsHeight N : ℕ) : ℝ) →
        δ ≤ Real.sqrt (mulDistSqPair f (charFn y) (Nat.primesLE z))) →
      ‖∑ m ∈ Finset.Icc 1 N, f m‖
        ≤ (ghsRecursionError N
              + ((ghsScaleCount N + 2 : ℕ) : ℝ)
                * (ghsTotalError N (ghsHeight N) (ghsScaleCount N) σ
                    + (1 / (2 * Real.pi))
                      * (dampedSize σ δ z N * ((N : ℝ) + 1 / 2) ^ σ
                          * ghsBlockConstOf σ ghsShapeConst))) / Real.log (N : ℝ) := by
  filter_upwards [eventually_ghsHeight_admissible] with N hN
  obtain ⟨hN16, hlog, hexp, hPN, hNP, hroot⟩ := hN
  intro z σ δ hσ hz hδ hunif
  exact norm_sum_Icc_le_ghs_window hf1 hmul hcm hf hσ hz hδ hunif hexp hN16 hPN hNP hroot
    (ghs_height_inequality hlog (le_trans (ghs_log_pow_four_le N hlog) (log_pow_le_ghsHeight N)))

end RHTower.Sieve

end
