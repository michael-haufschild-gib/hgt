import GaloisForLFunctions.RHTower.PerronVonMangoldtSwap
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The `ζ′/ζ` bound on vertical lines `Re s = a > 1`

`‖ζ′/ζ(s)‖ ≤ Σ Λ(n) n^{-Re s} ≤ 8/(Re s - 1)²` for `1 < Re s ≤ 2`:
the von Mangoldt Dirichlet series dominates its own norms, `Λ(n) ≤
log n ≤ (2/(a-1))·n^{(a-1)/2}`, and the remaining `p`-series is an
integral comparison.  This is the tail estimate for the `a`-line of
the Perron contour at `a = 1 + 1/log x`.
-/

noncomputable section

namespace RHTower

open MeasureTheory Set ArithmeticFunction

/-- The shifted `p`-series bound `Σ (n+1)^{-b} ≤ 1 + 1/(b-1)`. -/
theorem tsum_add_one_rpow_le {b : ℝ} (hb : 1 < b) :
    ∑' n : ℕ, ((n : ℝ) + 1) ^ (-b) ≤ 1 + 1 / (b - 1) := by
  have hb1 : (0 : ℝ) < b - 1 := by linarith
  have hsummable : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-b)) := by
    have h1 := (Real.summable_one_div_nat_add_rpow 1 b).2 hb
    apply h1.congr
    intro n
    rw [Real.rpow_neg (by positivity), abs_of_pos (by positivity),
      inv_eq_one_div]
  have hanti : ∀ M : ℕ, AntitoneOn (fun t : ℝ => t ^ (-b))
      (Set.Icc ((1 : ℕ) : ℝ) ((M + 1 : ℕ) : ℝ)) := by
    intro M s hs t ht hst
    have hs0 : (0 : ℝ) < s := by
      have h2 := hs.1
      push_cast at h2
      linarith
    exact Real.rpow_le_rpow_of_nonpos hs0 hst (by linarith)
  have hintle : ∀ M : ℕ,
      (∫ t in ((1 : ℕ) : ℝ)..((M + 1 : ℕ) : ℝ), t ^ (-b))
        ≤ 1 / (b - 1) := by
    intro M
    have hM1 : ((1 : ℕ) : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := by
      push_cast
      linarith
    rw [intervalIntegral.integral_of_le hM1]
    have hio : IntegrableOn (fun t : ℝ => t ^ (-b)) (Set.Ioi (1 : ℝ)) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
    calc ∫ t in Set.Ioc ((1 : ℕ) : ℝ) ((M + 1 : ℕ) : ℝ), t ^ (-b)
        ≤ ∫ t in Set.Ioi (1 : ℝ), t ^ (-b) := by
          apply setIntegral_mono_set hio
          · filter_upwards [MeasureTheory.ae_restrict_mem
              measurableSet_Ioi] with t ht
            have ht1 : (1 : ℝ) < t := ht
            positivity
          · filter_upwards with t ht
            obtain ⟨h3, h4⟩ := ht
            show (1 : ℝ) < t
            push_cast at h3
            linarith
      _ = 1 / (b - 1) := by
          rw [integral_Ioi_rpow_of_lt (by linarith) one_pos,
            Real.one_rpow]
          have hne : (-b + 1 : ℝ) ≠ 0 := by linarith
          field_simp
          linarith
  apply hsummable.tsum_le_of_sum_range_le
  intro N
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
    positivity
  · obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
      (Nat.pos_iff_ne_zero.1 hN)
    rw [Finset.sum_range_succ']
    have hzero : ((0 : ℕ) : ℝ) + 1 = 1 := by norm_num
    rw [hzero, Real.one_rpow]
    have hcompare := (hanti M).sum_le_integral_Ico
      (by omega : 1 ≤ M + 1)
    rw [Finset.sum_Ico_eq_sum_range] at hcompare
    simp only [Nat.add_sub_cancel] at hcompare
    have hsame : (∑ i ∈ Finset.range M, (((i + 1 : ℕ) : ℝ) + 1) ^ (-b))
        = ∑ i ∈ Finset.range M, ((((1 + i : ℕ) + 1 : ℕ)) : ℝ) ^ (-b) := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      push_cast
      ring
    rw [hsame]
    have h4 := le_trans hcompare (hintle M)
    linarith

/-- **The von Mangoldt `p`-series bound**:
`Σ Λ(n)/n^a ≤ 8/(a-1)²` for `1 < a ≤ 2`. -/
theorem tsum_vonMangoldt_div_rpow_le {a : ℝ} (h1 : 1 < a) (h2 : a ≤ 2) :
    ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ a
      ≤ 8 / (a - 1) ^ 2 := by
  have ha1 : (0 : ℝ) < a - 1 := by linarith
  have hb : 1 < (a + 1) / 2 := by linarith
  have hε : (0 : ℝ) < (a - 1) / 2 := by linarith
  have hbne : -((a + 1) / 2) ≠ 0 := neg_ne_zero.2 (ne_of_gt (by linarith))
  -- termwise domination
  have hterm : ∀ n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ a
      ≤ (2 / (a - 1)) * ((n : ℝ)) ^ (-((a + 1) / 2)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [ArithmeticFunction.map_zero, Nat.cast_zero, zero_div,
        Real.zero_rpow hbne, mul_zero]
    · have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 hn
      have hlog : Real.log (n : ℝ)
          ≤ (2 / (a - 1)) * ((n : ℝ)) ^ ((a - 1) / 2) := by
        have h3 := Real.log_le_rpow_div hn0.le hε
        calc Real.log (n : ℝ)
            ≤ ((n : ℝ)) ^ ((a - 1) / 2) / ((a - 1) / 2) := h3
          _ = (2 / (a - 1)) * ((n : ℝ)) ^ ((a - 1) / 2) := by
              field_simp
      calc ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ a
          ≤ Real.log (n : ℝ) / (n : ℝ) ^ a := by
            gcongr
            exact vonMangoldt_le_log
        _ ≤ ((2 / (a - 1)) * ((n : ℝ)) ^ ((a - 1) / 2)) / (n : ℝ) ^ a := by
            gcongr
        _ = (2 / (a - 1)) * ((n : ℝ)) ^ (-((a + 1) / 2)) := by
            rw [mul_div_assoc, ← Real.rpow_sub hn0,
              show (a - 1) / 2 - a = -((a + 1) / 2) from by ring]
  have hg_summable : Summable
      (fun n : ℕ => (2 / (a - 1)) * ((n : ℝ)) ^ (-((a + 1) / 2))) := by
    apply Summable.mul_left
    exact Real.summable_nat_rpow.2 (by linarith)
  have hf_nonneg : ∀ n : ℕ,
      0 ≤ ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ a := fun n =>
    div_nonneg vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) a)
  have hf_summable : Summable
      (fun n : ℕ => ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ a) :=
    Summable.of_nonneg_of_le hf_nonneg hterm hg_summable
  have hsb : Summable (fun n : ℕ => ((n : ℝ)) ^ (-((a + 1) / 2))) :=
    Real.summable_nat_rpow.2 (by linarith)
  calc ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ a
      ≤ ∑' n : ℕ, (2 / (a - 1)) * ((n : ℝ)) ^ (-((a + 1) / 2)) :=
        hf_summable.tsum_le_tsum hterm hg_summable
    _ = (2 / (a - 1)) * ∑' n : ℕ, ((n : ℝ)) ^ (-((a + 1) / 2)) :=
        tsum_mul_left
    _ ≤ (2 / (a - 1)) * (1 + 1 / ((a + 1) / 2 - 1)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [hsb.tsum_eq_zero_add, Nat.cast_zero, Real.zero_rpow hbne,
          zero_add]
        have hcast : (fun n : ℕ => (((n + 1 : ℕ)) : ℝ) ^ (-((a + 1) / 2)))
            = fun n : ℕ => ((n : ℝ) + 1) ^ (-((a + 1) / 2)) := by
          funext n
          congr 1
          push_cast
          ring
        rw [hcast]
        exact tsum_add_one_rpow_le hb
    _ ≤ 8 / (a - 1) ^ 2 := by
        rw [show (a + 1) / 2 - 1 = (a - 1) / 2 from by ring, one_div_div]
        have h5 : 2 / (a - 1) * (1 + 2 / (a - 1))
            = 2 * (a - 1) / (a - 1) ^ 2 + 4 / (a - 1) ^ 2 := by
          field_simp
          ring
        have h6 : 2 * (a - 1) / (a - 1) ^ 2 ≤ 2 / (a - 1) ^ 2 := by
          gcongr
          linarith
        have h7 : (2 : ℝ) / (a - 1) ^ 2 + 4 / (a - 1) ^ 2
            ≤ 8 / (a - 1) ^ 2 := by
          rw [← add_div]
          gcongr
          norm_num
        linarith

/-- **The `ζ′/ζ` vertical-line bound**:
`‖ζ′/ζ(s)‖ ≤ 8/(Re s - 1)²` for `1 < Re s ≤ 2`. -/
theorem norm_zeta_logDeriv_le_line {s : ℂ} (h1 : 1 < s.re)
    (h2 : s.re ≤ 2) :
    ‖deriv riemannZeta s / riemannZeta s‖ ≤ 8 / (s.re - 1) ^ 2 := by
  have hLS := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := s) h1
  have hnorms : Summable (fun n : ℕ =>
      ‖LSeries.term (fun m : ℕ =>
        ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ)) s n‖) :=
    summable_norm_iff.2 hLS
  have hterm_norm : ∀ n : ℕ,
      ‖LSeries.term (fun m : ℕ =>
        ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ)) s n‖
      = ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ s.re := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [LSeries.term_def, ArithmeticFunction.map_zero]
    · have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 hn
      rw [LSeries.term_def, if_neg (Nat.pos_iff_ne_zero.1 hn), norm_div,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg vonMangoldt_nonneg,
        show ((n : ℕ) : ℂ) = (((n : ℕ) : ℝ) : ℂ) from
          (Complex.ofReal_natCast n).symm,
        Complex.norm_cpow_eq_rpow_re_of_pos hn0]
  have hnorm_eq : ‖deriv riemannZeta s / riemannZeta s‖
      = ‖LSeries (fun m : ℕ =>
          ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ)) s‖ := by
    rw [LSeries_vonMangoldt_eq_deriv_riemannZeta_div h1, neg_div,
      norm_neg]
  rw [hnorm_eq]
  calc ‖LSeries (fun m : ℕ =>
          ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ)) s‖
      ≤ ∑' n : ℕ, ‖LSeries.term (fun m : ℕ =>
          ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ)) s n‖ :=
        norm_tsum_le_tsum_norm hnorms
    _ = ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ s.re :=
        tsum_congr hterm_norm
    _ ≤ 8 / (s.re - 1) ^ 2 := tsum_vonMangoldt_div_rpow_le h1 h2

end RHTower
