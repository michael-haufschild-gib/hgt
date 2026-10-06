import GaloisForLFunctions.RHTower.SelbergNearLineWindowConvexity

/-!
# Three-lines for the mollified tail with a far right line

The coefficients of the tail `f_N = ζΨ_N − 1 − P_N` vanish up to `N` and are at most `n` beyond, so
on `Re s ≥ σ ≥ 3`

`‖f_N(s)‖ ≤ Σ_{n > N} n^{1−σ} ≤ N^{3−σ} Σ_{n > N} n^{−2} ≤ 2 N^{2−σ}` (`norm_hbMollifiedTail_le_rpow`).

For `H ≥ σ_R ≥ 3` every window of length `2H` on `Re z = σ_R` therefore has windowed mean square at
most `8e² H N^{4−2σ_R}` (`integral_nearLineWindowField_farRight_le`), and three-lines between a left
line `σ_L ≥ 1/4` and `σ_R` gives, on every center line `1/2 ≤ σ₀ ≤ 1`,

`∫_{τ−H}^{τ+H} ‖f_N(σ₀+it)‖² dt ≤ 2e² S_L^{1−λ} (8e² H N^{4−2σ_R})^λ`,  `λ = (σ₀−σ_L)/(σ_R−σ_L)`
(`integral_hbMollifiedTail_window_le_farRight`).

Moving the right line out costs only the factor `(σ_R − 2)/(σ_R − σ_L)` in the decay rate `N^{−2λ(σ_R−2)}`.
-/

noncomputable section

open Complex Set MeasureTheory

namespace RHTower

/-- **The tail on `Re s ≥ σ ≥ 3`.** `‖ζΨ_N − 1 − P_N‖ ≤ 2 N^{2−σ}`. -/
theorem norm_hbMollifiedTail_le_rpow {N : ℕ} (hN : 2 ≤ N) {σ : ℝ} (hσ : 3 ≤ σ) {s : ℂ}
    (hs : σ ≤ s.re) : ‖hbMollifiedTail N s‖ ≤ 2 * (N : ℝ) ^ (2 - σ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  rw [hbMollifiedTail_eq_LSeries (by linarith)]
  set g : ℕ → ℝ := fun n => if N < n then ((n : ℝ) ^ 2)⁻¹ else 0 with hg
  have hg0 : ∀ n, 0 ≤ g n := fun n => by simp only [hg]; split_ifs <;> positivity
  have hP0 : 0 ≤ (N : ℝ) ^ (3 - σ) := Real.rpow_nonneg hN0.le _
  have hterm : ∀ n : ℕ, ‖LSeries.term (hbTailCoeff N) s n‖ ≤ (N : ℝ) ^ (3 - σ) * g n := by
    intro n
    rw [LSeries.norm_term_eq]
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [if_pos h0]
      exact mul_nonneg hP0 (hg0 n)
    · rw [if_neg hpos.ne']
      by_cases hNn : N < n
      · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
        have hnpos : (0 : ℝ) < n := by linarith
        have hNn' : (N : ℝ) ≤ n := by exact_mod_cast hNn.le
        have hc := norm_hbTailCoeff_le hN hNn
        have hpow : (n : ℝ) ^ σ ≤ (n : ℝ) ^ s.re := Real.rpow_le_rpow_of_exponent_le hn1 hs
        have hgn : g n = ((n : ℝ) ^ 2)⁻¹ := by simp only [hg, if_pos hNn]
        have hsplit : (n : ℝ) ^ σ = (n : ℝ) ^ 3 * (n : ℝ) ^ (σ - 3) := by
          rw [← Real.rpow_natCast, ← Real.rpow_add hnpos]
          norm_num
        have hmono : (n : ℝ) ^ (3 - σ) ≤ (N : ℝ) ^ (3 - σ) :=
          Real.rpow_le_rpow_of_nonpos hN0 hNn' (by linarith)
        have hinv : (n : ℝ) ^ (3 - σ) * (n : ℝ) ^ (σ - 3) = 1 := by
          rw [← Real.rpow_add hnpos]
          norm_num
        rw [hgn, div_le_iff₀ (by positivity)]
        calc ‖hbTailCoeff N n‖ ≤ n := hc
          _ = ((n : ℝ) ^ (3 - σ) * (n : ℝ) ^ (σ - 3)) * ((n : ℝ) ^ 3 * ((n : ℝ) ^ 2)⁻¹) := by
              rw [hinv, one_mul]
              field_simp
          _ = (n : ℝ) ^ (3 - σ) * ((n : ℝ) ^ 2)⁻¹ * ((n : ℝ) ^ 3 * (n : ℝ) ^ (σ - 3)) := by ring
          _ ≤ (N : ℝ) ^ (3 - σ) * ((n : ℝ) ^ 2)⁻¹ * (n : ℝ) ^ s.re := by
              rw [← hsplit]
              exact mul_le_mul (mul_le_mul_of_nonneg_right hmono (by positivity)) hpow
                (by positivity) (by positivity)
      · rw [hbTailCoeff_eq_zero_of_le hN (not_lt.mp hNn), norm_zero, zero_div]
        exact mul_nonneg hP0 (hg0 n)
  have hgsum : Summable g := by
    refine Summable.of_nonneg_of_le hg0 (fun n => ?_)
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    simp only [hg]
    split_ifs
    · rw [one_div]
    · positivity
  have htsum : ∑' n, g n ≤ 2 / N := by
    refine hgsum.tsum_le_of_sum_le fun S => ?_
    obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ n ∈ S, n < M := ⟨S.sup id + 1, fun n hn =>
      Nat.lt_succ_of_le (Finset.le_sup (f := id) hn)⟩
    calc ∑ n ∈ S, g n ≤ ∑ n ∈ Finset.range M, g n := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => Finset.mem_range.mpr (hM n hn))
            fun n _ _ => hg0 n
      _ = ∑ n ∈ Finset.Ioo N M, ((n : ℝ) ^ 2)⁻¹ := by
          rw [← Finset.sum_filter_add_sum_filter_not (Finset.range M) (fun n => N < n)]
          have h1 : ∑ n ∈ (Finset.range M).filter (fun n => ¬ N < n), g n = 0 :=
            Finset.sum_eq_zero fun n hn => by
              simp only [hg, if_neg (Finset.mem_filter.mp hn).2]
          rw [h1, add_zero]
          have hset : (Finset.range M).filter (fun n => N < n) = Finset.Ioo N M := by
            ext n
            simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioo]
            tauto
          rw [hset]
          refine Finset.sum_congr rfl fun n hn => ?_
          simp only [hg, if_pos (Finset.mem_Ioo.mp hn).1]
      _ ≤ 2 / ((N : ℝ) + 1) := sum_Ioo_inv_sq_le N M
      _ ≤ 2 / N := div_le_div_of_nonneg_left (by norm_num) hN0 (by linarith)
  have hsumnorm : Summable fun n => ‖LSeries.term (hbTailCoeff N) s n‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm (hgsum.mul_left _)
  have hNpow : (N : ℝ) ^ (3 - σ) * (2 / N) = 2 * (N : ℝ) ^ (2 - σ) := by
    have h : (N : ℝ) ^ (3 - σ) = (N : ℝ) ^ (2 - σ) * N := by
      rw [show (3 : ℝ) - σ = (2 - σ) + 1 by ring, Real.rpow_add hN0, Real.rpow_one]
    rw [h]
    field_simp
  calc ‖LSeries (hbTailCoeff N) s‖ ≤ ∑' n, ‖LSeries.term (hbTailCoeff N) s n‖ :=
        norm_tsum_le_tsum_norm hsumnorm
    _ ≤ ∑' n, (N : ℝ) ^ (3 - σ) * g n := hsumnorm.tsum_le_tsum hterm (hgsum.mul_left _)
    _ = (N : ℝ) ^ (3 - σ) * ∑' n, g n := tsum_mul_left
    _ ≤ (N : ℝ) ^ (3 - σ) * (2 / N) := mul_le_mul_of_nonneg_left htsum hP0
    _ = 2 * (N : ℝ) ^ (2 - σ) := hNpow

/-- The windowed field on `Re z ≥ 3`: the Gaussian is at most `e` while `H ≥ Re z`. -/
theorem norm_nearLineWindowField_le_of_three_le {N : ℕ} (hN : 2 ≤ N) {H τ : ℝ} {z : ℂ}
    (hz : 3 ≤ z.re) (hH : z.re ≤ H) :
    ‖nearLineWindowField N H τ z‖ ≤ Real.exp 1 * (2 * (N : ℝ) ^ (2 - z.re)) := by
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; norm_num at hz
  have hz1 : z ≠ 1 := fun h => by rw [h] at hz; norm_num at hz
  have hH0 : 0 < H := by linarith
  unfold nearLineWindowField
  rw [norm_mul, nearLineField_eq hz0 hz1, norm_mul]
  have hG : ‖nearLineGauss H τ z‖ ≤ Real.exp 1 := by
    rw [norm_nearLineGauss_eq]
    apply Real.exp_le_exp.mpr
    rw [div_le_one (by positivity)]
    nlinarith [sq_nonneg (z.im - τ)]
  have hfac : ‖(z - 1) / z‖ ≤ 1 := norm_sub_one_div_le_one (by linarith)
  have htail := norm_hbMollifiedTail_le_rpow hN hz (le_refl z.re)
  calc ‖nearLineGauss H τ z‖ * (‖(z - 1) / z‖ * ‖hbMollifiedTail N z‖)
      ≤ Real.exp 1 * (1 * (2 * (N : ℝ) ^ (2 - z.re))) := by gcongr
    _ = Real.exp 1 * (2 * (N : ℝ) ^ (2 - z.re)) := by ring

/-- **Far right edge.** Every window of length `2H` on `Re z = σ_R` has windowed mean square at most
`8e² H N^{4−2σ_R}`. -/
theorem integral_nearLineWindowField_farRight_le {N : ℕ} (hN : 2 ≤ N) {H τ σR : ℝ}
    (hσR : 3 ≤ σR) (hH : σR ≤ H) (y : ℝ) :
    ∫ t in (τ - H)..(τ + H),
        ‖nearLineWindowField N H τ ((σR : ℂ) + ((y + t : ℝ) : ℂ) * I)‖ ^ 2 ≤
      8 * Real.exp 2 * H * (N : ℝ) ^ (4 - 2 * σR) := by
  have hH0 : 0 < H := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hsq : ((N : ℝ) ^ (2 - σR)) ^ 2 = (N : ℝ) ^ (4 - 2 * σR) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    norm_num
    ring_nf
  have hpt : ∀ t : ℝ, ‖nearLineWindowField N H τ ((σR : ℂ) + ((y + t : ℝ) : ℂ) * I)‖ ^ 2 ≤
      4 * Real.exp 2 * (N : ℝ) ^ (4 - 2 * σR) := by
    intro t
    have hre : ((σR : ℂ) + ((y + t : ℝ) : ℂ) * I).re = σR := by simp
    have h := norm_nearLineWindowField_le_of_three_le hN (H := H) (τ := τ)
      (z := (σR : ℂ) + ((y + t : ℝ) : ℂ) * I) (by rw [hre]; exact hσR) (by rw [hre]; exact hH)
    rw [hre] at h
    calc ‖nearLineWindowField N H τ ((σR : ℂ) + ((y + t : ℝ) : ℂ) * I)‖ ^ 2
        ≤ (Real.exp 1 * (2 * (N : ℝ) ^ (2 - σR))) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h 2
      _ = 4 * (Real.exp 1 ^ 2) * ((N : ℝ) ^ (2 - σR)) ^ 2 := by ring
      _ = 4 * Real.exp 2 * (N : ℝ) ^ (4 - 2 * σR) := by
          rw [hsq, ← Real.exp_nat_mul]
          norm_num
  have hint : IntervalIntegrable
      (fun t : ℝ => ‖nearLineWindowField N H τ ((σR : ℂ) + ((y + t : ℝ) : ℂ) * I)‖ ^ 2)
      volume (τ - H) (τ + H) := by
    have hc := continuous_nearLineWindowField_line N H τ (σ := σR) (by linarith)
    exact ((hc.comp (continuous_const.add continuous_id)).norm.pow 2).intervalIntegrable _ _
  calc ∫ t in (τ - H)..(τ + H),
        ‖nearLineWindowField N H τ ((σR : ℂ) + ((y + t : ℝ) : ℂ) * I)‖ ^ 2
      ≤ ∫ _t in (τ - H)..(τ + H), (4 * Real.exp 2 * (N : ℝ) ^ (4 - 2 * σR) : ℝ) :=
        intervalIntegral.integral_mono_on (by linarith) hint intervalIntegrable_const
          fun t _ => hpt t
    _ = 8 * Real.exp 2 * H * (N : ℝ) ^ (4 - 2 * σR) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        ring

/-- **Three-lines for one window, far right line.** -/
theorem integral_hbMollifiedTail_window_le_farRight {N : ℕ} (hN : 2 ≤ N)
    {H τ σL σ₀ σR SL CW : ℝ} (hσR : 3 ≤ σR) (hH : σR ≤ H) (hCW : 0 ≤ CW)
    (hW : ∀ z : ℂ, 1 / 4 ≤ z.re → z.re ≤ 3 → ‖nearLineField N z‖ ≤ CW * N * (1 + |z.im|))
    (hσL : 1 / 4 ≤ σL) (hσL₀ : σL ≤ σ₀) (hσ₀ : 1 / 2 ≤ σ₀) (hσ₀' : σ₀ ≤ 1)
    (hτ : 1 + H ≤ τ) (hSL : 0 < SL)
    (hleft : ∀ y : ℝ, ∫ t in (τ - H)..(τ + H),
      ‖nearLineWindowField N H τ ((σL : ℂ) + ((y + t : ℝ) : ℂ) * I)‖ ^ 2 ≤ SL) :
    ∫ t in (τ - H)..(τ + H), ‖hbMollifiedTail N ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      2 * Real.exp 2 * (SL ^ (1 - (σ₀ - σL) / (σR - σL)) *
        (8 * Real.exp 2 * H * (N : ℝ) ^ (4 - 2 * σR)) ^ ((σ₀ - σL) / (σR - σL))) := by
  have hH0 : 0 < H := by linarith
  have hH3 : 3 ≤ H := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlu : σL < σR := by linarith
  set F : ℂ → ℂ := nearLineWindowField N H τ with hF
  have hFd : DifferentiableOn ℂ F {z : ℂ | 0 < z.re} := differentiableOn_nearLineWindowField N H τ
  have hsub : closure (Complex.HadamardThreeLines.verticalStrip σL σR) ⊆ {z : ℂ | 0 < z.re} := by
    rw [GaloisForLFunctions.HTGeometry.closure_verticalStrip hlu]
    intro z hz
    have : z.re ∈ Icc σL σR := hz
    show 0 < z.re
    linarith [this.1]
  have hdc : DiffContOnCl ℂ F (Complex.HadamardThreeLines.verticalStrip σL σR) :=
    (hFd.mono hsub).diffContOnCl
  have hM : ∀ z ∈ Complex.HadamardThreeLines.verticalClosedStrip σL σR,
      ‖F z‖ ≤ Real.exp 1 * (CW * N * ((1 + |τ|) * (1 + H))) + Real.exp 1 * 2 := by
    intro z hz
    have hzI : z.re ∈ Icc σL σR := hz
    have hA : 0 ≤ Real.exp 1 * (CW * N * ((1 + |τ|) * (1 + H))) := by positivity
    have hB : 0 ≤ Real.exp 1 * 2 := by positivity
    rcases le_total z.re 3 with h3 | h3
    · have h := norm_nearLineWindowField_le (τ := τ) hH3 hCW hW (by linarith [hzI.1]) h3
      linarith
    · have h := norm_nearLineWindowField_le_of_three_le hN (H := H) (τ := τ) h3
        (by linarith [hzI.2])
      have hpow : (N : ℝ) ^ (2 - z.re) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (by omega : 1 ≤ N))
          (by linarith)
      have h' : ‖F z‖ ≤ Real.exp 1 * 2 := by
        calc ‖F z‖ ≤ Real.exp 1 * (2 * (N : ℝ) ^ (2 - z.re)) := h
          _ ≤ Real.exp 1 * (2 * 1) := by gcongr
          _ = Real.exp 1 * 2 := by ring
      linarith
  have hSR : 0 < 8 * Real.exp 2 * H * (N : ℝ) ^ (4 - 2 * σR) := by
    have := Real.rpow_pos_of_pos hN0 (4 - 2 * σR)
    positivity
  have hright : ∀ y : ℝ, ∫ t in (τ - H)..(τ + H),
      ‖F ((σR : ℂ) + ((y + t : ℝ) : ℂ) * I)‖ ^ 2 ≤ 8 * Real.exp 2 * H * (N : ℝ) ^ (4 - 2 * σR) :=
    fun y => integral_nearLineWindowField_farRight_le hN hσR hH y
  have hthree := GaloisForLFunctions.HTGeometry.integral_normSq_le_of_three_lines
    (F := F) (l := σL) (u := σR) (σ := σ₀) (A := τ - H) (B := τ + H) hlu hσL₀ (by linarith)
    (by linarith) hdc hM hSL hSR hleft hright
  have hab : τ - H ≤ τ + H := by linarith
  have hpos : 0 < τ - H := by linarith
  have hint1 : IntervalIntegrable
      (fun t : ℝ => ‖hbMollifiedTail N ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2) volume (τ - H) (τ + H) :=
    (continuousOn_normSq_hbMollifiedTail_line N σ₀ hpos).intervalIntegrable_of_Icc hab
  have hint2 : IntervalIntegrable
      (fun t : ℝ => 2 * Real.exp 2 * ‖F ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2) volume (τ - H) (τ + H) :=
    (continuous_const.mul ((continuous_nearLineWindowField_line N H τ
      (by linarith : (0 : ℝ) < σ₀)).norm.pow 2)).intervalIntegrable _ _
  have hpt : ∀ t ∈ Icc (τ - H) (τ + H),
      ‖hbMollifiedTail N ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
        2 * Real.exp 2 * ‖F ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
    intro t ht
    refine normSq_hbMollifiedTail_le_window hH0 hσ₀ hσ₀' ?_ ?_
    · exact abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    · rw [abs_of_pos (by linarith [ht.1])]
      linarith [ht.1]
  calc ∫ t in (τ - H)..(τ + H), ‖hbMollifiedTail N ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2
      ≤ ∫ t in (τ - H)..(τ + H), 2 * Real.exp 2 * ‖F ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
        intervalIntegral.integral_mono_on hab hint1 hint2 hpt
    _ = 2 * Real.exp 2 * ∫ t in (τ - H)..(τ + H), ‖F ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
        intervalIntegral.integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hthree (by positivity)

end RHTower
