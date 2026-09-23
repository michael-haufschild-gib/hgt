import GaloisForLFunctions.RHTower.HardyZDyadicMean

/-!
# The mean of Hardy's `Z` over subwindows of a dyadic block

The two van der Corput regimes of the dyadic mean lemma — the second-derivative test below the
conductor and the first-derivative test above it — hold on every subinterval `[a, b]` of
`[T, 2T]`, because both phase hypotheses are pointwise on the ambient dyadic block.  The direct
edge of the smooth approximate functional equation therefore has mean `O(T^{3/4})` over every
subwindow, and the reflected edge and residue are pointwise exponentially small, so the full
Hardy `Z` has mean `O(T^{3/4})` over every subwindow of `[T, 2T]`.  This is the first-moment
input for window-level sign-change counting.
-/

open Set MeasureTheory Complex

namespace RHTower

noncomputable section

/-! ## The two oscillatory bounds on subwindows -/

theorem norm_integral_twist_second_le_window {T a b : ℝ} (hT : 4 ≤ T)
    (ha : T ≤ a) (hb : b ≤ 2 * T) (hab : a ≤ b) (L : ℝ) (c : ℂ) :
    ‖∫ τ in a..b, c * Complex.exp (Complex.I * (hardyTwistPhase L τ : ℂ))‖
      ≤ 64 * ‖c‖ * Real.sqrt (200 * T) := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hmu : (0 : ℝ) < 1 / (200 * T) := by positivity
  have hsub : Set.Icc a b ⊆ Set.Icc T (2 * T) := Set.Icc_subset_Icc ha hb
  have h := secondDerivTestOn (a := a) (b := b) (mu := 1 / (200 * T)) hab hmu
    (φ := hardyTwistPhase L) (φ' := fun τ => gammaHardyPhaseRate τ - L)
    (φ'' := deriv gammaHardyPhaseRate) (A := fun _ => c) (A' := fun _ => 0)
    (fun τ _ => hasDerivAt_hardyTwistPhase L τ)
    (fun τ _ => hasDerivAt_hardyTwistRate L τ)
    continuous_deriv_gammaHardyPhaseRate.continuousOn
    (fun τ _ => hasDerivAt_const τ c)
    continuousOn_const
    (fun τ hτ => curvature_lower_dyadic hT (hsub hτ))
  have hzero : (∫ _ : ℝ in a..b, ‖(0 : ℂ)‖) = 0 := by simp
  rw [hzero] at h
  have hsqrt : Real.sqrt (1 / (200 * T)) = (Real.sqrt (200 * T))⁻¹ := by
    rw [one_div, Real.sqrt_inv]
  rw [hsqrt] at h
  have hs0 : (0 : ℝ) < Real.sqrt (200 * T) := Real.sqrt_pos.mpr (by positivity)
  refine le_trans h (le_of_eq ?_)
  field_simp
  ring

theorem norm_integral_twist_first_le_window {T a b L : ℝ} (hT : 16 ≤ T)
    (ha : T ≤ a) (hb : b ≤ 2 * T) (hab : a ≤ b)
    (hL : Real.log (5 * Real.sqrt T) ≤ L) (c : ℂ) :
    ‖∫ τ in a..b, c * Complex.exp (Complex.I * (hardyTwistPhase L τ : ℂ))‖
      ≤ 8 * ‖c‖ := by
  have hT4 : (4 : ℝ) ≤ T := by linarith
  have hsub : Set.Icc a b ⊆ Set.Icc T (2 * T) := Set.Icc_subset_Icc ha hb
  have h := firstDerivTestOn (a := a) (b := b) (lam := 1) hab one_pos
    (φ := hardyTwistPhase L) (φ' := fun τ => gammaHardyPhaseRate τ - L)
    (φ'' := deriv gammaHardyPhaseRate) (A := fun _ => c) (A' := fun _ => 0)
    (fun τ _ => hasDerivAt_hardyTwistPhase L τ)
    (fun τ _ => hasDerivAt_hardyTwistRate L τ)
    continuous_deriv_gammaHardyPhaseRate.continuousOn
    (fun τ _ => hasDerivAt_const τ c)
    continuousOn_const
    (fun τ hτ => le_trans (by positivity) (curvature_lower_dyadic hT4 (hsub hτ)))
    (fun τ hτ => one_le_abs_rate_sub_above_conductor hT (hsub hτ) hL)
  have hzero : (∫ _ : ℝ in a..b, ‖(0 : ℂ)‖) = 0 := by simp
  rw [hzero] at h
  refine le_trans h (le_of_eq ?_)
  ring

/-! ## Per-term bounds on subwindows -/

theorem abs_integral_hardyDirectTerm_le_second_window {T a b : ℝ} (hT : 4 ≤ T)
    (ha : T ≤ a) (hb : b ≤ 2 * T) (hab : a ≤ b) (x : ℝ) (n : ℕ) :
    |∫ τ in a..b, hardyDirectTerm x n τ|
      ≤ 64 * Real.sqrt (200 * T) * cutoffWeight x n := by
  have hs : (0 : ℝ) ≤ (Real.sqrt ((n : ℝ) + 1))⁻¹ := by positivity
  rw [integral_hardyDirectTerm_eq, abs_mul, abs_of_nonneg hs]
  have hre := Complex.abs_re_le_norm (∫ τ in a..b,
    smoothAFECutoff (((n : ℝ) + 1) / x) *
      Complex.exp (Complex.I *
        ((hardyTwistPhase (Real.log ((n : ℝ) + 1)) τ : ℝ) : ℂ)))
  have hosc := norm_integral_twist_second_le_window hT ha hb hab
    (Real.log ((n : ℝ) + 1)) (smoothAFECutoff (((n : ℝ) + 1) / x))
  have hchain := le_trans hre hosc
  calc (Real.sqrt ((n : ℝ) + 1))⁻¹ * |(∫ τ in a..b,
        smoothAFECutoff (((n : ℝ) + 1) / x) *
          Complex.exp (Complex.I *
            ((hardyTwistPhase (Real.log ((n : ℝ) + 1)) τ : ℝ) : ℂ))).re|
      ≤ (Real.sqrt ((n : ℝ) + 1))⁻¹ *
          (64 * ‖smoothAFECutoff (((n : ℝ) + 1) / x)‖ * Real.sqrt (200 * T)) :=
        mul_le_mul_of_nonneg_left hchain hs
    _ = 64 * Real.sqrt (200 * T) * cutoffWeight x n := by
        unfold cutoffWeight; ring

theorem abs_integral_hardyDirectTerm_le_first_window {T a b : ℝ} (hT : 16 ≤ T)
    (ha : T ≤ a) (hb : b ≤ 2 * T) (hab : a ≤ b) (x : ℝ) (n : ℕ)
    (hn : Real.log (5 * Real.sqrt T) ≤ Real.log ((n : ℝ) + 1)) :
    |∫ τ in a..b, hardyDirectTerm x n τ| ≤ 8 * cutoffWeight x n := by
  have hs : (0 : ℝ) ≤ (Real.sqrt ((n : ℝ) + 1))⁻¹ := by positivity
  rw [integral_hardyDirectTerm_eq, abs_mul, abs_of_nonneg hs]
  have hre := Complex.abs_re_le_norm (∫ τ in a..b,
    smoothAFECutoff (((n : ℝ) + 1) / x) *
      Complex.exp (Complex.I *
        ((hardyTwistPhase (Real.log ((n : ℝ) + 1)) τ : ℝ) : ℂ)))
  have hosc := norm_integral_twist_first_le_window hT ha hb hab hn
    (smoothAFECutoff (((n : ℝ) + 1) / x))
  have hchain := le_trans hre hosc
  calc (Real.sqrt ((n : ℝ) + 1))⁻¹ * |(∫ τ in a..b,
        smoothAFECutoff (((n : ℝ) + 1) / x) *
          Complex.exp (Complex.I *
            ((hardyTwistPhase (Real.log ((n : ℝ) + 1)) τ : ℝ) : ℂ))).re|
      ≤ (Real.sqrt ((n : ℝ) + 1))⁻¹ *
          (8 * ‖smoothAFECutoff (((n : ℝ) + 1) / x)‖) :=
        mul_le_mul_of_nonneg_left hchain hs
    _ = 8 * cutoffWeight x n := by
        unfold cutoffWeight; ring

/-! ## The direct edge over a subwindow -/

theorem setIntegral_norm_hardyDirectTerm_le_window {a b : ℝ} (hab : a ≤ b) (x : ℝ) (n : ℕ) :
    (∫ τ in Ioc a b, ‖hardyDirectTerm x n τ‖) ≤ cutoffWeight x n * (b - a) := by
  have hb : (∫ τ in Ioc a b, ‖hardyDirectTerm x n τ‖)
      ≤ ∫ _ in Ioc a b, cutoffWeight x n := by
    refine setIntegral_mono_on
      ((continuous_hardyDirectTerm x n).integrableOn_Ioc.norm)
      (continuous_const.integrableOn_Ioc) measurableSet_Ioc (fun τ _ => ?_)
    rw [Real.norm_eq_abs]
    exact abs_hardyDirectTerm_le x n τ
  rw [setIntegral_const, Real.volume_real_Ioc_of_le hab, smul_eq_mul] at hb
  calc (∫ τ in Ioc a b, ‖hardyDirectTerm x n τ‖)
      ≤ (b - a) * cutoffWeight x n := hb
    _ = cutoffWeight x n * (b - a) := by ring

theorem integral_hardyDirectSeries_eq_window {a b : ℝ} (hab : a ≤ b) {x : ℝ} (hx : 1 ≤ x) :
    ∫ τ in a..b, (∑' n : ℕ, hardyDirectTerm x n τ)
      = ∑' n : ℕ, ∫ τ in a..b, hardyDirectTerm x n τ := by
  obtain ⟨C, hC, hmain⟩ := exists_summable_tsum_cutoffWeight_le
  obtain ⟨hsumm, hle⟩ := hmain hx
  have hint : ∀ n : ℕ, Integrable (hardyDirectTerm x n) (volume.restrict (Ioc a b)) :=
    fun n => (continuous_hardyDirectTerm x n).integrableOn_Ioc
  have hnorm : Summable (fun n : ℕ =>
      ∫ τ in Ioc a b, ‖hardyDirectTerm x n τ‖) := by
    refine Summable.of_nonneg_of_le
      (fun n => integral_nonneg fun _ => norm_nonneg _)
      (fun n => setIntegral_norm_hardyDirectTerm_le_window hab x n)
      (hsumm.mul_right (b - a))
  have hs := hasSum_integral_of_summable_integral_norm
    (μ := volume.restrict (Ioc a b)) hint hnorm
  rw [intervalIntegral.integral_of_le hab]
  simp_rw [intervalIntegral.integral_of_le hab]
  exact hs.tsum_eq.symm

theorem exists_abs_integral_hardyDirectSeries_le_window :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {T a b x : ℝ}, 16 ≤ T → T ≤ a → a ≤ b → b ≤ 2 * T → 1 ≤ x →
      |∫ τ in a..b, (∑' n : ℕ, hardyDirectTerm x n τ)|
        ≤ C * (Real.sqrt T * Real.sqrt (Real.sqrt T) + Real.sqrt x) := by
  obtain ⟨Ct, hCt, hmain⟩ := exists_summable_tsum_cutoffWeight_le
  obtain ⟨Ch, hCh, hhead⟩ := exists_sum_range_cutoffWeight_le
  refine ⟨max (64 * Ch * Real.sqrt 200 * Real.sqrt 6) (8 * Ct), ?_, ?_⟩
  · exact le_trans (by positivity) (le_max_right _ _)
  intro T a b x hT ha hab hb hx
  have hT0 : (0 : ℝ) < T := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  obtain ⟨hsumm, hle⟩ := hmain hx
  set M : ℕ := ⌈5 * Real.sqrt T⌉₊ with hMdef
  have hsT : Real.sqrt T ≥ 4 := by
    rw [show (4 : ℝ) = Real.sqrt 16 by
      rw [show (16 : ℝ) = 4 ^ (2 : ℕ) by norm_num, Real.sqrt_sq]; norm_num]
    exact Real.sqrt_le_sqrt hT
  have hMge : 5 * Real.sqrt T ≤ (M : ℝ) := Nat.le_ceil _
  have hMlt : (M : ℝ) < 5 * Real.sqrt T + 1 := Nat.ceil_lt_add_one (by positivity)
  have hMle : (M : ℝ) ≤ 6 * Real.sqrt T := by linarith
  have hsecond : ∀ n : ℕ, |∫ τ in a..b, hardyDirectTerm x n τ|
      ≤ 64 * Real.sqrt (200 * T) * cutoffWeight x n :=
    fun n => abs_integral_hardyDirectTerm_le_second_window (by linarith) ha hb hab x n
  have hfirst : ∀ n : ℕ, |∫ τ in a..b, hardyDirectTerm x (n + M) τ|
      ≤ 8 * cutoffWeight x (n + M) := by
    intro n
    refine abs_integral_hardyDirectTerm_le_first_window hT ha hb hab x (n + M) ?_
    refine Real.log_le_log (by positivity) ?_
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have : ((n + M : ℕ) : ℝ) + 1 = (n : ℝ) + (M : ℝ) + 1 := by push_cast; ring
    rw [this]
    linarith
  have habs : Summable (fun n : ℕ => |∫ τ in a..b, hardyDirectTerm x n τ|) := by
    refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) hsecond ?_
    exact hsumm.mul_left (64 * Real.sqrt (200 * T))
  have hshift : Summable (fun n : ℕ => |∫ τ in a..b, hardyDirectTerm x (n + M) τ|) :=
    (summable_nat_add_iff M).mpr habs
  have hsplit := habs.sum_add_tsum_nat_add M
  have hheadbd : ∑ n ∈ Finset.range M, |∫ τ in a..b, hardyDirectTerm x n τ|
      ≤ 64 * Real.sqrt (200 * T) * (Ch * Real.sqrt (M : ℝ)) := by
    refine le_trans (Finset.sum_le_sum (fun n _ => hsecond n)) ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hhead hx0 M) (by positivity)
  have htailbd : ∑' n : ℕ, |∫ τ in a..b, hardyDirectTerm x (n + M) τ|
      ≤ 8 * (Ct * Real.sqrt x) := by
    refine le_trans (hshift.tsum_le_tsum hfirst
      (((summable_nat_add_iff M).mpr hsumm).mul_left 8)) ?_
    rw [tsum_mul_left]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    exact le_trans (tsum_cutoffWeight_shift_le hx M) hle
  have hsq200 : Real.sqrt (200 * T) = Real.sqrt 200 * Real.sqrt T :=
    Real.sqrt_mul (by norm_num) T
  have hsqM : Real.sqrt (M : ℝ) ≤ Real.sqrt 6 * Real.sqrt (Real.sqrt T) := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 6)]
    exact Real.sqrt_le_sqrt hMle
  have hstep1 : 64 * Real.sqrt (200 * T) * (Ch * Real.sqrt (M : ℝ))
      ≤ 64 * Ch * Real.sqrt 200 * Real.sqrt 6 * (Real.sqrt T * Real.sqrt (Real.sqrt T)) := by
    rw [hsq200]
    have hbase : (0 : ℝ) ≤ 64 * (Real.sqrt 200 * Real.sqrt T) := by positivity
    have hinner : Ch * Real.sqrt (M : ℝ) ≤ Ch * (Real.sqrt 6 * Real.sqrt (Real.sqrt T)) :=
      mul_le_mul_of_nonneg_left hsqM hCh
    calc 64 * (Real.sqrt 200 * Real.sqrt T) * (Ch * Real.sqrt (M : ℝ))
        ≤ 64 * (Real.sqrt 200 * Real.sqrt T) *
            (Ch * (Real.sqrt 6 * Real.sqrt (Real.sqrt T))) :=
          mul_le_mul_of_nonneg_left hinner hbase
      _ = 64 * Ch * Real.sqrt 200 * Real.sqrt 6 *
            (Real.sqrt T * Real.sqrt (Real.sqrt T)) := by ring
  have hfinal : |∫ τ in a..b, (∑' n : ℕ, hardyDirectTerm x n τ)|
      ≤ ∑' n : ℕ, |∫ τ in a..b, hardyDirectTerm x n τ| := by
    rw [integral_hardyDirectSeries_eq_window hab hx]
    have := norm_tsum_le_tsum_norm (f := fun n : ℕ => ∫ τ in a..b, hardyDirectTerm x n τ)
      (by simpa [Real.norm_eq_abs] using habs)
    simpa [Real.norm_eq_abs] using this
  have hAnn : (0 : ℝ) ≤ Real.sqrt T * Real.sqrt (Real.sqrt T) := by positivity
  have hBnn : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  have h1 : 64 * Ch * Real.sqrt 200 * Real.sqrt 6
      ≤ max (64 * Ch * Real.sqrt 200 * Real.sqrt 6) (8 * Ct) := le_max_left _ _
  have h2 : 8 * Ct ≤ max (64 * Ch * Real.sqrt 200 * Real.sqrt 6) (8 * Ct) := le_max_right _ _
  calc |∫ τ in a..b, (∑' n : ℕ, hardyDirectTerm x n τ)|
      ≤ ∑' n : ℕ, |∫ τ in a..b, hardyDirectTerm x n τ| := hfinal
    _ = ∑ n ∈ Finset.range M, |∫ τ in a..b, hardyDirectTerm x n τ|
          + ∑' n : ℕ, |∫ τ in a..b, hardyDirectTerm x (n + M) τ| := hsplit.symm
    _ ≤ 64 * Ch * Real.sqrt 200 * Real.sqrt 6 * (Real.sqrt T * Real.sqrt (Real.sqrt T))
          + 8 * Ct * Real.sqrt x := by
        have := htailbd
        nlinarith [hheadbd, hstep1]
    _ ≤ max (64 * Ch * Real.sqrt 200 * Real.sqrt 6) (8 * Ct) *
          (Real.sqrt T * Real.sqrt (Real.sqrt T) + Real.sqrt x) := by
        nlinarith [h1, h2, hAnn, hBnn]

/-! ## The window mean of Hardy's `Z` -/

/-- **The mean of Hardy's `Z` over every subwindow of a dyadic block is `O(T^{3/4})`.** -/
theorem exists_abs_integral_hardyZ_window_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {T a b : ℝ}, 16 ≤ T → T ≤ a → a ≤ b → b ≤ 2 * T →
      |∫ τ in a..b, hardyZ τ| ≤ C * (Real.sqrt T * Real.sqrt (Real.sqrt T)) := by
  obtain ⟨CD, hCD, hdirect⟩ := exists_abs_integral_hardyDirectSeries_le_window
  obtain ⟨K, hK, htail⟩ := exists_abs_hardyZ_sub_direct_le
  refine ⟨2 * CD + 9 * K + 2, by positivity, fun {T a b} hT ha hab hb => ?_⟩
  have hT0 : (0 : ℝ) < T := by linarith
  set s : ℝ := Real.sqrt T with hs
  have hs2 : s * s = T := Real.mul_self_sqrt hT0.le
  have hs4 : (4 : ℝ) ≤ s := by
    rw [hs, show (4 : ℝ) = Real.sqrt 16 by
      rw [show (16 : ℝ) = 4 ^ (2 : ℕ) by norm_num, Real.sqrt_sq]; norm_num]
    exact Real.sqrt_le_sqrt hT
  have hs0 : (0 : ℝ) < s := by linarith
  set x : ℝ := T * s with hx
  have hx1 : (1 : ℝ) ≤ x := by nlinarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hsqx : Real.sqrt x = s * Real.sqrt s := by
    rw [hx, Real.sqrt_mul hT0.le, ← hs]
  have hss : Real.sqrt s ≤ s := by
    nlinarith [Real.sq_sqrt hs0.le, Real.sqrt_nonneg s, sq_nonneg (Real.sqrt s - 1)]
  have hsqs1 : (1 : ℝ) ≤ Real.sqrt s := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith)
  clear_value s x
  have hZint : IntervalIntegrable hardyZ volume a b :=
    continuous_hardyZ.intervalIntegrable _ _
  have hDint : IntervalIntegrable (fun τ : ℝ => ∑' n : ℕ, hardyDirectTerm x n τ)
      volume a b := (continuous_hardyDirectSeries hx1).intervalIntegrable _ _
  have hdecomp : (∫ τ in a..b, hardyZ τ)
      = (∫ τ in a..b, (∑' n : ℕ, hardyDirectTerm x n τ))
        + ∫ τ in a..b, (hardyZ τ - ∑' n : ℕ, hardyDirectTerm x n τ) := by
    rw [intervalIntegral.integral_sub hZint hDint]
    ring
  have hconst : ∀ τ ∈ Set.uIoc a b,
      ‖hardyZ τ - ∑' n : ℕ, hardyDirectTerm x n τ‖
        ≤ 9 * K / s + Real.sqrt x * Real.exp (1 / 4) * Real.exp (-(T ^ (2 : ℕ))) := by
    intro τ hτ
    rw [Set.uIoc_of_le hab] at hτ
    have hτ1 : (1 : ℝ) ≤ τ := by linarith [hτ.1]
    have hτ2T : τ ≤ 2 * T := le_trans hτ.2 hb
    have hτT : T ≤ τ := le_trans ha hτ.1.le
    have hbnd := htail hx0 hτ1
    rw [Real.norm_eq_abs]
    refine le_trans hbnd (add_le_add ?_ ?_)
    · have hnum : 3 * K * (1 + τ) ≤ 9 * K * T := by nlinarith [hK]
      rw [div_le_div_iff₀ hx0 hs0]
      nlinarith [hK, hs0.le]
    · have hexp : Real.exp (-(τ ^ (2 : ℕ))) ≤ Real.exp (-(T ^ (2 : ℕ))) := by
        refine Real.exp_le_exp.mpr ?_
        nlinarith
      have hcoef : (0 : ℝ) ≤ Real.sqrt x * Real.exp (1 / 4) := by positivity
      exact mul_le_mul_of_nonneg_left hexp hcoef
  have htailint := intervalIntegral.norm_integral_le_of_norm_le_const hconst
  have habsba : |b - a| ≤ T := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have htailT : ‖∫ τ in a..b, (hardyZ τ - ∑' n : ℕ, hardyDirectTerm x n τ)‖
      ≤ (9 * K / s + Real.sqrt x * Real.exp (1 / 4) * Real.exp (-(T ^ (2 : ℕ)))) * T := by
    refine le_trans htailint ?_
    have hcnn : (0 : ℝ) ≤ 9 * K / s + Real.sqrt x * Real.exp (1 / 4) * Real.exp (-(T ^ (2 : ℕ))) := by
      positivity
    exact mul_le_mul_of_nonneg_left habsba hcnn
  have hexpbd : Real.sqrt x * Real.exp (1 / 4) * Real.exp (-(T ^ (2 : ℕ))) * T ≤ 2 := by
    have h1 : Real.sqrt x ≤ T := by
      rw [hsqx]; nlinarith
    have h2 : Real.exp (1 / 4) ≤ 2 := by
      have hlog : Real.exp (1 / 4) ≤ Real.exp (Real.log 2) :=
        Real.exp_le_exp.mpr (by linarith [Real.log_two_gt_d9])
      rwa [Real.exp_log (by norm_num)] at hlog
    have h3 : T ^ (2 : ℕ) * Real.exp (-(T ^ (2 : ℕ))) ≤ 1 := by
      have hle : T ^ (2 : ℕ) ≤ Real.exp (T ^ (2 : ℕ)) := by
        have := Real.add_one_le_exp (T ^ (2 : ℕ))
        linarith
      have hpos : (0 : ℝ) < Real.exp (T ^ (2 : ℕ)) := Real.exp_pos _
      rw [Real.exp_neg, mul_inv_le_iff₀ hpos]
      linarith
    have hexppos : (0 : ℝ) < Real.exp (-(T ^ (2 : ℕ))) := Real.exp_pos _
    have hstep : Real.sqrt x * Real.exp (1 / 4) ≤ T * 2 := by
      nlinarith [Real.sqrt_nonneg x, Real.exp_pos (1 / 4 : ℝ), hT0.le]
    calc Real.sqrt x * Real.exp (1 / 4) * Real.exp (-(T ^ (2 : ℕ))) * T
        ≤ T * 2 * Real.exp (-(T ^ (2 : ℕ))) * T :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hstep hexppos.le) hT0.le
      _ = 2 * (T ^ (2 : ℕ) * Real.exp (-(T ^ (2 : ℕ)))) := by ring
      _ ≤ 2 * 1 := by nlinarith
      _ = 2 := by ring
  have hdirbd := hdirect hT ha hab hb hx1
  rw [← hs, hsqx] at hdirbd
  have hKsT : 9 * K / s * T = 9 * K * s := by
    field_simp
    nlinarith [hs2]
  have hsplitbd : |∫ τ in a..b, hardyZ τ|
      ≤ CD * (s * Real.sqrt s + s * Real.sqrt s)
        + (9 * K / s + Real.sqrt x * Real.exp (1 / 4) * Real.exp (-(T ^ (2 : ℕ)))) * T := by
    rw [hdecomp]
    refine le_trans (abs_add_le _ _) ?_
    have h1 : |∫ τ in a..b, (hardyZ τ - ∑' n : ℕ, hardyDirectTerm x n τ)|
        ≤ (9 * K / s + Real.sqrt x * Real.exp (1 / 4) * Real.exp (-(T ^ (2 : ℕ)))) * T := by
      rw [← Real.norm_eq_abs]
      exact htailT
    linarith [hdirbd]
  have hsss : (1 : ℝ) * s ≤ s * Real.sqrt s := by
    have h1 : s * 1 ≤ s * Real.sqrt s := mul_le_mul_of_nonneg_left hsqs1 hs0.le
    linarith only [h1]
  calc |∫ τ in a..b, hardyZ τ|
      ≤ CD * (s * Real.sqrt s + s * Real.sqrt s)
        + (9 * K / s + Real.sqrt x * Real.exp (1 / 4) * Real.exp (-(T ^ (2 : ℕ)))) * T := hsplitbd
    _ = 2 * CD * (s * Real.sqrt s) + 9 * K / s * T
        + Real.sqrt x * Real.exp (1 / 4) * Real.exp (-(T ^ (2 : ℕ))) * T := by ring
    _ ≤ 2 * CD * (s * Real.sqrt s) + 9 * K * s + 2 := by
        rw [hKsT]
        linarith [hexpbd]
    _ ≤ 2 * CD * (s * Real.sqrt s) + 9 * K * (s * Real.sqrt s)
          + 2 * (s * Real.sqrt s) := by
        have hs_le : s ≤ s * Real.sqrt s := by
          have h1 : s * 1 ≤ s * Real.sqrt s :=
            mul_le_mul_of_nonneg_left hsqs1 hs0.le
          rwa [mul_one] at h1
        have h9 : 9 * K * s ≤ 9 * K * (s * Real.sqrt s) :=
          mul_le_mul_of_nonneg_left hs_le (by linarith only [hK])
        have h2' : (2 : ℝ) ≤ 2 * (s * Real.sqrt s) := by
          have h1 : (1 : ℝ) ≤ s * Real.sqrt s := by
            have h2 : (1 : ℝ) * 1 ≤ s * Real.sqrt s :=
              mul_le_mul (by linarith only [hs4]) hsqs1 (by norm_num) hs0.le
            linarith only [h2]
          linarith only [h1]
        linarith
    _ = (2 * CD + 9 * K + 2) * (s * Real.sqrt s) := by ring

end

end RHTower
