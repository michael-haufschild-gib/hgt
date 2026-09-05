/-
# The outer law for `ζΨ_M` is equivalent to `(L)`

With the small-values estimate (`exists_line_smallValues_bound`) the torus law for the linear
mollifier becomes two-sided, and the outer decomposition law closes into an equivalence:

  `(L)`  ⟺  for every `ε ∈ (0,1)` and `η > 0`, eventually
            `(1/T)∫_T^{2T} log|ζΨ_M(1/2+it)| dt ≤ J_M(ε) + η`,

where `(L)` is `(1/T)∫_T^{2T} log|ζ(1/2+it)| dt → 0` (the fixed-scale zero-density law
`∑_{β>1/2}(β−1/2) = o(T)` by Littlewood) and `J_M(ε) = linearMollifierTorusLogMean M ε` is the
mollifier's truncated torus Jensen mass. Under `(L)` the mollified log-mean is squeezed between
`J_M(ε) − D_M/log(1/ε) − η` and `J_M(ε) + η`.
-/
import GaloisForLFunctions.RHTower.OuterDecompositionLawMollifiedProduct
import GaloisForLFunctions.RHTower.DirichletPolynomialLineSmallValues

open MeasureTheory intervalIntegral Filter Topology Complex Finset Set
open scoped Classical

namespace RHTower

open SteinhausModel

noncomputable section

/-! ## The ζ floor at every height -/

/-- The heights of zeros of `ζ` in the strip `[1/2, 15/2] × [20, ∞)` form a countable set. -/
theorem countable_zetaZeroHeights :
    Set.Countable {T : ℝ | 20 ≤ T ∧ ∃ x ∈ Set.Icc (1 / 2 : ℝ) (15 / 2 : ℝ),
      riemannZeta ((x : ℂ) + (T : ℂ) * I) = 0} := by
  have hZ : ∀ n : ℕ, ∃ Z : Finset ℂ, ∀ z : ℂ, z ∈ Z ↔
      z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc (20 : ℝ) (21 + n)) ∧ riemannZeta z = 0 :=
    fun n => exists_zetaRectangleZeros_finset le_rfl (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])
  choose Z hZ using hZ
  have hsub : {T : ℝ | 20 ≤ T ∧ ∃ x ∈ Set.Icc (1 / 2 : ℝ) (15 / 2 : ℝ),
      riemannZeta ((x : ℂ) + (T : ℂ) * I) = 0} ⊆ ⋃ n : ℕ, Complex.im '' ((Z n : Finset ℂ) : Set ℂ) := by
    intro T hT
    obtain ⟨h20, x, hx, hzero⟩ := hT
    obtain ⟨n, hn⟩ := exists_nat_ge (T - 20)
    rw [Set.mem_iUnion]
    refine ⟨n, (x : ℂ) + (T : ℂ) * I, ?_, by simp⟩
    rw [Finset.mem_coe, hZ n]
    refine ⟨Complex.mem_reProdIm.mpr ⟨?_, ?_⟩, hzero⟩
    · have h : ((x : ℂ) + (T : ℂ) * I).re = x := by simp
      rw [h, Set.uIcc_of_le (by norm_num)]; exact hx
    · have h : ((x : ℂ) + (T : ℂ) * I).im = T := by simp
      rw [h, Set.uIcc_of_le (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])]
      exact ⟨h20, by linarith⟩
  refine Set.Countable.mono hsub ?_
  exact Set.countable_iUnion fun n => (Z n).countable_toSet.image _

/-- **Littlewood's floor for `ζ` at every height `T ≥ 20`** (density of the admissible heights and
continuity of both sides). -/
theorem exists_zetaLine_logMean_floor_all_heights :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ T : ℝ, 20 ≤ T →
      -(C + K * Real.log (2 * T)) ≤
        ∫ t in T..(2 * T), Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ := by
  obtain ⟨C, K, hC, hK, hfloor⟩ := exists_zetaLine_logMean_floor
  refine ⟨C, K, hC, hK, ?_⟩
  set H := {T : ℝ | 20 ≤ T ∧ ∃ x ∈ Set.Icc (1 / 2 : ℝ) (15 / 2 : ℝ),
    riemannZeta ((x : ℂ) + (T : ℂ) * I) = 0} with hH
  set B : Set ℝ := H ∪ (fun x : ℝ => x / 2) '' H with hB
  have hBc : B.Countable := countable_zetaZeroHeights.union (countable_zetaZeroHeights.image _)
  have hdense : Dense Bᶜ := hBc.dense_compl ℝ
  set s : Set ℝ := Set.Ioi 20 ∩ Bᶜ with hs
  have hclos : Set.Ici (20 : ℝ) ⊆ closure s := by
    have h1 : Set.Ioi (20 : ℝ) ⊆ closure s := hdense.open_subset_closure_inter isOpen_Ioi
    have h2 : closure (Set.Ioi (20 : ℝ)) ⊆ closure s := closure_minimal h1 isClosed_closure
    rw [closure_Ioi] at h2
    exact h2
  have hsIci : closure s ⊆ Set.Ici 20 := by
    apply closure_minimal _ isClosed_Ici
    intro T hT
    exact (Set.mem_Ioi.mp hT.1).le
  set f : ℝ → ℝ := fun T => -(C + K * Real.log (2 * T)) with hf
  set g : ℝ → ℝ := fun T => ∫ t in T..(2 * T),
    Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ with hg
  have hfg : ∀ T ∈ s, f T ≤ g T := by
    intro T hT
    obtain ⟨hT20, hTB⟩ := hT
    have hT20' : (20 : ℝ) < T := hT20
    have hnotH : T ∉ H := fun h => hTB (Or.inl h)
    have hnotH2 : 2 * T ∉ H := by
      intro h
      apply hTB
      right
      exact ⟨2 * T, h, by ring⟩
    have hG1 : ∀ x ∈ Set.Icc (1 / 2 : ℝ) (15 / 2 : ℝ), riemannZeta ((x : ℂ) + (T : ℂ) * I) ≠ 0 := by
      intro x hx h0
      exact hnotH ⟨hT20'.le, x, hx, h0⟩
    have hG2 : ∀ x ∈ Set.Icc (1 / 2 : ℝ) (15 / 2 : ℝ),
        riemannZeta ((x : ℂ) + ((2 * T : ℝ) : ℂ) * I) ≠ 0 := by
      intro x hx h0
      exact hnotH2 ⟨by linarith, x, hx, h0⟩
    have := hfloor T (2 * T) hT20'.le (by linarith) hG1 hG2
    simpa [hf, hg] using this
  have hfc : ContinuousOn f (closure s) := by
    apply ContinuousOn.mono _ hsIci
    rw [hf]
    apply ContinuousOn.neg
    apply ContinuousOn.add continuousOn_const
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.log (continuousOn_const.mul continuousOn_id)
    intro T hT
    have : (20 : ℝ) ≤ T := hT
    simp; linarith
  have hgc : ContinuousOn g (closure s) := by
    apply Continuous.continuousOn
    have hprim : Continuous fun x : ℝ => ∫ t in (0 : ℝ)..x,
        Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ :=
      intervalIntegral.continuous_primitive (fun a b => intervalIntegrable_log_norm_riemannZeta_line a b) 0
    have heq : g = fun T => (∫ t in (0 : ℝ)..(2 * T),
        Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) -
        ∫ t in (0 : ℝ)..T, Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ := by
      funext T
      rw [hg]
      simp only
      rw [intervalIntegral.integral_interval_sub_left (intervalIntegrable_log_norm_riemannZeta_line _ _)
        (intervalIntegrable_log_norm_riemannZeta_line _ _)]
    rw [heq]
    exact (hprim.comp (continuous_const.mul continuous_id)).sub hprim
  intro T hT
  exact le_on_closure hfg hfc hgc (hclos hT)


/-! ## The lower torus law for the linear mollifier -/

/-- `½ log max(x², ε²) = max (log x) (log ε)` for `x, ε > 0`. -/
theorem logMaxHalf_sq_eq_max {ε x : ℝ} (hε : 0 < ε) (hx : 0 < x) :
    logMaxHalf ε (x ^ 2) = max (Real.log x) (Real.log ε) := by
  unfold logMaxHalf
  have hsq : max (x ^ 2) (ε ^ 2) = (max x ε) ^ 2 := by
    rcases le_total x ε with h | h
    · rw [max_eq_right h, max_eq_right (pow_le_pow_left₀ hx.le h 2)]
    · rw [max_eq_left h, max_eq_left (pow_le_pow_left₀ hε.le h 2)]
  rw [hsq, Real.log_pow]
  have hmax : Real.log (max x ε) = max (Real.log x) (Real.log ε) := by
    rcases le_total x ε with h | h
    · rw [max_eq_right h, max_eq_right (Real.log_le_log hx h)]
    · rw [max_eq_left h, max_eq_left (Real.log_le_log hε h)]
  rw [hmax]
  push_cast
  ring

theorem max_sub_max_sub_eq {L a : ℝ} : max L a - max (a - L) 0 = L := by
  rcases le_total a L with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring

/-- **Lower torus law for the linear mollifier.**  Eventually
`(1/T)∫_T^{2T} log ‖Ψ_M(1/2+it)‖ ≥ J_M(ε) − η − D_M / log(1/ε)`. -/
theorem exists_eventually_window_logMean_linearMollifier_ge (M : ℕ) (hM : 1 < M) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ η : ℝ, 0 < η →
      ∀ᶠ T in atTop,
        linearMollifierTorusLogMean M ε - η - D / Real.log (1 / ε) ≤
          T⁻¹ * ∫ t in T..(2 * T), Real.log ‖edPoly (levinsonShiftedLinearMollifierCoeff M (1 / 2))
            (Finset.Icc 1 M) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ := by
  set s : Finset ℕ := Finset.Icc 1 M with hsdef
  have hs : ∀ n ∈ s, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  have h1 : 1 ∈ s := Finset.mem_Icc.mpr ⟨le_rfl, hM.le⟩
  set b := levinsonShiftedLinearMollifierCoeff M (1 / 2) with hb
  have hb1 : b 1 = 1 := levinsonShiftedLinearMollifierCoeff_one hM _
  have hbn : ∀ n ∈ s, ‖b n‖ ≤ 1 :=
    fun n hn => norm_levinsonShiftedLinearMollifierCoeff_le_one hM (hs n hn) le_rfl
  have hne : ∃ z : ℂ, edPoly b s z ≠ 0 := by
    refine ⟨(7 : ℂ), fun h0 => ?_⟩
    have h := norm_edPoly_sub_one_le_half_of_six_le b hs h1 hb1 hbn (z := (7 : ℂ)) (by simp; norm_num)
    rw [h0] at h
    have : ‖(0 : ℂ) - 1‖ = 1 := by simp
    rw [this] at h
    norm_num at h
  obtain ⟨C₁, C₂, hC₁, hC₂, hsmall⟩ := exists_line_smallValues_bound b hM.le hb1 hbn
  refine ⟨C₁ + 4 * C₂, by positivity, ?_⟩
  intro ε hε hε1 η hη
  set lam : ℝ := Real.log (1 / ε) with hlam
  have hlampos : 0 < lam := Real.log_pos (by rw [lt_div_iff₀ hε]; linarith)
  set a : ℕ → ℝ := linearMollifierLineCoeff M with ha
  have hline : ∀ t : ℝ, edPoly b s (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) = dpoly a s t := by
    intro t
    rw [hb, hsdef, edPoly_levinsonShiftedLinearMollifierCoeff_line M (1 / 2) t,
      levinsonLinearMollifier_eq_dpoly]
  have hlim := tendsto_contMoment_window_steinhaus a s hs (logMaxHalf ε) (continuous_logMaxHalf hε)
  have hev := (Metric.tendsto_atTop.mp hlim) η hη
  obtain ⟨T₀, hT₀⟩ := hev
  filter_upwards [eventually_ge_atTop T₀, eventually_ge_atTop (20 : ℝ)] with T hT h20
  have hTpos : 0 < T := by linarith
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have hclose := hT₀ T hT
  rw [Real.dist_eq, abs_lt] at hclose
  -- the decomposition of log ‖Ψ‖ off the zeros
  set φ : ℝ → ℝ := fun t => max (Real.log ε -
    Real.log ‖edPoly b s (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) 0 with hφ
  have hΨan : AnalyticOnNhd ℂ (edPoly b s) Set.univ := analyticOnNhd_edPoly b hs
  have hφint : IntervalIntegrable φ MeasureTheory.volume T (2 * T) := by
    have hf : IntervalIntegrable (fun t : ℝ => Real.log ε -
        Real.log ‖edPoly b s (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) MeasureTheory.volume T (2 * T) :=
      intervalIntegrable_const.sub (intervalIntegrable_log_norm_vertical_of_entire hΨan (1 / 2) T (2 * T))
    rw [intervalIntegrable_iff] at hf ⊢
    exact hf.pos_part
  have hcontD : Continuous (dpoly a s) := by
    unfold dpoly cterm
    exact continuous_finset_sum _ fun n _ => by fun_prop
  have hcφ : Continuous (fun t : ℝ => logMaxHalf ε (‖dpoly a s t‖ ^ 2)) :=
    (continuous_logMaxHalf hε).comp (by fun_prop)
  have hdecomp : (∫ t in T..(2 * T), Real.log ‖edPoly b s (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖)
      = (∫ t in T..(2 * T), logMaxHalf ε (‖dpoly a s t‖ ^ 2)) - ∫ t in T..(2 * T), φ t := by
    rw [← intervalIntegral.integral_sub (hcφ.intervalIntegrable _ _) hφint]
    apply intervalIntegral.integral_congr_ae
    have hfin := finite_edPolyLine_zeros b hs hne T (2 * T)
    have hnull := hfin.measure_zero MeasureTheory.volume
    rw [MeasureTheory.measure_eq_zero_iff_ae_notMem] at hnull
    filter_upwards [hnull] with t ht hmem
    have hIcc : t ∈ Set.Icc T (2 * T) := by
      rw [Set.uIoc_of_le (by linarith)] at hmem
      exact ⟨hmem.1.le, hmem.2⟩
    have hne0 : edPoly b s (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 := fun h0 => ht ⟨hIcc, h0⟩
    have hpos : 0 < ‖edPoly b s (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ := norm_pos_iff.mpr hne0
    simp only [hφ]
    rw [← hline t, logMaxHalf_sq_eq_max hε hpos, max_sub_max_sub_eq]
  have hsm := hsmall T (2 * T) (by linarith) ε hε hε1
  have hsm' : (∫ t in T..(2 * T), φ t) ≤ (C₁ + 4 * C₂) * T / lam := by
    refine hsm.trans ?_
    rw [div_le_div_iff_of_pos_right hlampos]
    rw [abs_of_pos hTpos, abs_of_pos (by linarith : (0 : ℝ) < 2 * T)]
    nlinarith [hC₂, hT1]
  rw [hdecomp, mul_sub]
  have hJ : linearMollifierTorusLogMean M ε - η ≤
      T⁻¹ * ∫ t in T..(2 * T), logMaxHalf ε (‖dpoly a s t‖ ^ 2) := by
    unfold linearMollifierTorusLogMean
    linarith [hclose.1]
  have hφ' : T⁻¹ * ∫ t in T..(2 * T), φ t ≤ (C₁ + 4 * C₂) / lam := by
    calc T⁻¹ * ∫ t in T..(2 * T), φ t ≤ T⁻¹ * ((C₁ + 4 * C₂) * T / lam) := by
          gcongr
      _ = (C₁ + 4 * C₂) / lam := by field_simp
  linarith

/-! ## The equivalence -/

/-- **The outer law for `ζΨ_M` is equivalent to `(L)`.**  `(L)` is the statement that the
log-mean of `|ζ|` on the critical line over `[T,2T]` is eventually `≤ η` for every `η > 0`
(its lower bound is Littlewood's floor, `exists_zetaLine_logMean_floor_all_heights`); the outer
law is the statement that the log-mean of `|ζΨ_M|` is eventually `≤ J_M(ε) + η` for every
`ε ∈ (0,1)`, `η > 0`. -/
theorem zetaLine_logMean_le_iff_mollifiedProduct_logMean_le (M : ℕ) (hM : 1 < M) :
    (∀ η : ℝ, 0 < η → ∀ᶠ T in atTop,
      T⁻¹ * (∫ t in T..(2 * T), Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) ≤ η) ↔
    (∀ ε : ℝ, 0 < ε → ε < 1 → ∀ η : ℝ, 0 < η → ∀ᶠ T in atTop,
      T⁻¹ * (∫ t in T..(2 * T), Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
          edPoly (levinsonShiftedLinearMollifierCoeff M (1 / 2)) (Finset.Icc 1 M)
            (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖)
        ≤ linearMollifierTorusLogMean M ε + η) := by
  set s : Finset ℕ := Finset.Icc 1 M with hsdef
  have hs : ∀ n ∈ s, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  have h1 : 1 ∈ s := Finset.mem_Icc.mpr ⟨le_rfl, hM.le⟩
  set b := levinsonShiftedLinearMollifierCoeff M (1 / 2) with hb
  have hb1 : b 1 = 1 := levinsonShiftedLinearMollifierCoeff_one hM _
  have hbn : ∀ n ∈ s, ‖b n‖ ≤ 1 :=
    fun n hn => norm_levinsonShiftedLinearMollifierCoeff_le_one hM (hs n hn) le_rfl
  have hne : ∃ z : ℂ, edPoly b s z ≠ 0 := by
    refine ⟨(7 : ℂ), fun h0 => ?_⟩
    have h := norm_edPoly_sub_one_le_half_of_six_le b hs h1 hb1 hbn (z := (7 : ℂ)) (by simp; norm_num)
    rw [h0] at h
    have : ‖(0 : ℂ) - 1‖ = 1 := by simp
    rw [this] at h
    norm_num at h
  constructor
  · intro hL ε hε hε1 η hη
    have h1' := eventually_window_logMean_zeta_mul_linearMollifier_le M hM hε (half_pos hη)
    have h2 := hL (η / 2) (half_pos hη)
    filter_upwards [h1', h2, eventually_gt_atTop (0 : ℝ)] with T hT1 hT2 hTpos
    try simp only [← hb, ← hsdef] at hT1
    have : T⁻¹ * (∫ t in T..(2 * T), Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        edPoly b s (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖)
        ≤ T⁻¹ * ((∫ t in T..(2 * T), Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖)
          + T * (linearMollifierTorusLogMean M ε + η / 2)) := by gcongr
    rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hTpos.ne', one_mul] at this
    linarith
  · intro hout η hη
    obtain ⟨D, hD, hlow⟩ := exists_eventually_window_logMean_linearMollifier_ge M hM
    set ε : ℝ := Real.exp (-(3 * (D + 1) / η)) with hεdef
    have hε : 0 < ε := Real.exp_pos _
    have hε1 : ε < 1 := by
      have hneg : -(3 * (D + 1) / η) < 0 := by
        have : 0 < 3 * (D + 1) / η := by positivity
        linarith
      have := Real.exp_lt_exp.mpr hneg
      rwa [Real.exp_zero] at this
    have hlam : Real.log (1 / ε) = 3 * (D + 1) / η := by
      rw [hεdef, one_div, ← Real.exp_neg, Real.log_exp, neg_neg]
    have hDlam : D / Real.log (1 / ε) ≤ η / 3 := by
      rw [hlam, div_div_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [hD, hη]
    have h1' := hout ε hε hε1 (η / 3) (by positivity)
    have h2 := hlow ε hε hε1 (η / 3) (by positivity)
    filter_upwards [h1', h2, eventually_ge_atTop (20 : ℝ)] with T hT1 hT2 h20
    have hTpos : 0 < T := by linarith
    try simp only [← hb, ← hsdef] at hT1 hT2
    have hdec := integral_log_norm_zeta_mul_edPoly_line b hs hne h20 (by linarith : T < 2 * T)
    rw [hdec, mul_add] at hT1
    linarith

/-- **Two-sided squeeze under `(L)`.**  If `(L)` holds then for every `ε ∈ (0,1)` and `η > 0`,
eventually `J_M(ε) − D_M/log(1/ε) − η ≤ (1/T)∫_T^{2T} log |ζΨ_M| ≤ J_M(ε) + η`. -/
theorem exists_mollifiedProduct_logMean_squeeze_of_L (M : ℕ) (hM : 1 < M)
    (hL : ∀ η : ℝ, 0 < η → ∀ᶠ T in atTop,
      |T⁻¹ * (∫ t in T..(2 * T), Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖)| ≤ η) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ η : ℝ, 0 < η → ∀ᶠ T in atTop,
      linearMollifierTorusLogMean M ε - D / Real.log (1 / ε) - η ≤
        T⁻¹ * (∫ t in T..(2 * T), Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
          edPoly (levinsonShiftedLinearMollifierCoeff M (1 / 2)) (Finset.Icc 1 M)
            (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) ∧
      T⁻¹ * (∫ t in T..(2 * T), Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
          edPoly (levinsonShiftedLinearMollifierCoeff M (1 / 2)) (Finset.Icc 1 M)
            (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) ≤ linearMollifierTorusLogMean M ε + η := by
  set s : Finset ℕ := Finset.Icc 1 M with hsdef
  have hs : ∀ n ∈ s, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  have h1 : 1 ∈ s := Finset.mem_Icc.mpr ⟨le_rfl, hM.le⟩
  set b := levinsonShiftedLinearMollifierCoeff M (1 / 2) with hb
  have hb1 : b 1 = 1 := levinsonShiftedLinearMollifierCoeff_one hM _
  have hbn : ∀ n ∈ s, ‖b n‖ ≤ 1 :=
    fun n hn => norm_levinsonShiftedLinearMollifierCoeff_le_one hM (hs n hn) le_rfl
  have hne : ∃ z : ℂ, edPoly b s z ≠ 0 := by
    refine ⟨(7 : ℂ), fun h0 => ?_⟩
    have h := norm_edPoly_sub_one_le_half_of_six_le b hs h1 hb1 hbn (z := (7 : ℂ)) (by simp; norm_num)
    rw [h0] at h
    have : ‖(0 : ℂ) - 1‖ = 1 := by simp
    rw [this] at h
    norm_num at h
  obtain ⟨D, hD, hlow⟩ := exists_eventually_window_logMean_linearMollifier_ge M hM
  refine ⟨D, hD, ?_⟩
  intro ε hε hε1 η hη
  have hupper := (zetaLine_logMean_le_iff_mollifiedProduct_logMean_le M hM).mp
    (fun η' hη' => by
      filter_upwards [hL η' hη'] with T hT
      exact (abs_le.mp hT).2) ε hε hε1 η hη
  have hlow' := hlow ε hε hε1 (η / 2) (half_pos hη)
  have hLlow := hL (η / 2) (half_pos hη)
  filter_upwards [hupper, hlow', hLlow, eventually_ge_atTop (20 : ℝ)] with T hT1 hT2 hT3 h20
  refine ⟨?_, hT1⟩
  have hTpos : 0 < T := by linarith
  try simp only [← hb, ← hsdef] at hT2
  have hdec := integral_log_norm_zeta_mul_edPoly_line b hs hne h20 (by linarith : T < 2 * T)
  rw [hdec, mul_add]
  have := (abs_le.mp hT3).1
  linarith

end

end RHTower
