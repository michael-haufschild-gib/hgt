import GaloisForLFunctions.HTGeometry.WeightedDirichletReadout
import GaloisForLFunctions.HTGeometry.UniformZeroCountBound
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Linear real-zero count of weighted Dirichlet readouts

Let `F(z) = Σ_{n ≥ 1} cₙ n^{iz}` with `Σ ‖cₙ‖ n^η < ∞`, `η > 0`, and not all `cₙ` zero.  High above
the real line the least index `n₀` with `c_{n₀} ≠ 0` dominates:
`|F(s + iY)| ≥ |c_{n₀}| n₀^{-Y} / 2` for all real `s` once `Y` is large.  A Jensen disc centred at
`s + iY` of radius `Y + η/2` stays in the half-plane of holomorphy, where `|F| ≤ Σ ‖cₙ‖ n^η`, and
contains the real window `[s - 1/2, s + 1/2]`.  Hence every unit real window carries at most a fixed
number `K` of distinct zeros, and `[0, T]` carries at most `K (1 + T)` of them.
-/

noncomputable section
set_option autoImplicit false

open Complex Filter Topology Set Metric LSeries MeromorphicOn

namespace GaloisForLFunctions.HTGeometry

/-! ### The leading term dominates high above the real line -/

theorem norm_term_eq_rpow (c : ℕ → ℂ) (w : ℂ) {n : ℕ} (hn : n ≠ 0) :
    ‖term c w n‖ = ‖c n‖ * (n : ℝ) ^ (-w.re) := by
  rw [norm_term_eq, if_neg hn, div_eq_mul_inv,
    ← Real.rpow_neg (Nat.cast_nonneg n)]

/-- **Leading-term lower bound.**  If `c_{n₀} ≠ 0` is the first nonzero coefficient, then
`|F(s + iY)| ≥ |c_{n₀}| n₀^{-Y}/2` for all real `s` and all large `Y`. -/
theorem exists_height_lower_bound {c : ℕ → ℂ} {η : ℝ} (hc : WeightedAbsSummable c η)
    (hη : 0 ≤ η) {n₀ : ℕ} (hn₀ : 0 < n₀) (hcn₀ : c n₀ ≠ 0)
    (hbelow : ∀ n, 0 < n → n < n₀ → c n = 0) :
    ∃ Y₀ : ℝ, 0 ≤ Y₀ ∧ ∀ Y ≥ Y₀, ∀ s : ℝ,
      ‖c n₀‖ * (n₀ : ℝ) ^ (-Y) / 2 ≤ ‖dirichletReadout c ((s : ℂ) + Y * I)‖ := by
  classical
  set G : ℝ → ℕ → ℝ := fun Y n => if n₀ < n then ‖c n‖ * ((n₀ : ℝ) / n) ^ Y else 0 with hGdef
  have hn₀pos : (0 : ℝ) < n₀ := by exact_mod_cast hn₀
  have hsum : Summable fun n => ‖c n‖ := hc.summable_norm hη
  have hlim : Tendsto (fun Y => ∑' n, G Y n) atTop (𝓝 (∑' _ : ℕ, (0 : ℝ))) := by
    refine tendsto_tsum_of_dominated_convergence hsum (fun n => ?_) ?_
    · by_cases hn : n₀ < n
      · have hn' : (n₀ : ℝ) < n := by exact_mod_cast hn
        have hnpos : (0 : ℝ) < n := hn₀pos.trans hn'
        have hb1 : (n₀ : ℝ) / n < 1 := (div_lt_one hnpos).mpr hn'
        have hb0 : -1 < (n₀ : ℝ) / n := by
          have : 0 ≤ (n₀ : ℝ) / n := by positivity
          linarith
        have := (tendsto_rpow_atTop_of_base_lt_one _ hb0 hb1).const_mul ‖c n‖
        simpa [hGdef, hn] using this
      · simp [hGdef, hn]
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with Y hY n
      by_cases hn : n₀ < n
      · have hn' : (n₀ : ℝ) < n := by exact_mod_cast hn
        have hnpos : (0 : ℝ) < n := hn₀pos.trans hn'
        simp only [hGdef, if_pos hn, Real.norm_eq_abs]
        rw [abs_of_nonneg (by positivity)]
        have hle : ((n₀ : ℝ) / n) ^ Y ≤ 1 :=
          Real.rpow_le_one (by positivity) ((div_le_one hnpos).mpr hn'.le) hY
        calc ‖c n‖ * ((n₀ : ℝ) / n) ^ Y ≤ ‖c n‖ * 1 := by gcongr
          _ = ‖c n‖ := mul_one _
      · simp [hGdef, hn]
  rw [tsum_zero] at hlim
  have hc0 : 0 < ‖c n₀‖ := norm_pos_iff.mpr hcn₀
  obtain ⟨Y₁, hY₁⟩ := eventually_atTop.mp
    (hlim.eventually (gt_mem_nhds (show (0 : ℝ) < ‖c n₀‖ / 2 by positivity)))
  refine ⟨max Y₁ 0, le_max_right _ _, fun Y hY s => ?_⟩
  have hYY₁ : Y₁ ≤ Y := (le_max_left _ _).trans hY
  have hY0 : 0 ≤ Y := (le_max_right _ _).trans hY
  have hGY := hY₁ Y hYY₁
  set w : ℂ := -(I * ((s : ℂ) + Y * I)) with hw
  have hwre : w.re = Y := by simp [hw]
  have hsumm : Summable (term c w) := hc.lSeriesSummable (by rw [hwre]; linarith)
  have hnorm : Summable fun n => ‖term c w n‖ := hc.summable_norm_term (by rw [hwre]; linarith)
  have hsplit := hsumm.tsum_eq_add_tsum_ite n₀
  have hrest : ∀ n, ‖ite (n = n₀) 0 (term c w n)‖ ≤ (n₀ : ℝ) ^ (-Y) * G Y n := by
    intro n
    by_cases h : n = n₀
    · subst h; simp [hGdef]
    · rw [if_neg h]
      rcases lt_or_gt_of_ne h with hlt | hgt
      · rcases Nat.eq_zero_or_pos n with h0 | hpos
        · subst h0; simp [hGdef, not_lt.mpr (Nat.zero_le n₀)]
        · rw [term_of_ne_zero hpos.ne', hbelow n hpos hlt, zero_div, norm_zero]
          have : ¬ n₀ < n := not_lt.mpr hlt.le
          simp [hGdef, this]
      · have hn' : (n₀ : ℝ) < n := by exact_mod_cast hgt
        have hnpos : (0 : ℝ) < n := hn₀pos.trans hn'
        rw [norm_term_eq_rpow c w (by omega), hwre]
        simp only [hGdef, if_pos hgt]
        rw [Real.div_rpow hn₀pos.le hnpos.le]
        have h1 : (n₀ : ℝ) ^ Y ≠ 0 := (Real.rpow_pos_of_pos hn₀pos Y).ne'
        have h2 : (n : ℝ) ^ Y ≠ 0 := (Real.rpow_pos_of_pos hnpos Y).ne'
        refine le_of_eq ?_
        rw [Real.rpow_neg hn₀pos.le, Real.rpow_neg hnpos.le]
        field_simp
  have hGsum : Summable (G Y) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hsum
    · simp only [hGdef]; split_ifs <;> positivity
    · simp only [hGdef]
      split_ifs with hn
      · have hn' : (n₀ : ℝ) < n := by exact_mod_cast hn
        have hnpos : (0 : ℝ) < n := hn₀pos.trans hn'
        have hle : ((n₀ : ℝ) / n) ^ Y ≤ 1 :=
          Real.rpow_le_one (by positivity) ((div_le_one hnpos).mpr hn'.le) hY0
        calc ‖c n‖ * ((n₀ : ℝ) / n) ^ Y ≤ ‖c n‖ * 1 := by gcongr
          _ = ‖c n‖ := mul_one _
      · exact norm_nonneg _
  have hiteSum : Summable fun n => ‖ite (n = n₀) 0 (term c w n)‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hnorm
    split_ifs <;> simp
  have hbound : ‖∑' n, ite (n = n₀) 0 (term c w n)‖ ≤ (n₀ : ℝ) ^ (-Y) * (‖c n₀‖ / 2) := by
    refine (norm_tsum_le_tsum_norm hiteSum).trans ?_
    calc ∑' n, ‖ite (n = n₀) 0 (term c w n)‖ ≤ ∑' n, (n₀ : ℝ) ^ (-Y) * G Y n :=
          hiteSum.tsum_le_tsum hrest (hGsum.mul_left _)
      _ = (n₀ : ℝ) ^ (-Y) * ∑' n, G Y n := tsum_mul_left
      _ ≤ (n₀ : ℝ) ^ (-Y) * (‖c n₀‖ / 2) := by
          gcongr
  have hlead : ‖term c w n₀‖ = ‖c n₀‖ * (n₀ : ℝ) ^ (-Y) := by
    rw [norm_term_eq_rpow c w hn₀.ne', hwre]
  have hF : dirichletReadout c ((s : ℂ) + Y * I) =
      term c w n₀ + ∑' n, ite (n = n₀) 0 (term c w n) := by
    rw [dirichletReadout, ← hw]
    exact hsplit
  rw [hF]
  have htri := norm_sub_norm_le (term c w n₀) (-∑' n, ite (n = n₀) 0 (term c w n))
  rw [sub_neg_eq_add, norm_neg] at htri
  have hpos : 0 ≤ (n₀ : ℝ) ^ (-Y) := by positivity
  nlinarith [hlead, hbound, htri]

/-! ### Zeros in a Jensen disc -/

/-- Distinct zeros in a closed ball contribute to the divisor count of a function analytic on a
preconnected open set containing the ball and nonvanishing at the centre. -/
theorem card_le_sum_divisor_of_zeros_on {f : ℂ → ℂ} {U : Set ℂ}
    (hUc : IsPreconnected U) (hf : AnalyticOnNhd ℂ f U) {c : ℂ} (hcU : c ∈ U) (hfc : f c ≠ 0)
    {r : ℝ} (hball : closedBall c r ⊆ U) {α : Type*} [DecidableEq α] (s : Finset α) (z : α → ℂ)
    (hinj : Set.InjOn z s) (hmem : ∀ i ∈ s, z i ∈ closedBall c r)
    (hzero : ∀ i ∈ s, f (z i) = 0) :
    (s.card : ℤ) ≤ ∑ᶠ u, (divisor f (closedBall c r)) u := by
  let d := divisor f (closedBall c r)
  have horderC : meromorphicOrderAt f c ≠ ⊤ := by
    rw [(hf c hcU).meromorphicOrderAt_eq, (hf c hcU).analyticOrderAt_eq_zero.mpr hfc]
    simp
  have horder : ∀ u ∈ U, meromorphicOrderAt f u ≠ ⊤ := fun u hu =>
    hf.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected hUc hcU hu horderC
  have hfan : AnalyticOnNhd ℂ f (closedBall c r) := hf.mono hball
  have hsupport : closedBall c r ∩ f ⁻¹' {0} = Function.support d :=
    hfan.meromorphicNFOn.zero_set_eq_divisor_support fun u => horder u.1 (hball u.2)
  let Z : Finset ℂ := s.image z
  have hZcard : Z.card = s.card := Finset.card_image_iff.mpr hinj
  have hZsupport : (Z : Set ℂ) ⊆ Function.support d := by
    intro u hu
    simp only [Z, Finset.mem_coe, Finset.mem_image] at hu
    obtain ⟨i, hi, rfl⟩ := hu
    rw [← hsupport]
    exact ⟨hmem i hi, hzero i hi⟩
  have hdnonneg : ∀ u : ℂ, 0 ≤ d u := AnalyticOnNhd.divisor_nonneg hfan
  have hone : ∀ u ∈ Z, (1 : ℤ) ≤ d u := by
    intro u hu
    have hne : d u ≠ 0 := hZsupport hu
    have hnn : 0 ≤ d u := hdnonneg u
    omega
  have hdfin : (Function.support d).Finite := d.finiteSupport (isCompact_closedBall c r)
  let D : Finset ℂ := hdfin.toFinset
  have hZsub : Z ⊆ D := by
    intro u hu
    have hu' : u ∈ Function.support d := hZsupport (by simpa using hu)
    simpa [D] using hu'
  calc (s.card : ℤ) = ∑ u ∈ Z, (1 : ℤ) := by simp [hZcard]
    _ ≤ ∑ u ∈ Z, d u := Finset.sum_le_sum fun u hu => hone u hu
    _ ≤ ∑ u ∈ D, d u := Finset.sum_le_sum_of_subset_of_nonneg hZsub fun u _ _ => hdnonneg u
    _ = ∑ᶠ u, d u := by
        symm
        apply finsum_eq_sum_of_support_subset
        intro u hu
        simpa [D] using hu

/-! ### Uniform count in unit windows -/

theorem exists_first_nonzero_coeff {c : ℕ → ℂ} (hne : ∃ n, 0 < n ∧ c n ≠ 0) :
    ∃ n₀, 0 < n₀ ∧ c n₀ ≠ 0 ∧ ∀ n, 0 < n → n < n₀ → c n = 0 := by
  classical
  refine ⟨Nat.find hne, (Nat.find_spec hne).1, (Nat.find_spec hne).2, fun n hn hlt => ?_⟩
  by_contra h
  exact Nat.find_min hne hlt ⟨hn, h⟩

/-- **Uniform zero count in unit windows.** -/
theorem exists_window_zero_bound {c : ℕ → ℂ} {η : ℝ} (hc : WeightedAbsSummable c η)
    (hη : 0 < η) (hne : ∃ n, 0 < n ∧ c n ≠ 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (t₀ : ℝ) (S : Finset ℝ),
      (∀ t ∈ S, |t - t₀| ≤ 1 / 2 ∧ dirichletReadout c t = 0) → (S.card : ℝ) ≤ K := by
  obtain ⟨n₀, hn₀, hcn₀, hbelow⟩ := exists_first_nonzero_coeff hne
  obtain ⟨Y₀, hY₀, hlow⟩ := exists_height_lower_bound hc hη.le hn₀ hcn₀ hbelow
  set Y : ℝ := max Y₀ (1 / η) + 1 with hYdef
  have hYY₀ : Y₀ ≤ Y := by rw [hYdef]; linarith [le_max_left Y₀ (1 / η)]
  have hYη : 1 / η < Y := by rw [hYdef]; linarith [le_max_right Y₀ (1 / η)]
  have hYpos : 0 < Y := lt_of_le_of_lt (by positivity) hYη
  have hn₀pos : (0 : ℝ) < n₀ := by exact_mod_cast hn₀
  set m : ℝ := ‖c n₀‖ * (n₀ : ℝ) ^ (-Y) / 2 with hmdef
  have hm : 0 < m := by
    have := norm_pos_iff.mpr hcn₀
    have := Real.rpow_pos_of_pos hn₀pos (-Y)
    positivity
  set M : ℝ := max 1 (∑' n, ‖c n‖ * (n : ℝ) ^ η) with hMdef
  have hM : 1 ≤ M := le_max_left _ _
  set R : ℝ := Y + η / 2 with hRdef
  set r : ℝ := Real.sqrt (Y ^ 2 + 1 / 4) with hrdef
  have hRpos : 0 < R := by positivity
  have hrpos : 0 < r := Real.sqrt_pos.mpr (by positivity)
  have hrR : r < R := by
    rw [hrdef, Real.sqrt_lt' hRpos]
    have : 1 < Y * η := by
      rw [div_lt_iff₀ hη] at hYη; linarith
    nlinarith
  have hlogpos : 0 < Real.log (R / r) := Real.log_pos ((one_lt_div hrpos).mpr hrR)
  refine ⟨max 0 (Real.log (M / m) / Real.log (R / r)), le_max_left _ _, fun t₀ S hS => ?_⟩
  set z₀ : ℂ := (t₀ : ℂ) + Y * I with hz₀
  have hz₀im : z₀.im = Y := by simp [hz₀]
  have hball : closedBall z₀ R ⊆ {z : ℂ | -η < z.im} := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    have h1 : |z.im - Y| ≤ R := by
      have := Complex.abs_im_le_norm (z - z₀)
      simp only [sub_im, hz₀im] at this
      linarith
    simp only [mem_setOf_eq]
    rw [abs_le] at h1
    rw [hRdef] at h1
    linarith [h1.1]
  have hfz₀ : m ≤ ‖dirichletReadout c z₀‖ := hlow Y hYY₀ t₀
  have hsphere : ∀ z ∈ sphere z₀ |R|, ‖dirichletReadout c z‖ ≤ M := by
    intro z hz
    rw [abs_of_pos hRpos] at hz
    have hzb : z ∈ {z : ℂ | -η < z.im} := hball (sphere_subset_closedBall hz)
    exact (norm_dirichletReadout_le hc (le_of_lt hzb)).trans (le_max_right _ _)
  have hjensen := sum_divisor_le_of_bounds (c := z₀) (r := r) (R := R)
    (by rw [abs_of_pos hrpos]; exact hrpos) (by rw [abs_of_pos hrpos, abs_of_pos hRpos]; exact hrR)
    hM hm ((analyticOnNhd_dirichletReadout hc).mono (by rw [abs_of_pos hRpos]; exact hball))
    hfz₀ hsphere
  rw [abs_of_pos hrpos] at hjensen
  have hfne : dirichletReadout c z₀ ≠ 0 := by
    intro h; rw [h, norm_zero] at hfz₀; linarith
  have hcard := card_le_sum_divisor_of_zeros_on
    (convex_halfSpace_im_gt (-η)).isPreconnected (analyticOnNhd_dirichletReadout hc)
    (hball (mem_closedBall_self hRpos.le)) hfne
    ((closedBall_subset_closedBall hrR.le).trans hball) S (fun t : ℝ => (t : ℂ))
    (fun a _ b _ h => ofReal_injective h)
    (fun t ht => by
      rw [mem_closedBall, dist_eq_norm, hrdef]
      have hsq : ‖(t : ℂ) - z₀‖ ^ 2 = (t - t₀) ^ 2 + Y ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; simp [hz₀]; ring
      have htt := (hS t ht).1
      have hsq_le : (t - t₀) ^ 2 ≤ 1 / 4 := by
        have := abs_le.mp htt
        nlinarith [this.1, this.2]
      rw [← Real.sqrt_sq (norm_nonneg ((t : ℂ) - z₀)), hsq]
      exact Real.sqrt_le_sqrt (by linarith))
    (fun t ht => (hS t ht).2)
  have hcardR : (S.card : ℝ) ≤ (↑(∑ᶠ u, (divisor (dirichletReadout c) (closedBall z₀ r)) u) : ℝ) := by
    exact_mod_cast hcard
  exact hcardR.trans (hjensen.trans (le_max_right _ _))

/-- **Linear zero count.**  Unless all coefficients vanish, the distinct real zeros of the readout in
`[0, T]` number at most `K (1 + T)`. -/
theorem exists_zero_count_linear {c : ℕ → ℂ} {η : ℝ} (hc : WeightedAbsSummable c η)
    (hη : 0 < η) (hne : ∃ n, 0 < n ∧ c n ≠ 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ, 0 ≤ T → ∀ S : Finset ℝ,
      (∀ t ∈ S, 0 ≤ t ∧ t ≤ T ∧ dirichletReadout c t = 0) → (S.card : ℝ) ≤ K * (1 + T) := by
  classical
  obtain ⟨K₀, hK₀, hwin⟩ := exists_window_zero_bound hc hη hne
  refine ⟨2 * K₀, by positivity, fun T hT S hS => ?_⟩
  set φ : ℝ → ℕ := fun t => ⌊t + 1 / 2⌋₊ with hφ
  set N : ℕ := ⌊T + 1 / 2⌋₊ with hN
  have hmaps : Set.MapsTo φ (S : Set ℝ) (Finset.range (N + 1) : Set ℕ) := by
    intro t ht
    simp only [Finset.coe_range, mem_Iio]
    have := Nat.floor_le_floor (show t + 1 / 2 ≤ T + 1 / 2 by linarith [(hS t ht).2.1])
    simp only [hφ, hN]; omega
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hfib : ∀ k ∈ Finset.range (N + 1), (({a ∈ S | φ a = k}.card : ℕ) : ℝ) ≤ K₀ := by
    intro k _
    refine hwin k _ fun t ht => ?_
    rw [Finset.mem_filter] at ht
    obtain ⟨htS, hk⟩ := ht
    obtain ⟨ht0, -, hzero⟩ := hS t htS
    refine ⟨?_, hzero⟩
    have h1 := Nat.floor_le (show (0 : ℝ) ≤ t + 1 / 2 by linarith)
    have h2 := Nat.lt_floor_add_one (t + 1 / 2)
    simp only [hφ] at hk
    rw [hk] at h1 h2
    rw [abs_le]; constructor <;> linarith
  push_cast
  calc ∑ k ∈ Finset.range (N + 1), (({a ∈ S | φ a = k}.card : ℕ) : ℝ)
      ≤ ∑ _k ∈ Finset.range (N + 1), K₀ := Finset.sum_le_sum hfib
    _ = (N + 1) * K₀ := by simp
    _ ≤ (T + 3 / 2) * K₀ := by
        have := Nat.floor_le (show (0 : ℝ) ≤ T + 1 / 2 by linarith)
        rw [← hN] at this
        exact mul_le_mul_of_nonneg_right (by linarith) hK₀
    _ ≤ 2 * K₀ * (1 + T) := by nlinarith

end GaloisForLFunctions.HTGeometry
