import GaloisForLFunctions.SurfaceOfSpecZ.OnlyDeepOrdinatesNeedSeparation
import GaloisForLFunctions.SurfaceOfSpecZ.TheOtherSideSeesEveryZero

/-!
# The other side on windows

Upper bounds on windows decide as lower bounds do, and real zeros do not mask. Let the exponents of
depth `> c ≥ 0` of a tempered configuration have `δ`-separated ordinates
(`DeepSeparatedOrdinates`); real zeros are allowed. An upper bound `2 Re S ≤ K e^{su}`, `s ≥ c`,
on windows of length `80/δ` beyond every bound puts every zero in `Re ρ ≤ ½ + s`
(`re_le_of_bddAbove_exp_windows_of_deepSeparated`), and a bounded trace from above at the primes of
windows `[x, e^{80/δ + 1} x]` gives `Re ρ ≤ ½ + c`
(`re_le_of_bddAbove_prime_windows_of_deepSeparated`).

Landau's inequality is applied to `K − F`. The zero-frequency coefficient enters with its sign
(`norm_le_re_add_of_window_lower`): a real exponent of depth `> c` contributes
`−D_x e^{xu₀} σ_ℓ(x − x₀)² ≤ 0`, since `D_x > 0` (`evenCoeff_spline_pos_of_real`), so it helps the
upper side, as in the attained case. If the dominant exponent is itself real, the same test reads
its weight at frequency zero.

For `ζ`: if the zeros off the line have `δ`-separated ordinates, a bounded trace from above at the
primes of one sparse sequence of windows of fixed ratio gives the Riemann hypothesis
(`riemannHypothesis_of_prime_windows_bddAbove_of_offLine_separated`).
-/

open Complex Filter Topology Set
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23

variable {Z : ZeroConfig}

/-- `σ_ℓ` is real at real arguments. -/
theorem boxAvg_ofReal_im (ℓ r : ℝ) : (boxAvg ℓ (r : ℂ)).im = 0 := by
  have h : (fun s : ℝ => cexp ((r : ℂ) * s)) = fun s : ℝ => ((Real.exp (r * s) : ℝ) : ℂ) := by
    funext s; push_cast; rfl
  unfold boxAvg
  rw [h, intervalIntegral.integral_ofReal, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
    Complex.ofReal_im]

/-- **A deep real exponent has a nonnegative zero-frequency term.** -/
theorem re_term_nonneg_of_real {z : ℂ} (hz : z ∈ zeroExps Z) (him : z.im = 0) (hre : 0 < z.re)
    (u₀ ℓ x₀ : ℝ) :
    0 ≤ (evenCoeff Z (boxSpline 1 3) z * cexp (z * u₀) * boxAvg ℓ (z - x₀) ^ 2).re := by
  have hzr : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [him])
  have hzc : conj z = z := by rw [hzr, Complex.conj_ofReal]
  have hmem : (1 / 2 + z) ∈ Z.carrier := by
    rcases hz with h | h
    · exact h
    · rwa [hzc] at h
  have hD := evenCoeff_spline_pos_of_real Z hmem hre him
  have hDim : (evenCoeff Z (boxSpline 1 3) z).im = 0 := by
    have h := evenCoeff_conj Z z
    rw [hzc] at h
    have := congrArg Complex.im h
    rw [Complex.conj_im] at this
    linarith
  have he : cexp (z * u₀) = ((Real.exp (z.re * u₀) : ℝ) : ℂ) := by
    rw [hzr]; push_cast; simp
  have hb : (boxAvg ℓ (z - x₀)).im = 0 := by
    rw [hzr, ← Complex.ofReal_sub]; exact boxAvg_ofReal_im _ _
  have hD' : evenCoeff Z (boxSpline 1 3) z = (((evenCoeff Z (boxSpline 1 3) z).re : ℝ) : ℂ) :=
    Complex.ext (by simp) (by simp [hDim])
  have hb' : boxAvg ℓ (z - x₀) = (((boxAvg ℓ (z - x₀)).re : ℝ) : ℂ) :=
    Complex.ext (by simp) (by simp [hb])
  rw [hD', he, hb', ← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
    Complex.ofReal_re]
  exact mul_nonneg (mul_nonneg hD.le (Real.exp_pos _).le) (sq_nonneg _)

/-- **Truncation on a window, from above.** -/
theorem exists_finset_window_upper (hZ : TemperedConfig Z) (u₀ ℓ : ℝ) {c : ℝ}
    (hall : ∀ u ∈ Icc (u₀ - ℓ) (u₀ + ℓ), 2 * (lagStructure Z (boxSpline 1 3) u).re ≤ c)
    (T : Finset ℂ) :
    ∃ S : Finset ℂ, (∀ z ∈ T, evenCoeff Z (boxSpline 1 3) z ≠ 0 → z ∈ S) ∧
      (∀ z ∈ S, z ∈ zeroExps Z) ∧ ∀ v ∈ Icc (-ℓ) ℓ,
        (∑ z ∈ S, evenCoeff Z (boxSpline 1 3) z * cexp (z * ((u₀ + v : ℝ) : ℂ))).re ≤ c + 1 := by
  classical
  obtain ⟨S₀, hS₀⟩ := exists_finset_trace_approx hZ (|u₀| + ℓ) one_pos
  refine ⟨(S₀ ∪ T).filter (fun z => evenCoeff Z (boxSpline 1 3) z ≠ 0),
    fun z hz h => Finset.mem_filter.mpr ⟨by simp [hz], h⟩,
    fun z hz => mem_of_evenCoeff_ne_zero (Finset.mem_filter.mp hz).2, fun v hv => ?_⟩
  have hsumS : ∑ z ∈ (S₀ ∪ T).filter (fun z => evenCoeff Z (boxSpline 1 3) z ≠ 0),
      evenCoeff Z (boxSpline 1 3) z * cexp (z * ((u₀ + v : ℝ) : ℂ)) =
      ∑ z ∈ S₀ ∪ T, evenCoeff Z (boxSpline 1 3) z * cexp (z * ((u₀ + v : ℝ) : ℂ)) :=
    Finset.sum_filter_of_ne fun z _ h => left_ne_zero_of_mul h
  have hR : |u₀ + v| ≤ |u₀| + ℓ :=
    (abs_add_le _ _).trans (by linarith [abs_le.mpr ⟨hv.1, hv.2⟩])
  have happ := hS₀ (S₀ ∪ T) Finset.subset_union_left (u₀ + v) hR
  have hK1 := hall (u₀ + v) ⟨by linarith [hv.1], by linarith [hv.2]⟩
  rw [hsumS]
  have hd := Complex.re_le_norm ((∑ z ∈ S₀ ∪ T, evenCoeff Z (boxSpline 1 3) z *
    cexp (z * ((u₀ + v : ℝ) : ℂ))) -
    ((2 * (lagStructure Z (boxSpline 1 3) (u₀ + v)).re : ℝ) : ℂ))
  rw [Complex.sub_re, Complex.ofReal_re, norm_sub_rev] at hd
  linarith

/-- **The dominant weight on a window, from above.** If `Re Σ_S D_z e^{z(u₀+v)} ≤ K'` on
`|v| ≤ ℓ`, with separation above depth `c ≥ 0` and the drift bound `B ≤ 3M₀`, then
`M₀ ≤ 3K' e^{ℓ/2} + 5 (Σ|D_z|) e^{ℓ} e^{cu₀}`. Real exponents are allowed: the deep ones enter the
zero-frequency coefficient with the helpful sign. -/
theorem expWeight_le_of_window_upper_deep (hZ : TemperedConfig Z) {c δ : ℝ} (hc : 0 ≤ c)
    (hδ : 0 < δ) (hsep : DeepSeparatedOrdinates Z c δ) {S : Finset ℂ}
    (hSE : ∀ z ∈ S, z ∈ zeroExps Z) {z₀ : ℂ} (hz₀S : z₀ ∈ S) (hz₀'S : conj z₀ ∈ S)
    (hz₀c : c < z₀.re) {u₀ ℓ K' B : ℝ} (hu₀ : 0 ≤ u₀) (hℓ0 : 0 < ℓ) (hK'0 : 0 ≤ K')
    (hδℓ : 40 ≤ δ * ℓ)
    (hdrift : ∀ z, expWeight Z u₀ z * Real.exp (|z.re - z₀.re| * ℓ) ≤ B)
    (hBle : B ≤ 3 * expWeight Z u₀ z₀)
    (hup : ∀ v ∈ Icc (-ℓ) ℓ,
      (∑ z ∈ S, evenCoeff Z (boxSpline 1 3) z * cexp (z * ((u₀ + v : ℝ) : ℂ))).re ≤ K') :
    expWeight Z u₀ z₀ ≤ 3 * K' * Real.exp (ℓ / 2) +
      5 * ((∑' z, ‖evenCoeff Z (boxSpline 1 3) z‖) * Real.exp ℓ * Real.exp (c * u₀)) := by
  classical
  set M₀ := expWeight Z u₀ z₀ with hM₀
  set Sh := (∑' z, ‖evenCoeff Z (boxSpline 1 3) z‖) * Real.exp ℓ * Real.exp (c * u₀) with hSh
  have hz₀E := hSE z₀ hz₀S
  have hz₀'E := hSE _ hz₀'S
  have hx₀ := abs_re_le_of_mem_zeroExps hz₀E
  -- Landau for `K' − F`
  have hL := norm_le_re_add_of_window_lower (D := fun z => -evenCoeff Z (boxSpline 1 3) z)
    hz₀S hz₀'S (by simp only [evenCoeff_conj, map_neg]) hℓ0 hK'0 (fun v hv => by
      have := hup v hv
      simp only [neg_mul, Finset.sum_neg_distrib, Complex.neg_re]
      linarith)
  simp only [neg_mul, norm_neg, Finset.sum_neg_distrib, Complex.neg_re] at hL
  have hM : ‖evenCoeff Z (boxSpline 1 3) z₀ * cexp (z₀ * u₀)‖ = M₀ := by
    rw [norm_mul, norm_cexp_mul_ofReal]; rfl
  rw [hM] at hL
  have hsepS : ∀ g : ℝ, g ≤ δ → ∀ S' : Finset ℂ, S' ⊆ S → ∀ z ∈ S', ∀ z' ∈ S', c < z.re →
      c < z'.re → z' ≠ z → g ≤ |z.im - z'.im| := fun g hg S' hS' z hz z' hz' h1 h2 h3 =>
    hg.trans (hsep z (hSE z (hS' hz)) z' (hSE z' (hS' hz')) h1 h2 h3)
  -- zero frequency: nonreal exponents leak, deep real ones have the helpful sign
  set t : ℂ → ℂ := fun z => evenCoeff Z (boxSpline 1 3) z * cexp (z * u₀) *
    boxAvg ℓ (z - z₀.re) ^ 2 with ht
  set Snr := S.filter (fun z => z.im ≠ 0) with hSnr
  set Sr := S.filter (fun z => ¬ z.im ≠ 0) with hSr
  have hsplit : ∑ z ∈ S, t z = ∑ z ∈ Snr, t z + ∑ z ∈ Sr, t z :=
    (Finset.sum_filter_add_sum_filter_not S (fun z => z.im ≠ 0) t).symm
  have hnr : ∑ z ∈ Snr, ‖t z‖ ≤ B * (4 / ℓ ^ 2) * (8 / (δ / 2) ^ 2) + Sh := by
    have hnot : ((z₀.re : ℝ) : ℂ) ∉ Snr := fun h =>
      (Finset.mem_filter.mp h).2 (Complex.ofReal_im _)
    have h := sum_term_erase_deep_le hZ (S := Snr)
      (fun z hz => hSE z (Finset.mem_of_mem_filter z hz)) (c := c) (half_pos hδ)
      (q := ((z₀.re : ℝ) : ℂ)) hu₀ hℓ0 (by rw [Complex.ofReal_re]; exact hx₀)
      (hsepS _ (by linarith) Snr (Finset.filter_subset _ _))
      (fun z hz hzc _ => by
        obtain ⟨hzS, him⟩ := Finset.mem_filter.mp hz
        rw [Complex.ofReal_im, sub_zero]
        have h := hsep z (hSE z hzS) (conj z) (conj_mem_zeroExps (hSE z hzS)) hzc
          (by rw [Complex.conj_re]; exact hzc)
          (fun h => him (by have := congrArg Complex.im h; simp at this; linarith))
        rw [Complex.conj_im, sub_neg_eq_add, ← two_mul, abs_mul, abs_two] at h
        linarith)
      (by simpa only [Complex.ofReal_re] using hdrift)
    rwa [Finset.erase_eq_of_notMem hnot] at h
  have hr : -Sh ≤ (∑ z ∈ Sr, t z).re := by
    rw [← Finset.sum_filter_add_sum_filter_not Sr (fun z => c < z.re), Complex.add_re]
    have h1 : 0 ≤ (∑ z ∈ Sr.filter (fun z => c < z.re), t z).re := by
      rw [Complex.re_sum]
      refine Finset.sum_nonneg fun z hz => ?_
      obtain ⟨hzr, hzc⟩ := Finset.mem_filter.mp hz
      obtain ⟨hzS, him⟩ := Finset.mem_filter.mp hzr
      push Not at him
      exact re_term_nonneg_of_real (hSE z hzS) him (lt_of_le_of_lt hc hzc) u₀ ℓ z₀.re
    have h2 := sum_term_shallow_le hZ (S := Sr)
      (fun z hz => hSE z (Finset.mem_of_mem_filter z hz)) (c := c) hu₀ hℓ0
      (q := ((z₀.re : ℝ) : ℂ)) (by rw [Complex.ofReal_re]; exact hx₀)
    have h3 := (abs_le.mp ((Complex.abs_re_le_norm
      (∑ z ∈ Sr.filter (fun z => ¬ c < z.re), t z)).trans (norm_sum_le _ _))).1
    linarith
  have hX : -(∑ z ∈ S, t z).re ≤ B * (4 / ℓ ^ 2) * (8 / (δ / 2) ^ 2) + 2 * Sh := by
    rw [hsplit, Complex.add_re]
    have h1 := (abs_le.mp ((Complex.abs_re_le_norm (∑ z ∈ Snr, t z)).trans
      (norm_sum_le _ _))).1
    linarith
  -- the dominant ordinates
  have hm := sum_term_erase_deep_le hZ hSE (c := c) hδ (q := z₀) hu₀ hℓ0 hx₀
    (hsepS _ le_rfl S (Finset.Subset.refl _))
    (fun z hz hzc hne => by
      have := hsep z₀ hz₀E z (hSE z hz) hz₀c hzc hne; rwa [abs_sub_comm] at this) hdrift
  have hp := sum_term_erase_deep_le hZ hSE (c := c) hδ (q := conj z₀) hu₀ hℓ0
    (by rw [Complex.conj_re]; exact hx₀) (hsepS _ le_rfl S (Finset.Subset.refl _))
    (fun z hz hzc hne => by
      have := hsep (conj z₀) hz₀'E z (hSE z hz) (by rw [Complex.conj_re]; exact hz₀c) hzc hne
      rwa [abs_sub_comm] at this)
    (by simpa only [Complex.conj_re] using hdrift)
  have hM0 : 0 ≤ M₀ := expWeight_nonneg _ _
  have hB0 : 0 ≤ B := le_trans (mul_nonneg (expWeight_nonneg _ _) (Real.exp_pos _).le) (hdrift 0)
  have h1600 : (1600 : ℝ) ≤ (δ * ℓ) ^ 2 :=
    calc (1600 : ℝ) = 40 * 40 := by norm_num
      _ ≤ (δ * ℓ) * (δ * ℓ) := mul_le_mul hδℓ hδℓ (by norm_num) (by linarith)
      _ = (δ * ℓ) ^ 2 := by ring
  have hq0 : 4 / ℓ ^ 2 * (8 / (δ / 2) ^ 2) ≤ 2 / 25 := by
    rw [show 4 / ℓ ^ 2 * (8 / (δ / 2) ^ 2) = 128 / (δ * ℓ) ^ 2 by field_simp; ring]
    calc 128 / (δ * ℓ) ^ 2 ≤ 128 / 1600 :=
          div_le_div_of_nonneg_left (by norm_num) (by norm_num) h1600
      _ = 2 / 25 := by norm_num
  have hq1 : 4 / ℓ ^ 2 * (8 / δ ^ 2) ≤ 1 / 50 := by
    rw [show 4 / ℓ ^ 2 * (8 / δ ^ 2) = 32 / (δ * ℓ) ^ 2 by field_simp; ring]
    calc 32 / (δ * ℓ) ^ 2 ≤ 32 / 1600 :=
          div_le_div_of_nonneg_left (by norm_num) (by norm_num) h1600
      _ = 1 / 50 := by norm_num
  have t0 : B * (4 / ℓ ^ 2) * (8 / (δ / 2) ^ 2) ≤ B * (2 / 25) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hq0 hB0
  have t1 : B * (4 / ℓ ^ 2) * (8 / δ ^ 2) ≤ B * (1 / 50) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hq1 hB0
  have hKexp : 2 * K' * Real.exp (|z₀.re| * ℓ) ≤ 2 * K' * Real.exp (ℓ / 2) := by
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
    calc |z₀.re| * ℓ ≤ 1 / 2 * ℓ := mul_le_mul_of_nonneg_right hx₀ hℓ0.le
      _ = ℓ / 2 := by ring
  have hKE : 0 ≤ K' * Real.exp (ℓ / 2) := by positivity
  have hSh0 : 0 ≤ Sh := by positivity
  linarith

/-- **The windowed width law from above.** Let the exponents of depth `> c ≥ 0` of a tempered
configuration have `δ`-separated ordinates (real zeros allowed), and let some zero have real part
`> ½ + s`, `s ≥ c`. For every `K` and `ℓ ≥ 40/δ`, far enough out every window
`[u₀ − ℓ, u₀ + ℓ]` contains a scale with `2 Re S(u) > K e^{su}`. -/
theorem exists_gt_exp_in_window_of_deepSeparated (hZ : TemperedConfig Z) {c δ : ℝ} (hc : 0 ≤ c)
    (hδ : 0 < δ) (hsep : DeepSeparatedOrdinates Z c δ) {s : ℝ} (hs : c ≤ s) {ρ₁ : ℂ}
    (hρ₁ : ρ₁ ∈ Z.carrier) (hρ₁re : 1 / 2 + s < ρ₁.re) {ℓ : ℝ} (hℓ : 40 / δ ≤ ℓ) (K : ℝ) :
    ∃ U : ℝ, ∀ u₀, U ≤ u₀ → ∃ u ∈ Icc (u₀ - ℓ) (u₀ + ℓ),
      K * Real.exp (s * u) < 2 * (lagStructure Z (boxSpline 1 3) u).re := by
  have hs0 : 0 ≤ s := hc.trans hs
  set zp : ℂ := ρ₁ - 1 / 2 with hzpdef
  have hzp : evenCoeff Z (boxSpline 1 3) zp ≠ 0 :=
    evenCoeff_sub_half_ne_zero_of_conj_symm Z (contDiff_boxSpline (r := 1) one_pos 2).continuous
      (hasCompactSupport_of_support_subset_abs (boxSpline_support (r := 1) one_pos 3))
      (conj_paperFT_boxSpline _ _) (paperFT_boxSpline_neg _ _) hρ₁
      (paperFT_boxSpline_ne_zero one_pos 3 (im_gammaOf_ne_zero (by linarith)))
  have hzpre : s < zp.re := by simp [zp]; linarith
  obtain ⟨b, hb, hbsup⟩ := exists_depth_sup hzp
  have hbz : zp.re ≤ b := hb zp hzp
  have hδℓ : 40 ≤ δ * ℓ := by rw [div_le_iff₀ hδ] at hℓ; linarith
  have hℓ0 : 0 < ℓ := by
    by_contra h; push Not at h; nlinarith
  set η := min ((zp.re - s) / 2) (1 / ℓ) with hηdef
  have hη : 0 < η := lt_min (by linarith) (by positivity)
  have hηb : η ≤ (zp.re - s) / 2 := min_le_left _ _
  have hηℓ : η * ℓ ≤ 1 :=
    calc η * ℓ ≤ 1 / ℓ * ℓ := mul_le_mul_of_nonneg_right (min_le_right _ _) hℓ0.le
      _ = 1 := by field_simp
  obtain ⟨z₁, hz₁, hz₁b⟩ := hbsup (η / 2) (half_pos hη)
  obtain ⟨U₁, hdom⟩ := le_re_of_dominant hZ hη hz₁ hz₁b
  set A := ∑' z, ‖evenCoeff Z (boxSpline 1 3) z‖ with hA
  have hA0 : 0 ≤ A := tsum_nonneg fun _ => norm_nonneg _
  set C : ℝ := 3 * (|K| + 1) * Real.exp (s * ℓ) * Real.exp (ℓ / 2) + 5 * (A * Real.exp ℓ)
    with hCdef
  have hgrow : Tendsto (fun u => expWeight Z u zp * Real.exp (-(s * u))) atTop atTop := by
    have e : (fun u => expWeight Z u zp * Real.exp (-(s * u))) =
        fun u => ‖evenCoeff Z (boxSpline 1 3) zp‖ * Real.exp ((zp.re - s) * u) := by
      funext u; unfold expWeight; rw [mul_assoc, ← Real.exp_add]; ring_nf
    rw [e]
    exact Tendsto.const_mul_atTop (norm_pos_iff.mpr hzp)
      (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by linarith)))
  obtain ⟨U₃, hU₃⟩ := Filter.eventually_atTop.mp (hgrow.eventually_gt_atTop C)
  refine ⟨max (U₁ + ℓ) (max U₃ ℓ), fun u₀ hu₀ => ?_⟩
  have hu₁ : U₁ + ℓ ≤ u₀ := (le_max_left _ _).trans hu₀
  have hu₃ : U₃ ≤ u₀ := ((le_max_left _ _).trans (le_max_right _ _)).trans hu₀
  have hu₄ : ℓ ≤ u₀ := ((le_max_right _ _).trans (le_max_right _ _)).trans hu₀
  have hu00 : 0 ≤ u₀ := hℓ0.le.trans hu₄
  by_contra hall
  push Not at hall
  set E := Real.exp (s * (u₀ + ℓ)) with hE
  have hE1 : 1 ≤ E := Real.one_le_exp (mul_nonneg hs0 (by linarith))
  have hall' : ∀ u ∈ Icc (u₀ - ℓ) (u₀ + ℓ),
      2 * (lagStructure Z (boxSpline 1 3) u).re ≤ |K| * E := fun u hu => by
    have hKe : K * Real.exp (s * u) ≤ |K| * E :=
      mul_le_mul (le_abs_self K) (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu.2 hs0))
        (Real.exp_pos _).le (abs_nonneg K)
    linarith [hall u hu]
  obtain ⟨z₀, hz₀, h₀⟩ := exists_dominant hZ u₀ hzp
  obtain ⟨zA, hzA, hA'⟩ := exists_dominant hZ (u₀ + ℓ) hzp
  obtain ⟨zB, -, hB⟩ := exists_dominant hZ (u₀ + -ℓ) hzp
  have hz₀b : b - η ≤ z₀.re := hdom u₀ (by linarith) z₀ h₀
  have hzBb : b - η ≤ zB.re := hdom (u₀ + -ℓ) (by linarith) zB hB
  have hdrift := expWeight_drift_le hℓ0.le hb h₀ hz₀ hz₀b hA' hzA hB hzBb
  have hM0 : 0 ≤ expWeight Z u₀ z₀ := expWeight_nonneg _ _
  have hBle : Real.exp (η * ℓ) * expWeight Z u₀ z₀ ≤ 3 * expWeight Z u₀ z₀ :=
    mul_le_mul_of_nonneg_right ((Real.exp_le_exp.mpr hηℓ).trans
      (by linarith [Real.exp_one_lt_d9])) hM0
  have hz₀c : c < z₀.re := by linarith
  have hconj0 : evenCoeff Z (boxSpline 1 3) (conj z₀) ≠ 0 := by
    rw [evenCoeff_conj]; exact (map_ne_zero _).mpr hz₀
  classical
  obtain ⟨S, hTS, hSE, hup⟩ := exists_finset_window_upper hZ u₀ ℓ hall' {z₀, conj z₀}
  have hz₀S : z₀ ∈ S := hTS z₀ (by simp) hz₀
  have hz₀'S : conj z₀ ∈ S := hTS _ (by simp) hconj0
  have hle := expWeight_le_of_window_upper_deep hZ hc hδ hsep hSE hz₀S hz₀'S hz₀c hu00 hℓ0
    (by positivity : 0 ≤ |K| * E + 1) hδℓ hdrift hBle hup
  have h1 := hU₃ u₀ hu₃
  have h2 : expWeight Z u₀ zp * Real.exp (-(s * u₀)) * Real.exp (s * u₀) =
      expWeight Z u₀ zp := by rw [mul_assoc, ← Real.exp_add]; simp
  have hEe : E = Real.exp (s * ℓ) * Real.exp (s * u₀) := by
    rw [hE, ← Real.exp_add]; ring_nf
  have hcs : Real.exp (c * u₀) ≤ Real.exp (s * u₀) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hs hu00)
  have h3 : 3 * (|K| * E + 1) * Real.exp (ℓ / 2) + 5 * (A * Real.exp ℓ * Real.exp (c * u₀)) ≤
      C * Real.exp (s * u₀) := by
    have ha : 3 * (|K| * E + 1) * Real.exp (ℓ / 2) ≤
        3 * (|K| + 1) * Real.exp (s * ℓ) * Real.exp (ℓ / 2) * Real.exp (s * u₀) := by
      have hx : 0 ≤ Real.exp (ℓ / 2) := (Real.exp_pos _).le
      have hu1 : 1 ≤ Real.exp (s * ℓ) * Real.exp (s * u₀) := hEe ▸ hE1
      rw [hEe]
      nlinarith [abs_nonneg K]
    have hb' : 5 * (A * Real.exp ℓ * Real.exp (c * u₀)) ≤
        5 * (A * Real.exp ℓ) * Real.exp (s * u₀) := by
      have := mul_le_mul_of_nonneg_left hcs (show 0 ≤ 5 * (A * Real.exp ℓ) by positivity)
      linarith
    rw [hCdef, add_mul]
    linarith
  have h4 : C * Real.exp (s * u₀) < expWeight Z u₀ z₀ :=
    calc C * Real.exp (s * u₀) < expWeight Z u₀ zp * Real.exp (-(s * u₀)) * Real.exp (s * u₀) :=
          mul_lt_mul_of_pos_right h1 (Real.exp_pos _)
      _ = expWeight Z u₀ zp := h2
      _ ≤ expWeight Z u₀ z₀ := h₀ zp
  linarith

/-- **The width law on windows, from above.** -/
theorem re_le_of_bddAbove_exp_windows_of_deepSeparated (hZ : TemperedConfig Z) {c δ : ℝ}
    (hc : 0 ≤ c) (hδ : 0 < δ) (hsep : DeepSeparatedOrdinates Z c δ) {s : ℝ} (hs : c ≤ s)
    {T : Set ℝ} (hT : ∀ U : ℝ, ∃ a, U ≤ a ∧ Icc a (a + 80 / δ) ⊆ T) {K : ℝ}
    (hK : ∀ u ∈ T, 2 * (lagStructure Z (boxSpline 1 3) u).re ≤ K * Real.exp (s * u)) :
    ∀ ρ ∈ Z.carrier, ρ.re ≤ 1 / 2 + s := by
  intro ρ₁ hρ₁
  by_contra h
  push Not at h
  obtain ⟨U, hU⟩ := exists_gt_exp_in_window_of_deepSeparated hZ hc hδ hsep hs hρ₁ h
    (le_refl (40 / δ)) K
  obtain ⟨a, ha, hsub⟩ := hT U
  have h40 : 0 < 40 / δ := by positivity
  have h80 : 80 / δ = 40 / δ + 40 / δ := by ring
  obtain ⟨u, hu, hlt⟩ := hU (a + 40 / δ) (by linarith)
  have hmem : u ∈ T := hsub ⟨by linarith [hu.1], by linarith [hu.2]⟩
  linarith [hK u hmem]

/-- **Prime windows transfer to real windows, from above.** -/
theorem exists_bddAbove_exp_windows_of_prime_windows (hZ : TemperedConfig Z) {a α L K : ℝ}
    (ha : 0 ≤ a) (hα : 0 ≤ α) (haα : a - 1 / 3 ≤ α)
    (hwidth : ∀ ρ ∈ Z.carrier, ρ.re ≤ 1 / 2 + a)
    (hprime : ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧ ∀ p : ℕ, p.Prime → T ≤ Real.log p →
      Real.log p ≤ T + L + 1 → 2 * (lagStructure Z (boxSpline 1 3) (Real.log p)).re ≤ K) :
    ∃ M : ℝ, ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧ ∀ u ∈ Icc (T + 1) (T + 1 + L),
      2 * (lagStructure Z (boxSpline 1 3) u).re ≤ M * Real.exp (α * u) := by
  obtain ⟨G, U₀, hG, hU₀, hnear⟩ := exists_log_degree_near (θ := (2 : ℝ) / 3)
    (by norm_num) (powGaps_primes (by norm_num) (by norm_num))
  set Lc : ℝ := ∑' z : ℂ, ‖lagCoeff Z (boxSpline 1 3) z‖ * ‖z‖ with hLc
  have hLc0 : 0 ≤ Lc := tsum_nonneg fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hgaplim : Tendsto (fun u : ℝ => 2 * G * Real.exp (((2 : ℝ) / 3 - 1) * u)) atTop (𝓝 0) := by
    have he := Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by norm_num : (2 : ℝ) / 3 - 1 < 0))
    simpa only [Function.comp_def, id_eq, mul_zero] using he.const_mul (2 * G)
  obtain ⟨U₁, hU₁⟩ := eventually_atTop.mp
    (hgaplim.eventually_le_const (by norm_num : (0 : ℝ) < 1))
  refine ⟨|K| + 4 * Lc * G, fun U => ?_⟩
  obtain ⟨T, hTU, hbound⟩ := hprime (max U (max U₀ (max U₁ 0)))
  have hT₀ : U₀ ≤ T := ((le_max_left _ _).trans (le_max_right _ _)).trans hTU
  have hT₁ : U₁ ≤ T := (((le_max_left _ _).trans (le_max_right _ _)).trans
    (le_max_right _ _)).trans hTU
  have hT0 : 0 ≤ T := (((le_max_right _ _).trans (le_max_right _ _)).trans
    (le_max_right _ _)).trans hTU
  refine ⟨T, (le_max_left _ _).trans hTU, fun u hu => ?_⟩
  have hu0 : 0 ≤ u := by linarith [hu.1]
  obtain ⟨p, hp, -, hlog0, hlogu, hgap⟩ := hnear u (by linarith [hu.1])
  have hgap₁ : u - Real.log p ≤ 1 := hgap.trans (hU₁ u (by linarith [hu.1]))
  have hbase := hbound p hp (by linarith [hu.1]) (by linarith [hu.2])
  have hlip := abs_two_re_lagStructure_sub_le_of_width hZ ha hwidth hlog0 hlogu
  have hvar : |2 * (lagStructure Z (boxSpline 1 3) u).re -
      2 * (lagStructure Z (boxSpline 1 3) (Real.log p)).re| ≤
      4 * Lc * G * Real.exp (α * u) := by
    have h₁ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hgap (show 0 ≤ 2 * Lc by positivity)) (Real.exp_pos (a * u)).le
    have he : Real.exp (((2 : ℝ) / 3 - 1) * u) * Real.exp (a * u) =
        Real.exp ((a - 1 / 3) * u) := by
      rw [← Real.exp_add]; congr 1; ring
    have h₂ : 2 * Lc * (2 * G * Real.exp (((2 : ℝ) / 3 - 1) * u)) * Real.exp (a * u) =
        4 * Lc * G * Real.exp ((a - 1 / 3) * u) := by
      calc _ = 4 * Lc * G * (Real.exp (((2 : ℝ) / 3 - 1) * u) * Real.exp (a * u)) := by ring
        _ = _ := by rw [he]
    have h₃ := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right haα hu0))
      (show 0 ≤ 4 * Lc * G by positivity)
    exact hlip.trans (h₁.trans (h₂.le.trans h₃))
  have hK : K ≤ |K| * Real.exp (α * u) :=
    (le_abs_self K).trans (by
      have hh := mul_le_mul_of_nonneg_left (Real.one_le_exp (mul_nonneg hα hu0)) (abs_nonneg K)
      simpa only [mul_one] using hh)
  have hhigh := (abs_le.mp hvar).2
  have e : (|K| + 4 * Lc * G) * Real.exp (α * u) =
      |K| * Real.exp (α * u) + 4 * Lc * G * Real.exp (α * u) := by ring
  rw [e]
  linarith

/-- One bootstrap step at the primes, from above. -/
theorem re_le_of_prime_windows_step_above (hZ : TemperedConfig Z) {c δ : ℝ} (hc : 0 ≤ c)
    (hδ : 0 < δ) (hsep : DeepSeparatedOrdinates Z c δ) {a α K : ℝ} (ha : 0 ≤ a) (hα : c ≤ α)
    (haα : a - 1 / 3 ≤ α) (hwidth : ∀ ρ ∈ Z.carrier, ρ.re ≤ 1 / 2 + a)
    (hprime : ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧ ∀ p : ℕ, p.Prime → T ≤ Real.log p →
      Real.log p ≤ T + 80 / δ + 1 → 2 * (lagStructure Z (boxSpline 1 3) (Real.log p)).re ≤ K) :
    ∀ ρ ∈ Z.carrier, ρ.re ≤ 1 / 2 + α := by
  obtain ⟨M, hM⟩ := exists_bddAbove_exp_windows_of_prime_windows hZ ha (hc.trans hα) haα hwidth
    hprime
  refine re_le_of_bddAbove_exp_windows_of_deepSeparated hZ hc hδ hsep hα
    (T := {u | 2 * (lagStructure Z (boxSpline 1 3) u).re ≤ M * Real.exp (α * u)})
    (fun U => ?_) (fun u hu => hu)
  obtain ⟨T, hTU, hT⟩ := hM U
  exact ⟨T + 1, by linarith, fun u hu => hT u ⟨hu.1, by linarith [hu.2]⟩⟩

/-- **Prime windows from above.** If the exponents of depth `> c ≥ 0` have `δ`-separated ordinates
and `2 Re S(log p) ≤ K` at the primes of windows `[T, T + 80/δ + 1]` (in `log p`) beyond every
bound, every zero has real part `≤ ½ + c`; real zeros are allowed. -/
theorem re_le_of_bddAbove_prime_windows_of_deepSeparated (hZ : TemperedConfig Z) {c δ : ℝ}
    (hc : 0 ≤ c) (hδ : 0 < δ) (hsep : DeepSeparatedOrdinates Z c δ) {K : ℝ}
    (hprime : ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧ ∀ p : ℕ, p.Prime → T ≤ Real.log p →
      Real.log p ≤ T + 80 / δ + 1 → 2 * (lagStructure Z (boxSpline 1 3) (Real.log p)).re ≤ K) :
    ∀ ρ ∈ Z.carrier, ρ.re ≤ 1 / 2 + c := by
  have hhalf : ∀ ρ ∈ Z.carrier, ρ.re ≤ 1 / 2 + 1 / 2 := fun ρ hρ => by
    linarith [(Z.strip ρ hρ).2]
  have h1 := re_le_of_prime_windows_step_above hZ hc hδ hsep (a := 1 / 2)
    (α := max c (1 / 6)) (by norm_num) (le_max_left _ _)
    ((by norm_num : (1 : ℝ) / 2 - 1 / 3 ≤ 1 / 6).trans (le_max_right _ _)) hhalf hprime
  rcases le_total c (1 / 6) with h | h
  · rw [max_eq_right h] at h1
    exact re_le_of_prime_windows_step_above hZ hc hδ hsep (a := 1 / 6) (α := c)
      (by norm_num) le_rfl (by linarith) h1 hprime
  · rwa [max_eq_left h] at h1

/-- **For `ζ`, from above.** If the zeros of `ζ` off the critical line have `δ`-separated
ordinates, a bounded trace `2 Re S(log p) ≤ K` at the primes of windows `[x, e^{80/δ + 1} x]` along
any sequence of scales gives the Riemann hypothesis. -/
theorem riemannHypothesis_of_prime_windows_bddAbove_of_offLine_separated {δ : ℝ} (hδ : 0 < δ)
    (hsep : DeepSeparatedOrdinates zetaZeroConfig 0 δ) {K : ℝ}
    (hprime : ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧ ∀ p : ℕ, p.Prime → T ≤ Real.log p →
      Real.log p ≤ T + 80 / δ + 1 →
      2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re ≤ K) :
    RiemannHypothesis :=
  riemannHypothesis_of_forall_re_le fun ρ hρ => by
    have := re_le_of_bddAbove_prime_windows_of_deepSeparated temperedConfig_zetaZeroConfig
      le_rfl hδ hsep hprime ρ hρ
    linarith

end GaloisForLFunctions.SurfaceOfSpecZ
