import GaloisForLFunctions.RHTower.ZetaNotchDualOscillation
import GaloisForLFunctions.HTGeometry.GaussianPolynomialTail

/-!
# The two-line oscillation bound for the critical dual weight

With `ω = ω_L`, `J(Y, ξ) = ∫ ω(t) W_t(Y) e^{−iξt} dt` and `ω̂(ξ) = ∫ ω(t) e^{−iξt} dt`, for
`L ≥ 16`, `Y > 0`, `ξ ≠ 0`:

* dual line (`exists_norm_notchDualOscillation_le`):
  `‖J‖ ≤ (C/Y)(L²/|ξ| + L³ e^{−L²/128})`, and `‖J‖ ≤ C L³/Y` for every `ξ`;
* right line `Re w = 1/4` (`exists_norm_notchDualOscillation_sub_window_le`):
  `‖J − ω̂‖ ≤ C Y^{1/4}(L^{−1/2}/|ξ| + L e^{−L²/128})`, and `‖J − ω̂‖ ≤ C L Y^{1/4}`.

**Proof.**
- Fubini exchanges the height and Mellin integrals.
- The windowed carriers are estimated by one integration by parts for `|v| ≤ L/8` and trivially
  beyond.
- The Gaussian tail `e^{−v²}` on `|v| > L/8` costs `e^{−L²/128}`.
-/

noncomputable section

namespace RHTower.ZetaNotch

open Complex MeasureTheory Set Filter Topology RHTower GaloisForLFunctions.HTGeometry

/-! ## Continuity of the carrier and of its increment -/

theorem continuousAt_zetaChi_of_gammaR {z : ℂ} (hz : Gammaℝ (1 - z) ≠ 0) :
    ContinuousAt zetaChi z :=
  (zetaChi_analyticAt hz).continuousAt

theorem continuousAt_logDeriv_zetaChi {z : ℂ} (hz : Gammaℝ (1 - z) ≠ 0) (hz0 : zetaChi z ≠ 0) :
    ContinuousAt (logDeriv zetaChi) z := by
  have hA := zetaChi_analyticAt hz
  have hfun : logDeriv zetaChi = fun x => deriv zetaChi x / zetaChi x := by
    funext x
    rw [logDeriv_apply]
  rw [hfun]
  exact hA.deriv.continuousAt.div hA.continuousAt hz0

theorem gammaR_one_sub_linePt_ne_zero (τ : ℝ) : Gammaℝ (1 - linePt τ) ≠ 0 := by
  apply Gammaℝ_ne_zero_of_re_pos
  rw [Complex.sub_re, Complex.one_re, linePt_re]
  norm_num

theorem continuous_linePt : Continuous linePt := by
  unfold linePt
  fun_prop

/-- Joint continuity of the carrier along a continuous family of shifts. -/
theorem continuous_critCarrier_uncurry {w : ℝ → ℂ} (hw : Continuous w)
    (hΓ : ∀ t v, Gammaℝ (1 - (linePt t + w v)) ≠ 0) :
    Continuous (fun p : ℝ × ℝ => critCarrier p.1 (w p.2)) := by
  have hnum : ∀ σ : ℝ, σ = 1 ∨ σ = -1 →
      Continuous (fun p : ℝ × ℝ => zetaChi (linePt (σ * p.1) + w p.2)) := by
    intro σ _
    rw [continuous_iff_continuousAt]
    intro p
    have hin : Continuous (fun p : ℝ × ℝ => linePt (σ * p.1) + w p.2) :=
      (continuous_linePt.comp (continuous_const.mul continuous_fst)).add (hw.comp continuous_snd)
    exact ContinuousAt.comp (g := zetaChi) (continuousAt_zetaChi_of_gammaR (hΓ _ _))
      hin.continuousAt
  have hden : ∀ σ : ℝ, Continuous (fun p : ℝ × ℝ => zetaChi (linePt (σ * p.1))) := by
    intro σ
    rw [continuous_iff_continuousAt]
    intro p
    exact ContinuousAt.comp (g := zetaChi)
      (continuousAt_zetaChi_of_gammaR (gammaR_one_sub_linePt_ne_zero _))
      ((continuous_linePt.comp (continuous_const.mul continuous_fst)).continuousAt)
  have h1 := (hnum 1 (Or.inl rfl)).div (hden 1) (fun p => zetaChi_line_ne_zero _)
  have h2 := (hnum (-1) (Or.inr rfl)).div (hden (-1)) (fun p => zetaChi_line_ne_zero _)
  refine (h1.mul h2).congr fun p => ?_
  simp only [Pi.mul_apply, Pi.div_apply, one_mul, neg_one_mul, critCarrier,
    smoothAFEZetaChiShiftRatio]

/-- Continuity in the height of the carrier increment. -/
theorem continuous_critIncrement {w : ℂ} (hΓ : ∀ t, Gammaℝ (1 - (linePt t + w)) ≠ 0)
    (h0 : ∀ t, zetaChi (linePt t + w) ≠ 0) :
    Continuous (fun t : ℝ => critIncrement t w) := by
  have hL : ∀ σ : ℝ, Continuous (fun t : ℝ => logDeriv zetaChi (linePt (σ * t) + w)) := by
    intro σ
    rw [continuous_iff_continuousAt]
    intro t
    exact ContinuousAt.comp (g := logDeriv zetaChi)
      (continuousAt_logDeriv_zetaChi (hΓ _) (h0 _))
      (((continuous_linePt.comp (continuous_const.mul continuous_id)).add
        continuous_const).continuousAt)
  have hL0 : ∀ σ : ℝ, Continuous (fun t : ℝ => logDeriv zetaChi (linePt (σ * t))) := by
    intro σ
    rw [continuous_iff_continuousAt]
    intro t
    exact ContinuousAt.comp (g := logDeriv zetaChi)
      (continuousAt_logDeriv_zetaChi (gammaR_one_sub_linePt_ne_zero _) (zetaChi_line_ne_zero _))
      ((continuous_linePt.comp (continuous_const.mul continuous_id)).continuousAt)
  have h : Continuous (fun t : ℝ =>
      I * (logDeriv zetaChi (linePt (1 * t) + w) - logDeriv zetaChi (linePt (1 * t))) -
        I * (logDeriv zetaChi (linePt (-1 * t) + w) - logDeriv zetaChi (linePt (-1 * t)))) :=
    (continuous_const.mul ((hL 1).sub (hL0 1))).sub
      (continuous_const.mul ((hL (-1)).sub (hL0 (-1))))
  refine h.congr fun t => ?_
  simp only [one_mul, neg_one_mul, critIncrement]

/-! ## Windowed carriers on the dual line `w = −(1+iv)` -/

theorem dualShift_im (v : ℝ) : (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)).im = -v := by simp

theorem dualShift_re (v : ℝ) : (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)).re = -1 := by simp

theorem norm_dualShift_le (v : ℝ) : ‖-(((1 : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤ 1 + |v| := by
  rw [norm_neg]
  refine (norm_add_le _ _).trans ?_
  simp

theorem norm_critCarrier_dual_le_window {L t v : ℝ} (hL : 2 ≤ L) (ht : t ∈ Icc (L / 2) (5 * L / 2)) :
    ‖critCarrier t (-(((1 : ℝ) : ℂ) + (v : ℂ) * I))‖ ≤ 9 * L ^ 2 * (1 + |v|) ^ 2 := by
  refine (norm_critCarrier_dual_le t v).trans ?_
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have h1 : (1 + |t|) ^ 2 ≤ (3 * L) ^ 2 := by
    rw [abs_of_nonneg ht0]
    exact pow_le_pow_left₀ (by linarith) (by linarith [ht.2]) 2
  calc (1 + |t|) ^ 2 * (1 + |v|) ^ 2 ≤ (3 * L) ^ 2 * (1 + |v|) ^ 2 :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = 9 * L ^ 2 * (1 + |v|) ^ 2 := by ring

theorem continuous_critIncrement_dual (v : ℝ) :
    Continuous (fun t : ℝ => critIncrement t (-(((1 : ℝ) : ℂ) + (v : ℂ) * I))) :=
  continuous_critIncrement (fun t => gammaR_one_sub_dual_ne_zero t v)
    (fun t => zetaChi_dual_ne_zero t v)

/-- The windowed dual carrier, by one integration by parts. -/
theorem norm_windowed_dual_le {L v ξ : ℝ} (hL : 16 ≤ L) (hv : |v| ≤ L / 8) (hξ : ξ ≠ 0) :
    ‖∫ t, notchWindow L t * critCarrier t (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)) *
        Complex.exp (-(ξ * t) * I)‖ ≤
      9 * L ^ 2 * (1 + |v|) ^ 3 * (4 * blockWindowConst 1 + 80) / |ξ| := by
  have hL0 : 0 < L := by linarith
  have hc := blockWindowConst_nonneg 1
  set w : ℂ := -(((1 : ℝ) : ℂ) + (v : ℂ) * I) with hw
  have hmain := norm_integral_notchWindow_mul_cexp_le (L := L) hL0 (A := 9 * L ^ 2 * (1 + |v|) ^ 2)
    (B := 40 * (1 + |v|) / L) (ξ := ξ) (G := fun t => critCarrier t w)
    (G' := fun t => critCarrier t w * critIncrement t w) hξ
    (fun t => hasDerivAt_critCarrier_dual t v)
    (((continuous_iff_continuousAt.mpr fun t =>
      (hasDerivAt_critCarrier_dual t v).continuousAt)).mul (continuous_critIncrement_dual v))
    (fun t ht => norm_critCarrier_dual_le_window (by linarith) ht)
    (fun t ht => by
      have ht4 : 4 ≤ t := by linarith [ht.1]
      have hwim : 2 * |w.im| ≤ t := by
        rw [hw, dualShift_im, abs_neg]; linarith [ht.1]
      have hinc := norm_critIncrement_le ht4 hwim (by norm_num [hw, dualShift_re])
        (by norm_num [hw, dualShift_re])
      rw [norm_mul]
      apply mul_le_mul (norm_critCarrier_dual_le_window (by linarith) ht) _ (norm_nonneg _)
        (by positivity)
      refine hinc.trans ?_
      have hwn := norm_dualShift_le v
      have htL : L / 2 ≤ t := ht.1
      rw [div_le_div_iff₀ (by linarith) hL0]
      nlinarith [abs_nonneg v])
  refine hmain.trans ?_
  apply div_le_div_of_nonneg_right _ (abs_nonneg _)
  have h1v : 1 ≤ 1 + |v| := by linarith [abs_nonneg v]
  have hexp : 9 * L ^ 2 * (1 + |v|) ^ 2 * (4 * blockWindowConst 1 + 2 * L * (40 * (1 + |v|) / L))
      = 9 * L ^ 2 * (1 + |v|) ^ 2 * (4 * blockWindowConst 1 + 80 * (1 + |v|)) := by
    field_simp
    ring
  rw [hexp]
  have hpos : 0 ≤ 9 * L ^ 2 * (1 + |v|) ^ 2 := by positivity
  calc 9 * L ^ 2 * (1 + |v|) ^ 2 * (4 * blockWindowConst 1 + 80 * (1 + |v|))
      ≤ 9 * L ^ 2 * (1 + |v|) ^ 2 * ((1 + |v|) * (4 * blockWindowConst 1 + 80)) := by
        apply mul_le_mul_of_nonneg_left _ hpos
        nlinarith
    _ = 9 * L ^ 2 * (1 + |v|) ^ 3 * (4 * blockWindowConst 1 + 80) := by ring

theorem norm_windowed_dual_le_trivial {L v ξ : ℝ} (hL : 16 ≤ L) :
    ‖∫ t, notchWindow L t * critCarrier t (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)) *
        Complex.exp (-(ξ * t) * I)‖ ≤ 18 * L ^ 3 * (1 + |v|) ^ 2 := by
  have h := norm_integral_notchWindow_mul_cexp_le_trivial (L := L) (by linarith) (ξ := ξ)
    (G := fun t => critCarrier t (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)))
    (fun t ht => norm_critCarrier_dual_le_window (by linarith) ht)
  refine h.trans (le_of_eq ?_)
  ring

/-! ## Windowed carriers on the right line `w = 1/4 − iv` -/

/-- The fixed right abscissa. -/
def rightAbscissa : ℝ := 1 / 4

theorem rightAbscissa_pos : 0 < rightAbscissa := by unfold rightAbscissa; norm_num

theorem rightAbscissa_lt_half : rightAbscissa < 1 / 2 := by unfold rightAbscissa; norm_num

theorem rightShift_im (v : ℝ) : (((rightAbscissa : ℝ) : ℂ) + ((-v : ℝ) : ℂ) * I).im = -v := by
  simp

theorem rightShift_re (v : ℝ) : (((rightAbscissa : ℝ) : ℂ) + ((-v : ℝ) : ℂ) * I).re = 1 / 4 := by
  simp [rightAbscissa]

theorem norm_rightShift_le (v : ℝ) : ‖((rightAbscissa : ℝ) : ℂ) + ((-v : ℝ) : ℂ) * I‖ ≤ 1 + |v| := by
  refine (norm_add_le _ _).trans ?_
  simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one, abs_neg]
  unfold rightAbscissa
  norm_num

theorem continuous_critIncrement_right (v : ℝ) :
    Continuous (fun t : ℝ => critIncrement t (((rightAbscissa : ℝ) : ℂ) + ((-v : ℝ) : ℂ) * I)) :=
  continuous_critIncrement (fun t => gammaR_one_sub_right_ne_zero rightAbscissa_lt_half t v)
    (fun t => zetaChi_right_ne_zero rightAbscissa_pos rightAbscissa_lt_half t v)

/-- Size of the right-line carrier on the window: `≤ K (L/4)^{−1/2}` for `|v| ≤ L/8`. -/
theorem norm_critCarrier_right_le_window {K L t v : ℝ} (hK : 0 ≤ K)
    (hcar : ∀ t v : ℝ, ‖critCarrier t (((rightAbscissa : ℝ) : ℂ) + ((-v : ℝ) : ℂ) * I)‖ ≤
      K / ((max 1 |t - v|) ^ rightAbscissa * (max 1 |-t - v|) ^ rightAbscissa))
    (hL : 16 ≤ L) (hv : |v| ≤ L / 8) (ht : t ∈ Icc (L / 2) (5 * L / 2)) :
    ‖critCarrier t (((rightAbscissa : ℝ) : ℂ) + ((-v : ℝ) : ℂ) * I)‖ ≤
      K / ((L / 4) ^ rightAbscissa * (L / 4) ^ rightAbscissa) := by
  refine (hcar t v).trans ?_
  have hδ := rightAbscissa_pos
  have hL4 : 0 < L / 4 := by linarith
  have h1 : L / 4 ≤ max 1 |t - v| := by
    refine le_trans ?_ (le_max_right _ _)
    have := abs_sub_abs_le_abs_sub t v
    rw [abs_of_nonneg (by linarith [ht.1] : (0 : ℝ) ≤ t)] at this
    linarith [ht.1]
  have h2 : L / 4 ≤ max 1 |-t - v| := by
    refine le_trans ?_ (le_max_right _ _)
    have := abs_sub_abs_le_abs_sub (-t) v
    rw [abs_neg, abs_of_nonneg (by linarith [ht.1] : (0 : ℝ) ≤ t)] at this
    linarith [ht.1]
  have hp1 : (L / 4) ^ rightAbscissa ≤ (max 1 |t - v|) ^ rightAbscissa :=
    Real.rpow_le_rpow hL4.le h1 hδ.le
  have hp2 : (L / 4) ^ rightAbscissa ≤ (max 1 |-t - v|) ^ rightAbscissa :=
    Real.rpow_le_rpow hL4.le h2 hδ.le
  have hq1 : 0 < (L / 4) ^ rightAbscissa := Real.rpow_pos_of_pos hL4 _
  apply div_le_div_of_nonneg_left hK (by positivity)
  exact mul_le_mul hp1 hp2 hq1.le (by linarith)

theorem norm_critCarrier_right_le_const {K t v : ℝ} (hK : 0 ≤ K)
    (hcar : ∀ t v : ℝ, ‖critCarrier t (((rightAbscissa : ℝ) : ℂ) + ((-v : ℝ) : ℂ) * I)‖ ≤
      K / ((max 1 |t - v|) ^ rightAbscissa * (max 1 |-t - v|) ^ rightAbscissa)) :
    ‖critCarrier t (((rightAbscissa : ℝ) : ℂ) + ((-v : ℝ) : ℂ) * I)‖ ≤ K := by
  refine (hcar t v).trans ?_
  have hδ := rightAbscissa_pos
  have h1 : 1 ≤ (max 1 |t - v|) ^ rightAbscissa := Real.one_le_rpow (le_max_left _ _) hδ.le
  have h2 : 1 ≤ (max 1 |-t - v|) ^ rightAbscissa := Real.one_le_rpow (le_max_left _ _) hδ.le
  exact div_le_self hK (by nlinarith)

/-- The windowed right-line carrier, by one integration by parts. -/
theorem norm_windowed_right_le {K L v ξ : ℝ} (hK : 0 ≤ K)
    (hcar : ∀ t v : ℝ, ‖critCarrier t (((rightAbscissa : ℝ) : ℂ) + ((-v : ℝ) : ℂ) * I)‖ ≤
      K / ((max 1 |t - v|) ^ rightAbscissa * (max 1 |-t - v|) ^ rightAbscissa))
    (hL : 16 ≤ L) (hv : |v| ≤ L / 8) (hξ : ξ ≠ 0) :
    ‖∫ t, notchWindow L t * critCarrier t (((rightAbscissa : ℝ) : ℂ) + ((-v : ℝ) : ℂ) * I) *
        Complex.exp (-(ξ * t) * I)‖ ≤
      K / ((L / 4) ^ rightAbscissa * (L / 4) ^ rightAbscissa) * (1 + |v|) *
        (4 * blockWindowConst 1 + 80) / |ξ| := by
  have hL0 : 0 < L := by linarith
  have hc := blockWindowConst_nonneg 1
  set w : ℂ := ((rightAbscissa : ℝ) : ℂ) + ((-v : ℝ) : ℂ) * I with hw
  set A : ℝ := K / ((L / 4) ^ rightAbscissa * (L / 4) ^ rightAbscissa) with hAdef
  have hA0 : 0 ≤ A := by
    have : 0 < (L / 4) ^ rightAbscissa := Real.rpow_pos_of_pos (by linarith) _
    positivity
  have hmain := norm_integral_notchWindow_mul_cexp_le (L := L) hL0 (A := A)
    (B := 40 * (1 + |v|) / L) (ξ := ξ) (G := fun t => critCarrier t w)
    (G' := fun t => critCarrier t w * critIncrement t w) hξ
    (fun t => hasDerivAt_critCarrier_right rightAbscissa_pos rightAbscissa_lt_half t v)
    (((continuous_iff_continuousAt.mpr fun t =>
      (hasDerivAt_critCarrier_right rightAbscissa_pos rightAbscissa_lt_half t v).continuousAt)).mul
      (continuous_critIncrement_right v))
    (fun t ht => norm_critCarrier_right_le_window hK hcar hL hv ht)
    (fun t ht => by
      have ht4 : 4 ≤ t := by linarith [ht.1]
      have hwim : 2 * |w.im| ≤ t := by
        rw [hw, rightShift_im, abs_neg]; linarith [ht.1]
      have hinc := norm_critIncrement_le ht4 hwim (by norm_num [hw, rightShift_re, rightAbscissa])
        (by norm_num [hw, rightShift_re, rightAbscissa])
      rw [norm_mul]
      apply mul_le_mul (norm_critCarrier_right_le_window hK hcar hL hv ht) _ (norm_nonneg _) hA0
      refine hinc.trans ?_
      have hwn := norm_rightShift_le v
      have htL : L / 2 ≤ t := ht.1
      rw [div_le_div_iff₀ (by linarith) hL0]
      nlinarith [abs_nonneg v])
  refine hmain.trans ?_
  apply div_le_div_of_nonneg_right _ (abs_nonneg _)
  have hexp : A * (4 * blockWindowConst 1 + 2 * L * (40 * (1 + |v|) / L))
      = A * (4 * blockWindowConst 1 + 80 * (1 + |v|)) := by
    field_simp
    ring
  rw [hexp]
  calc A * (4 * blockWindowConst 1 + 80 * (1 + |v|))
      ≤ A * ((1 + |v|) * (4 * blockWindowConst 1 + 80)) := by
        apply mul_le_mul_of_nonneg_left _ hA0
        nlinarith [abs_nonneg v]
    _ = A * (1 + |v|) * (4 * blockWindowConst 1 + 80) := by ring

theorem norm_windowed_right_le_trivial {K L v ξ : ℝ} (hK : 0 ≤ K)
    (hcar : ∀ t v : ℝ, ‖critCarrier t (((rightAbscissa : ℝ) : ℂ) + ((-v : ℝ) : ℂ) * I)‖ ≤
      K / ((max 1 |t - v|) ^ rightAbscissa * (max 1 |-t - v|) ^ rightAbscissa))
    (hL : 16 ≤ L) :
    ‖∫ t, notchWindow L t * critCarrier t (((rightAbscissa : ℝ) : ℂ) + ((-v : ℝ) : ℂ) * I) *
        Complex.exp (-(ξ * t) * I)‖ ≤ 2 * L * K :=
  norm_integral_notchWindow_mul_cexp_le_trivial (L := L) (by linarith) (ξ := ξ)
    (G := fun t => critCarrier t (((rightAbscissa : ℝ) : ℂ) + ((-v : ℝ) : ℂ) * I))
    (fun t _ => norm_critCarrier_right_le_const hK hcar)

/-! ## Fubini over the Mellin variable -/

/-- The windowed height integral of a Mellin average is the Mellin average of the windowed height
integrals, given joint integrability. -/
theorem integral_notch_mul_integral_eq {L ξ : ℝ} (F : ℝ → ℝ → ℂ)
    (hF : Integrable (Function.uncurry fun t v =>
      notchWindow L t * F t v * Complex.exp (-(ξ * t) * I)) (volume.prod volume)) :
    ∫ t, notchWindow L t * (∫ v, F t v) * Complex.exp (-(ξ * t) * I) =
      ∫ v, ∫ t, notchWindow L t * F t v * Complex.exp (-(ξ * t) * I) := by
  have hpt : ∀ t, notchWindow L t * (∫ v, F t v) * Complex.exp (-(ξ * t) * I) =
      ∫ v, notchWindow L t * F t v * Complex.exp (-(ξ * t) * I) := by
    intro t
    rw [← integral_const_mul, ← integral_mul_const]
  simp_rw [hpt]
  exact integral_integral_swap hF

/-- Joint integrability of a windowed Mellin family with a product envelope. -/
theorem integrable_notch_mellin {L ξ : ℝ} (hL : 0 < L) {F : ℝ → ℝ → ℂ}
    (hFc : Continuous (Function.uncurry F)) {A : ℝ} {g : ℝ → ℝ} (hg : Integrable g)
    (hFb : ∀ t ∈ Icc (L / 2) (5 * L / 2), ∀ v, ‖F t v‖ ≤ A * g v) :
    Integrable (Function.uncurry fun t v =>
      notchWindow L t * F t v * Complex.exp (-(ξ * t) * I)) (volume.prod volume) := by
  have hind : Integrable ((Icc (L / 2) (5 * L / 2)).indicator (fun _ => A)) :=
    (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc
  refine Integrable.mono' (hind.mul_prod hg) ?_ (Filter.Eventually.of_forall fun p => ?_)
  · apply Continuous.aestronglyMeasurable
    have h1 : Continuous (fun p : ℝ × ℝ => notchWindow L p.1) :=
      (continuous_notchWindow L).comp continuous_fst
    have h3 : Continuous (fun p : ℝ × ℝ => Complex.exp (-(ξ * p.1) * I)) := by fun_prop
    exact (h1.mul hFc).mul h3
  · show ‖notchWindow L p.1 * F p.1 p.2 * Complex.exp (-(ξ * p.1) * I)‖ ≤ _
    by_cases ht : p.1 ∈ Icc (L / 2) (5 * L / 2)
    · rw [indicator_of_mem ht, norm_mul, norm_mul, Complex.norm_exp]
      have hre : (-(↑ξ * ↑p.1) * I).re = 0 := by simp
      rw [hre, Real.exp_zero, mul_one]
      have hFp := hFb p.1 ht p.2
      calc ‖notchWindow L p.1‖ * ‖F p.1 p.2‖ ≤ 1 * (A * g p.2) :=
            mul_le_mul (norm_notchWindow_le_one L p.1) hFp (norm_nonneg _) zero_le_one
        _ = A * g p.2 := one_mul _
    · rw [indicator_of_notMem ht, notchWindow_eq_zero hL ht]
      simp

/-! ## The dual line -/

theorem continuous_dualMellin_uncurry {Y : ℝ} (hY : 0 < Y) :
    Continuous (Function.uncurry fun t v : ℝ =>
      critCarrier t (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)) *
        smoothAFEMellinIntegrand Y (((1 : ℝ) : ℂ) + (v : ℂ) * I)) := by
  have h1 := continuous_critCarrier_uncurry (w := fun v : ℝ => -(((1 : ℝ) : ℂ) + (v : ℂ) * I))
    (by fun_prop) (fun t v => gammaR_one_sub_dual_ne_zero t v)
  have h2 : Continuous (fun p : ℝ × ℝ =>
      smoothAFEMellinIntegrand Y (((1 : ℝ) : ℂ) + (p.2 : ℂ) * I)) :=
    (continuous_smoothAFEMellinIntegrand_line (by norm_num) hY).comp continuous_snd
  exact h1.mul h2

theorem norm_dualMellin_le {L t v Y : ℝ} (hL : 2 ≤ L) (hY : 0 < Y)
    (ht : t ∈ Icc (L / 2) (5 * L / 2)) :
    ‖critCarrier t (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)) *
        smoothAFEMellinIntegrand Y (((1 : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤
      (9 * L ^ 2 * (Y⁻¹ * Real.exp 1)) * ((1 + |v|) ^ 2 * Real.exp (-(v ^ (2 : ℕ)))) := by
  rw [norm_mul]
  have hm := norm_smoothAFEMellinIntegrand_vertical_le hY (show (0 : ℝ) < 1 by norm_num) v
  have hm' : ‖smoothAFEMellinIntegrand Y (((1 : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤
      (Y⁻¹ * Real.exp 1) * Real.exp (-(v ^ (2 : ℕ))) := by
    simpa [Real.rpow_neg_one] using hm
  calc _ ≤ (9 * L ^ 2 * (1 + |v|) ^ 2) * ((Y⁻¹ * Real.exp 1) * Real.exp (-(v ^ (2 : ℕ)))) :=
        mul_le_mul (norm_critCarrier_dual_le_window hL ht) hm' (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- **Fubini form of the dual oscillation.** -/
theorem integral_notch_critDualWeight_eq {L Y ξ : ℝ} (hL : 2 ≤ L) (hY : 0 < Y) :
    ∫ t, notchWindow L t * critDualWeight t Y * Complex.exp (-(ξ * t) * I) =
      (1 / (2 * Real.pi)) • ∫ v : ℝ, (∫ t, notchWindow L t *
          critCarrier t (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)) * Complex.exp (-(ξ * t) * I)) *
        smoothAFEMellinIntegrand Y (((1 : ℝ) : ℂ) + (v : ℂ) * I) := by
  have hL0 : 0 < L := by linarith
  set F : ℝ → ℝ → ℂ := fun t v => critCarrier t (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)) *
    smoothAFEMellinIntegrand Y (((1 : ℝ) : ℂ) + (v : ℂ) * I) with hFdef
  have hint := integrable_notch_mellin (ξ := ξ) hL0 (F := F) (continuous_dualMellin_uncurry hY)
    (integrable_one_add_abs_pow_mul_exp_neg_sq 2)
    (fun t ht v => norm_dualMellin_le hL hY ht)
  have hW : ∀ t, critDualWeight t Y = (1 / (2 * Real.pi)) • ∫ v, F t v := fun t => rfl
  simp_rw [hW]
  have hpt : ∀ t, notchWindow L t * ((1 / (2 * Real.pi)) • ∫ v, F t v) *
      Complex.exp (-(ξ * t) * I) =
      (1 / (2 * Real.pi)) • (notchWindow L t * (∫ v, F t v) * Complex.exp (-(ξ * t) * I)) := by
    intro t
    rw [Complex.real_smul, Complex.real_smul]
    ring
  simp_rw [hpt]
  rw [integral_smul, integral_notch_mul_integral_eq F hint]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [hFdef]
  rw [← integral_mul_const]
  congr 1
  funext t
  ring

/-- **Dual-line oscillation bound.** -/
theorem exists_norm_notchDualOscillation_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {L Y ξ : ℝ}, 16 ≤ L → 0 < Y → ξ ≠ 0 →
      ‖∫ t, notchWindow L t * critDualWeight t Y * Complex.exp (-(ξ * t) * I)‖ ≤
        C / Y * (L ^ 2 / |ξ| + L ^ 3 * Real.exp (-(L ^ 2) / 128)) := by
  set c₁ : ℝ := 9 * (4 * blockWindowConst 1 + 80) with hc₁
  set I₃ : ℝ := ∫ v : ℝ, (1 + |v|) ^ 3 * Real.exp (-(v ^ (2 : ℕ))) with hI₃
  have hc := blockWindowConst_nonneg 1
  have hI₃0 : 0 ≤ I₃ := integral_nonneg fun v => by positivity
  set C : ℝ := (1 / (2 * Real.pi)) * Real.exp 1 *
    (c₁ * I₃ + 18 * (Real.exp (2 ^ 2) * Real.sqrt (4 * Real.pi))) with hCdef
  refine ⟨C, by positivity, fun {L Y ξ} hL hY hξ => ?_⟩
  have hL0 : 0 < L := by linarith
  rw [integral_notch_critDualWeight_eq (by linarith) hY, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
  set inner : ℝ → ℂ := fun v : ℝ => ∫ t, notchWindow L t *
      critCarrier t (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)) * Complex.exp (-(ξ * t) * I) with hinner
  set S : Set ℝ := {v : ℝ | |v| ≤ L / 8} with hS
  have hSmeas : MeasurableSet Sᶜ :=
    (isClosed_le continuous_abs continuous_const).measurableSet.compl
  set g : ℝ → ℝ := fun v => (Y⁻¹ * Real.exp 1) *
    (c₁ * L ^ 2 / |ξ| * ((1 + |v|) ^ 3 * Real.exp (-(v ^ (2 : ℕ)))) +
      18 * L ^ 3 * Sᶜ.indicator (fun v => (1 + |v|) ^ 2 * Real.exp (-(v ^ (2 : ℕ)))) v) with hg
  have hgint : Integrable g := by
    have h1 := (integrable_one_add_abs_pow_mul_exp_neg_sq 3).const_mul (c₁ * L ^ 2 / |ξ|)
    have h2 := ((integrable_one_add_abs_pow_mul_exp_neg_sq 2).indicator hSmeas).const_mul
      (18 * L ^ 3)
    exact (h1.add h2).const_mul _
  have hpt : ∀ v, ‖inner v * smoothAFEMellinIntegrand Y (((1 : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤ g v := by
    intro v
    rw [norm_mul]
    have hm := norm_smoothAFEMellinIntegrand_vertical_le hY (show (0 : ℝ) < 1 by norm_num) v
    have hm' : ‖smoothAFEMellinIntegrand Y (((1 : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤
        (Y⁻¹ * Real.exp 1) * Real.exp (-(v ^ (2 : ℕ))) := by
      simpa [Real.rpow_neg_one] using hm
    have hinnerb : ‖inner v‖ ≤ c₁ * L ^ 2 / |ξ| * (1 + |v|) ^ 3 +
        18 * L ^ 3 * Sᶜ.indicator (fun v => (1 + |v|) ^ 2) v := by
      by_cases hv : |v| ≤ L / 8
      · have hb := norm_windowed_dual_le hL hv hξ
        have hnot : v ∉ Sᶜ := by simp [hS, hv]
        rw [indicator_of_notMem hnot, mul_zero, add_zero]
        refine hb.trans (le_of_eq ?_)
        rw [hc₁]
        ring
      · have hb := norm_windowed_dual_le_trivial (v := v) (ξ := ξ) hL
        have hmem : v ∈ Sᶜ := by simp [hS, hv]
        rw [indicator_of_mem hmem]
        have hnn : 0 ≤ c₁ * L ^ 2 / |ξ| * (1 + |v|) ^ 3 := by positivity
        linarith
    have hind : Sᶜ.indicator (fun v => (1 + |v|) ^ 2) v * Real.exp (-(v ^ (2 : ℕ))) =
        Sᶜ.indicator (fun v => (1 + |v|) ^ 2 * Real.exp (-(v ^ (2 : ℕ)))) v := by
      by_cases hv : v ∈ Sᶜ
      · rw [indicator_of_mem hv, indicator_of_mem hv]
      · rw [indicator_of_notMem hv, indicator_of_notMem hv, zero_mul]
    calc ‖inner v‖ * ‖smoothAFEMellinIntegrand Y (((1 : ℝ) : ℂ) + (v : ℂ) * I)‖
        ≤ (c₁ * L ^ 2 / |ξ| * (1 + |v|) ^ 3 +
            18 * L ^ 3 * Sᶜ.indicator (fun v => (1 + |v|) ^ 2) v) *
          ((Y⁻¹ * Real.exp 1) * Real.exp (-(v ^ (2 : ℕ)))) :=
          mul_le_mul hinnerb hm' (norm_nonneg _) (by
            have : 0 ≤ Sᶜ.indicator (fun v : ℝ => (1 + |v|) ^ 2) v :=
              indicator_nonneg (fun _ _ => by positivity) v
            positivity)
      _ = g v := by
          simp only [hg]
          rw [← hind]
          ring
  have hbound := norm_integral_le_of_norm_le hgint (Filter.Eventually.of_forall hpt)
  have hgval : ∫ v, g v ≤ (Y⁻¹ * Real.exp 1) * (c₁ * L ^ 2 / |ξ| * I₃ +
      18 * L ^ 3 * (Real.exp (2 ^ 2) * Real.exp (-(L / 8) ^ 2 / 2) * Real.sqrt (4 * Real.pi))) := by
    have htail := integral_one_add_abs_pow_mul_exp_neg_sq_compl_le 2 (V := L / 8) (by linarith)
    have hsplit : ∫ v, g v = (Y⁻¹ * Real.exp 1) * (c₁ * L ^ 2 / |ξ| * I₃ +
        18 * L ^ 3 * ∫ v in Sᶜ, (1 + |v|) ^ 2 * Real.exp (-(v ^ (2 : ℕ)))) := by
      simp only [hg]
      rw [integral_const_mul, integral_add, integral_const_mul, integral_const_mul,
        integral_indicator hSmeas]
      · exact (integrable_one_add_abs_pow_mul_exp_neg_sq 3).const_mul _
      · exact ((integrable_one_add_abs_pow_mul_exp_neg_sq 2).indicator hSmeas).const_mul _
    rw [hsplit]
    have htail' : ∫ v in Sᶜ, (1 + |v|) ^ 2 * Real.exp (-(v ^ (2 : ℕ))) ≤
        Real.exp (2 ^ 2) * Real.exp (-(L / 8) ^ 2 / 2) * Real.sqrt (4 * Real.pi) := by
      simpa using htail
    gcongr
  have hexp : Real.exp (-(L / 8) ^ 2 / 2) = Real.exp (-(L ^ 2) / 128) := by
    congr 1; ring
  rw [hexp] at hgval
  calc 1 / (2 * Real.pi) * ‖∫ v, inner v * smoothAFEMellinIntegrand Y (((1 : ℝ) : ℂ) + (v : ℂ) * I)‖
      ≤ 1 / (2 * Real.pi) * ((Y⁻¹ * Real.exp 1) * (c₁ * L ^ 2 / |ξ| * I₃ +
          18 * L ^ 3 * (Real.exp (2 ^ 2) * Real.exp (-(L ^ 2) / 128) *
            Real.sqrt (4 * Real.pi)))) :=
        mul_le_mul_of_nonneg_left (hbound.trans hgval) (by positivity)
    _ ≤ C / Y * (L ^ 2 / |ξ| + L ^ 3 * Real.exp (-(L ^ 2) / 128)) := by
        rw [hCdef]
        have hA : 0 ≤ L ^ 2 / |ξ| := by positivity
        have hB : 0 ≤ L ^ 3 * Real.exp (-(L ^ 2) / 128) := by positivity
        have hsq : 0 ≤ Real.exp (2 ^ 2) * Real.sqrt (4 * Real.pi) := by positivity
        have hc10 : 0 ≤ c₁ := by rw [hc₁]; positivity
        have key : c₁ * L ^ 2 / |ξ| * I₃ + 18 * L ^ 3 * (Real.exp (2 ^ 2) *
            Real.exp (-(L ^ 2) / 128) * Real.sqrt (4 * Real.pi)) ≤
            (c₁ * I₃ + 18 * (Real.exp (2 ^ 2) * Real.sqrt (4 * Real.pi))) *
              (L ^ 2 / |ξ| + L ^ 3 * Real.exp (-(L ^ 2) / 128)) := by
          have e1 : c₁ * L ^ 2 / |ξ| * I₃ = c₁ * I₃ * (L ^ 2 / |ξ|) := by ring
          have e2 : 18 * L ^ 3 * (Real.exp (2 ^ 2) * Real.exp (-(L ^ 2) / 128) *
              Real.sqrt (4 * Real.pi)) =
              18 * (Real.exp (2 ^ 2) * Real.sqrt (4 * Real.pi)) *
                (L ^ 3 * Real.exp (-(L ^ 2) / 128)) := by ring
          rw [e1, e2]
          nlinarith [mul_nonneg (mul_nonneg hc10 hI₃0) hB,
            mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 18) hsq) hA]
        calc 1 / (2 * Real.pi) * ((Y⁻¹ * Real.exp 1) * (c₁ * L ^ 2 / |ξ| * I₃ +
              18 * L ^ 3 * (Real.exp (2 ^ 2) * Real.exp (-(L ^ 2) / 128) *
                Real.sqrt (4 * Real.pi))))
            ≤ 1 / (2 * Real.pi) * ((Y⁻¹ * Real.exp 1) *
                ((c₁ * I₃ + 18 * (Real.exp (2 ^ 2) * Real.sqrt (4 * Real.pi))) *
                  (L ^ 2 / |ξ| + L ^ 3 * Real.exp (-(L ^ 2) / 128)))) := by
              gcongr
          _ = _ := by field_simp

/-! ## The right line -/

theorem neg_rightLine (v : ℝ) :
    -(((-rightAbscissa : ℝ) : ℂ) + (v : ℂ) * I) = ((rightAbscissa : ℝ) : ℂ) + ((-v : ℝ) : ℂ) * I := by
  push_cast; ring

theorem continuous_rightMellin_uncurry {Y : ℝ} (hY : 0 < Y) :
    Continuous (Function.uncurry fun t v : ℝ =>
      critCarrier t (-(((-rightAbscissa : ℝ) : ℂ) + (v : ℂ) * I)) *
        smoothAFEMellinIntegrand Y (((-rightAbscissa : ℝ) : ℂ) + (v : ℂ) * I)) := by
  have h1 := continuous_critCarrier_uncurry
    (w := fun v : ℝ => -(((-rightAbscissa : ℝ) : ℂ) + (v : ℂ) * I)) (by fun_prop)
    (fun t v => by rw [neg_rightLine]; exact gammaR_one_sub_right_ne_zero rightAbscissa_lt_half t v)
  have h2 : Continuous (fun p : ℝ × ℝ =>
      smoothAFEMellinIntegrand Y (((-rightAbscissa : ℝ) : ℂ) + (p.2 : ℂ) * I)) :=
    (continuous_smoothAFEMellinIntegrand_line (by linarith [rightAbscissa_pos]) hY).comp
      continuous_snd
  exact h1.mul h2

/-- The right-line Mellin integrand is `≤ K' Y^{1/4} e^{−v²}` uniformly in the height. -/
theorem exists_norm_rightMellin_le :
    ∃ K' : ℝ, 0 ≤ K' ∧ ∀ {Y : ℝ}, 0 < Y → ∀ t v : ℝ,
      ‖critCarrier t (-(((-rightAbscissa : ℝ) : ℂ) + (v : ℂ) * I)) *
          smoothAFEMellinIntegrand Y (((-rightAbscissa : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤
        K' * Y ^ rightAbscissa * Real.exp (-(v ^ (2 : ℕ))) := by
  obtain ⟨K', hK', hb⟩ := exists_norm_critDualIntegrand_neg_le rightAbscissa_pos
    rightAbscissa_lt_half
  refine ⟨K', hK', fun {Y} hY t v => (hb hY t v).trans ?_⟩
  have hden : 1 ≤ (max 1 |t - v|) ^ rightAbscissa * (max 1 |-t - v|) ^ rightAbscissa := by
    have h1 : 1 ≤ (max 1 |t - v|) ^ rightAbscissa :=
      Real.one_le_rpow (le_max_left _ _) rightAbscissa_pos.le
    have h2 : 1 ≤ (max 1 |-t - v|) ^ rightAbscissa :=
      Real.one_le_rpow (le_max_left _ _) rightAbscissa_pos.le
    nlinarith
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  exact div_le_self (by positivity) hden

theorem integrable_rightMellin {Y L ξ : ℝ} (hL : 0 < L) (hY : 0 < Y) :
    Integrable (Function.uncurry fun t (v : ℝ) =>
      notchWindow L t * (critCarrier t (-(((-rightAbscissa : ℝ) : ℂ) + (v : ℂ) * I)) *
        smoothAFEMellinIntegrand Y (((-rightAbscissa : ℝ) : ℂ) + (v : ℂ) * I)) *
      Complex.exp (-(ξ * t) * I)) (volume.prod volume) := by
  obtain ⟨K', hK', hb⟩ := exists_norm_rightMellin_le
  exact integrable_notch_mellin hL (continuous_rightMellin_uncurry hY)
    (A := K' * Y ^ rightAbscissa) (integrable_exp_neg_mul_sq (b := 1) (by norm_num))
    (fun t _ v => by
      refine (hb hY t v).trans (le_of_eq ?_)
      simp)

/-- **Residue form of the dual oscillation**: `J = ω̂ + (1/2π) ∫ (windowed right carrier)·M`. -/
theorem integral_notch_critDualWeight_eq_window_add {L Y ξ : ℝ} (hL : 0 < L) (hY : 0 < Y) :
    ∫ t, notchWindow L t * critDualWeight t Y * Complex.exp (-(ξ * t) * I) =
      (∫ t, notchWindow L t * Complex.exp (-(ξ * t) * I)) +
        (1 / (2 * Real.pi)) • ∫ v : ℝ, (∫ t, notchWindow L t *
            critCarrier t (-(((-rightAbscissa : ℝ) : ℂ) + (v : ℂ) * I)) *
              Complex.exp (-(ξ * t) * I)) *
          smoothAFEMellinIntegrand Y (((-rightAbscissa : ℝ) : ℂ) + (v : ℂ) * I) := by
  set F : ℝ → ℝ → ℂ := fun t v => critCarrier t (-(((-rightAbscissa : ℝ) : ℂ) + (v : ℂ) * I)) *
    smoothAFEMellinIntegrand Y (((-rightAbscissa : ℝ) : ℂ) + (v : ℂ) * I) with hFdef
  have hint := integrable_rightMellin (ξ := ξ) hL hY
  have hW : ∀ t, critDualWeight t Y = 1 + (1 / (2 * Real.pi)) • ∫ v, F t v := fun t =>
    critDualWeight_eq_one_add_at_neg rightAbscissa_pos rightAbscissa_lt_half hY t
  have hsplit : ∀ t, notchWindow L t * critDualWeight t Y * Complex.exp (-(ξ * t) * I) =
      notchWindow L t * Complex.exp (-(ξ * t) * I) +
        (1 / (2 * Real.pi)) • (notchWindow L t * (∫ v, F t v) * Complex.exp (-(ξ * t) * I)) := by
    intro t
    rw [hW, Complex.real_smul, Complex.real_smul]
    ring
  simp_rw [hsplit]
  have hωe : Integrable (fun t => notchWindow L t * Complex.exp (-(ξ * t) * I)) := by
    have hc : Continuous (fun t => notchWindow L t * Complex.exp (-(ξ * t) * I)) :=
      (continuous_notchWindow L).mul (by fun_prop)
    refine hc.integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.of_support_subset_isCompact (K := Icc (L / 2) (5 * L / 2))
      isCompact_Icc ?_
    intro t ht
    by_contra hnot
    exact ht (by simp only [notchWindow_eq_zero hL hnot, zero_mul])
  have hsecond : Integrable (fun t => notchWindow L t * (∫ v, F t v) * Complex.exp (-(ξ * t) * I)) := by
    have h := hint.integral_prod_left
    refine h.congr (Filter.Eventually.of_forall fun t => ?_)
    simp only [Function.uncurry_apply_pair]
    rw [← integral_const_mul, ← integral_mul_const]
  have hsecond' : Integrable (fun t => (1 / (2 * Real.pi)) •
      (notchWindow L t * (∫ v, F t v) * Complex.exp (-(ξ * t) * I))) :=
    hsecond.smul (1 / (2 * Real.pi))
  rw [integral_add hωe hsecond', integral_smul, integral_notch_mul_integral_eq F hint]
  congr 2
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [hFdef]
  rw [← integral_mul_const]
  congr 1
  funext t
  ring

/-- **Right-line oscillation bound.** -/
theorem exists_norm_notchDualOscillation_sub_window_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {L Y ξ : ℝ}, 16 ≤ L → 0 < Y → ξ ≠ 0 →
      ‖(∫ t, notchWindow L t * critDualWeight t Y * Complex.exp (-(ξ * t) * I)) -
          ∫ t, notchWindow L t * Complex.exp (-(ξ * t) * I)‖ ≤
        C * Y ^ rightAbscissa * (1 / Real.sqrt L / |ξ| + L * Real.exp (-(L ^ 2) / 128)) := by
  obtain ⟨K, hK, hcar⟩ := exists_norm_critCarrier_right_le rightAbscissa_pos rightAbscissa_lt_half
  have hc := blockWindowConst_nonneg 1
  set c₂ : ℝ := 2 * K * (4 * blockWindowConst 1 + 80) with hc₂
  set I₁ : ℝ := ∫ v : ℝ, (1 + |v|) ^ 1 * Real.exp (-(v ^ (2 : ℕ))) with hI₁
  have hI₁0 : 0 ≤ I₁ := integral_nonneg fun v => by positivity
  set E : ℝ := Real.exp (rightAbscissa ^ 2) / rightAbscissa with hE
  have hE0 : 0 ≤ E := by have := rightAbscissa_pos; positivity
  set C : ℝ := (1 / (2 * Real.pi)) * E *
    (c₂ * I₁ + 2 * K * (Real.exp ((0 : ℝ) ^ 2) * Real.sqrt (4 * Real.pi))) with hCdef
  refine ⟨C, by positivity, fun {L Y ξ} hL hY hξ => ?_⟩
  have hL0 : 0 < L := by linarith
  rw [integral_notch_critDualWeight_eq_window_add hL0 hY, add_sub_cancel_left, norm_smul,
    Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
  set inner : ℝ → ℂ := fun v : ℝ => ∫ t, notchWindow L t *
      critCarrier t (-(((-rightAbscissa : ℝ) : ℂ) + (v : ℂ) * I)) * Complex.exp (-(ξ * t) * I)
    with hinner
  set S : Set ℝ := {v : ℝ | |v| ≤ L / 8} with hS
  have hSmeas : MeasurableSet Sᶜ :=
    (isClosed_le continuous_abs continuous_const).measurableSet.compl
  have hsqrt : (L / 4) ^ rightAbscissa * (L / 4) ^ rightAbscissa = Real.sqrt L / 2 := by
    rw [← Real.rpow_add (by linarith), show rightAbscissa + rightAbscissa = 1 / 2 by
      unfold rightAbscissa; norm_num, ← Real.sqrt_eq_rpow, Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 4),
      show Real.sqrt 4 = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  have hsqL : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL0
  set g : ℝ → ℝ := fun v => (Y ^ rightAbscissa * E) *
    (c₂ / Real.sqrt L / |ξ| * ((1 + |v|) ^ 1 * Real.exp (-(v ^ (2 : ℕ)))) +
      2 * L * K * Sᶜ.indicator (fun v => (1 + |v|) ^ 0 * Real.exp (-(v ^ (2 : ℕ)))) v) with hg
  have hgint : Integrable g := by
    have h1 := (integrable_one_add_abs_pow_mul_exp_neg_sq 1).const_mul (c₂ / Real.sqrt L / |ξ|)
    have h2 := ((integrable_one_add_abs_pow_mul_exp_neg_sq 0).indicator hSmeas).const_mul
      (2 * L * K)
    exact (h1.add h2).const_mul _
  have hpt : ∀ v, ‖inner v *
      smoothAFEMellinIntegrand Y (((-rightAbscissa : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤ g v := by
    intro v
    rw [norm_mul]
    have hk := norm_smoothAFEGaussianKernel_vertical_le_of_ne (σ := -rightAbscissa)
      (by linarith [rightAbscissa_pos]) v
    have hpow : ‖(Y : ℂ) ^ (-(((-rightAbscissa : ℝ) : ℂ) + (v : ℂ) * I))‖ = Y ^ rightAbscissa := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hY]
      simp
    have hm : ‖smoothAFEMellinIntegrand Y (((-rightAbscissa : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤
        (Y ^ rightAbscissa * E) * Real.exp (-(v ^ (2 : ℕ))) := by
      unfold smoothAFEMellinIntegrand
      rw [norm_mul, hpow, hE]
      have hk' : ‖smoothAFEGaussianKernel (((-rightAbscissa : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤
          (Real.exp (rightAbscissa ^ 2) / rightAbscissa) * Real.exp (-(v ^ (2 : ℕ))) := by
        simpa [neg_sq, abs_neg, abs_of_pos rightAbscissa_pos] using hk
      calc Y ^ rightAbscissa * ‖smoothAFEGaussianKernel (((-rightAbscissa : ℝ) : ℂ) + (v : ℂ) * I)‖
          ≤ Y ^ rightAbscissa * ((Real.exp (rightAbscissa ^ 2) / rightAbscissa) *
              Real.exp (-(v ^ (2 : ℕ)))) :=
            mul_le_mul_of_nonneg_left hk' (by positivity)
        _ = _ := by ring
    have hinnerb : ‖inner v‖ ≤ c₂ / Real.sqrt L / |ξ| * (1 + |v|) +
        2 * L * K * Sᶜ.indicator (fun _ => (1 : ℝ)) v := by
      have hrw : ∀ t : ℝ, critCarrier t (-(((-rightAbscissa : ℝ) : ℂ) + (v : ℂ) * I)) =
          critCarrier t (((rightAbscissa : ℝ) : ℂ) + ((-v : ℝ) : ℂ) * I) := fun t => by
        rw [neg_rightLine]
      simp only [hinner, hrw]
      by_cases hv : |v| ≤ L / 8
      · have hb := norm_windowed_right_le hK hcar hL hv hξ
        have hnot : v ∉ Sᶜ := by simp [hS, hv]
        rw [indicator_of_notMem hnot, mul_zero, add_zero]
        refine hb.trans (le_of_eq ?_)
        rw [hsqrt, hc₂]
        field_simp
      · have hb := norm_windowed_right_le_trivial (v := v) (ξ := ξ) hK hcar hL
        have hmem : v ∈ Sᶜ := by simp [hS, hv]
        rw [indicator_of_mem hmem, mul_one]
        have hnn : 0 ≤ c₂ / Real.sqrt L / |ξ| * (1 + |v|) := by
          have : 0 ≤ c₂ := by rw [hc₂]; positivity
          positivity
        linarith
    have hind : Sᶜ.indicator (fun _ => (1 : ℝ)) v * Real.exp (-(v ^ (2 : ℕ))) =
        Sᶜ.indicator (fun v => (1 + |v|) ^ 0 * Real.exp (-(v ^ (2 : ℕ)))) v := by
      by_cases hv : v ∈ Sᶜ
      · rw [indicator_of_mem hv, indicator_of_mem hv, pow_zero]
      · rw [indicator_of_notMem hv, indicator_of_notMem hv, zero_mul]
    have hc₂0 : 0 ≤ c₂ := by rw [hc₂]; positivity
    calc ‖inner v‖ * ‖smoothAFEMellinIntegrand Y (((-rightAbscissa : ℝ) : ℂ) + (v : ℂ) * I)‖
        ≤ (c₂ / Real.sqrt L / |ξ| * (1 + |v|) +
            2 * L * K * Sᶜ.indicator (fun _ => (1 : ℝ)) v) *
          ((Y ^ rightAbscissa * E) * Real.exp (-(v ^ (2 : ℕ)))) :=
          mul_le_mul hinnerb hm (norm_nonneg _) (by
            have : 0 ≤ Sᶜ.indicator (fun _ : ℝ => (1 : ℝ)) v :=
              indicator_nonneg (fun _ _ => by positivity) v
            positivity)
      _ = g v := by
          simp only [hg]
          rw [← hind, pow_one]
          ring
  have hbound := norm_integral_le_of_norm_le hgint (Filter.Eventually.of_forall hpt)
  have hgval : ∫ v, g v ≤ (Y ^ rightAbscissa * E) * (c₂ / Real.sqrt L / |ξ| * I₁ +
      2 * L * K * (Real.exp ((0 : ℝ) ^ 2) * Real.exp (-(L / 8) ^ 2 / 2) *
        Real.sqrt (4 * Real.pi))) := by
    have htail := integral_one_add_abs_pow_mul_exp_neg_sq_compl_le 0 (V := L / 8) (by linarith)
    have hsplit : ∫ v, g v = (Y ^ rightAbscissa * E) * (c₂ / Real.sqrt L / |ξ| * I₁ +
        2 * L * K * ∫ v in Sᶜ, (1 + |v|) ^ 0 * Real.exp (-(v ^ (2 : ℕ)))) := by
      simp only [hg]
      rw [integral_const_mul, integral_add, integral_const_mul, integral_const_mul,
        integral_indicator hSmeas]
      · exact (integrable_one_add_abs_pow_mul_exp_neg_sq 1).const_mul _
      · exact ((integrable_one_add_abs_pow_mul_exp_neg_sq 0).indicator hSmeas).const_mul _
    rw [hsplit]
    have htail' : ∫ v in Sᶜ, (1 + |v|) ^ 0 * Real.exp (-(v ^ (2 : ℕ))) ≤
        Real.exp ((0 : ℝ) ^ 2) * Real.exp (-(L / 8) ^ 2 / 2) * Real.sqrt (4 * Real.pi) := by
      simpa using htail
    gcongr
  have hexp : Real.exp (-(L / 8) ^ 2 / 2) = Real.exp (-(L ^ 2) / 128) := by
    congr 1; ring
  rw [hexp] at hgval
  have hc₂0 : 0 ≤ c₂ := by rw [hc₂]; positivity
  calc 1 / (2 * Real.pi) * ‖∫ v : ℝ, inner v *
        smoothAFEMellinIntegrand Y (((-rightAbscissa : ℝ) : ℂ) + (v : ℂ) * I)‖
      ≤ 1 / (2 * Real.pi) * ((Y ^ rightAbscissa * E) * (c₂ / Real.sqrt L / |ξ| * I₁ +
          2 * L * K * (Real.exp ((0 : ℝ) ^ 2) * Real.exp (-(L ^ 2) / 128) *
            Real.sqrt (4 * Real.pi)))) :=
        mul_le_mul_of_nonneg_left (hbound.trans hgval) (by positivity)
    _ ≤ C * Y ^ rightAbscissa * (1 / Real.sqrt L / |ξ| + L * Real.exp (-(L ^ 2) / 128)) := by
        rw [hCdef]
        have hA : 0 ≤ 1 / Real.sqrt L / |ξ| := by positivity
        have hB : 0 ≤ L * Real.exp (-(L ^ 2) / 128) := by positivity
        have hsq : 0 ≤ Real.exp ((0 : ℝ) ^ 2) * Real.sqrt (4 * Real.pi) := by positivity
        have hY0 : 0 ≤ Y ^ rightAbscissa := by positivity
        have key : c₂ / Real.sqrt L / |ξ| * I₁ + 2 * L * K * (Real.exp ((0 : ℝ) ^ 2) *
            Real.exp (-(L ^ 2) / 128) * Real.sqrt (4 * Real.pi)) ≤
            (c₂ * I₁ + 2 * K * (Real.exp ((0 : ℝ) ^ 2) * Real.sqrt (4 * Real.pi))) *
              (1 / Real.sqrt L / |ξ| + L * Real.exp (-(L ^ 2) / 128)) := by
          have e1 : c₂ / Real.sqrt L / |ξ| * I₁ = c₂ * I₁ * (1 / Real.sqrt L / |ξ|) := by ring
          have e2 : 2 * L * K * (Real.exp ((0 : ℝ) ^ 2) * Real.exp (-(L ^ 2) / 128) *
              Real.sqrt (4 * Real.pi)) = 2 * K * (Real.exp ((0 : ℝ) ^ 2) *
                Real.sqrt (4 * Real.pi)) * (L * Real.exp (-(L ^ 2) / 128)) := by ring
          rw [e1, e2]
          nlinarith [mul_nonneg (mul_nonneg hc₂0 hI₁0) hB,
            mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * K) hsq) hA]
        calc 1 / (2 * Real.pi) * ((Y ^ rightAbscissa * E) * (c₂ / Real.sqrt L / |ξ| * I₁ +
              2 * L * K * (Real.exp ((0 : ℝ) ^ 2) * Real.exp (-(L ^ 2) / 128) *
                Real.sqrt (4 * Real.pi))))
            ≤ 1 / (2 * Real.pi) * ((Y ^ rightAbscissa * E) *
                ((c₂ * I₁ + 2 * K * (Real.exp ((0 : ℝ) ^ 2) * Real.sqrt (4 * Real.pi))) *
                  (1 / Real.sqrt L / |ξ| + L * Real.exp (-(L ^ 2) / 128)))) := by
              gcongr
          _ = _ := by ring

end RHTower.ZetaNotch
