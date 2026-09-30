import GaloisForLFunctions.RHTower.ZetaLogDerivSelbergExplicitFormulaHeight
import GaloisForLFunctions.RHTower.Sieve.ZetaResidueUnitGlobalZeroCount

/-!
# The zero sum of Selberg's explicit formula at typical heights

Let `x > 1`, `ℓ = log x`, `R > 0`, and let `s` lie in the box `Re s ≥ ½ + 3R/4`,
`|Im s − t| ≤ 6R`. The zeros `w` of the explicit formula at height `t` split into

* **left zeros** `Re w ≤ ½ + R/2`: `‖K_x(w − s)‖ ≤ 2 x^{−R/4}/ℓ · 1153/((R/4)² + (Im w − t)²)`, so their
  sum is dominated by a Lorentzian sum over a fixed finite set of zeros
  (`sum_left_selbergKernel_le`), whose integral over any height window is `≤ (4π/R) × multiplicity`
  (`integral_selbergLorentzSum_le`);
* **right zeros** `Re w > ½ + R/2`: outside the windows `|Im w − t| ≤ W(w) = 12R x^{3(Re w − ½)}`,
  `‖K_x(w − s)‖ ≤ 16 x^{2(Re w−½)}/(ℓ (W(w)² + (Im w − t)²))` (`sum_right_selbergKernel_le`), whose
  integral is `≤ (4π/(3Rℓ)) x^{−(Re w − ½)}` per zero (`integral_selbergRightFar_le`); the windows
  themselves have total length `≤ Σ 2W(w)` (`volume_selbergRightExceptional_le`).

All zeros at heights in `[T, 2T]` lie in one fixed rectangle (`selbergHeightZeros_subset_mid`),
whose multiplicity is `O(T log T)` (`exists_sum_mult_selbergMidZeros_le`).
-/

noncomputable section

open Complex Set MeasureTheory Filter

namespace RHTower

open Sieve

/-- Multiplicity of a residue-unit zero. -/
def zeroMult (w : ℂ) : ℝ := ((analyticOrderAt zetaResidueUnit w).toNat : ℝ)

theorem zeroMult_nonneg (w : ℂ) : 0 ≤ zeroMult w := Nat.cast_nonneg _

/-- **Markov's inequality on an interval** for a continuous nonnegative function. -/
theorem volume_Icc_setOf_le_le_of_integral {f : ℝ → ℝ} {a b c I₀ : ℝ} (hab : a ≤ b) (hc : 0 < c)
    (hf0 : ∀ t, 0 ≤ f t) (hfc : Continuous f) (hI : ∫ t in a..b, f t ≤ I₀) :
    volume {t | t ∈ Icc a b ∧ c ≤ f t} ≤ ENNReal.ofReal (I₀ / c) := by
  have hfi : Integrable f (volume.restrict (Ioc a b)) :=
    (hfc.intervalIntegrable a b |>.def' |>.mono_set (by rw [uIoc_of_le hab]))
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ := volume.restrict (Ioc a b))
    (Eventually.of_forall hf0) hfi c
  rw [← intervalIntegral.integral_of_le hab] at hmark
  have hfin : volume.restrict (Ioc a b) {t | c ≤ f t} ≠ ⊤ :=
    measure_ne_top_of_subset (Set.subset_univ _) (by
      rw [Measure.restrict_apply_univ, Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hsub : {t | t ∈ Icc a b ∧ c ≤ f t} ⊆ ({t | c ≤ f t} ∩ Ioc a b) ∪ {a} := by
    rintro t ⟨ht, hct⟩
    rcases eq_or_lt_of_le ht.1 with h | h
    · right; exact h.symm
    · left; exact ⟨hct, h, ht.2⟩
  calc volume {t | t ∈ Icc a b ∧ c ≤ f t}
      ≤ volume ({t | c ≤ f t} ∩ Ioc a b) + volume ({a} : Set ℝ) :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ = ENNReal.ofReal ((volume.restrict (Ioc a b)).real {t | c ≤ f t}) := by
        rw [Real.volume_singleton, add_zero, Measure.real, ENNReal.ofReal_toReal hfin,
          Measure.restrict_apply' measurableSet_Ioc]
    _ ≤ ENNReal.ofReal (I₀ / c) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [le_div_iff₀ hc, mul_comm]
        exact hmark.trans hI

/-! ## A fixed rectangle for all heights in `[T, 2T]` -/

/-- The zeros of the residue unit in `[σ_L(4T), 4] × [T/2 − 1, 3T + 1]`. -/
def selbergMidZeros (T : ℝ) : Finset ℂ :=
  zetaResidueUnitClosedRectangleZeros ((reflectedLeftAbscissa (4 * T) : ℂ) + (T / 2 - 1 : ℝ) * I)
    ((4 : ℂ) + (3 * T + 1 : ℝ) * I)

theorem reflectedLeftAbscissa_antitone {T T' : ℝ} (hT : 16 ≤ T) (hTT : T ≤ T') :
    reflectedLeftAbscissa T' ≤ reflectedLeftAbscissa T := by
  have hl := log_ge_of_sixteen_le hT
  have hl' : Real.log T ≤ Real.log T' := Real.log_le_log (by linarith) hTT
  unfold reflectedLeftAbscissa
  apply div_le_div_of_nonneg_left zetaLowerA_pos.le (by positivity)
  have := pow_le_pow_left₀ (by linarith) hl' 9
  linarith

theorem selbergHeightZeros_subset_mid {T t T₁ T₂ : ℝ} (hT : 16 ≤ T) (ht : t ∈ Icc T (2 * T))
    (h1 : t / 2 - 1 < T₁) (h2 : T₂ < 3 * t / 2 + 1) (h12 : T₁ ≤ T₂) :
    selbergHeightZeros t T₁ T₂ ⊆ selbergMidZeros T := by
  intro w hw
  rw [selbergHeightZeros, mem_zetaResidueUnitClosedRectangleZeros] at hw
  rw [selbergMidZeros, mem_zetaResidueUnitClosedRectangleZeros]
  refine ⟨?_, hw.2⟩
  obtain ⟨hre, him⟩ := Complex.mem_reProdIm.mp hw.1
  have hσ : reflectedLeftAbscissa (4 * T) ≤ reflectedLeftAbscissa (2 * t) :=
    reflectedLeftAbscissa_antitone (by linarith [ht.1]) (by linarith [ht.2])
  have hσ2 : reflectedLeftAbscissa (2 * t) ≤ 2 := by
    have := reflectedLeftAbscissa_le (show 16 ≤ 2 * t by linarith [ht.1])
    have hl := log_ge_of_sixteen_le (show 16 ≤ 2 * t by linarith [ht.1])
    have : 1 / (8 * Real.log (2 * t) ^ (9 : ℕ)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (2 : ℝ) ^ 9 ≤ Real.log (2 * t) ^ (9 : ℕ) := pow_le_pow_left₀ (by norm_num) hl 9
      linarith
    linarith
  have e1 : ((reflectedLeftAbscissa (4 * T) : ℂ) + ((T / 2 - 1 : ℝ) : ℂ) * I).re =
      reflectedLeftAbscissa (4 * T) := by simp
  have e2 : ((4 : ℂ) + ((3 * T + 1 : ℝ) : ℂ) * I).re = 4 := by simp
  have e3 : ((reflectedLeftAbscissa (4 * T) : ℂ) + ((T / 2 - 1 : ℝ) : ℂ) * I).im = T / 2 - 1 := by
    simp
  have e4 : ((4 : ℂ) + ((3 * T + 1 : ℝ) : ℂ) * I).im = 3 * T + 1 := by simp
  have f1 : ((reflectedLeftAbscissa (2 * t) : ℂ) + (T₁ : ℂ) * I).re =
      reflectedLeftAbscissa (2 * t) := by simp
  have f2 : (((2 : ℝ) : ℂ) + (T₂ : ℂ) * I).re = 2 := by simp
  have f3 : ((reflectedLeftAbscissa (2 * t) : ℂ) + (T₁ : ℂ) * I).im = T₁ := by simp
  have f4 : (((2 : ℝ) : ℂ) + (T₂ : ℂ) * I).im = T₂ := by simp
  rw [f1, f2] at hre
  rw [f3, f4] at him
  refine Complex.mem_reProdIm.mpr ⟨?_, ?_⟩
  · rw [e1, e2, uIcc_of_le (by linarith)]
    rw [uIcc_of_le hσ2] at hre
    exact ⟨hσ.trans hre.1, by linarith [hre.2]⟩
  · rw [e3, e4, uIcc_of_le (by linarith)]
    rw [uIcc_of_le h12] at him
    exact ⟨by linarith [him.1, ht.1], by linarith [him.2, ht.2]⟩

/-- The multiplicity of the fixed rectangle is `O(T log T)`. -/
theorem exists_sum_mult_selbergMidZeros_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 16 ≤ T →
      ∑ w ∈ selbergMidZeros T, zeroMult w ≤ C * (4 * T + 4) * Real.log (4 * T + 5) := by
  obtain ⟨C, hC, hcount⟩ := exists_zetaResidueUnitClosedRectangleMultiplicity_le_global
  refine ⟨C, hC, fun T hT => ?_⟩
  have h4T : 16 ≤ 4 * T := by linarith
  have hc0 := reflectedLeftAbscissa_pos h4T
  have hc1 : reflectedLeftAbscissa (4 * T) ≤ 1 := by
    have := reflectedLeftAbscissa_le h4T
    have hl := log_ge_of_sixteen_le h4T
    have : 1 / (8 * Real.log (4 * T) ^ (9 : ℕ)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (2 : ℝ) ^ 9 ≤ Real.log (4 * T) ^ (9 : ℕ) := pow_le_pow_left₀ (by norm_num) hl 9
      linarith
    linarith
  have h := hcount (c := reflectedLeftAbscissa (4 * T)) (T := 4 * T) hc0 hc1 (by linarith)
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun w _ _ => zeroMult_nonneg w) h
  intro w hw
  rw [selbergMidZeros, mem_zetaResidueUnitClosedRectangleZeros] at hw
  rw [mem_zetaResidueUnitClosedRectangleZeros]
  refine ⟨?_, hw.2⟩
  obtain ⟨hre, him⟩ := Complex.mem_reProdIm.mp hw.1
  refine Complex.mem_reProdIm.mpr ⟨?_, ?_⟩
  · simpa using hre
  · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, Complex.im_ofNat] at him ⊢
    rw [uIcc_of_le (by linarith)] at him ⊢
    exact ⟨by linarith [him.1], by linarith [him.2]⟩

/-! ## Left zeros: Lorentzian domination -/

/-- The Lorentzian sum `Σ_w m_w/(u² + (Im w − t)²)`. -/
def selbergLorentzSum (Z : Finset ℂ) (u t : ℝ) : ℝ :=
  ∑ w ∈ Z, zeroMult w * (u ^ 2 + (w.im - t) ^ 2)⁻¹

theorem selbergLorentzSum_nonneg (Z : Finset ℂ) (u t : ℝ) : 0 ≤ selbergLorentzSum Z u t :=
  Finset.sum_nonneg fun w _ => mul_nonneg (zeroMult_nonneg w) (by positivity)

theorem continuous_lorentz_term {u : ℝ} (hu : 0 < u) (γ : ℝ) :
    Continuous fun t : ℝ => (u ^ 2 + (γ - t) ^ 2)⁻¹ :=
  (continuous_const.add ((continuous_const.sub continuous_id).pow 2)).inv₀
    fun t => (by positivity : (0 : ℝ) < u ^ 2 + (γ - t) ^ 2).ne'

theorem continuous_selbergLorentzSum (Z : Finset ℂ) {u : ℝ} (hu : 0 < u) :
    Continuous (selbergLorentzSum Z u) := by
  unfold selbergLorentzSum
  exact continuous_finsetSum _ fun w _ => continuous_const.mul (continuous_lorentz_term hu w.im)

theorem integral_selbergLorentzSum_le (Z : Finset ℂ) {u : ℝ} (hu : 0 < u) {T₁ T₂ : ℝ}
    (hT : T₁ ≤ T₂) :
    ∫ t in T₁..T₂, selbergLorentzSum Z u t ≤ Real.pi / u * ∑ w ∈ Z, zeroMult w := by
  unfold selbergLorentzSum
  rw [intervalIntegral.integral_finsetSum
    (f := fun w t => zeroMult w * (u ^ 2 + (w.im - t) ^ 2)⁻¹) (fun w _ =>
      (continuous_const.mul (continuous_lorentz_term hu w.im)).intervalIntegrable _ _)]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun w _ => ?_
  rw [intervalIntegral.integral_const_mul]
  have h := integral_lorentz_window_le hu w.im hT
  have e : ∀ t : ℝ, (u ^ 2 + (w.im - t) ^ 2)⁻¹ = (u ^ 2 + (t - w.im) ^ 2)⁻¹ := by
    intro t; ring_nf
  simp_rw [e]
  have := mul_le_mul_of_nonneg_left h (zeroMult_nonneg w)
  linarith

/-- **The left zeros are dominated by a Lorentzian sum.** -/
theorem sum_left_selbergKernel_le {x R t : ℝ} {s : ℂ} (hx : 1 < x) (hR : 0 < R)
    (hs : 1 / 2 + 3 * R / 4 ≤ s.re) (hst : |s.im - t| ≤ 6 * R) {Z Z' : Finset ℂ} (hZ : Z ⊆ Z') :
    ∑ w ∈ Z.filter (fun w => w.re ≤ 1 / 2 + R / 2), zeroMult w * ‖selbergKernel x (w - s)‖ ≤
      2 * Real.exp (-(R / 4) * Real.log x) / Real.log x * 1153 *
        selbergLorentzSum Z' (R / 4) t := by
  have hl : 0 < Real.log x := Real.log_pos hx
  set c : ℝ := 2 * Real.exp (-(R / 4) * Real.log x) / Real.log x * 1153 with hc
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hpt : ∀ w ∈ Z.filter (fun w => w.re ≤ 1 / 2 + R / 2),
      zeroMult w * ‖selbergKernel x (w - s)‖ ≤ c * (zeroMult w * ((R / 4) ^ 2 + (w.im - t) ^ 2)⁻¹) := by
    intro w hw
    have hwre := (Finset.mem_filter.mp hw).2
    have hre : (w - s).re ≤ -(R / 4) := by simp; linarith
    have hK := norm_selbergKernel_le_line hx (w - s)
    have hexp : Real.exp (2 * (w - s).re * Real.log x) + Real.exp ((w - s).re * Real.log x) ≤
        2 * Real.exp (-(R / 4) * Real.log x) := by
      have h1 : Real.exp (2 * (w - s).re * Real.log x) ≤ Real.exp (-(R / 4) * Real.log x) :=
        Real.exp_le_exp.mpr (by nlinarith)
      have h2 : Real.exp ((w - s).re * Real.log x) ≤ Real.exp (-(R / 4) * Real.log x) :=
        Real.exp_le_exp.mpr (by nlinarith)
      linarith
    have him : (w - s).im = w.im - s.im := by simp
    have hlor : ((R / 4) ^ 2 + (w.im - t) ^ 2) ≤ 1153 * ((w - s).re ^ 2 + (w - s).im ^ 2) := by
      rw [him]
      have hre2 : (R / 4) ^ 2 ≤ (w - s).re ^ 2 := by nlinarith
      have hst' := abs_le.mp hst
      nlinarith [sq_nonneg (w.im - s.im + (s.im - t)), sq_nonneg (w.im - s.im - (s.im - t))]
    have hpos1 : 0 < (R / 4) ^ 2 + (w.im - t) ^ 2 := by positivity
    have hpos2 : 0 < (w - s).re ^ 2 + (w - s).im ^ 2 := by nlinarith
    have hKb : ‖selbergKernel x (w - s)‖ ≤
        2 * Real.exp (-(R / 4) * Real.log x) / Real.log x * 1153 *
          ((R / 4) ^ 2 + (w.im - t) ^ 2)⁻¹ := by
      have hDP : ((R / 4) ^ 2 + (w.im - t) ^ 2) / 1153 ≤ (w - s).re ^ 2 + (w - s).im ^ 2 := by
        linarith
      calc ‖selbergKernel x (w - s)‖
          ≤ (Real.exp (2 * (w - s).re * Real.log x) + Real.exp ((w - s).re * Real.log x)) /
              (Real.log x * ((w - s).re ^ 2 + (w - s).im ^ 2)) := hK
        _ ≤ 2 * Real.exp (-(R / 4) * Real.log x) /
              (Real.log x * ((w - s).re ^ 2 + (w - s).im ^ 2)) :=
            div_le_div_of_nonneg_right hexp (by positivity)
        _ ≤ 2 * Real.exp (-(R / 4) * Real.log x) /
              (Real.log x * (((R / 4) ^ 2 + (w.im - t) ^ 2) / 1153)) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity)
              (mul_le_mul_of_nonneg_left hDP hl.le)
        _ = 2 * Real.exp (-(R / 4) * Real.log x) / Real.log x * 1153 *
              ((R / 4) ^ 2 + (w.im - t) ^ 2)⁻¹ := by
            field_simp
    calc zeroMult w * ‖selbergKernel x (w - s)‖ ≤ zeroMult w * (c * ((R / 4) ^ 2 + (w.im - t) ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left hKb (zeroMult_nonneg w)
      _ = c * (zeroMult w * ((R / 4) ^ 2 + (w.im - t) ^ 2)⁻¹) := by ring
  calc ∑ w ∈ Z.filter (fun w => w.re ≤ 1 / 2 + R / 2), zeroMult w * ‖selbergKernel x (w - s)‖
      ≤ ∑ w ∈ Z.filter (fun w => w.re ≤ 1 / 2 + R / 2),
          c * (zeroMult w * ((R / 4) ^ 2 + (w.im - t) ^ 2)⁻¹) := Finset.sum_le_sum hpt
    _ = c * ∑ w ∈ Z.filter (fun w => w.re ≤ 1 / 2 + R / 2),
          zeroMult w * ((R / 4) ^ 2 + (w.im - t) ^ 2)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ c * selbergLorentzSum Z' (R / 4) t := by
        refine mul_le_mul_of_nonneg_left ?_ hc0
        unfold selbergLorentzSum
        exact Finset.sum_le_sum_of_subset_of_nonneg ((Finset.filter_subset _ _).trans hZ)
          fun w _ _ => mul_nonneg (zeroMult_nonneg w) (by positivity)

/-! ## Right zeros: exclusion windows -/

/-- The exclusion window `W(w) = 12R x^{3(Re w − ½)}`. -/
def selbergRightWindow (x R : ℝ) (w : ℂ) : ℝ :=
  12 * R * Real.exp (3 * (w.re - 1 / 2) * Real.log x)

/-- The far-right majorant `Σ_w m_w · 16 x^{2(Re w−½)}/(ℓ (W(w)² + (Im w − t)²))`. -/
def selbergRightFar (Z : Finset ℂ) (x R t : ℝ) : ℝ :=
  ∑ w ∈ Z.filter (fun w => 1 / 2 + R / 2 < w.re), zeroMult w *
    (16 * Real.exp (2 * (w.re - 1 / 2) * Real.log x) / Real.log x) *
      (selbergRightWindow x R w ^ 2 + (w.im - t) ^ 2)⁻¹

theorem selbergRightWindow_pos {x R : ℝ} (hR : 0 < R) (w : ℂ) : 0 < selbergRightWindow x R w := by
  unfold selbergRightWindow; positivity

theorem selbergRightWindow_ge {x R : ℝ} (hx : 1 < x) (hR : 0 < R) {w : ℂ} (hw : 1 / 2 ≤ w.re) :
    12 * R ≤ selbergRightWindow x R w := by
  unfold selbergRightWindow
  have hl := Real.log_pos hx
  have : 1 ≤ Real.exp (3 * (w.re - 1 / 2) * Real.log x) := Real.one_le_exp (by nlinarith)
  nlinarith

/-- **The right zeros outside their windows are dominated by the far majorant.** -/
theorem sum_right_selbergKernel_le {x R t : ℝ} {s : ℂ} (hx : 1 < x) (hR : 0 < R)
    (hs : 1 / 2 ≤ s.re) (hst : |s.im - t| ≤ 6 * R) {Z Z' : Finset ℂ} (hZ : Z ⊆ Z')
    (hgood : ∀ w ∈ Z', 1 / 2 + R / 2 < w.re → selbergRightWindow x R w < |w.im - t|) :
    ∑ w ∈ Z.filter (fun w => 1 / 2 + R / 2 < w.re), zeroMult w * ‖selbergKernel x (w - s)‖ ≤
      selbergRightFar Z' x R t := by
  have hl : 0 < Real.log x := Real.log_pos hx
  have hpt : ∀ w ∈ Z.filter (fun w => 1 / 2 + R / 2 < w.re),
      zeroMult w * ‖selbergKernel x (w - s)‖ ≤ zeroMult w *
        (16 * Real.exp (2 * (w.re - 1 / 2) * Real.log x) / Real.log x) *
          (selbergRightWindow x R w ^ 2 + (w.im - t) ^ 2)⁻¹ := by
    intro w hw
    have hwre := (Finset.mem_filter.mp hw).2
    have hwZ' := hZ (Finset.mem_filter.mp hw).1
    have hW := hgood w hwZ' hwre
    have hW12 := selbergRightWindow_ge hx hR (show 1 / 2 ≤ w.re by linarith)
    have hWpos := selbergRightWindow_pos (x := x) hR w
    set b : ℝ := w.re - 1 / 2 with hb
    have hb0 : 0 ≤ b := by rw [hb]; linarith
    set W : ℝ := selbergRightWindow x R w with hWdef
    have hgt : 12 * R < |w.im - t| := lt_of_le_of_lt hW12 hW
    have hst' := abs_le.mp hst
    have hv : |w.im - t| / 2 ≤ |(w - s).im| := by
      have him : (w - s).im = (w.im - t) - (s.im - t) := by simp
      rw [him]
      have := abs_sub_abs_le_abs_sub (w.im - t) (s.im - t)
      have h6 : |s.im - t| ≤ 6 * R := hst
      linarith
    have hK := norm_selbergKernel_le_line hx (w - s)
    have hre : (w - s).re ≤ b := by simp [hb]; linarith
    have hexp : Real.exp (2 * (w - s).re * Real.log x) + Real.exp ((w - s).re * Real.log x) ≤
        2 * Real.exp (2 * b * Real.log x) := by
      have h1 : Real.exp (2 * (w - s).re * Real.log x) ≤ Real.exp (2 * b * Real.log x) :=
        Real.exp_le_exp.mpr (by nlinarith)
      have h2 : Real.exp ((w - s).re * Real.log x) ≤ Real.exp (2 * b * Real.log x) :=
        Real.exp_le_exp.mpr (by nlinarith)
      linarith
    have hv2 : (w.im - t) ^ 2 / 4 ≤ (w - s).re ^ 2 + (w - s).im ^ 2 := by
      have h1 : (|w.im - t| / 2) ^ 2 ≤ |(w - s).im| ^ 2 :=
        pow_le_pow_left₀ (by positivity) hv 2
      rw [div_pow, sq_abs, sq_abs] at h1
      nlinarith [sq_nonneg (w - s).re]
    have hq : W ^ 2 + (w.im - t) ^ 2 ≤ 2 * (w.im - t) ^ 2 := by
      have h1 : W ^ 2 ≤ |w.im - t| ^ 2 := pow_le_pow_left₀ hWpos.le hW.le 2
      rw [sq_abs] at h1
      linarith
    have hpos : 0 < (w.im - t) ^ 2 := by
      have : 0 < |w.im - t| := by linarith
      rw [← sq_abs]; positivity
    have hKb : ‖selbergKernel x (w - s)‖ ≤
        16 * Real.exp (2 * b * Real.log x) / Real.log x * (W ^ 2 + (w.im - t) ^ 2)⁻¹ := by
      calc ‖selbergKernel x (w - s)‖
          ≤ (Real.exp (2 * (w - s).re * Real.log x) + Real.exp ((w - s).re * Real.log x)) /
              (Real.log x * ((w - s).re ^ 2 + (w - s).im ^ 2)) := hK
        _ ≤ 2 * Real.exp (2 * b * Real.log x) / (Real.log x * ((w.im - t) ^ 2 / 4)) := by
            apply div_le_div₀ (by positivity) hexp (by positivity)
            exact mul_le_mul_of_nonneg_left hv2 hl.le
        _ ≤ 2 * Real.exp (2 * b * Real.log x) / (Real.log x * ((W ^ 2 + (w.im - t) ^ 2) / 8)) := by
            apply div_le_div_of_nonneg_left (by positivity) (by positivity)
            exact mul_le_mul_of_nonneg_left (by linarith) hl.le
        _ = 16 * Real.exp (2 * b * Real.log x) / Real.log x * (W ^ 2 + (w.im - t) ^ 2)⁻¹ := by
            field_simp
            ring
    have := mul_le_mul_of_nonneg_left hKb (zeroMult_nonneg w)
    rw [hWdef, hb] at this
    calc zeroMult w * ‖selbergKernel x (w - s)‖ ≤ _ := this
      _ = _ := by ring
  refine (Finset.sum_le_sum hpt).trans ?_
  unfold selbergRightFar
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun w _ _ => ?_
  · intro w hw
    rw [Finset.mem_filter] at hw ⊢
    exact ⟨hZ hw.1, hw.2⟩
  · have := zeroMult_nonneg w
    have := selbergRightWindow_pos (x := x) hR w
    positivity

/-- **The exclusion windows are short in total.** -/
theorem volume_selbergRightExceptional_le (Z : Finset ℂ) {x R T : ℝ} (hR : 0 < R) :
    volume {t | t ∈ Icc T (2 * T) ∧ ∃ w ∈ Z, 1 / 2 + R / 2 < w.re ∧
        |w.im - t| ≤ selbergRightWindow x R w} ≤
      ENNReal.ofReal (∑ w ∈ Z.filter (fun w => 1 / 2 + R / 2 < w.re),
        2 * selbergRightWindow x R w) := by
  have hsub : {t | t ∈ Icc T (2 * T) ∧ ∃ w ∈ Z, 1 / 2 + R / 2 < w.re ∧
        |w.im - t| ≤ selbergRightWindow x R w} ⊆
      ⋃ w ∈ Z.filter (fun w => 1 / 2 + R / 2 < w.re),
        Icc (w.im - selbergRightWindow x R w) (w.im + selbergRightWindow x R w) := by
    rintro t ⟨-, w, hwZ, hwre, hwt⟩
    refine mem_iUnion₂.mpr ⟨w, Finset.mem_filter.mpr ⟨hwZ, hwre⟩, ?_⟩
    have := abs_le.mp hwt
    exact ⟨by linarith, by linarith⟩
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  rw [ENNReal.ofReal_sum_of_nonneg fun w _ => by
    have := selbergRightWindow_pos (x := x) hR w; positivity]
  refine Finset.sum_le_sum fun w _ => ?_
  rw [Real.volume_Icc]
  exact le_of_eq (by congr 1; ring)

theorem continuous_selbergRightFar (Z : Finset ℂ) {x R : ℝ} (hR : 0 < R) :
    Continuous (selbergRightFar Z x R) := by
  unfold selbergRightFar
  refine continuous_finsetSum _ fun w _ => continuous_const.mul ?_
  have hW := selbergRightWindow_pos (x := x) hR w
  simpa [pow_two] using continuous_lorentz_term hW w.im

theorem selbergRightFar_nonneg (Z : Finset ℂ) {x R : ℝ} (hx : 1 < x) (hR : 0 < R) (t : ℝ) :
    0 ≤ selbergRightFar Z x R t := by
  have hl := Real.log_pos hx
  unfold selbergRightFar
  refine Finset.sum_nonneg fun w _ => ?_
  have := zeroMult_nonneg w
  have := selbergRightWindow_pos (x := x) hR w
  positivity

/-- **The far majorant integrates to `(4π/(3Rℓ)) Σ m_w x^{−(Re w − ½)}`.** -/
theorem integral_selbergRightFar_le (Z : Finset ℂ) {x R : ℝ} (hx : 1 < x) (hR : 0 < R)
    {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂) :
    ∫ t in T₁..T₂, selbergRightFar Z x R t ≤
      ∑ w ∈ Z.filter (fun w => 1 / 2 + R / 2 < w.re),
        zeroMult w * (4 * Real.pi / (3 * R * Real.log x)) *
          Real.exp (-((w.re - 1 / 2) * Real.log x)) := by
  have hl := Real.log_pos hx
  unfold selbergRightFar
  rw [intervalIntegral.integral_finsetSum
    (f := fun w t => zeroMult w * (16 * Real.exp (2 * (w.re - 1 / 2) * Real.log x) / Real.log x) *
      (selbergRightWindow x R w ^ 2 + (w.im - t) ^ 2)⁻¹) (fun w _ => by
        have hW := selbergRightWindow_pos (x := x) hR w
        exact (continuous_const.mul (by simpa [pow_two] using continuous_lorentz_term hW w.im)
          ).intervalIntegrable _ _)]
  refine Finset.sum_le_sum fun w hw => ?_
  have hW := selbergRightWindow_pos (x := x) hR w
  rw [intervalIntegral.integral_const_mul]
  have h := integral_lorentz_window_le hW w.im hT
  have e : ∀ t : ℝ, (selbergRightWindow x R w ^ 2 + (w.im - t) ^ 2)⁻¹ =
      (selbergRightWindow x R w ^ 2 + (t - w.im) ^ 2)⁻¹ := by intro t; ring_nf
  simp_rw [e]
  have hc : 0 ≤ zeroMult w * (16 * Real.exp (2 * (w.re - 1 / 2) * Real.log x) / Real.log x) := by
    have := zeroMult_nonneg w; positivity
  refine (mul_le_mul_of_nonneg_left h hc).trans (le_of_eq ?_)
  unfold selbergRightWindow
  have e2 : Real.exp (3 * (w.re - 1 / 2) * Real.log x) =
      Real.exp (2 * (w.re - 1 / 2) * Real.log x) * Real.exp ((w.re - 1 / 2) * Real.log x) := by
    rw [← Real.exp_add]; ring_nf
  rw [e2, Real.exp_neg]
  field_simp
  ring

end RHTower
