import GaloisForLFunctions.RHTower.XiGuinandWeilRectangularGammaCancellation

/-!
# Asymptotic constancy of the rectangular Gamma--polar correction

After the exact polar square is removed, the only aperture-dependent archimedean term is the
cross-edge autocorrelation tent.  Its support is the translated interval
`(4 * (a - L), 4 * a)` and its Gamma weight is exponentially small there.  Consequently the
Gamma--polar correction converges to an explicit limiting integral at rate `O_L(exp (-a))`.
-/

open Complex Filter Function Set MeasureTheory

namespace RHTower

noncomputable section

/-- The translated cross-edge tent appearing in the positive-time Gamma kernel. -/
def rectangularGammaMovingTent (L a t : ℝ) : ℝ :=
  max 0 (L - |t / 2 - (2 * a - L)|)

/-- The aperture-dependent cross-edge part of the Gamma cancellation kernel. -/
def rectangularGammaMovingKernel (L a t : ℝ) : ℝ :=
  Real.exp (-(t / 4)) * rectangularGammaMovingTent L a t /
    (1 - Real.exp (-t))

/-- The fixed self-edge kernel left after the cross-edge tent has escaped to infinity. -/
def rectangularGammaLimitingKernel (L t : ℝ) : ℝ :=
  (Real.exp (-t) * (2 * L) -
      Real.exp (-(t / 4)) * (2 * max 0 (L - t / 2))) /
    (1 - Real.exp (-t))

theorem rectangularGammaCancellationKernel_eq_limiting_sub_moving
    {L a t : ℝ} (hL : 0 ≤ L) (ha : L ≤ a) (ht : 0 < t) :
    rectangularGammaCancellationKernel L a t =
      rectangularGammaLimitingKernel L t - rectangularGammaMovingKernel L a t := by
  rw [rectangularGammaCancellationKernel, rectangularGammaCancellationNumerator,
    rectangularTwoEdgeAutocorrelation_zero hL ha,
    rectangularTwoEdgeAutocorrelation_eq_fixed_add_moving_tent hL ha (by positivity)]
  unfold rectangularGammaLimitingKernel rectangularGammaMovingKernel
  unfold rectangularGammaMovingTent
  ring

theorem rectangularGammaMovingTent_nonneg (L a t : ℝ) :
    0 ≤ rectangularGammaMovingTent L a t := by
  unfold rectangularGammaMovingTent
  positivity

theorem rectangularGammaMovingTent_le
    {L a t : ℝ} (hL : 0 ≤ L) :
    rectangularGammaMovingTent L a t ≤ L := by
  unfold rectangularGammaMovingTent
  exact max_le hL (by linarith [abs_nonneg (t / 2 - (2 * a - L))])

theorem rectangularGammaMovingTent_support
    {L a t : ℝ} (hpos : 0 < rectangularGammaMovingTent L a t) :
    4 * (a - L) < t ∧ t < 4 * a := by
  unfold rectangularGammaMovingTent at hpos
  rw [lt_max_iff] at hpos
  rcases hpos with hfalse | hpos
  · exact (lt_irrefl 0 hfalse).elim
  · have habs : |t / 2 - (2 * a - L)| < L := by linarith
    rcases abs_lt.mp habs with ⟨hleft, hright⟩
    constructor <;> linarith

theorem rectangularGammaMovingTent_eq_zero_of_not_mem_support
    {L a t : ℝ} (ht : t ∉ Ioo (4 * (a - L)) (4 * a)) :
    rectangularGammaMovingTent L a t = 0 := by
  apply le_antisymm
  · by_contra hnot
    have hpos : 0 < rectangularGammaMovingTent L a t :=
      lt_of_not_ge hnot
    exact ht (rectangularGammaMovingTent_support hpos)
  · exact rectangularGammaMovingTent_nonneg L a t

theorem rectangularGammaMovingKernel_nonneg
    {L a t : ℝ} (ht : 0 < t) :
    0 ≤ rectangularGammaMovingKernel L a t := by
  unfold rectangularGammaMovingKernel
  exact div_nonneg
    (mul_nonneg (Real.exp_pos _).le (rectangularGammaMovingTent_nonneg L a t))
    (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith)))

theorem rectangularGammaMovingKernel_eq_zero_of_not_mem_support
    {L a t : ℝ} (ht : t ∉ Ioo (4 * (a - L)) (4 * a)) :
    rectangularGammaMovingKernel L a t = 0 := by
  rw [rectangularGammaMovingKernel,
    rectangularGammaMovingTent_eq_zero_of_not_mem_support ht, mul_zero, zero_div]

theorem continuousOn_rectangularGammaMovingKernel_support
    {L a : ℝ} (ha : L + 1 / 4 ≤ a) :
    ContinuousOn (rectangularGammaMovingKernel L a)
      (Icc (4 * (a - L)) (4 * a)) := by
  let num : ℝ → ℝ := fun t =>
    Real.exp (-(t / 4)) * rectangularGammaMovingTent L a t
  let den : ℝ → ℝ := fun t => 1 - Real.exp (-t)
  have hnum : Continuous num := by
    dsimp only [num, rectangularGammaMovingTent]
    fun_prop
  have hden : Continuous den := by
    dsimp only [den]
    fun_prop
  have hquot : ContinuousOn (fun t => num t / den t)
      (Icc (4 * (a - L)) (4 * a)) := by
    apply hnum.continuousOn.div hden.continuousOn
    intro t ht
    have ht1 : 1 ≤ t := by
      have : 1 ≤ 4 * (a - L) := by linarith
      exact this.trans ht.1
    have hexplt : Real.exp (-t) < 1 :=
      Real.exp_lt_one_iff.mpr (by linarith)
    dsimp only [den]
    linarith
  change ContinuousOn (fun t => rectangularGammaMovingKernel L a t)
    (Icc (4 * (a - L)) (4 * a))
  simpa only [num, den, rectangularGammaMovingKernel] using hquot

theorem integrableOn_rectangularGammaMovingKernel
    {L a : ℝ} (ha : L + 1 / 4 ≤ a) :
    IntegrableOn (rectangularGammaMovingKernel L a) (Ioi 0) := by
  let lo : ℝ := 4 * (a - L)
  let hi : ℝ := 4 * a
  have hcompact : IntegrableOn (rectangularGammaMovingKernel L a) (Icc lo hi) := by
    exact (continuousOn_rectangularGammaMovingKernel_support ha).integrableOn_Icc
  have hopen : IntegrableOn (rectangularGammaMovingKernel L a) (Ioo lo hi) :=
    hcompact.mono_set Ioo_subset_Icc_self
  rw [← integrable_indicator_iff measurableSet_Ioi]
  have hind := hopen.integrable_indicator measurableSet_Ioo
  apply hind.congr
  filter_upwards with t
  by_cases ht : t ∈ Ioo lo hi
  · have htpos : 0 < t := by
      have hlo : 0 < lo := by
        dsimp only [lo]
        linarith
      exact hlo.trans ht.1
    simp [Set.indicator, ht, htpos]
  · have hzero : rectangularGammaMovingKernel L a t = 0 :=
      rectangularGammaMovingKernel_eq_zero_of_not_mem_support ht
    by_cases htpos : t ∈ Ioi (0 : ℝ)
    · simp [Set.indicator, ht, htpos, hzero]
    · simp [Set.indicator, ht, htpos]

theorem integral_rectangularGammaMovingKernel_support
    {L a : ℝ} (ha : L + 1 / 4 ≤ a) :
    (∫ t : ℝ in Ioi 0, rectangularGammaMovingKernel L a t) =
      ∫ t : ℝ in Ioo (4 * (a - L)) (4 * a),
        rectangularGammaMovingKernel L a t := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  filter_upwards with t
  by_cases ht : t ∈ Ioo (4 * (a - L)) (4 * a)
  · have htpos : 0 < t := by
      have hlo : 0 < 4 * (a - L) := by linarith
      exact hlo.trans ht.1
    simp [Set.indicator, ht, htpos]
  · have hzero : rectangularGammaMovingKernel L a t = 0 :=
      rectangularGammaMovingKernel_eq_zero_of_not_mem_support ht
    by_cases htpos : t ∈ Ioi (0 : ℝ)
    · simp [Set.indicator, ht, htpos, hzero]
    · simp [Set.indicator, ht, htpos]

theorem rectangularGammaMovingKernel_le_exp
    {L a t : ℝ} (hL : 0 ≤ L) (ha : L + 1 / 4 ≤ a) :
    rectangularGammaMovingKernel L a t ≤
      (L / (1 - Real.exp (-1))) * Real.exp (-(a - L)) := by
  by_cases htent : rectangularGammaMovingTent L a t = 0
  · rw [rectangularGammaMovingKernel, htent, mul_zero, zero_div]
    exact mul_nonneg
      (div_nonneg hL (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by norm_num))))
      (Real.exp_pos _).le
  · have htentPos : 0 < rectangularGammaMovingTent L a t :=
      lt_of_le_of_ne (rectangularGammaMovingTent_nonneg L a t) (Ne.symm htent)
    have hsupp := rectangularGammaMovingTent_support htentPos
    have ht1 : 1 < t := by
      have hlo : 1 ≤ 4 * (a - L) := by linarith
      exact hlo.trans_lt hsupp.1
    have hdenPos : 0 < 1 - Real.exp (-t) := by
      have := Real.exp_lt_one_iff.mpr (by linarith : -t < 0)
      linarith
    have hdenOne : 1 - Real.exp (-1) ≤ 1 - Real.exp (-t) := by
      have hexp : Real.exp (-t) ≤ Real.exp (-1) :=
        Real.exp_le_exp.mpr (by linarith)
      linarith
    have hdenOnePos : 0 < 1 - Real.exp (-1) := by
      have := Real.exp_lt_one_iff.mpr (by norm_num : (-1 : ℝ) < 0)
      linarith
    have hexp : Real.exp (-(t / 4)) ≤ Real.exp (-(a - L)) := by
      apply Real.exp_le_exp.mpr
      linarith [hsupp.1]
    have hnum : Real.exp (-(t / 4)) * rectangularGammaMovingTent L a t ≤
        Real.exp (-(a - L)) * L :=
      mul_le_mul hexp (rectangularGammaMovingTent_le hL)
        (rectangularGammaMovingTent_nonneg L a t) (Real.exp_pos _).le
    unfold rectangularGammaMovingKernel
    calc
      Real.exp (-(t / 4)) * rectangularGammaMovingTent L a t /
          (1 - Real.exp (-t)) ≤
          (Real.exp (-(a - L)) * L) / (1 - Real.exp (-t)) :=
        div_le_div_of_nonneg_right hnum hdenPos.le
      _ ≤ (Real.exp (-(a - L)) * L) / (1 - Real.exp (-1)) := by
        exact div_le_div_of_nonneg_left
          (mul_nonneg (Real.exp_pos _).le hL) hdenOnePos hdenOne
      _ = (L / (1 - Real.exp (-1))) * Real.exp (-(a - L)) := by ring

/-- Explicit `L^1` escape estimate for the moving cross-edge Gamma kernel. -/
theorem integral_rectangularGammaMovingKernel_le_exp
    {L a : ℝ} (hL : 0 ≤ L) (ha : L + 1 / 4 ≤ a) :
    0 ≤ ∫ t : ℝ in Ioi 0, rectangularGammaMovingKernel L a t ∧
    (∫ t : ℝ in Ioi 0, rectangularGammaMovingKernel L a t) ≤
      (4 * L ^ 2 / (1 - Real.exp (-1))) * Real.exp (-(a - L)) := by
  have hint := integrableOn_rectangularGammaMovingKernel ha
  constructor
  · apply integral_nonneg_of_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact rectangularGammaMovingKernel_nonneg ht
  · rw [integral_rectangularGammaMovingKernel_support ha]
    have hpoint : ∀ t ∈ Ioo (4 * (a - L)) (4 * a),
        ‖rectangularGammaMovingKernel L a t‖ ≤
          (L / (1 - Real.exp (-1))) * Real.exp (-(a - L)) := by
      intro t ht
      have htpos : 0 < t := (by linarith : 0 < 4 * (a - L)).trans ht.1
      rw [Real.norm_eq_abs, abs_of_nonneg
        (rectangularGammaMovingKernel_nonneg htpos)]
      exact rectangularGammaMovingKernel_le_exp hL ha
    have hnorm := norm_setIntegral_le_of_norm_le_const
      (μ := volume)
      (f := rectangularGammaMovingKernel L a)
      (C := (L / (1 - Real.exp (-1))) * Real.exp (-(a - L)))
      measure_Ioo_lt_top hpoint
    rw [Measure.real, Real.volume_Ioo, ENNReal.toReal_ofReal] at hnorm
    · rw [Real.norm_eq_abs, abs_of_nonneg] at hnorm
      · convert hnorm using 1 <;> ring
      · apply integral_nonneg_of_ae
        filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
        have hlo : 0 < 4 * (a - L) := by linarith
        have htpos : 0 < t := hlo.trans ht.1
        exact rectangularGammaMovingKernel_nonneg htpos
    · linarith

theorem integrableOn_rectangularGammaLimitingKernel
    {L : ℝ} (hL : 0 ≤ L) :
    IntegrableOn (rectangularGammaLimitingKernel L) (Ioi 0) := by
  let a0 : ℝ := L + 1
  have ha0 : L ≤ a0 := by dsimp only [a0]; linarith
  have haQuarter : L + 1 / 4 ≤ a0 := by dsimp only [a0]; linarith
  have hgamma := integrableOn_rectangularGammaCancellationKernel hL ha0
  have hmoving := integrableOn_rectangularGammaMovingKernel haQuarter
  have hsum := hgamma.add hmoving
  apply hsum.congr_fun _ measurableSet_Ioi
  intro t ht
  have hdecomp := rectangularGammaCancellationKernel_eq_limiting_sub_moving
    hL ha0 ht
  change rectangularGammaCancellationKernel L a0 t +
      rectangularGammaMovingKernel L a0 t = rectangularGammaLimitingKernel L t
  rw [hdecomp]
  ring

/-- The limiting constant of the Gamma--polar correction after its moving tent escapes. -/
def rectangularGammaPolarLimit (L : ℝ) : ℝ :=
  (∫ t : ℝ in Ioi 0, rectangularGammaLimitingKernel L t) -
    (Real.eulerMascheroniConstant + Real.log Real.pi) * (2 * L)

/-- **Gamma--polar asymptotic law.**  The correction converges to an explicit constant with an
exponential aperture error. -/
theorem abs_rectangularGammaPolarCorrection_sub_limit_le_exp
    {L a : ℝ} (hL : 0 ≤ L) (ha : L + 1 / 4 ≤ a) :
    |rectangularGammaPolarCorrection L a - rectangularGammaPolarLimit L| ≤
      (4 * L ^ 2 * Real.exp L / (1 - Real.exp (-1))) * Real.exp (-a) := by
  have haL : L ≤ a := by linarith [ha]
  have hgamma := integrableOn_rectangularGammaCancellationKernel hL haL
  have hlimit := integrableOn_rectangularGammaLimitingKernel hL
  have hmoving := integrableOn_rectangularGammaMovingKernel ha
  have hdecomp : (∫ t : ℝ in Ioi 0, rectangularGammaCancellationKernel L a t) =
      (∫ t : ℝ in Ioi 0, rectangularGammaLimitingKernel L t) -
        ∫ t : ℝ in Ioi 0, rectangularGammaMovingKernel L a t := by
    rw [← integral_sub hlimit hmoving]
    apply integral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact rectangularGammaCancellationKernel_eq_limiting_sub_moving hL
      haL ht
  have hbound := (integral_rectangularGammaMovingKernel_le_exp hL ha).2
  rw [rectangularGammaPolarCorrection, rectangularGammaPolarLimit, hdecomp]
  have hnonneg := (integral_rectangularGammaMovingKernel_le_exp hL ha).1
  rw [show
      ((∫ t : ℝ in Ioi 0, rectangularGammaLimitingKernel L t) -
          ∫ t : ℝ in Ioi 0, rectangularGammaMovingKernel L a t) -
        (Real.eulerMascheroniConstant + Real.log Real.pi) * (2 * L) -
        ((∫ t : ℝ in Ioi 0, rectangularGammaLimitingKernel L t) -
          (Real.eulerMascheroniConstant + Real.log Real.pi) * (2 * L)) =
      -(∫ t : ℝ in Ioi 0, rectangularGammaMovingKernel L a t) by ring,
    abs_neg, abs_of_nonneg hnonneg]
  calc
    (∫ t : ℝ in Ioi 0, rectangularGammaMovingKernel L a t) ≤
        (4 * L ^ 2 / (1 - Real.exp (-1))) * Real.exp (-(a - L)) := hbound
    _ = (4 * L ^ 2 * Real.exp L / (1 - Real.exp (-1))) * Real.exp (-a) := by
      rw [show -(a - L) = L + -a by ring, Real.exp_add]
      ring

/-- Arithmetic-aperture specialization: the archimedean remainder differs from its limiting
constant by `O_L(n^{-1/2})`. -/
theorem abs_rectangularGammaPolarCorrection_logSample_sub_limit_le_inv_sqrt
    {L : ℝ} (hL : 0 ≤ L) {n : ℕ} (hn : 1 ≤ n)
    (ha : L + 1 / 4 ≤ Real.log n / 2) :
    |rectangularGammaPolarCorrection L (Real.log n / 2) -
        rectangularGammaPolarLimit L| ≤
      (4 * L ^ 2 * Real.exp L / (1 - Real.exp (-1))) / Real.sqrt n := by
  have h := abs_rectangularGammaPolarCorrection_sub_limit_le_exp hL ha
  calc
    |rectangularGammaPolarCorrection L (Real.log n / 2) -
        rectangularGammaPolarLimit L| ≤
        (4 * L ^ 2 * Real.exp L / (1 - Real.exp (-1))) *
          Real.exp (-(Real.log n / 2)) := h
    _ = (4 * L ^ 2 * Real.exp L / (1 - Real.exp (-1))) / Real.sqrt n := by
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      have hlog : -(Real.log n / 2) = -Real.log (Real.sqrt n) := by
        rw [Real.log_sqrt (Nat.cast_nonneg n)]
      have hexp : Real.exp (-Real.log (Real.sqrt n)) = (Real.sqrt n)⁻¹ := by
        rw [Real.exp_neg, Real.exp_log (Real.sqrt_pos.mpr hnpos)]
      rw [hlog, hexp]
      ring

end

end RHTower
