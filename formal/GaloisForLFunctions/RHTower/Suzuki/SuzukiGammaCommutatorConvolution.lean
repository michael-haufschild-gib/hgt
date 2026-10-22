import GaloisForLFunctions.RHTower.Suzuki.SuzukiGammaWallCutoffCommutator

/-!
# The Gamma cutoff commutator is dominated by an exponential convolution

Every cutoff difference across a gap `s` cancels the singularity of the Gamma jump kernel at the
origin and inherits its exponential decay past the origin, so the commutator integrand obeys the
envelope `4Λe^{-s}` uniformly in the base point.  Consequently

`‖[R,χ]F(L)‖  ≤  ∫_{s>0} 4Λ e^{-s} (‖F(L+s)‖ + ‖F(L−s)‖) ds`,

a convolution against a fixed kernel of one-sided mass `4Λ`.  Everything is stated through the
extended norm, so no integrability or measurability hypothesis on `F` is required: where the
defining Bochner integral fails to converge it is zero and the bound is trivial.

This is the analytic core of the block estimate: bounding the convolution kernel on a pair of unit
blocks turns it into the exponentially localized block matrix that the flat-flux Volterra argument
consumes.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower (gammaJumpKernel)

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {χ : ℝ → ℝ} {Λ : ℝ} {F : ℝ → X}

/-- **The pointwise commutator envelope in the extended norm.** -/
theorem enorm_gammaWallCommutator_integrand_le_envelope
    (hlip : ∀ x y, |χ x - χ y| ≤ Λ * |x - y|)
    (hzero : ∀ x : ℝ, x ≤ 0 → χ x = 0) (hone : ∀ x : ℝ, 1 ≤ x → χ x = 1)
    {L s : ℝ} (hs : 0 < s) :
    ‖gammaJumpKernel s •
        ((χ L - χ (L + s)) • F (L + s) + (χ L - χ (L - s)) • F (L - s))‖ₑ
      ≤ ENNReal.ofReal (4 * Λ * Real.exp (-s)) * (‖F (L + s)‖ₑ + ‖F (L - s)‖ₑ) := by
  have hplus : |L - (L + s)| = s := by
    rw [show L - (L + s) = -s by ring, abs_neg, abs_of_pos hs]
  have hminus : |L - (L - s)| = s := by
    rw [show L - (L - s) = s by ring, abs_of_pos hs]
  have hk : 0 < gammaJumpKernel s := gammaJumpKernel_pos hs
  have hb1 := gammaJumpKernel_mul_cutoffDiff_le hlip hzero hone hs hplus
  have hb2 := gammaJumpKernel_mul_cutoffDiff_le hlip hzero hone hs hminus
  have hsplit : gammaJumpKernel s •
      ((χ L - χ (L + s)) • F (L + s) + (χ L - χ (L - s)) • F (L - s))
      = (gammaJumpKernel s * (χ L - χ (L + s))) • F (L + s)
        + (gammaJumpKernel s * (χ L - χ (L - s))) • F (L - s) := by
    module
  have hexpand : ENNReal.ofReal (4 * Λ * Real.exp (-s)) * (‖F (L + s)‖ₑ + ‖F (L - s)‖ₑ)
      = ENNReal.ofReal (4 * Λ * Real.exp (-s)) * ‖F (L + s)‖ₑ
        + ENNReal.ofReal (4 * Λ * Real.exp (-s)) * ‖F (L - s)‖ₑ := by
    rw [mul_add]
  rw [hsplit, hexpand]
  refine le_trans (enorm_add_le _ _) (add_le_add ?_ ?_)
  · rw [enorm_smul]
    refine mul_le_mul' ?_ le_rfl
    have habs : ‖gammaJumpKernel s * (χ L - χ (L + s))‖ₑ
        = ENNReal.ofReal (gammaJumpKernel s * |χ L - χ (L + s)|) := by
      rw [← ofReal_norm, Real.norm_eq_abs, abs_mul, abs_of_pos hk]
    rw [habs]
    exact ENNReal.ofReal_le_ofReal hb1
  · rw [enorm_smul]
    refine mul_le_mul' ?_ le_rfl
    have habs : ‖gammaJumpKernel s * (χ L - χ (L - s))‖ₑ
        = ENNReal.ofReal (gammaJumpKernel s * |χ L - χ (L - s)|) := by
      rw [← ofReal_norm, Real.norm_eq_abs, abs_mul, abs_of_pos hk]
    rw [habs]
    exact ENNReal.ofReal_le_ofReal hb2

/-- **The commutator is dominated by the exponential convolution.** -/
theorem enorm_gammaWallCommutator_le_lintegral
    (hlip : ∀ x y, |χ x - χ y| ≤ Λ * |x - y|)
    (hzero : ∀ x : ℝ, x ≤ 0 → χ x = 0) (hone : ∀ x : ℝ, 1 ≤ x → χ x = 1)
    (F : ℝ → X) (L : ℝ) :
    ‖gammaWallCommutator χ F L‖ₑ
      ≤ ∫⁻ s in Ioi (0 : ℝ),
          ENNReal.ofReal (4 * Λ * Real.exp (-s)) * (‖F (L + s)‖ₑ + ‖F (L - s)‖ₑ) := by
  have hstep : ‖gammaWallCommutator χ F L‖ₑ
      ≤ ∫⁻ s in Ioi (0 : ℝ), ‖gammaJumpKernel s •
          ((χ L - χ (L + s)) • F (L + s) + (χ L - χ (L - s)) • F (L - s))‖ₑ := by
    rw [gammaWallCommutator]
    exact enorm_integral_le_lintegral_enorm _
  refine hstep.trans (setLIntegral_mono' measurableSet_Ioi fun s hs => ?_)
  exact enorm_gammaWallCommutator_integrand_le_envelope hlip hzero hone hs

/-! ## The mass of the envelope -/

/-- The one-sided exponential envelope has mass exactly `4Λ`. -/
theorem lintegral_exp_envelope (hΛ : 0 ≤ Λ) :
    (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (4 * Λ * Real.exp (-s))) = ENNReal.ofReal (4 * Λ) := by
  have hbase : IntegrableOn (fun s : ℝ => Real.exp (-s)) (Ioi (0 : ℝ)) volume := by
    simpa using exp_neg_integrableOn_Ioi (0 : ℝ) (by norm_num : (0 : ℝ) < 1)
  have hintOn : IntegrableOn (fun s : ℝ => 4 * Λ * Real.exp (-s)) (Ioi (0 : ℝ)) volume :=
    hbase.const_mul (4 * Λ)
  have hnn : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), 0 ≤ 4 * Λ * Real.exp (-s) :=
    Filter.Eventually.of_forall fun s => by positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hintOn hnn]
  congr 1
  have hint : ∫ s in Ioi (0 : ℝ), Real.exp (-s) = 1 := by
    simpa using integral_exp_neg_Ioi (0 : ℝ)
  calc ∫ s in Ioi (0 : ℝ), 4 * Λ * Real.exp (-s)
      = (4 * Λ) * ∫ s in Ioi (0 : ℝ), Real.exp (-s) := by
        rw [← MeasureTheory.integral_const_mul]
    _ = 4 * Λ := by rw [hint, mul_one]

/-! ## The two-sided kernel and the `L²` bound -/

section Young

open GaloisForLFunctions.HTGeometry

/-- The two-sided exponential convolution kernel of the Gamma cutoff commutator. -/
def gammaCommKernel (Λ : ℝ) (y : ℝ) : ℝ≥0∞ := ENNReal.ofReal (4 * Λ * Real.exp (-|y|))

theorem measurable_gammaCommKernel (Λ : ℝ) : Measurable (gammaCommKernel Λ) := by
  unfold gammaCommKernel
  fun_prop

theorem gammaCommKernel_neg (Λ y : ℝ) : gammaCommKernel Λ (-y) = gammaCommKernel Λ y := by
  rw [gammaCommKernel, gammaCommKernel, abs_neg]

theorem gammaCommKernel_of_nonneg (Λ : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    gammaCommKernel Λ s = ENNReal.ofReal (4 * Λ * Real.exp (-s)) := by
  rw [gammaCommKernel, abs_of_nonneg hs]

/-- The reflection of a half-line integral of the kernel against a shifted profile. -/
theorem lintegral_Iic_neg_reflect (Λ L : ℝ) (G : ℝ → ℝ≥0∞) :
    (∫⁻ y in Iic (0 : ℝ), gammaCommKernel Λ y * G (L - y))
      = ∫⁻ s in Ici (0 : ℝ), gammaCommKernel Λ s * G (L + s) := by
  have hind : ∀ y : ℝ,
      (Iic (0 : ℝ)).indicator (fun y => gammaCommKernel Λ y * G (L - y)) (-y)
        = (Ici (0 : ℝ)).indicator (fun s => gammaCommKernel Λ s * G (L + s)) y := by
    intro y
    by_cases hy : (0 : ℝ) ≤ y
    · have hmem1 : -y ∈ Iic (0 : ℝ) := by simpa using neg_nonpos.mpr hy
      have hmem2 : y ∈ Ici (0 : ℝ) := hy
      rw [Set.indicator_of_mem hmem1, Set.indicator_of_mem hmem2, gammaCommKernel_neg]
      congr 2
      ring
    · have hy' : y < 0 := lt_of_not_ge hy
      have hmem1 : -y ∉ Iic (0 : ℝ) := by
        simp only [Set.mem_Iic, not_le]
        linarith
      have hmem2 : y ∉ Ici (0 : ℝ) := by
        simp only [Set.mem_Ici, not_le]
        linarith
      rw [Set.indicator_of_notMem hmem1, Set.indicator_of_notMem hmem2]
  calc (∫⁻ y in Iic (0 : ℝ), gammaCommKernel Λ y * G (L - y))
      = ∫⁻ y, (Iic (0 : ℝ)).indicator (fun y => gammaCommKernel Λ y * G (L - y)) y := by
        rw [lintegral_indicator measurableSet_Iic]
    _ = ∫⁻ y, (Iic (0 : ℝ)).indicator (fun y => gammaCommKernel Λ y * G (L - y)) (-y) :=
        (lintegral_neg_eq_self _).symm
    _ = ∫⁻ y, (Ici (0 : ℝ)).indicator (fun s => gammaCommKernel Λ s * G (L + s)) y :=
        lintegral_congr hind
    _ = ∫⁻ s in Ici (0 : ℝ), gammaCommKernel Λ s * G (L + s) := by
        rw [lintegral_indicator measurableSet_Ici]

/-- **The total mass of the two-sided kernel is `8Λ`.** -/
theorem lintegral_gammaCommKernel (hΛ : 0 ≤ Λ) :
    (∫⁻ y, gammaCommKernel Λ y) = ENNReal.ofReal (8 * Λ) := by
  have hIci : (∫⁻ s in Ici (0 : ℝ), gammaCommKernel Λ s) = ENNReal.ofReal (4 * Λ) := by
    rw [setLIntegral_congr Ioi_ae_eq_Ici.symm]
    rw [setLIntegral_congr_fun measurableSet_Ioi
      (fun s hs => gammaCommKernel_of_nonneg Λ (le_of_lt hs))]
    exact lintegral_exp_envelope hΛ
  have hIic : (∫⁻ y in Iic (0 : ℝ), gammaCommKernel Λ y) = ENNReal.ofReal (4 * Λ) := by
    have h := lintegral_Iic_neg_reflect Λ 0 (fun _ => (1 : ℝ≥0∞))
    simp only [mul_one] at h
    rw [h, hIci]
  have hsplit := lintegral_add_compl (μ := (volume : Measure ℝ))
    (fun y => gammaCommKernel Λ y) (measurableSet_Iic (a := (0 : ℝ)))
  rw [hIic] at hsplit
  have hcompl : (Iic (0 : ℝ))ᶜ = Ioi (0 : ℝ) := by
    ext y
    simp
  rw [hcompl] at hsplit
  have hIoi : (∫⁻ s in Ioi (0 : ℝ), gammaCommKernel Λ s) = ENNReal.ofReal (4 * Λ) := by
    rw [setLIntegral_congr_fun measurableSet_Ioi
      (fun s hs => gammaCommKernel_of_nonneg Λ (le_of_lt hs))]
    exact lintegral_exp_envelope hΛ
  rw [hIoi] at hsplit
  rw [← hsplit, ← ENNReal.ofReal_add (by linarith) (by linarith)]
  congr 1
  ring

/-- **The commutator is dominated by the two-sided convolution.** -/
theorem enorm_gammaWallCommutator_le_conv
    (hlip : ∀ x y, |χ x - χ y| ≤ Λ * |x - y|)
    (hzero : ∀ x : ℝ, x ≤ 0 → χ x = 0) (hone : ∀ x : ℝ, 1 ≤ x → χ x = 1)
    (hFm : Measurable fun x => ‖F x‖ₑ) (L : ℝ) :
    ‖gammaWallCommutator χ F L‖ₑ ≤ ∫⁻ y, gammaCommKernel Λ y * ‖F (L - y)‖ₑ := by
  refine (enorm_gammaWallCommutator_le_lintegral hlip hzero hone F L).trans ?_
  have hrw : (∫⁻ s in Ioi (0 : ℝ),
      ENNReal.ofReal (4 * Λ * Real.exp (-s)) * (‖F (L + s)‖ₑ + ‖F (L - s)‖ₑ))
      = ∫⁻ s in Ioi (0 : ℝ),
          (gammaCommKernel Λ s * ‖F (L + s)‖ₑ + gammaCommKernel Λ s * ‖F (L - s)‖ₑ) := by
    refine setLIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    rw [gammaCommKernel_of_nonneg Λ (le_of_lt hs), mul_add]
  rw [hrw]
  have hmeas1 : AEMeasurable
      (fun s : ℝ => gammaCommKernel Λ s * ‖F (L + s)‖ₑ) (volume.restrict (Ioi (0 : ℝ))) :=
    ((measurable_gammaCommKernel Λ).mul
      (hFm.comp (measurable_const.add measurable_id))).aemeasurable
  rw [lintegral_add_left' hmeas1]
  have hsplit := lintegral_add_compl (μ := (volume : Measure ℝ))
    (fun y => gammaCommKernel Λ y * ‖F (L - y)‖ₑ) (measurableSet_Iic (a := (0 : ℝ)))
  have hcompl : (Iic (0 : ℝ))ᶜ = Ioi (0 : ℝ) := by
    ext y
    simp
  rw [hcompl, lintegral_Iic_neg_reflect Λ L (fun x => ‖F x‖ₑ)] at hsplit
  rw [← hsplit, setLIntegral_congr Ioi_ae_eq_Ici.symm]

/-- **`(7)`, unlocalized: the Gamma cutoff commutator is bounded on `L²` with norm at most `8Λ`.**
Young's inequality against the two-sided exponential kernel. -/
theorem lintegral_enorm_sq_gammaWallCommutator_le
    (hlip : ∀ x y, |χ x - χ y| ≤ Λ * |x - y|)
    (hzero : ∀ x : ℝ, x ≤ 0 → χ x = 0) (hone : ∀ x : ℝ, 1 ≤ x → χ x = 1)
    (hΛ : 0 ≤ Λ) (hFm : Measurable fun x => ‖F x‖ₑ) :
    (∫⁻ L, ‖gammaWallCommutator χ F L‖ₑ ^ 2)
      ≤ ENNReal.ofReal (8 * Λ) ^ 2 * ∫⁻ x, ‖F x‖ₑ ^ 2 := by
  have hbound := lintegral_enorm_sq_le_of_convolution_bound
    (measurable_gammaCommKernel Λ) hFm
    (fun L => enorm_gammaWallCommutator_le_conv hlip hzero hone hFm L)
  rwa [lintegral_gammaCommKernel hΛ] at hbound

end Young

end GaloisForLFunctions.RHTower
