import GaloisForLFunctions.RHTower.PutnamPoissonBound
import GaloisForLFunctions.RHTower.PutnamJump
import GaloisForLFunctions.HTGeometry.CosineArc

/-!
# The conjugate kernel blows up at a jump

On the first half period the imaginary part of the Cauchy kernel is nonnegative and its integral is
`d^{-1} log((1+r)/(1-r))`, which is unbounded as `r → 1`.  Pairing it against the periodisation
folds the second half period onto the first and produces the difference of the two one-sided limits
of the periodisation at the origin, so a nonzero jump forces the pairing to be unbounded — while the
Poisson bound keeps it bounded.
-/

open Complex MeasureTheory Set Filter Topology HTGeometry

noncomputable section

namespace RHTower

theorem putnamPeriod_half_mul {d : ℝ} (hd : 0 < d) : d * (putnamPeriod d / 2) = Real.pi := by
  rw [putnamPeriod]
  field_simp

theorem circleFactor_zero (r d : ℝ) : circleFactor r d 0 = ((1 - r : ℝ) : ℂ) := by
  rw [circleFactor]
  push_cast
  simp

theorem circleFactor_half {d : ℝ} (hd : 0 < d) (r : ℝ) :
    circleFactor r d (putnamPeriod d / 2) = ((1 + r : ℝ) : ℂ) := by
  have h := putnamPeriod_half_mul hd
  rw [circleFactor,
    show (d : ℂ) * ((putnamPeriod d / 2 : ℝ) : ℂ) * I = ((Real.pi : ℝ) : ℂ) * I by
      push_cast [← h]; ring]
  rw [Complex.exp_pi_mul_I]
  push_cast
  ring

/-- **The mass of the conjugate kernel on a half period.** -/
theorem integral_circleKernel_im_half {d r : ℝ} (hd : 0 < d) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∫ y in Ioc (0 : ℝ) (putnamPeriod d / 2), ((circleFactor r d y)⁻¹).im)
      = (Real.log (1 + r) - Real.log (1 - r)) / d := by
  have hH : 0 < putnamPeriod d / 2 := by
    have := putnamPeriod_pos hd
    linarith
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hcauchy : (∫ y in Ioc (0 : ℝ) (putnamPeriod d / 2), (circleFactor r d y)⁻¹)
      = ((putnamPeriod d / 2 : ℝ) : ℂ)
        + (I / (d : ℂ)) * (((Real.log (1 + r) : ℝ) : ℂ) - ((Real.log (1 - r) : ℝ) : ℂ)) := by
    rw [← intervalIntegral.integral_of_le hH.le,
      integral_circleKernel hr0 hr1 hd.ne' 0 (putnamPeriod d / 2),
      circleFactor_zero, circleFactor_half hd,
      ← Complex.ofReal_log (by linarith : (0:ℝ) ≤ 1 + r),
      ← Complex.ofReal_log (by linarith : (0:ℝ) ≤ 1 - r)]
    push_cast
    ring
  have hco : (∫ y in Ioc (0 : ℝ) (putnamPeriod d / 2), ((((circleFactor r d y)⁻¹).im : ℝ) : ℂ))
      = (((∫ y in Ioc (0 : ℝ) (putnamPeriod d / 2), ((circleFactor r d y)⁻¹).im) : ℝ) : ℂ) :=
    integral_ofReal
  have hfin : (volume (Ioc (0 : ℝ) (putnamPeriod d / 2))) ≠ ⊤ := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have hint1 : IntegrableOn (fun y => (circleFactor r d y)⁻¹)
      (Ioc (0 : ℝ) (putnamPeriod d / 2)) :=
    Integrable.mono' (g := fun _ : ℝ => (1 - r)⁻¹) (integrableOn_const hfin)
      ((continuous_circleKernel hr0 hr1 d).aestronglyMeasurable.restrict)
      (Filter.Eventually.of_forall fun y => norm_circleKernel_le hr0 hr1 d y)
  have hint2 : IntegrableOn (fun y => (starRingEnd ℂ) ((circleFactor r d y)⁻¹))
      (Ioc (0 : ℝ) (putnamPeriod d / 2)) :=
    Integrable.mono' (g := fun _ : ℝ => (1 - r)⁻¹) (integrableOn_const hfin)
      ((Complex.continuous_conj.comp
        (continuous_circleKernel hr0 hr1 d)).aestronglyMeasurable.restrict)
      (Filter.Eventually.of_forall fun y => by
        rw [RCLike.norm_conj]; exact norm_circleKernel_le hr0 hr1 d y)
  have hpt : ∀ y : ℝ, ((((circleFactor r d y)⁻¹).im : ℝ) : ℂ) * (2 * I)
      = (circleFactor r d y)⁻¹ - (starRingEnd ℂ) ((circleFactor r d y)⁻¹) := by
    intro y
    rw [Complex.sub_conj]
    push_cast
    ring
  have hsub : (∫ y in Ioc (0 : ℝ) (putnamPeriod d / 2),
        ((circleFactor r d y)⁻¹ - (starRingEnd ℂ) ((circleFactor r d y)⁻¹)))
      = (∫ y in Ioc (0 : ℝ) (putnamPeriod d / 2), (circleFactor r d y)⁻¹)
        - ∫ y in Ioc (0 : ℝ) (putnamPeriod d / 2), (starRingEnd ℂ) ((circleFactor r d y)⁻¹) :=
    integral_sub hint1 hint2
  have hconjint : (∫ y in Ioc (0 : ℝ) (putnamPeriod d / 2),
        (starRingEnd ℂ) ((circleFactor r d y)⁻¹))
      = (starRingEnd ℂ) (∫ y in Ioc (0 : ℝ) (putnamPeriod d / 2), (circleFactor r d y)⁻¹) :=
    integral_conj
  have hmain : (((∫ y in Ioc (0 : ℝ) (putnamPeriod d / 2),
        ((circleFactor r d y)⁻¹).im) : ℝ) : ℂ) * (2 * I)
      = (((Real.log (1 + r) - Real.log (1 - r)) / d : ℝ) : ℂ) * (2 * I) := by
    rw [← hco, ← integral_mul_const, setIntegral_congr_fun measurableSet_Ioc (fun y _ => hpt y),
      hsub, hconjint, hcauchy]
    rw [map_add, map_mul, map_div₀, Complex.conj_I, Complex.conj_ofReal, Complex.conj_ofReal,
      map_sub, Complex.conj_ofReal, Complex.conj_ofReal]
    push_cast
    field_simp
    ring
  have h2I : (2 : ℂ) * I ≠ 0 := by
    simp [Complex.I_ne_zero]
  have := mul_right_cancel₀ h2I hmain
  exact_mod_cast this

theorem circleKernelIm_nonneg_of_mem {d r : ℝ} (hd : 0 < d) (hr0 : 0 ≤ r) (hr1 : r < 1) {y : ℝ}
    (hy : y ∈ Ioc (0 : ℝ) (putnamPeriod d / 2)) : 0 ≤ ((circleFactor r d y)⁻¹).im := by
  refine circleKernel_im_nonneg hr0 hr1 (Real.sin_nonneg_of_nonneg_of_le_pi ?_ ?_)
  · exact mul_nonneg hd.le hy.1.le
  · rw [← putnamPeriod_half_mul hd]
    exact mul_le_mul_of_nonneg_left hy.2 hd.le

theorem abs_circleKernelIm_le_of_far {d r δ : ℝ} (hd : 0 < d) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hδ0 : 0 < δ) (hδH : δ < putnamPeriod d / 2) {y : ℝ}
    (hy : y ∈ Ioc δ (putnamPeriod d / 2)) :
    |((circleFactor r d y)⁻¹).im| ≤ 1 / (1 - Real.cos (d * δ) ^ 2) := by
  have hdδ0 : 0 ≤ d * δ := by positivity
  have hdδπ : d * δ < Real.pi := by
    rw [← putnamPeriod_half_mul hd]
    exact mul_lt_mul_of_pos_left hδH hd
  have hdy : d * y ≤ Real.pi := by
    rw [← putnamPeriod_half_mul hd]
    exact mul_le_mul_of_nonneg_left hy.2 hd.le
  have hcos : Real.cos (d * y) ≤ Real.cos (d * δ) :=
    Real.cos_le_cos_of_nonneg_of_le_pi hdδ0 hdy (mul_le_mul_of_nonneg_left hy.1.le hd.le)
  have hγ1 : Real.cos (d * δ) < 1 := by
    have hpos : 0 < d * δ := by positivity
    have := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl (0:ℝ)) hdδπ.le hpos
    simpa using this
  have hγ0 : -1 < Real.cos (d * δ) := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi hdδ0 (le_refl Real.pi) hdδπ
    simpa using this
  exact abs_circleKernel_im_le hr0 hr1 (d := d) (y := y) hcos hγ1 hγ0

theorem norm_ofReal_circleKernelIm_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (d y : ℝ) :
    ‖((((circleFactor r d y)⁻¹).im : ℝ) : ℂ)‖ ≤ (1 - r)⁻¹ := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact le_trans (Complex.abs_im_le_norm _) (norm_circleKernel_le hr0 hr1 d y)

/-- **Folding the pairing onto the first half period.** -/
theorem fold_kernelIm_pairing {a d r : ℝ} (hd : 0 < d) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∫ y in Ioc (0 : ℝ) (putnamPeriod d),
        putnamPeriodization a d y * ((((circleFactor r d y)⁻¹).im : ℝ) : ℂ))
      = ∫ y in Ioc (0 : ℝ) (putnamPeriod d / 2),
          (putnamPeriodization a d y - putnamPeriodization a d (putnamPeriod d - y))
            * ((((circleFactor r d y)⁻¹).im : ℝ) : ℂ) := by
  set P := putnamPeriod d with hPdef
  set D := putnamPeriodization a d with hDdef
  set f : ℝ → ℂ := fun y => D y * ((((circleFactor r d y)⁻¹).im : ℝ) : ℂ) with hfdef
  have hP : 0 < P := putnamPeriod_pos hd
  have hH : 0 < P / 2 := by linarith
  have hHP : P / 2 ≤ P := by linarith
  have hhalf : P - P / 2 = P / 2 := by ring
  have hdP : d * P = 2 * Real.pi := by
    rw [hPdef, putnamPeriod]
    field_simp
  have hfint : IntegrableOn f (Ioc (0 : ℝ) P) :=
    integrableOn_periodization_mul hd (continuous_circleKernel_im hr0 hr1 d)
      (norm_ofReal_circleKernelIm_le hr0 hr1 d)
  have hf1 : IntervalIntegrable f volume 0 (P / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hH.le).mpr
      (hfint.mono_set (Ioc_subset_Ioc_right hHP))
  have hf2 : IntervalIntegrable f volume (P / 2) P :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hHP).mpr
      (hfint.mono_set (Ioc_subset_Ioc_left hH.le))
  have hgint : IntervalIntegrable (fun x => f (P - x)) volume 0 (P / 2) := by
    have h := (hf2.comp_sub_left P)
    rw [hhalf, sub_self] at h
    exact h.symm
  have hrefl : ∀ x : ℝ, f (P - x) = -(D (P - x) * ((((circleFactor r d x)⁻¹).im : ℝ) : ℂ)) := by
    intro x
    rw [hfdef]
    simp only
    rw [circleKernel_im_reflect hdP r x]
    push_cast
    ring
  have hcomp : (∫ x in (0 : ℝ)..(P / 2), f (P - x)) = ∫ x in (P / 2)..P, f x := by
    have h := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := P / 2) f P
    rw [h, hhalf, sub_zero]
  have hsplit : (∫ y in (0 : ℝ)..P, f y)
      = (∫ y in (0 : ℝ)..(P / 2), f y) + ∫ y in (0 : ℝ)..(P / 2), f (P - y) := by
    rw [hcomp]
    exact (intervalIntegral.integral_add_adjacent_intervals hf1 hf2).symm
  have hcombine : (∫ y in (0 : ℝ)..(P / 2), f y) + ∫ y in (0 : ℝ)..(P / 2), f (P - y)
      = ∫ y in (0 : ℝ)..(P / 2), (f y + f (P - y)) :=
    (intervalIntegral.integral_add hf1 hgint).symm
  have hpt : ∀ y : ℝ, f y + f (P - y)
      = (D y - D (P - y)) * ((((circleFactor r d y)⁻¹).im : ℝ) : ℂ) := by
    intro y
    rw [hrefl y, hfdef]
    ring
  rw [← intervalIntegral.integral_of_le hP.le, hsplit, hcombine,
    intervalIntegral.integral_congr (g := fun y =>
      (D y - D (P - y)) * ((((circleFactor r d y)⁻¹).im : ℝ) : ℂ)) (fun y _ => hpt y),
    intervalIntegral.integral_of_le hH.le]

/-- The left limit of the periodisation at the origin. -/
def putnamLeftValue (a d : ℝ) : ℂ :=
  ∑' k : ℤ, putnamKernelLeft a (0 + (k : ℝ) * putnamPeriod d)

theorem tendsto_periodization_right_zero {a d : ℝ} (hd : 0 < d) :
    Tendsto (putnamPeriodization a d) (𝓝[>] (0 : ℝ)) (𝓝 (putnamPeriodization a d 0)) :=
  tendsto_putnamPeriodization_right hd 0

theorem tendsto_periodization_left_zero {a d : ℝ} (hd : 0 < d) :
    Tendsto (putnamPeriodization a d) (𝓝[<] (0 : ℝ)) (𝓝 (putnamLeftValue a d)) :=
  tendsto_putnamPeriodization_left hd 0

/-- **The jump at the origin.** -/
theorem putnamLeftValue_sub_ne_zero {a d : ℝ} (hd : 0 < d) :
    putnamLeftValue a d - putnamPeriodization a d 0 ≠ 0 := by
  have hsub : putnamLeftValue a d - putnamPeriodization a d 0
      = ∑' k : ℤ, putnamJumpTerm a d k := by
    rw [putnamLeftValue, putnamPeriodization,
      ← (summable_putnamKernelLeft_translates hd 0).tsum_sub
        (summable_putnamKernel_translates hd 0)]
    refine tsum_congr fun k => ?_
    rw [putnamKernelLeft, putnamJumpTerm, zero_add]
    push_cast
    ring
  rw [hsub]
  exact tsum_putnamJumpTerm_ne_zero hd

/-- The folded difference tends to the jump at the origin. -/
theorem tendsto_foldedDifference {a d : ℝ} (hd : 0 < d) :
    Tendsto (fun y : ℝ => putnamPeriodization a d y
        - putnamPeriodization a d (putnamPeriod d - y)) (𝓝[>] (0 : ℝ))
      (𝓝 (putnamPeriodization a d 0 - putnamLeftValue a d)) := by
  have hneg : Tendsto (fun y : ℝ => -y) (𝓝[>] (0 : ℝ)) (𝓝[<] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (Filter.Tendsto.mono_left (by simpa using (continuous_neg.tendsto (0 : ℝ)))
        nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact mem_Iio.mpr (by simpa using (mem_Ioi.mp hx))
  have hcomp : Tendsto (fun y : ℝ => putnamPeriodization a d (-y)) (𝓝[>] (0 : ℝ))
      (𝓝 (putnamLeftValue a d)) := (tendsto_periodization_left_zero hd).comp hneg
  have hkey : Tendsto (fun y : ℝ => putnamPeriodization a d y - putnamPeriodization a d (-y))
      (𝓝[>] (0 : ℝ)) (𝓝 (putnamPeriodization a d 0 - putnamLeftValue a d)) :=
    (tendsto_periodization_right_zero hd).sub hcomp
  refine hkey.congr (fun y => ?_)
  congr 1
  have := putnamPeriodization_periodic a d (-y)
  rw [show putnamPeriod d - y = -y + putnamPeriod d by ring, this]

theorem norm_periodization_reflect_le {a d : ℝ} (hd : 0 < d) {y : ℝ}
    (hy : y ∈ Ioc (0 : ℝ) (putnamPeriod d / 2)) :
    ‖putnamPeriodization a d (putnamPeriod d - y)‖ ≤ periodizationBound d := by
  refine norm_putnamPeriodization_le_bound hd ⟨?_, ?_⟩
  · have := putnamPeriod_pos hd
    have := hy.2
    linarith
  · linarith [hy.1]

theorem integrableOn_foldBase {a d : ℝ} (hd : 0 < d) :
    IntegrableOn (fun y => putnamPeriodization a d y
        - putnamPeriodization a d (putnamPeriod d - y)) (Ioc (0 : ℝ) (putnamPeriod d / 2)) := by
  have hP : 0 < putnamPeriod d := putnamPeriod_pos hd
  have hfin : (volume (Ioc (0 : ℝ) (putnamPeriod d / 2))) ≠ ⊤ := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have h1 : IntegrableOn (putnamPeriodization a d) (Ioc (0 : ℝ) (putnamPeriod d / 2)) :=
    (integrableOn_putnamPeriodization (a := a) hd).mono_set
      (Ioc_subset_Ioc_right (by linarith))
  have h2 : IntegrableOn (fun y => putnamPeriodization a d (putnamPeriod d - y))
      (Ioc (0 : ℝ) (putnamPeriod d / 2)) := by
    refine Integrable.mono' (g := fun _ : ℝ => periodizationBound d) (integrableOn_const hfin)
      (((measurable_putnamPeriodization a d).comp
        (measurable_const.sub measurable_id)).aestronglyMeasurable.restrict) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr
      (Filter.Eventually.of_forall fun y hy => norm_periodization_reflect_le hd hy)
  exact h1.sub h2

theorem integrableOn_mul_bdd {f g : ℝ → ℂ} {s : Set ℝ} {C : ℝ} (hf : IntegrableOn f s)
    (hg : Continuous g) (hC : ∀ x, ‖g x‖ ≤ C) : IntegrableOn (fun y => f y * g y) s := by
  have h := hf.bdd_mul (c := C) (hg.aestronglyMeasurable.restrict)
    (Filter.Eventually.of_forall hC)
  exact h.congr (Filter.Eventually.of_forall fun x => mul_comm _ _)

/-- The estimate at a single radius: the jump forces the folded pairing to grow like the mass of
the conjugate kernel. -/
theorem jump_estimate {a d : ℝ} (hd : 0 < d)
    (hcon : ∀ n : ℕ,
      (∫ x in Ioc (0 : ℝ) (putnamPeriod d), putnamPeriodTwist a d (n : ℤ) x) = 0)
    {δ : ℝ} (hδ0 : 0 < δ) (hδH : δ < putnamPeriod d / 2)
    (hδ : ∀ y ∈ Ioc (0 : ℝ) δ,
      ‖(putnamPeriodization a d y - putnamPeriodization a d (putnamPeriod d - y))
        - (putnamPeriodization a d 0 - putnamLeftValue a d)‖
        ≤ ‖putnamPeriodization a d 0 - putnamLeftValue a d‖ / 2)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ‖putnamPeriodization a d 0 - putnamLeftValue a d‖ / 2
        * ((Real.log (1 + r) - Real.log (1 - r)) / d)
      ≤ periodizationBound d * putnamPeriod d / 2
        + (2 * periodizationBound d
            + ‖putnamPeriodization a d 0 - putnamLeftValue a d‖) * (putnamPeriod d / 2)
          * (1 / (1 - Real.cos (d * δ) ^ 2)) := by
  classical
  set P := putnamPeriod d with hPdef
  set D := putnamPeriodization a d with hDdef
  set M := periodizationBound d with hMdef
  set J : ℂ := D 0 - putnamLeftValue a d with hJdef
  set K : ℝ → ℝ := fun y => ((circleFactor r d y)⁻¹).im with hKdef
  set Λ : ℝ := (Real.log (1 + r) - Real.log (1 - r)) / d with hΛdef
  set Ψ : ℝ → ℂ := fun y => D y - D (P - y) with hΨdef
  set Cδ : ℝ := 1 / (1 - Real.cos (d * δ) ^ 2) with hCδdef
  have hP : 0 < P := putnamPeriod_pos hd
  have hH : 0 < P / 2 := by linarith
  have hMnn : (0 : ℝ) ≤ M := periodizationBound_nonneg d
  have hfinH : (volume (Ioc (0 : ℝ) (P / 2))) ≠ ⊤ := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have hKnn : ∀ y ∈ Ioc (0 : ℝ) (P / 2), 0 ≤ K y := fun y hy =>
    circleKernelIm_nonneg_of_mem hd hr0 hr1 hy
  have hKbdd : ∀ y : ℝ, ‖((K y : ℝ) : ℂ)‖ ≤ (1 - r)⁻¹ := norm_ofReal_circleKernelIm_le hr0 hr1 d
  have hΛeq : (∫ y in Ioc (0 : ℝ) (P / 2), K y) = Λ := integral_circleKernel_im_half hd hr0 hr1
  have hKintR : IntegrableOn K (Ioc (0 : ℝ) (P / 2)) := by
    refine Integrable.mono' (g := fun _ : ℝ => (1 - r)⁻¹) (integrableOn_const hfinH)
      ((Complex.continuous_im.comp
        (continuous_circleKernel hr0 hr1 d)).aestronglyMeasurable.restrict)
      (Filter.Eventually.of_forall fun y => ?_)
    have := hKbdd y
    rwa [Complex.norm_real] at this
  have hΨint : IntegrableOn Ψ (Ioc (0 : ℝ) (P / 2)) := integrableOn_foldBase hd
  have hΨKint : IntegrableOn (fun y => Ψ y * ((K y : ℝ) : ℂ)) (Ioc (0 : ℝ) (P / 2)) :=
    integrableOn_mul_bdd hΨint (continuous_circleKernel_im hr0 hr1 d) hKbdd
  have hconstint : IntegrableOn (fun _ : ℝ => J) (Ioc (0 : ℝ) (P / 2)) := integrableOn_const hfinH
  have hJKint : IntegrableOn (fun y => J * ((K y : ℝ) : ℂ)) (Ioc (0 : ℝ) (P / 2)) :=
    integrableOn_mul_bdd hconstint (continuous_circleKernel_im hr0 hr1 d) hKbdd
  have hdiffKint : IntegrableOn (fun y => (Ψ y - J) * ((K y : ℝ) : ℂ)) (Ioc (0 : ℝ) (P / 2)) :=
    integrableOn_mul_bdd (hΨint.sub hconstint) (continuous_circleKernel_im hr0 hr1 d) hKbdd
  -- the Poisson bound, folded
  have hbound : ‖∫ y in Ioc (0 : ℝ) (P / 2), Ψ y * ((K y : ℝ) : ℂ)‖ ≤ M * P / 2 := by
    have h := norm_integral_periodization_kernelIm_le (a := a) hd hr0 hr1 hcon
    rwa [fold_kernelIm_pairing (a := a) hd hr0 hr1] at h
  -- the main term
  have hJval : (∫ y in Ioc (0 : ℝ) (P / 2), J * ((K y : ℝ) : ℂ)) = J * ((Λ : ℝ) : ℂ) := by
    rw [integral_const_mul]
    congr 1
    have hco : (∫ y in Ioc (0 : ℝ) (P / 2), ((K y : ℝ) : ℂ))
        = (((∫ y in Ioc (0 : ℝ) (P / 2), K y) : ℝ) : ℂ) := integral_ofReal
    rw [hco, hΛeq]
  have hsplit : (∫ y in Ioc (0 : ℝ) (P / 2), Ψ y * ((K y : ℝ) : ℂ))
      = J * ((Λ : ℝ) : ℂ) + ∫ y in Ioc (0 : ℝ) (P / 2), (Ψ y - J) * ((K y : ℝ) : ℂ) := by
    rw [← hJval, ← integral_add hJKint hdiffKint]
    exact setIntegral_congr_fun measurableSet_Ioc (fun y _ => by ring)
  -- split the error into a near and a far part
  have hδle : δ ≤ P / 2 := hδH.le
  have hIoc : Ioc (0 : ℝ) δ ∪ Ioc δ (P / 2) = Ioc (0 : ℝ) (P / 2) :=
    Set.Ioc_union_Ioc_eq_Ioc hδ0.le hδle
  have hdisj : Disjoint (Ioc (0 : ℝ) δ) (Ioc δ (P / 2)) :=
    Set.disjoint_left.mpr (fun x hx hx' => absurd hx'.1 (not_lt.mpr hx.2))
  have hsub1 : Ioc (0 : ℝ) δ ⊆ Ioc (0 : ℝ) (P / 2) := Ioc_subset_Ioc_right hδle
  have hsub2 : Ioc δ (P / 2) ⊆ Ioc (0 : ℝ) (P / 2) := Ioc_subset_Ioc_left hδ0.le
  have herr : (∫ y in Ioc (0 : ℝ) (P / 2), (Ψ y - J) * ((K y : ℝ) : ℂ))
      = (∫ y in Ioc (0 : ℝ) δ, (Ψ y - J) * ((K y : ℝ) : ℂ))
        + ∫ y in Ioc δ (P / 2), (Ψ y - J) * ((K y : ℝ) : ℂ) := by
    rw [← hIoc, setIntegral_union hdisj measurableSet_Ioc
      (hdiffKint.mono_set hsub1) (hdiffKint.mono_set hsub2)]
  have hΛnn : 0 ≤ Λ := by
    rw [← hΛeq]
    exact setIntegral_nonneg measurableSet_Ioc (fun y hy => hKnn y hy)
  have hKmass : (∫ y in Ioc (0 : ℝ) δ, K y) ≤ Λ := by
    have hsplitK : (∫ y in Ioc (0 : ℝ) (P / 2), K y)
        = (∫ y in Ioc (0 : ℝ) δ, K y) + ∫ y in Ioc δ (P / 2), K y := by
      rw [← hIoc, setIntegral_union hdisj measurableSet_Ioc
        (hKintR.mono_set hsub1) (hKintR.mono_set hsub2)]
    have hfarnn : 0 ≤ ∫ y in Ioc δ (P / 2), K y :=
      setIntegral_nonneg measurableSet_Ioc (fun y hy => hKnn y (hsub2 hy))
    rw [hΛeq] at hsplitK
    linarith
  have hnear : ‖∫ y in Ioc (0 : ℝ) δ, (Ψ y - J) * ((K y : ℝ) : ℂ)‖ ≤ ‖J‖ / 2 * Λ := by
    refine le_trans (norm_integral_le_integral_norm _) ?_
    have hmono : (∫ y in Ioc (0 : ℝ) δ, ‖(Ψ y - J) * ((K y : ℝ) : ℂ)‖)
        ≤ ∫ y in Ioc (0 : ℝ) δ, ‖J‖ / 2 * K y := by
      refine setIntegral_mono_on ((hdiffKint.mono_set hsub1).norm)
        ((hKintR.mono_set hsub1).const_mul _) measurableSet_Ioc (fun y hy => ?_)
      have hKy : 0 ≤ K y := hKnn y (hsub1 hy)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hKy]
      exact mul_le_mul_of_nonneg_right (hδ y hy) hKy
    have hval : (∫ y in Ioc (0 : ℝ) δ, ‖J‖ / 2 * K y) = ‖J‖ / 2 * ∫ y in Ioc (0 : ℝ) δ, K y :=
      integral_const_mul _ _
    rw [hval] at hmono
    refine le_trans hmono ?_
    exact mul_le_mul_of_nonneg_left hKmass (by positivity)
  have hfar : ‖∫ y in Ioc δ (P / 2), (Ψ y - J) * ((K y : ℝ) : ℂ)‖
      ≤ (2 * M + ‖J‖) * (P / 2) * Cδ := by
    have hCδnn : 0 ≤ Cδ := by
      rw [hCδdef]
      have h := abs_circleKernelIm_le_of_far (d := d) (r := r) hd hr0 hr1 hδ0 hδH
        (y := P / 2) ⟨hδH, le_refl _⟩
      exact le_trans (abs_nonneg _) h
    have hCnn : 0 ≤ (2 * M + ‖J‖) * Cδ := by
      have : (0 : ℝ) ≤ 2 * M + ‖J‖ := by positivity
      exact mul_nonneg this hCδnn
    have hptbound : ∀ y ∈ Ioc δ (P / 2), ‖(Ψ y - J) * ((K y : ℝ) : ℂ)‖
        ≤ (2 * M + ‖J‖) * Cδ := by
      intro y hy
      have hyH : y ∈ Ioc (0 : ℝ) (P / 2) := hsub2 hy
      have h1 : ‖Ψ y‖ ≤ 2 * M := by
        refine le_trans (norm_sub_le _ _) ?_
        have hA := norm_putnamPeriodization_le_bound (a := a) hd
          (show y ∈ Ioc (0 : ℝ) P from ⟨hyH.1, by linarith [hyH.2]⟩)
        have hB := norm_periodization_reflect_le (a := a) hd hyH
        linarith
      have h2 : ‖Ψ y - J‖ ≤ 2 * M + ‖J‖ := le_trans (norm_sub_le _ _) (by linarith)
      have h3 : ‖((K y : ℝ) : ℂ)‖ ≤ Cδ := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact abs_circleKernelIm_le_of_far hd hr0 hr1 hδ0 hδH hy
      rw [norm_mul]
      exact mul_le_mul h2 h3 (norm_nonneg _) (by positivity)
    refine le_trans (norm_integral_le_of_norm_le_const (C := (2 * M + ‖J‖) * Cδ) ?_) ?_
    · exact (ae_restrict_iff' measurableSet_Ioc).mpr
        (Filter.Eventually.of_forall hptbound)
    · have hmeas : (volume.restrict (Ioc δ (P / 2))).real univ = P / 2 - δ := by
        simp [MeasureTheory.Measure.real, Real.volume_Ioc]
        linarith
      rw [hmeas]
      have : P / 2 - δ ≤ P / 2 := by linarith
      calc (2 * M + ‖J‖) * Cδ * (P / 2 - δ)
          ≤ (2 * M + ‖J‖) * Cδ * (P / 2) := mul_le_mul_of_nonneg_left this hCnn
        _ = (2 * M + ‖J‖) * (P / 2) * Cδ := by ring
  have hJnorm : ‖J * ((Λ : ℝ) : ℂ)‖ = ‖J‖ * Λ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΛnn]
  have hfinal : ‖J‖ * Λ
      ≤ ‖∫ y in Ioc (0 : ℝ) (P / 2), Ψ y * ((K y : ℝ) : ℂ)‖
        + ‖∫ y in Ioc (0 : ℝ) (P / 2), (Ψ y - J) * ((K y : ℝ) : ℂ)‖ := by
    have heq : J * ((Λ : ℝ) : ℂ)
        = (∫ y in Ioc (0 : ℝ) (P / 2), Ψ y * ((K y : ℝ) : ℂ))
          - ∫ y in Ioc (0 : ℝ) (P / 2), (Ψ y - J) * ((K y : ℝ) : ℂ) := by
      rw [hsplit]
      ring
    rw [← hJnorm, heq]
    exact norm_sub_le _ _
  have herrnorm : ‖∫ y in Ioc (0 : ℝ) (P / 2), (Ψ y - J) * ((K y : ℝ) : ℂ)‖
      ≤ ‖J‖ / 2 * Λ + (2 * M + ‖J‖) * (P / 2) * Cδ := by
    rw [herr]
    exact le_trans (norm_add_le _ _) (add_le_add hnear hfar)
  linarith [hfinal, hbound, herrnorm]

/-- **Putnam's theorem, one-sided form.**  The Fourier coefficients of the periodisation of
nonnegative index cannot all vanish: the periodisation has a nonzero jump at the origin, while a
one-sided spectrum forces its Cauchy transform to be bounded, and the conjugate kernel picks the
jump out with unbounded mass. -/
theorem exists_fourierCoeff_ne_zero {a d : ℝ} (hd : 0 < d) :
    ∃ n : ℕ, (∫ x in Ioc (0 : ℝ) (putnamPeriod d), putnamPeriodTwist a d (n : ℤ) x) ≠ 0 := by
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  set P := putnamPeriod d with hPdef
  set D := putnamPeriodization a d with hDdef
  set M := periodizationBound d with hMdef
  set J : ℂ := D 0 - putnamLeftValue a d with hJdef
  have hP : 0 < P := putnamPeriod_pos hd
  have hMnn : (0 : ℝ) ≤ M := periodizationBound_nonneg d
  have hJne : J ≠ 0 := by
    intro h
    refine putnamLeftValue_sub_ne_zero (a := a) hd ?_
    have hneg : putnamLeftValue a d - D 0 = -J := by rw [hJdef]; ring
    rw [hneg, h, neg_zero]
  have hJpos : 0 < ‖J‖ := norm_pos_iff.mpr hJne
  obtain ⟨δ, hδ0, hδH, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ δ < P / 2 ∧
      ∀ y ∈ Ioc (0 : ℝ) δ, ‖(D y - D (P - y)) - J‖ ≤ ‖J‖ / 2 := by
    have hlim := tendsto_foldedDifference (a := a) hd
    rw [Metric.tendsto_nhdsWithin_nhds] at hlim
    obtain ⟨δ₀, hδ₀, hδ₀'⟩ := hlim (‖J‖ / 2) (by positivity)
    refine ⟨min (δ₀ / 2) (P / 4), by positivity, ?_, ?_⟩
    · calc min (δ₀ / 2) (P / 4) ≤ P / 4 := min_le_right _ _
        _ < P / 2 := by linarith
    · intro y hy
      have hy0 : 0 < y := hy.1
      have hylt : y < δ₀ := by
        have h2 := hy.2
        have h1 : min (δ₀ / 2) (P / 4) ≤ δ₀ / 2 := min_le_left _ _
        linarith
      have hres := hδ₀' (mem_Ioi.mpr hy0)
        (by rw [Real.dist_eq, sub_zero, abs_of_pos hy0]; exact hylt)
      rw [dist_eq_norm] at hres
      exact hres.le
  have hdδ0 : 0 < d * δ := by positivity
  have hdδπ : d * δ < Real.pi := by
    rw [← putnamPeriod_half_mul hd]
    exact mul_lt_mul_of_pos_left hδH hd
  have hcos1 : Real.cos (d * δ) < 1 := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl (0 : ℝ)) hdδπ.le hdδ0
    simpa using this
  have hcos0 : -1 < Real.cos (d * δ) := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi hdδ0.le (le_refl Real.pi) hdδπ
    simpa using this
  have hCpos : 0 < 1 - Real.cos (d * δ) ^ 2 := by nlinarith
  set Cδ : ℝ := 1 / (1 - Real.cos (d * δ) ^ 2) with hCδdef
  have hCδnn : 0 ≤ Cδ := by
    rw [hCδdef]
    positivity
  set B : ℝ := M * P / 2 + (2 * M + ‖J‖) * (P / 2) * Cδ with hBdef
  have hBnn : 0 ≤ B := by
    have h1 : (0 : ℝ) ≤ M * P / 2 := by positivity
    have h2 : (0 : ℝ) ≤ (2 * M + ‖J‖) * (P / 2) * Cδ := by positivity
    linarith
  set L : ℝ := B / (‖J‖ / 2) + 1 with hLdef
  have hLpos : 0 < L := by
    rw [hLdef]
    have : (0 : ℝ) ≤ B / (‖J‖ / 2) := by positivity
    linarith
  set r : ℝ := 1 - Real.exp (-(d * L)) with hrdef
  have hexp1 : Real.exp (-(d * L)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 < d * L := by positivity
    linarith
  have hr0 : 0 ≤ r := by
    rw [hrdef]
    linarith
  have hr1 : r < 1 := by
    rw [hrdef]
    have := Real.exp_pos (-(d * L))
    linarith
  have hone_sub : 1 - r = Real.exp (-(d * L)) := by
    rw [hrdef]
    ring
  have hΛge : L ≤ (Real.log (1 + r) - Real.log (1 - r)) / d := by
    rw [hone_sub, Real.log_exp]
    have hlog : 0 ≤ Real.log (1 + r) := Real.log_nonneg (by linarith)
    rw [le_div_iff₀ hd]
    linarith
  have hest := jump_estimate (a := a) hd hcon hδ0 hδH hδ hr0 hr1
  have h1 : ‖J‖ / 2 * L ≤ ‖J‖ / 2 * ((Real.log (1 + r) - Real.log (1 - r)) / d) :=
    mul_le_mul_of_nonneg_left hΛge (by positivity)
  have h2 : ‖J‖ / 2 * L = B + ‖J‖ / 2 := by
    rw [hLdef]
    field_simp
  linarith [hest, h1, h2]

end RHTower

end
