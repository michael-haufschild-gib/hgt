import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStateOriginFailure

/-!
# Kernel bounds for the shifted ground states

Test-coordinate forms of the ground jumps and of the potential density of `ω_a`, the elementary
bounds on Riemann's kernel and on the shift difference (`Φ ≤ Φ(0)`, `|Φ(y−a) − Φ(y+a)| ≤ Φ(0)`,
monotonicity on the half line), the bounds `ω(t) ≤ 3/(2t)` on `(0,1]` and `ω(t) ≤ (3/2) e^{−t/2}` on
`[1,∞)` for the archimedean Lévy density, integrability of `t ↦ ω(t) t` on `(0,∞)`, and Lipschitz
bounds on compact intervals for `C¹` functions. These are the ingredients of the admissibility of
`ω_a` for the folded ground-state representation.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-! ### Test-coordinate forms -/

theorem foldedShiftGenerator_shiftedGroundState (a t x : ℝ) :
    foldedShiftGenerator (shiftedGroundState a) t x =
      shiftDifference a x * (riemannKernelReal (x + t) + riemannKernelReal |x - t|) -
        riemannKernelReal x * (shiftDifference a (x + t) + shiftDifference a |x - t|) := by
  unfold foldedShiftGenerator
  rw [← riemannKernelReal_abs' (x - t)]
  have h1 := riemannKernelReal_mul_shiftedGroundState a x
  have h2 := riemannKernelReal_mul_shiftedGroundState a (x + t)
  have h3 := riemannKernelReal_mul_shiftedGroundState a |x - t|
  linear_combination (riemannKernelReal (x + t) + riemannKernelReal |x - t|) * h1 -
    riemannKernelReal x * h2 - riemannKernelReal x * h3

theorem sameSideGroundJump_shiftedGroundState (a : ℝ) (u : ℝ → ℝ) (t x : ℝ) :
    sameSideGroundJump (shiftedGroundState a) u t x =
      shiftDifference a x * shiftDifference a (x + t) * (u x - u (x + t)) ^ 2 := by
  unfold sameSideGroundJump
  have h1 := riemannKernelReal_mul_shiftedGroundState a x
  have h2 := riemannKernelReal_mul_shiftedGroundState a (x + t)
  linear_combination
    (riemannKernelReal (x + t) * shiftedGroundState a (x + t) * (u x - u (x + t)) ^ 2) * h1 +
      (shiftDifference a x * (u x - u (x + t)) ^ 2) * h2

theorem reflectedGroundJump_shiftedGroundState (a : ℝ) (u : ℝ → ℝ) (t x : ℝ) :
    reflectedGroundJump (shiftedGroundState a) u t x =
      shiftDifference a x * shiftDifference a (t - x) * (u x + u (t - x)) ^ 2 := by
  unfold reflectedGroundJump
  have h1 := riemannKernelReal_mul_shiftedGroundState a x
  have h2 := riemannKernelReal_mul_shiftedGroundState a (t - x)
  linear_combination
    (riemannKernelReal (t - x) * shiftedGroundState a (t - x) * (u x + u (t - x)) ^ 2) * h1 +
      (shiftDifference a x * (u x + u (t - x)) ^ 2) * h2

/-- The potential density of `ω_a` in test coordinates. -/
def shiftedPotentialKernel (a t x : ℝ) : ℝ :=
  shiftDifference a x *
    (shiftedGroundState a x * (riemannKernelReal (x + t) + riemannKernelReal |x - t|) -
      (shiftDifference a (x + t) + shiftDifference a |x - t|))

theorem groundPotentialDensity_shiftedGroundState (a : ℝ) (u : ℝ → ℝ) (t x : ℝ) :
    groundPotentialDensity (shiftedGroundState a) u t x = u x ^ 2 * shiftedPotentialKernel a t x := by
  unfold groundPotentialDensity shiftedPotentialKernel
  rw [foldedShiftGenerator_shiftedGroundState]
  have h1 := riemannKernelReal_mul_shiftedGroundState a x
  linear_combination (-(u x ^ 2) * (shiftDifference a (x + t) + shiftDifference a |x - t|)) * h1

/-- The potential kernel as a sum of four differences: the form used for the small-shift bound. -/
theorem shiftedPotentialKernel_eq_differences (a t x : ℝ) :
    shiftedPotentialKernel a t x =
      shiftDifference a x *
        (shiftedGroundState a x * (riemannKernelReal (x + t) - riemannKernelReal x) +
          shiftedGroundState a x * (riemannKernelReal |x - t| - riemannKernelReal x) -
          (shiftDifference a (x + t) - shiftDifference a x) -
          (shiftDifference a |x - t| - shiftDifference a x)) := by
  unfold shiftedPotentialKernel
  have h1 := riemannKernelReal_mul_shiftedGroundState a x
  linear_combination (2 * shiftDifference a x) * h1

/-! ### Elementary bounds on the kernel and the shift difference -/

theorem riemannKernelReal_antitone_of_nonneg {s r : ℝ} (hs : 0 ≤ s) (hsr : s ≤ r) :
    riemannKernelReal r ≤ riemannKernelReal s :=
  strictAntiOn_riemannKernelReal_Ici.antitoneOn hs (hs.trans hsr) hsr

theorem riemannKernelReal_le_zero_point (y : ℝ) : riemannKernelReal y ≤ riemannKernelReal 0 := by
  rw [← riemannKernelReal_abs' y]
  exact riemannKernelReal_antitone_of_nonneg le_rfl (abs_nonneg y)

theorem abs_shiftDifference_le (a y : ℝ) : |shiftDifference a y| ≤ riemannKernelReal 0 := by
  unfold shiftDifference
  have h1 := riemannKernelReal_le_zero_point (y - a)
  have h2 := riemannKernelReal_le_zero_point (y + a)
  have h3 := riemannKernelReal_pos (y - a)
  have h4 := riemannKernelReal_pos (y + a)
  rw [abs_le]
  constructor <;> linarith

theorem shiftDifference_le_kernel (a y : ℝ) : shiftDifference a y ≤ riemannKernelReal (y - a) := by
  unfold shiftDifference
  linarith [riemannKernelReal_pos (y + a)]

theorem shiftDifference_nonneg_of_nonneg {a y : ℝ} (ha : 0 ≤ a) (hy : 0 ≤ y) :
    0 ≤ shiftDifference a y := by
  unfold shiftDifference
  rw [← riemannKernelReal_abs' (y - a)]
  have habs : |y - a| ≤ y + a := by
    rw [abs_le]
    constructor <;> linarith
  linarith [riemannKernelReal_antitone_of_nonneg (abs_nonneg (y - a)) habs]

theorem abs_shiftDifference_le_kernel_of_nonneg {a y : ℝ} (ha : 0 ≤ a) (hy : 0 ≤ y) :
    |shiftDifference a y| ≤ riemannKernelReal (y - a) := by
  rw [abs_of_nonneg (shiftDifference_nonneg_of_nonneg ha hy)]
  exact shiftDifference_le_kernel a y

/-- Below a cutoff `c₀ > 0`, Riemann's kernel at `t − c₀` is at least `Φ(c₀)`. -/
theorem riemannKernelReal_sub_ge_of_le {t c₀ : ℝ} (ht : 0 ≤ t) (htc : t ≤ c₀) :
    riemannKernelReal c₀ ≤ riemannKernelReal (t - c₀) := by
  rw [← riemannKernelReal_abs' (t - c₀)]
  apply riemannKernelReal_antitone_of_nonneg (abs_nonneg _)
  rw [abs_le]
  constructor <;> linarith

/-! ### The archimedean Lévy density -/

theorem two_mul_div_le_one_sub_exp {t : ℝ} (ht : 0 ≤ t) :
    2 * t / (1 + 2 * t) ≤ 1 - Real.exp (-2 * t) := by
  have h := Real.add_one_le_exp (2 * t)
  have hpos : 0 < 1 + 2 * t := by linarith
  have hexp : Real.exp (-2 * t) ≤ 1 / (1 + 2 * t) := by
    rw [show -2 * t = -(2 * t) by ring, Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le hpos (by linarith)
  have hid : 1 - 1 / (1 + 2 * t) = 2 * t / (1 + 2 * t) := by
    field_simp
    ring
  linarith

theorem archLevyDensity_le_of_le_one {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    archLevyDensity t ≤ 3 / 2 / t := by
  unfold archLevyDensity
  have hden : 2 * t / 3 ≤ 1 - Real.exp (-2 * t) := by
    have h1 := two_mul_div_le_one_sub_exp ht0.le
    have h2 : 2 * t / 3 ≤ 2 * t / (1 + 2 * t) :=
      div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith)
    linarith
  have hnum : Real.exp (-t / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hdpos : 0 < 2 * t / 3 := by positivity
  calc Real.exp (-t / 2) / (1 - Real.exp (-2 * t)) ≤ 1 / (2 * t / 3) :=
        div_le_div₀ (by norm_num) hnum hdpos hden
    _ = 3 / 2 / t := by
        field_simp

theorem archLevyDensity_le_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    archLevyDensity t ≤ 3 / 2 * Real.exp (-t / 2) := by
  unfold archLevyDensity
  have h1 := two_mul_div_le_one_sub_exp (zero_le_one' ℝ)
  norm_num at h1
  have hmono : Real.exp (-2 * t) ≤ Real.exp (-2) := Real.exp_le_exp.mpr (by linarith)
  have hden : 2 / 3 ≤ 1 - Real.exp (-2 * t) := by
    linarith
  have hexp := Real.exp_pos (-t / 2)
  calc Real.exp (-t / 2) / (1 - Real.exp (-2 * t)) ≤ Real.exp (-t / 2) / (2 / 3) :=
        div_le_div_of_nonneg_left hexp.le (by norm_num) hden
    _ = 3 / 2 * Real.exp (-t / 2) := by ring

/-- `ω(t) t ≤ 6 e^{(1−t)/4}` on `(0,∞)`. -/
theorem archLevyDensity_mul_self_le {t : ℝ} (ht : 0 < t) :
    archLevyDensity t * t ≤ 6 * Real.exp ((1 - t) / 4) := by
  rcases le_or_gt t 1 with h1 | h1
  · have hb := archLevyDensity_le_of_le_one ht h1
    have h2 : archLevyDensity t * t ≤ 3 / 2 := by
      calc archLevyDensity t * t ≤ 3 / 2 / t * t := mul_le_mul_of_nonneg_right hb ht.le
        _ = 3 / 2 := by field_simp
    have h3 : (1 : ℝ) ≤ Real.exp ((1 - t) / 4) := Real.one_le_exp_iff.mpr (by linarith)
    nlinarith
  · have hb := archLevyDensity_le_of_one_le h1.le
    have h2 : archLevyDensity t * t ≤ 3 / 2 * Real.exp (-t / 2) * t :=
      mul_le_mul_of_nonneg_right hb ht.le
    have h3 : t ≤ 4 * Real.exp (t / 4) := by
      have := Real.add_one_le_exp (t / 4)
      linarith
    have h4 : 3 / 2 * Real.exp (-t / 2) * t ≤ 6 * Real.exp ((1 - t) / 4) := by
      have he : Real.exp (-t / 2) * Real.exp (t / 4) = Real.exp (-t / 4) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have h5 : Real.exp (-t / 4) ≤ Real.exp ((1 - t) / 4) := Real.exp_le_exp.mpr (by linarith)
      have hpos := Real.exp_pos (-t / 2)
      calc 3 / 2 * Real.exp (-t / 2) * t ≤ 3 / 2 * Real.exp (-t / 2) * (4 * Real.exp (t / 4)) :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = 6 * (Real.exp (-t / 2) * Real.exp (t / 4)) := by ring
        _ = 6 * Real.exp (-t / 4) := by rw [he]
        _ ≤ 6 * Real.exp ((1 - t) / 4) := by linarith
    linarith

theorem measurable_archLevyDensity_mul_id : Measurable fun t : ℝ => archLevyDensity t * t :=
  measurable_archLevyDensity.mul measurable_id

/-- `t ↦ ω(t) t` is integrable on `(0,∞)`. -/
theorem integrableOn_archLevyDensity_mul_id :
    IntegrableOn (fun t : ℝ => archLevyDensity t * t) (Ioi 0) := by
  have hg : IntegrableOn (fun t : ℝ => 6 * Real.exp ((1 - t) / 4)) (Ioi 0) := by
    have h : IntegrableOn (fun t : ℝ => 6 * Real.exp (1 / 4) * Real.exp (-(1 / 4) * t)) (Ioi 0) :=
      (exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 1 / 4)).const_mul (6 * Real.exp (1 / 4))
    refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
    rw [show (1 - t) / 4 = 1 / 4 + -(1 / 4) * t by ring, Real.exp_add]
    ring
  refine Integrable.mono' hg measurable_archLevyDensity_mul_id.aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
  have ht0 : 0 < t := ht
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (archLevyDensity_pos ht0).le ht0.le)]
  exact archLevyDensity_mul_self_le ht0

/-! ### Lipschitz and boundedness helpers -/

/-- A `C¹` function is Lipschitz on every compact interval. -/
theorem exists_lipschitz_bound_on_Icc {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (A B : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ Icc A B, ∀ y ∈ Icc A B, |f y - f x| ≤ L * |y - x| := by
  obtain ⟨C, hC⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn (hf.continuous_deriv le_rfl).continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x hx y hy => ?_⟩
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (C := max C 0)
    (fun z _ => (hf.differentiable one_ne_zero).differentiableAt)
    (fun z hz => (hC z hz).trans (le_max_left C 0)) (convex_Icc A B) hx hy
  simpa [Real.norm_eq_abs] using h

/-- A `C¹` function with compact support is globally Lipschitz. -/
theorem exists_lipschitz_bound_of_compactSupport {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y, |f y - f x| ≤ L * |y - x| := by
  obtain ⟨C, hC⟩ := (hf.continuous_deriv le_rfl).bounded_above_of_compact_support hfc.deriv
  refine ⟨max C 0, le_max_right _ _, fun x y => ?_⟩
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (C := max C 0)
    (fun z _ => (hf.differentiable one_ne_zero).differentiableAt)
    (fun z _ => (hC z).trans (le_max_left C 0)) convex_univ (mem_univ x) (mem_univ y)
  simpa [Real.norm_eq_abs] using h

/-- A compactly supported function vanishes outside a symmetric interval of radius at least one. -/
theorem exists_support_radius {f : ℝ → ℝ} (hfc : HasCompactSupport f) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ x, R < |x| → f x = 0 := by
  obtain ⟨r, hr⟩ := hfc.isBounded.subset_closedBall (0 : ℝ)
  refine ⟨max r 1, le_max_right _ _, fun x hx => ?_⟩
  by_contra h
  have hmem : x ∈ tsupport f := subset_tsupport f h
  have := hr hmem
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
  linarith [le_max_left r 1]

theorem contDiff_shiftDifference (a : ℝ) : ContDiff ℝ 1 (shiftDifference a) := by
  unfold shiftDifference
  exact (contDiff_riemannKernelReal.comp (contDiff_id.sub contDiff_const)).sub
    (contDiff_riemannKernelReal.comp (contDiff_id.add contDiff_const))

theorem contDiff_riemannKernelReal_one : ContDiff ℝ 1 riemannKernelReal :=
  contDiff_riemannKernelReal

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
