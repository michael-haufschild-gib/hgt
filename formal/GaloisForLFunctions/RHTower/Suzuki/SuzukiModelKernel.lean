import GaloisForLFunctions.RHTower.CauchyKernelTotality
import GaloisForLFunctions.RHTower.Suzuki.SuzukiClarkMeasure
import GaloisForLFunctions.HTGeometry.UpperHalfPlaneCauchyFormula

noncomputable section

/-!
# The reproducing kernel of the model space

`k_w(z) = (i/2π)(1 - conj(Θ(w)) Θ(z))/(z - conj w)` is the reproducing kernel of `K(Θ_ξ)` at a
point `w` of the upper half-plane.  Everything about it is elementary once the Riemann hypothesis
makes `A/E` — hence `Θ = 2(A/E) - 1` — holomorphic and bounded on the closed upper half-plane.

* The kernel is a Hardy function: it decays like `1/|z|` there, so its Cauchy transform vanishes
  below the axis, and those kernels are total in the orthogonal complement of `H²`.
* `Θ conj(k_w)` is the divided slope `(-i/2π) (Θ(z) - Θ(w))/(z - w)`, again holomorphic and
  decaying, hence again a Hardy function.  So `k_w` lies in `K(Θ) = H² ∩ (Θ H²)^⊥`.
* Against any element of the model space the pairing collapses: the `Θ`-twisted half is the Cauchy
  transform of the conjugate of a Hardy function, which vanishes above the axis.  What remains is a
  single Cauchy transform, so an element with a holomorphic decaying representative is reproduced.
* Consequently the kernels are total: an element of the model space annihilated by all of them has
  a Cauchy transform vanishing in *both* half-planes, so it lies in `H²` and in its orthogonal
  complement at once.
-/

open MeasureTheory Set Complex Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

theorem norm_sq_ofReal_sub (w : ℂ) (x : ℝ) :
    ‖((x : ℝ) : ℂ) - w‖ ^ (2 : ℕ) = (x - w.re) ^ (2 : ℕ) + w.im ^ (2 : ℕ) := by
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  simp
  ring

theorem memLp_two_of_poisson_bound {u : ℝ → ℂ} {a b D : ℝ} (hb : 0 < b)
    (hmeas : AEStronglyMeasurable u volume)
    (hbd : ∀ x : ℝ, ‖u x‖ ^ (2 : ℕ) ≤ D / ((x - a) ^ (2 : ℕ) + b ^ (2 : ℕ))) :
    MemLp u 2 volume := by
  refine (memLp_two_iff_integrable_sq_norm hmeas).mpr ?_
  refine Integrable.mono'
    ((integrable_inv_sub_sq_add_sq (a := a) hb).const_mul D) (hmeas.norm.pow 2) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h := hbd x
  rwa [div_eq_mul_inv] at h

/-- **A boundary function holomorphic and decaying on the closed upper half-plane is a Hardy
function.**  Its Cauchy transform vanishes below the axis, and those kernels are total. -/
theorem mem_hardyL2_of_upperHalfPlane_decay {u : ℂ → ℂ} {M R : ℝ}
    (hdiff : ∀ z : ℂ, 0 ≤ z.im → DifferentiableAt ℂ u z) (hR : 0 < R)
    (hfar : ∀ z : ℂ, 0 ≤ z.im → R ≤ ‖z‖ → ‖u z‖ ≤ M / ‖z‖)
    (hmem : MemLp (fun x : ℝ => u ((x : ℝ) : ℂ)) 2 (volume : Measure ℝ)) :
    hmem.toLp _ ∈ hardyL2 := by
  refine mem_hardyL2_of_cauchyTransform_eq_zero ?_
  intro v hv
  have hrw : (∫ x : ℝ, ((hmem.toLp (fun x : ℝ => u ((x : ℝ) : ℂ)) :
        Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x / (((x : ℝ) : ℂ) - v))
      = ∫ x : ℝ, u ((x : ℝ) : ℂ) / (((x : ℝ) : ℂ) - v) := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hmem.coeFn_toLp] with x h1
    rw [h1]
  rw [hrw]
  have hMnn : (0 : ℝ) ≤ M := by
    have hz : (0 : ℝ) ≤ ((R : ℂ) * I).im := by simp [le_of_lt hR]
    have hn : ‖(R : ℂ) * I‖ = R := by
      rw [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hR, mul_one]
    have h := hfar ((R : ℂ) * I) hz (by rw [hn])
    rw [hn] at h
    have h0 : (0 : ℝ) ≤ M / R := le_trans (norm_nonneg _) h
    rcases div_nonneg_iff.mp h0 with ⟨hm, _⟩ | ⟨_, hbad⟩
    · exact hm
    · linarith
  set R' : ℝ := 2 * (R + ‖v‖) + 1 with hR'def
  have hvnn : (0 : ℝ) ≤ ‖v‖ := norm_nonneg v
  have hR'0 : 0 < R' := by rw [hR'def]; linarith
  refine integral_eq_zero_of_upperHalfPlane_farDecay
    (u := fun z : ℂ => u z / (z - v)) (M := 2 * M) (R := R') ?_ hR'0 ?_
  · intro z hz
    have hzv : z - v ≠ 0 := by
      intro h
      have hzv' : z = v := sub_eq_zero.mp h
      rw [hzv'] at hz
      linarith
    exact (hdiff z hz).div (differentiableAt_id.sub_const _) hzv
  · intro z hz hzR
    have hzn : 0 < ‖z‖ := lt_of_lt_of_le hR'0 hzR
    have hhalf : ‖v‖ ≤ ‖z‖ / 2 := by rw [hR'def] at hzR; linarith
    have hzv : ‖z‖ / 2 ≤ ‖z - v‖ := by
      have h := norm_sub_norm_le z v
      linarith
    have hzh : 0 < ‖z‖ / 2 := by linarith
    have hu := hfar z hz (by rw [hR'def] at hzR; linarith)
    rw [norm_div, div_le_div_iff₀ (lt_of_lt_of_le hzh hzv) (by positivity)]
    have huz : ‖u z‖ * ‖z‖ ≤ M := by
      have h := mul_le_mul_of_nonneg_right hu (le_of_lt hzn)
      rwa [div_mul_cancel₀ _ (ne_of_gt hzn)] at h
    nlinarith [norm_nonneg (u z)]

/-! ## The meromorphic inner function on the closed upper half-plane -/

theorem differentiableAt_suzukiThetaMero_of_rh (hRH : RiemannHypothesis) {z : ℂ}
    (hz : 0 ≤ z.im) : DifferentiableAt ℂ suzukiThetaMero z := by
  have h : DifferentiableAt ℂ (fun z : ℂ => 2 * suzukiHalfInner z - 1) z :=
    ((differentiableAt_suzukiHalfInner_of_rh hRH hz).const_mul 2).sub_const 1
  exact h

theorem norm_suzukiThetaMero_le_of_rh (hRH : RiemannHypothesis) {z : ℂ} (hz : 0 ≤ z.im) :
    ‖suzukiThetaMero z‖ ≤ 3 := by
  have h := norm_suzukiHalfInner_le_one_of_rh hRH hz
  calc ‖suzukiThetaMero z‖ ≤ ‖2 * suzukiHalfInner z‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 * ‖suzukiHalfInner z‖ + 1 := by
        rw [norm_mul, norm_one]
        norm_num
    _ ≤ 3 := by linarith

/-! ## The reproducing kernel of the model space -/

/-- The reproducing kernel of `K(Θ)` at a point of the upper half-plane. -/
def suzukiModelKernel (w z : ℂ) : ℂ :=
  (I / (2 * (Real.pi : ℂ))) * (1 - (starRingEnd ℂ) (suzukiThetaMero w) * suzukiThetaMero z)
    / (z - (starRingEnd ℂ) w)

/-- The size constant of the kernel. -/
def suzukiModelKernelBound (w : ℂ) : ℝ :=
  (1 + 3 * ‖suzukiThetaMero w‖) / (2 * Real.pi)

theorem suzukiModelKernelBound_nonneg (w : ℂ) : 0 ≤ suzukiModelKernelBound w := by
  have := Real.pi_pos
  have := norm_nonneg (suzukiThetaMero w)
  unfold suzukiModelKernelBound
  positivity

theorem conj_im_neg {w : ℂ} (hw : 0 < w.im) : ((starRingEnd ℂ) w).im < 0 := by simpa using hw

theorem sub_conj_ne_zero {w z : ℂ} (hw : 0 < w.im) (hz : 0 ≤ z.im) :
    z - (starRingEnd ℂ) w ≠ 0 := by
  intro h
  have hzw : z = (starRingEnd ℂ) w := sub_eq_zero.mp h
  rw [hzw] at hz
  have := conj_im_neg hw
  linarith

theorem norm_suzukiModelKernel_le (hRH : RiemannHypothesis) {w z : ℂ} (hw : 0 < w.im)
    (hz : 0 ≤ z.im) :
    ‖suzukiModelKernel w z‖ ≤ suzukiModelKernelBound w / ‖z - (starRingEnd ℂ) w‖ := by
  have hpi := Real.pi_pos
  have hnum : ‖1 - (starRingEnd ℂ) (suzukiThetaMero w) * suzukiThetaMero z‖
      ≤ 1 + 3 * ‖suzukiThetaMero w‖ := by
    calc ‖1 - (starRingEnd ℂ) (suzukiThetaMero w) * suzukiThetaMero z‖
        ≤ ‖(1 : ℂ)‖ + ‖(starRingEnd ℂ) (suzukiThetaMero w) * suzukiThetaMero z‖ :=
          norm_sub_le _ _
      _ = 1 + ‖suzukiThetaMero w‖ * ‖suzukiThetaMero z‖ := by
          rw [norm_one, norm_mul, RCLike.norm_conj]
      _ ≤ 1 + ‖suzukiThetaMero w‖ * 3 := by
          have h3 := norm_suzukiThetaMero_le_of_rh hRH hz
          have := norm_nonneg (suzukiThetaMero w)
          nlinarith
      _ = 1 + 3 * ‖suzukiThetaMero w‖ := by ring
  have hden : 0 < ‖z - (starRingEnd ℂ) w‖ :=
    norm_pos_iff.mpr (sub_conj_ne_zero hw hz)
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  have hK : ‖suzukiModelKernel w z‖
      = ‖1 - (starRingEnd ℂ) (suzukiThetaMero w) * suzukiThetaMero z‖ /
        (2 * Real.pi * ‖z - (starRingEnd ℂ) w‖) := by
    rw [suzukiModelKernel, norm_div, norm_mul, norm_div, Complex.norm_I, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi, h2]
    field_simp
  rw [hK, suzukiModelKernelBound, div_div]
  gcongr


theorem differentiableAt_suzukiModelKernel (hRH : RiemannHypothesis) {w : ℂ} (hw : 0 < w.im)
    {z : ℂ} (hz : 0 ≤ z.im) : DifferentiableAt ℂ (suzukiModelKernel w) z := by
  have hnum : DifferentiableAt ℂ
      (fun ζ : ℂ => (I / (2 * (Real.pi : ℂ))) *
        (1 - (starRingEnd ℂ) (suzukiThetaMero w) * suzukiThetaMero ζ)) z :=
    (((differentiableAt_suzukiThetaMero_of_rh hRH hz).const_mul _).const_sub 1).const_mul _
  exact hnum.div (differentiableAt_id.sub_const _) (sub_conj_ne_zero hw hz)

theorem continuous_suzukiModelKernel_ofReal (hRH : RiemannHypothesis) {w : ℂ} (hw : 0 < w.im) :
    Continuous fun x : ℝ => suzukiModelKernel w ((x : ℝ) : ℂ) := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  have hd : DifferentiableAt ℂ (suzukiModelKernel w) ((x : ℝ) : ℂ) :=
    differentiableAt_suzukiModelKernel hRH hw (by simp)
  exact hd.continuousAt.comp Complex.continuous_ofReal.continuousAt

theorem norm_sq_ofReal_sub_conj (w : ℂ) (x : ℝ) :
    ‖((x : ℝ) : ℂ) - (starRingEnd ℂ) w‖ ^ (2 : ℕ) = (x - w.re) ^ (2 : ℕ) + w.im ^ (2 : ℕ) := by
  rw [norm_sq_ofReal_sub]
  simp

theorem memLp_suzukiModelKernel (hRH : RiemannHypothesis) {w : ℂ} (hw : 0 < w.im) :
    MemLp (fun x : ℝ => suzukiModelKernel w ((x : ℝ) : ℂ)) 2 (volume : Measure ℝ) := by
  refine memLp_two_of_poisson_bound (a := w.re) (b := w.im)
    (D := (suzukiModelKernelBound w) ^ (2 : ℕ)) hw
    (continuous_suzukiModelKernel_ofReal hRH hw).aestronglyMeasurable ?_
  intro x
  have hz : (0 : ℝ) ≤ (((x : ℝ) : ℂ)).im := by simp
  have h := norm_suzukiModelKernel_le hRH hw hz
  have hden : 0 < ‖((x : ℝ) : ℂ) - (starRingEnd ℂ) w‖ :=
    norm_pos_iff.mpr (sub_conj_ne_zero hw hz)
  have hsq := norm_sq_ofReal_sub_conj w x
  have hB := suzukiModelKernelBound_nonneg w
  have hle : ‖suzukiModelKernel w ((x : ℝ) : ℂ)‖ ^ (2 : ℕ)
      ≤ (suzukiModelKernelBound w) ^ (2 : ℕ) / ‖((x : ℝ) : ℂ) - (starRingEnd ℂ) w‖ ^ (2 : ℕ) := by
    rw [← div_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  rwa [hsq] at hle

theorem suzukiModelKernel_mem_hardyL2 (hRH : RiemannHypothesis) {w : ℂ} (hw : 0 < w.im) :
    (memLp_suzukiModelKernel hRH hw).toLp _ ∈ hardyL2 := by
  have hwnn : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
  have hB := suzukiModelKernelBound_nonneg w
  refine mem_hardyL2_of_upperHalfPlane_decay
    (u := suzukiModelKernel w) (M := 2 * suzukiModelKernelBound w) (R := 2 * ‖w‖ + 1)
    (fun z hz => differentiableAt_suzukiModelKernel hRH hw hz) (by linarith) ?_
    (memLp_suzukiModelKernel hRH hw)
  intro z hz hzR
  have hzn : 0 < ‖z‖ := by linarith
  have hhalf : ‖w‖ ≤ ‖z‖ / 2 := by linarith
  have hwn : ‖(starRingEnd ℂ) w‖ = ‖w‖ := by simp
  have hzw : ‖z‖ / 2 ≤ ‖z - (starRingEnd ℂ) w‖ := by
    have h := norm_sub_norm_le z ((starRingEnd ℂ) w)
    rw [hwn] at h
    linarith
  have hzh : 0 < ‖z‖ / 2 := by linarith
  have h := norm_suzukiModelKernel_le hRH hw hz
  calc ‖suzukiModelKernel w z‖
      ≤ suzukiModelKernelBound w / ‖z - (starRingEnd ℂ) w‖ := h
    _ ≤ suzukiModelKernelBound w / (‖z‖ / 2) := by gcongr
    _ = 2 * suzukiModelKernelBound w / ‖z‖ := by
        field_simp


/-! ## The `Θ`-conjugate of the kernel -/

/-- `Θ · conj(k_w)` on the axis: a divided slope of the inner function. -/
def suzukiModelKernelStar (w z : ℂ) : ℂ :=
  (-I / (2 * (Real.pi : ℂ))) * dslope suzukiThetaMero w z

theorem differentiableAt_dslope_suzukiThetaMero (hRH : RiemannHypothesis) {w : ℂ}
    (hw : 0 < w.im) {z : ℂ} (hz : 0 ≤ z.im) :
    DifferentiableAt ℂ (dslope suzukiThetaMero w) z := by
  rcases eq_or_ne z w with rfl | hne
  · refine differentiableAt_dslope_of_eventually_differentiableAt ?_
    filter_upwards [Metric.ball_mem_nhds z hw] with ζ hζ
    exact differentiableAt_suzukiThetaMero_of_rh hRH (by
      have h2 : ‖ζ - z‖ < z.im := by
        rw [Metric.mem_ball, Complex.dist_eq] at hζ
        exact hζ
      have h1 : |(ζ - z).im| ≤ ‖ζ - z‖ := Complex.abs_im_le_norm (ζ - z)
      have h3 : (ζ - z).im = ζ.im - z.im := by simp
      rw [h3] at h1
      have h4 := abs_lt.mp (lt_of_le_of_lt h1 h2)
      linarith [h4.1])
  · exact differentiableAt_dslope_of_ne hne (differentiableAt_suzukiThetaMero_of_rh hRH hz)

theorem differentiableAt_suzukiModelKernelStar (hRH : RiemannHypothesis) {w : ℂ}
    (hw : 0 < w.im) {z : ℂ} (hz : 0 ≤ z.im) :
    DifferentiableAt ℂ (suzukiModelKernelStar w) z :=
  (differentiableAt_dslope_suzukiThetaMero hRH hw hz).const_mul _

theorem norm_suzukiModelKernelStar_le (hRH : RiemannHypothesis) {w : ℂ} (hw : 0 < w.im)
    {z : ℂ} (hz : 0 ≤ z.im) (hne : z ≠ w) :
    ‖suzukiModelKernelStar w z‖ ≤ (6 / (2 * Real.pi)) / ‖z - w‖ := by
  have hpi := Real.pi_pos
  have hden : 0 < ‖z - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hnum : ‖suzukiThetaMero z - suzukiThetaMero w‖ ≤ 6 := by
    have h1 := norm_suzukiThetaMero_le_of_rh hRH hz
    have h2 := norm_suzukiThetaMero_le_of_rh hRH hw.le
    calc ‖suzukiThetaMero z - suzukiThetaMero w‖
        ≤ ‖suzukiThetaMero z‖ + ‖suzukiThetaMero w‖ := norm_sub_le _ _
      _ ≤ 6 := by linarith
  have hval : ‖suzukiModelKernelStar w z‖
      = ‖suzukiThetaMero z - suzukiThetaMero w‖ / (2 * Real.pi * ‖z - w‖) := by
    rw [suzukiModelKernelStar, dslope_of_ne _ hne, slope_def_field, norm_mul, norm_div,
      norm_div, norm_neg, Complex.norm_I, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hpi]
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2]
    field_simp
  rw [hval, div_div]
  gcongr

theorem continuous_suzukiModelKernelStar_ofReal (hRH : RiemannHypothesis) {w : ℂ}
    (hw : 0 < w.im) : Continuous fun x : ℝ => suzukiModelKernelStar w ((x : ℝ) : ℂ) := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  have hd : DifferentiableAt ℂ (suzukiModelKernelStar w) ((x : ℝ) : ℂ) :=
    differentiableAt_suzukiModelKernelStar hRH hw (by simp)
  exact hd.continuousAt.comp Complex.continuous_ofReal.continuousAt

theorem ofReal_ne_of_im_pos {w : ℂ} (hw : 0 < w.im) (x : ℝ) : ((x : ℝ) : ℂ) ≠ w := by
  intro h
  rw [← h] at hw
  simp at hw

theorem memLp_suzukiModelKernelStar (hRH : RiemannHypothesis) {w : ℂ} (hw : 0 < w.im) :
    MemLp (fun x : ℝ => suzukiModelKernelStar w ((x : ℝ) : ℂ)) 2 (volume : Measure ℝ) := by
  have hpi := Real.pi_pos
  refine memLp_two_of_poisson_bound (a := w.re) (b := w.im)
    (D := (6 / (2 * Real.pi)) ^ (2 : ℕ)) hw
    (continuous_suzukiModelKernelStar_ofReal hRH hw).aestronglyMeasurable ?_
  intro x
  have hz : (0 : ℝ) ≤ (((x : ℝ) : ℂ)).im := by simp
  have h := norm_suzukiModelKernelStar_le hRH hw hz (ofReal_ne_of_im_pos hw x)
  have hsq := norm_sq_ofReal_sub w x
  have hle : ‖suzukiModelKernelStar w ((x : ℝ) : ℂ)‖ ^ (2 : ℕ)
      ≤ (6 / (2 * Real.pi)) ^ (2 : ℕ) / ‖((x : ℝ) : ℂ) - w‖ ^ (2 : ℕ) := by
    rw [← div_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  rwa [hsq] at hle

theorem suzukiModelKernelStar_mem_hardyL2 (hRH : RiemannHypothesis) {w : ℂ} (hw : 0 < w.im) :
    (memLp_suzukiModelKernelStar hRH hw).toLp _ ∈ hardyL2 := by
  have hpi := Real.pi_pos
  have hwnn : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
  have hBnn : (0 : ℝ) ≤ 6 / (2 * Real.pi) := by positivity
  refine mem_hardyL2_of_upperHalfPlane_decay
    (u := suzukiModelKernelStar w) (M := 2 * (6 / (2 * Real.pi))) (R := 2 * ‖w‖ + 1)
    (fun z hz => differentiableAt_suzukiModelKernelStar hRH hw hz) (by linarith) ?_
    (memLp_suzukiModelKernelStar hRH hw)
  intro z hz hzR
  have hzn : 0 < ‖z‖ := by linarith
  have hhalf : ‖w‖ ≤ ‖z‖ / 2 := by linarith
  have hzw : ‖z‖ / 2 ≤ ‖z - w‖ := by
    have h := norm_sub_norm_le z w
    linarith
  have hzh : 0 < ‖z‖ / 2 := by linarith
  have hne : z ≠ w := by
    intro h
    rw [h] at hzn hzw
    rw [sub_self, norm_zero] at hzw
    linarith
  calc ‖suzukiModelKernelStar w z‖
      ≤ (6 / (2 * Real.pi)) / ‖z - w‖ := norm_suzukiModelKernelStar_le hRH hw hz hne
    _ ≤ (6 / (2 * Real.pi)) / (‖z‖ / 2) := by gcongr
    _ = 2 * (6 / (2 * Real.pi)) / ‖z‖ := by
        field_simp


theorem conj_suzukiModelKernel_ofReal {w : ℂ} (x : ℝ) :
    (starRingEnd ℂ) (suzukiModelKernel w ((x : ℝ) : ℂ))
      = (-I / (2 * (Real.pi : ℂ))) *
        (1 - suzukiThetaMero w * (starRingEnd ℂ) (suzukiThetaMero ((x : ℝ) : ℂ)))
        / (((x : ℝ) : ℂ) - w) := by
  rw [suzukiModelKernel, map_div₀, map_mul, map_sub, map_one, map_mul, Complex.conj_conj,
    map_div₀, Complex.conj_I, map_mul, map_ofNat, Complex.conj_ofReal, map_sub,
    Complex.conj_ofReal, Complex.conj_conj]

/-- **On the axis the inner function turns the conjugated kernel into a divided slope.** -/
theorem suzukiThetaMero_mul_conj_suzukiModelKernel {w : ℂ} (hw : 0 < w.im) {x : ℝ}
    (hunit : suzukiThetaMero ((x : ℝ) : ℂ) * (starRingEnd ℂ) (suzukiThetaMero ((x : ℝ) : ℂ))
      = 1) :
    suzukiThetaMero ((x : ℝ) : ℂ) * (starRingEnd ℂ) (suzukiModelKernel w ((x : ℝ) : ℂ))
      = suzukiModelKernelStar w ((x : ℝ) : ℂ) := by
  have key : suzukiThetaMero ((x : ℝ) : ℂ) *
      (1 - suzukiThetaMero w * (starRingEnd ℂ) (suzukiThetaMero ((x : ℝ) : ℂ)))
      = suzukiThetaMero ((x : ℝ) : ℂ) - suzukiThetaMero w := by
    linear_combination (-suzukiThetaMero w) * hunit
  rw [conj_suzukiModelKernel_ofReal, suzukiModelKernelStar,
    dslope_of_ne _ (ofReal_ne_of_im_pos hw x), slope_def_field]
  rw [show suzukiThetaMero ((x : ℝ) : ℂ) * ((-I / (2 * (Real.pi : ℂ))) *
        (1 - suzukiThetaMero w * (starRingEnd ℂ) (suzukiThetaMero ((x : ℝ) : ℂ)))
        / (((x : ℝ) : ℂ) - w))
      = (-I / (2 * (Real.pi : ℂ))) * (suzukiThetaMero ((x : ℝ) : ℂ) *
        (1 - suzukiThetaMero w * (starRingEnd ℂ) (suzukiThetaMero ((x : ℝ) : ℂ))))
        / (((x : ℝ) : ℂ) - w) by ring]
  rw [key]
  ring

theorem thetaMul_star_suzukiModelKernelLp (hRH : RiemannHypothesis) {w : ℂ} (hw : 0 < w.im) :
    thetaMul (star ((memLp_suzukiModelKernel hRH hw).toLp _))
      = (memLp_suzukiModelKernelStar hRH hw).toLp _ := by
  refine MeasureTheory.Lp.ext ?_
  filter_upwards [thetaMul_coeFn (star ((memLp_suzukiModelKernel hRH hw).toLp
      (fun x : ℝ => suzukiModelKernel w ((x : ℝ) : ℂ)))),
    MeasureTheory.Lp.coeFn_star ((memLp_suzukiModelKernel hRH hw).toLp
      (fun x : ℝ => suzukiModelKernel w ((x : ℝ) : ℂ))),
    (memLp_suzukiModelKernel hRH hw).coeFn_toLp,
    (memLp_suzukiModelKernelStar hRH hw).coeFn_toLp,
    suzukiThetaMero_ae_eq_symbol] with x k1 k2 k3 k4 k5
  have hunit : suzukiThetaMero ((x : ℝ) : ℂ) * (starRingEnd ℂ) (suzukiThetaMero ((x : ℝ) : ℂ))
      = 1 := by
    rw [k5, Complex.mul_conj]
    have h := norm_suzukiThetaSymbol x
    rw [Complex.normSq_eq_norm_sq, h]
    norm_num
  rw [k1, k2, Pi.star_apply, k3, k4, ← k5]
  exact suzukiThetaMero_mul_conj_suzukiModelKernel hw hunit

/-- **The kernel lies in the model space.** -/
theorem suzukiModelKernel_mem_suzukiModelSpace (hRH : RiemannHypothesis) {w : ℂ}
    (hw : 0 < w.im) :
    (memLp_suzukiModelKernel hRH hw).toLp _ ∈ suzukiModelSpace := by
  rw [mem_suzukiModelSpace_iff_conj]
  refine ⟨suzukiModelKernel_mem_hardyL2 hRH hw, ?_⟩
  rw [thetaMul_star_suzukiModelKernelLp hRH hw]
  exact suzukiModelKernelStar_mem_hardyL2 hRH hw


/-! ## The reproducing property -/

theorem memLp_conj_suzukiModelKernel {f : ℝ → ℂ} (h : MemLp f 2 (volume : Measure ℝ)) :
    MemLp (fun x : ℝ => (starRingEnd ℂ) (f x)) 2 (volume : Measure ℝ) := by
  refine ⟨(Complex.continuous_conj.comp_aestronglyMeasurable h.1), ?_⟩
  have hnorm : ∀ x : ℝ, ‖(starRingEnd ℂ) (f x)‖ = ‖f x‖ := fun x => RCLike.norm_conj _
  have := h.2
  rwa [eLpNorm_congr_norm_ae (Filter.Eventually.of_forall hnorm)]

theorem integrable_lp_div_sub {w : ℂ} (hw : w.im ≠ 0) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    Integrable (fun x : ℝ => (f : ℝ → ℂ) x / (((x : ℝ) : ℂ) - w)) volume := by
  have h1 : MemLp ((f : ℝ → ℂ)) 2 (volume : Measure ℝ) := MeasureTheory.Lp.memLp f
  have h2 := memLp_cauchyKernel hw
  have h := h1.integrable_mul h2
  refine h.congr ?_
  filter_upwards with x
  rw [Pi.mul_apply, div_eq_mul_inv]

theorem integrable_conj_lp_div_sub {w : ℂ} (hw : w.im ≠ 0) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    Integrable
      (fun x : ℝ => (starRingEnd ℂ) ((f : ℝ → ℂ) x) / (((x : ℝ) : ℂ) - w)) volume := by
  have h1 : MemLp (fun x : ℝ => (starRingEnd ℂ) ((f : ℝ → ℂ) x)) 2 (volume : Measure ℝ) :=
    memLp_conj_suzukiModelKernel (MeasureTheory.Lp.memLp f)
  have h2 := memLp_cauchyKernel hw
  have h := h1.integrable_mul h2
  refine h.congr ?_
  filter_upwards with x
  rw [Pi.mul_apply, div_eq_mul_inv]

/-- **The Cauchy transform of the conjugate of a Hardy function vanishes above the axis.** -/
theorem integral_conj_cauchyTransform_eq_zero {G : Lp ℂ 2 (volume : Measure ℝ)}
    (hG : G ∈ hardyL2) {w : ℂ} (hw : 0 < w.im) :
    (∫ x : ℝ, (starRingEnd ℂ) ((G : ℝ → ℂ) x) / (((x : ℝ) : ℂ) - w)) = 0 := by
  have hconj : ((starRingEnd ℂ) w).im < 0 := by simpa using hw
  have hbase := integral_cauchyTransform_eq_zero hG hconj
  have hmap : (starRingEnd ℂ)
      (∫ x : ℝ, (starRingEnd ℂ) ((G : ℝ → ℂ) x) / (((x : ℝ) : ℂ) - w))
      = ∫ x : ℝ, (G : ℝ → ℂ) x / (((x : ℝ) : ℂ) - (starRingEnd ℂ) w) := by
    rw [← integral_conj]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with x
    rw [map_div₀, Complex.conj_conj, map_sub, Complex.conj_ofReal]
  have h0 : (starRingEnd ℂ)
      (∫ x : ℝ, (starRingEnd ℂ) ((G : ℝ → ℂ) x) / (((x : ℝ) : ℂ) - w)) = 0 := by
    rw [hmap, hbase]
  have := congrArg (starRingEnd ℂ) h0
  rwa [Complex.conj_conj, map_zero] at this

/-- **The reproducing identity in integral form.**  Against an element of the model space the
kernel pairing collapses to a single Cauchy transform: the `Θ`-twisted half is the Cauchy transform
of the conjugate of a Hardy function, which vanishes above the axis. -/
theorem inner_suzukiModelKernelLp (hRH : RiemannHypothesis) {w : ℂ} (hw : 0 < w.im)
    {F : Lp ℂ 2 (volume : Measure ℝ)} (hF : F ∈ suzukiModelSpace) :
    (inner ℂ ((memLp_suzukiModelKernel hRH hw).toLp _) F : ℂ)
      = (-I / (2 * (Real.pi : ℂ))) * ∫ x : ℝ, (F : ℝ → ℂ) x / (((x : ℝ) : ℂ) - w) := by
  obtain ⟨hFH, hGH⟩ := (mem_suzukiModelSpace_iff_conj F).mp hF
  set G : Lp ℂ 2 (volume : Measure ℝ) := thetaMul (star F) with hGdef
  have hwne : w.im ≠ 0 := ne_of_gt hw
  have hint1 := integrable_lp_div_sub hwne F
  have hint2 := integrable_conj_lp_div_sub hwne G
  have hae : (fun x : ℝ => (inner ℂ ((((memLp_suzukiModelKernel hRH hw).toLp
        (fun x : ℝ => suzukiModelKernel w ((x : ℝ) : ℂ)) :
          Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x) ((F : ℝ → ℂ) x) : ℂ))
      =ᵐ[volume] fun x : ℝ =>
        (-I / (2 * (Real.pi : ℂ))) * ((F : ℝ → ℂ) x / (((x : ℝ) : ℂ) - w))
        - (-I / (2 * (Real.pi : ℂ))) * suzukiThetaMero w *
          ((starRingEnd ℂ) ((G : ℝ → ℂ) x) / (((x : ℝ) : ℂ) - w)) := by
    filter_upwards [(memLp_suzukiModelKernel hRH hw).coeFn_toLp,
      thetaMul_coeFn (star F), MeasureTheory.Lp.coeFn_star F,
      suzukiThetaMero_ae_eq_symbol] with x k1 k2 k3 k4
    rw [RCLike.inner_apply, k1, conj_suzukiModelKernel_ofReal]
    have hGx : (starRingEnd ℂ) ((G : ℝ → ℂ) x)
        = (starRingEnd ℂ) (suzukiThetaMero ((x : ℝ) : ℂ)) * (F : ℝ → ℂ) x := by
      rw [hGdef, k2, k3, Pi.star_apply, k4, map_mul]
      congr 1
      rw [starRingEnd_apply, star_star]
    rw [hGx]
    ring
  rw [MeasureTheory.L2.inner_def, MeasureTheory.integral_congr_ae hae]
  rw [MeasureTheory.integral_sub (hint1.const_mul _)
    (hint2.const_mul ((-I / (2 * (Real.pi : ℂ))) * suzukiThetaMero w))]
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    integral_conj_cauchyTransform_eq_zero hGH hw]
  ring


/-- **The reproducing property.**  An element of the model space with a holomorphic decaying
representative is reproduced by the kernel. -/
theorem inner_suzukiModelKernelLp_of_decay (hRH : RiemannHypothesis) {w : ℂ} (hw : 0 < w.im)
    {F : Lp ℂ 2 (volume : Measure ℝ)} (hF : F ∈ suzukiModelSpace)
    {u : ℂ → ℂ} {M R : ℝ}
    (hdiff : ∀ z : ℂ, 0 ≤ z.im → DifferentiableAt ℂ u z) (hR : 0 < R)
    (hfar : ∀ z : ℂ, 0 ≤ z.im → R ≤ ‖z‖ → ‖u z‖ ≤ M / ‖z‖)
    (hcoe : (F : ℝ → ℂ) =ᵐ[volume] fun x : ℝ => u ((x : ℝ) : ℂ)) :
    (inner ℂ ((memLp_suzukiModelKernel hRH hw).toLp _) F : ℂ) = u w := by
  have hpi := Real.pi_pos
  have hpine : (2 * (Real.pi : ℂ)) ≠ 0 := by
    simp [Complex.ext_iff, Real.pi_ne_zero]
  rw [inner_suzukiModelKernelLp hRH hw hF]
  have hrw : (∫ x : ℝ, (F : ℝ → ℂ) x / (((x : ℝ) : ℂ) - w))
      = ∫ x : ℝ, u ((x : ℝ) : ℂ) / (((x : ℝ) : ℂ) - w) := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hcoe] with x h1
    rw [h1]
  rw [hrw, integral_div_sub_eq_of_upperHalfPlane_farDecay hdiff hR hfar hw]
  field_simp
  linear_combination (-(u w)) * Complex.I_sq

/-- **The kernel norm is its own diagonal value.** -/
theorem inner_suzukiModelKernel_pair (hRH : RiemannHypothesis) {w v : ℂ} (hw : 0 < w.im)
    (hv : 0 < v.im) :
    (inner ℂ ((memLp_suzukiModelKernel hRH hw).toLp _)
      ((memLp_suzukiModelKernel hRH hv).toLp _) : ℂ) = suzukiModelKernel v w := by
  have hvnn : (0 : ℝ) ≤ ‖v‖ := norm_nonneg v
  have hB := suzukiModelKernelBound_nonneg v
  refine inner_suzukiModelKernelLp_of_decay hRH hw
    (suzukiModelKernel_mem_suzukiModelSpace hRH hv)
    (u := suzukiModelKernel v) (M := 2 * suzukiModelKernelBound v) (R := 2 * ‖v‖ + 1)
    (fun z hz => differentiableAt_suzukiModelKernel hRH hv hz) (by linarith) ?_
    (memLp_suzukiModelKernel hRH hv).coeFn_toLp
  intro z hz hzR
  have hzn : 0 < ‖z‖ := by linarith
  have hhalf : ‖v‖ ≤ ‖z‖ / 2 := by linarith
  have hvn : ‖(starRingEnd ℂ) v‖ = ‖v‖ := by simp
  have hzv : ‖z‖ / 2 ≤ ‖z - (starRingEnd ℂ) v‖ := by
    have h := norm_sub_norm_le z ((starRingEnd ℂ) v)
    rw [hvn] at h
    linarith
  have hzh : 0 < ‖z‖ / 2 := by linarith
  calc ‖suzukiModelKernel v z‖
      ≤ suzukiModelKernelBound v / ‖z - (starRingEnd ℂ) v‖ :=
        norm_suzukiModelKernel_le hRH hv hz
    _ ≤ suzukiModelKernelBound v / (‖z‖ / 2) := by gcongr
    _ = 2 * suzukiModelKernelBound v / ‖z‖ := by field_simp

/-! ## Totality of the kernels -/

theorem eq_zero_of_inner_suzukiModelKernel_eq_zero (hRH : RiemannHypothesis)
    {F : Lp ℂ 2 (volume : Measure ℝ)} (hF : F ∈ suzukiModelSpace)
    (h : ∀ (w : ℂ) (hw : 0 < w.im),
      (inner ℂ ((memLp_suzukiModelKernel hRH hw).toLp _) F : ℂ) = 0) :
    F = 0 := by
  have hpi := Real.pi_pos
  obtain ⟨hFH, -⟩ := (mem_suzukiModelSpace_iff_conj F).mp hF
  have hcne : (-I / (2 * (Real.pi : ℂ))) ≠ 0 := by
    refine div_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) ?_
    simp [Complex.ext_iff, Real.pi_ne_zero]
  have hupper : ∀ w : ℂ, 0 < w.im → (∫ x : ℝ, (F : ℝ → ℂ) x / (((x : ℝ) : ℂ) - w)) = 0 := by
    intro w hw
    have hval := (inner_suzukiModelKernelLp hRH hw hF).symm.trans (h w hw)
    exact (mul_eq_zero.mp hval).resolve_left hcne
  have hstar : star F ∈ hardyL2 := by
    refine mem_hardyL2_of_cauchyTransform_eq_zero ?_
    intro v hv
    have hvc : 0 < ((starRingEnd ℂ) v).im := by simpa using hv
    have hmap : (starRingEnd ℂ) (∫ x : ℝ, ((star F : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x
          / (((x : ℝ) : ℂ) - v))
        = ∫ x : ℝ, (F : ℝ → ℂ) x / (((x : ℝ) : ℂ) - (starRingEnd ℂ) v) := by
      rw [← integral_conj]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [MeasureTheory.Lp.coeFn_star F] with x k1
      rw [k1, Pi.star_apply, map_div₀, map_sub, Complex.conj_ofReal, starRingEnd_apply,
        star_star]
    have h0 := hupper _ hvc
    rw [← hmap] at h0
    have := congrArg (starRingEnd ℂ) h0
    rwa [Complex.conj_conj, map_zero] at this
  have hFperp : F ∈ hardyL2ᗮ := by
    rw [← map_star_hardyL2]
    refine ⟨star F, hstar, ?_⟩
    rw [lpStarₛₗ_apply, star_star]
  have hzero : (inner ℂ F F : ℂ) = 0 :=
    Submodule.mem_orthogonal _ _ |>.mp hFperp F hFH
  exact inner_self_eq_zero.mp hzero


end RHTower
