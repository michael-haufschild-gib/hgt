import GaloisForLFunctions.HTGeometry.PrincipalSquareRoot
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Holomorphy of the principal square root on the right half plane

On `{Re z > 0}` the principal square root is a local left inverse of `w ↦ w²` whose value never
vanishes, so the inverse-function theorem gives it a complex derivative `1/(2√z)` there.  This is
the analytic input needed to continue identities in a spectral parameter through the principal
root of a moving argument.
-/

open Complex Filter Topology

namespace HTGeometry

/-- Cartesian form of the principal square root. -/
theorem csqrt_eq (z : ℂ) : csqrt z = (csqrtRe z : ℂ) + (csqrtIm z : ℂ) * I := by
  apply Complex.ext <;> simp [csqrt_re, csqrt_im]

theorem continuousAt_csqrtRe {z : ℂ} (hz : 0 < z.re) : ContinuousAt csqrtRe z := by
  have hpos : 0 < (‖z‖ + z.re) / 2 := by
    have := Complex.abs_re_le_norm z
    have habs : |z.re| ≤ ‖z‖ := this
    have : z.re ≤ ‖z‖ := le_trans (le_abs_self _) habs
    linarith
  unfold csqrtRe
  fun_prop

theorem continuousAt_csqrt {z : ℂ} (hz : 0 < z.re) : ContinuousAt csqrt z := by
  have hre : ContinuousAt csqrtRe z := continuousAt_csqrtRe hz
  have hne : csqrtRe z ≠ 0 := ne_of_gt (csqrtRe_pos hz)
  have him : ContinuousAt csqrtIm z := by
    unfold csqrtIm
    exact ContinuousAt.div (Complex.continuous_im.continuousAt) (by fun_prop)
      (by simpa using hne)
  have : ContinuousAt (fun w : ℂ => (csqrtRe w : ℂ) + (csqrtIm w : ℂ) * I) z := by
    exact (Complex.continuous_ofReal.continuousAt.comp hre).add
      (((Complex.continuous_ofReal.continuousAt.comp him)).mul continuousAt_const)
  exact this.congr (Filter.Eventually.of_forall fun w => (csqrt_eq w).symm)

theorem csqrt_ne_zero {z : ℂ} (hz : 0 < z.re) : csqrt z ≠ 0 := by
  intro h
  have hre : (csqrt z).re = 0 := by rw [h]; simp
  rw [csqrt_re] at hre
  exact absurd hre (ne_of_gt (csqrtRe_pos hz))

/-- **The principal square root is complex differentiable on the right half plane.** -/
theorem hasStrictDerivAt_csqrt {z : ℂ} (hz : 0 < z.re) :
    HasStrictDerivAt csqrt (2 * csqrt z)⁻¹ z := by
  have hcont : ContinuousAt csqrt z := continuousAt_csqrt hz
  have hsq : HasStrictDerivAt (fun w : ℂ => w ^ 2) (2 * csqrt z) (csqrt z) := by
    have := hasStrictDerivAt_pow 2 (csqrt z)
    simpa using this
  have hne : (2 : ℂ) * csqrt z ≠ 0 := by
    refine mul_ne_zero two_ne_zero (csqrt_ne_zero hz)
  have hloc : ∀ᶠ y : ℂ in nhds z, (fun w : ℂ => w ^ 2) (csqrt y) = y := by
    have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds hz] with y hy
    exact csqrt_sq hy
  exact hsq.of_local_left_inverse hcont hne hloc

theorem differentiableAt_csqrt {z : ℂ} (hz : 0 < z.re) : DifferentiableAt ℂ csqrt z :=
  (hasStrictDerivAt_csqrt hz).hasDerivAt.differentiableAt

private theorem isOpen_rightHalfPlane : IsOpen {w : ℂ | 0 < w.re} :=
  isOpen_lt continuous_const Complex.continuous_re

theorem differentiableOn_csqrt : DifferentiableOn ℂ csqrt {w : ℂ | 0 < w.re} := by
  intro w hw
  exact (differentiableAt_csqrt hw).differentiableWithinAt

/-! ## The complementary nonreal locus -/

/-- Away from the real axis, the principal-root radicand is strictly positive. -/
theorem norm_add_re_pos_of_im_ne_zero {w : ℂ} (hw : w.im ≠ 0) : 0 < ‖w‖ + w.re := by
  have hsq : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hnn : 0 ≤ ‖w‖ := norm_nonneg w
  have him : 0 < w.im ^ 2 := by positivity
  nlinarith [hsq, hnn, him, sq_nonneg (‖w‖ + w.re), sq_nonneg (‖w‖ - w.re)]

theorem csqrtRe_pos_of_im_ne_zero {w : ℂ} (hw : w.im ≠ 0) : 0 < csqrtRe w := by
  rw [csqrtRe]
  exact Real.sqrt_pos.mpr (by linarith [norm_add_re_pos_of_im_ne_zero hw])

theorem csqrt_re_pos_of_im_ne_zero {w : ℂ} (hw : w.im ≠ 0) : 0 < (csqrt w).re := by
  rw [csqrt_re]
  exact csqrtRe_pos_of_im_ne_zero hw

/-- Off the real axis, the chosen square root squares back to its argument. -/
theorem csqrt_sq_of_im_ne_zero {w : ℂ} (hw : w.im ≠ 0) : csqrt w ^ 2 = w := by
  have hp : 0 < csqrtRe w := csqrtRe_pos_of_im_ne_zero hw
  have hrad : 0 < ‖w‖ + w.re := norm_add_re_pos_of_im_ne_zero hw
  have hpsq : csqrtRe w ^ 2 = (‖w‖ + w.re) / 2 := by
    rw [csqrtRe, Real.sq_sqrt (by linarith)]
  have hnormsq : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hqsq : csqrtIm w ^ 2 = (‖w‖ - w.re) / 2 := by
    rw [csqrtIm, div_pow, mul_pow, hpsq]
    rw [div_eq_iff (by nlinarith [hrad] : ((2:ℝ) ^ 2 * ((‖w‖ + w.re) / 2)) ≠ 0)]
    nlinarith [hnormsq, hrad]
  have hprod : 2 * (csqrtRe w * csqrtIm w) = w.im := by
    rw [csqrtIm]
    field_simp
  apply Complex.ext
  · rw [pow_two, Complex.mul_re, csqrt_re, csqrt_im]
    nlinarith [hpsq, hqsq]
  · rw [pow_two, Complex.mul_im, csqrt_re, csqrt_im]
    nlinarith [hprod]

theorem continuousAt_csqrtRe_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) :
    ContinuousAt csqrtRe z := by
  have hpos : 0 < (‖z‖ + z.re) / 2 := by
    linarith [norm_add_re_pos_of_im_ne_zero hz]
  unfold csqrtRe
  fun_prop

theorem continuousAt_csqrt_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) : ContinuousAt csqrt z := by
  have hre : ContinuousAt csqrtRe z := continuousAt_csqrtRe_of_im_ne_zero hz
  have hne : csqrtRe z ≠ 0 := ne_of_gt (csqrtRe_pos_of_im_ne_zero hz)
  have him : ContinuousAt csqrtIm z := by
    unfold csqrtIm
    exact ContinuousAt.div (Complex.continuous_im.continuousAt) (by fun_prop)
      (by simpa using hne)
  have hsum : ContinuousAt (fun w : ℂ => (csqrtRe w : ℂ) + (csqrtIm w : ℂ) * I) z := by
    exact (Complex.continuous_ofReal.continuousAt.comp hre).add
      ((Complex.continuous_ofReal.continuousAt.comp him).mul continuousAt_const)
  exact hsum.congr (Filter.Eventually.of_forall fun w => (csqrt_eq w).symm)

theorem csqrt_ne_zero_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) : csqrt z ≠ 0 := by
  intro h
  have hre : (csqrt z).re = 0 := by rw [h]; simp
  rw [csqrt_re] at hre
  exact absurd hre (ne_of_gt (csqrtRe_pos_of_im_ne_zero hz))

/-- **The principal square root is complex differentiable off the real axis.** -/
theorem hasStrictDerivAt_csqrt_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) :
    HasStrictDerivAt csqrt (2 * csqrt z)⁻¹ z := by
  have hcont : ContinuousAt csqrt z := continuousAt_csqrt_of_im_ne_zero hz
  have hsq : HasStrictDerivAt (fun w : ℂ => w ^ 2) (2 * csqrt z) (csqrt z) := by
    have := hasStrictDerivAt_pow 2 (csqrt z)
    simpa using this
  have hne : (2 : ℂ) * csqrt z ≠ 0 := by
    exact mul_ne_zero two_ne_zero (csqrt_ne_zero_of_im_ne_zero hz)
  have hopen : IsOpen {w : ℂ | w.im ≠ 0} := by
    change IsOpen (Complex.im ⁻¹' {r : ℝ | r ≠ 0})
    exact isOpen_ne.preimage Complex.continuous_im
  have hloc : ∀ᶠ y : ℂ in nhds z, (fun w : ℂ => w ^ 2) (csqrt y) = y := by
    filter_upwards [hopen.mem_nhds hz] with y hy
    exact csqrt_sq_of_im_ne_zero hy
  exact hsq.of_local_left_inverse hcont hne hloc

theorem differentiableAt_csqrt_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) :
    DifferentiableAt ℂ csqrt z :=
  (hasStrictDerivAt_csqrt_of_im_ne_zero hz).hasDerivAt.differentiableAt


/-- On the positive reals the principal square root is the real one. -/
theorem csqrt_ofReal_of_pos {r : ℝ} (hr : 0 < r) :
    csqrt ((r : ℝ) : ℂ) = ((Real.sqrt r : ℝ) : ℂ) := by
  have hnorm : ‖((r : ℝ) : ℂ)‖ = r := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have hre : csqrtRe ((r : ℝ) : ℂ) = Real.sqrt r := by
    rw [csqrtRe, hnorm]
    simp only [Complex.ofReal_re]
    congr 1
    ring
  have him : csqrtIm ((r : ℝ) : ℂ) = 0 := by
    rw [csqrtIm]
    simp
  apply Complex.ext
  · rw [csqrt_re, hre]
    simp
  · rw [csqrt_im, him]
    simp


/-! ## Agreement with the principal complex power -/

theorem cpow_half_re_pos {z : ℂ} (hz : 0 < z.re) : 0 < (z ^ (1 / 2 : ℂ)).re := by
  have hzne : z ≠ 0 := by
    intro h
    rw [h] at hz
    simp at hz
  have harg : |z.arg| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hz)
  rw [Complex.cpow_def_of_ne_zero hzne, Complex.exp_re]
  have him : (Complex.log z * (1 / 2 : ℂ)).im = z.arg / 2 := by
    simp [Complex.mul_im, Complex.log_im]
    ring
  rw [him]
  have hcos : 0 < Real.cos (z.arg / 2) := by
    refine Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩
    · have := (abs_lt.1 harg).1
      linarith [Real.pi_pos]
    · have := (abs_lt.1 harg).2
      linarith [Real.pi_pos]
  positivity

theorem cpow_half_sq {z : ℂ} : (z ^ (1 / 2 : ℂ)) ^ 2 = z := by
  by_cases hz : z = 0
  · rw [hz]
    norm_num
  · have him : (Complex.log z * (1 / 2 : ℂ)).im = z.arg / 2 := by
      simp [Complex.mul_im, Complex.log_im]
      ring
    have h1 : -Real.pi < (Complex.log z * (1 / 2 : ℂ)).im := by
      rw [him]
      have := Complex.neg_pi_lt_arg z
      linarith [Real.pi_pos]
    have h2 : (Complex.log z * (1 / 2 : ℂ)).im ≤ Real.pi := by
      rw [him]
      have := Complex.arg_le_pi z
      linarith [Real.pi_pos]
    have hmul := Complex.cpow_mul (x := z) (y := (1 / 2 : ℂ)) (2 : ℂ) h1 h2
    rw [show (1 / 2 : ℂ) * 2 = 1 from by ring, Complex.cpow_one] at hmul
    have hcast : (z ^ (1 / 2 : ℂ)) ^ (2 : ℂ) = (z ^ (1 / 2 : ℂ)) ^ (2 : ℕ) := by
      rw [show ((2 : ℂ)) = ((2 : ℕ) : ℂ) from by norm_num, Complex.cpow_natCast]
    rw [← hcast]
    exact hmul.symm

/-- **The principal square root is the principal one-half power.** -/
theorem csqrt_eq_cpow_half {z : ℂ} (hz : 0 < z.re) : csqrt z = z ^ (1 / 2 : ℂ) := by
  have hsq : csqrt z ^ 2 = (z ^ (1 / 2 : ℂ)) ^ 2 := by
    rw [csqrt_sq hz, cpow_half_sq]
  have hfac : (csqrt z - z ^ (1 / 2 : ℂ)) * (csqrt z + z ^ (1 / 2 : ℂ)) = 0 := by
    linear_combination hsq
  rcases mul_eq_zero.1 hfac with h | h
  · exact sub_eq_zero.1 h
  · exfalso
    have hre : (csqrt z).re + (z ^ (1 / 2 : ℂ)).re = 0 := by
      have := congrArg Complex.re h
      simpa [Complex.add_re] using this
    have h1 : 0 < (csqrt z).re := by rw [csqrt_re]; exact csqrtRe_pos hz
    have h2 : 0 < (z ^ (1 / 2 : ℂ)).re := cpow_half_re_pos hz
    linarith


/-! ## Multiplicative rules on the right half plane -/

/-- A square root with positive real part is the principal one. -/
theorem csqrt_eq_of_sq_of_re_pos {w v : ℂ} (hw : 0 < w.re) (hv : 0 < v.re) (hsq : v ^ 2 = w) :
    csqrt w = v := by
  have hcs : csqrt w ^ 2 = w := csqrt_sq hw
  have hfac : (csqrt w - v) * (csqrt w + v) = 0 := by
    linear_combination hcs - hsq
  rcases mul_eq_zero.1 hfac with h | h
  · exact sub_eq_zero.1 h
  · exfalso
    have hre : (csqrt w).re + v.re = 0 := by
      have := congrArg Complex.re h
      simpa [Complex.add_re] using this
    have h1 : 0 < (csqrt w).re := by rw [csqrt_re]; exact csqrtRe_pos hw
    linarith

theorem re_ofReal_mul_pos {r : ℝ} (hr : 0 < r) {w : ℂ} (hw : 0 < w.re) :
    0 < ((r : ℂ) * w).re := by
  rw [Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_pos hr hw

theorem re_inv_pos {w : ℂ} (hw : 0 < w.re) : 0 < (w⁻¹).re := by
  have hne : w ≠ 0 := by
    intro h
    rw [h] at hw
    simp at hw
  have hns : 0 < Complex.normSq w := by simpa using Complex.normSq_pos.2 hne
  rw [Complex.inv_re]
  positivity

/-- Real positive scalars factor out of the principal square root. -/
theorem csqrt_ofReal_mul {r : ℝ} (hr : 0 < r) {w : ℂ} (hw : 0 < w.re) :
    csqrt ((r : ℂ) * w) = ((Real.sqrt r : ℝ) : ℂ) * csqrt w := by
  refine csqrt_eq_of_sq_of_re_pos (re_ofReal_mul_pos hr hw) ?_ ?_
  · rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, csqrt_re]
    exact mul_pos (Real.sqrt_pos.2 hr) (csqrtRe_pos hw)
  · rw [mul_pow, csqrt_sq hw, ← Complex.ofReal_pow, Real.sq_sqrt hr.le]

/-- The principal square root commutes with inversion. -/
theorem csqrt_inv {w : ℂ} (hw : 0 < w.re) : csqrt w⁻¹ = (csqrt w)⁻¹ := by
  have hcsne : csqrt w ≠ 0 := csqrt_ne_zero hw
  refine csqrt_eq_of_sq_of_re_pos (re_inv_pos hw) ?_ ?_
  · exact re_inv_pos (by rw [csqrt_re]; exact csqrtRe_pos hw)
  · rw [inv_pow, csqrt_sq hw]


/-! ## Perturbation near one -/

/-- The principal square root is `1`-Lipschitz at `1` on the right half plane. -/
theorem norm_csqrt_sub_one_le {w : ℂ} (hw : 0 < w.re) : ‖csqrt w - 1‖ ≤ ‖w - 1‖ := by
  have hcs : csqrt w ^ 2 = w := csqrt_sq hw
  have hre : 0 < (csqrt w).re := by rw [csqrt_re]; exact csqrtRe_pos hw
  have hsum : (1 : ℝ) ≤ ‖csqrt w + 1‖ := by
    refine le_trans ?_ (Complex.re_le_norm (csqrt w + 1))
    simp only [Complex.add_re, Complex.one_re]
    linarith
  have hne : csqrt w + 1 ≠ 0 := by
    intro h
    rw [h] at hsum
    simp at hsum
    linarith
  have hfac : (csqrt w - 1) * (csqrt w + 1) = w - 1 := by
    linear_combination hcs
  have hval : csqrt w - 1 = (w - 1) / (csqrt w + 1) := by
    field_simp
    linear_combination hfac
  rw [hval, norm_div]
  rw [div_le_iff₀ (lt_of_lt_of_le zero_lt_one hsum)]
  nlinarith [norm_nonneg (w - 1), hsum]

/-- The map `w ↦ w √w` is Lipschitz at `1` on the right half plane. -/
theorem norm_mul_csqrt_sub_one_le {w : ℂ} (hw : 0 < w.re) :
    ‖w * csqrt w - 1‖ ≤ (2 + ‖w - 1‖) * ‖w - 1‖ := by
  have hsplit : w * csqrt w - 1 = w * (csqrt w - 1) + (w - 1) := by ring
  have hcs := norm_csqrt_sub_one_le hw
  have hw1 : ‖w‖ ≤ 1 + ‖w - 1‖ := by
    have : ‖w‖ = ‖(w - 1) + 1‖ := by ring_nf
    rw [this]
    exact le_trans (norm_add_le _ _) (by simp [add_comm])
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_mul]
  have hnn : (0 : ℝ) ≤ ‖w - 1‖ := norm_nonneg _
  have hprod : ‖w‖ * ‖csqrt w - 1‖ ≤ (1 + ‖w - 1‖) * ‖w - 1‖ :=
    mul_le_mul hw1 hcs (norm_nonneg _) (by positivity)
  nlinarith [hprod]


/-- The principal square root halves the modulus. -/
theorem norm_csqrt {w : ℂ} (hw : 0 < w.re) : ‖csqrt w‖ = Real.sqrt ‖w‖ := by
  have hsq : csqrt w ^ 2 = w := csqrt_sq hw
  have hnorm : ‖csqrt w‖ ^ 2 = ‖w‖ := by
    rw [← norm_pow, hsq]
  rw [← hnorm, Real.sqrt_sq (norm_nonneg _)]

/-- Multiplicative perturbation: a product of two near-units is a near-unit. -/
theorem norm_mul_sub_one_le {A B : ℂ} {α β : ℝ} (hA : ‖A - 1‖ ≤ α) (hB : ‖B - 1‖ ≤ β)
    (hα : 0 ≤ α) : ‖A * B - 1‖ ≤ α + β + α * β := by
  have hsplit : A * B - 1 = (A - 1) * (B - 1) + ((A - 1) + (B - 1)) := by ring
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  refine le_trans (add_le_add le_rfl (norm_add_le _ _)) ?_
  rw [norm_mul]
  have hprod : ‖A - 1‖ * ‖B - 1‖ ≤ α * β :=
    mul_le_mul hA hB (norm_nonneg _) hα
  linarith

/-- Inversion of a near-unit. -/
theorem norm_inv_sub_one_le {W : ℂ} {γ : ℝ} (hW : ‖W - 1‖ ≤ γ) (hγ : γ ≤ 1 / 2) :
    ‖W⁻¹ - 1‖ ≤ 2 * γ := by
  have hγ0 : 0 ≤ γ := le_trans (norm_nonneg _) hW
  have hone : (1 : ℝ) ≤ ‖W‖ + ‖W - 1‖ := by
    have h := norm_sub_le W (W - 1)
    simpa using h
  have hWpos : (1 : ℝ) / 2 ≤ ‖W‖ := by linarith
  have hWne : W ≠ 0 := by
    intro h
    rw [h] at hWpos
    simp at hWpos
    linarith
  have hval : W⁻¹ - 1 = (1 - W) / W := by
    field_simp
  rw [hval, norm_div]
  have hnum : ‖1 - W‖ = ‖W - 1‖ := by
    rw [← norm_neg]
    ring_nf
  rw [hnum, div_le_iff₀ (by linarith : (0:ℝ) < ‖W‖)]
  nlinarith [hW, hWpos, hγ0]


/-- A triple product of near-units. -/
theorem norm_mul3_sub_one_le {A B C : ℂ} {α β γ : ℝ} (hA : ‖A - 1‖ ≤ α) (hB : ‖B - 1‖ ≤ β)
    (hC : ‖C - 1‖ ≤ γ) (hβ : β ≤ 1) (hγ : γ ≤ 1) :
    ‖A * B * C - 1‖ ≤ 4 * α + 2 * β + γ := by
  have hBn : ‖B‖ ≤ 2 := by
    have h := norm_sub_le B 1
    have : ‖B‖ ≤ ‖B - 1‖ + ‖(1 : ℂ)‖ := by
      have := norm_add_le (B - 1) (1 : ℂ)
      simpa using this
    simp only [norm_one] at this
    linarith [hB, hβ]
  have hCn : ‖C‖ ≤ 2 := by
    have : ‖C‖ ≤ ‖C - 1‖ + ‖(1 : ℂ)‖ := by
      have := norm_add_le (C - 1) (1 : ℂ)
      simpa using this
    simp only [norm_one] at this
    linarith [hC, hγ]
  have hsplit : A * B * C - 1 = (A - 1) * B * C + ((B - 1) * C + (C - 1)) := by ring
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  refine le_trans (add_le_add le_rfl (norm_add_le _ _)) ?_
  rw [norm_mul, norm_mul, norm_mul]
  have hα0 : 0 ≤ ‖A - 1‖ := norm_nonneg _
  have hβ0 : 0 ≤ ‖B - 1‖ := norm_nonneg _
  have hBn0 : 0 ≤ ‖B‖ := norm_nonneg _
  have hCn0 : 0 ≤ ‖C‖ := norm_nonneg _
  have hα1 : 0 ≤ α := le_trans hα0 hA
  have hβ1 : 0 ≤ β := le_trans hβ0 hB
  have hab : ‖A - 1‖ * ‖B‖ ≤ α * 2 := mul_le_mul hA hBn hBn0 hα1
  have h1 : ‖A - 1‖ * ‖B‖ * ‖C‖ ≤ 4 * α := by
    have := mul_le_mul hab hCn hCn0 (by linarith)
    linarith [this]
  have h2 : ‖B - 1‖ * ‖C‖ ≤ 2 * β := by
    have := mul_le_mul hB hCn hCn0 hβ1
    linarith [this]
  linarith [h1, h2, hC]

end HTGeometry
