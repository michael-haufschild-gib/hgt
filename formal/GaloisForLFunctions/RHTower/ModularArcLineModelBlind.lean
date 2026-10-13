import GaloisForLFunctions.RHTower.ModularArcLogEdgeWitness
import GaloisForLFunctions.RHTower.PoissonVectorFourierWhittaker

/-!
# The line-model vector of the modular arc witness is blind at every nonzero integer

For a finite measure `ν` on the bottom arc `{z = u + iy : u² + y² = 1, |u| ≤ ½}` put

`h_ν(x) = ∫ (y / ((x − u)² + y²))^{1/2} dν`  (`arcLineVector`),

the superposition of the `s = ½` Poisson vectors of the arc points, and

`h_ν'(x) = −∫ √y (x − u) ((x − u)² + y²)^{−3/2} dν`  (`arcLineDeriv`, its derivative,
`hasDerivAt_arcLineVector`).

* **Inversion** (`arcLineVector_inv`).  `h_ν(1/x) = |x| h_ν(x)` for `x ≠ 0`, for every `ν`.  For a point
  of the unit circle, `(1/x − u)² + y² = ((x − u)² + y²)/x²`.
* **Fourier coefficients** (`integral_arcLineDeriv_mul_sin`, `integral_arcLineDeriv_mul_cos`).  For
  `c = 2π(n + 1)`:
  `∫ h_ν'(x) sin(cx) dx = −2c ∫ √y K₀(cy) cos(cu) dν` and
  `∫ h_ν'(x) cos(cx) dx = 2c ∫ √y K₀(cy) sin(cu) dν`.
  Proof: shift `x = u + w`, the parity of `w (w² + y²)^{−3/2}`, and
  `∫ w (w² + y²)^{−3/2} sin(cw) dw = 2c K₀(cy)` (`integral_mul_rpow_sin_eq_kMoment`).
* **Theorem** (`exists_arcLineWitness`).  For the arc witness of `exists_arcWitness`, the integrable
  function `h_ν'` has vanishing Fourier coefficients at every nonzero integer frequency.  `h_ν` is
  even, satisfies `h_ν(1/x) = |x| h_ν(x)`, and its log-scale profile `e^{v/2} h_ν(e^v)` is strictly
  positive definite.  This is the line-model form of a positive (N1) witness at the logarithmic edge:
  the periodization of `h_ν` (equivalently, of `h_ν'`) carries no nonconstant Fourier mode.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-- The arc height squared plus the horizontal offset: on the unit circle this is
`x² − 2ux + 1`. -/
theorem sub_sq_add_modularArcHeight_sq (u : ArcParam) (x : ℝ) :
    (x - u) ^ 2 + modularArcHeight u ^ 2 = x ^ 2 - 2 * u * x + 1 := by
  have := modularArcHeight_sq u.2
  nlinarith

theorem sub_sq_add_modularArcHeight_sq_pos (u : ArcParam) (x : ℝ) :
    0 < (x - u) ^ 2 + modularArcHeight u ^ 2 := by
  have := modularArcHeight_pos u.2; positivity

/-- The line-model vector `h_ν(x) = ∫ (y/((x−u)² + y²))^{1/2} dν`. -/
def arcLineVector (ν : Measure ArcParam) (x : ℝ) : ℝ :=
  ∫ u, (modularArcHeight u / ((x - u) ^ 2 + modularArcHeight u ^ 2)) ^ (1 / 2 : ℝ) ∂ν

/-- Its derivative `h_ν'(x) = −∫ √y (x−u) ((x−u)² + y²)^{−3/2} dν`. -/
def arcLineDeriv (ν : Measure ArcParam) (x : ℝ) : ℝ :=
  -∫ u, Real.sqrt (modularArcHeight u) * ((x - u) *
    ((x - u) ^ 2 + modularArcHeight u ^ 2) ^ (-(3 / 2) : ℝ)) ∂ν

/-- **Inversion.**  `h_ν(1/x) = |x| h_ν(x)`. -/
theorem arcLineVector_inv (ν : Measure ArcParam) {x : ℝ} (hx : x ≠ 0) :
    arcLineVector ν (1 / x) = |x| * arcLineVector ν x := by
  unfold arcLineVector
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  have hy := modularArcHeight_pos u.2
  have hA := sub_sq_add_modularArcHeight_sq_pos u x
  have e : (1 / x - u) ^ 2 + modularArcHeight u ^ 2 =
      ((x - u) ^ 2 + modularArcHeight u ^ 2) / x ^ 2 := by
    rw [sub_sq_add_modularArcHeight_sq, sub_sq_add_modularArcHeight_sq]
    field_simp
    ring
  simp only
  rw [e, div_div_eq_mul_div, mul_div_right_comm, Real.mul_rpow (by positivity) (by positivity)]
  have hx2 : (x ^ 2) ^ (1 / 2 : ℝ) = |x| := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs]
  rw [hx2, mul_comm]

/-- The pointwise bound `|√y (x−u)((x−u)²+y²)^{−3/2}| ≤ 32 (1 + x²)⁻¹`. -/
theorem abs_arcLineDeriv_kernel_le (u : ArcParam) (x : ℝ) :
    |Real.sqrt (modularArcHeight u) * ((x - u) *
      ((x - u) ^ 2 + modularArcHeight u ^ 2) ^ (-(3 / 2) : ℝ))| ≤ 32 * (1 + x ^ 2)⁻¹ := by
  have hy := modularArcHeight_pos u.2
  have hA := sub_sq_add_modularArcHeight_sq_pos u x
  have hy1 : modularArcHeight u ≤ 1 := by
    unfold modularArcHeight; rw [Real.sqrt_le_one]; nlinarith [sq_nonneg (u : ℝ)]
  have hsq : Real.sqrt (modularArcHeight u) ≤ 1 := Real.sqrt_le_one.mpr hy1
  have hk := abs_mul_rpow_le_inv (x := x - u) hy
  have hy34 : (3 / 4 : ℝ) ≤ modularArcHeight u ^ 2 := by
    have := modularArcHeight_sq u.2; nlinarith [u.2.1, u.2.2]
  have hmax : max 1 (1 / modularArcHeight u ^ 2) ≤ 2 := by
    refine max_le (by norm_num) ?_
    rw [div_le_iff₀ (by positivity)]; linarith
  have hshift : (1 + (x - u) ^ 2)⁻¹ ≤ 16 * (1 + x ^ 2)⁻¹ := by
    rw [inv_le_comm₀ (by positivity) (by positivity), mul_inv, inv_inv]
    have hu : |(u : ℝ)| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [u.2.1], u.2.2⟩
    have : (u : ℝ) ^ 2 ≤ 1 / 4 := by nlinarith [abs_nonneg (u : ℝ), sq_abs (u : ℝ)]
    nlinarith [sq_nonneg (x - 2 * u), sq_nonneg x]
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_mul,
    abs_of_nonneg (Real.rpow_nonneg hA.le _)]
  calc Real.sqrt (modularArcHeight u) * (|x - u| *
        ((x - u) ^ 2 + modularArcHeight u ^ 2) ^ (-(3 / 2) : ℝ))
      ≤ 1 * (max 1 (1 / modularArcHeight u ^ 2) * (1 + (x - u) ^ 2)⁻¹) :=
        mul_le_mul hsq hk (by positivity) zero_le_one
    _ ≤ 1 * (2 * (16 * (1 + x ^ 2)⁻¹)) := by
        gcongr
    _ = 32 * (1 + x ^ 2)⁻¹ := by ring

theorem integrable_mul_rpow_mul_trig {y : ℝ} (hy : 0 < y) {g : ℝ → ℝ} (hg : Continuous g)
    (hg1 : ∀ w, |g w| ≤ 1) :
    Integrable fun w : ℝ => w * (w ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) * g w := by
  refine (integrable_abs_mul_rpow hy).mono' ?_ (Eventually.of_forall fun w => ?_)
  · have : Continuous fun w : ℝ => (w ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) :=
      Continuous.rpow_const (by fun_prop) fun w => Or.inl (by positivity)
    exact ((continuous_id.mul this).mul hg).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    calc |w| * (w ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) * |g w|
        ≤ |w| * (w ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left (hg1 w) (mul_nonneg (abs_nonneg _)
            (Real.rpow_nonneg (by positivity) _))
      _ = |w| * (w ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) := mul_one _

theorem integral_mul_rpow_cos_eq_zero (y c : ℝ) :
    ∫ w : ℝ, w * (w ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) * Real.cos (c * w) = 0 := by
  have h := integral_neg_eq_self
    (fun w : ℝ => w * (w ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) * Real.cos (c * w)) volume
  have e : (fun w : ℝ => -w * ((-w) ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) * Real.cos (c * -w)) =
      fun w => -(w * (w ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) * Real.cos (c * w)) := by
    funext w; rw [neg_sq, mul_neg, Real.cos_neg]; ring
  rw [e, integral_neg] at h
  linarith

/-- `∫ (x−u)((x−u)²+y²)^{−3/2} sin(cx) dx = 2c K₀(cy) cos(cu)`. -/
theorem integral_shift_mul_rpow_sin {y c : ℝ} (hy : 0 < y) (hc : 0 < c) (u : ℝ) :
    ∫ x : ℝ, (x - u) * ((x - u) ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) * Real.sin (c * x) =
      2 * c * kMoment 0 (c * y) * Real.cos (c * u) := by
  have hsh := integral_add_right_eq_self (μ := volume)
    (fun x : ℝ => (x - u) * ((x - u) ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) * Real.sin (c * x)) u
  rw [← hsh]
  have e : ∀ w : ℝ, (w + u - u) * ((w + u - u) ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) *
      Real.sin (c * (w + u)) =
      Real.cos (c * u) * (w * (w ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) * Real.sin (c * w)) +
      Real.sin (c * u) * (w * (w ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) * Real.cos (c * w)) := by
    intro w
    rw [add_sub_cancel_right, mul_add, Real.sin_add]
    ring
  simp_rw [e]
  rw [integral_add ((integrable_mul_rpow_mul_trig hy (by fun_prop)
      fun w => Real.abs_sin_le_one _).const_mul _)
    ((integrable_mul_rpow_mul_trig hy (by fun_prop) fun w => Real.abs_cos_le_one _).const_mul _),
    integral_const_mul, integral_const_mul, integral_mul_rpow_sin_eq_kMoment hy hc,
    integral_mul_rpow_cos_eq_zero]
  ring

/-- `∫ (x−u)((x−u)²+y²)^{−3/2} cos(cx) dx = −2c K₀(cy) sin(cu)`. -/
theorem integral_shift_mul_rpow_cos {y c : ℝ} (hy : 0 < y) (hc : 0 < c) (u : ℝ) :
    ∫ x : ℝ, (x - u) * ((x - u) ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) * Real.cos (c * x) =
      -(2 * c * kMoment 0 (c * y) * Real.sin (c * u)) := by
  have hsh := integral_add_right_eq_self (μ := volume)
    (fun x : ℝ => (x - u) * ((x - u) ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) * Real.cos (c * x)) u
  rw [← hsh]
  have e : ∀ w : ℝ, (w + u - u) * ((w + u - u) ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) *
      Real.cos (c * (w + u)) =
      Real.cos (c * u) * (w * (w ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) * Real.cos (c * w)) -
      Real.sin (c * u) * (w * (w ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) * Real.sin (c * w)) := by
    intro w
    rw [add_sub_cancel_right, mul_add, Real.cos_add]
    ring
  simp_rw [e]
  rw [integral_sub ((integrable_mul_rpow_mul_trig hy (by fun_prop)
      fun w => Real.abs_cos_le_one _).const_mul _)
    ((integrable_mul_rpow_mul_trig hy (by fun_prop) fun w => Real.abs_sin_le_one _).const_mul _),
    integral_const_mul, integral_const_mul, integral_mul_rpow_sin_eq_kMoment hy hc,
    integral_mul_rpow_cos_eq_zero]
  ring

/-- The kernel of `h_ν'`, as a function of `(x, u)`. -/
def arcLineKernel (x : ℝ) (u : ArcParam) : ℝ :=
  Real.sqrt (modularArcHeight u) * ((x - u) *
    ((x - u) ^ 2 + modularArcHeight u ^ 2) ^ (-(3 / 2) : ℝ))

theorem continuous_arcLineKernel : Continuous fun p : ℝ × ArcParam => arcLineKernel p.1 p.2 := by
  unfold arcLineKernel modularArcHeight
  have hpos : ∀ p : ℝ × ArcParam, 0 < (p.1 - p.2) ^ 2 + Real.sqrt (1 - (p.2 : ℝ) ^ 2) ^ 2 :=
    fun p => sub_sq_add_modularArcHeight_sq_pos p.2 p.1
  exact (by fun_prop : Continuous fun p : ℝ × ArcParam => Real.sqrt (Real.sqrt (1 - (p.2 : ℝ) ^ 2)))
    |>.mul ((by fun_prop : Continuous fun p : ℝ × ArcParam => p.1 - (p.2 : ℝ)).mul
      (Continuous.rpow_const (by fun_prop) fun p => Or.inl (hpos p).ne'))

theorem integrable_arcLineKernel_prod (ν : Measure ArcParam) [IsFiniteMeasure ν] {g : ℝ → ℝ}
    (hg : Continuous g) (hg1 : ∀ x, |g x| ≤ 1) :
    Integrable (fun p : ℝ × ArcParam => arcLineKernel p.1 p.2 * g p.1) (volume.prod ν) := by
  have hb : Integrable (fun p : ℝ × ArcParam => 32 * (1 + p.1 ^ 2)⁻¹ * (1 : ℝ)) (volume.prod ν) :=
    (integrable_inv_one_add_sq.const_mul 32).mul_prod (integrable_const (1 : ℝ))
  refine hb.mono' ((continuous_arcLineKernel.mul (hg.comp continuous_fst)).aestronglyMeasurable)
    (Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs, abs_mul, mul_one]
  calc |arcLineKernel p.1 p.2| * |g p.1| ≤ 32 * (1 + p.1 ^ 2)⁻¹ * 1 :=
        mul_le_mul (abs_arcLineDeriv_kernel_le p.2 p.1) (hg1 _) (abs_nonneg _) (by positivity)
    _ = 32 * (1 + p.1 ^ 2)⁻¹ := mul_one _

/-- **Sine coefficients of `h_ν'`.** -/
theorem integral_arcLineDeriv_mul_sin (ν : Measure ArcParam) [IsFiniteMeasure ν] (n : ℕ) :
    ∫ x, arcLineDeriv ν x * Real.sin (arcFreq n * x) =
      -(2 * arcFreq n * ∫ u, arcWhittakerCos n u ∂ν) := by
  have hint := integrable_arcLineKernel_prod ν (g := fun x => Real.sin (arcFreq n * x))
    (by fun_prop) fun x => Real.abs_sin_le_one _
  have hswap := integral_integral_swap (f := fun x u => arcLineKernel x u *
    Real.sin (arcFreq n * x)) hint
  have hl : ∫ x, arcLineDeriv ν x * Real.sin (arcFreq n * x) =
      -∫ x, ∫ u, arcLineKernel x u * Real.sin (arcFreq n * x) ∂ν := by
    rw [← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [arcLineDeriv, arcLineKernel]
    rw [neg_mul, integral_mul_const]
  rw [hl, hswap]
  have hinner : ∀ u : ArcParam, ∫ x, arcLineKernel x u * Real.sin (arcFreq n * x) =
      2 * arcFreq n * arcWhittakerCos n u := by
    intro u
    have hy := modularArcHeight_pos u.2
    have e : (fun x => arcLineKernel x u * Real.sin (arcFreq n * x)) = fun x =>
        Real.sqrt (modularArcHeight u) * ((x - u) * ((x - u) ^ 2 + modularArcHeight u ^ 2) ^
          (-(3 / 2) : ℝ) * Real.sin (arcFreq n * x)) := by
      funext x; simp only [arcLineKernel]; ring
    rw [e, integral_const_mul, integral_shift_mul_rpow_sin hy (arcFreq_pos n)]
    simp only [arcWhittakerCos, arcCosMode_apply]
    ring
  simp_rw [hinner]
  rw [integral_const_mul]

/-- **Cosine coefficients of `h_ν'`.** -/
theorem integral_arcLineDeriv_mul_cos (ν : Measure ArcParam) [IsFiniteMeasure ν] (n : ℕ) :
    ∫ x, arcLineDeriv ν x * Real.cos (arcFreq n * x) =
      2 * arcFreq n * ∫ u, arcWhittakerSin n u ∂ν := by
  have hint := integrable_arcLineKernel_prod ν (g := fun x => Real.cos (arcFreq n * x))
    (by fun_prop) fun x => Real.abs_cos_le_one _
  have hswap := integral_integral_swap (f := fun x u => arcLineKernel x u *
    Real.cos (arcFreq n * x)) hint
  have hl : ∫ x, arcLineDeriv ν x * Real.cos (arcFreq n * x) =
      -∫ x, ∫ u, arcLineKernel x u * Real.cos (arcFreq n * x) ∂ν := by
    rw [← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [arcLineDeriv, arcLineKernel]
    rw [neg_mul, integral_mul_const]
  rw [hl, hswap]
  have hinner : ∀ u : ArcParam, ∫ x, arcLineKernel x u * Real.cos (arcFreq n * x) =
      -(2 * arcFreq n * arcWhittakerSin n u) := by
    intro u
    have hy := modularArcHeight_pos u.2
    have e : (fun x => arcLineKernel x u * Real.cos (arcFreq n * x)) = fun x =>
        Real.sqrt (modularArcHeight u) * ((x - u) * ((x - u) ^ 2 + modularArcHeight u ^ 2) ^
          (-(3 / 2) : ℝ) * Real.cos (arcFreq n * x)) := by
      funext x; simp only [arcLineKernel]; ring
    rw [e, integral_const_mul, integral_shift_mul_rpow_cos hy (arcFreq_pos n)]
    simp only [arcWhittakerSin, arcSinMode_apply]
    ring
  simp_rw [hinner]
  rw [integral_neg, integral_const_mul, neg_neg]

/-! ### The derivative, the profile, and the witness -/

theorem hasDerivAt_arcPoisson (u : ArcParam) (x : ℝ) :
    HasDerivAt (fun x => (modularArcHeight u / ((x - u) ^ 2 + modularArcHeight u ^ 2)) ^
      (1 / 2 : ℝ)) (-arcLineKernel x u) x := by
  have hy := modularArcHeight_pos u.2
  have hA := sub_sq_add_modularArcHeight_sq_pos u x
  have hfun : (fun x => (modularArcHeight u / ((x - u) ^ 2 + modularArcHeight u ^ 2)) ^
      (1 / 2 : ℝ)) = fun x => Real.sqrt (modularArcHeight u) *
        ((x - u) ^ 2 + modularArcHeight u ^ 2) ^ (-(1 / 2) : ℝ) := by
    funext x
    have hA' := sub_sq_add_modularArcHeight_sq_pos u x
    rw [Real.div_rpow hy.le hA'.le, Real.rpow_neg hA'.le, ← Real.sqrt_eq_rpow, div_eq_mul_inv]
  rw [hfun]
  have hd : HasDerivAt (fun x : ℝ => (x - u) ^ 2 + modularArcHeight u ^ 2) (2 * (x - u)) x := by
    have := ((hasDerivAt_id x).sub_const (u : ℝ)).pow 2
    simpa using this.add_const (modularArcHeight u ^ 2)
  have h := (hd.rpow_const (p := -(1 / 2)) (Or.inl hA.ne')).const_mul (Real.sqrt (modularArcHeight u))
  refine h.congr_deriv ?_
  unfold arcLineKernel
  rw [show (-(1 / 2) : ℝ) - 1 = -(3 / 2) by norm_num]
  ring

theorem hasDerivAt_arcLineVector (ν : Measure ArcParam) [IsFiniteMeasure ν] (x : ℝ) :
    HasDerivAt (arcLineVector ν) (arcLineDeriv ν x) x := by
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν)
    (F := fun (x : ℝ) (u : ArcParam) =>
      (modularArcHeight u / ((x - u) ^ 2 + modularArcHeight u ^ 2)) ^ (1 / 2 : ℝ))
    (F' := fun x u => -arcLineKernel x u) (x₀ := x) (bound := fun _ => 32)
    (s := univ) Filter.univ_mem
    (Eventually.of_forall fun x' => by
      refine Continuous.aestronglyMeasurable ?_
      have : Continuous fun u : ArcParam => (modularArcHeight u /
          ((x' - u) ^ 2 + modularArcHeight u ^ 2)) ^ (1 / 2 : ℝ) := by
        unfold modularArcHeight
        exact Continuous.rpow_const (by
          refine Continuous.div (by fun_prop) (by fun_prop) fun u => ?_
          exact (sub_sq_add_modularArcHeight_sq_pos u x').ne') fun _ => Or.inr (by norm_num)
      exact this)
    (integrable_of_continuous_arc (by
      unfold modularArcHeight
      exact Continuous.rpow_const (by
        refine Continuous.div (by fun_prop) (by fun_prop) fun u => ?_
        exact (sub_sq_add_modularArcHeight_sq_pos u x).ne') fun _ => Or.inr (by norm_num)))
    ((continuous_arcLineKernel.comp (continuous_const.prodMk continuous_id)).neg.aestronglyMeasurable)
    (Eventually.of_forall fun u x' _ => by
      rw [norm_neg, Real.norm_eq_abs]
      calc |arcLineKernel x' u| ≤ 32 * (1 + x' ^ 2)⁻¹ := abs_arcLineDeriv_kernel_le u x'
        _ ≤ 32 * 1 := by
            gcongr; exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg x'])
        _ = 32 := mul_one _)
    (integrable_const _)
    (Eventually.of_forall fun u x' _ => hasDerivAt_arcPoisson u x')
  have h := key.2
  rw [integral_neg] at h
  exact h

theorem integrable_arcLineDeriv (ν : Measure ArcParam) [IsFiniteMeasure ν] :
    Integrable (arcLineDeriv ν) := by
  have hint := integrable_arcLineKernel_prod ν (g := fun _ => (1 : ℝ)) continuous_const
    fun _ => by norm_num
  have h := hint.integral_prod_left
  refine h.neg.congr (Eventually.of_forall fun x => ?_)
  simp only [arcLineDeriv, arcLineKernel, mul_one]
  rfl

/-- `e^{v/2} h_ν(e^v)` is the log-scale Poisson profile. -/
theorem exp_half_mul_arcLineVector (ν : Measure ArcParam) (v : ℝ) :
    Real.exp (v / 2) * arcLineVector ν (Real.exp v) = arcPoissonProfile ν v := by
  unfold arcLineVector arcPoissonProfile
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  have hy := modularArcHeight_pos u.2
  have hc := cosh_sub_arc_pos u v
  have e1 : (Real.exp v - u) ^ 2 + modularArcHeight u ^ 2 =
      Real.exp v * (2 * (Real.cosh v - u)) := by
    rw [sub_sq_add_modularArcHeight_sq, Real.cosh_eq]
    have h1 : Real.exp v * Real.exp (-v) = 1 := by rw [← Real.exp_add]; simp
    linear_combination (-1 : ℝ) * h1
  simp only
  rw [e1, Real.div_rpow hy.le (by positivity), Real.mul_rpow (Real.exp_pos v).le (by positivity),
    Real.mul_rpow (by norm_num) hc.le, Real.sqrt_eq_rpow, Real.div_rpow hy.le (by norm_num)]
  have hneg : (Real.cosh v - u) ^ (-1 / 2 : ℝ) = ((Real.cosh v - u) ^ (1 / 2 : ℝ))⁻¹ := by
    rw [← Real.rpow_neg hc.le]; norm_num
  rw [hneg]
  have he : Real.exp (v / 2) = Real.exp v ^ (1 / 2 : ℝ) := by
    rw [← Real.exp_mul]; ring_nf
  rw [he]
  have hev : 0 < Real.exp v ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos (Real.exp_pos v) _
  have h2 : 0 < (2 : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos two_pos _
  have hcr : 0 < (Real.cosh v - u) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hc _
  field_simp

/-- **The line-model witness.** -/
theorem exists_arcLineWitness :
    ∃ ν : Measure ArcParam, IsFiniteMeasure ν ∧ ν ≠ 0 ∧
      (∀ x, arcLineVector ν (-x) = arcLineVector ν x) ∧
      (∀ x, x ≠ 0 → arcLineVector ν (1 / x) = |x| * arcLineVector ν x) ∧
      (∀ x, HasDerivAt (arcLineVector ν) (arcLineDeriv ν x) x) ∧ Integrable (arcLineDeriv ν) ∧
      (∀ n : ℕ, ∫ x, arcLineDeriv ν x * Real.sin (arcFreq n * x) = 0 ∧
        ∫ x, arcLineDeriv ν x * Real.cos (arcFreq n * x) = 0) ∧
      ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * (Real.exp (v / 2) * arcLineVector ν (Real.exp v)) := by
  obtain ⟨ν, hfin, hne, hsym, hblind, hpd⟩ := exists_arcWitness
  refine ⟨ν, hfin, hne, fun x => ?_, fun x hx => arcLineVector_inv ν hx,
    hasDerivAt_arcLineVector ν, integrable_arcLineDeriv ν, fun n => ⟨?_, ?_⟩, fun τ => ?_⟩
  · unfold arcLineVector
    conv_rhs => rw [← hsym]
    rw [integral_map measurable_arcNeg.aemeasurable (by
      refine Continuous.aestronglyMeasurable ?_
      unfold modularArcHeight
      exact Continuous.rpow_const (by
        refine Continuous.div (by fun_prop) (by fun_prop) fun u => ?_
        exact (sub_sq_add_modularArcHeight_sq_pos u x).ne') fun _ => Or.inr (by norm_num))]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [arcNeg, modularArcHeight_neg]
    congr 2
    ring
  · rw [integral_arcLineDeriv_mul_sin, (hblind n).1, mul_zero, neg_zero]
  · rw [integral_arcLineDeriv_mul_cos, (hblind n).2, mul_zero]
  · simp_rw [exp_half_mul_arcLineVector]
    exact hpd τ

end

end RHTower
