import GaloisForLFunctions.RHTower.XiHorizontalAbsoluteMonotonicityStrip
import GaloisForLFunctions.RHTower.XiSliceSaddleArcBoundsEulerRegion
import GaloisForLFunctions.RHTower.XiSliceCoeffQuarterArc

/-!
# The slice on the real axis: Euler-edge majorant and Euler-region growth

On the real axis the slice is `f_t(y) = |ξ(½ + y + it)|²` (`xiSliceReal`).

**Euler-edge majorant** (`xiSliceReal_le_of_abs_sub_half_le`).  If `|y − ½| ≤ z − ½`, then
`f_t(y) ≤ f_t(z)`.  The Taylor coefficients of the slice at the centre `½` (the line `σ = 1`) are
nonnegative at every height (`horizontalAbsMono_half`), so `|f_t(½ + w)| ≤ Σ c_n |w|^n = f_t(½ + |w|)`.
In particular `f_t(y) ≤ f_t(1 + |y|)` for every real `y` (`xiSliceReal_le_one_add_abs`): on the
whole real axis, including the critical strip, the slice is dominated by its values on the Euler
side `σ ≥ 3/2`.  No convexity bound for `ζ` is used.

**Euler-region growth** (`xiSliceReal_growth`).  For `t ≥ 8` and `1 ≤ y₁ ≤ y₂ ≤ t/2`,

  `f_t(y₁) e^{(log(t/2) − 2K)(y₂ − y₁)} ≤ f_t(y₂) ≤ f_t(y₁) e^{(log t + 2K)(y₂ − y₁)}`,

with `K = xiEulerConstant ½`.  Indeed `(log f_t)' = ξ'/ξ(½+y+it) + ξ'/ξ(½+y−it)`
(`hasDerivAt_xiSliceReal`), which lies in `[log(t/2) − 2K, log t + 2K]` there
(`xiSliceLogDeriv_real_bounds_euler`).
-/

open Complex Filter Topology
open scoped ComplexOrder Nat

namespace RHTower

noncomputable section

/-- The slice on the real axis, `|ξ(½ + y + it)|²`. -/
def xiSliceReal (t y : ℝ) : ℝ := ‖xi (((1 / 2 + y : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2

theorem xiSliceProduct_ofReal_eq_xiSliceReal (t y : ℝ) :
    xiSliceProduct t (y : ℂ) = (xiSliceReal t y : ℂ) :=
  xiSliceProduct_ofReal_eq t y

theorem xiSliceReal_nonneg (t y : ℝ) : 0 ≤ xiSliceReal t y := by
  unfold xiSliceReal
  positivity

theorem xiSliceReal_pos (t : ℝ) {y : ℝ} (hy : 1 / 2 < y) : 0 < xiSliceReal t y := by
  unfold xiSliceReal
  have h : xi (((1 / 2 + y : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 :=
    xi_ne_zero_of_one_lt_re (by simp; linarith)
  have := norm_pos_iff.mpr h
  positivity

/-- **Euler-edge majorant.**  If `|y − ½| ≤ z − ½` then `f_t(y) ≤ f_t(z)`. -/
theorem xiSliceReal_le_of_abs_sub_half_le (t : ℝ) {y z : ℝ} (hyz : |y - 1 / 2| ≤ z - 1 / 2) :
    xiSliceReal t y ≤ xiSliceReal t z := by
  have hdnn : ∀ n, 0 ≤ iteratedDeriv n (xiSliceProduct t) (((1 / 2 : ℝ) : ℂ)) :=
    horizontalAbsMono_half t
  obtain ⟨r, hr⟩ : ∃ r : ℕ → ℝ, ∀ n,
      iteratedDeriv n (xiSliceProduct t) (((1 / 2 : ℝ) : ℂ)) = ((r n : ℝ) : ℂ) := by
    refine ⟨fun n => (iteratedDeriv n (xiSliceProduct t) (((1 / 2 : ℝ) : ℂ))).re, fun n => ?_⟩
    have h := Complex.nonneg_iff.mp (hdnn n)
    apply Complex.ext
    · rw [Complex.ofReal_re]
    · rw [Complex.ofReal_im]
      exact h.2.symm
  have hr0 : ∀ n, 0 ≤ r n := by
    intro n
    have h := hdnn n
    rw [hr n] at h
    exact_mod_cast h
  have hz0 : 0 ≤ z - 1 / 2 := le_trans (abs_nonneg _) hyz
  set a : ℕ → ℝ := fun n => ((n ! : ℝ))⁻¹ * (z - 1 / 2) ^ n * r n with ha
  set b : ℕ → ℝ := fun n => ((n ! : ℝ))⁻¹ * |y - 1 / 2| ^ n * r n with hb
  have hTz := Complex.hasSum_taylorSeries_of_entire (differentiable_xiSliceProduct t)
    (((1 / 2 : ℝ) : ℂ)) (z : ℂ)
  have hTy := Complex.hasSum_taylorSeries_of_entire (differentiable_xiSliceProduct t)
    (((1 / 2 : ℝ) : ℂ)) (y : ℂ)
  have ez : (fun n : ℕ => ((n ! : ℂ))⁻¹ • ((z : ℂ) - ((1 / 2 : ℝ) : ℂ)) ^ n •
      iteratedDeriv n (xiSliceProduct t) (((1 / 2 : ℝ) : ℂ))) = fun n => ((a n : ℝ) : ℂ) := by
    funext n
    rw [hr n, smul_eq_mul, smul_eq_mul, ha]
    push_cast
    ring
  rw [ez, xiSliceProduct_ofReal_eq_xiSliceReal] at hTz
  have hza : HasSum a (xiSliceReal t z) := Complex.hasSum_ofReal.mp hTz
  have hnorm : ∀ n : ℕ, ‖((n ! : ℂ))⁻¹ • ((y : ℂ) - ((1 / 2 : ℝ) : ℂ)) ^ n •
      iteratedDeriv n (xiSliceProduct t) (((1 / 2 : ℝ) : ℂ))‖ = b n := by
    intro n
    rw [hr n, smul_eq_mul, smul_eq_mul, ← Complex.ofReal_sub]
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, norm_inv,
      Complex.norm_natCast, abs_of_nonneg (hr0 n), hb]
    ring
  have hba : ∀ n, b n ≤ a n := by
    intro n
    simp only [ha, hb]
    have h1 := pow_le_pow_left₀ (abs_nonneg _) hyz n
    have hf : 0 ≤ ((n ! : ℝ))⁻¹ := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hf) (hr0 n)
  have hb0 : ∀ n, 0 ≤ b n := fun n => by simp only [hb]; have := hr0 n; positivity
  have hbs : Summable b := Summable.of_nonneg_of_le hb0 hba hza.summable
  have hy' : xiSliceReal t y = ‖xiSliceProduct t (y : ℂ)‖ := by
    rw [xiSliceProduct_ofReal_eq_xiSliceReal, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (xiSliceReal_nonneg t y)]
  rw [hy', ← hTy.tsum_eq]
  calc ‖∑' n : ℕ, ((n ! : ℂ))⁻¹ • ((y : ℂ) - ((1 / 2 : ℝ) : ℂ)) ^ n •
        iteratedDeriv n (xiSliceProduct t) (((1 / 2 : ℝ) : ℂ))‖
      ≤ ∑' n : ℕ, ‖((n ! : ℂ))⁻¹ • ((y : ℂ) - ((1 / 2 : ℝ) : ℂ)) ^ n •
          iteratedDeriv n (xiSliceProduct t) (((1 / 2 : ℝ) : ℂ))‖ :=
        norm_tsum_le_tsum_norm (by simp_rw [hnorm]; exact hbs)
    _ = ∑' n, b n := by simp_rw [hnorm]
    _ ≤ ∑' n, a n := hbs.tsum_le_tsum hba hza.summable
    _ = xiSliceReal t z := hza.tsum_eq

/-- On the whole real axis `f_t(y) ≤ f_t(1 + |y|)`. -/
theorem xiSliceReal_le_one_add_abs (t y : ℝ) : xiSliceReal t y ≤ xiSliceReal t (1 + |y|) := by
  refine xiSliceReal_le_of_abs_sub_half_le t ?_
  rw [abs_le]
  constructor <;> cases abs_cases y <;> linarith

/-- The slice is nondecreasing on `[½, ∞)`. -/
theorem xiSliceReal_mono {t y z : ℝ} (hy : 1 / 2 ≤ y) (hyz : y ≤ z) :
    xiSliceReal t y ≤ xiSliceReal t z := by
  refine xiSliceReal_le_of_abs_sub_half_le t ?_
  rw [abs_of_nonneg (by linarith)]
  linarith

/-- `f_t' = f_t · Re(ξ'/ξ(½+y+it) + ξ'/ξ(½+y−it))` on `y > ½`. -/
theorem hasDerivAt_xiSliceReal (t : ℝ) {y : ℝ} (hy : 1 / 2 < y) :
    HasDerivAt (xiSliceReal t) (xiSliceReal t y * (xiSliceLogDeriv t y).re) y := by
  set S := xiSliceProduct t with hSdef
  have hS : HasDerivAt S (deriv S (y : ℂ)) (y : ℂ) :=
    (differentiable_xiSliceProduct t (y : ℂ)).hasDerivAt
  have hfun : (fun x : ℝ => (S (x : ℂ)).re) = xiSliceReal t := by
    funext x
    rw [hSdef, xiSliceProduct_ofReal_eq_xiSliceReal, Complex.ofReal_re]
  have hd := hS.real_of_complex
  rw [hfun] at hd
  convert hd using 1
  have hSy : S (y : ℂ) ≠ 0 := by
    rw [hSdef, xiSliceProduct_ofReal_eq_xiSliceReal]
    exact_mod_cast (xiSliceReal_pos t hy).ne'
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast (by linarith : y ≠ 0)
  have hsc := scaledLogDeriv_xiSliceProduct (t := t) (w := (y : ℂ)) (by simpa using hy)
  rw [HTGeometry.scaledLogDeriv] at hsc
  have hder : deriv S (y : ℂ) = S (y : ℂ) * xiSliceLogDeriv t y := by
    field_simp at hsc
    rw [← hsc, hSdef]
    rw [hSdef] at hSy
    field_simp
  rw [hder, hSdef, xiSliceProduct_ofReal_eq_xiSliceReal, Complex.re_ofReal_mul]

/-- **Euler-region growth.**  For `t ≥ 8` and `1 ≤ y₁ ≤ y₂ ≤ t/2`,
`f_t(y₁) e^{(log(t/2) − 2K)(y₂−y₁)} ≤ f_t(y₂) ≤ f_t(y₁) e^{(log t + 2K)(y₂−y₁)}`. -/
theorem xiSliceReal_growth {t : ℝ} (ht : 8 ≤ t) {y₁ y₂ : ℝ} (h1 : 1 ≤ y₁) (h12 : y₁ ≤ y₂)
    (h2 : y₂ ≤ t / 2) :
    xiSliceReal t y₁ * Real.exp ((Real.log (t / 2) - 2 * xiEulerConstant (1 / 2)) * (y₂ - y₁))
        ≤ xiSliceReal t y₂ ∧
      xiSliceReal t y₂ ≤
        xiSliceReal t y₁ * Real.exp ((Real.log t + 2 * xiEulerConstant (1 / 2)) * (y₂ - y₁)) := by
  set D : Set ℝ := Set.Icc 1 (t / 2) with hD
  set g : ℝ → ℝ := fun y => Real.log (xiSliceReal t y) with hg
  have hpos : ∀ y ∈ D, 0 < xiSliceReal t y := fun y hy => xiSliceReal_pos t (by linarith [hy.1])
  have hgder : ∀ y ∈ D, HasDerivAt g (xiSliceLogDeriv t y).re y := by
    intro y hy
    have h := (hasDerivAt_xiSliceReal t (by linarith [hy.1] : (1 : ℝ) / 2 < y)).log
      (hpos y hy).ne'
    convert h using 1
    field_simp [(hpos y hy).ne']
  have hcont : ContinuousOn g D := fun y hy => (hgder y hy).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ g (interior D) := fun y hy =>
    (hgder y (interior_subset hy)).differentiableAt.differentiableWithinAt
  have hbounds : ∀ y ∈ interior D,
      Real.log (t / 2) - 2 * xiEulerConstant (1 / 2) ≤ deriv g y ∧
        deriv g y ≤ Real.log t + 2 * xiEulerConstant (1 / 2) := by
    intro y hy
    have hyD := interior_subset hy
    rw [(hgder y hyD).deriv]
    obtain ⟨-, hlo, hhi⟩ := xiSliceLogDeriv_real_bounds_euler (t := t) (R := y) (η := 1 / 2)
      (by norm_num) ht (by linarith [hyD.1]) hyD.2
    exact ⟨hlo, hhi⟩
  have hy₁ : y₁ ∈ D := ⟨h1, by linarith⟩
  have hy₂ : y₂ ∈ D := ⟨by linarith, h2⟩
  have hlow := (convex_Icc (1 : ℝ) (t / 2)).mul_sub_le_image_sub_of_le_deriv hcont hdiff
    (fun y hy => (hbounds y hy).1) y₁ hy₁ y₂ hy₂ h12
  have hup := (convex_Icc (1 : ℝ) (t / 2)).image_sub_le_mul_sub_of_deriv_le hcont hdiff
    (fun y hy => (hbounds y hy).2) y₁ hy₁ y₂ hy₂ h12
  simp only [hg] at hlow hup
  have hp1 := hpos y₁ hy₁
  have hp2 := hpos y₂ hy₂
  constructor
  · rw [← Real.exp_log hp1, ← Real.exp_log hp2, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  · rw [← Real.exp_log hp1, ← Real.exp_log hp2, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)

end

end RHTower
