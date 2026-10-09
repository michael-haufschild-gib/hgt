import GaloisForLFunctions.RHTower.RiemannKernelDampedTransformNotLaguerrePolya
import GaloisForLFunctions.HTGeometry.LaguerrePolyaLocallyUniformLimit

/-!
# The sine symbol preserves the Laguerre–Pólya class on Riemann-kernel transforms

Fix `s > 0`, put `b = π/6`, `x(u) = b + isu`, `y(u) = −b + isu`, and let

  `σ_s(u) = (2π/3) sin(x(u)) sin(y(u)) / y(u)`,

the kernel symbol of `φ₃(sD)` with `φ₃(w) = (2π/3) sin(w + π/6) sin(w − π/6)/(w − π/6)`.

**Theorem** (`laguerrePolya_paperFT_mul_sineSym`). If `g` has exponential growth and
`z ↦ ∫ Φ(u)g(u)e^{izu}du` is Laguerre–Pólya, so is `z ↦ ∫ Φ(u)g(u)σ_s(u)e^{izu}du`.

**Proof.**
* The truncated Euler products `σ_{s,m}(u) = (2π/3)·x∏_{j<m}(1 − x²/a_j²)·∏_{j<m}(1 − y²/a_j²)`,
  `a_j = π(j+1)`, are products of linear factors `A + iBu` with `A ≠ 0`. Each factor is a real
  multiple of `1 − icu`, which acts as `1 − cD` (`paperFT_kernel_sub_smul_deriv`) and preserves
  the class (`laguerrePolya_paperFT_mul_linear`).
* `σ_{s,m} → σ_s` pointwise by Euler's sine product, and `|σ_{s,m}(u)| ≤ C e^{2s|u|}` uniformly in
  `m`, because `t∏(1 + t²/a_j²) ≤ sinh t` (`mul_prod_one_add_le_sinh`). Since `Φ` decays faster
  than every exponential, dominated convergence makes the transforms converge locally uniformly
  (`tendstoLocallyUniformly_paperFT_approxSym`). The class is closed under such limits
  (`LaguerrePolya.of_tendstoLocallyUniformly`).
-/

open Complex MeasureTheory Filter Topology Set Metric
open Zeta23
open GaloisForLFunctions.HTGeometry

namespace RHTower.KernelStrip

noncomputable section

/-! ## Linear factors -/

theorem expGrowth_linear (A B : ℝ) : ExpGrowth fun u : ℝ => (A : ℂ) + I * B * u := by
  refine ⟨by fun_prop, |A| + 1, |B|, fun u => ?_⟩
  have h1 : ‖(A : ℂ) + I * B * u‖ ≤ |A| + |B| * |u| := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
  have h2 : |B| * |u| + 1 ≤ Real.exp (|B| * |u|) := by linarith [Real.add_one_le_exp (|B| * |u|)]
  have h3 : 1 ≤ Real.exp (|B| * |u|) := Real.one_le_exp (by positivity)
  nlinarith [abs_nonneg A]

theorem paperFT_kernel_const_mul {h : ℝ → ℂ} (a : ℂ) (z : ℂ) :
    paperFT (fun u => riemannPhiKernel u * (h u * a)) z =
      a * paperFT (fun u => riemannPhiKernel u * h u) z := by
  unfold paperFT
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only
  ring

/-- **A linear factor `A + iBu` (`A ≠ 0`) preserves the class.** -/
theorem laguerrePolya_paperFT_mul_linear {h : ℝ → ℂ} (hh : ExpGrowth h) {A : ℝ} (hA : A ≠ 0)
    (B : ℝ) (hLP : GaloisForLFunctions.HTGeometry.LaguerrePolya fun z : ℂ => paperFT (fun u => riemannPhiKernel u * h u) z) :
    GaloisForLFunctions.HTGeometry.LaguerrePolya fun z : ℂ =>
      paperFT (fun u => riemannPhiKernel u * (h u * ((A : ℂ) + I * B * u))) z := by
  set c : ℝ := -B / A with hc
  have e : ∀ u : ℝ, h u * ((A : ℂ) + I * B * u) = (h u * (1 - I * c * u)) * (A : ℂ) := by
    intro u
    have hA' : (A : ℂ) ≠ 0 := by exact_mod_cast hA
    simp only [hc]
    push_cast
    field_simp
    ring
  have hfun : (fun z : ℂ =>
      paperFT (fun u => riemannPhiKernel u * (h u * ((A : ℂ) + I * B * u))) z) =
      fun z : ℂ => (A : ℂ) * (paperFT (fun u => riemannPhiKernel u * h u) z -
        (c : ℂ) * deriv (fun z : ℂ => paperFT (fun u => riemannPhiKernel u * h u) z) z) := by
    funext z
    rw [paperFT_kernel_sub_smul_deriv hh c z, ← paperFT_kernel_const_mul]
    congr 1
    funext u
    rw [e u]
  rw [hfun]
  exact (laguerrePolya_sub_smul_deriv hLP c).const_mul A

/-! ## The sinh bound for partial Euler products -/

/-- `t∏_{j<m}(1 + t²/(π(j+1))²) → sinh t`. -/
theorem tendsto_mul_prod_one_add (t : ℝ) :
    Tendsto (fun m => t * ∏ j ∈ Finset.range m, (1 + t ^ 2 / (Real.pi * (j + 1)) ^ 2)) atTop
      (𝓝 (Real.sinh t)) := by
  have h := Complex.tendsto_euler_sin_prod (I * t / Real.pi)
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have e1 : ∀ m, (Real.pi : ℂ) * (I * t / Real.pi) *
      ∏ j ∈ Finset.range m, (1 - (I * t / Real.pi) ^ 2 / ((j : ℂ) + 1) ^ 2) =
      I * ((t * ∏ j ∈ Finset.range m, (1 + t ^ 2 / (Real.pi * (j + 1)) ^ 2) : ℝ) : ℂ) := by
    intro m
    have hpi : (Real.pi : ℂ) * (I * t / Real.pi) = I * t := by field_simp
    rw [hpi, mul_assoc]
    congr 1
    push_cast
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    have hj : ((j : ℂ) + 1) ≠ 0 := by
      have : (0 : ℝ) < (j : ℝ) + 1 := by positivity
      exact_mod_cast this.ne'
    rw [div_pow, mul_pow, I_sq]
    field_simp
    ring
  have e2 : Complex.sin ((Real.pi : ℂ) * (I * t / Real.pi)) = I * ((Real.sinh t : ℝ) : ℂ) := by
    rw [show (Real.pi : ℂ) * (I * t / Real.pi) = (t : ℂ) * I by field_simp,
      Complex.sin_mul_I, Complex.ofReal_sinh]
    ring
  simp_rw [e1, e2] at h
  have h3 := h.const_mul (-I)
  have e3 : ∀ w : ℂ, -I * (I * w) = w := fun w => by
    rw [← mul_assoc, show -I * I = 1 by rw [neg_mul, I_mul_I, neg_neg]]; ring
  simp only [e3] at h3
  have h4 := (Complex.continuous_re.tendsto _).comp h3
  simp only [Function.comp_def, Complex.ofReal_re] at h4
  exact h4

/-- **The sinh bound.** For `t ≥ 0`, `t∏_{j<m}(1 + t²/(π(j+1))²) ≤ sinh t`. -/
theorem mul_prod_one_add_le_sinh {t : ℝ} (ht : 0 ≤ t) (m : ℕ) :
    t * ∏ j ∈ Finset.range m, (1 + t ^ 2 / (Real.pi * (j + 1)) ^ 2) ≤ Real.sinh t := by
  refine Monotone.ge_of_tendsto (f := fun m => t * ∏ j ∈ Finset.range m,
    (1 + t ^ 2 / (Real.pi * (j + 1)) ^ 2)) ?_ (tendsto_mul_prod_one_add t) m
  refine monotone_nat_of_le_succ fun n => ?_
  simp only [Finset.prod_range_succ]
  have h0 : 0 ≤ t * ∏ j ∈ Finset.range n, (1 + t ^ 2 / (Real.pi * (j + 1)) ^ 2) :=
    mul_nonneg ht (Finset.prod_nonneg fun j _ => by positivity)
  have h1 : 1 ≤ 1 + t ^ 2 / (Real.pi * (n + 1)) ^ 2 := by
    have : 0 ≤ t ^ 2 / (Real.pi * (n + 1)) ^ 2 := by positivity
    linarith
  calc t * ∏ j ∈ Finset.range n, (1 + t ^ 2 / (Real.pi * (j + 1)) ^ 2)
      = (t * ∏ j ∈ Finset.range n, (1 + t ^ 2 / (Real.pi * (j + 1)) ^ 2)) * 1 := by ring
    _ ≤ (t * ∏ j ∈ Finset.range n, (1 + t ^ 2 / (Real.pi * (j + 1)) ^ 2)) *
          (1 + t ^ 2 / (Real.pi * (n + 1)) ^ 2) := mul_le_mul_of_nonneg_left h1 h0
    _ = _ := by ring

/-- `‖∏_{j<m}(1 − w²/(π(j+1))²)‖ ≤ ∏_{j<m}(1 + ‖w‖²/(π(j+1))²)`. -/
theorem norm_sineEulerFactors_le (w : ℂ) (m : ℕ) :
    ‖∏ j ∈ Finset.range m, (1 - w ^ 2 / ((Real.pi : ℂ) * (j + 1)) ^ 2)‖ ≤
      ∏ j ∈ Finset.range m, (1 + ‖w‖ ^ 2 / (Real.pi * (j + 1)) ^ 2) := by
  rw [norm_prod]
  refine Finset.prod_le_prod (fun j _ => norm_nonneg _) fun j _ => ?_
  refine (norm_sub_le _ _).trans ?_
  rw [norm_one, norm_div, norm_pow, norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]
  have : ‖((j : ℂ) + 1)‖ = (j : ℝ) + 1 := by
    rw [show ((j : ℂ) + 1) = (((j : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [this]

/-! ## The truncated sine symbols -/

/-- `x(u) = π/6 + isu`. -/
def sineArgPlus (s u : ℝ) : ℂ := ((Real.pi / 6 : ℝ) : ℂ) + I * s * u

/-- `y(u) = −π/6 + isu`. -/
def sineArgMinus (s u : ℝ) : ℂ := ((-(Real.pi / 6) : ℝ) : ℂ) + I * s * u

/-- The partial Euler product `∏_{j<m}(1 − w²/(π(j+1))²)`. -/
def sineEulerPartial (m : ℕ) (w : ℂ) : ℂ :=
  ∏ j ∈ Finset.range m, (1 - w ^ 2 / ((Real.pi : ℂ) * (j + 1)) ^ 2)

/-- The truncated symbol `σ_{s,m} = (2π/3)·x∏(1 − x²/a_j²)·∏(1 − y²/a_j²)`. -/
def approxSym (s : ℝ) (m : ℕ) (u : ℝ) : ℂ :=
  ((2 * Real.pi / 3 : ℝ) : ℂ) * (sineArgPlus s u * sineEulerPartial m (sineArgPlus s u)) *
    sineEulerPartial m (sineArgMinus s u)

/-- The sine symbol `σ_s = (2π/3) sin x · (sin y)/y`. -/
def sineSym (s : ℝ) (u : ℝ) : ℂ :=
  ((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.sin (sineArgPlus s u) *
    (Complex.sin (sineArgMinus s u) / sineArgMinus s u)

theorem sineArgMinus_ne_zero (s u : ℝ) : sineArgMinus s u ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp [sineArgMinus] at this

theorem norm_I_mul_mul (s u : ℝ) : ‖I * (s : ℂ) * (u : ℂ)‖ = |s| * |u| := by
  rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs]

theorem norm_sineArgPlus_le (s u : ℝ) : ‖sineArgPlus s u‖ ≤ Real.pi / 6 + |s| * |u| := by
  have h1 : ‖((Real.pi / 6 : ℝ) : ℂ)‖ = Real.pi / 6 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have h := norm_add_le ((Real.pi / 6 : ℝ) : ℂ) (I * (s : ℂ) * (u : ℂ))
  rw [h1, norm_I_mul_mul] at h
  exact h

theorem norm_sineArgMinus_le (s u : ℝ) : ‖sineArgMinus s u‖ ≤ Real.pi / 6 + |s| * |u| := by
  have h1 : ‖((-(Real.pi / 6) : ℝ) : ℂ)‖ = Real.pi / 6 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]
  have h := norm_add_le ((-(Real.pi / 6) : ℝ) : ℂ) (I * (s : ℂ) * (u : ℂ))
  rw [h1, norm_I_mul_mul] at h
  exact h

theorem pi_div_six_le_norm_sineArgMinus (s u : ℝ) : Real.pi / 6 ≤ ‖sineArgMinus s u‖ := by
  have h := Complex.abs_re_le_norm (sineArgMinus s u)
  have hre : (sineArgMinus s u).re = -(Real.pi / 6) := by simp [sineArgMinus]
  rw [hre, abs_neg, abs_of_pos (by positivity)] at h
  exact h

theorem real_sinh_le_exp (t : ℝ) : Real.sinh t ≤ Real.exp t := by
  rw [Real.sinh_eq]
  linarith [Real.exp_pos (-t), Real.exp_pos t]

/-- **Uniform bound.** `|σ_{s,m}(u)| ≤ 4e^{π/3}e^{2|s||u|}`. -/
theorem norm_approxSym_le (s : ℝ) (m : ℕ) (u : ℝ) :
    ‖approxSym s m u‖ ≤ 4 * Real.exp (Real.pi / 3) * Real.exp (2 * |s| * |u|) := by
  set x := sineArgPlus s u
  set y := sineArgMinus s u
  have hb : 0 < Real.pi / 6 := by positivity
  have hx := norm_sineEulerFactors_le x m
  have hy := norm_sineEulerFactors_le y m
  have hxs := mul_prod_one_add_le_sinh (norm_nonneg x) m
  have hys := mul_prod_one_add_le_sinh (norm_nonneg y) m
  have hyb := pi_div_six_le_norm_sineArgMinus s u
  have hy0 : 0 < ‖y‖ := lt_of_lt_of_le hb hyb
  have hP0 : 0 ≤ ∏ j ∈ Finset.range m, (1 + ‖y‖ ^ 2 / (Real.pi * (j + 1)) ^ 2) :=
    Finset.prod_nonneg fun j _ => by positivity
  -- the two factors
  have h1 : ‖x * sineEulerPartial m x‖ ≤ Real.exp ‖x‖ := by
    rw [norm_mul, sineEulerPartial]
    calc ‖x‖ * ‖∏ j ∈ Finset.range m, (1 - x ^ 2 / ((Real.pi : ℂ) * (j + 1)) ^ 2)‖
        ≤ ‖x‖ * ∏ j ∈ Finset.range m, (1 + ‖x‖ ^ 2 / (Real.pi * (j + 1)) ^ 2) :=
          mul_le_mul_of_nonneg_left hx (norm_nonneg _)
      _ ≤ Real.sinh ‖x‖ := hxs
      _ ≤ Real.exp ‖x‖ := real_sinh_le_exp _
  have h2 : ‖sineEulerPartial m y‖ ≤ Real.exp ‖y‖ / (Real.pi / 6) := by
    rw [sineEulerPartial, le_div_iff₀ hb]
    calc ‖∏ j ∈ Finset.range m, (1 - y ^ 2 / ((Real.pi : ℂ) * (j + 1)) ^ 2)‖ * (Real.pi / 6)
        ≤ (∏ j ∈ Finset.range m, (1 + ‖y‖ ^ 2 / (Real.pi * (j + 1)) ^ 2)) * ‖y‖ :=
          mul_le_mul hy hyb hb.le hP0
      _ = ‖y‖ * ∏ j ∈ Finset.range m, (1 + ‖y‖ ^ 2 / (Real.pi * (j + 1)) ^ 2) := by ring
      _ ≤ Real.sinh ‖y‖ := hys
      _ ≤ Real.exp ‖y‖ := real_sinh_le_exp _
  have hxe : Real.exp ‖x‖ ≤ Real.exp (Real.pi / 6 + |s| * |u|) :=
    Real.exp_le_exp.mpr (norm_sineArgPlus_le s u)
  have hye : Real.exp ‖y‖ ≤ Real.exp (Real.pi / 6 + |s| * |u|) :=
    Real.exp_le_exp.mpr (norm_sineArgMinus_le s u)
  have hc : ‖((2 * Real.pi / 3 : ℝ) : ℂ)‖ = 2 * Real.pi / 3 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [approxSym, norm_mul, norm_mul, hc]
  calc 2 * Real.pi / 3 * ‖x * sineEulerPartial m x‖ * ‖sineEulerPartial m y‖
      ≤ 2 * Real.pi / 3 * Real.exp (Real.pi / 6 + |s| * |u|) *
          (Real.exp (Real.pi / 6 + |s| * |u|) / (Real.pi / 6)) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left (h1.trans hxe) (by positivity))
          (h2.trans (div_le_div_of_nonneg_right hye hb.le)) (norm_nonneg _) (by positivity)
    _ = 4 * Real.exp (Real.pi / 3) * Real.exp (2 * |s| * |u|) := by
        have hE : Real.exp (Real.pi / 6 + |s| * |u|) * Real.exp (Real.pi / 6 + |s| * |u|) =
            Real.exp (Real.pi / 3) * Real.exp (2 * |s| * |u|) := by
          rw [← Real.exp_add, ← Real.exp_add]; ring_nf
        have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
        calc 2 * Real.pi / 3 * Real.exp (Real.pi / 6 + |s| * |u|) *
              (Real.exp (Real.pi / 6 + |s| * |u|) / (Real.pi / 6))
            = 4 * (Real.exp (Real.pi / 6 + |s| * |u|) * Real.exp (Real.pi / 6 + |s| * |u|)) := by
              field_simp; ring
          _ = _ := by rw [hE]; ring

/-- **Euler.** `σ_{s,m}(u) → σ_s(u)`. -/
theorem tendsto_approxSym (s u : ℝ) :
    Tendsto (fun m => approxSym s m u) atTop (𝓝 (sineSym s u)) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have euler : ∀ w : ℂ, Tendsto (fun m => w * sineEulerPartial m w) atTop (𝓝 (Complex.sin w)) := by
    intro w
    have h := Complex.tendsto_euler_sin_prod (w / Real.pi)
    have e1 : (fun n => (Real.pi : ℂ) * (w / Real.pi) *
        ∏ j ∈ Finset.range n, (1 - (w / Real.pi) ^ 2 / ((j : ℂ) + 1) ^ 2)) =
        fun m => w * sineEulerPartial m w := by
      funext n
      rw [sineEulerPartial, show (Real.pi : ℂ) * (w / Real.pi) = w by field_simp]
      congr 1
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [div_pow, mul_pow, div_div]
    rw [e1, show (Real.pi : ℂ) * (w / Real.pi) = w by field_simp] at h
    exact h
  have hy := (euler (sineArgMinus s u)).div_const (sineArgMinus s u)
  have hy' : Tendsto (fun m => sineEulerPartial m (sineArgMinus s u)) atTop
      (𝓝 (Complex.sin (sineArgMinus s u) / sineArgMinus s u)) := by
    refine hy.congr fun m => ?_
    field_simp [sineArgMinus_ne_zero s u]
  have := ((euler (sineArgPlus s u)).const_mul ((2 * Real.pi / 3 : ℝ) : ℂ)).mul hy'
  simpa only [approxSym, sineSym, mul_assoc] using this

theorem norm_sineSym_le (s u : ℝ) :
    ‖sineSym s u‖ ≤ 4 * Real.exp (Real.pi / 3) * Real.exp (2 * |s| * |u|) :=
  le_of_tendsto' (continuous_norm.tendsto _ |>.comp (tendsto_approxSym s u))
    fun m => norm_approxSym_le s m u

theorem continuous_approxSym (s : ℝ) (m : ℕ) : Continuous (approxSym s m) := by
  unfold approxSym sineEulerPartial sineArgPlus sineArgMinus
  fun_prop

theorem continuous_sineSym (s : ℝ) : Continuous (sineSym s) := by
  unfold sineSym
  refine Continuous.mul (by unfold sineArgPlus; fun_prop) ?_
  exact (by unfold sineArgMinus; fun_prop : Continuous fun u => Complex.sin (sineArgMinus s u)).div
    (by unfold sineArgMinus; fun_prop) (sineArgMinus_ne_zero s)

theorem expGrowth_approxSym (s : ℝ) (m : ℕ) : ExpGrowth (approxSym s m) :=
  ⟨continuous_approxSym s m, 4 * Real.exp (Real.pi / 3), 2 * |s|, fun u =>
    norm_approxSym_le s m u⟩

theorem expGrowth_sineSym (s : ℝ) : ExpGrowth (sineSym s) :=
  ⟨continuous_sineSym s, 4 * Real.exp (Real.pi / 3), 2 * |s|, fun u => norm_sineSym_le s u⟩

/-! ## The truncated symbols preserve the class -/

theorem laguerrePolya_paperFT_congr {h₁ h₂ : ℝ → ℂ} (e : ∀ u, h₁ u = h₂ u)
    (hl : GaloisForLFunctions.HTGeometry.LaguerrePolya fun z : ℂ =>
      paperFT (fun u => riemannPhiKernel u * h₁ u) z) :
    GaloisForLFunctions.HTGeometry.LaguerrePolya fun z : ℂ =>
      paperFT (fun u => riemannPhiKernel u * h₂ u) z := by
  have : h₁ = h₂ := funext e
  subst this
  exact hl

/-- **The truncated symbols preserve the class.** -/
theorem laguerrePolya_paperFT_mul_approxSym {g : ℝ → ℂ} (hg : ExpGrowth g) (s : ℝ)
    (hLP : GaloisForLFunctions.HTGeometry.LaguerrePolya fun z : ℂ =>
      paperFT (fun u => riemannPhiKernel u * g u) z) (m : ℕ) :
    GaloisForLFunctions.HTGeometry.LaguerrePolya fun z : ℂ =>
      paperFT (fun u => riemannPhiKernel u * (g u * approxSym s m u)) z := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  induction m with
  | zero =>
    have h1 := laguerrePolya_paperFT_mul_linear hg (A := 2 * Real.pi / 3) (by positivity) 0 hLP
    have h2 := laguerrePolya_paperFT_mul_linear (hg.mul (expGrowth_linear _ 0))
      (A := Real.pi / 6) (by positivity) s h1
    refine laguerrePolya_paperFT_congr (fun u => ?_) h2
    simp only [approxSym, sineEulerPartial, sineArgPlus, Finset.prod_range_zero]
    push_cast
    ring
  | succ m ih =>
    set a : ℝ := Real.pi * ((m : ℝ) + 1) with ha
    have ha0 : 0 < a := by positivity
    have hb : (Real.pi / 6) / a ≤ 1 / 6 := by
      rw [ha, div_le_iff₀ ha0]
      have : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
      nlinarith [Real.pi_pos]
    have hb0 : 0 ≤ (Real.pi / 6) / a := by positivity
    have hA1 : 1 - (Real.pi / 6) / a ≠ 0 := by linarith
    have hA2 : 1 + (Real.pi / 6) / a ≠ 0 := by linarith
    have hgm := hg.mul (expGrowth_approxSym s m)
    have s1 := laguerrePolya_paperFT_mul_linear hgm hA1 (-s / a) ih
    have s2 := laguerrePolya_paperFT_mul_linear (hgm.mul (expGrowth_linear _ _)) hA2 (s / a) s1
    have s3 := laguerrePolya_paperFT_mul_linear
      ((hgm.mul (expGrowth_linear _ _)).mul (expGrowth_linear _ _)) hA2 (-s / a) s2
    have s4 := laguerrePolya_paperFT_mul_linear
      (((hgm.mul (expGrowth_linear _ _)).mul (expGrowth_linear _ _)).mul (expGrowth_linear _ _))
      hA1 (s / a) s3
    refine laguerrePolya_paperFT_congr (fun u => ?_) s4
    have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha0.ne'
    have hpa : (Real.pi : ℂ) * ((m : ℂ) + 1) = (a : ℂ) := by rw [ha]; push_cast; ring
    simp only [approxSym, sineEulerPartial, Finset.prod_range_succ, sineArgPlus, sineArgMinus]
    rw [hpa]
    push_cast
    field_simp
    ring

/-! ## Dominated convergence -/

theorem norm_cexp_I_mul_le_of_norm_le {z : ℂ} {R : ℝ} (hz : ‖z‖ ≤ R) (u : ℝ) :
    ‖cexp (I * z * u)‖ ≤ Real.exp (|R| * |u|) := by
  rw [Complex.norm_exp]
  refine Real.exp_le_exp.mpr ?_
  have : (I * z * (u : ℂ)).re = -(z.im * u) := by simp
  rw [this]
  have h1 : -(z.im * u) ≤ |z.im| * |u| := by rw [← abs_mul]; exact neg_le_abs _
  have h2 : |z.im| ≤ |R| := (Complex.abs_im_le_norm z).trans (hz.trans (le_abs_self R))
  nlinarith [abs_nonneg u]

/-- **Locally uniform convergence of the transforms.** -/
theorem tendstoLocallyUniformly_paperFT_approxSym {g : ℝ → ℂ} (hg : ExpGrowth g) (s : ℝ) :
    TendstoLocallyUniformly
      (fun (m : ℕ) (z : ℂ) => paperFT (fun u => riemannPhiKernel u * (g u * approxSym s m u)) z)
      (fun z : ℂ => paperFT (fun u => riemannPhiKernel u * (g u * sineSym s u)) z) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  have hg' := hg
  obtain ⟨gc, A, κ, hA⟩ := hg
  have hA0 : 0 ≤ A := by have := (norm_nonneg _).trans (hA 0); simpa using this
  set B : ℝ := 8 * Real.exp (Real.pi / 3) with hB
  obtain ⟨C, hC0, hC⟩ := exists_norm_riemannPhiKernel_le_exp (κ + 2 * |s| + |R| + 1)
  have hdiff : ∀ (m : ℕ) (u : ℝ), ‖sineSym s u - approxSym s m u‖ ≤
      B * Real.exp (2 * |s| * |u|) := fun m u => by
    refine (norm_sub_le _ _).trans ?_
    have := norm_sineSym_le s u
    have := norm_approxSym_le s m u
    rw [hB]; linarith
  set D : ℕ → ℝ → ℝ := fun m u => ‖riemannPhiKernel u‖ * ‖g u‖ *
    ‖sineSym s u - approxSym s m u‖ * Real.exp (|R| * |u|) with hD
  have hDbound : ∀ m u, D m u ≤ C * A * B * Real.exp (-(1 * |u|)) := by
    intro m u
    have hu := abs_nonneg u
    have e1 := hC u
    have e2 := hA u
    have e3 := hdiff m u
    calc D m u ≤ (C * Real.exp (-((κ + 2 * |s| + |R| + 1) * |u|))) * (A * Real.exp (κ * |u|)) *
          (B * Real.exp (2 * |s| * |u|)) * Real.exp (|R| * |u|) := by
          simp only [hD]
          gcongr
      _ = C * A * B * Real.exp (-(1 * |u|)) := by
          rw [show C * Real.exp (-((κ + 2 * |s| + |R| + 1) * |u|)) * (A * Real.exp (κ * |u|)) *
              (B * Real.exp (2 * |s| * |u|)) * Real.exp (|R| * |u|) =
              C * A * B * (Real.exp (-((κ + 2 * |s| + |R| + 1) * |u|)) * Real.exp (κ * |u|) *
                Real.exp (2 * |s| * |u|) * Real.exp (|R| * |u|)) by ring]
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
          ring_nf
  have hDcont : ∀ m, Continuous (D m) := fun m => by
    simp only [hD]
    exact ((continuous_norm.comp continuous_riemannPhiKernel).mul (continuous_norm.comp gc)).mul
      (continuous_norm.comp ((continuous_sineSym s).sub (continuous_approxSym s m))) |>.mul
      (by fun_prop)
  have hint : Integrable fun u : ℝ => C * A * B * Real.exp (-(1 * |u|)) :=
    (RHTower.integrable_exp_neg_mul_abs' (c := 1) one_pos).const_mul _
  have hDint : ∀ m, Integrable (D m) := fun m =>
    hint.mono' (hDcont m).aestronglyMeasurable (Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by simp only [hD]; positivity)]
      exact hDbound m u)
  have hDlim : Tendsto (fun m => ∫ u, D m u) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (fun u => C * A * B * Real.exp (-(1 * |u|)))
      (fun m => (hDcont m).aestronglyMeasurable) hint
      (fun m => Eventually.of_forall fun u => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by simp only [hD]; positivity)]
        exact hDbound m u)
      (Eventually.of_forall fun u => by
        have h1 : Tendsto (fun m => ‖sineSym s u - approxSym s m u‖) atTop (𝓝 0) := by
          have := (tendsto_approxSym s u).const_sub (sineSym s u)
          rw [sub_self] at this
          have h2 := (continuous_norm.tendsto _).comp this
          rw [norm_zero] at h2
          exact h2
        have := (h1.const_mul (‖riemannPhiKernel u‖ * ‖g u‖)).mul_const (Real.exp (|R| * |u|))
        simpa [hD, mul_assoc] using this)
    simpa using h
  -- the transform defect is dominated by the scalar defect
  have hG : ∀ (m : ℕ) (z : ℂ), ‖z‖ ≤ R →
      dist (paperFT (fun u => riemannPhiKernel u * (g u * sineSym s u)) z)
        (paperFT (fun u => riemannPhiKernel u * (g u * approxSym s m u)) z) ≤ ∫ u, D m u := by
    intro m z hz
    have hz' : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
    obtain ⟨C₁, -, hC₁⟩ := integrable_kernel_mul_cexp (hg'.mul (expGrowth_sineSym s)) ‖z‖
    obtain ⟨C₂, -, hC₂⟩ := integrable_kernel_mul_cexp (hg'.mul (expGrowth_approxSym s m)) ‖z‖
    have i1 : Integrable fun u : ℝ => riemannPhiKernel u * (g u * sineSym s u) * cexp (I * z * u) :=
      ((RHTower.integrable_exp_neg_mul_abs' (c := 1) one_pos).const_mul C₁).mono'
        ((continuous_riemannPhiKernel.mul (gc.mul (continuous_sineSym s))).mul
          (by fun_prop)).aestronglyMeasurable
        (Eventually.of_forall fun u => (hC₁ z hz' u).1)
    have i2 : Integrable fun u : ℝ =>
        riemannPhiKernel u * (g u * approxSym s m u) * cexp (I * z * u) :=
      ((RHTower.integrable_exp_neg_mul_abs' (c := 1) one_pos).const_mul C₂).mono'
        ((continuous_riemannPhiKernel.mul (gc.mul (continuous_approxSym s m))).mul
          (by fun_prop)).aestronglyMeasurable
        (Eventually.of_forall fun u => (hC₂ z hz' u).1)
    rw [dist_eq_norm]
    unfold paperFT
    rw [← integral_sub i1 i2]
    refine norm_integral_le_of_norm_le (hDint m) (Eventually.of_forall fun u => ?_)
    have e : riemannPhiKernel u * (g u * sineSym s u) * cexp (I * z * u) -
        riemannPhiKernel u * (g u * approxSym s m u) * cexp (I * z * u) =
        riemannPhiKernel u * g u * (sineSym s u - approxSym s m u) * cexp (I * z * u) := by ring
    rw [e, norm_mul, norm_mul, norm_mul]
    simp only [hD]
    exact mul_le_mul_of_nonneg_left (norm_cexp_I_mul_le_of_norm_le hz u) (by positivity)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hDlim.eventually (gt_mem_nhds hε)] with m hm z hz
  have hzR : ‖z‖ ≤ R := by simpa using hR hz
  exact (hG m z hzR).trans_lt hm

/-- **The sine symbol preserves the class.** -/
theorem laguerrePolya_paperFT_mul_sineSym {g : ℝ → ℂ} (hg : ExpGrowth g) (s : ℝ)
    (hLP : GaloisForLFunctions.HTGeometry.LaguerrePolya fun z : ℂ =>
      paperFT (fun u => riemannPhiKernel u * g u) z) :
    GaloisForLFunctions.HTGeometry.LaguerrePolya fun z : ℂ =>
      paperFT (fun u => riemannPhiKernel u * (g u * sineSym s u)) z :=
  GaloisForLFunctions.HTGeometry.LaguerrePolya.of_tendstoLocallyUniformly
    (laguerrePolya_paperFT_mul_approxSym hg s hLP) (tendstoLocallyUniformly_paperFT_approxSym hg s)

end

end RHTower.KernelStrip
