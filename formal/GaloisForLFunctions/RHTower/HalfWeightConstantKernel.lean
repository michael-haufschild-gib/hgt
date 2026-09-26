import GaloisForLFunctions.RHTower.HalfWeightKernelContinuation
import GaloisForLFunctions.RHTower.HalfWeightThetaMultiplier

/-!
# The constant term of the weight-½ kernel and its continuation

For `h_{a,b}(x) = (x+iy)^{-a}(x-iy)^{-b}` and `Re(a+b) > 1` write `A = ∫h_{a,b}`,
`B = ∫h_{a+1,b}`, `C = ∫h_{a,b+1}`, `D = ∫h_{a+1,b+1}`. Three relations hold:

* `aB + bC = 0` (`integral_hab_R1`: the Fourier recursion at `ξ = 0`);
* `C - B = 2iy D` (`hab_sub`: `(x+iy) - (x-iy) = 2iy`);
* `(1-a-b)A = -iay B + iby C` (`integral_hab_R3`: integrate `(x h_{a,b})'`, which tends to `0`).

Eliminating `B` and `C` gives the **constant-term recursion** (`integral_hab_rec`)
`(a+b)(a+b-1) ∫h_{a,b} = 4ab y² ∫h_{a+1,b+1}`.

* `JN`: `J_0 = ∫h`, `J_{k+1}(a,b) = 4ab y² J_k(a+1,b+1)`; `Pk`: `P_k(s) = ∏_{j<k}(s+2j)(s+2j-1)`.
  `JN_eq`: `P_k(a+b)∫h_{a,b} = J_k(a,b)` on `Re(a+b) > 1`; `JN_add`: `J_{k+m} = P_m(a+b+2k) J_k`;
  `JN_scale`: `J_k^{(y)}(a,b) = y^{1-a-b} J_k^{(1)}(a,b)`; `differentiableAt_JN`: holomorphy along
  `(w+α, w+β)` on `Re(2w+α+β) + 2k > 1`.
* `integral_kerH_eq`: `P_k(2w) ∫kerH_{y,w} = y^{1-w} c_k(w)` for `Re w > 1/2`, with
  `c_k(w) = J_k^{(1)}(w+1/4, w-1/4)` holomorphic on `Re w > 1/2 - k` (`differentiableAt_cK`).

So the constant term `∫kerH_{y,w} = y^{1-w} c_1(w)/(2w(2w-1))` continues meromorphically across
`Re w = 1/2`, with at most a simple pole at `w = 1/2` on `Re w > 0`.
-/

open Real Complex MeasureTheory Filter Topology
open scoped FourierTransform

namespace GaloisForLFunctions.RHTower.HalfWeight

open GaloisForLFunctions.RHTower.SelbergPoincareKernel

noncomputable section

variable {y : ℝ}

/-! ### Algebraic relations between the `h_{a,b}` -/

theorem plus_mul_hab (hy : 0 < y) (a b : ℂ) (x : ℝ) :
    ((x : ℂ) + y * I) * hab y (a + 1) b x = hab y a b x := by
  unfold hab
  have h := Complex.cpow_add (-(a + 1)) 1 (plus_ne_zero hy x)
  rw [Complex.cpow_one, show -(a + 1) + 1 = -a by ring] at h
  rw [h]; ring

theorem minus_mul_hab (hy : 0 < y) (a b : ℂ) (x : ℝ) :
    ((x : ℂ) - y * I) * hab y a (b + 1) x = hab y a b x := by
  unfold hab
  have h := Complex.cpow_add (-(b + 1)) 1 (minus_ne_zero hy x)
  rw [Complex.cpow_one, show -(b + 1) + 1 = -b by ring] at h
  rw [h]; ring

/-- `h_{a,b+1} - h_{a+1,b} = 2iy h_{a+1,b+1}`. -/
theorem hab_sub (hy : 0 < y) (a b : ℂ) (x : ℝ) :
    hab y a (b + 1) x - hab y (a + 1) b x = 2 * I * y * hab y (a + 1) (b + 1) x := by
  rw [← plus_mul_hab hy a (b + 1) x, ← minus_mul_hab hy (a + 1) b x]; ring

theorem fourier_zero_eq_integral (f : ℝ → ℂ) : 𝓕 f 0 = ∫ x, f x := by
  simp [Real.fourier_real_eq]

theorem re_add_one_add {a b : ℂ} (h : 1 < (a + b).re) : 1 < (a + 1 + b).re := by
  simp; simp at h; linarith

theorem re_add_add_one {a b : ℂ} (h : 1 < (a + b).re) : 1 < (a + (b + 1)).re := by
  simp; simp at h; linarith

/-- `a ∫h_{a+1,b} + b ∫h_{a,b+1} = 0`. -/
theorem integral_hab_R1 (hy : 0 < y) {a b : ℂ} (h : 1 < (a + b).re) :
    a * (∫ x, hab y (a + 1) b x) + b * (∫ x, hab y a (b + 1) x) = 0 := by
  have := fourier_hab_rec hy h 0
  rw [fourier_zero_eq_integral, fourier_zero_eq_integral, fourier_zero_eq_integral] at this
  simp only [Complex.ofReal_zero, mul_zero, zero_mul] at this
  set B := ∫ x, hab y (a + 1) b x
  set C := ∫ x, hab y a (b + 1) x
  linear_combination this

/-- `x h_{a,b}(x) → 0` as `|x| → ∞`, for `Re(a+b) > 1`. -/
theorem norm_mul_hab_le (hy : 0 < y) (a b : ℂ) (x : ℝ) :
    ‖(x : ℂ) * hab y a b x‖ ≤ Real.exp (Real.pi * (|a.im| + |b.im|)) *
      (x ^ 2 + y ^ 2) ^ ((1 - (a + b).re) / 2) := by
  have hpos : 0 < x ^ 2 + y ^ 2 := by positivity
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hx : |x| ≤ (x ^ 2 + y ^ 2) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith)
  calc |x| * ‖hab y a b x‖ ≤ (x ^ 2 + y ^ 2) ^ (1 / 2 : ℝ) *
        (Real.exp (Real.pi * (|a.im| + |b.im|)) * (x ^ 2 + y ^ 2) ^ (-(a + b).re / 2)) :=
        mul_le_mul hx (norm_hab_le hy a b x) (norm_nonneg _) (by positivity)
    _ = _ := by
        rw [mul_left_comm, ← Real.rpow_add hpos]; congr 2; ring

theorem tendsto_mul_hab (hy : 0 < y) {a b : ℂ} (h : 1 < (a + b).re) (l : Filter ℝ)
    (hl : Tendsto (fun x : ℝ => x ^ 2 + y ^ 2) l atTop) :
    Tendsto (fun x : ℝ => (x : ℂ) * hab y a b x) l (𝓝 0) := by
  have h0 : Tendsto (fun x : ℝ => Real.exp (Real.pi * (|a.im| + |b.im|)) *
      (x ^ 2 + y ^ 2) ^ ((1 - (a + b).re) / 2)) l (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (show 0 < ((a + b).re - 1) / 2 by linarith)).comp hl
    have := this.const_mul (Real.exp (Real.pi * (|a.im| + |b.im|)))
    rw [mul_zero] at this
    refine this.congr fun x => ?_
    simp only [Function.comp]; congr 2; ring
  exact squeeze_zero_norm (norm_mul_hab_le hy a b) h0

theorem tendsto_sq_add_atTop (y : ℝ) :
    Tendsto (fun x : ℝ => x ^ 2 + y ^ 2) atTop atTop := by
  refine tendsto_atTop_add_const_right _ _ ?_
  exact (tendsto_pow_atTop two_ne_zero)

theorem tendsto_sq_add_atBot (y : ℝ) :
    Tendsto (fun x : ℝ => x ^ 2 + y ^ 2) atBot atTop := by
  refine tendsto_atTop_add_const_right _ _ ?_
  exact (tendsto_pow_atTop two_ne_zero).comp tendsto_neg_atBot_atTop |>.congr (fun x => by simp)

/-- `(1-a-b) ∫h_{a,b} = -iay ∫h_{a+1,b} + iby ∫h_{a,b+1}` (integrate `(x h_{a,b})'`). -/
theorem integral_hab_R3 (hy : 0 < y) {a b : ℂ} (h : 1 < (a + b).re) :
    (1 - a - b) * (∫ x, hab y a b x) =
      -(I * a * y) * (∫ x, hab y (a + 1) b x) + I * b * y * (∫ x, hab y a (b + 1) x) := by
  have hint := integrable_hab hy h
  have hint1 := integrable_hab hy (re_add_one_add h)
  have hint2 := integrable_hab hy (re_add_add_one h)
  have hd : ∀ x : ℝ, HasDerivAt (fun t : ℝ => (t : ℂ) * hab y a b t)
      ((1 - a - b) * hab y a b x + I * a * y * hab y (a + 1) b x -
        I * b * y * hab y a (b + 1) x) x := by
    intro x
    have h1 := ((hasDerivAt_id x).ofReal_comp).mul (hasDerivAt_hab hy a b x)
    refine h1.congr_deriv ?_
    have e1 := plus_mul_hab hy a b x
    have e2 := minus_mul_hab hy a b x
    simp only [id, Complex.ofReal_one]
    linear_combination (-a) * e1 - b * e2
  have hI := integral_of_hasDerivAt_of_tendsto hd
    (((hint.const_mul _).add (hint1.const_mul _)).sub (hint2.const_mul _))
    (tendsto_mul_hab hy h atBot (tendsto_sq_add_atBot y))
    (tendsto_mul_hab hy h atTop (tendsto_sq_add_atTop y))
  have e1 := integral_sub (f := fun x => (1 - a - b) * hab y a b x + I * a * y * hab y (a + 1) b x)
    (g := fun x => I * b * y * hab y a (b + 1) x) ((hint.const_mul _).add (hint1.const_mul _))
    (hint2.const_mul _)
  have e2 := integral_add (f := fun x => (1 - a - b) * hab y a b x)
    (g := fun x => I * a * y * hab y (a + 1) b x) (hint.const_mul _) (hint1.const_mul _)
  rw [e1, e2, integral_const_mul, integral_const_mul, integral_const_mul, sub_zero] at hI
  set A := ∫ x, hab y a b x
  set B := ∫ x, hab y (a + 1) b x
  set C := ∫ x, hab y a (b + 1) x
  linear_combination hI

/-- **The constant-term recursion**:
`(a+b)(a+b-1) ∫h_{a,b} = 4ab y² ∫h_{a+1,b+1}` for `Re(a+b) > 1`. -/
theorem integral_hab_rec (hy : 0 < y) {a b : ℂ} (h : 1 < (a + b).re) :
    (a + b) * (a + b - 1) * (∫ x, hab y a b x) =
      4 * a * b * (y : ℂ) ^ 2 * (∫ x, hab y (a + 1) (b + 1) x) := by
  have R1 := integral_hab_R1 hy h
  have R3 := integral_hab_R3 hy h
  have hint1 := integrable_hab hy (re_add_one_add h)
  have hint2 := integrable_hab hy (re_add_add_one h)
  have R2 : (∫ x, hab y a (b + 1) x) - (∫ x, hab y (a + 1) b x) =
      2 * I * y * (∫ x, hab y (a + 1) (b + 1) x) := by
    rw [← integral_sub hint2 hint1, ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun x => hab_sub hy a b x)
  set A := ∫ x, hab y a b x
  set B := ∫ x, hab y (a + 1) b x
  set C := ∫ x, hab y a (b + 1) x
  set D := ∫ x, hab y (a + 1) (b + 1) x
  linear_combination (-(a + b)) * R3 + (I * y * (a - b)) * R1 - (2 * I * y * a * b) * R2
    - (4 * a * b * (y : ℂ) ^ 2 * D) * Complex.I_sq


/-! ### Scaling in `y` -/

theorem hab_scale (hy : 0 < y) (a b : ℂ) (t : ℝ) :
    hab y a b (y * t) = (y : ℂ) ^ (-a - b) * hab 1 a b t := by
  unfold hab
  have hp : (((y * t : ℝ) : ℂ) + y * I) = ((t : ℂ) + ((1 : ℝ) : ℂ) * I) * (y : ℝ) := by
    push_cast; ring
  have hm : (((y * t : ℝ) : ℂ) - y * I) = ((t : ℂ) - ((1 : ℝ) : ℂ) * I) * (y : ℝ) := by
    push_cast; ring
  rw [hp, hm, cpow_mul_ofReal_pos (plus_ne_zero one_pos t) hy,
    cpow_mul_ofReal_pos (minus_ne_zero one_pos t) hy,
    show -a - b = -a + -b by ring, Complex.cpow_add _ _ (by exact_mod_cast hy.ne')]
  ring

theorem integral_hab_scale (hy : 0 < y) (a b : ℂ) :
    ∫ x, hab y a b x = (y : ℂ) ^ (1 - a - b) * ∫ t, hab 1 a b t := by
  have h := Measure.integral_comp_mul_left (hab y a b) y
  simp_rw [hab_scale hy] at h
  rw [integral_const_mul, abs_inv, abs_of_pos hy, Complex.real_smul] at h
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have e : (y : ℂ) ^ (1 - a - b) = (y : ℂ) * (y : ℂ) ^ (-a - b) := by
    rw [show (1 : ℂ) - a - b = 1 + (-a - b) by ring, Complex.cpow_add _ _ hy0, Complex.cpow_one]
  rw [e, mul_assoc, h, Complex.ofReal_inv]
  field_simp


/-! ### The continued constant-term transform -/

/-- `J_0(a,b) = ∫h_{a,b}` and `J_{k+1}(a,b) = 4ab y² J_k(a+1,b+1)`. -/
def JN (y : ℝ) : ℕ → ℂ → ℂ → ℂ
  | 0, a, b => ∫ x, hab y a b x
  | k + 1, a, b => 4 * a * b * (y : ℂ) ^ 2 * JN y k (a + 1) (b + 1)

/-- `P_k(s) = ∏_{j<k} (s+2j)(s+2j-1)`. -/
def Pk : ℕ → ℂ → ℂ
  | 0, _ => 1
  | k + 1, s => s * (s - 1) * Pk k (s + 2)

theorem JN_zero (a b : ℂ) : JN y 0 a b = ∫ x, hab y a b x := rfl

theorem JN_succ (k : ℕ) (a b : ℂ) :
    JN y (k + 1) a b = 4 * a * b * (y : ℂ) ^ 2 * JN y k (a + 1) (b + 1) := rfl

theorem Pk_succ (k : ℕ) (s : ℂ) : Pk (k + 1) s = s * (s - 1) * Pk k (s + 2) := rfl

/-- On the region of convergence, `P_k(a+b) ∫h_{a,b} = J_k(a,b)`. -/
theorem JN_eq (hy : 0 < y) (k : ℕ) :
    ∀ a b : ℂ, 1 < (a + b).re → Pk k (a + b) * (∫ x, hab y a b x) = JN y k a b := by
  induction k with
  | zero => intro a b _; simp [Pk, JN_zero]
  | succ k ih =>
    intro a b h
    have h2 : 1 < (a + 1 + (b + 1)).re := by simp; simp at h; linarith
    rw [Pk_succ, JN_succ, ← ih (a + 1) (b + 1) h2, show a + 1 + (b + 1) = a + b + 2 by ring]
    have := integral_hab_rec hy h
    set A := ∫ x, hab y a b x
    set D := ∫ x, hab y (a + 1) (b + 1) x
    linear_combination Pk k (a + b + 2) * this

/-- `J_{k+m}(a,b) = P_m(a+b+2k) J_k(a,b)` wherever `Re(a+b) + 2k > 1`. -/
theorem JN_add (hy : 0 < y) (m k : ℕ) :
    ∀ a b : ℂ, 1 < (a + b).re + 2 * k → JN y (k + m) a b = Pk m (a + b + 2 * k) * JN y k a b := by
  induction k with
  | zero =>
    intro a b h
    simp only [Nat.cast_zero, mul_zero, add_zero, zero_add] at h ⊢
    rw [JN_zero, JN_eq hy m a b h]
  | succ k ih =>
    intro a b h
    have h2 : 1 < (a + 1 + (b + 1)).re + 2 * k := by
      simp; push_cast at h; simp at h; linarith
    rw [show k + 1 + m = (k + m) + 1 by ring, JN_succ, JN_succ, ih (a + 1) (b + 1) h2]
    push_cast
    rw [show a + 1 + (b + 1) + 2 * (k : ℂ) = a + b + 2 * (k + 1) by ring]
    ring

/-- `J_k` scales exactly: `J_k^{(y)}(a,b) = y^{1-a-b} J_k^{(1)}(a,b)`. -/
theorem JN_scale (hy : 0 < y) (k : ℕ) :
    ∀ a b : ℂ, JN y k a b = (y : ℂ) ^ (1 - a - b) * JN 1 k a b := by
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  induction k with
  | zero => intro a b; exact integral_hab_scale hy a b
  | succ k ih =>
    intro a b
    rw [JN_succ, JN_succ, ih]
    have e : (y : ℂ) ^ (1 - a - b) = (y : ℂ) ^ 2 * (y : ℂ) ^ (1 - (a + 1) - (b + 1)) := by
      rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ hy0]
      congr 1; push_cast; ring
    rw [e]; push_cast; ring

/-- Holomorphy of `w ↦ J_k(w+α, w+β)` on `Re(2w+α+β) + 2k > 1`. -/
theorem differentiableAt_JN (hy : 0 < y) (k : ℕ) :
    ∀ (α β w₀ : ℂ), 1 < (2 * w₀ + α + β).re + 2 * k →
      DifferentiableAt ℂ (fun w => JN y k (w + α) (w + β)) w₀ := by
  induction k with
  | zero =>
    intro α β w₀ h
    simp only [Nat.cast_zero, mul_zero, add_zero] at h
    simp only [JN_zero, ← fourier_zero_eq_integral]
    exact differentiableAt_fourier_hab hy α β 0 h
  | succ k ih =>
    intro α β w₀ h
    push_cast at h
    have h1 := ih (α + 1) (β + 1) w₀ (by simp; simp at h; linarith)
    have e : (fun w => JN y k (w + α + 1) (w + β + 1)) = fun w => JN y k (w + (α + 1)) (w + (β + 1)) := by
      funext w; congr 1 <;> ring
    simp only [JN_succ]
    refine (((differentiableAt_const _).mul (differentiableAt_id.add_const α)).mul
      (differentiableAt_id.add_const β)).mul_const _ |>.mul ?_
    rw [e]; exact h1


/-! ### The constant term of the kernel -/

/-- The continued constant-term coefficient `c_k(w) = J_k^{(1)}(w+1/4, w-1/4)`. -/
def cK (k : ℕ) (w : ℂ) : ℂ := JN 1 k (w + 1 / 4) (w - 1 / 4)

theorem add_quarter_add_sub (w : ℂ) : w + 1 / 4 + (w - 1 / 4) = 2 * w := by ring

/-- **The constant term of the kernel**: for `Re w > 1/2` and every `k`,
`P_k(2w) ∫ kerH_{y,w} = y^{1-w} c_k(w)`. -/
theorem integral_kerH_eq (hy : 0 < y) (k : ℕ) {w : ℂ} (hw : 1 / 2 < w.re) :
    Pk k (2 * w) * (∫ x, kerH y w x) = (y : ℂ) ^ (1 - w) * cK k w := by
  have hre : 1 < (w + 1 / 4 + (w - 1 / 4)).re := by simp; linarith
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  simp_rw [kerH_eq_hab hy w]
  rw [integral_const_mul, mul_left_comm, ← add_quarter_add_sub, JN_eq hy k _ _ hre,
    JN_scale hy, cK, ← mul_assoc, ← Complex.cpow_add _ _ hy0]
  congr 2; ring

theorem differentiableAt_cK (k : ℕ) {w₀ : ℂ} (h : 1 < 2 * w₀.re + 2 * k) :
    DifferentiableAt ℂ (cK k) w₀ := by
  have := differentiableAt_JN one_pos k (1 / 4) (-(1 / 4)) w₀ (by simp; linarith)
  have e : cK k = fun w => JN 1 k (w + 1 / 4) (w + -(1 / 4)) := by
    funext w; simp only [cK, sub_eq_add_neg]
  rw [e]; exact this

/-- Compatibility: `c_{k+m}(w) = P_m(2w+2k) c_k(w)` on `Re w > 1/2 - k`. -/
theorem cK_add (m k : ℕ) {w : ℂ} (h : 1 < 2 * w.re + 2 * k) :
    cK (k + m) w = Pk m (2 * w + 2 * k) * cK k w := by
  unfold cK
  rw [JN_add one_pos m k _ _ (by simp; linarith), add_quarter_add_sub]

/-- `P_1(2w) = 2w(2w-1)`: the only factor vanishing on `Re w > -1/2` besides `w = 0` is `w = 1/2`. -/
theorem Pk_one (s : ℂ) : Pk 1 s = s * (s - 1) := by simp [Pk]
