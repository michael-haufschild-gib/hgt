import GaloisForLFunctions.RHTower.WeilMarginSuperexponentialLaw
import GaloisForLFunctions.RHTower.MaassZetaSquaredConverseWide
import GaloisForLFunctions.RHTower.STCFlatGapMeasureReaderNoGo

/-!
# The transform with kernel `Φ ⋆ Φ` is injective

Let `Φ` be Riemann's kernel, `ξ(s) = ∫ Φ(x) e^{(s−½)x} dx`, and let `K = Φ ⋆ Φ`
(`sqKernel`), so that `∫ K(y) e^{(s−½)y} dy = ξ(s)²`.  For weights `w` with
`Σ |w(n)| n^{−σ} < ∞` for every `σ > 3/2`, put `c(n) = w(n)/√n` and

`S₊(y) = Σ_n c(n) K(y + log n)`,  `S₋(y) = Σ_n c(n) K(y − log n)`.

**Theorem** (`eq_zero_of_sqKernelTransform_eq_zero`).  If `S₋(y) + S₊(y) = 0` for every real `y`,
then `w(n) = 0` for every `n ≥ 1`.  In coefficient form
(`eq_zero_of_sqKernel_coeffTransform_eq_zero`): `Σ_{n≥1} u(n)(K(y − log n) + K(y + log n)) ≡ 0`
with `Σ |u(n)| n^{−τ} < ∞` for every `τ > 1`, e.g. `u(n) = O(log n)`, forces `u = 0`.

Dually, since the Fourier transform of `K` is `Ξ²`, a tempered distribution supported on the
real zeros of `Ξ`, of order at most one at every simple zero (atoms and dipoles), whose Fourier
transform is carried by `±log n` with weights `w(n) n^{−½}`, vanishes.  The atomic case is the
injectivity of the transform with kernel `Φ` (`eq_zero_of_riemannKernelTransform_eq_zero_of_sq`).
The degree matters: the same argument with `K₃ = Φ ⋆ Φ ⋆ Φ` would need an odd degree-three
converse theorem, and odd degree-three functional equations have nonzero solutions.

**Proof.**
* `S₊` decays faster than every exponential as `y → +∞`, and `S₋` does so as `y → −∞`.  The
  hypothesis `S₊ = −S₋` therefore makes `S₊` decay in both directions, so
  `H(s) = ∫ S₊(y) e^{(s−½)y} dy` is entire and bounded on every vertical strip.
* `K` is even, so `S₊(−y) = S₋(y) = −S₊(y)`, and `H(1 − s) = −H(s)`.
* On `Re s > 3/2`, termwise integration gives `H(s) = ξ(s)² Σ w(n) n^{−s}`, which equals
  `s²(s−1)²Γ_ℝ(s)² L(g, s)` with `g = ¼ (d ⋆ w)`, `d` the divisor function.
* The odd converse theorem for `ζ²` at abscissa `3/2`
  (`coeff_eq_zero_of_odd_functional_equation_wide`) gives `g = 0`, hence `Σ w(n) n^{−s} = 0` on
  `Re s > 3/2`, hence `w = 0`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace RHTower

namespace RiemannSquareKernel

noncomputable section

local notation "Φ" => riemannPhiKernel

/-! ## The kernel `K = Φ ⋆ Φ` -/

/-- The self-convolution `K = Φ ⋆ Φ` of Riemann's kernel. -/
def sqKernel : ℝ → ℂ := convolution Φ Φ (ContinuousLinearMap.mul ℝ ℂ) volume

theorem sqKernel_apply (y : ℝ) : sqKernel y = ∫ t : ℝ, Φ t * Φ (y - t) := by
  simp [sqKernel, convolution_def]

theorem exists_norm_riemannPhiKernel_le_const : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖Φ x‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_riemannPhiKernel_le_exp (B := 0) le_rfl
  exact ⟨C, hC0, fun x => by simpa using hC x⟩

/-- `K` decays faster than every exponential. -/
theorem exists_norm_sqKernel_le {B : ℝ} (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, ‖sqKernel y‖ ≤ C * Real.exp (-(B * |y|)) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_riemannPhiKernel_le_exp (B := B + 1) (by positivity)
  have hint := integrable_exp_neg_mul_abs_modSource (a := 1) one_pos
  set M : ℝ := ∫ t : ℝ, Real.exp (-1 * |t|) with hM
  have hM0 : 0 ≤ M := integral_nonneg fun t => (Real.exp_pos _).le
  refine ⟨C ^ 2 * M, by positivity, fun y => ?_⟩
  rw [sqKernel_apply]
  have hbound : ∀ t : ℝ, ‖Φ t * Φ (y - t)‖ ≤
      C ^ 2 * Real.exp (-(B * |y|)) * Real.exp (-1 * |t|) := by
    intro t
    rw [norm_mul]
    have h1 := hC t
    have h2 := hC (y - t)
    have htri : |y| ≤ |t| + |y - t| := by
      calc |y| = |t + (y - t)| := by ring_nf
        _ ≤ |t| + |y - t| := abs_add_le _ _
    have hexp : Real.exp (-((B + 1) * |t|)) * Real.exp (-((B + 1) * |y - t|)) ≤
        Real.exp (-(B * |y|)) * Real.exp (-1 * |t|) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [abs_nonneg (y - t), abs_nonneg t]
    calc ‖Φ t‖ * ‖Φ (y - t)‖
        ≤ (C * Real.exp (-((B + 1) * |t|))) * (C * Real.exp (-((B + 1) * |y - t|))) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = C ^ 2 * (Real.exp (-((B + 1) * |t|)) * Real.exp (-((B + 1) * |y - t|))) := by ring
      _ ≤ C ^ 2 * (Real.exp (-(B * |y|)) * Real.exp (-1 * |t|)) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = C ^ 2 * Real.exp (-(B * |y|)) * Real.exp (-1 * |t|) := by ring
  calc ‖∫ t : ℝ, Φ t * Φ (y - t)‖
      ≤ ∫ t : ℝ, C ^ 2 * Real.exp (-(B * |y|)) * Real.exp (-1 * |t|) :=
        norm_integral_le_of_norm_le (hint.const_mul _) (Eventually.of_forall hbound)
    _ = C ^ 2 * M * Real.exp (-(B * |y|)) := by
        rw [integral_const_mul, hM]; ring

theorem continuous_sqKernel : Continuous sqKernel := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := exists_norm_riemannPhiKernel_le_const
  have hcont : Continuous fun y : ℝ => ∫ t : ℝ, Φ t * Φ (y - t) := by
    refine continuous_of_dominated (bound := fun t => ‖Φ t‖ * C₀)
      (fun y => (continuous_riemannPhiKernel.mul
        (continuous_riemannPhiKernel.comp (continuous_const.sub continuous_id))).aestronglyMeasurable)
      (fun y => Eventually.of_forall fun t => ?_) (integrable_riemannPhiKernel.norm.mul_const C₀)
      (Eventually.of_forall fun t =>
        continuous_const.mul (continuous_riemannPhiKernel.comp (continuous_id.sub continuous_const)))
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC₀ _) (norm_nonneg _)
  exact hcont.congr fun y => (sqKernel_apply y).symm

theorem sqKernel_neg (y : ℝ) : sqKernel (-y) = sqKernel y := by
  rw [sqKernel_apply, sqKernel_apply,
    ← integral_neg_eq_self (fun t : ℝ => Φ t * Φ (-y - t)) volume]
  congr 1
  funext t
  rw [riemannPhiKernel_neg, show -y - -t = -(y - t) by ring, riemannPhiKernel_neg]

/-! ## The Laplace transform of `K` -/

/-- `e^{zt} Φ(t)`. -/
def phiWeighted (z : ℂ) (t : ℝ) : ℂ := cexp ((t : ℂ) * z) * Φ t

theorem integrable_phiWeighted (z : ℂ) : Integrable (phiWeighted z) := by
  have h := integrable_norm_riemannPhiKernel_mul_exp (b := |z.re|) (abs_nonneg _)
  refine h.mono' ((Continuous.mul (by fun_prop) continuous_riemannPhiKernel).aestronglyMeasurable)
    (Eventually.of_forall fun t => ?_)
  rw [phiWeighted, norm_mul, Complex.norm_exp, mul_comm]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
  have : ((t : ℂ) * z).re = t * z.re := by simp [Complex.mul_re]
  rw [this]
  calc t * z.re ≤ |t * z.re| := le_abs_self _
    _ = |z.re| * |t| := by rw [abs_mul, mul_comm]

theorem integral_phiWeighted (z : ℂ) :
    ∫ t : ℝ, phiWeighted z t = riemannPhiTransform (z + 1 / 2) := by
  unfold phiWeighted riemannPhiTransform
  congr 1
  funext t
  congr 2
  ring

theorem convolution_phiWeighted (z : ℂ) (y : ℝ) :
    convolution (phiWeighted z) (phiWeighted z) (ContinuousLinearMap.mul ℝ ℂ) volume y =
      sqKernel y * cexp ((y : ℂ) * z) := by
  rw [convolution_def, sqKernel_apply, mul_comm, ← integral_const_mul]
  congr 1
  funext t
  simp only [ContinuousLinearMap.mul_apply', phiWeighted]
  have : cexp ((t : ℂ) * z) * cexp (((y - t : ℝ) : ℂ) * z) = cexp ((y : ℂ) * z) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  calc cexp ((t : ℂ) * z) * Φ t * (cexp (((y - t : ℝ) : ℂ) * z) * Φ (y - t))
      = (cexp ((t : ℂ) * z) * cexp (((y - t : ℝ) : ℂ) * z)) * (Φ t * Φ (y - t)) := by ring
    _ = cexp ((y : ℂ) * z) * (Φ t * Φ (y - t)) := by rw [this]

/-- `∫ K(y) e^{zy} dy = ξ(z + ½)²` for every complex `z`. -/
theorem integral_sqKernel_mul_cexp (z : ℂ) :
    ∫ y : ℝ, sqKernel y * cexp ((y : ℂ) * z) = riemannPhiTransform (z + 1 / 2) ^ 2 := by
  have h := integral_convolution (μ := volume) (ν := volume) (ContinuousLinearMap.mul ℝ ℂ)
    (integrable_phiWeighted z) (integrable_phiWeighted z)
  simp only [convolution_phiWeighted, ContinuousLinearMap.mul_apply',
    integral_phiWeighted] at h
  rw [h, sq]

theorem integrable_norm_sqKernel_mul_exp (b : ℝ) :
    Integrable fun y : ℝ => ‖sqKernel y‖ * Real.exp (b * |y|) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_sqKernel_le (B := |b| + 1) (by positivity)
  refine ((integrable_exp_neg_mul_abs_modSource (a := 1) one_pos).const_mul C).mono'
    ((continuous_sqKernel.norm.mul (by fun_prop)).aestronglyMeasurable)
    (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖sqKernel y‖ * Real.exp (b * |y|)
      ≤ C * Real.exp (-((|b| + 1) * |y|)) * Real.exp (b * |y|) :=
        mul_le_mul_of_nonneg_right (hC y) (Real.exp_pos _).le
    _ = C * Real.exp (-((|b| + 1) * |y|) + b * |y|) := by rw [mul_assoc, ← Real.exp_add]
    _ ≤ C * Real.exp (-1 * |y|) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC0
        nlinarith [le_abs_self b, abs_nonneg y]

/-! ## The coefficients and the two half sums -/

/-- `c(n) = w(n)/√n` (zero at `n = 0`). -/
def coef (w : ℕ → ℂ) (n : ℕ) : ℂ := w n / (Real.sqrt n : ℂ)

theorem norm_coef (w : ℕ → ℂ) (n : ℕ) : ‖coef w n‖ = ‖w n‖ * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [coef]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [coef, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sqrt_eq_rpow, Real.rpow_neg hn0.le, div_eq_mul_inv]

/-- `S₊(y) = Σ c(n) K(y + log n)`. -/
def sPlus (w : ℕ → ℂ) (y : ℝ) : ℂ := ∑' n : ℕ, coef w n * sqKernel (y + Real.log n)

/-- `S₋(y) = Σ c(n) K(y − log n)`. -/
def sMinus (w : ℕ → ℂ) (y : ℝ) : ℂ := ∑' n : ℕ, coef w n * sqKernel (y - Real.log n)

theorem exp_neg_mul_log (B : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    Real.exp (-(B * Real.log n)) = (n : ℝ) ^ (-B) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.rpow_def_of_pos hn0]; ring_nf

/-- The term bound `‖c(n)K(x)‖ ≤ C‖w(n)‖n^{−½}e^{−B|x|}`. -/
theorem norm_coef_mul_sqKernel_le (w : ℕ → ℂ) {B C : ℝ} (hC : ∀ y : ℝ, ‖sqKernel y‖ ≤
    C * Real.exp (-(B * |y|))) (n : ℕ) (x : ℝ) :
    ‖coef w n * sqKernel x‖ ≤ C * (‖w n‖ * (n : ℝ) ^ (-(1 / 2 : ℝ))) * Real.exp (-(B * |x|)) := by
  rw [norm_mul, norm_coef]
  have h0 : 0 ≤ ‖w n‖ * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
  calc ‖w n‖ * (n : ℝ) ^ (-(1 / 2 : ℝ)) * ‖sqKernel x‖
      ≤ ‖w n‖ * (n : ℝ) ^ (-(1 / 2 : ℝ)) * (C * Real.exp (-(B * |x|))) :=
        mul_le_mul_of_nonneg_left (hC x) h0
    _ = C * (‖w n‖ * (n : ℝ) ^ (-(1 / 2 : ℝ))) * Real.exp (-(B * |x|)) := by ring

/-- `‖w(n)‖n^{−½}e^{−B|y ± log n|} ≤ e^{B|y|}‖w(n)‖n^{−(B+½)}`. -/
theorem weight_mul_exp_le (w : ℕ → ℂ) {B : ℝ} (hB : 0 ≤ B) (n : ℕ) (y : ℝ) {x : ℝ}
    (hx : Real.log n - |y| ≤ |x|) :
    ‖w n‖ * (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (-(B * |x|)) ≤
      Real.exp (B * |y|) * (‖w n‖ * (n : ℝ) ^ (-(B + 1 / 2))) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp; positivity
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hsplit : (n : ℝ) ^ (-(B + 1 / 2)) = (n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-B) := by
    rw [← Real.rpow_add hn0]; ring_nf
  rw [hsplit, ← exp_neg_mul_log B hn]
  have hexp : Real.exp (-(B * |x|)) ≤ Real.exp (B * |y|) * Real.exp (-(B * Real.log n)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have h0 : 0 ≤ ‖w n‖ * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
  calc ‖w n‖ * (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (-(B * |x|))
      ≤ ‖w n‖ * (n : ℝ) ^ (-(1 / 2 : ℝ)) * (Real.exp (B * |y|) * Real.exp (-(B * Real.log n))) :=
        mul_le_mul_of_nonneg_left hexp h0
    _ = _ := by ring

theorem log_sub_abs_le_abs_add (n : ℕ) (y : ℝ) : Real.log n - |y| ≤ |y + Real.log n| := by
  have := neg_abs_le y
  have := le_abs_self (y + Real.log n)
  linarith

theorem log_sub_abs_le_abs_sub (n : ℕ) (y : ℝ) : Real.log n - |y| ≤ |y - Real.log n| := by
  have := le_abs_self y
  have := neg_abs_le (y - Real.log n)
  linarith

section Weights

variable {w : ℕ → ℂ} (hw : ∀ σ : ℝ, 3 / 2 < σ → Summable fun n : ℕ => ‖w n‖ * (n : ℝ) ^ (-σ))
include hw

theorem summable_weight {B : ℝ} (hB : 1 < B) :
    Summable fun n : ℕ => ‖w n‖ * (n : ℝ) ^ (-(B + 1 / 2)) :=
  hw (B + 1 / 2) (by linarith)

/-- Summability of the half sums, with a bound uniform in `|y| ≤ R`. -/
theorem summable_coef_mul_sqKernel (y : ℝ) (sgn : ℝ) (hsgn : sgn = 1 ∨ sgn = -1) :
    Summable fun n : ℕ => coef w n * sqKernel (y + sgn * Real.log n) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_sqKernel_le (B := 2) zero_le_two
  refine Summable.of_norm_bounded (g := fun n => C * (Real.exp (2 * |y|) *
    (‖w n‖ * (n : ℝ) ^ (-(2 + 1 / 2))))) (((summable_weight hw (B := 2)
      (by norm_num)).mul_left _).mul_left _) (fun n => ?_)
  refine (norm_coef_mul_sqKernel_le w hC n _).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left (weight_mul_exp_le w zero_le_two n y ?_) hC0
  rcases hsgn with rfl | rfl
  · simpa using log_sub_abs_le_abs_add n y
  · simpa [sub_eq_add_neg] using log_sub_abs_le_abs_sub n y

theorem continuous_sPlus : Continuous (sPlus w) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_sqKernel_le (B := 2) zero_le_two
  refine continuous_iff_continuousAt.mpr fun y₀ => ?_
  set R : ℝ := |y₀| + 1
  have hcont : ContinuousOn (sPlus w) (Ioo (-R) R) := by
    refine continuousOn_tsum (u := fun n => C * (Real.exp (2 * R) *
      (‖w n‖ * (n : ℝ) ^ (-(2 + 1 / 2))))) (fun n => (continuous_const.mul
        (continuous_sqKernel.comp (continuous_id.add continuous_const))).continuousOn)
      (((summable_weight hw (B := 2) (by norm_num)).mul_left _).mul_left _) (fun n y hy => ?_)
    refine (norm_coef_mul_sqKernel_le w hC n _).trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ((weight_mul_exp_le w zero_le_two n y
      (log_sub_abs_le_abs_add n y)).trans ?_) hC0
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (by positivity)
    have := abs_lt.mpr hy
    linarith
  exact hcont.continuousAt (Ioo_mem_nhds (by linarith [abs_nonneg y₀, neg_abs_le y₀])
    (by linarith [le_abs_self y₀]))

/-- For `y ≥ 0`, `‖S₊(y)‖ ≤ C_B T_B e^{−By}`. -/
theorem norm_sPlus_le_of_nonneg {B : ℝ} (hB : 1 < B) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ y : ℝ, ‖sqKernel y‖ ≤ C * Real.exp (-(B * |y|))) {y : ℝ} (hy : 0 ≤ y) :
    ‖sPlus w y‖ ≤ C * (∑' n : ℕ, ‖w n‖ * (n : ℝ) ^ (-(B + 1 / 2))) * Real.exp (-(B * |y|)) := by
  have hB0 : 0 ≤ B := by linarith
  have hS := summable_weight hw hB
  have hterm : ∀ n : ℕ, ‖coef w n * sqKernel (y + Real.log n)‖ ≤
      C * Real.exp (-(B * |y|)) * (‖w n‖ * (n : ℝ) ^ (-(B + 1 / 2))) := by
    intro n
    refine (norm_coef_mul_sqKernel_le w hC n _).trans ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp; positivity
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
    have habs : |y + Real.log n| = |y| + Real.log n := by
      rw [abs_of_nonneg (by linarith), abs_of_nonneg hy]
    have hsplit : (n : ℝ) ^ (-(B + 1 / 2)) = (n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-B) := by
      rw [← Real.rpow_add hn0]; ring_nf
    rw [habs, hsplit, ← exp_neg_mul_log B hn,
      show -(B * (|y| + Real.log n)) = -(B * |y|) + -(B * Real.log n) by ring, Real.exp_add]
    ring_nf; rfl
  calc ‖sPlus w y‖ ≤ ∑' n : ℕ, ‖coef w n * sqKernel (y + Real.log n)‖ :=
        norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm
          (hS.mul_left _))
    _ ≤ ∑' n : ℕ, C * Real.exp (-(B * |y|)) * (‖w n‖ * (n : ℝ) ^ (-(B + 1 / 2))) :=
        Summable.tsum_le_tsum hterm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm
          (hS.mul_left _)) (hS.mul_left _)
    _ = _ := by rw [tsum_mul_left]; ring

/-- For `y ≤ 0`, `‖S₋(y)‖ ≤ C_B T_B e^{−B|y|}`. -/
theorem norm_sMinus_le_of_nonpos {B : ℝ} (hB : 1 < B) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ y : ℝ, ‖sqKernel y‖ ≤ C * Real.exp (-(B * |y|))) {y : ℝ} (hy : y ≤ 0) :
    ‖sMinus w y‖ ≤ C * (∑' n : ℕ, ‖w n‖ * (n : ℝ) ^ (-(B + 1 / 2))) * Real.exp (-(B * |y|)) := by
  have hS := summable_weight hw hB
  have hterm : ∀ n : ℕ, ‖coef w n * sqKernel (y - Real.log n)‖ ≤
      C * Real.exp (-(B * |y|)) * (‖w n‖ * (n : ℝ) ^ (-(B + 1 / 2))) := by
    intro n
    refine (norm_coef_mul_sqKernel_le w hC n _).trans ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp; positivity
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
    have habs : |y - Real.log n| = |y| + Real.log n := by
      rw [abs_of_nonpos (by linarith), abs_of_nonpos hy]; ring
    have hsplit : (n : ℝ) ^ (-(B + 1 / 2)) = (n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-B) := by
      rw [← Real.rpow_add hn0]; ring_nf
    rw [habs, hsplit, ← exp_neg_mul_log B hn,
      show -(B * (|y| + Real.log n)) = -(B * |y|) + -(B * Real.log n) by ring, Real.exp_add]
    ring_nf; rfl
  calc ‖sMinus w y‖ ≤ ∑' n : ℕ, ‖coef w n * sqKernel (y - Real.log n)‖ :=
        norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm
          (hS.mul_left _))
    _ ≤ ∑' n : ℕ, C * Real.exp (-(B * |y|)) * (‖w n‖ * (n : ℝ) ^ (-(B + 1 / 2))) :=
        Summable.tsum_le_tsum hterm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm
          (hS.mul_left _)) (hS.mul_left _)
    _ = _ := by rw [tsum_mul_left]; ring

/-- Under `S₋ + S₊ = 0`, `S₊` decays faster than every exponential in both directions. -/
theorem exists_norm_sPlus_le (hzero : ∀ y : ℝ, sMinus w y + sPlus w y = 0) {B : ℝ}
    (hB : 1 < B) : ∃ D : ℝ, 0 ≤ D ∧ ∀ y : ℝ, ‖sPlus w y‖ ≤ D * Real.exp (-(B * |y|)) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_sqKernel_le (B := B) (by linarith)
  have hT : 0 ≤ ∑' n : ℕ, ‖w n‖ * (n : ℝ) ^ (-(B + 1 / 2)) :=
    tsum_nonneg fun n => by positivity
  refine ⟨C * ∑' n : ℕ, ‖w n‖ * (n : ℝ) ^ (-(B + 1 / 2)), by positivity, fun y => ?_⟩
  rcases le_total 0 y with hy | hy
  · exact norm_sPlus_le_of_nonneg hw hB hC0 hC hy
  · have heq : sPlus w y = -sMinus w y := by linear_combination hzero y
    rw [heq, norm_neg]
    exact norm_sMinus_le_of_nonpos hw hB hC0 hC hy

end Weights


/-! ## The transform `H` -/

/-- `G_z(v) = K(v) e^{vz}`. -/
def kernelWeighted (z : ℂ) (v : ℝ) : ℂ := sqKernel v * cexp ((v : ℂ) * z)

theorem norm_cexp_ofReal_mul_le (u : ℝ) (z : ℂ) :
    ‖cexp ((u : ℂ) * z)‖ ≤ Real.exp (|z.re| * |u|) := by
  rw [Complex.norm_exp]
  refine Real.exp_le_exp.mpr ?_
  have : ((u : ℂ) * z).re = u * z.re := by simp [Complex.mul_re]
  rw [this]
  calc u * z.re ≤ |u * z.re| := le_abs_self _
    _ = |z.re| * |u| := by rw [abs_mul, mul_comm]

theorem integrable_kernelWeighted (z : ℂ) : Integrable (kernelWeighted z) := by
  refine (integrable_norm_sqKernel_mul_exp |z.re|).mono'
    ((continuous_sqKernel.mul (by fun_prop)).aestronglyMeasurable)
    (Eventually.of_forall fun v => ?_)
  rw [kernelWeighted, norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_cexp_ofReal_mul_le v z) (norm_nonneg _)

theorem integral_kernelWeighted (z : ℂ) :
    ∫ v : ℝ, kernelWeighted z v = riemannPhiTransform (z + 1 / 2) ^ 2 :=
  integral_sqKernel_mul_cexp z

/-- `coef(n) e^{−(log n)z} = term(w, z + ½, n)`. -/
theorem coef_mul_cexp_eq_term (w : ℕ → ℂ) (z : ℂ) (n : ℕ) :
    coef w n * cexp (-((Real.log n : ℂ) * z)) = LSeries.term w (z + 1 / 2) n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [coef]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hne : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [LSeries.term_of_ne_zero hn.ne', coef, Complex.cpow_def_of_ne_zero hne]
  have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log hn0.le]
  have hsqrt : ((Real.sqrt n : ℝ) : ℂ) = cexp ((Real.log n : ℂ) / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn0, Complex.ofReal_exp]
    congr 1; push_cast; ring
  rw [hlog, hsqrt, div_eq_mul_inv (w n), ← Complex.exp_neg, mul_assoc, ← Complex.exp_add,
    div_eq_mul_inv (w n), ← Complex.exp_neg]
  congr 2
  ring

section Transform

variable {w : ℕ → ℂ} (hw : ∀ σ : ℝ, 3 / 2 < σ → Summable fun n : ℕ => ‖w n‖ * (n : ℝ) ^ (-σ))
  (hzero : ∀ y : ℝ, sMinus w y + sPlus w y = 0)
include hw hzero

theorem integrable_norm_sPlus_mul_exp (c : ℝ) :
    Integrable fun u : ℝ => ‖sPlus w u‖ * Real.exp (c * |u|) := by
  obtain ⟨D, hD0, hD⟩ := exists_norm_sPlus_le hw hzero (B := |c| + 2)
    (by linarith [abs_nonneg c])
  refine ((integrable_exp_neg_mul_abs_modSource (a := 1) one_pos).const_mul D).mono'
    (((continuous_sPlus hw).norm.mul (by fun_prop)).aestronglyMeasurable)
    (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖sPlus w u‖ * Real.exp (c * |u|)
      ≤ D * Real.exp (-((|c| + 2) * |u|)) * Real.exp (c * |u|) :=
        mul_le_mul_of_nonneg_right (hD u) (Real.exp_pos _).le
    _ = D * Real.exp (-((|c| + 2) * |u|) + c * |u|) := by rw [mul_assoc, ← Real.exp_add]
    _ ≤ D * Real.exp (-1 * |u|) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hD0
        nlinarith [le_abs_self c, abs_nonneg u]

omit hw hzero in
theorem sPlus_neg (y : ℝ) : sPlus w (-y) = sMinus w y := by
  unfold sPlus sMinus
  congr 1
  funext n
  rw [show -y + Real.log n = -(y - Real.log n) by ring, sqKernel_neg]

end Transform

/-- `H(s) = ∫ S₊(y) e^{(s−½)y} dy`. -/
def bigH (w : ℕ → ℂ) (s : ℂ) : ℂ := spectralLaplace volume (sPlus w) (s - 1 / 2)

section TransformProps

variable {w : ℕ → ℂ} (hw : ∀ σ : ℝ, 3 / 2 < σ → Summable fun n : ℕ => ‖w n‖ * (n : ℝ) ^ (-σ))
  (hzero : ∀ y : ℝ, sMinus w y + sPlus w y = 0)
include hw hzero

theorem differentiable_bigH : Differentiable ℂ (bigH w) :=
  (differentiable_spectralLaplace (continuous_sPlus hw).aestronglyMeasurable
    (integrable_norm_sPlus_mul_exp hw hzero)).comp (differentiable_id.sub_const _)

omit hw in
theorem bigH_one_sub (s : ℂ) : bigH w (1 - s) = -bigH w s := by
  unfold bigH spectralLaplace
  rw [← integral_neg_eq_self (fun u : ℝ => sPlus w u * cexp ((u : ℂ) * (1 - s - 1 / 2))) volume,
    ← integral_neg]
  congr 1
  funext u
  rw [sPlus_neg, show sMinus w u = -sPlus w u by linear_combination hzero u]
  rw [show ((-u : ℝ) : ℂ) * (1 - s - 1 / 2) = (u : ℂ) * (s - 1 / 2) by push_cast; ring]
  ring

theorem exists_bound_bigH :
    ∃ M : ℝ, ∀ s : ℂ, -3 / 4 ≤ s.re → s.re ≤ 7 / 4 → ‖bigH w s‖ ≤ M := by
  refine ⟨∫ u : ℝ, ‖sPlus w u‖ * Real.exp (2 * |u|), fun s h1 h2 => ?_⟩
  unfold bigH spectralLaplace
  refine norm_integral_le_of_norm_le (integrable_norm_sPlus_mul_exp hw hzero 2)
    (Eventually.of_forall fun u => ?_)
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ((norm_cexp_ofReal_mul_le u _).trans
    (Real.exp_le_exp.mpr ?_)) (norm_nonneg _)
  have hre : (s - 1 / 2).re = s.re - 1 / 2 := by simp
  rw [hre]
  have habs : |s.re - 1 / 2| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  nlinarith [abs_nonneg u]

omit hzero in
/-- On `Re s > 3/2`, `H(s) = ξ(s)² Σ w(n) n^{−s}`. -/
theorem bigH_eq_of_three_halves_lt_re {s : ℂ} (hs : 3 / 2 < s.re) :
    bigH w s = riemannPhiTransform s ^ 2 * LSeries w s := by
  set z : ℂ := s - 1 / 2 with hz
  have hzre : z.re = s.re - 1 / 2 := by simp [hz]
  set F : ℕ → ℝ → ℂ := fun n u =>
    (coef w n * cexp (-((Real.log n : ℂ) * z))) * kernelWeighted z (u + Real.log n) with hF
  have hFint : ∀ n, Integrable (F n) := fun n =>
    ((integrable_kernelWeighted z).comp_add_right (Real.log n)).const_mul _
  have hFnorm : ∀ n, ∫ u : ℝ, ‖F n u‖ =
      ‖w n‖ * (n : ℝ) ^ (-s.re) * ∫ v : ℝ, ‖kernelWeighted z v‖ := by
    intro n
    simp only [hF, norm_mul]
    rw [integral_const_mul,
      integral_add_right_eq_self (fun v => ‖kernelWeighted z v‖) (Real.log n), norm_coef,
      Complex.norm_exp]
    congr 1
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [Real.zero_rpow (show -s.re ≠ 0 by linarith)]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hre : (-((Real.log n : ℂ) * z)).re = -(Real.log n * z.re) := by
      rw [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; ring
    rw [hre, hzre, Real.rpow_def_of_pos hn0, Real.rpow_def_of_pos hn0, mul_assoc,
      ← Real.exp_add]
    congr 2; ring
  have hFsum : Summable fun n => ∫ u : ℝ, ‖F n u‖ := by
    simp_rw [hFnorm]
    exact (hw s.re hs).mul_right _
  have hpt : ∀ u : ℝ, sPlus w u * cexp ((u : ℂ) * z) = ∑' n : ℕ, F n u := by
    intro u
    rw [sPlus, ← tsum_mul_right]
    congr 1
    funext n
    simp only [hF, kernelWeighted]
    have : cexp (-((Real.log n : ℂ) * z)) * cexp (((u + Real.log n : ℝ) : ℂ) * z) =
        cexp ((u : ℂ) * z) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    calc coef w n * sqKernel (u + Real.log n) * cexp ((u : ℂ) * z)
        = coef w n * sqKernel (u + Real.log n) *
            (cexp (-((Real.log n : ℂ) * z)) * cexp (((u + Real.log n : ℝ) : ℂ) * z)) := by
          rw [this]
      _ = coef w n * cexp (-((Real.log n : ℂ) * z)) *
            (sqKernel (u + Real.log n) * cexp (((u + Real.log n : ℝ) : ℂ) * z)) := by ring
  have hint_n : ∀ n, ∫ u : ℝ, F n u =
      LSeries.term w s n * riemannPhiTransform s ^ 2 := by
    intro n
    simp only [hF]
    rw [integral_const_mul,
      integral_add_right_eq_self (fun v => kernelWeighted z v) (Real.log n),
      integral_kernelWeighted, coef_mul_cexp_eq_term, hz, sub_add_cancel]
  unfold bigH spectralLaplace
  rw [← hz]
  simp_rw [hpt]
  rw [← integral_tsum_of_summable_integral_norm hFint hFsum]
  simp_rw [hint_n]
  rw [tsum_mul_right, LSeries, mul_comm]

end TransformProps

/-! ## The conclusion -/

theorem lseriesSummable_of_weights {w : ℕ → ℂ}
    (hw : ∀ σ : ℝ, 3 / 2 < σ → Summable fun n : ℕ => ‖w n‖ * (n : ℝ) ^ (-σ)) {s : ℂ}
    (hs : 3 / 2 < s.re) : LSeriesSummable w s := by
  refine Summable.of_norm ((hw s.re hs).congr fun n => ?_)
  rw [LSeries.norm_term_eq]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Real.zero_rpow (by linarith : -s.re ≠ 0)]
  rw [if_neg hn.ne', Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]

theorem summable_weights_of_lseriesSummable {g : ℕ → ℂ} {σ : ℝ} (hσ : σ ≠ 0)
    (h : LSeriesSummable g σ) : Summable fun n : ℕ => ‖g n‖ * (n : ℝ) ^ (-σ) := by
  refine (summable_norm_iff.mpr h).congr fun n => ?_
  rw [LSeries.norm_term_eq]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Real.zero_rpow (neg_ne_zero.mpr hσ)]
  rw [if_neg hn.ne', Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
  simp

/-- **Injectivity of the transform with kernel `K = Φ ⋆ Φ`.**  If
`Σ_n w(n) n^{−½} (K(y − log n) + K(y + log n)) = 0` for every real `y`, with
`Σ |w(n)| n^{−σ} < ∞` for every `σ > 3/2`, then `w(n) = 0` for every `n ≥ 1`. -/
theorem eq_zero_of_sqKernelTransform_eq_zero {w : ℕ → ℂ}
    (hw : ∀ σ : ℝ, 3 / 2 < σ → Summable fun n : ℕ => ‖w n‖ * (n : ℝ) ^ (-σ))
    (hzero : ∀ y : ℝ, sMinus w y + sPlus w y = 0) {m : ℕ} (hm : 1 ≤ m) : w m = 0 := by
  open MaassZetaSquaredConverse in
  set g : ℕ → ℂ := (1 / 4 : ℂ) • LSeries.convolution divisorCount w with hg
  have hgS : ∀ {s : ℂ}, 3 / 2 < s.re → LSeriesSummable g s := fun hs =>
    ((LSeriesSummable_divisorCount (by linarith)).convolution
      (lseriesSummable_of_weights hw hs)).smul _
  have hgsum : ∀ σ : ℝ, 3 / 2 < σ → Summable fun n : ℕ => ‖g n‖ * (n : ℝ) ^ (-σ) :=
    fun σ hσ => summable_weights_of_lseriesSummable (by linarith)
      (hgS (by simpa using hσ))
  have hLg : ∀ {s : ℂ}, 3 / 2 < s.re →
      LSeries g s = 1 / 4 * (riemannZeta s ^ 2 * LSeries w s) := fun hs => by
    rw [hg, LSeries_smul, LSeries_convolution' (LSeriesSummable_divisorCount (by linarith))
      (lseriesSummable_of_weights hw hs), LSeries_divisorCount (by linarith)]
  have heq : ∀ s : ℂ, 3 / 2 < s.re →
      bigH w s = s ^ 2 * (s - 1) ^ 2 * Complex.Gammaℝ s ^ 2 * LSeries g s := by
    intro s hs
    have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
    have hΓ : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
    have hΛ : completedRiemannZeta s = Complex.Gammaℝ s * riemannZeta s := by
      rw [riemannZeta_def_of_ne_zero hs0]; field_simp
    rw [bigH_eq_of_three_halves_lt_re hw hs, riemannPhiTransform_eq_of_one_lt_re (by linarith), hΛ,
      hLg hs]
    ring
  have hzero_g : ∀ k : ℕ, 1 ≤ k → g k = 0 := fun k hk =>
    MaassZetaSquaredConverseWide.coeff_eq_zero_of_odd_functional_equation_wide hgsum
      (differentiable_bigH hw hzero) (bigH_one_sub hzero) heq (exists_bound_bigH hw hzero) hk
  have hLw : ∀ x : ℝ, 3 / 2 < x → LSeries w x = 0 := by
    intro x hx
    have hxre : 3 / 2 < (x : ℂ).re := by simpa using hx
    have hg0 : LSeries g x = 0 := by
      rw [LSeries_congr (g := 0) (fun {k} hk => hzero_g k (Nat.one_le_iff_ne_zero.mpr hk))]
      simp
    rw [hLg hxre] at hg0
    have hζ : riemannZeta (x : ℂ) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by linarith)
    have : riemannZeta (x : ℂ) ^ 2 * LSeries w x = 0 := by
      linear_combination 4 * hg0
    rcases mul_eq_zero.mp this with h | h
    · exact absurd ((pow_eq_zero_iff two_ne_zero).mp h) hζ
    · exact h
  have hev : (fun x : ℝ => LSeries w x) =ᶠ[atTop] 0 :=
    (eventually_gt_atTop (3 / 2)).mono fun x hx => by simpa using hLw x hx
  rcases LSeries_eventually_eq_zero_iff'.mp hev with h | h
  · exact h m (by omega)
  · exfalso
    have h2 := (lseriesSummable_of_weights hw (s := 2) (by norm_num)).abscissaOfAbsConv_le
    rw [h] at h2
    simp at h2


/-- The symmetric form: `Σ_n w(n) n^{−½} (K(y − log n) + K(y + log n)) = 0` for every `y` forces
`w(n) = 0` for every `n ≥ 1`. -/
theorem eq_zero_of_sqKernelTransform_sum_eq_zero {w : ℕ → ℂ}
    (hw : ∀ σ : ℝ, 3 / 2 < σ → Summable fun n : ℕ => ‖w n‖ * (n : ℝ) ^ (-σ))
    (hzero : ∀ y : ℝ,
      ∑' n : ℕ, coef w n * (sqKernel (y - Real.log n) + sqKernel (y + Real.log n)) = 0)
    {m : ℕ} (hm : 1 ≤ m) : w m = 0 := by
  refine eq_zero_of_sqKernelTransform_eq_zero hw (fun y => ?_) hm
  have hm' := summable_coef_mul_sqKernel hw y (-1) (Or.inr rfl)
  have hp' := summable_coef_mul_sqKernel hw y 1 (Or.inl rfl)
  simp only [neg_one_mul, one_mul, ← sub_eq_add_neg] at hm' hp'
  rw [sMinus, sPlus, ← hm'.tsum_add hp', ← hzero y]
  congr 1
  funext n
  ring


/-- **Coefficient form.**  If `Σ_{n≥1} u(n)(K(y − log n) + K(y + log n)) = 0` for every real `y`,
where `Σ |u(n)| n^{−τ} < ∞` for every `τ > 1` (for instance `u(n) = O(log n)`), then `u = 0`. -/
theorem eq_zero_of_sqKernel_coeffTransform_eq_zero {u : ℕ → ℂ}
    (hu : ∀ τ : ℝ, 1 < τ → Summable fun n : ℕ => ‖u n‖ * (n : ℝ) ^ (-τ))
    (hzero : ∀ y : ℝ, ∑' n : ℕ, u (n + 1) *
      (sqKernel (y - Real.log (n + 1)) + sqKernel (y + Real.log (n + 1))) = 0)
    (n : ℕ) : u (n + 1) = 0 := by
  set w : ℕ → ℂ := fun k => u k * (Real.sqrt k : ℂ) with hwdef
  have hcoef1 : ∀ k : ℕ, coef w (k + 1) = u (k + 1) := by
    intro k
    have hne : ((Real.sqrt ((k + 1 : ℕ) : ℝ) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < ((k + 1 : ℕ) : ℝ))).ne'
    simp only [coef, hwdef]
    rw [mul_div_assoc, div_self hne, mul_one]
  have hcoef0 : coef w 0 = 0 := by simp [coef]
  have hw : ∀ σ : ℝ, 3 / 2 < σ → Summable fun n : ℕ => ‖w n‖ * (n : ℝ) ^ (-σ) := by
    intro σ hσ
    refine (hu (σ - 1 / 2) (by linarith)).congr fun k => ?_
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [hwdef, Real.zero_rpow (show (2⁻¹ - σ : ℝ) ≠ 0 by linarith),
        Real.zero_rpow (show -σ ≠ 0 by linarith)]
    · have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
      simp only [hwdef, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)]
      rw [Real.sqrt_eq_rpow, mul_assoc, ← Real.rpow_add hk0]
      ring_nf
  have htsum : ∀ f : ℕ → ℂ, f 0 = 0 → ∑' k, f k = ∑' k, f (k + 1) := by
    intro f hf0
    by_cases hs : Summable fun k => f (k + 1)
    · rw [tsum_eq_zero_add' hs, hf0, zero_add]
    · rw [tsum_eq_zero_of_not_summable hs, tsum_eq_zero_of_not_summable
        (fun h => hs ((summable_nat_add_iff 1).mpr h))]
  have hzero' : ∀ y : ℝ, ∑' k : ℕ, coef w k *
      (sqKernel (y - Real.log k) + sqKernel (y + Real.log k)) = 0 := by
    intro y
    rw [htsum _ (by simp [hcoef0])]
    simp_rw [hcoef1]
    push_cast
    exact hzero y
  have h := eq_zero_of_sqKernelTransform_sum_eq_zero hw hzero' (m := n + 1) (by omega)
  simp only [hwdef] at h
  have hsq : ((Real.sqrt ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ))).ne'
  exact (mul_eq_zero.mp h).resolve_right hsq

end

end RiemannSquareKernel

end RHTower
