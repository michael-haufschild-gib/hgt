import GaloisForLFunctions.RHTower.XiSliceHermiteWindowDetection
import GaloisForLFunctions.RHTower.XiSliceLargeRadiusArcBounds
import GaloisForLFunctions.RHTower.XiSliceHeatPerPairPositivity

/-!
# Heated slices detect off-line zeros at the Ki–Kim–Lee scale

Let `f_t(y) = |ξ(½+y+it)|²` and let `T_n(λ, 0, t)` be the heated slice coefficients.

**Theorem** (`re_xiSliceHeatTransfer_neg_of_slice_zero`).  Let `t ≥ e^{max(K₀, 8)}` with
`K₀ = 2(3 + Σ Λ(n)/n²) + log 6 ≤ 16`, `δ₀ ∈ (0, ½]`, `δ ≥ δ₀` with `f_t(δ) = 0` (an off-line zero
`½ + δ + it`), and `κ ∈ (0, κ₀(δ₀)]`, `κ₀(δ₀) = δ₀²/(200(log(3/δ₀) + 1))`.  Then some `T_n(κ/log t, 0, t)`
has negative real part.

So an off-line zero of offset `δ` at height `t ≥ e^{16}` is visible to heat `≍ δ²/(log(3/δ) log t)`,
with no condition on the zeros near `½ + it`.

Proof.  Suppose `a_n = Re T_n ≥ 0` for all `n`, with `λ = κ/log t`.  Then `H(y) = Σ a_n yⁿ` is the
Gaussian average `E f_t(y + √λ Z)` (`hasSum_re_xiSliceHeatTransfer_mul_pow`), and the coefficients are
nonnegative, so the slice at the zero is never evaluated directly.

* **Real-axis envelope** (`xiSliceReal_le_global`).  `f_t(y) ≤ f_t(3/2) e^{A|y| + y²}` with
  `A = log t + K₀`.  It comes from `f_t(y) ≤ f_t(3/2+|y|)`, Stirling growth on `[3/2, t/2]` with the
  explicit constant `3 + Σ Λ(n)/n²`, and the large-radius bound for `ξ'/ξ` beyond `t/2`.  Hence
  `H(R) ≤ √2 f_t(3/2) e^{AR + 2R² + 2A²λ}`, and `H(3/2) ≥ f_t(3/2)/2`.
* **Three radii** (`hasSum_three_radius_le`).  For nonnegative coefficients,
  `H(3/2) ≤ (3/δ)^M H(δ/2) + 2^{−M} H(3)`.  With `M ≍ log t` this gives
  `H(δ/2) ≥ (δ/3)^M f_t(3/2)/4`.  The lower bound at `δ/2` comes from the Euler region and does not use
  `f_t(0)`, which a cluster of zeros near `½ + it` can make arbitrarily small.
* **Hermite identity at the zero.**  `0 = f_t(δ) = Σ p_n a_n` with `p_n ≥ (δ/2)ⁿ` for
  `n ≤ n₀ = ⌊δ²/(4λ)⌋` and `|p_n| ≤ (δ + 2√(λn))ⁿ` (`XiSliceHermiteWindowDetection`).  With
  `a_n ≤ H(R_n)/R_nⁿ` at `R_n = 2(δ + 2√(λn))` this gives
  `H(δ/2) ≤ 6√2 f_t(3/2) e^{2Aδ+16δ²+34A²λ} (2/3)^{n₀+1}`.

Since `n₀ ≍ δ² log t/κ` and `M ≍ log t`, both bounds hold together only if `κ ≳ δ²/log(3/δ)`.

**Linear scale under regular growth** (`re_xiSliceHeatTransfer_neg_of_regular_growth`).  The upper
bound holds for any growth majorant `H(R) ≤ G₀ e^{αR + βR²}` (`heatSeries_half_le_of_growth`).  If the
heated slice grows from `δ/2` at the natural rate, `H(R) ≤ C H(δ/2) e^{c log t · R + BR²}`, the
Hermite identity alone gives detection at every `κ ≤ δ/(96(c+1))`, linear in `δ`.  The loss to
`δ²/log(3/δ)` in the unconditional theorem is exactly the three-radii lower bound `H(δ/2) ≥ (δ/3)^M
f_t(3/2)/4`, the worst case of `≍ log t` zeros clustered near `½ + it`.

**Corollaries.**  Every-height heat positivity at rate `κ ≤ κ₀(δ₀)` excludes zeros with
`Re ρ ≥ ½ + δ₀` above `e^{16}` (`DeBruijn.re_lt_of_heat_rate_pos`); positivity at every rate makes the
zeros with `Re ρ ≥ ½ + δ₀` bounded in height (`DeBruijn.exists_im_le_of_heat_rate_zero`).  Every zero
`ρ` with `Re ρ > ½` and `Im ρ ≥ e^{16}` gives `λ_WD ≥ κ₀(δ)/log Im ρ` and, for the de Bruijn–Newman
constant, `Λ ≥ κ₀(δ)/log Im ρ`, `δ = min(Re ρ − ½, ½)`
(`DeBruijn.le_newmanConstant_of_offLine_zero_explicit`).  The bound `K₀ ≤ 16` uses
`Σ Λ(n)/n² ≤ 4` (`vonMangoldtSquareMass_le_four`).
-/

open Complex MeasureTheory Filter Topology
open scoped ComplexOrder
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-! ## The slice on the whole real axis -/

/-- **Growth beyond `t/2`.**  For `t ≥ 16` and `t/2 ≤ y₁ ≤ y₂`,
`f_t(y₂) ≤ f_t(y₁) e^{(log(4y₂) + 2C)(y₂ − y₁)}`. -/
theorem xiSliceReal_le_of_large {t : ℝ} (ht : 16 ≤ t) {y₁ y₂ : ℝ} (h1 : t / 2 ≤ y₁)
    (h12 : y₁ ≤ y₂) :
    xiSliceReal t y₂ ≤ xiSliceReal t y₁ *
      Real.exp ((Real.log (4 * y₂) + 2 * xiLogDerivStirlingConstant) * (y₂ - y₁)) := by
  set D : Set ℝ := Set.Icc y₁ y₂ with hD
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
  have hbound : ∀ y ∈ interior D,
      deriv g y ≤ Real.log (4 * y₂) + 2 * xiLogDerivStirlingConstant := by
    intro y hy
    have hyD := interior_subset hy
    rw [(hgder y hyD).deriv]
    obtain ⟨-, -, hhi⟩ := xiSliceLogDeriv_real_bounds_large (t := t) (R := y)
      (by linarith [hyD.1]) (by linarith) (by linarith [hyD.1])
    have : Real.log (4 * y) ≤ Real.log (4 * y₂) :=
      Real.log_le_log (by linarith [hyD.1]) (by linarith [hyD.2])
    linarith
  have hy₁ : y₁ ∈ D := ⟨le_rfl, h12⟩
  have hy₂ : y₂ ∈ D := ⟨h12, le_rfl⟩
  have hup := (convex_Icc y₁ y₂).image_sub_le_mul_sub_of_deriv_le hcont hdiff hbound y₁ hy₁ y₂
    hy₂ h12
  simp only [hg] at hup
  have hp1 := hpos y₁ hy₁
  have hp2 := hpos y₂ hy₂
  rw [← Real.exp_log hp1, ← Real.exp_log hp2, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

/-- **Growth on the line `Re s = 2` and to its right.**  For `t ≥ 8` and `3/2 ≤ y₁ ≤ y₂ ≤ t/2`,
`f_t(y₂) ≤ f_t(y₁) e^{(log t + 2C)(y₂ − y₁)}` with the explicit Stirling constant
`C = 3 + Σ Λ(n)/n²`. -/
theorem xiSliceReal_le_of_stirling {t : ℝ} (ht : 8 ≤ t) {y₁ y₂ : ℝ} (h1 : 3 / 2 ≤ y₁)
    (h12 : y₁ ≤ y₂) (h2 : y₂ ≤ t / 2) :
    xiSliceReal t y₂ ≤ xiSliceReal t y₁ *
      Real.exp ((Real.log t + 2 * xiLogDerivStirlingConstant) * (y₂ - y₁)) := by
  set D : Set ℝ := Set.Icc y₁ y₂ with hD
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
  have hbound : ∀ y ∈ interior D,
      deriv g y ≤ Real.log t + 2 * xiLogDerivStirlingConstant := by
    intro y hy
    have hyD := interior_subset hy
    rw [(hgder y hyD).deriv]
    exact (xiSliceLogDeriv_real_bounds (t := t) (R := y) ht (by linarith [hyD.1])
      (by linarith [hyD.2])).2.2
  have hy₁ : y₁ ∈ D := ⟨le_rfl, h12⟩
  have hy₂ : y₂ ∈ D := ⟨h12, le_rfl⟩
  have hup := (convex_Icc y₁ y₂).image_sub_le_mul_sub_of_deriv_le hcont hdiff hbound y₁ hy₁ y₂
    hy₂ h12
  simp only [hg] at hup
  have hp1 := hpos y₁ hy₁
  have hp2 := hpos y₂ hy₂
  rw [← Real.exp_log hp1, ← Real.exp_log hp2, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

/-- The constant `K₀ = 2C + log 6` of the real-axis envelope, `C = 3 + Σ Λ(n)/n²`. -/
def xiSliceGlobalConstant : ℝ := 2 * xiLogDerivStirlingConstant + Real.log 6

theorem xiSliceGlobalConstant_pos : 0 < xiSliceGlobalConstant := by
  unfold xiSliceGlobalConstant
  have h2 := xiLogDerivStirlingConstant_pos
  have h3 : 0 < Real.log 6 := Real.log_pos (by norm_num)
  linarith

/-- **The real-axis envelope.**  For `t ≥ 16` and every real `y`,
`f_t(y) ≤ f_t(3/2) e^{(log t + K₀)|y| + y²}`. -/
theorem xiSliceReal_le_global {t : ℝ} (ht : 16 ≤ t) (y : ℝ) :
    xiSliceReal t y ≤ xiSliceReal t (3 / 2) *
      Real.exp ((Real.log t + xiSliceGlobalConstant) * |y| + y ^ 2) := by
  set C := xiLogDerivStirlingConstant with hC
  have hC0 : 0 < C := xiLogDerivStirlingConstant_pos
  have hl6 : 0 < Real.log 6 := Real.log_pos (by norm_num)
  have hlt : 0 < Real.log t := Real.log_pos (by linarith)
  have hF := xiSliceReal_nonneg t (3 / 2)
  have hy0 := abs_nonneg y
  have hsq : |y| * |y| = y ^ 2 := by rw [← sq, sq_abs]
  have hK : xiSliceGlobalConstant = 2 * C + Real.log 6 := rfl
  have hfirst : xiSliceReal t y ≤ xiSliceReal t (3 / 2 + |y|) := by
    refine xiSliceReal_le_of_abs_sub_half_le t ?_
    have := abs_sub y (1 / 2)
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at this
    linarith
  refine hfirst.trans ?_
  rcases le_or_gt (3 / 2 + |y|) (t / 2) with hz | hz
  · have h := xiSliceReal_le_of_stirling (t := t) (by linarith) (y₁ := 3 / 2) (y₂ := 3 / 2 + |y|)
      le_rfl (by linarith) hz
    rw [← hC] at h
    refine h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hF)
    rw [hK]
    nlinarith
  · have h1 := xiSliceReal_le_of_stirling (t := t) (by linarith) (y₁ := 3 / 2) (y₂ := t / 2)
      le_rfl (by linarith) le_rfl
    have h2 := xiSliceReal_le_of_large ht (y₁ := t / 2) (y₂ := 3 / 2 + |y|) le_rfl hz.le
    rw [← hC] at h1 h2
    have hlogz : Real.log (4 * (3 / 2 + |y|)) ≤ Real.log 6 + |y| := by
      rw [show 4 * (3 / 2 + |y|) = 6 * (1 + 2 / 3 * |y|) by ring,
        Real.log_mul (by norm_num) (by positivity)]
      have := Real.log_le_sub_one_of_pos (show 0 < 1 + 2 / 3 * |y| by positivity)
      linarith
    have hAy : t / 2 - 3 / 2 ≤ |y| := by linarith
    have hBy : 3 / 2 + |y| - t / 2 ≤ |y| := by linarith
    have hA : 0 ≤ t / 2 - 3 / 2 := by linarith
    have hB : 0 ≤ 3 / 2 + |y| - t / 2 := by linarith
    calc xiSliceReal t (3 / 2 + |y|)
        ≤ xiSliceReal t (t / 2) * Real.exp ((Real.log (4 * (3 / 2 + |y|)) + 2 * C)
            * (3 / 2 + |y| - t / 2)) := h2
      _ ≤ xiSliceReal t (3 / 2) * Real.exp ((Real.log t + 2 * C) * (t / 2 - 3 / 2))
            * Real.exp ((Real.log (4 * (3 / 2 + |y|)) + 2 * C) * (3 / 2 + |y| - t / 2)) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = xiSliceReal t (3 / 2) * Real.exp ((Real.log t + 2 * C) * (t / 2 - 3 / 2)
            + (Real.log (4 * (3 / 2 + |y|)) + 2 * C) * (3 / 2 + |y| - t / 2)) := by
          rw [Real.exp_add]; ring
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hF
          rw [hK]
          have e1 : (Real.log t + 2 * C) * (t / 2 - 3 / 2)
              ≤ (Real.log t + 2 * C + Real.log 6) * (t / 2 - 3 / 2) :=
            mul_le_mul_of_nonneg_right (by linarith) hA
          have e2 : (Real.log (4 * (3 / 2 + |y|)) + 2 * C) * (3 / 2 + |y| - t / 2)
              ≤ (Real.log t + 2 * C + Real.log 6 + |y|) * (3 / 2 + |y| - t / 2) :=
            mul_le_mul_of_nonneg_right (by linarith) hB
          have e3 : |y| * (3 / 2 + |y| - t / 2) ≤ |y| * |y| :=
            mul_le_mul_of_nonneg_left hBy hy0
          have e4 : (t / 2 - 3 / 2) + (3 / 2 + |y| - t / 2) = |y| := by ring
          nlinarith

/-! ## The heated slice on the positive axis -/

/-- The kernel envelope `E(r) = (∫ Φ(u) e^{r|u|} du)²` of the slice. -/
def xiSliceKernelEnvelope (r : ℝ) : ℝ :=
  (∫ u : ℝ, riemannKernelReal u * Real.exp (r * |u|)) ^ 2

theorem xiSliceKernelEnvelope_mono : Monotone xiSliceKernelEnvelope := by
  intro r r' hrr
  unfold xiSliceKernelEnvelope
  have h0 : 0 ≤ ∫ u : ℝ, riemannKernelReal u * Real.exp (r * |u|) :=
    integral_nonneg fun u => mul_nonneg (DeBruijn.riemannKernel_superExp.nonneg u)
      (Real.exp_pos _).le
  refine pow_le_pow_left₀ h0 (integral_mono (DeBruijn.riemannKernel_superExp.integrable_mul_exp r)
    (DeBruijn.riemannKernel_superExp.integrable_mul_exp r') fun u => ?_) 2
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hrr (abs_nonneg u)))
    (DeBruijn.riemannKernel_superExp.nonneg u)

/-- `‖S(t, z)‖ ≤ E(‖z‖)`. -/
theorem norm_xiSliceProduct_le_kernelEnvelope (t : ℝ) (z : ℂ) :
    ‖xiSliceProduct t z‖ ≤ xiSliceKernelEnvelope ‖z‖ := by
  set Φ := riemannKernelReal with hΦ
  have hΦ0 : ∀ u, 0 ≤ Φ u := DeBruijn.riemannKernel_superExp.nonneg
  set c := ‖z‖ with hc
  have hmaj := DeBruijn.integrable_prod_majorant DeBruijn.riemannKernel_superExp c
  rw [DeBruijn.xiSliceProduct_eq_integral]
  refine (norm_integral_le_of_norm_le hmaj (Eventually.of_forall fun p => ?_)).trans ?_
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp,
      abs_of_nonneg (mul_nonneg (hΦ0 p.1) (hΦ0 p.2))]
    have hre : (I * (t : ℂ) * ((p.1 : ℂ) + p.2) + z * ((p.1 : ℂ) - p.2)).re
        = z.re * (p.1 - p.2) := by
      simp [Complex.mul_re, Complex.add_re, Complex.sub_re]
    rw [hre]
    have h1 : z.re * (p.1 - p.2) ≤ c * |p.1| + c * |p.2| := by
      have := Complex.abs_re_le_norm z
      have h2 : z.re * (p.1 - p.2) ≤ |z.re| * |p.1 - p.2| := by
        rw [← abs_mul]; exact le_abs_self _
      have h3 : |p.1 - p.2| ≤ |p.1| + |p.2| := abs_sub _ _
      have h4 : |z.re| * |p.1 - p.2| ≤ c * (|p.1| + |p.2|) :=
        mul_le_mul this h3 (abs_nonneg _) (norm_nonneg _)
      linarith
    calc Φ p.1 * Φ p.2 * Real.exp (z.re * (p.1 - p.2))
        ≤ Φ p.1 * Φ p.2 * Real.exp (c * |p.1| + c * |p.2|) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h1) (mul_nonneg (hΦ0 _) (hΦ0 _))
      _ = Φ p.1 * Real.exp (c * |p.1|) * (Φ p.2 * Real.exp (c * |p.2|)) := by
          rw [Real.exp_add]; ring
  · unfold xiSliceKernelEnvelope
    refine le_of_eq ?_
    rw [Measure.volume_eq_prod, integral_prod_mul (fun u => riemannKernelReal u * Real.exp (c * |u|))
      (fun u => riemannKernelReal u * Real.exp (c * |u|)), sq]

/-- Gaussian integrability of the kernel envelope at any heat. -/
theorem integrable_gauss_mul_kernelEnvelope {lam : ℝ} (hlam : 0 ≤ lam) (y : ℝ) :
    Integrable (fun w : ℝ =>
      Real.exp (-(w ^ 2 / 2)) * xiSliceKernelEnvelope (Real.sqrt lam * |w| + 2 * y)) := by
  set a := 4 * lam + 1 with ha
  have ha0 : 0 < a := by linarith
  set Φ := riemannKernelReal with hΦ
  have hΦ0 : ∀ u, 0 ≤ Φ u := DeBruijn.riemannKernel_superExp.nonneg
  have hka : Integrable (fun u : ℝ => Φ u * Real.exp (a * u ^ 2)) := by
    simpa using (DeBruijn.riemannKernel_superExp.mul_exp_sq ha0.le).integrable_mul_exp 0
  set K := ∫ u : ℝ, Φ u * Real.exp (a * u ^ 2) with hK
  have hK0 : 0 ≤ K := integral_nonneg fun u => mul_nonneg (hΦ0 u) (Real.exp_pos _).le
  have henv : ∀ r : ℝ, xiSliceKernelEnvelope r ≤ (K * Real.exp (r ^ 2 / (4 * a))) ^ 2 := by
    intro r
    unfold xiSliceKernelEnvelope
    have h0 : 0 ≤ ∫ u : ℝ, Φ u * Real.exp (r * |u|) :=
      integral_nonneg fun u => mul_nonneg (hΦ0 u) (Real.exp_pos _).le
    refine pow_le_pow_left₀ h0 ?_ 2
    rw [hK, ← integral_mul_const]
    refine integral_mono (DeBruijn.riemannKernel_superExp.integrable_mul_exp r)
      (hka.mul_const _) fun u => ?_
    have hru : r * |u| ≤ a * u ^ 2 + r ^ 2 / (4 * a) := by
      have h1 : 0 ≤ (2 * a * |u| - r) ^ 2 / (4 * a) := by positivity
      have h2 : (2 * a * |u| - r) ^ 2 / (4 * a) = a * u ^ 2 - r * |u| + r ^ 2 / (4 * a) := by
        have hu := sq_abs u
        field_simp
        linear_combination 4 * a ^ 2 * hu
      linarith
    calc Φ u * Real.exp (r * |u|) ≤ Φ u * Real.exp (a * u ^ 2 + r ^ 2 / (4 * a)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hru) (hΦ0 u)
      _ = Φ u * Real.exp (a * u ^ 2) * Real.exp (r ^ 2 / (4 * a)) := by
          rw [Real.exp_add]; ring
  have hmeas : AEStronglyMeasurable (fun w : ℝ =>
      Real.exp (-(w ^ 2 / 2)) * xiSliceKernelEnvelope (Real.sqrt lam * |w| + 2 * y)) := by
    refine ((Real.continuous_exp.comp (by fun_prop)).measurable.mul
      (xiSliceKernelEnvelope_mono.measurable.comp (by fun_prop))).aestronglyMeasurable
  have hG : Integrable (fun w : ℝ => K ^ 2 * Real.exp (4 * y ^ 2 / a) * Real.exp (-(1 / 4) * w ^ 2)) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 4)).const_mul _
  refine hG.mono' hmeas (Eventually.of_forall fun w => ?_)
  have hE0 : 0 ≤ xiSliceKernelEnvelope (Real.sqrt lam * |w| + 2 * y) := by
    unfold xiSliceKernelEnvelope; positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hE0)]
  set r := Real.sqrt lam * |w| + 2 * y with hr
  have hr2 : r ^ 2 ≤ 2 * (lam * w ^ 2) + 8 * y ^ 2 := by
    have hs : (Real.sqrt lam * |w|) ^ 2 = lam * w ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hlam, sq_abs]
    rw [hr]; nlinarith [sq_nonneg (Real.sqrt lam * |w| - 2 * y)]
  have hexp : -(w ^ 2 / 2) + 2 * (r ^ 2 / (4 * a)) ≤ 4 * y ^ 2 / a + -(1 / 4) * w ^ 2 := by
    have h1 : 2 * (r ^ 2 / (4 * a)) ≤ (2 * (lam * w ^ 2) + 8 * y ^ 2) / (2 * a) := by
      rw [show 2 * (r ^ 2 / (4 * a)) = r ^ 2 / (2 * a) by field_simp; ring]
      exact div_le_div_of_nonneg_right hr2 (by positivity)
    have h2 : (2 * (lam * w ^ 2) + 8 * y ^ 2) / (2 * a) = lam * w ^ 2 / a + 4 * y ^ 2 / a := by
      field_simp; ring
    have h3 : lam * w ^ 2 / a ≤ w ^ 2 / 4 := by
      rw [div_le_iff₀ ha0]; nlinarith [sq_nonneg w]
    linarith
  calc Real.exp (-(w ^ 2 / 2)) * xiSliceKernelEnvelope r
      ≤ Real.exp (-(w ^ 2 / 2)) * (K * Real.exp (r ^ 2 / (4 * a))) ^ 2 :=
        mul_le_mul_of_nonneg_left (henv r) (Real.exp_pos _).le
    _ = K ^ 2 * Real.exp (-(w ^ 2 / 2) + 2 * (r ^ 2 / (4 * a))) := by
        rw [mul_pow, ← Real.exp_nat_mul, Real.exp_add]; push_cast; ring
    _ ≤ K ^ 2 * Real.exp (4 * y ^ 2 / a + -(1 / 4) * w ^ 2) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity)
    _ = _ := by rw [Real.exp_add]; ring

/-- **The heated slice on the positive axis.**  For `λ > 0` and `y > 0`,
`Σ_n Re T_n(λ, 0, t) yⁿ = (2π)^{−1/2} ∫ e^{−w²/2} f_t(√λ w + y) dw`. -/
theorem hasSum_re_xiSliceHeatTransfer_mul_pow {t lam y : ℝ} (hlam : 0 < lam) (hy : 0 < y) :
    HasSum (fun n : ℕ => (DeBruijn.xiSliceHeatTransfer lam 0 t n).re * y ^ n)
      ((∫ w : ℝ, Real.exp (-(w ^ 2 / 2)) * xiSliceReal t (Real.sqrt lam * w + y))
        / Real.sqrt (2 * Real.pi)) := by
  obtain ⟨h, -⟩ := DeBruijn.hasSum_xiSliceHeatTransfer_mul_pow (t := t) hlam.le hy
    (E := xiSliceKernelEnvelope) (fun r r' _ hrr => xiSliceKernelEnvelope_mono hrr)
    (norm_xiSliceProduct_le_kernelEnvelope t) (integrable_gauss_mul_kernelEnvelope hlam.le y)
  have hre := Complex.hasSum_re h
  have hint : (∫ w : ℝ, ((Real.exp (-(w ^ 2 / 2)) : ℝ) : ℂ)
      * xiSliceProduct t (((Real.sqrt lam * w : ℝ) : ℂ) + y))
      = ((∫ w : ℝ, Real.exp (-(w ^ 2 / 2)) * xiSliceReal t (Real.sqrt lam * w + y) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    simp only
    rw [show ((Real.sqrt lam * w : ℝ) : ℂ) + (y : ℂ) = ((Real.sqrt lam * w + y : ℝ) : ℂ) by
      push_cast; ring, xiSliceProduct_ofReal_eq_xiSliceReal]
    push_cast; ring
  rw [hint, Complex.ofReal_re] at hre
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  refine (hre.div_const (Real.sqrt (2 * Real.pi))).congr_fun fun n => ?_
  rw [show ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * DeBruijn.xiSliceHeatTransfer lam 0 t n
      * (y : ℂ) ^ n = ((Real.sqrt (2 * Real.pi) * y ^ n : ℝ) : ℂ)
        * DeBruijn.xiSliceHeatTransfer lam 0 t n by push_cast; ring, Complex.re_ofReal_mul]
  field_simp

/-- **Upper bound of the Gaussian average.**  For `t ≥ 16`, `16λ ≤ 1` and `R ≥ 0`,
`∫ e^{−w²/2} f_t(√λ w + R) dw ≤ √(4π) f_t(3/2) e^{AR + 2R² + 2A²λ}`, `A = log t + K₀`. -/
theorem integral_gauss_mul_xiSliceReal_le {t lam R : ℝ} (ht : 16 ≤ t) (hlam : 0 < lam)
    (hlam16 : 16 * lam ≤ 1) (hR : 0 ≤ R) :
    Integrable (fun w : ℝ => Real.exp (-(w ^ 2 / 2)) * xiSliceReal t (Real.sqrt lam * w + R)) ∧
    ∫ w : ℝ, Real.exp (-(w ^ 2 / 2)) * xiSliceReal t (Real.sqrt lam * w + R)
      ≤ Real.sqrt (4 * Real.pi) * (xiSliceReal t (3 / 2) * Real.exp ((Real.log t + xiSliceGlobalConstant)
          * R + 2 * R ^ 2 + 2 * (Real.log t + xiSliceGlobalConstant) ^ 2 * lam)) := by
  set A := Real.log t + xiSliceGlobalConstant with hA
  have hA0 : 0 ≤ A := by
    have := xiSliceGlobalConstant_pos; have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ t)
    linarith
  obtain ⟨hint, hle⟩ := DeBruijn.integral_gauss_mul_expEnvelope_le (c₀ := xiSliceReal t (3 / 2))
    (K := 0) (A := A) (B := 1) (r := R) (xiSliceReal_nonneg t (3 / 2)) zero_le_one hlam (by linarith)
  have hpt : ∀ w : ℝ, Real.exp (-(w ^ 2 / 2)) * xiSliceReal t (Real.sqrt lam * w + R)
      ≤ Real.exp (-(w ^ 2 / 2)) * DeBruijn.sliceExpEnvelope (xiSliceReal t (3 / 2)) 0 A 1
          (Real.sqrt lam * |w| + R) := by
    intro w
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    refine (xiSliceReal_le_global ht _).trans ?_
    unfold DeBruijn.sliceExpEnvelope
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (xiSliceReal_nonneg t (3 / 2))
    have h1 : |Real.sqrt lam * w + R| ≤ Real.sqrt lam * |w| + R := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg hR]
    have h2 : (Real.sqrt lam * w + R) ^ 2 ≤ (Real.sqrt lam * |w| + R) ^ 2 := by
      rw [← sq_abs (Real.sqrt lam * w + R)]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have h3 : A * |Real.sqrt lam * w + R| ≤ A * (Real.sqrt lam * |w| + R) :=
      mul_le_mul_of_nonneg_left h1 hA0
    linarith
  have hnn : ∀ w : ℝ, 0 ≤ Real.exp (-(w ^ 2 / 2)) * xiSliceReal t (Real.sqrt lam * w + R) :=
    fun w => mul_nonneg (Real.exp_pos _).le (xiSliceReal_nonneg _ _)
  have hcont : Continuous (xiSliceReal t) := by
    unfold xiSliceReal
    exact (xi_differentiable.continuous.comp (by fun_prop)).norm.pow 2
  refine ⟨hint.mono' (by fun_prop) (Eventually.of_forall fun w => ?_), ?_⟩
  · rw [Real.norm_eq_abs, abs_of_nonneg (hnn w)]; exact hpt w
  refine (integral_mono_of_nonneg (Eventually.of_forall hnn) hint
    (Eventually.of_forall hpt)).trans ?_
  refine hle.trans (le_of_eq ?_)
  ring_nf

/-- **Lower bound at an Euler point.**  For `b ≥ ½`,
`∫ e^{−w²/2} f_t(√λ w + b) dw ≥ √(2π) f_t(b)/2`, because `f_t ≥ f_t(b)` on `[b, ∞)` and one of
`b ± √λ w` lies there. -/
theorem integral_gauss_mul_xiSliceReal_base_ge {t lam b : ℝ} (hb : 1 / 2 ≤ b)
    (hint : Integrable (fun w : ℝ => Real.exp (-(w ^ 2 / 2)) * xiSliceReal t (Real.sqrt lam * w + b))) :
    Real.sqrt (2 * Real.pi) / 2 * xiSliceReal t b
      ≤ ∫ w : ℝ, Real.exp (-(w ^ 2 / 2)) * xiSliceReal t (Real.sqrt lam * w + b) := by
  set g : ℝ → ℝ := fun w => Real.exp (-(w ^ 2 / 2)) * xiSliceReal t (Real.sqrt lam * w + b) with hg
  have hneg : ∫ w, g (-w) = ∫ w, g w := integral_neg_eq_self g volume
  have hint' : Integrable (fun w => g (-w)) := hint.comp_neg
  have hgauss : ∫ w : ℝ, Real.exp (-(w ^ 2 / 2)) = Real.sqrt (2 * Real.pi) := by
    have h := integral_gaussian (1 / 2 : ℝ)
    rw [show Real.pi / (1 / 2) = 2 * Real.pi by ring] at h
    rw [← h]
    congr 1; funext w; congr 1; ring
  have hGi : Integrable (fun w : ℝ => Real.exp (-(w ^ 2 / 2)) * xiSliceReal t b) := by
    have := (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).mul_const (xiSliceReal t b)
    refine this.congr (Eventually.of_forall fun w => ?_)
    simp only; congr 2; ring
  have hpt : ∀ w : ℝ, Real.exp (-(w ^ 2 / 2)) * xiSliceReal t b ≤ g w + g (-w) := by
    intro w
    simp only [hg]
    rw [neg_sq, ← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    have h0 := xiSliceReal_nonneg t (Real.sqrt lam * w + b)
    have h0' := xiSliceReal_nonneg t (Real.sqrt lam * -w + b)
    rcases le_total 0 w with hw | hw
    · have := xiSliceReal_mono (t := t) (y := b) (z := Real.sqrt lam * w + b) hb
        (by nlinarith [Real.sqrt_nonneg lam])
      linarith
    · have := xiSliceReal_mono (t := t) (y := b) (z := Real.sqrt lam * -w + b) hb
        (by nlinarith [Real.sqrt_nonneg lam])
      linarith
  have hmono := integral_mono hGi (hint.add hint') hpt
  simp only [Pi.add_apply] at hmono
  rw [integral_mul_const, hgauss, integral_add hint hint', hneg] at hmono
  linarith

/-! ## Nonnegative power series -/

/-- **Three radii.**  For nonnegative `a_n`, `0 < y₁ ≤ y₂ < y₃` and `Gᵢ = Σ a_n yᵢⁿ`,
`G₂ ≤ (y₂/y₁)^M G₁ + G₃ (y₂/y₃)^{M+1}/(1 − y₂/y₃)` for every `M`. -/
theorem hasSum_three_radius_le {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) {y₁ y₂ y₃ G₁ G₂ G₃ : ℝ}
    (h1 : 0 < y₁) (h12 : y₁ ≤ y₂) (h23 : y₂ < y₃)
    (hG₁ : HasSum (fun n => a n * y₁ ^ n) G₁) (hG₂ : HasSum (fun n => a n * y₂ ^ n) G₂)
    (hG₃ : HasSum (fun n => a n * y₃ ^ n) G₃) (M : ℕ) :
    G₂ ≤ (y₂ / y₁) ^ M * G₁ + G₃ * (y₂ / y₃) ^ (M + 1) / (1 - y₂ / y₃) := by
  have hy₂ : 0 < y₂ := by linarith
  have hy₃ : 0 < y₃ := by linarith
  set q := y₂ / y₃ with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by rw [hq, div_lt_one hy₃]; exact h23
  have hr1 : 1 ≤ y₂ / y₁ := by rw [le_div_iff₀ h1]; linarith
  have hsplit := hG₂.summable.sum_add_tsum_nat_add (M + 1)
  rw [hG₂.tsum_eq] at hsplit
  -- the head
  have hhead : ∑ i ∈ Finset.range (M + 1), a i * y₂ ^ i ≤ (y₂ / y₁) ^ M * G₁ := by
    have h := sum_le_hasSum (Finset.range (M + 1))
      (fun i _ => mul_nonneg (ha i) (pow_nonneg h1.le i)) hG₁
    calc ∑ i ∈ Finset.range (M + 1), a i * y₂ ^ i
        ≤ ∑ i ∈ Finset.range (M + 1), (y₂ / y₁) ^ M * (a i * y₁ ^ i) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hiM : i ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          have e : a i * y₂ ^ i = (y₂ / y₁) ^ i * (a i * y₁ ^ i) := by
            rw [mul_left_comm, ← mul_pow, div_mul_cancel₀ _ h1.ne']
          rw [e]
          exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hr1 hiM)
            (mul_nonneg (ha i) (pow_nonneg h1.le i))
      _ = (y₂ / y₁) ^ M * ∑ i ∈ Finset.range (M + 1), a i * y₁ ^ i := by
          rw [Finset.mul_sum]
      _ ≤ (y₂ / y₁) ^ M * G₁ := mul_le_mul_of_nonneg_left h (by positivity)
  -- the tail
  have htail : ∑' i, a (i + (M + 1)) * y₂ ^ (i + (M + 1)) ≤ G₃ * q ^ (M + 1) / (1 - q) := by
    have hterm : ∀ i, a (i + (M + 1)) * y₂ ^ (i + (M + 1)) ≤ G₃ * q ^ (M + 1) * q ^ i := by
      intro i
      have hle := le_hasSum hG₃ (i + (M + 1)) fun j _ => mul_nonneg (ha j) (pow_nonneg hy₃.le j)
      have e : a (i + (M + 1)) * y₂ ^ (i + (M + 1))
          = a (i + (M + 1)) * y₃ ^ (i + (M + 1)) * q ^ (i + (M + 1)) := by
        rw [mul_assoc, ← mul_pow, hq, mul_div_cancel₀ _ hy₃.ne']
      rw [e, show G₃ * q ^ (M + 1) * q ^ i = G₃ * q ^ (i + (M + 1)) by ring]
      exact mul_le_mul_of_nonneg_right hle (pow_nonneg hq0 _)
    have hs1 : Summable fun i => a (i + (M + 1)) * y₂ ^ (i + (M + 1)) :=
      (summable_nat_add_iff (f := fun n => a n * y₂ ^ n) (M + 1)).mpr hG₂.summable
    have hs2 : Summable fun i : ℕ => G₃ * q ^ (M + 1) * q ^ i :=
      (summable_geometric_of_lt_one hq0 hq1).mul_left _
    refine (hs1.tsum_le_tsum hterm hs2).trans (le_of_eq ?_)
    rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
    field_simp
  linarith

/-- **The Hermite tail.**  Let `a_n ≥ 0` and `Σ p_n a_n = 0`, with `p_n ≥ (δ/2)ⁿ` for `n ≤ n₀` and
`(δ/2)ⁿ ≤ q_n`, `|p_n| ≤ q_n` for all `n`.  Then `Σ a_n (δ/2)ⁿ ≤ 2 Σ_{n > n₀} a_n q_n`. -/
theorem le_two_mul_tsum_tail_of_hasSum_zero {a p q : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hp : HasSum (fun n => p n * a n) 0) {δ G : ℝ} {n₀ : ℕ}
    (hwin : ∀ n ≤ n₀, (δ / 2) ^ n ≤ p n) (hq : ∀ n, |p n| ≤ q n) (hδq : ∀ n, (δ / 2) ^ n ≤ q n)
    (hG : HasSum (fun n => a n * (δ / 2) ^ n) G) (hsq : Summable (fun n => a n * q n)) :
    G ≤ 2 * ∑' k, a (k + (n₀ + 1)) * q (k + (n₀ + 1)) := by
  have hsplitp := hp.summable.sum_add_tsum_nat_add (n₀ + 1)
  rw [hp.tsum_eq] at hsplitp
  have hsplitG := hG.summable.sum_add_tsum_nat_add (n₀ + 1)
  rw [hG.tsum_eq] at hsplitG
  have hhead : ∑ i ∈ Finset.range (n₀ + 1), a i * (δ / 2) ^ i
      ≤ ∑ i ∈ Finset.range (n₀ + 1), p i * a i := by
    refine Finset.sum_le_sum fun i hi => ?_
    have hin : i ≤ n₀ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hwin i hin) (ha i)
  have hsq' : Summable fun k => a (k + (n₀ + 1)) * q (k + (n₀ + 1)) :=
    (summable_nat_add_iff (f := fun n => a n * q n) (n₀ + 1)).mpr hsq
  have hp' : Summable fun k => p (k + (n₀ + 1)) * a (k + (n₀ + 1)) :=
    (summable_nat_add_iff (f := fun n => p n * a n) (n₀ + 1)).mpr hp.summable
  have hG' : Summable fun k => a (k + (n₀ + 1)) * (δ / 2) ^ (k + (n₀ + 1)) :=
    (summable_nat_add_iff (f := fun n => a n * (δ / 2) ^ n) (n₀ + 1)).mpr hG.summable
  have h1 : -∑' k, a (k + (n₀ + 1)) * q (k + (n₀ + 1))
      ≤ ∑' k, p (k + (n₀ + 1)) * a (k + (n₀ + 1)) := by
    rw [← tsum_neg]
    refine hsq'.neg.tsum_le_tsum (fun k => ?_) hp'
    have h := hq (k + (n₀ + 1))
    have ha' := ha (k + (n₀ + 1))
    have := neg_abs_le (p (k + (n₀ + 1)))
    nlinarith
  have h2 : ∑' k, a (k + (n₀ + 1)) * (δ / 2) ^ (k + (n₀ + 1))
      ≤ ∑' k, a (k + (n₀ + 1)) * q (k + (n₀ + 1)) :=
    hG'.tsum_le_tsum (fun k => mul_le_mul_of_nonneg_left (hδq _) (ha _)) hsq'
  linarith

/-! ## The two bounds at `δ/2` under absolute monotonicity -/

/-- **Lower bound at `δ/2`.**  If every `Re T_n(λ, 0, t)` is `≥ 0`, then with
`A = log t + K₀`, `X = 3A + 20 + 2A²λ` and `M = ⌈X/log 2⌉`,
`(δ/3)^M f_t(3/2)/4 ≤ H(δ/2)`, where `H(y) = (2π)^{−1/2} ∫ e^{−w²/2} f_t(√λ w + y) dw`. -/
theorem heatSeries_half_ge {t lam δ : ℝ} (ht : 16 ≤ t) (hlam : 0 < lam) (hlam16 : 16 * lam ≤ 1)
    (hδ : 0 < δ) (hδ3 : δ ≤ 3)
    (hAM : ∀ n, 0 ≤ (DeBruijn.xiSliceHeatTransfer lam 0 t n).re) :
    (δ / 3) ^ ⌈(3 * (Real.log t + xiSliceGlobalConstant) + 20
        + 2 * (Real.log t + xiSliceGlobalConstant) ^ 2 * lam) / Real.log 2⌉₊
        * (xiSliceReal t (3 / 2) / 4)
      ≤ (∫ w : ℝ, Real.exp (-(w ^ 2 / 2)) * xiSliceReal t (Real.sqrt lam * w + δ / 2))
          / Real.sqrt (2 * Real.pi) := by
  set A := Real.log t + xiSliceGlobalConstant with hA
  set X := 3 * A + 20 + 2 * A ^ 2 * lam with hX
  set M := ⌈X / Real.log 2⌉₊ with hM
  set F := xiSliceReal t (3 / 2) with hF
  set H : ℝ → ℝ := fun y =>
    (∫ w : ℝ, Real.exp (-(w ^ 2 / 2)) * xiSliceReal t (Real.sqrt lam * w + y))
      / Real.sqrt (2 * Real.pi) with hH
  have hs2π : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hF0 : 0 < F := xiSliceReal_pos t (by norm_num)
  have hser : ∀ y, 0 < y → HasSum (fun n => (DeBruijn.xiSliceHeatTransfer lam 0 t n).re * y ^ n)
      (H y) := fun y hy => hasSum_re_xiSliceHeatTransfer_mul_pow hlam hy
  have h3 := hasSum_three_radius_le hAM (y₁ := δ / 2) (y₂ := 3 / 2) (y₃ := 3) (by positivity)
    (by linarith) (by norm_num) (hser _ (by positivity)) (hser _ (by norm_num))
    (hser _ (by norm_num)) M
  rw [show H 3 * ((3 / 2 : ℝ) / 3) ^ (M + 1) / (1 - 3 / 2 / 3) = H 3 * (1 / 2) ^ M by
    rw [show (3 / 2 : ℝ) / 3 = 1 / 2 by norm_num, pow_succ]; ring] at h3
  -- `H(3/2) ≥ F/2`
  obtain ⟨hint1, -⟩ := integral_gauss_mul_xiSliceReal_le (R := 3 / 2) ht hlam hlam16 (by norm_num)
  have hH1 : F / 2 ≤ H (3 / 2) := by
    have := integral_gauss_mul_xiSliceReal_base_ge (by norm_num) hint1
    simp only [hH]
    rw [le_div_iff₀ hs2π]
    linarith
  -- `H(3) (1/2)^M ≤ F/4`
  obtain ⟨-, hint2⟩ := integral_gauss_mul_xiSliceReal_le (R := 3) ht hlam hlam16 (by norm_num)
  rw [← hA] at hint2
  have hH2 : H 3 ≤ Real.sqrt 2 * (F * Real.exp (3 * A + 18 + 2 * A ^ 2 * lam)) := by
    simp only [hH]
    rw [div_le_iff₀ hs2π]
    have e : Real.sqrt (4 * Real.pi) = Real.sqrt 2 * Real.sqrt (2 * Real.pi) := by
      rw [← Real.sqrt_mul (by norm_num)]; congr 1; ring
    calc _ ≤ Real.sqrt (4 * Real.pi) * (F * Real.exp (A * 3 + 2 * 3 ^ 2 + 2 * A ^ 2 * lam)) :=
          hint2
      _ = _ := by rw [e]; ring_nf
  have hpowM : (1 / 2 : ℝ) ^ M ≤ Real.exp (-X) := by
    have hXM : X ≤ M * Real.log 2 := by
      have := Nat.le_ceil (X / Real.log 2)
      rw [← hM, div_le_iff₀ hl2] at this; exact this
    rw [show (1 / 2 : ℝ) ^ M = Real.exp (-(M * Real.log 2)) by
      rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log two_pos, one_div_pow, one_div]]
    exact Real.exp_le_exp.mpr (by linarith)
  have he2 : Real.sqrt 2 * Real.exp (-2) ≤ 1 / 4 := by
    have h1 : Real.sqrt 2 ≤ 3 / 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    have h2 : Real.exp (-2) ≤ 1 / 6 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
      have h3 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      have h4 := Real.exp_one_gt_d9
      nlinarith
    calc Real.sqrt 2 * Real.exp (-2) ≤ 3 / 2 * (1 / 6) :=
          mul_le_mul h1 h2 (Real.exp_pos _).le (by norm_num)
      _ = 1 / 4 := by norm_num
  have hH2M : H 3 * (1 / 2) ^ M ≤ F / 4 := by
    calc H 3 * (1 / 2) ^ M ≤ Real.sqrt 2 * (F * Real.exp (3 * A + 18 + 2 * A ^ 2 * lam))
          * Real.exp (-X) := mul_le_mul hH2 hpowM (by positivity) (by positivity)
      _ = F * (Real.sqrt 2 * Real.exp (-2)) := by
          rw [mul_assoc, mul_assoc, ← Real.exp_add,
            show 3 * A + 18 + 2 * A ^ 2 * lam + -X = -2 by rw [hX]; ring]
          ring
      _ ≤ F * (1 / 4) := mul_le_mul_of_nonneg_left he2 hF0.le
      _ = F / 4 := by ring
  -- conclusion
  have hkey : F / 4 ≤ ((3 / 2) / (δ / 2)) ^ M * H (δ / 2) := by linarith
  have hδ2' : 0 < δ / 2 := by positivity
  have hratio : (δ / 3) * ((3 / 2) / (δ / 2)) = 1 := by field_simp
  calc (δ / 3) ^ M * (F / 4) ≤ (δ / 3) ^ M * (((3 / 2) / (δ / 2)) ^ M * H (δ / 2)) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = H (δ / 2) := by
        rw [← mul_assoc, ← mul_pow, hratio, one_pow, one_mul]

/-- **Upper bound at `δ/2` from a zero at `δ`, for any growth majorant.**  Let `f_t(δ) = 0`, `δ > 0`,
every `Re T_n(λ, 0, t) ≥ 0`, and let the heated slice satisfy `H(R) ≤ G₀ e^{αR + βR²}` for `R > 0`, with
`β ≥ 0` and `256βλ ≤ 1`.  Then `H(δ/2) ≤ 6 G₀ e^{2αδ + 8βδ² + 32α²λ} (2/3)^{n₀+1}`,
`n₀ = ⌊δ²/(4λ)⌋`. -/
theorem heatSeries_half_le_of_growth {t lam δ G₀ α β : ℝ} (hlam : 0 < lam)
    (hδ : 0 < δ) (hzero : xiSliceReal t δ = 0) (hG₀ : 0 ≤ G₀) (hβ : 0 ≤ β)
    (hβlam : 256 * β * lam ≤ 1)
    (hgr : ∀ R : ℝ, 0 < R →
      (∫ w : ℝ, Real.exp (-(w ^ 2 / 2)) * xiSliceReal t (Real.sqrt lam * w + R))
          / Real.sqrt (2 * Real.pi) ≤ G₀ * Real.exp (α * R + β * R ^ 2))
    (hAM : ∀ n, 0 ≤ (DeBruijn.xiSliceHeatTransfer lam 0 t n).re) :
    (∫ w : ℝ, Real.exp (-(w ^ 2 / 2)) * xiSliceReal t (Real.sqrt lam * w + δ / 2))
          / Real.sqrt (2 * Real.pi)
      ≤ 6 * G₀ * Real.exp (2 * α * δ + 8 * β * δ ^ 2 + 32 * α ^ 2 * lam)
          * (2 / 3) ^ (⌊δ ^ 2 / (4 * lam)⌋₊ + 1) := by
  set c₁ := 2 * α * δ + 8 * β * δ ^ 2 + 32 * α ^ 2 * lam with hc₁
  set n₀ := ⌊δ ^ 2 / (4 * lam)⌋₊ with hn₀
  set a : ℕ → ℝ := fun n => (DeBruijn.xiSliceHeatTransfer lam 0 t n).re with ha
  set p : ℕ → ℝ := fun n => DeBruijn.sliceHermiteWeight lam δ n with hp
  set q : ℕ → ℝ := fun n => (δ + 2 * Real.sqrt (lam * n)) ^ n with hq
  set H : ℝ → ℝ := fun y =>
    (∫ w : ℝ, Real.exp (-(w ^ 2 / 2)) * xiSliceReal t (Real.sqrt lam * w + y))
      / Real.sqrt (2 * Real.pi) with hH
  have hser : ∀ y, 0 < y → HasSum (fun n => a n * y ^ n) (H y) := fun y hy =>
    hasSum_re_xiSliceHeatTransfer_mul_pow hlam hy
  -- the Hermite identity at the zero
  have hherm : HasSum (fun n => p n * a n) 0 := by
    have h := Complex.hasSum_re (DeBruijn.hasSum_hermiteWeight_mul_xiSliceHeatTransfer hlam t δ)
    rw [xiSliceProduct_ofReal_eq_xiSliceReal, hzero, Complex.ofReal_zero, Complex.zero_re] at h
    refine h.congr_fun fun n => ?_
    simp only [hp, ha]
    rw [Complex.re_ofReal_mul]
  have hwin : ∀ n ≤ n₀, (δ / 2) ^ n ≤ p n := by
    intro n hn
    refine DeBruijn.hermiteWeight_ge hlam hδ.le ?_
    have h1 : (n : ℝ) ≤ δ ^ 2 / (4 * lam) := le_trans (by exact_mod_cast hn) (Nat.floor_le
      (by positivity))
    rw [le_div_iff₀ (by positivity)] at h1
    linarith
  have hpq : ∀ n, |p n| ≤ q n := by
    intro n
    have h := DeBruijn.abs_hermiteWeight_le hlam δ n
    rwa [abs_of_pos hδ] at h
  have hδq : ∀ n, (δ / 2) ^ n ≤ q n := fun n =>
    pow_le_pow_left₀ (by positivity) (by linarith [Real.sqrt_nonneg (lam * n)]) n
  -- each `a_n q_n` is at most `G₀ e^{c₁} (2/3)ⁿ`
  have he14 : Real.exp (1 / 4) ≤ 4 / 3 := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 4 / 3 by norm_num)
    rw [← Real.exp_le_exp, Real.exp_log (by norm_num)] at h
    refine le_trans (Real.exp_le_exp.mpr (le_of_eq (by norm_num))) h
  have hterm : ∀ n, a n * q n ≤ G₀ * Real.exp c₁ * (2 / 3) ^ n := by
    intro n
    set r := Real.sqrt (lam * n) with hr
    have hr0 : 0 ≤ r := Real.sqrt_nonneg _
    set R := 2 * (δ + 2 * r) with hR
    have hR0 : 0 < R := by positivity
    have hle := le_hasSum (hser R hR0) n fun j _ => mul_nonneg (hAM j) (pow_nonneg hR0.le j)
    have hHR := hgr R hR0
    have hr2 : r ^ 2 = lam * n := Real.sq_sqrt (by positivity)
    have hexp : α * R + β * R ^ 2 ≤ c₁ + n / 4 := by
      have h1 : 4 * α * r ≤ n / 8 + 32 * α ^ 2 * lam := by
        nlinarith [sq_nonneg (r - 16 * α * lam), sq_nonneg (4 * α * r - n / 8 - 32 * α ^ 2 * lam)]
      have h2 : R ^ 2 ≤ 8 * δ ^ 2 + 32 * (lam * n) := by
        rw [hR, ← hr2]; nlinarith [sq_nonneg (δ - 2 * r)]
      have h3 : β * (32 * (lam * n)) ≤ n / 8 := by
        have := mul_le_mul_of_nonneg_right hβlam (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
        nlinarith
      have h4 : β * R ^ 2 ≤ β * (8 * δ ^ 2 + 32 * (lam * n)) := mul_le_mul_of_nonneg_left h2 hβ
      have h5 : α * R = 2 * α * δ + 4 * α * r := by rw [hR]; ring
      rw [hc₁]
      nlinarith
    have hqR : q n = R ^ n / 2 ^ n := by
      simp only [hq]; rw [hR, mul_pow, ← hr]; field_simp
    have h2n : Real.exp (n / 4) / 2 ^ n ≤ (2 / 3) ^ n := by
      rw [show Real.exp (n / 4) = Real.exp (1 / 4) ^ n by
        rw [← Real.exp_nat_mul]; congr 1; ring, ← div_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) n
    calc a n * q n = a n * R ^ n / 2 ^ n := by rw [hqR]; ring
      _ ≤ H R / 2 ^ n := div_le_div_of_nonneg_right hle (by positivity)
      _ ≤ G₀ * Real.exp (c₁ + n / 4) / 2 ^ n := by
          refine div_le_div_of_nonneg_right (hHR.trans ?_) (by positivity)
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hG₀
      _ = G₀ * Real.exp c₁ * (Real.exp (n / 4) / 2 ^ n) := by
          rw [Real.exp_add]; ring
      _ ≤ G₀ * Real.exp c₁ * (2 / 3) ^ n :=
          mul_le_mul_of_nonneg_left h2n (by positivity)
  have hgeo : Summable fun n : ℕ => G₀ * Real.exp c₁ * (2 / 3 : ℝ) ^ n :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have haq0 : ∀ n, 0 ≤ a n * q n := fun n =>
    mul_nonneg (hAM n) (pow_nonneg (by linarith [Real.sqrt_nonneg (lam * n)]) n)
  have hsq : Summable fun n => a n * q n := Summable.of_nonneg_of_le haq0 hterm hgeo
  have htail := le_two_mul_tsum_tail_of_hasSum_zero hAM hherm hwin hpq hδq
    (hser (δ / 2) (by positivity)) hsq
  have hsq' : Summable fun k => a (k + (n₀ + 1)) * q (k + (n₀ + 1)) :=
    (summable_nat_add_iff (f := fun n => a n * q n) (n₀ + 1)).mpr hsq
  have hgeo' : Summable fun k : ℕ => G₀ * Real.exp c₁ * (2 / 3 : ℝ) ^ (n₀ + 1)
      * (2 / 3 : ℝ) ^ k :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hsum : ∑' k, a (k + (n₀ + 1)) * q (k + (n₀ + 1))
      ≤ G₀ * Real.exp c₁ * (2 / 3 : ℝ) ^ (n₀ + 1) * 3 := by
    refine (hsq'.tsum_le_tsum (fun k => (hterm _).trans (le_of_eq ?_)) hgeo').trans (le_of_eq ?_)
    · rw [pow_add]; ring
    · rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num
  calc H (δ / 2) ≤ 2 * ∑' k, a (k + (n₀ + 1)) * q (k + (n₀ + 1)) := htail
    _ ≤ 2 * (G₀ * Real.exp c₁ * (2 / 3 : ℝ) ^ (n₀ + 1) * 3) := by linarith
    _ = _ := by ring

/-- **Upper bound at `δ/2` from a zero at `δ`.**  If `f_t(δ) = 0`, `δ > 0`, `512λ ≤ 1` and every
`Re T_n(λ, 0, t)` is `≥ 0`, then `H(δ/2) ≤ 6√2 f_t(3/2) e^{2Aδ + 16δ² + 34A²λ} (2/3)^{n₀+1}` with
`n₀ = ⌊δ²/(4λ)⌋`. -/
theorem heatSeries_half_le {t lam δ : ℝ} (ht : 16 ≤ t) (hlam : 0 < lam) (hlam512 : 512 * lam ≤ 1)
    (hδ : 0 < δ) (hzero : xiSliceReal t δ = 0)
    (hAM : ∀ n, 0 ≤ (DeBruijn.xiSliceHeatTransfer lam 0 t n).re) :
    (∫ w : ℝ, Real.exp (-(w ^ 2 / 2)) * xiSliceReal t (Real.sqrt lam * w + δ / 2))
          / Real.sqrt (2 * Real.pi)
      ≤ 6 * Real.sqrt 2 * xiSliceReal t (3 / 2)
          * Real.exp (2 * (Real.log t + xiSliceGlobalConstant) * δ + 16 * δ ^ 2
            + 34 * (Real.log t + xiSliceGlobalConstant) ^ 2 * lam)
          * (2 / 3) ^ (⌊δ ^ 2 / (4 * lam)⌋₊ + 1) := by
  set A := Real.log t + xiSliceGlobalConstant with hA
  set F := xiSliceReal t (3 / 2) with hF
  have hs2π : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hF0 : 0 < F := xiSliceReal_pos t (by norm_num)
  have hA0 : 0 ≤ A := by
    have := xiSliceGlobalConstant_pos; have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ t)
    linarith
  have hgr : ∀ R : ℝ, 0 < R →
      (∫ w : ℝ, Real.exp (-(w ^ 2 / 2)) * xiSliceReal t (Real.sqrt lam * w + R))
          / Real.sqrt (2 * Real.pi)
        ≤ (Real.sqrt 2 * F * Real.exp (2 * A ^ 2 * lam)) * Real.exp (A * R + 2 * R ^ 2) := by
    intro R hR0
    obtain ⟨-, hUR⟩ := integral_gauss_mul_xiSliceReal_le (R := R) ht hlam (by linarith) hR0.le
    rw [← hA] at hUR
    rw [div_le_iff₀ hs2π]
    have e : Real.sqrt (4 * Real.pi) = Real.sqrt 2 * Real.sqrt (2 * Real.pi) := by
      rw [← Real.sqrt_mul (by norm_num)]; congr 1; ring
    rw [e] at hUR
    calc _ ≤ Real.sqrt 2 * Real.sqrt (2 * Real.pi) * (F * Real.exp (A * R + 2 * R ^ 2
          + 2 * A ^ 2 * lam)) := hUR
      _ = _ := by rw [Real.exp_add]; ring
  have h := heatSeries_half_le_of_growth hlam hδ hzero (by positivity) zero_le_two
    (by linarith) hgr hAM
  have e : Real.exp (2 * A ^ 2 * lam) * Real.exp (2 * A * δ + 8 * 2 * δ ^ 2 + 32 * A ^ 2 * lam)
      = Real.exp (2 * A * δ + 16 * δ ^ 2 + 34 * A ^ 2 * lam) := by
    rw [← Real.exp_add]; congr 1; ring
  refine h.trans (le_of_eq ?_)
  rw [← e]; ring

/-! ## Detection -/

/-- The detection rate `κ₀(δ₀) = δ₀²/(200(log(3/δ₀) + 1))`. -/
def kklDetectionRate (δ₀ : ℝ) : ℝ := δ₀ ^ 2 / (200 * (Real.log (3 / δ₀) + 1))

theorem kklDetectionRate_pos {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (hδ₀2 : δ₀ ≤ 1 / 2) :
    0 < kklDetectionRate δ₀ := by
  unfold kklDetectionRate
  have : 0 ≤ Real.log (3 / δ₀) := Real.log_nonneg (by rw [le_div_iff₀ hδ₀]; linarith)
  positivity

theorem sixteen_le_exp_max (K : ℝ) : 16 ≤ Real.exp (max K 8) := by
  have h4 : 5 ≤ Real.exp 4 := by have := Real.add_one_le_exp (4 : ℝ); linarith
  have h8 : Real.exp 8 = Real.exp 4 * Real.exp 4 := by rw [← Real.exp_add]; norm_num
  have h88 : Real.exp 8 ≤ Real.exp (max K 8) := Real.exp_le_exp.mpr (le_max_right _ _)
  nlinarith

/-- **Detection of an off-line zero at the Ki–Kim–Lee scale.**  For `δ₀ ∈ (0, ½]`, `t ≥ e^{max(K₀, 8)}`,
`δ ≥ δ₀` with `f_t(δ) = 0` and `κ ∈ (0, κ₀(δ₀)]`, some heated slice coefficient `T_n(κ/log t, 0, t)` has
negative real part. -/
theorem re_xiSliceHeatTransfer_neg_of_slice_zero {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (hδ₀2 : δ₀ ≤ 1 / 2)
    {t : ℝ} (ht : Real.exp (max xiSliceGlobalConstant 8) ≤ t) {δ : ℝ} (hδ : δ₀ ≤ δ)
    (hzero : xiSliceReal t δ = 0) {κ : ℝ} (hκ : 0 < κ) (hκ₀ : κ ≤ kklDetectionRate δ₀) :
    ∃ n : ℕ, (DeBruijn.xiSliceHeatTransfer (κ / Real.log t) 0 t n).re < 0 := by
  by_contra hcon
  push Not at hcon
  have ht16 : 16 ≤ t := (sixteen_le_exp_max _).trans ht
  set L := Real.log t with hLdef
  have hLmax : max xiSliceGlobalConstant 8 ≤ L := by
    rw [hLdef, ← Real.log_exp (max xiSliceGlobalConstant 8)]
    exact Real.log_le_log (Real.exp_pos _) ht
  have hL8 : 8 ≤ L := (le_max_right _ _).trans hLmax
  have hLK : xiSliceGlobalConstant ≤ L := (le_max_left _ _).trans hLmax
  have hK0 := xiSliceGlobalConstant_pos
  set ℓ₀ := Real.log (3 / δ₀) with hℓ₀
  have hℓ₀0 : 0 ≤ ℓ₀ := Real.log_nonneg (by rw [le_div_iff₀ hδ₀]; linarith)
  have hκ₀' : κ * (200 * (ℓ₀ + 1)) ≤ δ₀ ^ 2 := by
    have := hκ₀; unfold kklDetectionRate at this
    rwa [le_div_iff₀ (by positivity)] at this
  have hκ400 : κ ≤ 1 / 400 := by
    have h1 : δ₀ ^ 2 ≤ 1 / 4 := by
      have := pow_le_pow_left₀ hδ₀.le hδ₀2 2; linarith only [this]
    have h2 : 200 ≤ 200 * (ℓ₀ + 1) := by linarith only [hℓ₀0]
    have h3 : κ * 200 ≤ κ * (200 * (ℓ₀ + 1)) := mul_le_mul_of_nonneg_left h2 hκ.le
    linarith only [h1, h3, hκ₀']
  set lam := κ / L with hlamdef
  have hlam : 0 < lam := by positivity
  have hlamL : lam * L = κ := by rw [hlamdef]; field_simp
  have hlam512 : 512 * lam ≤ 1 := by
    rw [hlamdef, mul_div_assoc', div_le_one (by linarith)]; linarith
  have hδ0 : 0 < δ := by linarith
  have hδ2 : δ ≤ 1 / 2 := by
    by_contra h
    push Not at h
    exact (xiSliceReal_pos t h).ne' hzero
  have hlow := heatSeries_half_ge ht16 hlam (by linarith) hδ0 (by linarith) hcon
  have hupp := heatSeries_half_le ht16 hlam hlam512 hδ0 hzero hcon
  set A := L + xiSliceGlobalConstant with hA
  set X := 3 * A + 20 + 2 * A ^ 2 * lam with hX
  set M := ⌈X / Real.log 2⌉₊ with hM
  set n₀ := ⌊δ ^ 2 / (4 * lam)⌋₊ with hn₀
  set c₁ := 2 * A * δ + 16 * δ ^ 2 + 34 * A ^ 2 * lam with hc₁
  set F := xiSliceReal t (3 / 2) with hF
  have hF0 : 0 < F := xiSliceReal_pos t (by norm_num)
  -- `(δ/3)^M ≤ 24√2 e^{c₁} (2/3)^{n₀+1}`
  have hcmp : (δ / 3) ^ M ≤ 24 * Real.sqrt 2 * Real.exp c₁ * (2 / 3) ^ (n₀ + 1) := by
    have h := hlow.trans hupp
    have h' : (δ / 3) ^ M * F ≤ (24 * Real.sqrt 2 * Real.exp c₁ * (2 / 3) ^ (n₀ + 1)) * F := by
      nlinarith
    exact le_of_mul_le_mul_right h' hF0
  -- logarithms
  set ℓ := Real.log (3 / δ) with hℓ
  have hℓ0 : 0 ≤ ℓ := Real.log_nonneg (by rw [le_div_iff₀ hδ0]; linarith)
  have hℓℓ₀ : ℓ ≤ ℓ₀ :=
    Real.log_le_log (by positivity) (div_le_div_of_nonneg_left (by norm_num) hδ₀ hδ)
  have hδ2' : δ / 3 = Real.exp (-ℓ) := by
    rw [hℓ, Real.exp_neg, Real.exp_log (by positivity)]; field_simp
  have hl32 : (1 : ℝ) / 3 ≤ Real.log (3 / 2) := by
    have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 3 / 2 by norm_num); norm_num at this ⊢
    linarith
  have h23 : (2 / 3 : ℝ) = Real.exp (-Real.log (3 / 2)) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have h24 : 24 * Real.sqrt 2 ≤ Real.exp 4 := by
    have h1 : Real.sqrt 2 ≤ 3 / 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
    have h2 := Real.exp_one_gt_d9
    have h3 : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h3]
    have h4 : (2.7182818283 : ℝ) ^ 4 ≤ Real.exp 1 ^ 4 := pow_le_pow_left₀ (by norm_num) h2.le 4
    nlinarith
  have hlogs : -(M * ℓ) ≤ 4 + c₁ - (n₀ + 1) * Real.log (3 / 2) := by
    rw [hδ2', h23, ← Real.exp_nat_mul, ← Real.exp_nat_mul] at hcmp
    have h := hcmp.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h24
      (Real.exp_pos _).le) (Real.exp_pos _).le)
    rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp] at h
    push_cast at h
    linarith
  -- the size of `M`, `c₁` and `n₀`
  have hA0 : 0 ≤ A := by linarith only [hL8, hK0, hA]
  have hA2 : A ≤ 2 * L := by linarith only [hLK, hA]
  have hA2lam : A ^ 2 * lam ≤ L / 100 := by
    have h1 : A ^ 2 ≤ 4 * L ^ 2 := by
      have := pow_le_pow_left₀ hA0 hA2 2
      linarith only [this, show (2 * L) ^ 2 = 4 * L ^ 2 by ring]
    have h2 : A ^ 2 * lam ≤ 4 * L ^ 2 * lam := mul_le_mul_of_nonneg_right h1 hlam.le
    have h3 : 4 * L ^ 2 * lam = 4 * L * κ := by rw [← hlamL]; ring
    have h4 : 4 * L * κ ≤ 4 * L * (1 / 400) :=
      mul_le_mul_of_nonneg_left hκ400 (by linarith only [hL8])
    linarith only [h2, h3, h4]
  have hc₁le : c₁ ≤ 234 / 100 * L + 4 := by
    have h1 : 2 * A * δ ≤ A := by
      have := mul_le_mul_of_nonneg_left hδ2 hA0
      linarith only [this]
    have h2 : 16 * δ ^ 2 ≤ 4 := by
      have := pow_le_pow_left₀ hδ0.le hδ2 2
      linarith only [this]
    rw [hc₁]; linarith only [h1, h2, hA2lam, hA2]
  have hl2 : 69 / 100 ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hMle : (M : ℝ) ≤ 873 / 100 * L + 30 := by
    have h1 : (M : ℝ) < X / Real.log 2 + 1 := Nat.ceil_lt_add_one (by positivity)
    have hX0 : 0 ≤ X := by positivity
    have h2 : X / Real.log 2 ≤ X / (69 / 100) := div_le_div_of_nonneg_left hX0 (by norm_num) hl2
    have h3 : X ≤ 602 / 100 * L + 20 := by rw [hX]; linarith only [hA2, hA2lam]
    have h4 : X / (69 / 100) ≤ (602 / 100 * L + 20) / (69 / 100) :=
      div_le_div_of_nonneg_right h3 (by norm_num)
    have h5 : (602 / 100 * L + 20) / (69 / 100) + 1 ≤ 873 / 100 * L + 30 := by
      rw [div_add_one (by norm_num), div_le_iff₀ (by norm_num)]; linarith only [hL8]
    linarith
  have hn₀le : 50 * (ℓ₀ + 1) * L ≤ n₀ + 1 := by
    have h1 : δ ^ 2 / (4 * lam) < n₀ + 1 := Nat.lt_floor_add_one _
    have h2 : 50 * (ℓ₀ + 1) * L ≤ δ ^ 2 / (4 * lam) := by
      rw [le_div_iff₀ (by positivity)]
      have h3 : 50 * (ℓ₀ + 1) * L * (4 * lam) = κ * (200 * (ℓ₀ + 1)) := by
        rw [← hlamL]; ring
      rw [h3]
      have h4 : δ₀ ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ hδ₀.le hδ 2
      linarith only [hκ₀', h4]
    linarith only [h1, h2]
  have hMℓ : (M : ℝ) * ℓ ≤ (873 / 100 * L + 30) * ℓ₀ :=
    mul_le_mul hMle hℓℓ₀ hℓ0 (by positivity)
  have hn₀l : (50 * (ℓ₀ + 1) * L) / 3 ≤ (n₀ + 1) * Real.log (3 / 2) := by
    have := mul_le_mul hn₀le hl32 (by norm_num) (by positivity)
    linarith only [this]
  have hfin : (873 / 100 * L + 30) * ℓ₀ + 234 / 100 * L + 8 < 50 * (ℓ₀ + 1) * L / 3 := by
    have h1 : 8 * ℓ₀ ≤ L * ℓ₀ := mul_le_mul_of_nonneg_right hL8 hℓ₀0
    nlinarith only [h1, hL8, hℓ₀0]
  linarith only [hfin, hn₀l, hlogs, hMℓ, hc₁le]

/-- The same with the height threshold `t₁ = e^{max(K₀, 8)}` packaged existentially. -/
theorem exists_re_xiSliceHeatTransfer_neg_of_slice_zero {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hδ₀2 : δ₀ ≤ 1 / 2) :
    ∃ t₁ : ℝ, 16 ≤ t₁ ∧ ∀ t : ℝ, t₁ ≤ t → ∀ δ : ℝ, δ₀ ≤ δ → xiSliceReal t δ = 0 →
      ∀ κ : ℝ, 0 < κ → κ ≤ kklDetectionRate δ₀ →
        ∃ n : ℕ, (DeBruijn.xiSliceHeatTransfer (κ / Real.log t) 0 t n).re < 0 :=
  ⟨Real.exp (max xiSliceGlobalConstant 8), sixteen_le_exp_max _,
    fun _ ht _ hδ hzero _ hκ hκ₀ => re_xiSliceHeatTransfer_neg_of_slice_zero hδ₀ hδ₀2 ht hδ hzero hκ hκ₀⟩

/-! ## Detection at the linear scale under regular local growth -/

/-- **Detection under a relative growth bound.**  Let `f_t(δ) = 0` with `δ > 0`, `16λ ≤ 1`, and suppose
the heated slice grows from `δ/2` at most like `H(R) ≤ C H(δ/2) e^{αR + βR²}` (`C > 0`, `β ≥ 0`,
`256βλ ≤ 1`).  If `log(6C) + 2αδ + 8βδ² + 32α²λ < (δ²/(4λ)) log(3/2)`, then some `T_n(λ, 0, t)` has
negative real part. -/
theorem re_xiSliceHeatTransfer_neg_of_relative_growth {t lam δ C α β : ℝ} (ht : 16 ≤ t)
    (hlam : 0 < lam) (hlam16 : 16 * lam ≤ 1) (hδ : 0 < δ) (hzero : xiSliceReal t δ = 0)
    (hC : 0 < C) (hβ : 0 ≤ β) (hβlam : 256 * β * lam ≤ 1)
    (hgr : ∀ R : ℝ, 0 < R →
      (∫ w : ℝ, Real.exp (-(w ^ 2 / 2)) * xiSliceReal t (Real.sqrt lam * w + R))
          / Real.sqrt (2 * Real.pi)
        ≤ C * ((∫ w : ℝ, Real.exp (-(w ^ 2 / 2)) * xiSliceReal t (Real.sqrt lam * w + δ / 2))
          / Real.sqrt (2 * Real.pi)) * Real.exp (α * R + β * R ^ 2))
    (hbig : Real.log (6 * C) + 2 * α * δ + 8 * β * δ ^ 2 + 32 * α ^ 2 * lam
      < δ ^ 2 / (4 * lam) * Real.log (3 / 2)) :
    ∃ n : ℕ, (DeBruijn.xiSliceHeatTransfer lam 0 t n).re < 0 := by
  by_contra hcon
  push Not at hcon
  set H₀ := (∫ w : ℝ, Real.exp (-(w ^ 2 / 2)) * xiSliceReal t (Real.sqrt lam * w + δ / 2))
    / Real.sqrt (2 * Real.pi) with hH₀
  set c₁ := 2 * α * δ + 8 * β * δ ^ 2 + 32 * α ^ 2 * lam with hc₁
  set n₀ := ⌊δ ^ 2 / (4 * lam)⌋₊ with hn₀
  have hδ2 : δ ≤ 1 / 2 := by
    by_contra h
    push Not at h
    exact (xiSliceReal_pos t h).ne' hzero
  have hH₀ : 0 < H₀ := by
    have hF := xiSliceReal_pos t (show (1 / 2 : ℝ) < 3 / 2 by norm_num)
    refine lt_of_lt_of_le ?_ (heatSeries_half_ge ht hlam hlam16 hδ (by linarith) hcon)
    exact mul_pos (pow_pos (by positivity) _) (by positivity)
  have hupp := heatSeries_half_le_of_growth hlam hδ hzero (mul_pos hC hH₀).le hβ hβlam hgr hcon
  have h1 : 1 ≤ 6 * C * Real.exp c₁ * (2 / 3) ^ (n₀ + 1) := by
    have h : 1 * H₀ ≤ (6 * C * Real.exp c₁ * (2 / 3) ^ (n₀ + 1)) * H₀ := by
      rw [one_mul]; refine hupp.trans (le_of_eq ?_); ring
    exact le_of_mul_le_mul_right h hH₀
  have h23 : (2 / 3 : ℝ) ^ (n₀ + 1) = Real.exp (-((n₀ + 1 : ℕ) * Real.log (3 / 2))) := by
    rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num), ← inv_pow]; norm_num
  rw [h23, ← Real.exp_log (show 0 < 6 * C by positivity), ← Real.exp_add, ← Real.exp_add,
    Real.one_le_exp_iff] at h1
  have hn : δ ^ 2 / (4 * lam) < ((n₀ + 1 : ℕ) : ℝ) := by
    push_cast; exact Nat.lt_floor_add_one _
  have hl : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  nlinarith [mul_lt_mul_of_pos_right hn hl]

/-- **Linear-scale detection unless the heated slice grows anomalously.**  Let `t ≥ 16`, `L = log t`,
`f_t(δ) = 0` with `δ > 0`, and `c, B ≥ 0`, `C > 0`.  Let `0 < κ ≤ δ/(96(c+1))`, `256Bκ ≤ L`,
`16κ ≤ L`, `log(6C) + 8Bδ² < 8δL`.  If the heated slice at heat `λ = κ/L` satisfies the regular growth
bound `H(R) ≤ C H(δ/2) e^{cLR + BR²}` for all `R > 0`, then some `T_n(κ/L, 0, t)` has negative real
part.

So an off-line zero of offset `δ` is detected at heat `≍ δ/log t`, linear in `δ`, unless the heated slice
at `δ/2` is anomalously small compared with its growth rate `≍ log t`.  The unconditional detection
scale `δ²/log(3/δ)` of `re_xiSliceHeatTransfer_neg_of_slice_zero` pays for exactly this possibility
through the three-radii lower bound. -/
theorem re_xiSliceHeatTransfer_neg_of_regular_growth {t δ κ C c B : ℝ} (ht : 16 ≤ t)
    (hδ : 0 < δ) (hzero : xiSliceReal t δ = 0) (hC : 0 < C) (hc : 0 ≤ c) (hB : 0 ≤ B)
    (hκ : 0 < κ) (hκδ : κ ≤ δ / (96 * (c + 1))) (hκB : 256 * B * κ ≤ Real.log t)
    (hκ16 : 16 * κ ≤ Real.log t)
    (hCδ : Real.log (6 * C) + 8 * B * δ ^ 2 < 8 * δ * Real.log t)
    (hgr : ∀ R : ℝ, 0 < R →
      (∫ w : ℝ, Real.exp (-(w ^ 2 / 2)) * xiSliceReal t (Real.sqrt (κ / Real.log t) * w + R))
          / Real.sqrt (2 * Real.pi)
        ≤ C * ((∫ w : ℝ, Real.exp (-(w ^ 2 / 2))
            * xiSliceReal t (Real.sqrt (κ / Real.log t) * w + δ / 2)) / Real.sqrt (2 * Real.pi))
          * Real.exp (c * Real.log t * R + B * R ^ 2)) :
    ∃ n : ℕ, (DeBruijn.xiSliceHeatTransfer (κ / Real.log t) 0 t n).re < 0 := by
  set L := Real.log t with hL
  have hL0 : 0 < L := Real.log_pos (by linarith)
  set lam := κ / L with hlamdef
  have hlam : 0 < lam := div_pos hκ hL0
  have hlamL : lam * L = κ := by rw [hlamdef]; field_simp
  refine re_xiSliceHeatTransfer_neg_of_relative_growth ht hlam ?_ hδ hzero hC hB ?_ hgr ?_
  · rw [hlamdef, mul_div_assoc', div_le_one hL0]; linarith
  · rw [hlamdef, mul_div_assoc', div_le_one hL0]; linarith
  · have hc1 : 0 < c + 1 := by linarith
    have hκδ' : κ * (96 * (c + 1)) ≤ δ := by rwa [le_div_iff₀ (by positivity)] at hκδ
    have hl32 : (1 : ℝ) / 3 ≤ Real.log (3 / 2) := by
      have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 3 / 2 by norm_num)
      norm_num at this ⊢; linarith
    -- the right side is at least `8(c+1)δL`
    have hR : 8 * (c + 1) * δ * L ≤ δ ^ 2 / (4 * lam) * Real.log (3 / 2) := by
      have e : δ ^ 2 / (4 * lam) = δ ^ 2 * L / (4 * κ) := by
        rw [← hlamL]; field_simp
      rw [e]
      have h1 : 8 * (c + 1) * δ * L ≤ δ ^ 2 * L / (4 * κ) / 3 := by
        rw [div_div, le_div_iff₀ (by positivity)]
        have := mul_le_mul_of_nonneg_left hκδ' (show 0 ≤ δ * L by positivity)
        nlinarith
      have h2 : δ ^ 2 * L / (4 * κ) / 3 ≤ δ ^ 2 * L / (4 * κ) * Real.log (3 / 2) := by
        rw [div_eq_mul_one_div (δ ^ 2 * L / (4 * κ)) 3]
        exact mul_le_mul_of_nonneg_left hl32 (by positivity)
      linarith
    -- the left side
    have hα : 32 * (c * L) ^ 2 * lam ≤ c * δ * L / 3 := by
      have e : 32 * (c * L) ^ 2 * lam = 32 * c ^ 2 * L * κ := by rw [← hlamL]; ring
      rw [e]
      have h1 : 96 * c * κ ≤ δ := by
        have := mul_le_mul_of_nonneg_left (show 96 * c ≤ 96 * (c + 1) by linarith) hκ.le
        linarith
      have := mul_le_mul_of_nonneg_left h1 (show 0 ≤ c * L / 3 by positivity)
      nlinarith
    have e1 : 2 * (c * L) * δ = 2 * (c * δ * L) := by ring
    have e2 : 8 * (c + 1) * δ * L = 8 * (c * δ * L) + 8 * δ * L := by ring
    have hcδL : 0 ≤ c * δ * L := by positivity
    rw [e1]; rw [e2] at hR
    linarith

/-- At a zero `ρ` of `ξ` the real slice at height `Im ρ` vanishes at `Re ρ − ½`. -/
theorem xiSliceReal_offset_eq_zero {ρ : ℂ} (hρ : xi ρ = 0) : xiSliceReal ρ.im (ρ.re - 1 / 2) = 0 := by
  unfold xiSliceReal
  have e : (((1 / 2 + (ρ.re - 1 / 2) : ℝ) : ℂ) + (ρ.im : ℂ) * I) = ρ := by
    apply Complex.ext <;> simp
  rw [e, hρ, norm_zero]
  norm_num

namespace DeBruijn

/-- **Heat rate excludes zeros.**  For `δ₀ ∈ (0, ½]` there is `t₁` such that: if
`T_{2m}(κ/log t, 0, t) > 0` for all `t ≥ t₀` and all `m`, with `0 < κ ≤ κ₀(δ₀)`, then every zero of `ξ`
with `Im ρ ≥ max(t₀, t₁)` has `Re ρ < ½ + δ₀`. -/
theorem re_lt_of_heat_rate_pos {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (hδ₀2 : δ₀ ≤ 1 / 2) :
    ∃ t₁ : ℝ, 16 ≤ t₁ ∧ ∀ κ t₀ : ℝ, 0 < κ → κ ≤ kklDetectionRate δ₀ →
      (∀ t : ℝ, t₀ ≤ t → ∀ m : ℕ, 0 < xiSliceHeatTransfer (κ / Real.log t) 0 t (2 * m)) →
      ∀ ρ : ℂ, xi ρ = 0 → max t₀ t₁ ≤ ρ.im → ρ.re < 1 / 2 + δ₀ := by
  obtain ⟨t₁, ht₁, hdet⟩ := exists_re_xiSliceHeatTransfer_neg_of_slice_zero hδ₀ hδ₀2
  refine ⟨t₁, ht₁, fun κ t₀ hκ hκ₀ hpos ρ hρ hγ => ?_⟩
  by_contra hre
  push Not at hre
  have hγ₁ : t₁ ≤ ρ.im := le_trans (le_max_right _ _) hγ
  obtain ⟨n, hn⟩ := hdet ρ.im hγ₁ (ρ.re - 1 / 2) (by linarith) (xiSliceReal_offset_eq_zero hρ) κ hκ
    hκ₀
  have hlam : 0 ≤ κ / Real.log ρ.im := div_nonneg hκ.le (Real.log_nonneg (by linarith))
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · have h := hpos ρ.im (le_trans (le_max_left _ _) hγ) m
    have := (Complex.lt_def.mp h).1
    simp only [Complex.zero_re] at this
    linarith
  · rw [xiSliceHeatTransfer_odd_eq_zero hlam] at hn
    simp at hn

/-- **Heat rate zero gives `Θ = ½` along the heights.**  If for every `κ > 0` the heated slice
coefficients `T_{2m}(κ/log t, 0, t)` are positive from some height on, then for every `δ₀ > 0` the
zeros of `ξ` with `Re ρ ≥ ½ + δ₀` have bounded imaginary part. -/
theorem exists_im_le_of_heat_rate_zero
    (h : ∀ κ : ℝ, 0 < κ → ∃ t₀ : ℝ, ∀ t : ℝ, t₀ ≤ t → ∀ m : ℕ,
      0 < xiSliceHeatTransfer (κ / Real.log t) 0 t (2 * m))
    {δ₀ : ℝ} (hδ₀ : 0 < δ₀) :
    ∃ T : ℝ, ∀ ρ : ℂ, xi ρ = 0 → 1 / 2 + δ₀ ≤ ρ.re → ρ.im ≤ T := by
  set δ₁ := min δ₀ (1 / 2) with hδ₁
  have hδ₁0 : 0 < δ₁ := lt_min hδ₀ (by norm_num)
  have hδ₁2 : δ₁ ≤ 1 / 2 := min_le_right _ _
  obtain ⟨t₁, -, hrec⟩ := re_lt_of_heat_rate_pos hδ₁0 hδ₁2
  obtain ⟨t₀, ht₀⟩ := h _ (kklDetectionRate_pos hδ₁0 hδ₁2)
  refine ⟨max t₀ t₁, fun ρ hρ hre => ?_⟩
  by_contra hT
  push Not at hT
  have := hrec _ t₀ (kklDetectionRate_pos hδ₁0 hδ₁2) le_rfl ht₀ ρ hρ hT.le
  have : δ₁ ≤ δ₀ := min_le_left _ _
  linarith

/-- **An off-line zero bounds the WD heat threshold from below at the Ki–Kim–Lee scale.**  For
`δ₀ ∈ (0, ½]` there is `t₁` such that every zero of `ξ` with `Re ρ ≥ ½ + δ₀` and `Im ρ ≥ t₁` gives
`λ_WD ≥ κ₀(δ₀)/log Im ρ`. -/
theorem le_wdHeatThreshold_of_offLine_zero {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (hδ₀2 : δ₀ ≤ 1 / 2) :
    ∃ t₁ : ℝ, 16 ≤ t₁ ∧ ∀ ρ : ℂ, xi ρ = 0 → 1 / 2 + δ₀ ≤ ρ.re → t₁ ≤ ρ.im →
      kklDetectionRate δ₀ / Real.log ρ.im ≤ wdHeatThreshold := by
  obtain ⟨t₁, ht₁, hdet⟩ := exists_re_xiSliceHeatTransfer_neg_of_slice_zero hδ₀ hδ₀2
  refine ⟨t₁, ht₁, fun ρ hρ hre hγ => ?_⟩
  have hL : 0 < Real.log ρ.im := Real.log_pos (by linarith)
  have hκ₀ := kklDetectionRate_pos hδ₀ hδ₀2
  refine le_csInf ⟨1 / 8, eighth_mem_wdHeatAdmissible⟩ fun lam hlam => ?_
  by_contra hlt
  push Not at hlt
  set lam' := max lam (kklDetectionRate δ₀ / (2 * Real.log ρ.im)) with hlam'
  have hlam'0 : 0 < lam' := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  have hlam'lt : lam' < kklDetectionRate δ₀ / Real.log ρ.im := by
    refine max_lt hlt ?_
    rw [div_lt_div_iff₀ (by positivity) hL]; nlinarith
  have hadm : ∀ t : ℝ, ∀ n : ℕ, 0 ≤ xiSliceHeatTransfer lam' 0 t n :=
    xiSliceHeatTransfer_nonneg_of_le (le_max_left _ _) hlam
  set κ := lam' * Real.log ρ.im with hκ
  have hκ0 : 0 < κ := by positivity
  have hκle : κ ≤ kklDetectionRate δ₀ := by
    rw [hκ]; rw [lt_div_iff₀ hL] at hlam'lt; linarith
  obtain ⟨n, hn⟩ := hdet ρ.im hγ (ρ.re - 1 / 2) (by linarith) (xiSliceReal_offset_eq_zero hρ) κ hκ0
    hκle
  rw [show κ / Real.log ρ.im = lam' by rw [hκ]; field_simp] at hn
  exact absurd (Complex.nonneg_iff.mp (hadm ρ.im n)).1 (not_le.mpr hn)

/-- **An off-line zero bounds the de Bruijn–Newman constant from below.**  For `δ₀ ∈ (0, ½]` there is
`t₁` such that every zero of `ξ` with `Re ρ ≥ ½ + δ₀` and `Im ρ ≥ t₁` gives
`Λ ≥ κ₀(δ₀)/log Im ρ`. -/
theorem le_newmanConstant_of_offLine_zero {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (hδ₀2 : δ₀ ≤ 1 / 2) :
    ∃ t₁ : ℝ, 16 ≤ t₁ ∧ ∀ ρ : ℂ, xi ρ = 0 → 1 / 2 + δ₀ ≤ ρ.re → t₁ ≤ ρ.im →
      kklDetectionRate δ₀ / Real.log ρ.im ≤ newmanConstant := by
  obtain ⟨t₁, ht₁, h⟩ := le_wdHeatThreshold_of_offLine_zero hδ₀ hδ₀2
  exact ⟨t₁, ht₁, fun ρ hρ hre hγ => (h ρ hρ hre hγ).trans wdHeatThreshold_le_newmanConstant⟩

/-- **Every off-line zero above `e^{max(K₀, 8)}` bounds `Λ` from below.**  Every zero `ρ` of `ξ` with
`Re ρ > ½` and `Im ρ ≥ e^{max(K₀, 8)}` gives `Λ ≥ κ₀(δ)/log Im ρ`, `δ = min(Re ρ − ½, ½)`. -/
theorem le_newmanConstant_of_offLine_zero_of_le {ρ : ℂ} (hρ : xi ρ = 0) (hre : 1 / 2 < ρ.re)
    (hγ : Real.exp (max xiSliceGlobalConstant 8) ≤ ρ.im) :
    kklDetectionRate (min (ρ.re - 1 / 2) (1 / 2)) / Real.log ρ.im ≤ newmanConstant := by
  set δ₀ := min (ρ.re - 1 / 2) (1 / 2) with hδ₀
  have hδ₀0 : 0 < δ₀ := lt_min (by linarith) (by norm_num)
  have hδ₀2 : δ₀ ≤ 1 / 2 := min_le_right _ _
  have h16 := (sixteen_le_exp_max xiSliceGlobalConstant).trans hγ
  have hL : 0 < Real.log ρ.im := Real.log_pos (by linarith)
  have hκ₀ := kklDetectionRate_pos hδ₀0 hδ₀2
  refine le_trans ?_ wdHeatThreshold_le_newmanConstant
  refine le_csInf ⟨1 / 8, eighth_mem_wdHeatAdmissible⟩ fun lam hlam => ?_
  by_contra hlt
  push Not at hlt
  set lam' := max lam (kklDetectionRate δ₀ / (2 * Real.log ρ.im)) with hlam'
  have hlam'0 : 0 < lam' := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  have hlam'lt : lam' < kklDetectionRate δ₀ / Real.log ρ.im := by
    refine max_lt hlt ?_
    rw [div_lt_div_iff₀ (by positivity) hL]; nlinarith
  have hadm : ∀ t : ℝ, ∀ n : ℕ, 0 ≤ xiSliceHeatTransfer lam' 0 t n :=
    xiSliceHeatTransfer_nonneg_of_le (le_max_left _ _) hlam
  set κ := lam' * Real.log ρ.im with hκ
  have hκ0 : 0 < κ := by positivity
  have hκle : κ ≤ kklDetectionRate δ₀ := by
    rw [hκ]; rw [lt_div_iff₀ hL] at hlam'lt; linarith
  obtain ⟨n, hn⟩ := re_xiSliceHeatTransfer_neg_of_slice_zero hδ₀0 hδ₀2 hγ
    (δ := ρ.re - 1 / 2) (min_le_left _ _) (xiSliceReal_offset_eq_zero hρ) hκ0 hκle
  rw [show κ / Real.log ρ.im = lam' by rw [hκ]; field_simp] at hn
  exact absurd (Complex.nonneg_iff.mp (hadm ρ.im n)).1 (not_le.mpr hn)

end DeBruijn

/-! ## The explicit height threshold -/

/-- `Λ(m)/m² ≤ 4/√(m−1) − 4/√m` for `m ≥ 2`, from `Λ(m) ≤ log m ≤ 2√m`. -/
theorem vonMangoldt_div_sq_le_telescope {m : ℕ} (hm : 2 ≤ m) :
    ArithmeticFunction.vonMangoldt m / (m : ℝ) ^ 2
      ≤ 4 / Real.sqrt ((m : ℝ) - 1) - 4 / Real.sqrt m := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  set a := Real.sqrt ((m : ℝ) - 1) with ha
  set b := Real.sqrt (m : ℝ) with hb
  have ha0 : 0 < a := Real.sqrt_pos.mpr (by linarith)
  have hb0 : 0 < b := Real.sqrt_pos.mpr (by linarith)
  have ha2 : a ^ 2 = m - 1 := Real.sq_sqrt (by linarith)
  have hb2 : b ^ 2 = m := Real.sq_sqrt (by linarith)
  have hab : a ≤ b := Real.sqrt_le_sqrt (by linarith)
  have hlog : ArithmeticFunction.vonMangoldt m ≤ 2 * b := by
    refine ArithmeticFunction.vonMangoldt_le_log.trans ?_
    have h := Real.log_le_rpow_div (x := (m : ℝ)) (ε := 1 / 2) (by linarith) (by norm_num)
    rw [← Real.sqrt_eq_rpow, show Real.sqrt (m : ℝ) / (1 / 2) = 2 * Real.sqrt m by ring] at h
    rw [hb]; exact h
  have hm2 : (m : ℝ) ^ 2 = b ^ 4 := by rw [← hb2]; ring
  have hstep1 : ArithmeticFunction.vonMangoldt m / (m : ℝ) ^ 2 ≤ 2 / b ^ 3 := by
    rw [hm2, div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul_of_nonneg_right hlog (by positivity : (0 : ℝ) ≤ b ^ 3)
    nlinarith
  have hstep2 : 4 / a - 4 / b = 4 / (a * b * (a + b)) := by
    rw [div_sub_div _ _ ha0.ne' hb0.ne', div_eq_div_iff (by positivity) (by positivity)]
    have h1 : b ^ 2 - a ^ 2 = 1 := by rw [ha2, hb2]; ring
    linear_combination (4 * a * b) * h1
  have hstep3 : 2 / b ^ 3 ≤ 4 / (a * b * (a + b)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : a * b * (a + b) ≤ b * b * (b + b) := by
      have := mul_le_mul_of_nonneg_right hab hb0.le
      have h2 : a + b ≤ b + b := by linarith
      calc a * b * (a + b) ≤ b * b * (a + b) := by nlinarith
        _ ≤ b * b * (b + b) := mul_le_mul_of_nonneg_left h2 (by positivity)
    nlinarith
  linarith [hstep1, hstep2, hstep3]

theorem sum_range_vonMangoldt_div_sq_le (N : ℕ) :
    ∑ n ∈ Finset.range (N + 2), ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ 2
      ≤ 4 - 4 / Real.sqrt ((N : ℝ) + 1) := by
  induction N with
  | zero => simp [Finset.sum_range_succ, ArithmeticFunction.vonMangoldt_apply_one]
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have h := vonMangoldt_div_sq_le_telescope (m := N + 2) (by omega)
    have e1 : ((N + 2 : ℕ) : ℝ) = (N : ℝ) + 2 := by push_cast; ring
    rw [e1, show (N : ℝ) + 2 - 1 = (N : ℝ) + 1 by ring] at h
    push_cast
    rw [show (N : ℝ) + 1 + 1 = (N : ℝ) + 2 by ring]
    linarith

/-- `Σ Λ(n)/n² ≤ 4`. -/
theorem vonMangoldtSquareMass_le_four : vonMangoldtSquareMass ≤ 4 := by
  unfold vonMangoldtSquareMass
  refine Real.tsum_le_of_sum_range_le
    (fun n => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)) fun n => ?_
  have hnn : ∀ i ∈ Finset.range (n + 2), i ∉ Finset.range n →
      0 ≤ ArithmeticFunction.vonMangoldt i / (i : ℝ) ^ 2 :=
    fun i _ _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) hnn).trans ?_
  refine (sum_range_vonMangoldt_div_sq_le n).trans ?_
  have : 0 ≤ 4 / Real.sqrt ((n : ℝ) + 1) := by positivity
  linarith

/-- `K₀ = 2(3 + Σ Λ(n)/n²) + log 6 ≤ 16`. -/
theorem xiSliceGlobalConstant_le_sixteen : xiSliceGlobalConstant ≤ 16 := by
  unfold xiSliceGlobalConstant xiLogDerivStirlingConstant
  have h1 := vonMangoldtSquareMass_le_four
  have h2 : Real.log 6 ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have := Real.exp_one_gt_d9
    have h3 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith
  linarith

theorem exp_max_xiSliceGlobalConstant_le : Real.exp (max xiSliceGlobalConstant 8) ≤ Real.exp 16 :=
  Real.exp_le_exp.mpr (max_le xiSliceGlobalConstant_le_sixteen (by norm_num))

namespace DeBruijn

/-- **Every off-line zero above height `e^{16}` bounds `Λ` from below.**  Every zero `ρ` of `ξ` with
`Re ρ > ½` and `Im ρ ≥ e^{16}` gives `Λ ≥ κ₀(δ)/log Im ρ`, `δ = min(Re ρ − ½, ½)`,
`κ₀(δ) = δ²/(200(log(3/δ) + 1))`. -/
theorem le_newmanConstant_of_offLine_zero_explicit {ρ : ℂ} (hρ : xi ρ = 0) (hre : 1 / 2 < ρ.re)
    (hγ : Real.exp 16 ≤ ρ.im) :
    kklDetectionRate (min (ρ.re - 1 / 2) (1 / 2)) / Real.log ρ.im ≤ newmanConstant :=
  le_newmanConstant_of_offLine_zero_of_le hρ hre (exp_max_xiSliceGlobalConstant_le.trans hγ)

end DeBruijn

end

end RHTower
