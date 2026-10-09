import GaloisForLFunctions.RHTower.RiemannKernelComplexStrip
import GaloisForLFunctions.HTGeometry.ThetaSumPeriodParseval

/-!
# Riemann's kernel near its natural boundary: flat theta bounds

On the line `Im z = c`, `0 ≤ c < π/4`, write `z = u + ic`, `x(u) = −e^{2u} sin 2c` and
`y(u) = e^{2u} cos 2c`. Then `−πn²e^{2z} = −πn²y + iπn²x`, so Riemann's kernel is a theta
expression in `τ = x + iy` (`kernelC_line_eq`):

  `Φ(u + ic) = e^{z/2}(4π²e^{4z} S₄(τ) − 6π e^{2z} S₂(τ))`,  `S_k(τ) = Σ n^k e^{iπn²τ}`,

and `|Φ|² ≍ e^{9u}|S₄|²` up to `e^{5u}|S₂|²` (`norm_sq_kernelC_line_le`, `norm_sq_kernelC_line_ge`).
As `c → π/4` the point `τ` approaches the real axis along the ray `y = −x cot 2c`. The change of
variables `x = x(u)` (`integral_comp_lineRe`) and Parseval over periods of `x`
(`HTGeometry.ThetaSumPeriodParseval`) make `|Φ(u + ic)|²` flat in `u` at height `(cos 2c)^{-9/2}`:

* **upper bound on every unit window** `U ≥ 0` (`integral_norm_sq_kernelC_line_le`):
  `∫_U^{U+1}|Φ(u+ic)|²du ≤ C (cos 2c)^{-4}/√(cos 2c)`;
* **lower bound on one window** (`exists_integral_norm_sq_kernelC_line_ge`):
  `∫_{U₀}^{U₀+1}|Φ(u+ic)|²du ≥ c₀ (cos 2c)^{-4}/√(cos 2c)` once `cos 2c` is small;
* **symmetry** (`norm_kernelC_neg_line`): `|Φ(−u+ic)| = |Φ(u+ic)|`, since `Φ` is even and real.

This is the flat mean-square spectrum of Hardy's `Z` seen at the boundary of the theta upper
half-plane: the frequencies `πn²` are distinct, so the `L²` mass over a period is the sum of the
squared coefficients.
-/

open Complex Polynomial MeasureTheory
open scoped Real
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower.KernelStrip

/-- `x(u) = −e^{2u} sin 2c`, the real part of `τ` on the line `Im z = c`. -/
def lineRe (c u : ℝ) : ℝ := -(Real.exp (2 * u) * Real.sin (2 * c))

/-- `y(u) = e^{2u} cos 2c`, the imaginary part of `τ` on the line `Im z = c`. -/
def lineIm (c u : ℝ) : ℝ := Real.exp (2 * u) * Real.cos (2 * c)

theorem aeval_riemannCuspPoly (w : ℂ) :
    aeval w riemannCuspPoly = (4 * π ^ 2 : ℂ) * w ^ 2 - (6 * π : ℂ) * w := by
  simp only [riemannCuspPoly, cuspDeriv, map_sub, map_add, map_mul, aeval_C, aeval_X,
    derivative_mul, derivative_C, derivative_X, derivative_one, map_zero, mul_one, mul_zero,
    zero_add, add_zero, zero_mul, Complex.coe_algebraMap]
  push_cast
  ring

theorem cexp_two_mul_line (c u : ℝ) :
    cexp (2 * ((u : ℂ) + c * I)) =
      (Real.exp (2 * u) : ℂ) * ((Real.cos (2 * c) : ℂ) + (Real.sin (2 * c) : ℂ) * I) := by
  have h : 2 * ((u : ℂ) + c * I) = ((2 * u : ℝ) : ℂ) + ((2 * c : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [h, Complex.exp_add, Complex.exp_mul_I, ← Complex.ofReal_exp, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin]

/-- `e^{-πm²e^{2z}} = e^{-πm²y} e^{iπm²x}` on the line `z = u + ic`. -/
theorem cexp_neg_pi_line (c u : ℝ) (m : ℕ) :
    cexp (-(π : ℂ) * ((m : ℂ) ^ 2 * cexp (2 * ((u : ℂ) + c * I)))) =
      ((Real.exp (-π * m ^ 2 * lineIm c u) : ℝ) : ℂ) * thetaWave m (lineRe c u) := by
  rw [cexp_two_mul_line, thetaWave, Complex.ofReal_exp (-π * m ^ 2 * lineIm c u),
    ← Complex.exp_add]
  congr 1
  simp only [lineIm, lineRe]
  push_cast
  ring

/-- The `m`-th coefficient of `S_k`. -/
def lineCoeff (k : ℕ) (c u : ℝ) (m : ℕ) : ℂ :=
  (((m : ℝ) ^ k * Real.exp (-π * m ^ 2 * lineIm c u) : ℝ) : ℂ) * thetaWave m (lineRe c u)

theorem cterm_line (c u : ℝ) (m : ℕ) :
    cterm riemannCuspPoly m ((u : ℂ) + c * I) =
      cexp (((u : ℂ) + c * I) / 2) * (4 * π ^ 2 : ℂ) * cexp (4 * ((u : ℂ) + c * I)) *
          lineCoeff 4 c u m -
        cexp (((u : ℂ) + c * I) / 2) * (6 * π : ℂ) * cexp (2 * ((u : ℂ) + c * I)) *
          lineCoeff 2 c u m := by
  unfold cterm lineCoeff
  rw [aeval_riemannCuspPoly, cexp_neg_pi_line]
  have h4 : cexp (4 * ((u : ℂ) + c * I)) = cexp (2 * ((u : ℂ) + c * I)) ^ 2 := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  rw [h4]
  push_cast
  ring

theorem summable_lineCoeff (k : ℕ) {c : ℝ} (hc : 0 < Real.cos (2 * c)) (u : ℝ) :
    Summable (lineCoeff k c u) := by
  have hy : 0 < lineIm c u := mul_pos (Real.exp_pos _) hc
  refine Summable.of_norm ?_
  have := summable_norm_thetaMoment_coeff k hy
  refine this.congr fun n => ?_
  simp [lineCoeff, norm_thetaWave]

theorem thetaMoment_line_eq_tsum_succ (k : ℕ) (hk : 1 ≤ k) {c : ℝ} (hc : 0 < Real.cos (2 * c))
    (u : ℝ) :
    thetaMoment k (lineIm c u) (lineRe c u) = ∑' n : ℕ, lineCoeff k c u (n + 1) := by
  have h := (summable_lineCoeff k hc u).tsum_eq_zero_add
  have h0 : lineCoeff k c u 0 = 0 := by
    simp [lineCoeff]; left; omega
  rw [h0, zero_add] at h
  exact h

/-- **Theta form of Riemann's kernel on the line `Im z = c`.** -/
theorem kernelC_line_eq {c : ℝ} (hc : 0 < Real.cos (2 * c)) (u : ℝ) :
    kernelC ((u : ℂ) + c * I) =
      cexp (((u : ℂ) + c * I) / 2) * (4 * π ^ 2 : ℂ) * cexp (4 * ((u : ℂ) + c * I)) *
          thetaMoment 4 (lineIm c u) (lineRe c u) -
        cexp (((u : ℂ) + c * I) / 2) * (6 * π : ℂ) * cexp (2 * ((u : ℂ) + c * I)) *
          thetaMoment 2 (lineIm c u) (lineRe c u) := by
  have s4 : Summable fun n : ℕ => lineCoeff 4 c u (n + 1) :=
    (summable_lineCoeff 4 hc u).comp_injective (add_left_injective 1)
  have s2 : Summable fun n : ℕ => lineCoeff 2 c u (n + 1) :=
    (summable_lineCoeff 2 hc u).comp_injective (add_left_injective 1)
  have hsub := (s4.mul_left (cexp (((u : ℂ) + c * I) / 2) * (4 * π ^ 2 : ℂ) *
      cexp (4 * ((u : ℂ) + c * I)))).tsum_sub (s2.mul_left (cexp (((u : ℂ) + c * I) / 2) *
      (6 * π : ℂ) * cexp (2 * ((u : ℂ) + c * I))))
  rw [thetaMoment_line_eq_tsum_succ 4 (by norm_num) hc, thetaMoment_line_eq_tsum_succ 2
    (by norm_num) hc, ← tsum_mul_left, ← tsum_mul_left, ← hsub]
  unfold kernelC cseries
  refine tsum_congr fun n => ?_
  rw [cterm_line]


theorem norm_cexp_line_div_two (c u : ℝ) : ‖cexp (((u : ℂ) + c * I) / 2)‖ = Real.exp (u / 2) := by
  rw [Complex.norm_exp]; congr 1; simp

theorem norm_cexp_line_mul (a : ℕ) (c u : ℝ) :
    ‖cexp ((a : ℂ) * ((u : ℂ) + c * I))‖ = Real.exp (a * u) := by
  rw [Complex.norm_exp]; congr 1; simp

/-- `|Φ(u+ic)|² ≤ 32π⁴e^{9u}|S₄|² + 72π²e^{5u}|S₂|²`. -/
theorem norm_sq_kernelC_line_le {c : ℝ} (hc : 0 < Real.cos (2 * c)) (u : ℝ) :
    ‖kernelC ((u : ℂ) + c * I)‖ ^ 2 ≤
      32 * π ^ 4 * Real.exp (9 * u) * ‖thetaMoment 4 (lineIm c u) (lineRe c u)‖ ^ 2 +
        72 * π ^ 2 * Real.exp (5 * u) * ‖thetaMoment 2 (lineIm c u) (lineRe c u)‖ ^ 2 := by
  rw [kernelC_line_eq hc]
  set A := ‖thetaMoment 4 (lineIm c u) (lineRe c u)‖
  set B := ‖thetaMoment 2 (lineIm c u) (lineRe c u)‖
  have h4 := norm_cexp_line_mul 4 c u
  have h2 := norm_cexp_line_mul 2 c u
  push_cast at h4 h2
  have hn := norm_sub_le
    (cexp (((u : ℂ) + c * I) / 2) * (4 * π ^ 2 : ℂ) * cexp (4 * ((u : ℂ) + c * I)) *
      thetaMoment 4 (lineIm c u) (lineRe c u))
    (cexp (((u : ℂ) + c * I) / 2) * (6 * π : ℂ) * cexp (2 * ((u : ℂ) + c * I)) *
      thetaMoment 2 (lineIm c u) (lineRe c u))
  have hπ : ‖(π : ℂ)‖ = π := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  simp only [norm_mul, norm_pow, norm_cexp_line_div_two, h4, h2, hπ, Complex.norm_ofNat] at hn
  have e9 : Real.exp (9 * u) = (Real.exp (u / 2) * Real.exp (4 * u)) ^ 2 := by
    rw [← Real.exp_add, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have e5 : Real.exp (5 * u) = (Real.exp (u / 2) * Real.exp (2 * u)) ^ 2 := by
    rw [← Real.exp_add, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [e9, e5]
  set P := Real.exp (u / 2) * 4 * π ^ 2 * Real.exp (4 * u) * A
  set Q := Real.exp (u / 2) * 6 * π * Real.exp (2 * u) * B
  have hP : 0 ≤ P := by positivity
  have hQ : 0 ≤ Q := by positivity
  have hnorm := norm_nonneg (cexp (((u : ℂ) + c * I) / 2) * (4 * π ^ 2 : ℂ) *
      cexp (4 * ((u : ℂ) + c * I)) * thetaMoment 4 (lineIm c u) (lineRe c u) -
    cexp (((u : ℂ) + c * I) / 2) * (6 * π : ℂ) * cexp (2 * ((u : ℂ) + c * I)) *
      thetaMoment 2 (lineIm c u) (lineRe c u))
  have : P ^ 2 * 2 + Q ^ 2 * 2 = 32 * π ^ 4 * (Real.exp (u / 2) * Real.exp (4 * u)) ^ 2 * A ^ 2 +
      72 * π ^ 2 * (Real.exp (u / 2) * Real.exp (2 * u)) ^ 2 * B ^ 2 := by
    simp only [P, Q]; ring
  nlinarith [mul_self_le_mul_self hnorm hn, sq_nonneg (P - Q)]

/-- `|Φ(u+ic)|² ≥ 8π⁴e^{9u}|S₄|² − 36π²e^{5u}|S₂|²`. -/
theorem norm_sq_kernelC_line_ge {c : ℝ} (hc : 0 < Real.cos (2 * c)) (u : ℝ) :
    8 * π ^ 4 * Real.exp (9 * u) * ‖thetaMoment 4 (lineIm c u) (lineRe c u)‖ ^ 2 -
        36 * π ^ 2 * Real.exp (5 * u) * ‖thetaMoment 2 (lineIm c u) (lineRe c u)‖ ^ 2 ≤
      ‖kernelC ((u : ℂ) + c * I)‖ ^ 2 := by
  rw [kernelC_line_eq hc]
  set A := ‖thetaMoment 4 (lineIm c u) (lineRe c u)‖
  set B := ‖thetaMoment 2 (lineIm c u) (lineRe c u)‖
  have h4 := norm_cexp_line_mul 4 c u
  have h2 := norm_cexp_line_mul 2 c u
  push_cast at h4 h2
  have hn := norm_sub_norm_le
    (cexp (((u : ℂ) + c * I) / 2) * (4 * π ^ 2 : ℂ) * cexp (4 * ((u : ℂ) + c * I)) *
      thetaMoment 4 (lineIm c u) (lineRe c u))
    (cexp (((u : ℂ) + c * I) / 2) * (6 * π : ℂ) * cexp (2 * ((u : ℂ) + c * I)) *
      thetaMoment 2 (lineIm c u) (lineRe c u))
  have hπ : ‖(π : ℂ)‖ = π := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  simp only [norm_mul, norm_pow, norm_cexp_line_div_two, h4, h2, hπ, Complex.norm_ofNat] at hn
  have e9 : Real.exp (9 * u) = (Real.exp (u / 2) * Real.exp (4 * u)) ^ 2 := by
    rw [← Real.exp_add, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have e5 : Real.exp (5 * u) = (Real.exp (u / 2) * Real.exp (2 * u)) ^ 2 := by
    rw [← Real.exp_add, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [e9, e5]
  set P := Real.exp (u / 2) * (4 * π ^ 2) * Real.exp (4 * u) * A
  set Q := Real.exp (u / 2) * (6 * π) * Real.exp (2 * u) * B
  have hP : 0 ≤ P := by positivity
  set N := ‖cexp (((u : ℂ) + c * I) / 2) * (4 * π ^ 2 : ℂ) * cexp (4 * ((u : ℂ) + c * I)) *
      thetaMoment 4 (lineIm c u) (lineRe c u) -
    cexp (((u : ℂ) + c * I) / 2) * (6 * π : ℂ) * cexp (2 * ((u : ℂ) + c * I)) *
      thetaMoment 2 (lineIm c u) (lineRe c u)‖
  have hN : 0 ≤ N := norm_nonneg _
  have : 8 * π ^ 4 * (Real.exp (u / 2) * Real.exp (4 * u)) ^ 2 * A ^ 2 -
      36 * π ^ 2 * (Real.exp (u / 2) * Real.exp (2 * u)) ^ 2 * B ^ 2 = P ^ 2 / 2 - Q ^ 2 := by
    simp only [P, Q]; ring
  rw [this]
  rcases le_total P Q with h | h
  · nlinarith [mul_self_le_mul_self hP h, sq_nonneg N]
  · have hPQ : 0 ≤ P - Q := by linarith
    have : (P - Q) ^ 2 ≤ N ^ 2 := pow_le_pow_left₀ hPQ hn 2
    nlinarith [sq_nonneg (P - 2 * Q)]


/-! ## Change of variables `u ↦ x(u)` -/

theorem hasDerivAt_lineRe (c u : ℝ) : HasDerivAt (fun u => lineRe c u) (2 * lineRe c u) u := by
  unfold lineRe
  have h1 : HasDerivAt (fun u : ℝ => 2 * u) 2 u :=
    ((hasDerivAt_id u).const_mul 2).congr_deriv (mul_one _)
  have h2 := (((Real.hasDerivAt_exp (2 * u)).comp u h1).mul_const (Real.sin (2 * c))).neg
  refine h2.congr_deriv ?_
  ring

theorem lineRe_neg {c : ℝ} (hs : 0 < Real.sin (2 * c)) (u : ℝ) : lineRe c u < 0 := by
  unfold lineRe; have := Real.exp_pos (2 * u); nlinarith

theorem lineRe_antitone {c : ℝ} (hs : 0 < Real.sin (2 * c)) {u v : ℝ} (h : u ≤ v) :
    lineRe c v ≤ lineRe c u := by
  unfold lineRe
  have := Real.exp_le_exp.mpr (by linarith : 2 * u ≤ 2 * v)
  nlinarith

theorem lineIm_eq {c : ℝ} (hs : 0 < Real.sin (2 * c)) (u : ℝ) :
    lineIm c u = Real.cos (2 * c) / Real.sin (2 * c) * -lineRe c u := by
  unfold lineIm lineRe; field_simp

/-- **Change of variables** `x = −e^{2u} sin 2c`: `du = dx/(2x)`. -/
theorem integral_comp_lineRe {c : ℝ} (hs : 0 < Real.sin (2 * c)) {g : ℝ → ℝ} {U V : ℝ}
    (hUV : U ≤ V) (hg : ContinuousOn g (Set.Icc (lineRe c V) (lineRe c U))) :
    ∫ u in U..V, g (lineRe c u) = ∫ x in lineRe c V..lineRe c U, g x / (-2 * x) := by
  have himg : lineRe c '' Set.uIcc U V ⊆ Set.Icc (lineRe c V) (lineRe c U) := by
    rintro _ ⟨u, hu, rfl⟩
    rw [Set.uIcc_of_le hUV] at hu
    exact ⟨lineRe_antitone hs hu.2, lineRe_antitone hs hu.1⟩
  have hG : ContinuousOn (fun x => g x / (2 * x)) (lineRe c '' Set.uIcc U V) := by
    refine (hg.mono himg).div (continuousOn_const.mul continuousOn_id) fun x hx => ?_
    obtain ⟨u, _, rfl⟩ := hx
    exact mul_ne_zero two_ne_zero (lineRe_neg hs u).ne
  have hcont : ContinuousOn (fun u => 2 * lineRe c u) (Set.uIcc U V) := by
    unfold lineRe; fun_prop
  have hcv := intervalIntegral.integral_comp_mul_deriv' (f := fun u => lineRe c u)
    (f' := fun u => 2 * lineRe c u) (g := fun x => g x / (2 * x))
    (fun u _ => hasDerivAt_lineRe c u) hcont hG
  have hlhs : ∫ u in U..V, ((fun x => g x / (2 * x)) ∘ fun u => lineRe c u) u * (2 * lineRe c u) =
      ∫ u in U..V, g (lineRe c u) := by
    refine intervalIntegral.integral_congr fun u _ => ?_
    have := (lineRe_neg hs u).ne
    simp only [Function.comp_apply]
    field_simp
  rw [← hlhs, hcv, intervalIntegral.integral_symm, ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun x _ => ?_
  ring

/-! ## Flat window bounds -/

theorem exp_two_le : Real.exp 2 ≤ 37 / 5 := by
  have h := Real.exp_one_lt_d9
  have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  have h0 := Real.exp_pos 1
  rw [h2]; nlinarith

/-- The algebra of the window bound: `4Σ_k + 4δ²π²Σ_{k+2} ≤ 4R(k! + 121(k+2)!)/π^k` with
`R = y₀^{-k}/(2√y₀)`, once `δ ≤ 11y₀`. -/
theorem window_mass_le (k : ℕ) {y₀ δ Bk Bk2 : ℝ} (hy₀ : 0 < y₀) (hδ0 : 0 ≤ δ) (hδy : δ ≤ 11 * y₀)
    (hB2 : 0 ≤ Bk2)
    (hBk : Bk ≤ k.factorial / π ^ k * y₀⁻¹ ^ k * (1 / (2 * Real.sqrt y₀)))
    (hBk2 : Bk2 ≤ (k + 2).factorial / π ^ (k + 2) * y₀⁻¹ ^ (k + 2) * (1 / (2 * Real.sqrt y₀))) :
    4 * Bk + 4 * δ ^ 2 * π ^ 2 * Bk2 ≤
      4 * (y₀⁻¹ ^ k * (1 / (2 * Real.sqrt y₀))) * (k.factorial + 121 * (k + 2).factorial) / π ^ k := by
  set R : ℝ := y₀⁻¹ ^ k * (1 / (2 * Real.sqrt y₀)) with hR_def
  have hR : 0 ≤ R := by positivity
  have hpk : 0 < π ^ k := by positivity
  have hsq : δ ^ 2 ≤ 121 * y₀ ^ 2 :=
    calc δ ^ 2 ≤ (11 * y₀) ^ 2 := pow_le_pow_left₀ hδ0 hδy 2
      _ = 121 * y₀ ^ 2 := by ring
  have h1 : Bk ≤ k.factorial / π ^ k * R := by rw [hR_def, ← mul_assoc]; exact hBk
  have hpow : y₀ ^ 2 * y₀⁻¹ ^ (k + 2) = y₀⁻¹ ^ k := by
    have : y₀ ≠ 0 := hy₀.ne'
    rw [inv_pow, inv_pow, pow_add]; field_simp
  have h2 : δ ^ 2 * Bk2 ≤ 121 * ((k + 2).factorial / π ^ (k + 2)) * R :=
    calc δ ^ 2 * Bk2
        ≤ (121 * y₀ ^ 2) * ((k + 2).factorial / π ^ (k + 2) * y₀⁻¹ ^ (k + 2) *
            (1 / (2 * Real.sqrt y₀))) := mul_le_mul hsq hBk2 hB2 (by positivity)
      _ = 121 * ((k + 2).factorial / π ^ (k + 2)) * R := by rw [hR_def, ← hpow]; ring
  have hπ2 : π ^ 2 * ((k + 2).factorial / π ^ (k + 2)) = (k + 2).factorial / π ^ k := by
    rw [pow_add]; field_simp
  calc 4 * Bk + 4 * δ ^ 2 * π ^ 2 * Bk2
      = 4 * Bk + 4 * π ^ 2 * (δ ^ 2 * Bk2) := by ring
    _ ≤ 4 * (k.factorial / π ^ k * R) + 4 * π ^ 2 * (121 * ((k + 2).factorial / π ^ (k + 2)) * R) := by
        gcongr
    _ = 4 * R * (k.factorial + 121 * (k + 2).factorial) / π ^ k := by
        rw [show 4 * π ^ 2 * (121 * ((k + 2).factorial / π ^ (k + 2)) * R) =
          4 * 121 * R * (π ^ 2 * ((k + 2).factorial / π ^ (k + 2))) by ring, hπ2]
        field_simp

/-- **Flat window bound for `S_k` on the line.** For `k ≥ 1`, `sin 2c ≥ 1/2`, `cos 2c > 0` and
`U ≥ 0`, `∫_U^{U+1}|S_k(x(u)+iy(u))|²du ≤ E_k y(U)^{-k}/√y(U)` with
`E_k = 6(k! + 121(k+2)!)/π^k`. -/
theorem integral_norm_sq_thetaMoment_line_le (k : ℕ) (hk : 1 ≤ k) {c : ℝ}
    (hs : 1 / 2 ≤ Real.sin (2 * c)) (hcos : 0 < Real.cos (2 * c)) {U : ℝ} (hU : 0 ≤ U) :
    ∫ u in U..U + 1, ‖thetaMoment k (lineIm c u) (lineRe c u)‖ ^ 2 ≤
      6 * (k.factorial + 121 * (k + 2).factorial) / π ^ k * (lineIm c U)⁻¹ ^ k *
        (1 / Real.sqrt (lineIm c U)) := by
  have hs0 : 0 < Real.sin (2 * c) := by linarith
  set s := Real.sin (2 * c) with hs_def
  set κ := Real.cos (2 * c) with hκ_def
  set t := κ / s with ht_def
  have ht : 0 < t := div_pos hcos hs0
  set Y := Real.exp (2 * U) with hY_def
  have hY1 : 1 ≤ Y := Real.one_le_exp (by linarith)
  have hx₁ : lineRe c U = -(Y * s) := rfl
  have hx₂ : lineRe c (U + 1) = -(Real.exp 2 * Y * s) := by
    rw [lineRe, show 2 * (U + 1) = 2 * U + 2 by ring, Real.exp_add]; ring
  have hx₁neg : lineRe c U < 0 := lineRe_neg hs0 U
  have hx₂₁ : lineRe c (U + 1) ≤ lineRe c U := lineRe_antitone hs0 (by linarith)
  have hy₀' : lineIm c U = t * -lineRe c U := lineIm_eq hs0 U
  have hy₀pos : 0 < lineIm c U := mul_pos (Real.exp_pos _) hcos
  set y₀ := lineIm c U with hy₀_def
  set x₁ := lineRe c U with hx₁_def
  set x₂ := lineRe c (U + 1) with hx₂_def
  set g : ℝ → ℝ := fun x => ‖thetaMoment k (t * -x) x‖ ^ 2 with hg_def
  have hrw : ∀ u, ‖thetaMoment k (lineIm c u) (lineRe c u)‖ ^ 2 = g (lineRe c u) := by
    intro u; simp only [hg_def]; rw [lineIm_eq hs0 u]
  simp_rw [hrw]
  have hgc : ContinuousOn g (Set.Icc x₂ x₁) := by
    have h := continuousOn_thetaMoment_comp k hy₀pos (s := Set.Icc x₂ x₁)
      (g := fun x => t * -x) (by fun_prop) (fun x hx => by rw [hy₀']; nlinarith [hx.2])
    exact (continuous_norm.comp_continuousOn h).pow 2
  rw [integral_comp_lineRe hs0 (by linarith) hgc]
  have hstep : ∫ x in x₂..x₁, g x / (-2 * x) ≤ (∫ x in x₂..x₁, g x) / (-2 * x₁) := by
    rw [← intervalIntegral.integral_div]
    refine intervalIntegral.integral_mono_on hx₂₁ ?_ ?_ fun x hx => ?_
    · refine (hgc.div (continuousOn_const.mul continuousOn_id) fun x hx => ?_).intervalIntegrable_of_Icc
        hx₂₁
      exact mul_ne_zero (by norm_num) (by linarith [hx.2] : x < 0).ne
    · exact (hgc.div continuousOn_const fun _ _ => by nlinarith).intervalIntegrable_of_Icc hx₂₁
    · have hgx : 0 ≤ g x := by positivity
      have h1 : 0 < -2 * x₁ := by linarith
      have h2 : -2 * x₁ ≤ -2 * x := by linarith [hx.2]
      exact div_le_div_of_nonneg_left hgx h1 h2
  have hray := integral_norm_sq_thetaMoment_ray_le k ht hx₂₁ hx₁neg
  rw [← hy₀'] at hray
  set K : ℕ := ⌈(x₁ - x₂) / 2⌉₊ with hK_def
  set δ : ℝ := t * (x₁ - x₂ + 2) with hδ_def
  have hK : (K : ℝ) ≤ (x₁ - x₂) / 2 + 1 :=
    (Nat.ceil_lt_add_one (by linarith)).le
  have he := exp_two_le
  have hYs : 1 / 2 ≤ Y * s := by nlinarith
  have hy₀eq : y₀ = t * (Y * s) := by rw [hy₀', hx₁]; ring
  have hδy : δ ≤ 11 * y₀ := by
    rw [hδ_def, hy₀eq, hx₁, hx₂]
    have : -(Y * s) - -(Real.exp 2 * Y * s) + 2 ≤ 11 * (Y * s) := by nlinarith
    nlinarith
  have hδ0 : 0 ≤ δ := by rw [hδ_def, hx₁, hx₂]; have := Real.exp_pos 2; nlinarith
  have hKx : (K : ℝ) / (-2 * x₁) ≤ 3 := by
    rw [div_le_iff₀ (by linarith), hx₁]
    have : (x₁ - x₂) / 2 + 1 ≤ 3 * (-2 * -(Y * s)) := by rw [hx₁, hx₂]; nlinarith
    linarith
  have hBk := tsum_pow_mul_exp_neg_two_sq_le hk hy₀pos
  have hBk2 := tsum_pow_mul_exp_neg_two_sq_le (k := k + 2) (by omega) hy₀pos
  set R : ℝ := y₀⁻¹ ^ k * (1 / (2 * Real.sqrt y₀)) with hR_def
  have hR : 0 ≤ R := by positivity
  have hpk : 0 < π ^ k := by positivity
  have hmass : 4 * thetaMomentMass k y₀ + 4 * δ ^ 2 * π ^ 2 * thetaMomentMass (k + 2) y₀ ≤
      4 * R * (k.factorial + 121 * (k + 2).factorial) / π ^ k :=
    window_mass_le k hy₀pos hδ0 hδy (thetaMomentMass_nonneg _ _) hBk hBk2
  have hx1pos : 0 < -2 * x₁ := by linarith
  calc ∫ x in x₂..x₁, g x / (-2 * x)
      ≤ (∫ x in x₂..x₁, g x) / (-2 * x₁) := hstep
    _ ≤ ((K : ℝ) * (4 * thetaMomentMass k y₀ + 4 * δ ^ 2 * π ^ 2 *
          thetaMomentMass (k + 2) y₀)) / (-2 * x₁) := by
        gcongr
    _ = (K : ℝ) / (-2 * x₁) * (4 * thetaMomentMass k y₀ + 4 * δ ^ 2 * π ^ 2 *
          thetaMomentMass (k + 2) y₀) := by ring
    _ ≤ 3 * (4 * R * (k.factorial + 121 * (k + 2).factorial) / π ^ k) := by
        refine mul_le_mul hKx hmass (add_nonneg (mul_nonneg (by norm_num)
          (thetaMomentMass_nonneg _ _)) (mul_nonneg (by positivity) (thetaMomentMass_nonneg _ _)))
          (by norm_num)
    _ = 6 * (k.factorial + 121 * (k + 2).factorial) / π ^ k * y₀⁻¹ ^ k *
          (1 / Real.sqrt y₀) := by
        rw [hR_def]; field_simp; ring


/-! ## Riemann's kernel: flat upper bound on unit windows -/

/-- `E_k = 6(k! + 121(k+2)!)/π^k`, the constant of the window bound for `S_k`. -/
def thetaWindowConst (k : ℕ) : ℝ := 6 * (k.factorial + 121 * (k + 2).factorial) / π ^ k

/-- The constant of the flat window bound for Riemann's kernel. -/
def kernelWindowConst : ℝ :=
  32 * π ^ 4 * Real.exp 9 * thetaWindowConst 4 + 72 * π ^ 2 * Real.exp 5 * thetaWindowConst 2

theorem thetaWindowConst_nonneg (k : ℕ) : 0 ≤ thetaWindowConst k := by
  unfold thetaWindowConst; positivity

theorem exp_window_identity (n : ℕ) (a : ℝ) (ha : a = 2 * n + 1) (U : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    Real.exp (a * (U + 1)) * (Real.exp (2 * U) * κ)⁻¹ ^ n *
        (1 / Real.sqrt (Real.exp (2 * U) * κ)) =
      Real.exp a * κ⁻¹ ^ n * (1 / Real.sqrt κ) := by
  have e1 : Real.exp (a * (U + 1)) = Real.exp a * Real.exp U ^ (2 * n + 1) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; rw [ha]; push_cast; ring
  have e2 : Real.exp (2 * U) = Real.exp U ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1
  rw [e1, e2, Real.sqrt_mul (by positivity), Real.sqrt_sq (Real.exp_pos U).le]
  have h1 : Real.exp U ≠ 0 := (Real.exp_pos U).ne'
  have h2 : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.mpr hκ).ne'
  have h3 : κ ≠ 0 := hκ.ne'
  simp only [mul_inv, mul_pow, inv_pow]
  field_simp
  ring

theorem continuous_kernelC_line {c : ℝ} (hc0 : 0 ≤ c) (hc : c < π / 4) :
    Continuous fun u : ℝ => kernelC ((u : ℂ) + c * I) := by
  refine continuous_iff_continuousAt.2 fun u => ?_
  have him : |((u : ℂ) + c * I).im| < π / 4 := by simpa [abs_of_nonneg hc0] using hc
  exact ContinuousAt.comp (g := kernelC) (f := fun u : ℝ => (u : ℂ) + c * I)
    (differentiableAt_kernelC him).continuousAt (Continuous.continuousAt (by fun_prop))

theorem continuousOn_thetaMoment_line (k : ℕ) {c : ℝ} (hcos : 0 < Real.cos (2 * c)) (U V : ℝ) :
    ContinuousOn (fun u => thetaMoment k (lineIm c u) (lineRe c u)) (Set.Icc U V) := by
  have hy : 0 < lineIm c U := mul_pos (Real.exp_pos _) hcos
  have h := (continuousOn_thetaMoment k hy).comp
    (Continuous.continuousOn (by unfold lineRe lineIm; fun_prop) :
      ContinuousOn (fun u => (lineRe c u, lineIm c u)) (Set.Icc U V))
    (fun u hu => ⟨Set.mem_univ _, by
      simp only [Set.mem_Ici, lineIm]
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith [hu.1])) hcos.le⟩)
  exact h

/-- **Flat upper bound.** For `0 ≤ c < π/4` with `sin 2c ≥ 1/2` and every `U ≥ 0`,
`∫_U^{U+1}|Φ(u+ic)|²du ≤ C(cos 2c)^{-4}/√(cos 2c)`. -/
theorem integral_norm_sq_kernelC_line_le {c : ℝ} (hc0 : 0 ≤ c) (hc : c < π / 4)
    (hs : 1 / 2 ≤ Real.sin (2 * c)) {U : ℝ} (hU : 0 ≤ U) :
    ∫ u in U..U + 1, ‖kernelC ((u : ℂ) + c * I)‖ ^ 2 ≤
      kernelWindowConst * (Real.cos (2 * c))⁻¹ ^ 4 * (1 / Real.sqrt (Real.cos (2 * c))) := by
  have hκ : 0 < Real.cos (2 * c) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  have hκ1 : Real.cos (2 * c) ≤ 1 := Real.cos_le_one _
  set κ := Real.cos (2 * c) with hκ_def
  have hUU : U ≤ U + 1 := by linarith
  have h4c := continuousOn_thetaMoment_line 4 hκ U (U + 1)
  have h2c := continuousOn_thetaMoment_line 2 hκ U (U + 1)
  have hI4 : IntervalIntegrable (fun u => ‖thetaMoment 4 (lineIm c u) (lineRe c u)‖ ^ 2)
      volume U (U + 1) := ((continuous_norm.comp_continuousOn h4c).pow 2).intervalIntegrable_of_Icc hUU
  have hI2 : IntervalIntegrable (fun u => ‖thetaMoment 2 (lineIm c u) (lineRe c u)‖ ^ 2)
      volume U (U + 1) := ((continuous_norm.comp_continuousOn h2c).pow 2).intervalIntegrable_of_Icc hUU
  have hW4 := integral_norm_sq_thetaMoment_line_le 4 (by norm_num) hs hκ hU
  have hW2 := integral_norm_sq_thetaMoment_line_le 2 (by norm_num) hs hκ hU
  have hy₀ : lineIm c U = Real.exp (2 * U) * κ := rfl
  rw [hy₀] at hW4 hW2
  have hstep : ∫ u in U..U + 1, ‖kernelC ((u : ℂ) + c * I)‖ ^ 2 ≤
      ∫ u in U..U + 1, (32 * π ^ 4 * Real.exp (9 * (U + 1)) *
          ‖thetaMoment 4 (lineIm c u) (lineRe c u)‖ ^ 2 +
        72 * π ^ 2 * Real.exp (5 * (U + 1)) * ‖thetaMoment 2 (lineIm c u) (lineRe c u)‖ ^ 2) := by
    refine intervalIntegral.integral_mono_on hUU
      (((continuous_kernelC_line hc0 hc).norm.pow 2).intervalIntegrable _ _)
      ((hI4.const_mul _).add (hI2.const_mul _)) fun u hu => ?_
    refine (norm_sq_kernelC_line_le hκ u).trans ?_
    have e9 : Real.exp (9 * u) ≤ Real.exp (9 * (U + 1)) := Real.exp_le_exp.mpr (by linarith [hu.2])
    have e5 : Real.exp (5 * u) ≤ Real.exp (5 * (U + 1)) := Real.exp_le_exp.mpr (by linarith [hu.2])
    gcongr
  rw [intervalIntegral.integral_add (hI4.const_mul _) (hI2.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hstep
  refine hstep.trans ?_
  have hid4 := exp_window_identity 4 9 (by norm_num) U hκ
  have hid2 := exp_window_identity 2 5 (by norm_num) U hκ
  have hκinv : 1 ≤ κ⁻¹ := one_le_inv_iff₀.mpr ⟨hκ, hκ1⟩
  have hk24 : κ⁻¹ ^ 2 ≤ κ⁻¹ ^ 4 := pow_le_pow_right₀ hκinv (by norm_num)
  have hsk : 0 ≤ 1 / Real.sqrt κ := by positivity
  calc 32 * π ^ 4 * Real.exp (9 * (U + 1)) *
        (∫ u in U..U + 1, ‖thetaMoment 4 (lineIm c u) (lineRe c u)‖ ^ 2) +
      72 * π ^ 2 * Real.exp (5 * (U + 1)) *
        (∫ u in U..U + 1, ‖thetaMoment 2 (lineIm c u) (lineRe c u)‖ ^ 2)
      ≤ 32 * π ^ 4 * Real.exp (9 * (U + 1)) * (thetaWindowConst 4 *
          (Real.exp (2 * U) * κ)⁻¹ ^ 4 * (1 / Real.sqrt (Real.exp (2 * U) * κ))) +
        72 * π ^ 2 * Real.exp (5 * (U + 1)) * (thetaWindowConst 2 *
          (Real.exp (2 * U) * κ)⁻¹ ^ 2 * (1 / Real.sqrt (Real.exp (2 * U) * κ))) := by
        gcongr
        · exact hW4
        · exact hW2
    _ = 32 * π ^ 4 * thetaWindowConst 4 * (Real.exp 9 * κ⁻¹ ^ 4 * (1 / Real.sqrt κ)) +
        72 * π ^ 2 * thetaWindowConst 2 * (Real.exp 5 * κ⁻¹ ^ 2 * (1 / Real.sqrt κ)) := by
        rw [← hid4, ← hid2]; ring
    _ ≤ 32 * π ^ 4 * thetaWindowConst 4 * (Real.exp 9 * κ⁻¹ ^ 4 * (1 / Real.sqrt κ)) +
        72 * π ^ 2 * thetaWindowConst 2 * (Real.exp 5 * κ⁻¹ ^ 4 * (1 / Real.sqrt κ)) := by
        have := thetaWindowConst_nonneg 2
        gcongr
    _ = kernelWindowConst * κ⁻¹ ^ 4 * (1 / Real.sqrt κ) := by
        unfold kernelWindowConst; ring


/-! ## Riemann's kernel: flat lower bound on one window -/

/-- One period of the ray: `∫_{x₁−2}^{x₁}|S₄(x − itx)|² ≥ Σ₄(y₀) − 8t²π²Σ₆(y₀)`, `y₀ = −tx₁`. -/
theorem integral_norm_sq_thetaMoment_period_ge {t x₁ : ℝ} (ht : 0 < t) (hx₁ : x₁ < 0) :
    thetaMomentMass 4 (t * -x₁) - 8 * t ^ 2 * π ^ 2 * thetaMomentMass 6 (t * -x₁) ≤
      ∫ x in x₁ - 2..x₁, ‖thetaMoment 4 (t * -x) x‖ ^ 2 := by
  set y₀ := t * -x₁ with hy₀_def
  have hy₀ : 0 < y₀ := by rw [hy₀_def]; nlinarith
  have hX : x₁ - 2 ≤ x₁ := by linarith
  have hyl : ∀ x ∈ Set.Icc (x₁ - 2) (x₁ - 2 + 2), y₀ ≤ t * -x := by
    intro x hx; have := hx.2; rw [hy₀_def]; nlinarith
  have hyu : ∀ x ∈ Set.Icc (x₁ - 2) (x₁ - 2 + 2), t * -x ≤ y₀ + 2 * t := by
    intro x hx; have := hx.1; rw [hy₀_def]; nlinarith
  have hyc : ContinuousOn (fun x : ℝ => t * -x) (Set.Icc (x₁ - 2) (x₁ - 2 + 2)) := by fun_prop
  have hV := integral_norm_sq_thetaMoment_sub_le 4 hy₀ (by positivity) hyc hyl hyu
  have hP := integral_norm_sq_thetaMoment 4 hy₀ (x₁ - 2)
  have he : x₁ - 2 + 2 = x₁ := by ring
  rw [he] at hV hP
  have hc1 : ContinuousOn (fun x => thetaMoment 4 (t * -x) x) (Set.Icc (x₁ - 2) x₁) := by
    have := continuousOn_thetaMoment_comp 4 hy₀ (s := Set.Icc (x₁ - 2) x₁) (g := fun x => t * -x)
      (by fun_prop) (fun x hx => by rw [hy₀_def]; nlinarith [hx.2])
    exact this
  have hc0 : ContinuousOn (fun x => thetaMoment 4 y₀ x) (Set.Icc (x₁ - 2) x₁) :=
    continuousOn_thetaMoment_comp 4 hy₀ (g := fun _ => y₀) continuousOn_const (fun _ _ => le_rfl)
  have hIa : IntervalIntegrable (fun x => ‖thetaMoment 4 (t * -x) x‖ ^ 2) volume (x₁ - 2) x₁ :=
    ((continuous_norm.comp_continuousOn hc1).pow 2).intervalIntegrable_of_Icc hX
  have hIb : IntervalIntegrable (fun x => ‖thetaMoment 4 y₀ x‖ ^ 2) volume (x₁ - 2) x₁ :=
    ((continuous_norm.comp_continuousOn hc0).pow 2).intervalIntegrable_of_Icc hX
  have hId : IntervalIntegrable (fun x => ‖thetaMoment 4 (t * -x) x - thetaMoment 4 y₀ x‖ ^ 2)
      volume (x₁ - 2) x₁ :=
    ((continuous_norm.comp_continuousOn (hc1.sub hc0)).pow 2).intervalIntegrable_of_Icc hX
  have hpt : ∀ x ∈ Set.Icc (x₁ - 2) x₁, (1 / 2) * ‖thetaMoment 4 y₀ x‖ ^ 2 -
      ‖thetaMoment 4 (t * -x) x - thetaMoment 4 y₀ x‖ ^ 2 ≤ ‖thetaMoment 4 (t * -x) x‖ ^ 2 := by
    intro x _
    have h := norm_sub_le (thetaMoment 4 (t * -x) x)
      (thetaMoment 4 (t * -x) x - thetaMoment 4 y₀ x)
    rw [sub_sub_cancel] at h
    nlinarith [mul_self_le_mul_self (norm_nonneg _) h,
      sq_nonneg (‖thetaMoment 4 (t * -x) x‖ - ‖thetaMoment 4 (t * -x) x - thetaMoment 4 y₀ x‖)]
  have hmono := intervalIntegral.integral_mono_on hX ((hIb.const_mul _).sub hId) hIa hpt
  rw [intervalIntegral.integral_sub (hIb.const_mul _) hId, intervalIntegral.integral_const_mul,
    hP] at hmono
  have hV' : ∫ x in x₁ - 2..x₁, ‖thetaMoment 4 (t * -x) x - thetaMoment 4 y₀ x‖ ^ 2 ≤
      (2 * t) ^ 2 * π ^ 2 * (2 * thetaMomentMass 6 y₀) := hV
  have hmono' : 1 / 2 * (2 * thetaMomentMass 4 y₀) -
      ∫ x in x₁ - 2..x₁, ‖thetaMoment 4 (t * -x) x - thetaMoment 4 y₀ x‖ ^ 2 ≤
      ∫ x in x₁ - 2..x₁, ‖thetaMoment 4 (t * -x) x‖ ^ 2 := hmono
  nlinarith [hV', hmono']


/-- The vertical-variation term is small at large `e^{2U}`. -/
theorem small_term_le {t y₀ Y s M6 : ℝ} (ht : 0 < t) (hy₀ : 0 < y₀) (hs : 1 / 2 ≤ s)
    (hY1 : 1 ≤ Y) (hYM : 46080 * Real.exp (8 * π) / π ^ 4 ≤ Y) (hty : t * (Y * s) = y₀)
    (hM6 : M6 ≤ 720 / π ^ 6 * y₀⁻¹ ^ 6 * (1 / (2 * Real.sqrt y₀))) :
    8 * t ^ 2 * π ^ 2 * M6 ≤ Real.exp (-8 * π) / 4 * y₀⁻¹ ^ 4 * (1 / Real.sqrt y₀) := by
  have hpi : 0 < π := Real.pi_pos
  have hsq : 0 < Real.sqrt y₀ := Real.sqrt_pos.mpr hy₀
  have hY0 : 0 < Y := by linarith
  have hs0 : 0 < s := by linarith
  set Q : ℝ := y₀⁻¹ ^ 4 * (1 / Real.sqrt y₀) with hQ_def
  have hQ : 0 ≤ Q := by positivity
  have h1 : 8 * t ^ 2 * π ^ 2 * M6 ≤
      8 * t ^ 2 * π ^ 2 * (720 / π ^ 6 * y₀⁻¹ ^ 6 * (1 / (2 * Real.sqrt y₀))) :=
    mul_le_mul_of_nonneg_left hM6 (by positivity)
  have h3 : t * y₀⁻¹ = (Y * s)⁻¹ := by
    rw [← hty]; field_simp
  have h2 : 8 * t ^ 2 * π ^ 2 * (720 / π ^ 6 * y₀⁻¹ ^ 6 * (1 / (2 * Real.sqrt y₀))) =
      2880 / π ^ 4 * (t * y₀⁻¹) ^ 2 * Q := by
    rw [hQ_def]; field_simp; ring
  have h4 : ((Y * s)⁻¹) ^ 2 ≤ 4 / Y ^ 2 := by
    rw [inv_pow, ← one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul hs hs (by norm_num) hs0.le, sq_nonneg Y]
  have hexp : Real.exp (-8 * π) * Real.exp (8 * π) = 1 := by rw [← Real.exp_add]; simp
  have hY2 : 46080 * Real.exp (8 * π) / π ^ 4 ≤ Y ^ 2 := by nlinarith
  have key : 46080 ≤ Real.exp (-8 * π) * (π ^ 4 * Y ^ 2) := by
    have h6 := (div_le_iff₀ (by positivity : (0 : ℝ) < π ^ 4)).1 hY2
    have h7 := mul_le_mul_of_nonneg_left h6 (Real.exp_pos (-8 * π)).le
    nlinarith [hexp]
  have h5 : 2880 / π ^ 4 * (4 / Y ^ 2) ≤ Real.exp (-8 * π) / 4 := by
    rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith [key]
  calc 8 * t ^ 2 * π ^ 2 * M6
      ≤ 8 * t ^ 2 * π ^ 2 * (720 / π ^ 6 * y₀⁻¹ ^ 6 * (1 / (2 * Real.sqrt y₀))) := h1
    _ = 2880 / π ^ 4 * ((Y * s)⁻¹) ^ 2 * Q := by rw [h2, h3]
    _ ≤ 2880 / π ^ 4 * (4 / Y ^ 2) * Q := by gcongr
    _ ≤ Real.exp (-8 * π) / 4 * Q := mul_le_mul_of_nonneg_right h5 hQ
    _ = Real.exp (-8 * π) / 4 * y₀⁻¹ ^ 4 * (1 / Real.sqrt y₀) := by rw [hQ_def]; ring

/-- **Window lower bound for `S₄`.** If `e^{2U} ≥ 46080e^{8π}/π⁴`, `sin 2c ≥ 1/2` and
`y(U) = e^{2U}cos 2c ≤ 1/4`, then
`∫_U^{U+1}|S₄(x(u)+iy(u))|²du ≥ e^{-8π}/(8(e^{2U}+2)) · y(U)^{-4}/√y(U)`. -/
theorem integral_norm_sq_thetaMoment_line_ge {c : ℝ} (hs : 1 / 2 ≤ Real.sin (2 * c))
    (hcos : 0 < Real.cos (2 * c)) {U : ℝ} (hU : 0 ≤ U)
    (hY : 46080 * Real.exp (8 * π) / π ^ 4 ≤ Real.exp (2 * U)) (hy4 : lineIm c U ≤ 1 / 4) :
    Real.exp (-8 * π) / (8 * (Real.exp (2 * U) + 2)) * (lineIm c U)⁻¹ ^ 4 *
        (1 / Real.sqrt (lineIm c U)) ≤
      ∫ u in U..U + 1, ‖thetaMoment 4 (lineIm c u) (lineRe c u)‖ ^ 2 := by
  have hs0 : 0 < Real.sin (2 * c) := by linarith
  have hs1 : Real.sin (2 * c) ≤ 1 := Real.sin_le_one _
  set s := Real.sin (2 * c) with hs_def
  set κ := Real.cos (2 * c) with hκ_def
  set t := κ / s with ht_def
  have ht : 0 < t := div_pos hcos hs0
  set Y := Real.exp (2 * U) with hY_def
  have hY1 : 1 ≤ Y := Real.one_le_exp (by linarith)
  have hx₁ : lineRe c U = -(Y * s) := rfl
  have hx₂ : lineRe c (U + 1) = -(Real.exp 2 * Y * s) := by
    rw [lineRe, show 2 * (U + 1) = 2 * U + 2 by ring, Real.exp_add]; ring
  have hx₁neg : lineRe c U < 0 := lineRe_neg hs0 U
  have hy₀' : lineIm c U = t * -lineRe c U := lineIm_eq hs0 U
  have hy₀pos : 0 < lineIm c U := mul_pos (Real.exp_pos _) hcos
  set y₀ := lineIm c U with hy₀_def
  set x₁ := lineRe c U with hx₁_def
  set x₂ := lineRe c (U + 1) with hx₂_def
  have he := exp_two_le
  have he2 : 7 ≤ Real.exp 2 := by
    have h1 := Real.exp_one_gt_d9
    have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h2]; nlinarith
  have hYs : 1 / 2 ≤ Y * s := by nlinarith
  have hx₂₁ : x₂ ≤ x₁ - 2 := by
    rw [hx₁, hx₂]
    have : 6 * (Y * s) ≤ (Real.exp 2 - 1) * (Y * s) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    nlinarith
  set g : ℝ → ℝ := fun x => ‖thetaMoment 4 (t * -x) x‖ ^ 2 with hg_def
  have hrw : ∀ u, ‖thetaMoment 4 (lineIm c u) (lineRe c u)‖ ^ 2 = g (lineRe c u) := by
    intro u; simp only [hg_def]; rw [lineIm_eq hs0 u]
  simp_rw [hrw]
  have hgc : ContinuousOn g (Set.Icc x₂ x₁) := by
    have h := continuousOn_thetaMoment_comp 4 hy₀pos (s := Set.Icc x₂ x₁)
      (g := fun x => t * -x) (by fun_prop) (fun x hx => by rw [hy₀']; nlinarith [hx.2])
    exact (continuous_norm.comp_continuousOn h).pow 2
  rw [integral_comp_lineRe hs0 (by linarith) hgc]
  have hsub : ∫ x in x₁ - 2..x₁, g x / (-2 * x) ≤ ∫ x in x₂..x₁, g x / (-2 * x) := by
    refine intervalIntegral.integral_mono_interval hx₂₁ (by linarith) le_rfl ?_ ?_
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun x hx => ?_)
      have : x < 0 := lt_of_le_of_lt hx.2 hx₁neg
      exact div_nonneg (by positivity) (by linarith)
    · refine (hgc.div (continuousOn_const.mul continuousOn_id) fun x hx => ?_).intervalIntegrable_of_Icc
        (by linarith)
      exact mul_ne_zero (by norm_num) (by linarith [hx.2] : x < 0).ne
  have hlow : (∫ x in x₁ - 2..x₁, g x) / (2 * (Y * s + 2)) ≤ ∫ x in x₁ - 2..x₁, g x / (-2 * x) := by
    rw [← intervalIntegral.integral_div]
    refine intervalIntegral.integral_mono_on (by linarith) ?_ ?_ fun x hx => ?_
    · exact ((hgc.mono (Set.Icc_subset_Icc (by linarith) le_rfl)).div continuousOn_const
        fun _ _ => by positivity).intervalIntegrable_of_Icc (by linarith)
    · exact ((hgc.mono (Set.Icc_subset_Icc (by linarith) le_rfl)).div
        (continuousOn_const.mul continuousOn_id) fun x hx => mul_ne_zero (by norm_num)
          (by linarith [hx.2] : x < 0).ne).intervalIntegrable_of_Icc (by linarith)
    · have hgx : 0 ≤ g x := by positivity
      have h1 : 0 < -2 * x := by linarith [hx.2]
      have h2 : -2 * x ≤ 2 * (Y * s + 2) := by rw [hx₁] at hx; linarith [hx.1]
      exact div_le_div_of_nonneg_left hgx h1 h2
  have hper := integral_norm_sq_thetaMoment_period_ge ht hx₁neg
  rw [← hy₀'] at hper
  have hB4 := tsum_pow_mul_exp_neg_two_sq_ge 4 hy₀pos hy4
  have hB6 := tsum_pow_mul_exp_neg_two_sq_le (k := 6) (by norm_num) hy₀pos
  have hB4' : Real.exp (-8 * π) / 2 * y₀⁻¹ ^ 4 * (1 / Real.sqrt y₀) ≤ thetaMomentMass 4 y₀ := hB4
  have hB6' : thetaMomentMass 6 y₀ ≤
      (Nat.factorial 6 / π ^ 6) * y₀⁻¹ ^ 6 * (1 / (2 * Real.sqrt y₀)) := hB6
  have hty : t * (Y * s) = y₀ := by rw [hy₀', hx₁]; ring
  have hfac : (Nat.factorial 6 : ℝ) = 720 := by norm_num [Nat.factorial]
  rw [hfac] at hB6'
  have hsmall := small_term_le ht hy₀pos hs hY1 hY hty hB6'
  have hgint : Real.exp (-8 * π) / 4 * y₀⁻¹ ^ 4 * (1 / Real.sqrt y₀) ≤ ∫ x in x₁ - 2..x₁, g x := by
    have : Real.exp (-8 * π) / 4 * y₀⁻¹ ^ 4 * (1 / Real.sqrt y₀) =
        Real.exp (-8 * π) / 2 * y₀⁻¹ ^ 4 * (1 / Real.sqrt y₀) -
          Real.exp (-8 * π) / 4 * y₀⁻¹ ^ 4 * (1 / Real.sqrt y₀) := by ring
    rw [this]; linarith [hper]
  have hY2 : Y * s + 2 ≤ Y + 2 := by nlinarith
  calc Real.exp (-8 * π) / (8 * (Y + 2)) * y₀⁻¹ ^ 4 * (1 / Real.sqrt y₀)
      = (Real.exp (-8 * π) / 4 * y₀⁻¹ ^ 4 * (1 / Real.sqrt y₀)) / (2 * (Y + 2)) := by
        field_simp; ring
    _ ≤ (∫ x in x₁ - 2..x₁, g x) / (2 * (Y + 2)) := by gcongr
    _ ≤ (∫ x in x₁ - 2..x₁, g x) / (2 * (Y * s + 2)) := by
        have h0 : 0 ≤ ∫ x in x₁ - 2..x₁, g x :=
          intervalIntegral.integral_nonneg (by linarith) fun x _ => by positivity
        gcongr
    _ ≤ ∫ x in x₁ - 2..x₁, g x / (-2 * x) := hlow
    _ ≤ ∫ x in x₂..x₁, g x / (-2 * x) := hsub


theorem lower_window_algebra {A B κ : ℝ} (hA : 0 < A) (hB : 0 ≤ B) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hκA : κ ≤ A / (2 * (B + 1))) :
    A / 2 * κ⁻¹ ^ 4 ≤ A * κ⁻¹ ^ 4 - B * κ⁻¹ ^ 2 := by
  have h1 : B * κ ^ 2 ≤ A / 2 := by
    have hκ2 : κ ^ 2 ≤ κ := by nlinarith
    have hBk : B * κ ≤ B * (A / (2 * (B + 1))) := mul_le_mul_of_nonneg_left hκA hB
    have hfrac : B * (A / (2 * (B + 1))) ≤ A / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hκ2 hB]
  have h2 : B * κ⁻¹ ^ 2 = B * κ ^ 2 * κ⁻¹ ^ 4 := by
    field_simp
  rw [h2]
  have h4 : 0 ≤ κ⁻¹ ^ 4 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h1 h4]

theorem inv_pow_mul_one_div_sqrt {Y κ : ℝ} (hY : 0 < Y) (hκ : 0 < κ) (n : ℕ) :
    (Y * κ)⁻¹ ^ n * (1 / Real.sqrt (Y * κ)) =
      (Y⁻¹ ^ n * (1 / Real.sqrt Y)) * (κ⁻¹ ^ n * (1 / Real.sqrt κ)) := by
  rw [mul_inv, mul_pow, Real.sqrt_mul hY.le]
  have := Real.sqrt_pos.mpr hY
  have := Real.sqrt_pos.mpr hκ
  field_simp

/-- **Flat lower bound.** There is a window `[U₀, U₀+1]` on which
`∫|Φ(u+ic)|²du ≥ c₀(cos 2c)^{-4}/√(cos 2c)` as `c → π/4`. -/
theorem exists_integral_norm_sq_kernelC_line_ge :
    ∃ U₀ : ℝ, 0 ≤ U₀ ∧ ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ c : ℝ, 0 ≤ c → c < π / 4 →
      1 / 2 ≤ Real.sin (2 * c) → Real.cos (2 * c) ≤ κ₀ →
      c₀ * (Real.cos (2 * c))⁻¹ ^ 4 * (1 / Real.sqrt (Real.cos (2 * c))) ≤
        ∫ u in U₀..U₀ + 1, ‖kernelC ((u : ℂ) + c * I)‖ ^ 2 := by
  have hpi : 0 < π := Real.pi_pos
  set M : ℝ := 46080 * Real.exp (8 * π) / π ^ 4 with hM_def
  have hM : 0 ≤ M := by positivity
  set U₀ : ℝ := M with hU₀_def
  set Y : ℝ := Real.exp (2 * U₀) with hY_def
  have hYM : M ≤ Y := by have := Real.add_one_le_exp (2 * U₀); linarith
  have hY1 : 1 ≤ Y := Real.one_le_exp (by positivity)
  have hY0 : 0 < Y := by linarith
  set A : ℝ := 8 * π ^ 4 * Real.exp (9 * U₀) * (Real.exp (-8 * π) / (8 * (Y + 2))) *
    (Y⁻¹ ^ 4 * (1 / Real.sqrt Y)) with hA_def
  set B : ℝ := 36 * π ^ 2 * Real.exp (5 * (U₀ + 1)) * thetaWindowConst 2 *
    (Y⁻¹ ^ 2 * (1 / Real.sqrt Y)) with hB_def
  have hA : 0 < A := by
    have := Real.sqrt_pos.mpr hY0
    rw [hA_def]; positivity
  have hB : 0 ≤ B := by
    have := thetaWindowConst_nonneg 2
    rw [hB_def]; positivity
  refine ⟨U₀, hM, A / 2, by positivity, min (1 / (4 * Y)) (min 1 (A / (2 * (B + 1)))),
    by positivity, ?_⟩
  intro c hc0 hc hs hκ₀
  have hκ : 0 < Real.cos (2 * c) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  set κ := Real.cos (2 * c) with hκ_def
  have hκY : κ ≤ 1 / (4 * Y) := le_trans hκ₀ (min_le_left _ _)
  have hκ1 : κ ≤ 1 := le_trans hκ₀ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hκA : κ ≤ A / (2 * (B + 1)) := le_trans hκ₀ (le_trans (min_le_right _ _) (min_le_right _ _))
  have hlineIm : lineIm c U₀ = Y * κ := rfl
  have hy4 : lineIm c U₀ ≤ 1 / 4 := by
    rw [hlineIm]
    have := mul_le_mul_of_nonneg_left hκY hY0.le
    rw [show Y * (1 / (4 * Y)) = 1 / 4 by field_simp] at this
    exact this
  have hL4 := integral_norm_sq_thetaMoment_line_ge hs hκ hM hYM hy4
  have hW2 := integral_norm_sq_thetaMoment_line_le 2 (by norm_num) hs hκ hM
  rw [hlineIm] at hL4 hW2
  have hUU : U₀ ≤ U₀ + 1 := by linarith
  have h4c := continuousOn_thetaMoment_line 4 hκ U₀ (U₀ + 1)
  have h2c := continuousOn_thetaMoment_line 2 hκ U₀ (U₀ + 1)
  have hI4 : IntervalIntegrable (fun u => ‖thetaMoment 4 (lineIm c u) (lineRe c u)‖ ^ 2)
      volume U₀ (U₀ + 1) :=
    ((continuous_norm.comp_continuousOn h4c).pow 2).intervalIntegrable_of_Icc hUU
  have hI2 : IntervalIntegrable (fun u => ‖thetaMoment 2 (lineIm c u) (lineRe c u)‖ ^ 2)
      volume U₀ (U₀ + 1) :=
    ((continuous_norm.comp_continuousOn h2c).pow 2).intervalIntegrable_of_Icc hUU
  have hstep : ∫ u in U₀..U₀ + 1, (8 * π ^ 4 * Real.exp (9 * U₀) *
        ‖thetaMoment 4 (lineIm c u) (lineRe c u)‖ ^ 2 -
      36 * π ^ 2 * Real.exp (5 * (U₀ + 1)) * ‖thetaMoment 2 (lineIm c u) (lineRe c u)‖ ^ 2) ≤
      ∫ u in U₀..U₀ + 1, ‖kernelC ((u : ℂ) + c * I)‖ ^ 2 := by
    refine intervalIntegral.integral_mono_on hUU ((hI4.const_mul _).sub (hI2.const_mul _))
      (((continuous_kernelC_line hc0 hc).norm.pow 2).intervalIntegrable _ _) fun u hu => ?_
    refine le_trans ?_ (norm_sq_kernelC_line_ge hκ u)
    have e9 : Real.exp (9 * U₀) ≤ Real.exp (9 * u) := Real.exp_le_exp.mpr (by linarith [hu.1])
    have e5 : Real.exp (5 * u) ≤ Real.exp (5 * (U₀ + 1)) := Real.exp_le_exp.mpr (by linarith [hu.2])
    have a4 := sq_nonneg ‖thetaMoment 4 (lineIm c u) (lineRe c u)‖
    have a2 := sq_nonneg ‖thetaMoment 2 (lineIm c u) (lineRe c u)‖
    have hp4 : 0 ≤ 8 * π ^ 4 := by positivity
    have hp2 : 0 ≤ 36 * π ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left e9 hp4, mul_le_mul_of_nonneg_left e5 hp2,
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left e9 hp4) a4,
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left e5 hp2) a2]
  rw [intervalIntegral.integral_sub (hI4.const_mul _) (hI2.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hstep
  refine le_trans ?_ hstep
  rw [← hY_def] at hL4
  rw [mul_assoc, inv_pow_mul_one_div_sqrt hY0 hκ] at hL4 hW2
  have hW2' : ∫ u in U₀..U₀ + 1, ‖thetaMoment 2 (lineIm c u) (lineRe c u)‖ ^ 2 ≤
      thetaWindowConst 2 * ((Y⁻¹ ^ 2 * (1 / Real.sqrt Y)) * (κ⁻¹ ^ 2 * (1 / Real.sqrt κ))) := by
    refine hW2.trans (le_of_eq ?_); unfold thetaWindowConst; ring
  have hsk : 0 ≤ 1 / Real.sqrt κ := by positivity
  have halg := lower_window_algebra hA hB hκ hκ1 hκA
  have hp4 : 0 ≤ 8 * π ^ 4 * Real.exp (9 * U₀) := by positivity
  have hp2 : 0 ≤ 36 * π ^ 2 * Real.exp (5 * (U₀ + 1)) := by positivity
  calc A / 2 * κ⁻¹ ^ 4 * (1 / Real.sqrt κ)
      ≤ (A * κ⁻¹ ^ 4 - B * κ⁻¹ ^ 2) * (1 / Real.sqrt κ) :=
        mul_le_mul_of_nonneg_right halg hsk
    _ = 8 * π ^ 4 * Real.exp (9 * U₀) * (Real.exp (-8 * π) / (8 * (Y + 2)) *
          ((Y⁻¹ ^ 4 * (1 / Real.sqrt Y)) * (κ⁻¹ ^ 4 * (1 / Real.sqrt κ)))) -
        36 * π ^ 2 * Real.exp (5 * (U₀ + 1)) * (thetaWindowConst 2 *
          ((Y⁻¹ ^ 2 * (1 / Real.sqrt Y)) * (κ⁻¹ ^ 2 * (1 / Real.sqrt κ)))) := by
        rw [hA_def, hB_def]; ring
    _ ≤ 8 * π ^ 4 * Real.exp (9 * U₀) *
          (∫ u in U₀..U₀ + 1, ‖thetaMoment 4 (lineIm c u) (lineRe c u)‖ ^ 2) -
        36 * π ^ 2 * Real.exp (5 * (U₀ + 1)) *
          (∫ u in U₀..U₀ + 1, ‖thetaMoment 2 (lineIm c u) (lineRe c u)‖ ^ 2) := by
        exact sub_le_sub (mul_le_mul_of_nonneg_left hL4 hp4) (mul_le_mul_of_nonneg_left hW2' hp2)


/-! ## Symmetry and the whole line -/

theorem conj_kernelC (z : ℂ) : kernelC (starRingEnd ℂ z) = starRingEnd ℂ (kernelC z) := by
  unfold kernelC cseries
  rw [Complex.conj_tsum]
  refine tsum_congr fun n => ?_
  unfold cterm
  have harg : starRingEnd ℂ (((n + 1 : ℕ) : ℂ) ^ 2 * cexp (2 * z)) =
      ((n + 1 : ℕ) : ℂ) ^ 2 * cexp (2 * starRingEnd ℂ z) := by
    rw [map_mul, map_pow, map_natCast, ← Complex.exp_conj, map_mul, map_ofNat]
  have haeval : aeval (((n + 1 : ℕ) : ℂ) ^ 2 * cexp (2 * starRingEnd ℂ z)) riemannCuspPoly =
      starRingEnd ℂ (aeval (((n + 1 : ℕ) : ℂ) ^ 2 * cexp (2 * z)) riemannCuspPoly) := by
    have h := Polynomial.aeval_algHom_apply Complex.conjAe
      (((n + 1 : ℕ) : ℂ) ^ 2 * cexp (2 * z)) riemannCuspPoly
    rw [Complex.conjAe_coe, harg] at h
    exact h
  rw [haeval]
  simp only [map_mul, map_neg, ← Complex.exp_conj, map_div₀, map_pow, map_natCast,
    Complex.conj_ofReal, map_ofNat]

theorem norm_kernelC_neg_line {c : ℝ} (hc0 : 0 ≤ c) (hc : c < π / 4) (u : ℝ) :
    ‖kernelC ((-u : ℝ) + c * I)‖ = ‖kernelC ((u : ℂ) + c * I)‖ := by
  have him : |((u : ℂ) - c * I).im| < π / 4 := by
    simp [abs_of_nonneg hc0]; exact hc
  have h1 : ((-u : ℝ) : ℂ) + c * I = -((u : ℂ) - c * I) := by push_cast; ring
  have h2 : (u : ℂ) - c * I = starRingEnd ℂ ((u : ℂ) + c * I) := by
    simp [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
  rw [h1, kernelC_neg him, h2, conj_kernelC, Complex.norm_conj]

end RHTower.KernelStrip
