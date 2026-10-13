import GaloisForLFunctions.RHTower.BesselKZeroMoments
import GaloisForLFunctions.RHTower.ZetaChiGaussianKernel
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# The sine transform of `x (x² + y²)^{−3/2}` is a Macdonald function

For `y, k > 0` (`integral_mul_rpow_sin_eq_kMoment`):

`∫_ℝ x (x² + y²)^{−3/2} sin(k x) dx = 2k K₀(k y)`,  with `K₀(r) = ∫₀^∞ e^{−r cosh t} dt`.

Since `x (x² + y²)^{−3/2} = −∂ₓ (x² + y²)^{−1/2}`, this is the (absolutely convergent) derivative
form of Basset's integral `∫ (x² + y²)^{−1/2} cos(kx) dx = 2K₀(ky)`.  It identifies the Fourier
coefficients of the derivative of the `s = ½` Poisson vector `(y/|x − z|²)^{1/2}` with the
Whittaker functions `√y K₀(2π|n|y) e^{2πinu}`.

Proof (Gaussian subordination, every step absolutely convergent).
* `A^{−3/2} = (2/√π) ∫₀^∞ s^{1/2} e^{−sA} ds` (Euler's integral, `Γ(3/2) = √π/2`).
* `∫ x e^{−sx²} sin(kx) dx = (k/2s) ∫ e^{−sx²} cos(kx) dx = (k/2s) √(π/s) e^{−k²/4s}`: integrate by
  parts, then use the Gaussian Fourier transform.
* Fubini on `ℝ × (0, ∞)` reduces the integral to `k ∫₀^∞ s^{−1} e^{−s y² − k²/(4s)} ds`.
* With `s = e^t`, `y² e^t + (k²/4) e^{−t} = ky cosh(t − t₀)`, so that integral is
  `∫_ℝ e^{−ky cosh t} dt = 2K₀(ky)` (`integral_exp_neg_mul_cosh`).
-/

open MeasureTheory Set Filter Topology
open RHTower.BesselKZero

namespace RHTower

noncomputable section

/-! ### The Gaussian cosine and sine transforms -/

theorem integral_exp_neg_mul_sq_mul_cos {s : ℝ} (hs : 0 < s) (k : ℝ) :
    ∫ x : ℝ, Real.exp (-(s * x ^ 2)) * Real.cos (k * x) =
      Real.sqrt (Real.pi / s) * Real.exp (-(k ^ 2 / (4 * s))) := by
  set T : ℝ := 2 * Real.sqrt s with hT
  have hsq : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs.le
  have hT0 : 0 < T := by rw [hT]; positivity
  have h := RHTower.GaussZeroSum.integral_cos_affine_mul_gaussDensity hT0 0 k
  have hpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hss : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have e : ∀ x : ℝ, Real.exp (-(s * x ^ 2)) * Real.cos (k * x) =
      Real.sqrt Real.pi / Real.sqrt s *
        (Real.cos (0 + k * x) * RHTower.GaussZeroSum.gaussDensity T x) := by
    intro x
    unfold RHTower.GaussZeroSum.gaussDensity
    rw [zero_add, show T ^ 2 * x ^ 2 / 4 = s * x ^ 2 by rw [hT]; nlinarith [hsq]]
    rw [hT]
    field_simp
  simp_rw [e]
  rw [integral_const_mul, h, Real.cos_zero, one_mul,
    show k ^ 2 / T ^ 2 = k ^ 2 / (4 * s) by rw [hT]; congr 1; nlinarith [hsq],
    Real.sqrt_div' _ hs.le]

theorem integrable_exp_neg_mul_sq_mul {s : ℝ} (hs : 0 < s) (g : ℝ → ℝ)
    (hg : ∀ x, |g x| ≤ 1 + |x|) (hgm : AEStronglyMeasurable g) :
    Integrable fun x : ℝ => Real.exp (-(s * x ^ 2)) * g x := by
  have h1 : Integrable fun x : ℝ => Real.exp (-s * x ^ 2) := integrable_exp_neg_mul_sq hs
  have h2 : Integrable fun x : ℝ => x * Real.exp (-s * x ^ 2) := integrable_mul_exp_neg_mul_sq hs
  refine (h1.add h2.norm).mono' ((by fun_prop : Continuous fun x : ℝ =>
    Real.exp (-(s * x ^ 2))).aestronglyMeasurable.mul hgm) (Eventually.of_forall fun x => ?_)
  simp only [Pi.add_apply, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), neg_mul]
  calc Real.exp (-(s * x ^ 2)) * |g x| ≤ Real.exp (-(s * x ^ 2)) * (1 + |x|) :=
        mul_le_mul_of_nonneg_left (hg x) (Real.exp_pos _).le
    _ = Real.exp (-(s * x ^ 2)) + |x| * Real.exp (-(s * x ^ 2)) := by ring

theorem integral_mul_exp_neg_mul_sq_mul_sin {s : ℝ} (hs : 0 < s) (k : ℝ) :
    ∫ x : ℝ, x * Real.exp (-(s * x ^ 2)) * Real.sin (k * x) =
      k / (2 * s) * (Real.sqrt (Real.pi / s) * Real.exp (-(k ^ 2 / (4 * s)))) := by
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun x => Real.sin (k * x)) (u' := fun x => k * Real.cos (k * x))
    (v := fun x => -(Real.exp (-(s * x ^ 2)) / (2 * s)))
    (v' := fun x => x * Real.exp (-(s * x ^ 2)))
    (fun x _ => by
      have := ((hasDerivAt_id x).const_mul k).sin
      simpa [mul_comm] using this)
    (fun x _ => by
      have h1 : HasDerivAt (fun x : ℝ => -(s * x ^ 2)) (-(s * (2 * x))) x := by
        have := ((hasDerivAt_pow 2 x).const_mul s).fun_neg
        simpa using this
      have h := (h1.exp.div_const (2 * s)).neg
      refine h.congr_deriv ?_
      field_simp)
    ?_ ?_ ?_
  · rw [show (∫ x : ℝ, x * Real.exp (-(s * x ^ 2)) * Real.sin (k * x)) =
        ∫ x : ℝ, Real.sin (k * x) * (x * Real.exp (-(s * x ^ 2))) by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_); simp only; ring]
    rw [hibp]
    have e : (fun x : ℝ => k * Real.cos (k * x) * -(Real.exp (-(s * x ^ 2)) / (2 * s))) =
        fun x => -(k / (2 * s)) * (Real.exp (-(s * x ^ 2)) * Real.cos (k * x)) := by
      funext x; ring
    rw [e, integral_const_mul, integral_exp_neg_mul_sq_mul_cos hs]
    ring
  · refine (integrable_exp_neg_mul_sq_mul hs (fun x => x * Real.sin (k * x)) (fun x => ?_)
      (by fun_prop)).congr (Eventually.of_forall fun x => ?_)
    · rw [abs_mul]
      calc |x| * |Real.sin (k * x)| ≤ |x| * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)
        _ ≤ 1 + |x| := by linarith
    · simp only [Pi.mul_apply]; ring
  · refine ((integrable_exp_neg_mul_sq_mul hs (fun x => Real.cos (k * x)) (fun x => ?_)
      (by fun_prop)).const_mul (-(k / (2 * s)))).congr (Eventually.of_forall fun x => ?_)
    · have := Real.abs_cos_le_one (k * x); have := abs_nonneg x; linarith
    · simp only [Pi.mul_apply]; ring
  · refine ((integrable_exp_neg_mul_sq_mul hs (fun x => Real.sin (k * x)) (fun x => ?_)
      (by fun_prop)).const_mul (-(1 / (2 * s)))).congr (Eventually.of_forall fun x => ?_)
    · have := Real.abs_sin_le_one (k * x); have := abs_nonneg x; linarith
    · simp only [Pi.mul_apply]; ring

/-! ### Euler's integral and the `K₀` substitution -/

theorem integral_sqrt_mul_exp_neg_mul {A : ℝ} (hA : 0 < A) :
    ∫ s in Ioi (0 : ℝ), s ^ (1 / 2 : ℝ) * Real.exp (-(s * A)) =
      A ^ (-(3 / 2) : ℝ) * (Real.sqrt Real.pi / 2) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := 1 / 2) (b := A) one_pos
    (by norm_num) hA
  have hG : Real.Gamma (3 / 2) = Real.sqrt Real.pi / 2 := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
      Real.Gamma_one_half_eq]
    ring
  have e : (fun s : ℝ => s ^ (1 / 2 : ℝ) * Real.exp (-(s * A))) =
      fun s => s ^ (1 / 2 : ℝ) * Real.exp (-A * s ^ (1 : ℝ)) := by
    funext s; rw [Real.rpow_one]; ring_nf
  rw [e, h, show (1 / 2 + 1) / (1 : ℝ) = 3 / 2 by norm_num, hG,
    show -(1 / 2 + 1) / (1 : ℝ) = -(3 / 2) by norm_num]
  ring

/-- `∫₀^∞ s^{−1} e^{−(As + B/s)} ds = 2 K₀(2√(AB))`. -/
theorem integral_inv_mul_exp_neg_add_inv {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    ∫ s in Ioi (0 : ℝ), s⁻¹ * Real.exp (-(A * s + B / s)) =
      2 * kMoment 0 (2 * Real.sqrt (A * B)) := by
  have himage : Real.exp '' univ = Ioi 0 := by rw [Set.image_univ, Real.range_exp]
  have hcv := integral_image_eq_integral_abs_deriv_smul (s := univ) (f := Real.exp)
    (f' := Real.exp) MeasurableSet.univ (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    Real.exp_injective.injOn (fun s => s⁻¹ * Real.exp (-(A * s + B / s)))
  rw [himage, Measure.restrict_univ] at hcv
  rw [hcv]
  have e1 : ∀ t : ℝ, |Real.exp t| • ((Real.exp t)⁻¹ * Real.exp (-(A * Real.exp t +
      B / Real.exp t))) = Real.exp (-(A * Real.exp t + B * Real.exp (-t))) := by
    intro t
    rw [abs_of_pos (Real.exp_pos t), smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (Real.exp_ne_zero t),
      one_mul, div_eq_mul_inv, ← Real.exp_neg]
  simp_rw [e1]
  set c : ℝ := Real.log (B / A) / 2 with hc
  have hshift := integral_add_right_eq_self (μ := volume)
    (fun t : ℝ => Real.exp (-(A * Real.exp t + B * Real.exp (-t)))) c
  rw [← hshift]
  have hAB : 0 < A * B := mul_pos hA hB
  have hec : Real.exp c = Real.sqrt (B / A) := by
    rw [hc, Real.sqrt_eq_rpow, Real.rpow_def_of_pos (div_pos hB hA)]
    ring_nf
  have hsA := Real.sqrt_pos.mpr hA
  have hsB := Real.sqrt_pos.mpr hB
  have hk1 : A * Real.sqrt (B / A) = Real.sqrt (A * B) := by
    rw [Real.sqrt_div' _ hA.le, Real.sqrt_mul hA.le]
    field_simp
    rw [Real.sq_sqrt hA.le]
  have hk2 : B * (Real.sqrt (B / A))⁻¹ = Real.sqrt (A * B) := by
    rw [Real.sqrt_div' _ hA.le, Real.sqrt_mul hA.le]
    field_simp
    rw [Real.sq_sqrt hB.le]
  have e2 : ∀ t : ℝ, Real.exp (-(A * Real.exp (t + c) + B * Real.exp (-(t + c)))) =
      Real.exp (-(2 * Real.sqrt (A * B) * Real.cosh t)) := by
    intro t
    have h1 : Real.exp (t + c) = Real.exp t * Real.sqrt (B / A) := by rw [Real.exp_add, hec]
    have h2 : Real.exp (-(t + c)) = Real.exp (-t) * (Real.sqrt (B / A))⁻¹ := by
      rw [neg_add, Real.exp_add, Real.exp_neg c, hec]
    congr 1
    rw [h1, h2, Real.cosh_eq]
    have : A * (Real.exp t * Real.sqrt (B / A)) + B * (Real.exp (-t) * (Real.sqrt (B / A))⁻¹) =
        Real.exp t * (A * Real.sqrt (B / A)) + Real.exp (-t) * (B * (Real.sqrt (B / A))⁻¹) := by
      ring
    rw [this, hk1, hk2]
    ring
  simp_rw [e2]
  exact integral_exp_neg_mul_cosh _

/-! ### The sine transform -/

theorem rpow_neg_three_halves_eq_integral {A : ℝ} (hA : 0 < A) :
    A ^ (-(3 / 2) : ℝ) = 2 / Real.sqrt Real.pi *
      ∫ s in Ioi (0 : ℝ), s ^ (1 / 2 : ℝ) * Real.exp (-(s * A)) := by
  rw [integral_sqrt_mul_exp_neg_mul hA]
  have : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  field_simp

theorem abs_mul_rpow_le_inv {y x : ℝ} (hy : 0 < y) :
    |x| * (x ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) ≤ max 1 (1 / y ^ 2) * (1 + x ^ 2)⁻¹ := by
  have hA : 0 < x ^ 2 + y ^ 2 := by positivity
  have h1 : |x| ≤ (x ^ 2 + y ^ 2) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg y])
  have h2 : |x| * (x ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) ≤ (x ^ 2 + y ^ 2)⁻¹ := by
    calc |x| * (x ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ)
        ≤ (x ^ 2 + y ^ 2) ^ (1 / 2 : ℝ) * (x ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hA.le _)
      _ = (x ^ 2 + y ^ 2)⁻¹ := by
          rw [← Real.rpow_add hA, show (1 / 2 : ℝ) + -(3 / 2) = -1 by norm_num, Real.rpow_neg_one]
  refine h2.trans ?_
  rw [inv_le_comm₀ hA (by positivity), mul_inv, inv_inv]
  rcases le_or_gt 1 y with hy1 | hy1
  · have : max 1 (1 / y ^ 2) = 1 := max_eq_left (by
      rw [div_le_one (by positivity)]; nlinarith)
    rw [this, inv_one, one_mul]; nlinarith
  · have : max 1 (1 / y ^ 2) = 1 / y ^ 2 := max_eq_right (by
      rw [le_div_iff₀ (by positivity)]; nlinarith)
    rw [this, one_div, inv_inv]
    have hy2 : y ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg x, mul_le_mul_of_nonneg_left hy2 (sq_nonneg x)]

theorem integrable_abs_mul_rpow {y : ℝ} (hy : 0 < y) :
    Integrable fun x : ℝ => |x| * (x ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) := by
  refine (integrable_inv_one_add_sq.const_mul (max 1 (1 / y ^ 2))).mono'
    (by fun_prop) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _)
    (Real.rpow_nonneg (by positivity) _))]
  exact abs_mul_rpow_le_inv hy

/-- **The derivative form of Basset's integral.**  For `y, k > 0`,
`∫ x (x² + y²)^{−3/2} sin(kx) dx = 2k K₀(ky)`. -/
theorem integral_mul_rpow_sin_eq_kMoment {y k : ℝ} (hy : 0 < y) (hk : 0 < k) :
    ∫ x : ℝ, x * (x ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) * Real.sin (k * x) =
      2 * k * kMoment 0 (k * y) := by
  set G : ℝ → ℝ → ℝ := fun x s => 2 / Real.sqrt Real.pi *
    (x * Real.sin (k * x) * (s ^ (1 / 2 : ℝ) * Real.exp (-(s * (x ^ 2 + y ^ 2))))) with hG
  have hpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  -- the inner `s`-integral
  have hinS : ∀ x : ℝ, ∫ s in Ioi (0 : ℝ), G x s =
      x * (x ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) * Real.sin (k * x) := by
    intro x
    have hA : 0 < x ^ 2 + y ^ 2 := by positivity
    simp only [hG]
    rw [integral_const_mul, integral_const_mul, rpow_neg_three_halves_eq_integral hA]
    ring
  have hintS : ∀ x : ℝ, IntegrableOn (fun s => s ^ (1 / 2 : ℝ) *
      Real.exp (-(s * (x ^ 2 + y ^ 2)))) (Ioi 0) := by
    intro x
    have hA : 0 < x ^ 2 + y ^ 2 := by positivity
    by_contra hni
    have h0 := integral_sqrt_mul_exp_neg_mul hA
    rw [integral_undef hni] at h0
    have : 0 < (x ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) * (Real.sqrt Real.pi / 2) :=
      mul_pos (Real.rpow_pos_of_pos hA _) (by positivity)
    linarith
  -- integrability on the product
  have hcontG : Continuous (Function.uncurry G) := by
    have hr : Continuous fun p : ℝ × ℝ => p.2 ^ (1 / 2 : ℝ) :=
      continuous_snd.rpow_const fun _ => Or.inr (by norm_num)
    simp only [hG]
    exact continuous_const.mul (((continuous_fst.mul (Real.continuous_sin.comp
      (continuous_const.mul continuous_fst)))).mul (hr.mul (by fun_prop)))
  have hnormS : ∀ x : ℝ, ∫ s in Ioi (0 : ℝ), ‖G x s‖ =
      |x| * |Real.sin (k * x)| * (x ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) := by
    intro x
    have hA : 0 < x ^ 2 + y ^ 2 := by positivity
    have e : ∀ s ∈ Ioi (0 : ℝ), ‖G x s‖ = 2 / Real.sqrt Real.pi * (|x| * |Real.sin (k * x)|) *
        (s ^ (1 / 2 : ℝ) * Real.exp (-(s * (x ^ 2 + y ^ 2)))) := by
      intro s hs
      simp only [hG, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _),
        abs_of_nonneg (Real.rpow_nonneg (le_of_lt hs) _),
        abs_of_pos (div_pos two_pos hpi)]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul,
      integral_sqrt_mul_exp_neg_mul hA]
    field_simp
  have hFint : Integrable (Function.uncurry G) (volume.prod (volume.restrict (Ioi (0 : ℝ)))) := by
    rw [integrable_prod_iff hcontG.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun x => ?_, ?_⟩
    · exact ((hintS x).const_mul (x * Real.sin (k * x))).const_mul (2 / Real.sqrt Real.pi) |>.congr
        (Eventually.of_forall fun s => by simp only [hG, Function.uncurry])
    · simp only [Function.uncurry]
      simp_rw [hnormS]
      refine (integrable_abs_mul_rpow hy).mono' (by fun_prop) (Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by
        have := Real.rpow_nonneg (show (0 : ℝ) ≤ x ^ 2 + y ^ 2 by positivity) (-(3 / 2) : ℝ)
        positivity)]
      calc |x| * |Real.sin (k * x)| * (x ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ)
          ≤ |x| * 1 * (x ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _)
              (abs_nonneg _)) (Real.rpow_nonneg (by positivity) _)
        _ = |x| * (x ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) := by ring
  -- Fubini
  have hswap := integral_integral_swap hFint
  have hlhs : ∫ x : ℝ, x * (x ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) * Real.sin (k * x) =
      ∫ x : ℝ, ∫ s in Ioi (0 : ℝ), G x s := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    exact (hinS x).symm
  rw [hlhs, hswap]
  -- the inner `x`-integral
  have hinX : ∀ s ∈ Ioi (0 : ℝ), ∫ x : ℝ, G x s =
      k * (s⁻¹ * Real.exp (-(y ^ 2 * s + k ^ 2 / 4 / s))) := by
    intro s hs
    have hs0 : (0 : ℝ) < s := hs
    have e : ∀ x : ℝ, G x s = 2 / Real.sqrt Real.pi * (s ^ (1 / 2 : ℝ) *
        Real.exp (-(s * y ^ 2))) * (x * Real.exp (-(s * x ^ 2)) * Real.sin (k * x)) := by
      intro x
      simp only [hG]
      rw [show -(s * (x ^ 2 + y ^ 2)) = -(s * y ^ 2) + -(s * x ^ 2) by ring, Real.exp_add]
      ring
    simp_rw [e]
    rw [integral_const_mul, integral_mul_exp_neg_mul_sq_mul_sin hs0]
    have hsq : Real.sqrt (Real.pi / s) = Real.sqrt Real.pi / s ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_div' _ hs0.le, Real.sqrt_eq_rpow s]
    rw [hsq]
    have hsr : 0 < s ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hs0 _
    have hexp : Real.exp (-(y ^ 2 * s + k ^ 2 / 4 / s)) =
        Real.exp (-(s * y ^ 2)) * Real.exp (-(k ^ 2 / (4 * s))) := by
      rw [← Real.exp_add]; congr 1; field_simp; ring
    rw [hexp]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi hinX, integral_const_mul,
    integral_inv_mul_exp_neg_add_inv (by positivity) (by positivity)]
  have hsq : Real.sqrt (y ^ 2 * (k ^ 2 / 4)) = k * y / 2 := by
    rw [show y ^ 2 * (k ^ 2 / 4) = (k * y / 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  rw [hsq]
  ring_nf

end

end RHTower
