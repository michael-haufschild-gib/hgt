import GaloisForLFunctions.HTGeometry.LogWeightedPoisson
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Differentiating a rational kernel in its mass

For a weight of at most logarithmic growth the pairing

`Y ↦ ∫_ℝ w(x)·(Y + x²)^{-(n+1)} dx`

is differentiable in the mass and

`d/dY ∫ w(x)(Y + x²)^{-(n+1)} dx = -(n+1)·∫ w(x)(Y + x²)^{-(n+2)} dx`.

The domination is uniform on any half-line `Y > Y₀ > 0`, because the extra powers are bounded below
by `Y₀^{n+1}` and the remaining single power is Poisson-integrable against a logarithm.  Iterating,
every power of the kernel is a mass derivative of the first one.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## Integrability of a logarithmic weight against a rational kernel -/

theorem integrable_logWeight_mul_inv_sq_add_sq {w : ℝ → ℂ} {K : ℝ} (hw : Continuous w)
    (hb : ∀ x : ℝ, ‖w x‖ ≤ K + Real.log (2 + |x|)) {A : ℝ} (hA : 0 < A) :
    Integrable fun x : ℝ => w x * ((A ^ 2 + x ^ 2 : ℝ) : ℂ)⁻¹ := by
  have hmaj : Integrable fun x : ℝ =>
      K * (A ^ 2 + x ^ 2)⁻¹ + Real.log (2 + |x|) * (A ^ 2 + x ^ 2)⁻¹ :=
    ((integrable_inv_sq_add_sq hA).const_mul K).add (integrable_log_mul_inv_sq_add_sq hA)
  refine hmaj.mono' ?_ ?_
  · refine (hw.aestronglyMeasurable).mul ?_
    refine Continuous.aestronglyMeasurable ?_
    refine Continuous.inv₀ (by fun_prop) fun x => ?_
    have h : (0 : ℝ) < ((A ^ 2 + x ^ 2 : ℝ) : ℂ).re := by
      simp only [Complex.ofReal_re]
      positivity
    intro h0
    rw [h0] at h
    simp at h
  filter_upwards with x
  have hpos : (0 : ℝ) < A ^ 2 + x ^ 2 := by positivity
  rw [norm_mul, ← Complex.ofReal_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (le_of_lt (inv_pos.mpr hpos))]
  have hstep : ‖w x‖ * (A ^ 2 + x ^ 2)⁻¹
      ≤ (K + Real.log (2 + |x|)) * (A ^ 2 + x ^ 2)⁻¹ :=
    mul_le_mul_of_nonneg_right (hb x) (le_of_lt (inv_pos.mpr hpos))
  calc ‖w x‖ * (A ^ 2 + x ^ 2)⁻¹
      ≤ (K + Real.log (2 + |x|)) * (A ^ 2 + x ^ 2)⁻¹ := hstep
    _ = K * (A ^ 2 + x ^ 2)⁻¹ + Real.log (2 + |x|) * (A ^ 2 + x ^ 2)⁻¹ := by ring

/-- The mass kernel of order `n`. -/
theorem integrable_logWeight_mul_massKernel {w : ℝ → ℂ} {K : ℝ} (hw : Continuous w)
    (hb : ∀ x : ℝ, ‖w x‖ ≤ K + Real.log (2 + |x|)) (n : ℕ) {Y : ℝ} (hY : 0 < Y) :
    Integrable fun x : ℝ => w x * ((((Y + x ^ 2) ^ (n + 1) : ℝ)) : ℂ)⁻¹ := by
  have hA : (0 : ℝ) < Real.sqrt Y := Real.sqrt_pos.mpr hY
  have hAsq : Real.sqrt Y ^ 2 = Y := Real.sq_sqrt hY.le
  have hmaj : Integrable fun x : ℝ =>
      (Y ^ n)⁻¹ * ‖w x * ((Real.sqrt Y ^ 2 + x ^ 2 : ℝ) : ℂ)⁻¹‖ :=
    ((integrable_logWeight_mul_inv_sq_add_sq hw hb hA).norm).const_mul _
  refine hmaj.mono' ?_ ?_
  · refine (hw.aestronglyMeasurable).mul ?_
    refine Continuous.aestronglyMeasurable ?_
    refine Continuous.inv₀ (by fun_prop) fun x => ?_
    have hpos : (0 : ℝ) < (Y + x ^ 2) ^ (n + 1) := by positivity
    intro h0
    have := congrArg Complex.re h0
    simp only [Complex.ofReal_re, Complex.zero_re] at this
    linarith
  filter_upwards with x
  have hpos : (0 : ℝ) < Y + x ^ 2 := by positivity
  have hpow : (0 : ℝ) < (Y + x ^ 2) ^ (n + 1) := by positivity
  have hYn : (0 : ℝ) < Y ^ n := by positivity
  have hcmp : Y ^ n * (Y + x ^ 2) ≤ (Y + x ^ 2) ^ (n + 1) := by
    have h1 : Y ^ n ≤ (Y + x ^ 2) ^ n := by
      refine pow_le_pow_left₀ hY.le ?_ n
      nlinarith [sq_nonneg x]
    calc Y ^ n * (Y + x ^ 2) ≤ (Y + x ^ 2) ^ n * (Y + x ^ 2) :=
          mul_le_mul_of_nonneg_right h1 hpos.le
      _ = (Y + x ^ 2) ^ (n + 1) := by ring
  rw [norm_mul, ← Complex.ofReal_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (le_of_lt (inv_pos.mpr hpow)), norm_mul, ← Complex.ofReal_inv,
    Complex.norm_real, Real.norm_eq_abs, hAsq,
    abs_of_nonneg (le_of_lt (inv_pos.mpr hpos))]
  have hinv : ((Y + x ^ 2) ^ (n + 1))⁻¹ ≤ (Y ^ n)⁻¹ * (Y + x ^ 2)⁻¹ := by
    have h := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < Y ^ n * (Y + x ^ 2)) hcmp
    rw [← mul_inv]
    simpa [one_div] using h
  calc ‖w x‖ * ((Y + x ^ 2) ^ (n + 1))⁻¹
      ≤ ‖w x‖ * ((Y ^ n)⁻¹ * (Y + x ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left hinv (norm_nonneg _)
    _ = (Y ^ n)⁻¹ * (‖w x‖ * (Y + x ^ 2)⁻¹) := by ring


/-! ## The mass derivative -/

theorem hasDerivAt_inv_massKernel (n : ℕ) {Y : ℝ} (hY : 0 < Y) (x : ℝ) :
    HasDerivAt (fun Z : ℝ => (((Z + x ^ 2) ^ (n + 1))⁻¹))
      (-((n : ℝ) + 1) * ((Y + x ^ 2) ^ (n + 2))⁻¹) Y := by
  have hpos : (0 : ℝ) < Y + x ^ 2 := by positivity
  have hne0 : (Y + x ^ 2) ≠ 0 := ne_of_gt hpos
  have hbase : HasDerivAt (fun Z : ℝ => (Z + x ^ 2) ^ (n + 1))
      (((n : ℝ) + 1) * (Y + x ^ 2) ^ n) Y := by
    have h : HasDerivAt (fun Z : ℝ => Z + x ^ 2) 1 Y := (hasDerivAt_id Y).add_const _
    have h2 : HasDerivAt (fun Z : ℝ => (Z + x ^ 2) ^ (n + 1))
        ((((n + 1 : ℕ) : ℝ)) * (Y + x ^ 2) ^ (n + 1 - 1) * 1) Y := h.pow (n + 1)
    refine h2.congr_deriv ?_
    push_cast
    simp
  have hne : (Y + x ^ 2) ^ (n + 1) ≠ 0 := by positivity
  have hinv := hbase.inv hne
  refine hinv.congr_deriv ?_
  rw [← pow_mul]
  field_simp
  ring

theorem hasDerivAt_ofReal_inv_massKernel (n : ℕ) {Y : ℝ} (hY : 0 < Y) (x : ℝ) :
    HasDerivAt (fun Z : ℝ => ((((Z + x ^ 2) ^ (n + 1) : ℝ)) : ℂ)⁻¹)
      (((-((n : ℝ) + 1) * ((Y + x ^ 2) ^ (n + 2))⁻¹ : ℝ)) : ℂ) Y := by
  have h := (hasDerivAt_inv_massKernel n hY x).ofReal_comp
  refine h.congr_of_eventuallyEq ?_
  filter_upwards with Z
  rw [Complex.ofReal_inv]

theorem massKernel_inv_le {Y₀ : ℝ} (hY₀ : 0 < Y₀) (m : ℕ) {Z : ℝ} (hZ : Y₀ < Z) (x : ℝ) :
    ((Z + x ^ 2) ^ (m + 2))⁻¹ ≤ (Y₀ ^ (m + 1))⁻¹ * (Y₀ + x ^ 2)⁻¹ := by
  have h0 : (0 : ℝ) < Y₀ + x ^ 2 := by positivity
  have h1 : (0 : ℝ) < Z + x ^ 2 := by nlinarith [sq_nonneg x]
  have hstep : Y₀ ^ (m + 1) * (Y₀ + x ^ 2) ≤ (Z + x ^ 2) ^ (m + 2) := by
    have hle : Y₀ + x ^ 2 ≤ Z + x ^ 2 := by linarith
    have hp1 : Y₀ ^ (m + 1) ≤ (Z + x ^ 2) ^ (m + 1) := by
      refine pow_le_pow_left₀ hY₀.le ?_ (m + 1)
      nlinarith [sq_nonneg x]
    calc Y₀ ^ (m + 1) * (Y₀ + x ^ 2) ≤ (Z + x ^ 2) ^ (m + 1) * (Z + x ^ 2) := by
          refine mul_le_mul hp1 hle h0.le (by positivity)
      _ = (Z + x ^ 2) ^ (m + 2) := by ring
  have h := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < Y₀ ^ (m + 1) * (Y₀ + x ^ 2)) hstep
  rw [← mul_inv]
  simpa [one_div] using h

/-- **The mass derivative of a logarithmically weighted rational pairing.** -/
theorem hasDerivAt_integral_logWeight_massKernel {w : ℝ → ℂ} {K : ℝ} (hw : Continuous w)
    (hb : ∀ x : ℝ, ‖w x‖ ≤ K + Real.log (2 + |x|)) (n : ℕ) {Y : ℝ} (hY : 0 < Y) :
    HasDerivAt (fun Z : ℝ => ∫ x : ℝ, w x * ((((Z + x ^ 2) ^ (n + 1) : ℝ)) : ℂ)⁻¹)
      (-((n : ℂ) + 1) * ∫ x : ℝ, w x * ((((Y + x ^ 2) ^ (n + 2) : ℝ)) : ℂ)⁻¹) Y := by
  set Y₀ : ℝ := Y / 2 with hY₀def
  have hY₀ : 0 < Y₀ := by rw [hY₀def]; linarith
  have hY₀Y : Y₀ < Y := by rw [hY₀def]; linarith
  have hA : (0 : ℝ) < Real.sqrt Y₀ := Real.sqrt_pos.mpr hY₀
  have hAsq : Real.sqrt Y₀ ^ 2 = Y₀ := Real.sq_sqrt hY₀.le
  have hmeasK : ∀ m : ℕ, ∀ Z : ℝ, 0 < Z →
      AEStronglyMeasurable (fun x : ℝ => w x * ((((Z + x ^ 2) ^ (m + 1) : ℝ)) : ℂ)⁻¹) := by
    intro m Z hZ
    refine (hw.aestronglyMeasurable).mul ?_
    refine Continuous.aestronglyMeasurable ?_
    refine Continuous.inv₀ (by fun_prop) fun x => ?_
    have hpos : (0 : ℝ) < (Z + x ^ 2) ^ (m + 1) := by positivity
    intro h0
    have hre := congrArg Complex.re h0
    simp only [Complex.ofReal_re, Complex.zero_re] at hre
    linarith
  have hbound : Integrable fun x : ℝ =>
      ((n : ℝ) + 1) * (Y₀ ^ (n + 1))⁻¹ *
        (K * (Y₀ + x ^ 2)⁻¹ + Real.log (2 + |x|) * (Y₀ + x ^ 2)⁻¹) := by
    have h := (((integrable_inv_sq_add_sq hA).const_mul K).add
      (integrable_log_mul_inv_sq_add_sq hA)).const_mul (((n : ℝ) + 1) * (Y₀ ^ (n + 1))⁻¹)
    refine h.congr ?_
    filter_upwards with x
    simp only [Pi.add_apply, hAsq]
  have hkey := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure ℝ)) (x₀ := Y) (s := Set.Ioi Y₀)
    (F := fun Z : ℝ => fun x : ℝ => w x * ((((Z + x ^ 2) ^ (n + 1) : ℝ)) : ℂ)⁻¹)
    (F' := fun Z : ℝ => fun x : ℝ =>
      w x * (((-((n : ℝ) + 1) * ((Z + x ^ 2) ^ (n + 2))⁻¹ : ℝ)) : ℂ))
    (bound := fun x : ℝ => ((n : ℝ) + 1) * (Y₀ ^ (n + 1))⁻¹ *
        (K * (Y₀ + x ^ 2)⁻¹ + Real.log (2 + |x|) * (Y₀ + x ^ 2)⁻¹))
    (Ioi_mem_nhds hY₀Y)
    (by
      filter_upwards [Ioi_mem_nhds hY] with Z hZ
      exact hmeasK n Z hZ)
    (integrable_logWeight_mul_massKernel hw hb n hY)
    (by
      refine (hw.aestronglyMeasurable).mul ?_
      refine Continuous.aestronglyMeasurable ?_
      refine Complex.continuous_ofReal.comp ?_
      refine continuous_const.mul ?_
      refine Continuous.inv₀ (by fun_prop) fun x => ?_
      have hpos : (0 : ℝ) < (Y + x ^ 2) ^ (n + 2) := by positivity
      exact ne_of_gt hpos)
    (by
      refine Filter.Eventually.of_forall fun x => ?_
      intro Z hZ
      simp only [Set.mem_Ioi] at hZ
      have hZpos : (0 : ℝ) < Z := lt_trans hY₀ hZ
      have hker := massKernel_inv_le hY₀ n hZ x
      have hpos : (0 : ℝ) < (Z + x ^ 2) ^ (n + 2) := by positivity
      have hY₀x : (0 : ℝ) < Y₀ + x ^ 2 := by positivity
      have hnn : (0 : ℝ) ≤ ((n : ℝ) + 1) := by positivity
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (by
          have : (0 : ℝ) < ((Z + x ^ 2) ^ (n + 2))⁻¹ := inv_pos.mpr hpos
          nlinarith)]
      have hstep : ‖w x‖ * (((n : ℝ) + 1) * ((Z + x ^ 2) ^ (n + 2))⁻¹)
          ≤ (K + Real.log (2 + |x|)) * (((n : ℝ) + 1) * ((Y₀ ^ (n + 1))⁻¹ * (Y₀ + x ^ 2)⁻¹)) := by
        refine mul_le_mul (hb x) (mul_le_mul_of_nonneg_left hker hnn) (by positivity) ?_
        linarith [norm_nonneg (w x), hb x]
      have hrw : ‖w x‖ * -(-((n : ℝ) + 1) * ((Z + x ^ 2) ^ (n + 2))⁻¹)
          = ‖w x‖ * (((n : ℝ) + 1) * ((Z + x ^ 2) ^ (n + 2))⁻¹) := by ring
      rw [hrw]
      refine le_trans hstep (le_of_eq ?_)
      ring)
    hbound
    (by
      refine Filter.Eventually.of_forall fun x => ?_
      intro Z hZ
      simp only [Set.mem_Ioi] at hZ
      have hZpos : (0 : ℝ) < Z := lt_trans hY₀ hZ
      exact HasDerivAt.const_mul (w x) (hasDerivAt_ofReal_inv_massKernel n hZpos x))
  refine hkey.2.congr_deriv ?_
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  push_cast
  ring


/-! ## Iterating the mass derivative -/

/-- The pairing of a weight with the mass kernel of order `n`. -/
def massPairing (w : ℝ → ℂ) (n : ℕ) (Y : ℝ) : ℂ :=
  ∫ x : ℝ, w x * ((((Y + x ^ 2) ^ (n + 1) : ℝ)) : ℂ)⁻¹

theorem hasDerivAt_massPairing {w : ℝ → ℂ} {K : ℝ} (hw : Continuous w)
    (hb : ∀ x : ℝ, ‖w x‖ ≤ K + Real.log (2 + |x|)) (n : ℕ) {Y : ℝ} (hY : 0 < Y) :
    HasDerivAt (massPairing w n) (-((n : ℂ) + 1) * massPairing w (n + 1) Y) Y :=
  hasDerivAt_integral_logWeight_massKernel hw hb n hY

/-- **Every mass power is a mass derivative of the first.** -/
theorem iteratedDeriv_massPairing {w : ℝ → ℂ} {K : ℝ} (hw : Continuous w)
    (hb : ∀ x : ℝ, ‖w x‖ ≤ K + Real.log (2 + |x|)) :
    ∀ (n : ℕ) {Y : ℝ}, 0 < Y →
      iteratedDeriv n (massPairing w 0) Y
        = (-1 : ℂ) ^ n * ((Nat.factorial n : ℕ) : ℂ) * massPairing w n Y := by
  intro n
  induction n with
  | zero =>
    intro Y _
    simp
  | succ n ih =>
    intro Y hY
    have heq : (fun Z : ℝ => iteratedDeriv n (massPairing w 0) Z)
        =ᶠ[nhds Y] fun Z : ℝ =>
          (-1 : ℂ) ^ n * ((Nat.factorial n : ℕ) : ℂ) * massPairing w n Z := by
      filter_upwards [Ioi_mem_nhds hY] with Z hZ
      exact ih hZ
    rw [iteratedDeriv_succ, heq.deriv_eq]
    have hderiv : HasDerivAt
        (fun Z : ℝ => (-1 : ℂ) ^ n * ((Nat.factorial n : ℕ) : ℂ) * massPairing w n Z)
        ((-1 : ℂ) ^ n * ((Nat.factorial n : ℕ) : ℂ)
          * (-((n : ℂ) + 1) * massPairing w (n + 1) Y)) Y :=
      (hasDerivAt_massPairing hw hb n hY).const_mul _
    rw [hderiv.deriv]
    have hfac : ((Nat.factorial (n + 1) : ℕ) : ℂ) = ((n : ℂ) + 1) * ((Nat.factorial n : ℕ) : ℂ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    rw [hfac]
    ring

end GaloisForLFunctions.HTGeometry

end

