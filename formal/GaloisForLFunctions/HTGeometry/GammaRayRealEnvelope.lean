import GaloisForLFunctions.HTGeometry.GammaRayShiftAsymptotic

/-!
# The real factorial envelope of a complex ray

Let `α` have positive real part `r`.  Subtracting the real factorial `Γ(1+rn)` from
`log ‖Γ(1+αn)‖` cancels every term of order `n log n`; what is left is linear in `n`, with slope

`log A = Re(α log α) − r log r`,

plus a logarithmically bounded remainder.  Consequently

`c n^{-B} A^n Γ(1+rn) ≤ ‖Γ(1+αn)‖ ≤ C n^{B} A^n Γ(1+rn)`

for absolute constants depending only on `α`.  Only this polynomially two-sided form is needed
downstream: an endpoint convolution estimate absorbs fixed polynomial weights into its exponent.

The proof never uses Stirling's series.  The one-step ratio of both sides is controlled by the ray
shift asymptotic, and the resulting defect satisfies `|D(n+1) − D(n)| = O(1/n)`, which telescopes
into `O(log n)` by the harmonic bound.
-/

open Filter Set Topology Function

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-! ## One step of the complex ray -/

theorem rayPoint_succ (α : ℂ) (n : ℕ) : rayPoint α (n + 1) = rayPoint α n + α := by
  rw [rayPoint, rayPoint]
  push_cast
  ring

theorem norm_Gamma_rayPoint_pos {α : ℂ} (hre : 0 < α.re) (n : ℕ) :
    0 < ‖Complex.Gamma (rayPoint α n)‖ :=
  norm_pos_iff.mpr (gamma_ne_zero_of_re_pos (rayPoint_re_pos hre n))

/-- **One step of the Gamma ray.** -/
theorem norm_Gamma_rayPoint_succ {α : ℂ} (hre : 0 < α.re) (n : ℕ) :
    ‖Complex.Gamma (rayPoint α (n + 1))‖
      = ‖Complex.Gamma (rayPoint α n)‖
        * Real.exp ((α * Complex.log (rayPoint α n)).re)
        * Real.exp ((rayShiftExponent α α n).re) := by
  have hz := rayPoint_re_pos hre n
  have hz0 := rayPoint_ne_zero hre n
  have hseg : 0 < (rayPoint α n + α).re := by
    rw [← rayPoint_succ]
    exact rayPoint_re_pos hre (n + 1)
  have hΓ : Complex.Gamma (rayPoint α n) ≠ 0 := gamma_ne_zero_of_re_pos hz
  have hpow : rayPoint α n ^ α = Complex.exp (α * Complex.log (rayPoint α n)) := by
    rw [Complex.cpow_def_of_ne_zero hz0]
    ring_nf
  have hpowne : rayPoint α n ^ α ≠ 0 := by
    rw [hpow]
    exact Complex.exp_ne_zero _
  have hratio := gamma_ray_shift_ratio_eq_exp hre hseg
  have hval : Complex.Gamma (rayPoint α n + α)
      = Complex.Gamma (rayPoint α n) * rayPoint α n ^ α
        * Complex.exp (rayShiftExponent α α n) := by
    field_simp at hratio
    linear_combination hratio
  rw [rayPoint_succ, hval, norm_mul, norm_mul, hpow, Complex.norm_exp, Complex.norm_exp]

/-! ## The real ray -/

theorem rayPoint_ofReal (r : ℝ) (n : ℕ) : rayPoint (r : ℂ) n = ((1 + r * n : ℝ) : ℂ) := by
  rw [rayPoint]
  push_cast
  ring

theorem norm_Gamma_rayPoint_ofReal {r : ℝ} (hr : 0 < r) (n : ℕ) :
    ‖Complex.Gamma (rayPoint (r : ℂ) n)‖ = Real.Gamma (1 + r * n) := by
  have hpos : (0 : ℝ) < 1 + r * n := by
    have := Nat.cast_nonneg (α := ℝ) n
    nlinarith
  rw [rayPoint_ofReal, Complex.Gamma_ofReal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.Gamma_pos_of_pos hpos)]

/-! ## Splitting the ray logarithm -/

theorem log_ofReal_of_pos {x : ℝ} (h : 0 < x) :
    Complex.log (x : ℂ) = ((Real.log x : ℝ) : ℂ) := by
  rw [Complex.log, Complex.arg_ofReal_of_nonneg h.le, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos h]
  simp

theorem re_mul_natCast_pos {α : ℂ} (hre : 0 < α.re) {n : ℕ} (hn : 1 ≤ n) :
    0 < (α * (n : ℂ)).re := by
  rw [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, mul_zero, sub_zero]
  have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  nlinarith

theorem re_inv_mul_natCast_nonneg {α : ℂ} (hre : 0 < α.re) (n : ℕ) :
    0 ≤ ((α * (n : ℂ))⁻¹).re := by
  have h1 : (0 : ℝ) ≤ (α * (n : ℂ)).re := by
    rw [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, mul_zero, sub_zero]
    have := Nat.cast_nonneg (α := ℝ) n
    positivity
  rw [Complex.inv_re]
  exact div_nonneg h1 (Complex.normSq_nonneg _)

/-- The ray point factors as the pure ray direction times a unit perturbation. -/
theorem rayPoint_factor {α : ℂ} (hre : 0 < α.re) {n : ℕ} (hn : 1 ≤ n) :
    rayPoint α n = (α * (n : ℂ)) * (1 + (α * (n : ℂ))⁻¹) := by
  have hpos := re_mul_natCast_pos hre hn
  have hne : α * (n : ℂ) ≠ 0 := by
    intro h
    rw [h] at hpos
    simp at hpos
  have hfac : (α * (n : ℂ)) * (1 + (α * (n : ℂ))⁻¹) = α * (n : ℂ) + 1 := by
    rw [mul_add, mul_one, mul_inv_cancel₀ hne]
  rw [rayPoint, hfac]
  ring

/-- **The ray logarithm splits into direction, size, and a unit perturbation.** -/
theorem log_rayPoint_split {α : ℂ} (hre : 0 < α.re) {n : ℕ} (hn : 1 ≤ n) :
    Complex.log (rayPoint α n)
      = Complex.log α + Complex.log (n : ℂ) + Complex.log (1 + (α * (n : ℂ))⁻¹) := by
  have hpos := re_mul_natCast_pos hre hn
  have hne : α * (n : ℂ) ≠ 0 := by
    intro h
    rw [h] at hpos
    simp at hpos
  have honere : 0 < (1 + (α * (n : ℂ))⁻¹).re := by
    have := re_inv_mul_natCast_nonneg hre n
    simp only [Complex.add_re, Complex.one_re]
    linarith
  have hone0 : (1 + (α * (n : ℂ))⁻¹) ≠ 0 := by
    intro h
    rw [h] at honere
    simp at honere
  have harg1 : |Complex.arg (α * (n : ℂ))| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hpos)
  have harg2 : |Complex.arg (1 + (α * (n : ℂ))⁻¹)| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl honere)
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [rayPoint_factor hre hn]
  rw [(Complex.log_mul_eq_add_log_iff hne hone0).mpr ?_]
  · rw [log_mul_natCast_of_re_pos hre hn]
  · constructor
    · have h1 := (abs_lt.mp harg1).1
      have h2 := (abs_lt.mp harg2).1
      linarith
    · have h1 := (abs_lt.mp harg1).2
      have h2 := (abs_lt.mp harg2).2
      linarith

/-- **The real part of the weighted ray logarithm.** -/
theorem re_mul_log_rayPoint {α : ℂ} (hre : 0 < α.re) {n : ℕ} (hn : 1 ≤ n) :
    (α * Complex.log (rayPoint α n)).re
      = (α * Complex.log α).re + α.re * Real.log n
        + (α * Complex.log (1 + (α * (n : ℂ))⁻¹)).re := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlogn : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
    rw [show ((n : ℂ)) = (((n : ℝ)) : ℂ) from by push_cast; ring]
    exact log_ofReal_of_pos hnpos
  rw [log_rayPoint_split hre hn, hlogn, mul_add, mul_add, Complex.add_re, Complex.add_re]
  congr 2
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

/-- The perturbation term is `O(1/n)`. -/
theorem abs_re_mul_log_one_add_inv_le {α : ℂ} (hre : 0 < α.re) {n : ℕ} (hn : 1 ≤ n)
    (hbig : 2 ≤ ‖α‖ * n) :
    |(α * Complex.log (1 + (α * (n : ℂ))⁻¹)).re| ≤ 2 / n := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hpos := re_mul_natCast_pos hre hn
  have hne : α * (n : ℂ) ≠ 0 := by
    intro h
    rw [h] at hpos
    simp at hpos
  have hαpos : (0 : ℝ) < ‖α‖ := by
    refine norm_pos_iff.mpr fun h => ?_
    rw [h] at hre
    simp at hre
  have hnormprod : ‖α * (n : ℂ)‖ = ‖α‖ * n := by
    rw [norm_mul, Complex.norm_natCast]
  have hξ : ‖(α * (n : ℂ))⁻¹‖ ≤ 1 / 2 := by
    rw [norm_inv, hnormprod]
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    linarith
  have hlog := norm_log_one_add_le_two_mul hξ
  have hstep : |(α * Complex.log (1 + (α * (n : ℂ))⁻¹)).re|
      ≤ ‖α * Complex.log (1 + (α * (n : ℂ))⁻¹)‖ := Complex.abs_re_le_norm _
  refine le_trans hstep ?_
  rw [norm_mul]
  have hnorminv : ‖(α * (n : ℂ))⁻¹‖ = 1 / (‖α‖ * n) := by
    rw [norm_inv, hnormprod, one_div]
  calc ‖α‖ * ‖Complex.log (1 + (α * (n : ℂ))⁻¹)‖
      ≤ ‖α‖ * (2 * ‖(α * (n : ℂ))⁻¹‖) := by
        exact mul_le_mul_of_nonneg_left hlog (le_of_lt hαpos)
    _ = 2 / (n : ℝ) := by
        rw [hnorminv]
        field_simp

/-! ## The logarithmic defect -/

/-- The linear growth slope of the real envelope, `Re(α log α) − r log r`. -/
def rayEnvelopeSlope (α : ℂ) : ℝ := (α * Complex.log α).re - α.re * Real.log α.re

/-- The logarithmic defect of the real envelope. -/
def rayEnvelopeDefect (α : ℂ) (n : ℕ) : ℝ :=
  Real.log ‖Complex.Gamma (rayPoint α n)‖
    - Real.log (Real.Gamma (1 + α.re * n)) - n * rayEnvelopeSlope α

theorem log_norm_Gamma_rayPoint_succ_sub {α : ℂ} (hre : 0 < α.re) (n : ℕ) :
    Real.log ‖Complex.Gamma (rayPoint α (n + 1))‖
        - Real.log ‖Complex.Gamma (rayPoint α n)‖
      = (α * Complex.log (rayPoint α n)).re + (rayShiftExponent α α n).re := by
  have hp := norm_Gamma_rayPoint_pos hre n
  have hstep := norm_Gamma_rayPoint_succ hre n
  rw [hstep, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_exp, Real.log_exp]
  ring

theorem re_ofReal_mul_log_ofReal {r : ℝ} (hr : 0 < r) :
    ((r : ℂ) * Complex.log (r : ℂ)).re = r * Real.log r := by
  rw [log_ofReal_of_pos hr, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

/-- **The one-step defect is the difference of two unit perturbations and two shift exponents.** -/
theorem rayEnvelopeDefect_succ_sub {α : ℂ} (hre : 0 < α.re) {n : ℕ} (hn : 1 ≤ n) :
    rayEnvelopeDefect α (n + 1) - rayEnvelopeDefect α n
      = ((α * Complex.log (1 + (α * (n : ℂ))⁻¹)).re
          - (((α.re : ℝ) : ℂ) * Complex.log (1 + (((α.re : ℝ) : ℂ) * (n : ℂ))⁻¹)).re)
        + ((rayShiftExponent α α n).re
          - (rayShiftExponent ((α.re : ℝ) : ℂ) ((α.re : ℝ) : ℂ) n).re) := by
  have hβre : (((α.re : ℝ) : ℂ)).re = α.re := Complex.ofReal_re _
  have hβpos : 0 < (((α.re : ℝ) : ℂ)).re := by rw [hβre]; exact hre
  have hcomplex := log_norm_Gamma_rayPoint_succ_sub hre n
  have hrealstep := log_norm_Gamma_rayPoint_succ_sub hβpos n
  simp only [norm_Gamma_rayPoint_ofReal hre] at hrealstep
  have hsplitα := re_mul_log_rayPoint hre hn
  have hsplitβ := re_mul_log_rayPoint hβpos hn
  rw [hβre, re_ofReal_mul_log_ofReal hre] at hsplitβ
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [rayEnvelopeDefect, rayEnvelopeDefect, rayEnvelopeSlope, hcast]
  push_cast at hrealstep
  linarith [hcomplex, hrealstep, hsplitα, hsplitβ]

/-! ## The one-step bound -/

theorem norm_ofReal_of_pos {x : ℝ} (h : 0 < x) : ‖((x : ℝ) : ℂ)‖ = x := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos h]

/-- The constant in the one-step defect bound. -/
def rayEnvelopeStepConst (α : ℂ) : ℝ :=
  4 + ‖α‖ * (6 + 2 * ‖α‖) / α.re + (6 + 2 * α.re)

theorem rayEnvelopeStepConst_nonneg {α : ℂ} (hre : 0 < α.re) :
    0 ≤ rayEnvelopeStepConst α := by
  have h := norm_nonneg α
  rw [rayEnvelopeStepConst]
  positivity

/-- **The one-step defect is `O(1/n)`.** -/
theorem abs_rayEnvelopeDefect_succ_sub_le {α : ℂ} (hre : 0 < α.re) {n : ℕ} (hn1 : 1 ≤ n)
    (hn : 2 * ‖α‖ + 4 ≤ (rayPoint α n).re) :
    |rayEnvelopeDefect α (n + 1) - rayEnvelopeDefect α n| ≤ rayEnvelopeStepConst α / n := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hαnorm : α.re ≤ ‖α‖ := Complex.re_le_norm α
  have hαpos : (0 : ℝ) < ‖α‖ := lt_of_lt_of_le hre hαnorm
  have hRval : (rayPoint α n).re = 1 + n * α.re := rayPoint_re α n
  have hR : (2 : ℝ) * ‖α‖ + 4 ≤ 1 + n * α.re := by rw [← hRval]; exact hn
  have hRpos : (0 : ℝ) < 1 + n * α.re := by nlinarith
  have hnα : (n : ℝ) * α.re ≤ 1 + n * α.re := by linarith
  have hβre : (((α.re : ℝ) : ℂ)).re = α.re := Complex.ofReal_re _
  have hβpos : 0 < (((α.re : ℝ) : ℂ)).re := by rw [hβre]; exact hre
  have hβnorm : ‖((α.re : ℝ) : ℂ)‖ = α.re := norm_ofReal_of_pos hre
  have hRβ : (rayPoint ((α.re : ℝ) : ℂ) n).re = 1 + n * α.re := by
    rw [rayPoint_re, hβre]
  have h1 : |(α * Complex.log (1 + (α * (n : ℂ))⁻¹)).re| ≤ 2 / n := by
    refine abs_re_mul_log_one_add_inv_le hre hn1 ?_
    nlinarith
  have h2 : |(((α.re : ℝ) : ℂ) * Complex.log (1 + (((α.re : ℝ) : ℂ) * (n : ℂ))⁻¹)).re|
      ≤ 2 / n := by
    refine abs_re_mul_log_one_add_inv_le hβpos hn1 ?_
    rw [hβnorm]
    nlinarith
  have h3 : |(rayShiftExponent α α n).re| ≤ ‖α‖ * (6 + 2 * ‖α‖) / ((n : ℝ) * α.re) := by
    have hbase := norm_rayShiftExponent_le (α := α) (w := α) hre (n := n) (by rw [hRval]; linarith)
    have habs : |(rayShiftExponent α α n).re| ≤ ‖rayShiftExponent α α n‖ :=
      Complex.abs_re_le_norm _
    refine le_trans (le_trans habs hbase) ?_
    rw [hRval]
    have hhalf : 3 / ((1 + n * α.re) - ‖α‖) ≤ 6 / (1 + n * α.re) := by
      rw [div_le_div_iff₀ (by linarith) hRpos]
      nlinarith
    have hstep : ‖α‖ * (3 / ((1 + n * α.re) - ‖α‖) + 2 * ‖α‖ / (1 + n * α.re))
        ≤ ‖α‖ * (6 / (1 + n * α.re) + 2 * ‖α‖ / (1 + n * α.re)) :=
      mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hαpos)
    refine le_trans hstep ?_
    have hcomb : ‖α‖ * (6 / (1 + n * α.re) + 2 * ‖α‖ / (1 + n * α.re))
        = ‖α‖ * (6 + 2 * ‖α‖) / (1 + n * α.re) := by
      field_simp
    rw [hcomb]
    refine div_le_div_of_nonneg_left (by positivity) (by positivity) hnα
  have h4 : |(rayShiftExponent ((α.re : ℝ) : ℂ) ((α.re : ℝ) : ℂ) n).re|
      ≤ (6 + 2 * α.re) / (n : ℝ) := by
    have hbase := norm_rayShiftExponent_le (α := ((α.re : ℝ) : ℂ)) (w := ((α.re : ℝ) : ℂ))
      hβpos (n := n) (by rw [hRβ, hβnorm]; linarith)
    have habs : |(rayShiftExponent ((α.re : ℝ) : ℂ) ((α.re : ℝ) : ℂ) n).re|
        ≤ ‖rayShiftExponent ((α.re : ℝ) : ℂ) ((α.re : ℝ) : ℂ) n‖ := Complex.abs_re_le_norm _
    refine le_trans (le_trans habs hbase) ?_
    rw [hRβ, hβnorm]
    have hhalf : 3 / ((1 + n * α.re) - α.re) ≤ 6 / (1 + n * α.re) := by
      rw [div_le_div_iff₀ (by linarith) hRpos]
      nlinarith
    have hstep : α.re * (3 / ((1 + n * α.re) - α.re) + 2 * α.re / (1 + n * α.re))
        ≤ α.re * (6 / (1 + n * α.re) + 2 * α.re / (1 + n * α.re)) :=
      mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hre)
    refine le_trans hstep ?_
    have hcomb : α.re * (6 / (1 + n * α.re) + 2 * α.re / (1 + n * α.re))
        = α.re * (6 + 2 * α.re) / (1 + n * α.re) := by
      field_simp
    rw [hcomb, div_le_div_iff₀ hRpos hnpos]
    nlinarith
  rw [rayEnvelopeDefect_succ_sub hre hn1]
  have hA := abs_sub ((α * Complex.log (1 + (α * (n : ℂ))⁻¹)).re)
    ((((α.re : ℝ) : ℂ) * Complex.log (1 + (((α.re : ℝ) : ℂ) * (n : ℂ))⁻¹)).re)
  have hB := abs_sub ((rayShiftExponent α α n).re)
    ((rayShiftExponent ((α.re : ℝ) : ℂ) ((α.re : ℝ) : ℂ) n).re)
  have hadd := abs_add_le
    ((α * Complex.log (1 + (α * (n : ℂ))⁻¹)).re
      - (((α.re : ℝ) : ℂ) * Complex.log (1 + (((α.re : ℝ) : ℂ) * (n : ℂ))⁻¹)).re)
    ((rayShiftExponent α α n).re
      - (rayShiftExponent ((α.re : ℝ) : ℂ) ((α.re : ℝ) : ℂ) n).re)
  have hsplit : rayEnvelopeStepConst α / (n : ℝ)
      = 2 / n + 2 / n + ‖α‖ * (6 + 2 * ‖α‖) / ((n : ℝ) * α.re) + (6 + 2 * α.re) / (n : ℝ) := by
    rw [rayEnvelopeStepConst]
    field_simp
    ring
  rw [hsplit]
  linarith

/-! ## The telescoped bound -/

/-- The one-step logarithmic lower bound `1/(a+1) ≤ log(a+1) − log a`. -/
theorem log_succ_lower_bound (a : ℝ) (ha : 0 < a) :
    (1 : ℝ) / (a + 1) ≤ Real.log (a + 1) - Real.log a := by
  have ha1 : (0 : ℝ) < a + 1 := by linarith
  have hlog := Real.log_le_sub_one_of_pos (show (0 : ℝ) < a / (a + 1) from div_pos ha ha1)
  rw [Real.log_div (ne_of_gt ha) (ne_of_gt ha1)] at hlog
  have hrhs : a / (a + 1) - 1 = -(1 / (a + 1)) := by
    field_simp
    ring
  rw [hrhs] at hlog
  linarith

/-- The index beyond which the one-step bound applies. -/
def rayEnvelopeThreshold (α : ℂ) : ℕ := ⌈(2 * ‖α‖ + 4) / α.re⌉₊ + 1

theorem one_le_rayEnvelopeThreshold (α : ℂ) : 1 ≤ rayEnvelopeThreshold α := by
  rw [rayEnvelopeThreshold]
  omega

theorem rayPoint_re_ge_of_threshold_le {α : ℂ} (hre : 0 < α.re) {n : ℕ}
    (hn : rayEnvelopeThreshold α ≤ n) : 2 * ‖α‖ + 4 ≤ (rayPoint α n).re := by
  have hceil : (2 * ‖α‖ + 4) / α.re ≤ (⌈(2 * ‖α‖ + 4) / α.re⌉₊ : ℝ) := Nat.le_ceil _
  have hnge : ((rayEnvelopeThreshold α : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [rayEnvelopeThreshold] at hnge
  push_cast at hnge
  have hdiv : (2 * ‖α‖ + 4) / α.re ≤ (n : ℝ) := by linarith
  rw [div_le_iff₀ hre] at hdiv
  rw [rayPoint_re]
  linarith

/-- **The defect grows at most logarithmically.** -/
theorem abs_rayEnvelopeDefect_le {α : ℂ} (hre : 0 < α.re) {n : ℕ}
    (hn : rayEnvelopeThreshold α ≤ n) :
    |rayEnvelopeDefect α n|
      ≤ |rayEnvelopeDefect α (rayEnvelopeThreshold α)|
        + 2 * rayEnvelopeStepConst α * Real.log n := by
  have hK := rayEnvelopeStepConst_nonneg hre
  induction n, hn using Nat.le_induction with
  | base =>
      have hone : (1 : ℝ) ≤ ((rayEnvelopeThreshold α : ℕ) : ℝ) := by
        exact_mod_cast one_le_rayEnvelopeThreshold α
      have hlog : 0 ≤ Real.log ((rayEnvelopeThreshold α : ℕ) : ℝ) := Real.log_nonneg hone
      nlinarith
  | succ n hn ih =>
      have hn1 : 1 ≤ n := le_trans (one_le_rayEnvelopeThreshold α) hn
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
      have hnone : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      have hstep := abs_rayEnvelopeDefect_succ_sub_le hre hn1
        (rayPoint_re_ge_of_threshold_le hre hn)
      have hlogstep : (1 : ℝ) / ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) + 1) - Real.log (n : ℝ) :=
        log_succ_lower_bound (n : ℝ) hnpos
      have hcast : (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      have hhalf : rayEnvelopeStepConst α / (n : ℝ)
          ≤ 2 * rayEnvelopeStepConst α * (1 / ((n : ℝ) + 1)) := by
        rw [div_le_iff₀ hnpos]
        have hfrac : (1 : ℝ) / ((n : ℝ) + 1) * (n : ℝ) ≥ 1 / 2 := by
          rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
          linarith
        nlinarith
      have htri : |rayEnvelopeDefect α (n + 1)|
          ≤ |rayEnvelopeDefect α n| + |rayEnvelopeDefect α (n + 1) - rayEnvelopeDefect α n| := by
        have := abs_add_le (rayEnvelopeDefect α n)
          (rayEnvelopeDefect α (n + 1) - rayEnvelopeDefect α n)
        simpa using this
      rw [hcast]
      nlinarith [htri, hstep, hhalf, ih, hlogstep, hK]

/-- **The uniform logarithmic bound on the defect.** -/
theorem exists_rayEnvelopeDefect_bound {α : ℂ} (hre : 0 < α.re) :
    ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧
      ∀ n : ℕ, 1 ≤ n → |rayEnvelopeDefect α n| ≤ C + K * Real.log n := by
  classical
  have hK : 0 ≤ 2 * rayEnvelopeStepConst α := by
    have := rayEnvelopeStepConst_nonneg hre
    linarith
  set n₀ : ℕ := rayEnvelopeThreshold α with hn₀
  have hne : (Finset.range (n₀ + 1)).Nonempty := ⟨0, by simp⟩
  set C₂ : ℝ := (Finset.range (n₀ + 1)).sup' hne (fun m => |rayEnvelopeDefect α m|) with hC₂
  have hC₂le : ∀ m : ℕ, m ≤ n₀ → |rayEnvelopeDefect α m| ≤ C₂ := by
    intro m hm
    exact Finset.le_sup' (fun m => |rayEnvelopeDefect α m|) (Finset.mem_range.mpr (by omega))
  have hC₂nonneg : 0 ≤ C₂ := le_trans (abs_nonneg _) (hC₂le 0 (Nat.zero_le _))
  refine ⟨C₂, 2 * rayEnvelopeStepConst α, hC₂nonneg, hK, ?_⟩
  intro n hn1
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
  rcases le_or_gt n₀ n with h | h
  · refine le_trans (abs_rayEnvelopeDefect_le hre h) ?_
    have := hC₂le n₀ le_rfl
    linarith
  · have hle := hC₂le n (le_of_lt h)
    nlinarith

/-! ## The envelope -/

/-- **The real factorial envelope of a complex ray.**  Up to a fixed polynomial factor, the modulus
of `Γ` along the ray `1 + αn` is the real factorial `Γ(1+rn)` times the exponential `e^{nS}`. -/
theorem exists_rayEnvelope {α : ℂ} (hre : 0 < α.re) :
    ∃ (B : ℕ) (C : ℝ), 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ‖Complex.Gamma (rayPoint α n)‖
          ≤ C * (n : ℝ) ^ B
            * (Real.exp (n * rayEnvelopeSlope α) * Real.Gamma (1 + α.re * n))
        ∧ Real.exp (n * rayEnvelopeSlope α) * Real.Gamma (1 + α.re * n)
          ≤ C * (n : ℝ) ^ B * ‖Complex.Gamma (rayPoint α n)‖ := by
  obtain ⟨C₀, K, hC₀, hKnn, hbound⟩ := exists_rayEnvelopeDefect_bound hre
  refine ⟨⌈K⌉₊, Real.exp C₀, Real.exp_pos _, ?_⟩
  intro n hn1
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hnone : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnone
  have hΓpos : 0 < ‖Complex.Gamma (rayPoint α n)‖ := norm_Gamma_rayPoint_pos hre n
  have hrpos : (0 : ℝ) < 1 + α.re * n := by
    have := Nat.cast_nonneg (α := ℝ) n
    nlinarith
  have hGpos : 0 < Real.Gamma (1 + α.re * n) := Real.Gamma_pos_of_pos hrpos
  -- the exponential form of the defect
  have hexp : ‖Complex.Gamma (rayPoint α n)‖
      = Real.exp (rayEnvelopeDefect α n)
        * (Real.exp (n * rayEnvelopeSlope α) * Real.Gamma (1 + α.re * n)) := by
    rw [rayEnvelopeDefect, Real.exp_sub, Real.exp_sub, Real.exp_log hΓpos, Real.exp_log hGpos]
    field_simp
  -- the polynomial bound on the exponentiated defect
  have hpow : Real.exp (K * Real.log (n : ℝ)) ≤ (n : ℝ) ^ (⌈K⌉₊) := by
    have hKle : K ≤ (⌈K⌉₊ : ℝ) := Nat.le_ceil K
    have hmono : Real.exp (K * Real.log (n : ℝ)) ≤ Real.exp ((⌈K⌉₊ : ℝ) * Real.log (n : ℝ)) := by
      refine Real.exp_le_exp.mpr ?_
      exact mul_le_mul_of_nonneg_right hKle hlogn
    refine le_trans hmono ?_
    rw [Real.exp_nat_mul, Real.exp_log hnpos]
  have hup : Real.exp (rayEnvelopeDefect α n) ≤ Real.exp C₀ * (n : ℝ) ^ (⌈K⌉₊) := by
    have h1 : rayEnvelopeDefect α n ≤ C₀ + K * Real.log (n : ℝ) :=
      le_trans (le_abs_self _) (hbound n hn1)
    calc Real.exp (rayEnvelopeDefect α n) ≤ Real.exp (C₀ + K * Real.log (n : ℝ)) :=
          Real.exp_le_exp.mpr h1
      _ = Real.exp C₀ * Real.exp (K * Real.log (n : ℝ)) := Real.exp_add _ _
      _ ≤ Real.exp C₀ * (n : ℝ) ^ (⌈K⌉₊) :=
          mul_le_mul_of_nonneg_left hpow (le_of_lt (Real.exp_pos _))
  have hdown : Real.exp (-(rayEnvelopeDefect α n)) ≤ Real.exp C₀ * (n : ℝ) ^ (⌈K⌉₊) := by
    have h1 : -(rayEnvelopeDefect α n) ≤ C₀ + K * Real.log (n : ℝ) :=
      le_trans (neg_le_abs _) (hbound n hn1)
    calc Real.exp (-(rayEnvelopeDefect α n)) ≤ Real.exp (C₀ + K * Real.log (n : ℝ)) :=
          Real.exp_le_exp.mpr h1
      _ = Real.exp C₀ * Real.exp (K * Real.log (n : ℝ)) := Real.exp_add _ _
      _ ≤ Real.exp C₀ * (n : ℝ) ^ (⌈K⌉₊) :=
          mul_le_mul_of_nonneg_left hpow (le_of_lt (Real.exp_pos _))
  have hprodpos : (0 : ℝ)
      < Real.exp (n * rayEnvelopeSlope α) * Real.Gamma (1 + α.re * n) := by positivity
  constructor
  · rw [hexp]
    exact mul_le_mul_of_nonneg_right hup (le_of_lt hprodpos)
  · have hrev : Real.exp (n * rayEnvelopeSlope α) * Real.Gamma (1 + α.re * n)
        = Real.exp (-(rayEnvelopeDefect α n)) * ‖Complex.Gamma (rayPoint α n)‖ := by
      rw [hexp, Real.exp_neg]
      field_simp
    rw [hrev]
    exact mul_le_mul_of_nonneg_right hdown (le_of_lt hΓpos)

end

end GaloisForLFunctions.HTGeometry
