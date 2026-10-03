import GaloisForLFunctions.RHTower.HamburgerTruncatedRadialIntegral
import GaloisForLFunctions.RHTower.HamburgerReflectedRadialLimit

/-!
# Hamburger's kernel on the line `Re s = 3/2`

For `Re τ > 0` write `A = arg(πτ²)`, `L = log‖τ‖`, and let
`k_τ(s) = π^{1−s/2} τ (πτ²)^{s/2−1}/sin(πs/2)` be Hamburger's kernel continued in `s`.

**Theorem** (`norm_offKernel_three_halves_sub_le`).  For `y ≤ −1`,
`‖k_τ(3/2 + iy) − c_τ e^{y κ_τ}‖ ≤ 4‖τ‖^{1/2} e^{πy}`, where
`κ_τ = iL + (π − A)/2` and `c_τ = 2iτ e^{−L/2 − iA/4 − 3πi/4}` with `‖c_τ‖ = 2‖τ‖^{1/2}`.

*Proof.*  `π^{1−s/2}(πτ²)^{s/2−1} = e^{(2L + iA)(s/2 − 1)}`.  With `u = e^{−iπs/2}`, `|u| = e^{πy/2}`,
one has `1/sin(πs/2) = 2iu/(1 − u²)`, so `1/sin(πs/2) − 2iu = 2iu³/(1 − u²)`, of modulus
`≤ 4|u|³`.

**Corollary** (`norm_integral_edge_term_le`).  For `n ≥ 1` with `n ≠ ‖τ‖` and `B ≤ −1`,
`‖∫_{y ≤ B} n^{−3/2−iy} k_τ(3/2 + iy) dy‖ ≤ n^{−3/2}(2‖τ‖^{1/2} e^{B(π−A)/2}/|L − log n| + 4‖τ‖^{1/2}e^{πB}/π)`.
The leading part is the exact integral `∫_{y≤B} e^{y(κ_τ − i log n)} dy = e^{B(κ_τ − i log n)}/(κ_τ − i log n)`.
These are the off-resonant terms of the right edge of the contour shift: for `τ = ε + im` only
`n = m` resonates.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

namespace RightEdgeKernel

open GaloisForLFunctions HamburgerStability TruncatedRadial

noncomputable section

/-- The leading coefficient `c_τ = 2iτ e^{−L/2 − iA/4 − 3πi/4}`. -/
def edgeCoeff (τ : ℂ) : ℂ :=
  2 * I * τ * cexp (-((Real.log ‖τ‖ : ℝ) : ℂ) / 2 - ((((Real.pi : ℂ) * τ ^ 2).arg : ℝ) : ℂ) * I / 4 -
    3 * (Real.pi : ℂ) * I / 4)

/-- The leading exponent `κ_τ = iL + (π − A)/2`. -/
def edgeExp (τ : ℂ) : ℂ :=
  ((Real.log ‖τ‖ : ℝ) : ℂ) * I + (((Real.pi - ((Real.pi : ℂ) * τ ^ 2).arg) / 2 : ℝ) : ℂ)

theorem edgeExp_re (τ : ℂ) : (edgeExp τ).re = (Real.pi - ((Real.pi : ℂ) * τ ^ 2).arg) / 2 := by
  simp [edgeExp]

theorem edgeExp_im (τ : ℂ) : (edgeExp τ).im = Real.log ‖τ‖ := by simp [edgeExp]

theorem norm_edgeCoeff {τ : ℂ} (hτ : τ ≠ 0) : ‖edgeCoeff τ‖ = 2 * ‖τ‖ ^ (1 / 2 : ℝ) := by
  have hτn : 0 < ‖τ‖ := norm_pos_iff.mpr hτ
  unfold edgeCoeff
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_exp, Complex.norm_I, Complex.norm_ofNat]
  have hre : (-((Real.log ‖τ‖ : ℝ) : ℂ) / 2 - ((((Real.pi : ℂ) * τ ^ 2).arg : ℝ) : ℂ) * I / 4 -
      3 * (Real.pi : ℂ) * I / 4).re = -(Real.log ‖τ‖) / 2 := by simp
  rw [hre, show -(Real.log ‖τ‖) / 2 = Real.log ‖τ‖ * (-(1 / 2 : ℝ)) by ring,
    ← Real.rpow_def_of_pos hτn]
  have e : ‖τ‖ ^ (1 / 2 : ℝ) = ‖τ‖ ^ ((1 : ℝ) + (-(1 / 2 : ℝ))) := by norm_num
  rw [e, Real.rpow_add hτn, Real.rpow_one]
  ring

/-- `π^{1−s/2}(πτ²)^{s/2−1} = e^{(2L + iA)(s/2 − 1)}`. -/
theorem pi_cpow_mul_cpow_eq {τ : ℂ} (hτ : τ ≠ 0) (s : ℂ) :
    (Real.pi : ℂ) ^ (1 - s / 2) * ((Real.pi : ℂ) * τ ^ 2) ^ (s / 2 - 1) =
      cexp ((2 * ((Real.log ‖τ‖ : ℝ) : ℂ) + ((((Real.pi : ℂ) * τ ^ 2).arg : ℝ) : ℂ) * I) *
        (s / 2 - 1)) := by
  have hpi := Real.pi_pos
  have hπ0 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast hpi.ne'
  have hz : (Real.pi : ℂ) * τ ^ 2 ≠ 0 := mul_ne_zero hπ0 (pow_ne_zero 2 hτ)
  have hτn : 0 < ‖τ‖ := norm_pos_iff.mpr hτ
  rw [Complex.cpow_def_of_ne_zero hπ0, Complex.cpow_def_of_ne_zero hz, ← Complex.exp_add]
  congr 1
  have hlogπ : Complex.log (Real.pi : ℂ) = ((Real.log Real.pi : ℝ) : ℂ) :=
    (Complex.ofReal_log hpi.le).symm
  have hlogz : Complex.log ((Real.pi : ℂ) * τ ^ 2) =
      ((Real.log Real.pi : ℝ) : ℂ) + 2 * ((Real.log ‖τ‖ : ℝ) : ℂ) +
        ((((Real.pi : ℂ) * τ ^ 2).arg : ℝ) : ℂ) * I := by
    have hn : ‖(Real.pi : ℂ) * τ ^ 2‖ = Real.pi * ‖τ‖ ^ 2 := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi]
    rw [Complex.log, hn, Real.log_mul hpi.ne' (by positivity), Real.log_pow]
    push_cast; ring
  rw [hlogπ, hlogz]
  ring

/-- `1/sin z = 2iu/(1 − u²)` with `u = e^{−iz}`, and the remainder bound
`‖1/sin z − 2iu‖ ≤ 4‖u‖³` when `‖u‖² ≤ 1/2`. -/
theorem norm_inv_sin_sub_le {z : ℂ} (hu : ‖cexp (-(z * I))‖ ^ 2 ≤ 1 / 2) :
    ‖(Complex.sin z)⁻¹ - 2 * I * cexp (-(z * I))‖ ≤ 4 * ‖cexp (-(z * I))‖ ^ 3 := by
  set u := cexp (-(z * I)) with hu_def
  have hu0 : u ≠ 0 := Complex.exp_ne_zero _
  have hinv : cexp (z * I) = u⁻¹ := by rw [hu_def, Complex.exp_neg, inv_inv]
  have hsin : Complex.sin z = (u - u⁻¹) * I / 2 := by
    rw [← hinv, hu_def]; simp only [Complex.sin, neg_mul]
  have hun : ‖u ^ 2‖ < 1 := by rw [norm_pow]; linarith
  have h1u : (1 : ℂ) - u ^ 2 ≠ 0 := by
    intro h
    have : u ^ 2 = 1 := by linear_combination -h
    rw [this, norm_one] at hun; exact lt_irrefl _ hun
  have hsin0 : Complex.sin z ≠ 0 := by
    rw [hsin]
    intro h
    have : u - u⁻¹ = 0 := by
      have hI : (I : ℂ) / 2 ≠ 0 := by simp [Complex.I_ne_zero]
      have := h
      rw [mul_div_assoc] at this
      exact (mul_eq_zero.mp this).resolve_right hI
    have : u ^ 2 = 1 := by field_simp at this; linear_combination this
    rw [this, norm_one] at hun; exact lt_irrefl _ hun
  have h2 : (u - u⁻¹) * u = u ^ 2 - 1 := by field_simp
  have hprod : (u - u⁻¹) * I / 2 * (2 * I * u / (1 - u ^ 2)) = 1 := by
    rw [show (u - u⁻¹) * I / 2 * (2 * I * u / (1 - u ^ 2)) =
      ((u - u⁻¹) * u) * (I * I) / (1 - u ^ 2) by ring, h2, Complex.I_mul_I]
    field_simp
    ring
  have hinv2 : (Complex.sin z)⁻¹ = 2 * I * u / (1 - u ^ 2) := by
    rw [hsin]; exact inv_eq_of_mul_eq_one_right hprod
  have hkey : (Complex.sin z)⁻¹ - 2 * I * u = 2 * I * u ^ 3 / (1 - u ^ 2) := by
    rw [hinv2]
    field_simp
    ring
  rw [hkey, norm_div, norm_mul, norm_mul, norm_pow, Complex.norm_I, Complex.norm_ofNat]
  have hden : 1 / 2 ≤ ‖(1 : ℂ) - u ^ 2‖ := by
    have := norm_sub_norm_le (1 : ℂ) (u ^ 2)
    rw [norm_one, norm_pow] at this
    linarith
  rw [div_le_iff₀ (by linarith)]
  have hu3 : 0 ≤ ‖u‖ ^ 3 := by positivity
  nlinarith

/-- **The kernel on `Re s = 3/2`**: a leading exponential plus an `e^{πy}` remainder. -/
theorem norm_offKernel_three_halves_sub_le {τ : ℂ} (hτ : 0 < τ.re) {y : ℝ} (hy : y ≤ -1) :
    ‖offKernel τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I) - edgeCoeff τ * cexp ((y : ℂ) * edgeExp τ)‖ ≤
      4 * ‖τ‖ ^ (1 / 2 : ℝ) * Real.exp (Real.pi * y) := by
  have hpi := Real.pi_pos
  have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτ; simp at hτ
  have hτn : 0 < ‖τ‖ := norm_pos_iff.mpr hτ0
  set s : ℂ := ((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I with hs
  set L : ℝ := Real.log ‖τ‖ with hL
  set A : ℝ := ((Real.pi : ℂ) * τ ^ 2).arg with hA
  set X : ℂ := cexp ((2 * (L : ℂ) + (A : ℂ) * I) * (s / 2 - 1)) with hX
  set z : ℂ := (Real.pi : ℂ) * s / 2 with hz
  set u : ℂ := cexp (-(z * I)) with hu
  have hoff : offKernel τ s = τ * X * (Complex.sin z)⁻¹ := by
    unfold offKernel
    rw [show (Real.pi : ℂ) ^ (1 - s / 2) * τ * ((Real.pi : ℂ) * τ ^ 2) ^ (s / 2 - 1) =
      τ * ((Real.pi : ℂ) ^ (1 - s / 2) * ((Real.pi : ℂ) * τ ^ 2) ^ (s / 2 - 1)) by ring,
      pi_cpow_mul_cpow_eq hτ0 s, div_eq_mul_inv]
  have hlead : τ * X * (2 * I * u) = edgeCoeff τ * cexp ((y : ℂ) * edgeExp τ) := by
    unfold edgeCoeff edgeExp
    rw [hX, hu, show τ * cexp ((2 * (L : ℂ) + (A : ℂ) * I) * (s / 2 - 1)) * (2 * I * cexp (-(z * I))) =
      2 * I * τ * (cexp ((2 * (L : ℂ) + (A : ℂ) * I) * (s / 2 - 1)) * cexp (-(z * I))) by ring,
      ← Complex.exp_add, mul_assoc (2 * I * τ), ← Complex.exp_add]
    congr 2
    rw [hz, hs]
    push_cast
    linear_combination (((A : ℂ) - Real.pi) * y / 2) * Complex.I_sq
  have hun : ‖u‖ = Real.exp (Real.pi * y / 2) := by
    rw [hu, Complex.norm_exp]
    congr 1
    rw [hz, hs]; simp
  have hu2 : ‖u‖ ^ 2 ≤ 1 / 2 := by
    rw [hun, ← Real.exp_nat_mul]
    have h1 : (2 : ℕ) * (Real.pi * y / 2) ≤ -1 := by push_cast; nlinarith [Real.pi_gt_three]
    calc Real.exp ((2 : ℕ) * (Real.pi * y / 2)) ≤ Real.exp (-1) := Real.exp_le_exp.mpr h1
      _ ≤ 1 / 2 := by
          have := Real.exp_one_gt_d9
          rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
          norm_num
          linarith
  have hXn : ‖X‖ = ‖τ‖ ^ (-(1 / 2 : ℝ)) * Real.exp (-(A * y / 2)) := by
    rw [hX, Complex.norm_exp]
    have hre : ((2 * (L : ℂ) + (A : ℂ) * I) * (s / 2 - 1)).re = L * (-(1 / 2 : ℝ)) + -(A * y / 2) := by
      rw [hs]; simp; ring
    rw [hre, Real.exp_add, hL, ← Real.rpow_def_of_pos hτn]
  have hrem := norm_inv_sin_sub_le (z := z) (by rw [← hu]; exact hu2)
  rw [← hu] at hrem
  have hA : A ≤ Real.pi := Complex.arg_le_pi _
  calc ‖offKernel τ s - edgeCoeff τ * cexp ((y : ℂ) * edgeExp τ)‖
      = ‖τ * X * ((Complex.sin z)⁻¹ - 2 * I * u)‖ := by
        rw [hoff, ← hlead]; congr 1; ring
    _ = ‖τ‖ * ‖X‖ * ‖(Complex.sin z)⁻¹ - 2 * I * u‖ := by rw [norm_mul, norm_mul]
    _ ≤ ‖τ‖ * (‖τ‖ ^ (-(1 / 2 : ℝ)) * Real.exp (-(A * y / 2))) * (4 * ‖u‖ ^ 3) := by
        rw [hXn]; gcongr
    _ = 4 * (‖τ‖ * ‖τ‖ ^ (-(1 / 2 : ℝ))) *
          (Real.exp (-(A * y / 2)) * Real.exp (Real.pi * y / 2) ^ 3) := by
        rw [hun]; ring
    _ = 4 * (‖τ‖ * ‖τ‖ ^ (-(1 / 2 : ℝ))) * Real.exp (y * ((3 * Real.pi - A) / 2)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 2
        push_cast; ring
    _ ≤ 4 * ‖τ‖ ^ (1 / 2 : ℝ) * Real.exp (Real.pi * y) := by
        have e : ‖τ‖ * ‖τ‖ ^ (-(1 / 2 : ℝ)) = ‖τ‖ ^ (1 / 2 : ℝ) := by
          have e1 : ‖τ‖ ^ (1 / 2 : ℝ) = ‖τ‖ ^ ((1 : ℝ) + (-(1 / 2 : ℝ))) := by norm_num
          rw [e1, Real.rpow_add hτn, Real.rpow_one]
        rw [e]
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
        nlinarith

/-! ### The off-resonant right-edge integrals -/

theorem natCast_cpow_eq_exp {n : ℕ} (hn : 1 ≤ n) (w : ℂ) :
    (n : ℂ) ^ w = cexp (((Real.log n : ℝ) : ℂ) * w) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (show n ≠ 0 by omega)),
    ← Complex.ofReal_natCast, ← Complex.ofReal_log (by positivity)]

theorem integral_exp_mul_Iic_real {c : ℝ} (hc : 0 < c) (B : ℝ) :
    ∫ y in Iic B, Real.exp (c * y) = Real.exp (c * B) / c := by
  have hint : IntegrableOn (fun y : ℝ => Real.exp (c * y)) (Iic B) := by
    have h : IntegrableOn (fun y : ℝ => ‖cexp ((c : ℂ) * (y : ℂ))‖) (Iic B) :=
      (integrableOn_exp_mul_complex_Iic (a := (c : ℂ)) (by simpa using hc) B).norm
    refine h.congr_fun (fun y _ => ?_) measurableSet_Iic
    show ‖cexp ((c : ℂ) * (y : ℂ))‖ = Real.exp (c * y)
    rw [Complex.norm_exp]
    congr 1; simp
  have hcont : ContinuousWithinAt (fun y : ℝ => Real.exp (c * y) / c) (Iic B) B :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).div_const c).continuousWithinAt
  have hder : ∀ y ∈ Iio B, HasDerivAt (fun y : ℝ => Real.exp (c * y) / c) (Real.exp (c * y)) y := by
    intro y _
    have := ((Real.hasDerivAt_exp (c * y)).comp y ((hasDerivAt_id y).const_mul c)).div_const c
    refine this.congr_deriv ?_
    field_simp
  have hlim : Tendsto (fun y : ℝ => Real.exp (c * y) / c) atBot (𝓝 0) := by
    have h : Tendsto (fun y : ℝ => c * y) atBot atBot := tendsto_id.const_mul_atBot hc
    have h2 := (Real.tendsto_exp_atBot.comp h).div_const c
    simpa using h2
  rw [integral_Iic_of_hasDerivAt_of_tendsto hcont hder hint hlim, sub_zero]

/-- **Off-resonant right-edge integral at a real frequency.**  For `ℓ ≠ log‖τ‖` and `B ≤ −1`,
`‖∫_{y≤B} e^{−ℓ(3/2+iy)} k_τ(3/2+iy) dy‖ ≤
  e^{−3ℓ/2}(2‖τ‖^{1/2} e^{B(π−A)/2}/|log‖τ‖ − ℓ| + 4‖τ‖^{1/2} e^{πB}/π)`. -/
theorem norm_integral_edge_exp_le {τ : ℂ} (hτ : 0 < τ.re) {ln : ℝ}
    (hne : Real.log ‖τ‖ ≠ ln) {B : ℝ} (hB : B ≤ -1) :
    ‖∫ y in Iic B, cexp (-((ln : ℂ) * (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I))) *
        offKernel τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
      Real.exp (-(3 / 2 * ln)) * (2 * ‖τ‖ ^ (1 / 2 : ℝ) *
        Real.exp (B * ((Real.pi - ((Real.pi : ℂ) * τ ^ 2).arg) / 2)) /
          |Real.log ‖τ‖ - ln| + 4 * ‖τ‖ ^ (1 / 2 : ℝ) * Real.exp (Real.pi * B) / Real.pi) := by
  have hpi := Real.pi_pos
  have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτ; simp at hτ
  set A : ℝ := ((Real.pi : ℂ) * τ ^ 2).arg with hA
  have hAlt : A < Real.pi := by
    have h := abs_arg_pi_mul_sq_le hτ
    have hδ : 0 < τ.re / ‖τ‖ := div_pos hτ (norm_pos_iff.mpr hτ0)
    have := le_abs_self A
    linarith
  set a : ℂ := edgeExp τ - (ln : ℂ) * I with ha
  have hare : 0 < a.re := by
    rw [ha, Complex.sub_re, edgeExp_re, ← hA]; simp; linarith
  have haim : a.im = Real.log ‖τ‖ - ln := by rw [ha, Complex.sub_im, edgeExp_im]; simp
  set r : ℝ → ℂ := fun y => offKernel τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I) -
    edgeCoeff τ * cexp ((y : ℂ) * edgeExp τ) with hr
  have hnpow : ∀ y : ℝ, cexp (-((ln : ℂ) * (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I))) =
      ((Real.exp (-(3 / 2 * ln)) : ℝ) : ℂ) * cexp (-((y : ℂ) * (ln : ℂ) * I)) := by
    intro y
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1; push_cast; ring
  have hsplit : ∀ y : ℝ, cexp (-((ln : ℂ) * (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I))) *
      offKernel τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I) =
        ((Real.exp (-(3 / 2 * ln)) : ℝ) : ℂ) * (edgeCoeff τ * cexp (a * (y : ℂ)) +
          cexp (-((y : ℂ) * (ln : ℂ) * I)) * r y) := by
    intro y
    rw [hnpow]
    simp only [hr]
    have e : cexp (-((y : ℂ) * (ln : ℂ) * I)) * cexp ((y : ℂ) * edgeExp τ) = cexp (a * (y : ℂ)) := by
      rw [← Complex.exp_add, ha]; congr 1; ring
    linear_combination ((Real.exp (-(3 / 2 * ln)) : ℝ) : ℂ) * edgeCoeff τ * e
  -- the leading exponential
  have hI1 : ∫ y in Iic B, cexp (a * (y : ℂ)) = cexp (a * B) / a := integral_exp_mul_complex_Iic hare B
  have hint1 : IntegrableOn (fun y : ℝ => cexp (a * (y : ℂ))) (Iic B) :=
    integrableOn_exp_mul_complex_Iic hare B
  -- the remainder
  have hrb : ∀ y ∈ Iic B, ‖cexp (-((y : ℂ) * (ln : ℂ) * I)) * r y‖ ≤
      4 * ‖τ‖ ^ (1 / 2 : ℝ) * Real.exp (Real.pi * y) := by
    intro y hy
    rw [norm_mul, show -((y : ℂ) * (ln : ℂ) * I) = ((-(y * ln) : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, one_mul]
    exact norm_offKernel_three_halves_sub_le hτ (le_trans hy hB)
  have hrc : Continuous fun y : ℝ => cexp (-((y : ℂ) * (ln : ℂ) * I)) * r y := by
    have hk : Continuous fun y : ℝ => offKernel τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I) := by
      rw [continuous_iff_continuousAt]
      intro y
      have hre : (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I).re = 3 / 2 := by simp
      exact (differentiableAt_offKernel hτ0 (by rw [hre]; norm_num)
        (by rw [hre]; norm_num)).continuousAt.comp (by fun_prop)
    simp only [hr]
    fun_prop
  have hexpint : IntegrableOn (fun y : ℝ => 4 * ‖τ‖ ^ (1 / 2 : ℝ) * Real.exp (Real.pi * y)) (Iic B) := by
    have h : IntegrableOn (fun y : ℝ => 4 * ‖τ‖ ^ (1 / 2 : ℝ) * ‖cexp ((Real.pi : ℂ) * (y : ℂ))‖)
        (Iic B) :=
      ((integrableOn_exp_mul_complex_Iic (a := (Real.pi : ℂ)) (by simpa using hpi) B).norm).const_mul _
    refine h.congr_fun (fun y _ => ?_) measurableSet_Iic
    show 4 * ‖τ‖ ^ (1 / 2 : ℝ) * ‖cexp ((Real.pi : ℂ) * (y : ℂ))‖ =
      4 * ‖τ‖ ^ (1 / 2 : ℝ) * Real.exp (Real.pi * y)
    rw [Complex.norm_exp]
    congr 2; simp
  have hint2 : IntegrableOn (fun y : ℝ => cexp (-((y : ℂ) * (ln : ℂ) * I)) * r y) (Iic B) :=
    hexpint.mono' hrc.aestronglyMeasurable ((ae_restrict_iff' measurableSet_Iic).mpr
      (Eventually.of_forall hrb))
  have hI2 : ‖∫ y in Iic B, cexp (-((y : ℂ) * (ln : ℂ) * I)) * r y‖ ≤
      4 * ‖τ‖ ^ (1 / 2 : ℝ) * Real.exp (Real.pi * B) / Real.pi := by
    refine (norm_integral_le_of_norm_le hexpint ((ae_restrict_iff' measurableSet_Iic).mpr
      (Eventually.of_forall hrb))).trans (le_of_eq ?_)
    rw [integral_const_mul, integral_exp_mul_Iic_real hpi B]
    ring
  have hare' : a.re = (Real.pi - A) / 2 := by
    rw [ha, Complex.sub_re, edgeExp_re, ← hA]; simp
  have hI1n : ‖∫ y in Iic B, cexp (a * (y : ℂ))‖ ≤
      Real.exp (B * ((Real.pi - A) / 2)) / |Real.log ‖τ‖ - ln| := by
    rw [hI1, norm_div, Complex.norm_exp]
    have hre : (a * (B : ℂ)).re = B * ((Real.pi - A) / 2) := by
      simp [Complex.mul_re, hare']; ring
    rw [hre]
    have habs : |Real.log ‖τ‖ - ln| ≤ ‖a‖ := by rw [← haim]; exact Complex.abs_im_le_norm a
    have hpos : 0 < |Real.log ‖τ‖ - ln| := abs_pos.mpr (sub_ne_zero.mpr hne)
    exact div_le_div_of_nonneg_left (Real.exp_pos _).le hpos habs
  have hcalc : ∫ y in Iic B, cexp (-((ln : ℂ) * (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I))) *
      offKernel τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I) =
        ((Real.exp (-(3 / 2 * ln)) : ℝ) : ℂ) * (edgeCoeff τ * (∫ y in Iic B, cexp (a * (y : ℂ))) +
          ∫ y in Iic B, cexp (-((y : ℂ) * (ln : ℂ) * I)) * r y) := by
    simp only [hsplit]
    rw [integral_const_mul, integral_add (hint1.const_mul _) hint2, integral_const_mul]
  have hnn : (0 : ℝ) ≤ Real.exp (-(3 / 2 * ln)) := (Real.exp_pos _).le
  rw [hcalc, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
  refine mul_le_mul_of_nonneg_left ?_ hnn
  calc ‖edgeCoeff τ * (∫ y in Iic B, cexp (a * (y : ℂ))) +
        ∫ y in Iic B, cexp (-((y : ℂ) * (ln : ℂ) * I)) * r y‖
      ≤ ‖edgeCoeff τ‖ * ‖∫ y in Iic B, cexp (a * (y : ℂ))‖ +
          ‖∫ y in Iic B, cexp (-((y : ℂ) * (ln : ℂ) * I)) * r y‖ := by
        refine (norm_add_le _ _).trans (le_of_eq ?_); rw [norm_mul]
    _ ≤ 2 * ‖τ‖ ^ (1 / 2 : ℝ) * (Real.exp (B * ((Real.pi - A) / 2)) / |Real.log ‖τ‖ - ln|) +
          4 * ‖τ‖ ^ (1 / 2 : ℝ) * Real.exp (Real.pi * B) / Real.pi := by
        rw [norm_edgeCoeff hτ0]
        gcongr
    _ = _ := by ring


/-- **Off-resonant right-edge integral.**  For `n ≥ 1`, `log n ≠ log‖τ‖` and `B ≤ −1`,
`‖∫_{y≤B} n^{−3/2−iy} k_τ(3/2+iy) dy‖ ≤
  n^{−3/2}(2‖τ‖^{1/2} e^{B(π−A)/2}/|log‖τ‖ − log n| + 4‖τ‖^{1/2} e^{πB}/π)`. -/
theorem norm_integral_edge_term_le {τ : ℂ} (hτ : 0 < τ.re) {n : ℕ} (hn : 1 ≤ n)
    (hne : Real.log ‖τ‖ ≠ Real.log n) {B : ℝ} (hB : B ≤ -1) :
    ‖∫ y in Iic B, (n : ℂ) ^ (-(((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) *
        offKernel τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
      (n : ℝ) ^ (-(3 / 2 : ℝ)) * (2 * ‖τ‖ ^ (1 / 2 : ℝ) *
        Real.exp (B * ((Real.pi - ((Real.pi : ℂ) * τ ^ 2).arg) / 2)) /
          |Real.log ‖τ‖ - Real.log n| + 4 * ‖τ‖ ^ (1 / 2 : ℝ) * Real.exp (Real.pi * B) / Real.pi) := by
  have hpow : ∀ y : ℝ, (n : ℂ) ^ (-(((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) =
      cexp (-(((Real.log n : ℝ) : ℂ) * (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I))) := by
    intro y; rw [natCast_cpow_eq_exp hn]; ring_nf
  have he : Real.exp (-(3 / 2 * Real.log n)) = (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
    rw [Real.rpow_def_of_pos (by exact_mod_cast (show 0 < n by omega))]; ring_nf
  simp only [hpow]
  rw [← he]
  exact norm_integral_edge_exp_le hτ hne hB
end

end RightEdgeKernel

end RHTower
