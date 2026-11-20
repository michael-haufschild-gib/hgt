import GaloisForLFunctions.HagedornBootstrap.EdgeFunction
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Blaschke factors of the strip

On the strip `|Im b| < 1/2` the unit image charges at `±ζ` between the grounded edges are
described by

  `T_ζ(b) = tanh(π(b − ζ)/2) · tanh(π(b + ζ)/2) = (cosh πb − cosh πζ)/(cosh πb + cosh πζ)`.

This file proves the toolkit used to build the optimal bootstrap functional from these factors:

* the product formula above, and `|T_ζ(x)| < 1` on the real axis (so the site weight
  `f_x(y) = log|T_y(x)|` is negative);
* **(T3)** reflection `T_ζ(b + i) = 1/T_ζ(b)` for every `ζ`, and `T_ζ(i/2) = −1`;
* **(T1)** `|T_ζ| = 1` on the edges `Im b = 1/2` for real `ζ`;
* **(T2)** a detuned pair `ζ = χ ± iε`: on the real axis
  `|T_{χ+iε}(x)|² = ∏_± (cosh π(x ∓ χ) − cos πε)/(cosh π(x ∓ χ) + cos πε) ≥ T_χ(x)²`;
* **detuning costs `O(ε²)`:** each factor exceeds its undetuned value by at most
  `exp(2ε²/(x ∓ χ)²)`;
* the site weight has `∂_y f_x(y) = π/sinh π(y − x) + π/sinh π(y + x)`: it increases for `y > x`.
-/

noncomputable section

open Real

namespace GaloisForLFunctions.HagedornBootstrap

/-! ### The real factor -/

/-- The strip Blaschke factor on the real axis. -/
def stripT (ζ x : ℝ) : ℝ := (Real.cosh (π * x) - Real.cosh (π * ζ)) / (Real.cosh (π * x) + Real.cosh (π * ζ))

/-- The product formula `T_ζ(x) = tanh(π(x − ζ)/2) tanh(π(x + ζ)/2)`. -/
theorem stripT_eq_tanh_mul (ζ x : ℝ) :
    stripT ζ x = Real.tanh (π * (x - ζ) / 2) * Real.tanh (π * (x + ζ) / 2) := by
  set A := π * (x - ζ) / 2
  set B := π * (x + ζ) / 2
  have hx : π * x = B + A := by simp only [A, B]; ring
  have hζ : π * ζ = B - A := by simp only [A, B]; ring
  have hcA := Real.cosh_pos A
  have hcB := Real.cosh_pos B
  unfold stripT
  rw [hx, hζ, Real.cosh_add, Real.cosh_sub, Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh]
  have hden : Real.cosh B * Real.cosh A + Real.sinh B * Real.sinh A +
      (Real.cosh B * Real.cosh A - Real.sinh B * Real.sinh A) = 2 * (Real.cosh A * Real.cosh B) := by ring
  rw [hden]
  field_simp
  ring

theorem stripT_abs_lt_one (ζ x : ℝ) : |stripT ζ x| < 1 := by
  have h1 := Real.cosh_pos (π * x)
  have h2 := Real.cosh_pos (π * ζ)
  unfold stripT
  rw [abs_div, abs_of_pos (by linarith : 0 < Real.cosh (π * x) + Real.cosh (π * ζ)),
    div_lt_one (by linarith), abs_lt]
  constructor <;> linarith

/-- The site weight `f_x(y) = log|T_y(x)|` is negative. -/
theorem log_abs_stripT_neg {ζ x : ℝ} (h : stripT ζ x ≠ 0) : Real.log |stripT ζ x| < 0 :=
  Real.log_neg (abs_pos.mpr h) (stripT_abs_lt_one ζ x)

theorem stripT_eq_zero_iff (ζ x : ℝ) : stripT ζ x = 0 ↔ |x| = |ζ| := by
  have h1 := Real.cosh_pos (π * x)
  have h2 := Real.cosh_pos (π * ζ)
  unfold stripT
  rw [div_eq_zero_iff, or_iff_left (by linarith), sub_eq_zero]
  constructor
  · intro h
    rw [← Real.cosh_abs, ← Real.cosh_abs (π * ζ)] at h
    have := Real.cosh_injOn (Set.mem_Ici.mpr (abs_nonneg _)) (Set.mem_Ici.mpr (abs_nonneg _)) h
    rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos] at this
    exact mul_left_cancel₀ Real.pi_ne_zero this
  · intro h
    rw [← Real.cosh_abs, ← Real.cosh_abs (π * ζ), abs_mul, abs_mul, h]

/-! ### The complex factor: reflection and the edges -/

/-- The strip Blaschke factor on `ℂ`. -/
def stripTC (ζ b : ℂ) : ℂ :=
  (Complex.cosh (π * b) - Complex.cosh (π * ζ)) / (Complex.cosh (π * b) + Complex.cosh (π * ζ))

/-- **(T3) Reflection:** `T_ζ(b + i) = 1/T_ζ(b)` for all `ζ, b`. -/
theorem stripTC_add_I (ζ b : ℂ) : stripTC ζ (b + Complex.I) = (stripTC ζ b)⁻¹ := by
  unfold stripTC
  rw [show (π : ℂ) * (b + Complex.I) = π * b + π * Complex.I by ring, Complex.cosh_add_pi_mul_I,
    inv_div, show -Complex.cosh (π * b) - Complex.cosh (π * ζ) =
      -(Complex.cosh (π * b) + Complex.cosh (π * ζ)) by ring,
    show -Complex.cosh (π * b) + Complex.cosh (π * ζ) =
      -(Complex.cosh (π * b) - Complex.cosh (π * ζ)) by ring, neg_div_neg_eq]

/-- **(T3) The vacuum:** `T_ζ(i/2) = −1` for real `ζ`. -/
theorem stripTC_half_I (ζ : ℝ) : stripTC ζ (Complex.I / 2) = -1 := by
  unfold stripTC
  have hc : Complex.cosh (π * (Complex.I / 2)) = 0 := by
    rw [show (π : ℂ) * (Complex.I / 2) = ((π / 2 : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.cosh_mul_I, ← Complex.ofReal_cos, Real.cos_pi_div_two]; simp
  have hC : Complex.cosh (π * (ζ : ℂ)) ≠ 0 := by
    rw [show (π : ℂ) * (ζ : ℂ) = ((π * ζ : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cosh]
    exact_mod_cast (Real.cosh_pos _).ne'
  rw [hc, zero_sub, zero_add, neg_div, div_self hC]

/-- On the edge, `cosh π(x + i/2) = i sinh πx`. -/
theorem cosh_edge (x : ℝ) :
    Complex.cosh (π * ((x : ℂ) + Complex.I / 2)) = Complex.I * (Real.sinh (π * x) : ℂ) := by
  rw [show (π : ℂ) * ((x : ℂ) + Complex.I / 2) = ((π * x : ℝ) : ℂ) + ((π / 2 : ℝ) : ℂ) * Complex.I by
    push_cast; ring, Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two, Real.sin_pi_div_two,
    ← Complex.ofReal_sinh]
  push_cast
  ring

/-- **(T1)** `|T_ζ| = 1` on the edge `Im b = 1/2` for real `ζ`. -/
theorem norm_stripTC_edge (ζ x : ℝ) : ‖stripTC ζ ((x : ℂ) + Complex.I / 2)‖ = 1 := by
  unfold stripTC
  rw [cosh_edge, show (π : ℂ) * (ζ : ℂ) = ((π * ζ : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cosh]
  set s := Real.sinh (π * x)
  set C := Real.cosh (π * ζ)
  have hC : 0 < C := Real.cosh_pos _
  have hden : Complex.I * (s : ℂ) + (C : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hconj : (starRingEnd ℂ) (Complex.I * (s : ℂ) + (C : ℂ)) = -(Complex.I * (s : ℂ) - (C : ℂ)) := by
    simp [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
  rw [norm_div, div_eq_one_iff_eq (by simpa using hden), ← Complex.norm_conj (Complex.I * (s : ℂ) + (C : ℂ)),
    hconj, norm_neg]

/-! ### Detuned pairs -/

/-- The modulus of a detuned pair on the real axis, in product form. -/
def pairModulus (χ ε x : ℝ) : ℝ :=
  (Real.cosh (π * (x - χ)) - Real.cos (π * ε)) / (Real.cosh (π * (x - χ)) + Real.cos (π * ε)) *
    ((Real.cosh (π * (x + χ)) - Real.cos (π * ε)) / (Real.cosh (π * (x + χ)) + Real.cos (π * ε)))

/-- The pair identity behind (T2):
`(cosh π(x−χ) − γ)(cosh π(x+χ) − γ) = (cosh πx − γ cosh πχ)² + (1 − γ²) sinh² πχ`. -/
theorem pair_factor_identity (χ x γ : ℝ) :
    (Real.cosh (π * (x - χ)) - γ) * (Real.cosh (π * (x + χ)) - γ) =
      (Real.cosh (π * x) - γ * Real.cosh (π * χ)) ^ 2 + (1 - γ ^ 2) * Real.sinh (π * χ) ^ 2 := by
  rw [show π * (x - χ) = π * x - π * χ by ring, show π * (x + χ) = π * x + π * χ by ring,
    Real.cosh_sub, Real.cosh_add]
  have h1 := Real.cosh_sq (π * x)
  have h2 := Real.cosh_sq (π * χ)
  nlinarith [h1, h2]

/-- **(T2)** `|cosh πx − cosh π(χ + iε)|² = (cosh π(x−χ) − cos πε)(cosh π(x+χ) − cos πε)`. -/
theorem normSq_cosh_sub_detuned (χ ε x : ℝ) :
    Complex.normSq ((Real.cosh (π * x) : ℂ) - Complex.cosh (π * ((χ : ℂ) + ε * Complex.I))) =
      (Real.cosh (π * (x - χ)) - Real.cos (π * ε)) * (Real.cosh (π * (x + χ)) - Real.cos (π * ε)) := by
  rw [pair_factor_identity]
  rw [show (π : ℂ) * ((χ : ℂ) + ε * Complex.I) = ((π * χ : ℝ) : ℂ) + ((π * ε : ℝ) : ℂ) * Complex.I by
    push_cast; ring, Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I, ← Complex.ofReal_cosh,
    ← Complex.ofReal_sinh, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  have hs := Real.sin_sq_add_cos_sq (π * ε)
  nlinarith [hs]

/-- `|cosh πx + cosh π(χ + iε)|²` is the corresponding plus-product. -/
theorem normSq_cosh_add_detuned (χ ε x : ℝ) :
    Complex.normSq ((Real.cosh (π * x) : ℂ) + Complex.cosh (π * ((χ : ℂ) + ε * Complex.I))) =
      (Real.cosh (π * (x - χ)) + Real.cos (π * ε)) * (Real.cosh (π * (x + χ)) + Real.cos (π * ε)) := by
  have h := pair_factor_identity χ x (-Real.cos (π * ε))
  rw [show Real.cosh (π * (x - χ)) + Real.cos (π * ε) = Real.cosh (π * (x - χ)) - -Real.cos (π * ε) by ring,
    show Real.cosh (π * (x + χ)) + Real.cos (π * ε) = Real.cosh (π * (x + χ)) - -Real.cos (π * ε) by ring, h]
  rw [show (π : ℂ) * ((χ : ℂ) + ε * Complex.I) = ((π * χ : ℝ) : ℂ) + ((π * ε : ℝ) : ℂ) * Complex.I by
    push_cast; ring, Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I, ← Complex.ofReal_cosh,
    ← Complex.ofReal_sinh, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  have hs := Real.sin_sq_add_cos_sq (π * ε)
  nlinarith [hs]

/-- **(T2)** The squared modulus of a detuned factor on the axis is the pair product. -/
theorem normSq_stripTC_detuned (χ ε x : ℝ) :
    Complex.normSq (stripTC ((χ : ℂ) + ε * Complex.I) (x : ℂ)) = pairModulus χ ε x := by
  unfold stripTC pairModulus
  rw [Complex.normSq_div, show (π : ℂ) * (x : ℂ) = ((π * x : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cosh, normSq_cosh_sub_detuned, normSq_cosh_add_detuned, div_mul_div_comm]

/-- Undetuned, the pair is the square of the real factor. -/
theorem pairModulus_zero (χ x : ℝ) : pairModulus χ 0 x = stripT χ x ^ 2 := by
  unfold pairModulus stripT
  rw [mul_zero, Real.cos_zero, div_mul_div_comm, div_pow]
  have hm := pair_factor_identity χ x 1
  have hp := pair_factor_identity χ x (-1)
  rw [show Real.cosh (π * (x - χ)) + 1 = Real.cosh (π * (x - χ)) - -1 by ring,
    show Real.cosh (π * (x + χ)) + 1 = Real.cosh (π * (x + χ)) - -1 by ring, hm, hp]
  congr 1 <;> ring

/-- The factor `(A − γ)/(A + γ)` decreases in `γ ∈ [0, 1]` for `A ≥ 1`. -/
theorem detune_factor_mono {A γ : ℝ} (hA : 1 ≤ A) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    (A - 1) / (A + 1) ≤ (A - γ) / (A + γ) := by
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- **Lifting a double zero off the axis raises the modulus there:** `T_χ(x)² ≤ |T_{χ+iε}(x)|²`
for `|ε| ≤ 1/2`. -/
theorem sq_stripT_le_pairModulus (χ x : ℝ) {ε : ℝ} (hε : |ε| ≤ 1 / 2) :
    stripT χ x ^ 2 ≤ pairModulus χ ε x := by
  have hγ0 : 0 ≤ Real.cos (π * ε) := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor <;> nlinarith [abs_le.mp hε, Real.pi_pos]
  have hγ1 := Real.cos_le_one (π * ε)
  rw [← pairModulus_zero]
  unfold pairModulus
  simp only [mul_zero, Real.cos_zero]
  have h1 := detune_factor_mono (Real.one_le_cosh (π * (x - χ))) hγ0 hγ1
  have h2 := detune_factor_mono (Real.one_le_cosh (π * (x + χ))) hγ0 hγ1
  have p1 : 0 ≤ (Real.cosh (π * (x - χ)) - 1) / (Real.cosh (π * (x - χ)) + 1) :=
    div_nonneg (by linarith [Real.one_le_cosh (π * (x - χ))]) (by linarith [Real.one_le_cosh (π * (x - χ))])
  have p2 : 0 ≤ (Real.cosh (π * (x + χ)) - 1) / (Real.cosh (π * (x + χ)) + 1) :=
    div_nonneg (by linarith [Real.one_le_cosh (π * (x + χ))]) (by linarith [Real.one_le_cosh (π * (x + χ))])
  exact mul_le_mul h1 h2 p2 (le_trans p1 h1)

/-- **Detuning costs `O(ε²/d²)` per factor:** for `A = cosh πd`, `d ≠ 0`, `|ε| ≤ 1/2`,
`(A − cos πε)/(A + cos πε) ≤ (A − 1)/(A + 1) · exp(2ε²/d²)`. -/
theorem detune_factor_le {d ε : ℝ} (hd : d ≠ 0) (hε : |ε| ≤ 1 / 2) :
    (Real.cosh (π * d) - Real.cos (π * ε)) / (Real.cosh (π * d) + Real.cos (π * ε)) ≤
      (Real.cosh (π * d) - 1) / (Real.cosh (π * d) + 1) * Real.exp (2 * ε ^ 2 / d ^ 2) := by
  set A := Real.cosh (π * d) with hA
  set γ := Real.cos (π * ε) with hγ
  have hγ0 : 0 ≤ γ := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor <;> nlinarith [abs_le.mp hε, Real.pi_pos]
  have hγ1 : γ ≤ 1 := Real.cos_le_one _
  -- `A − 1 ≥ (πd)²/2 > 0` and `1 − γ ≤ (πε)²/2`
  have hA1 : (π * d) ^ 2 / 2 ≤ A - 1 := by
    have := one_add_sq_div_two_le_cosh (abs_nonneg (π * d))
    rw [Real.cosh_abs, sq_abs] at this
    linarith
  have hπd : 0 < (π * d) ^ 2 := by positivity
  have hApos : 0 < A - 1 := by linarith
  have hγc : 1 - γ ≤ (π * ε) ^ 2 / 2 := by
    have := Real.one_sub_sq_div_two_le_cos (x := π * ε); linarith
  -- the ratio is `1 + 2A(1 − γ)/((A + γ)(A − 1)) ≤ 1 + 2(1 − γ)/(A − 1)`
  have hratio : (A - γ) / (A + γ) ≤ (A - 1) / (A + 1) * (1 + 2 * (1 - γ) / (A - 1)) := by
    rw [div_le_iff₀ (by linarith)]
    have e : (A - 1) / (A + 1) * (1 + 2 * (1 - γ) / (A - 1)) * (A + γ) =
        (A + 1 - 2 * γ) * (A + γ) / (A + 1) := by field_simp; ring
    rw [e, le_div_iff₀ (by linarith)]
    nlinarith
  have hsmall : 2 * (1 - γ) / (A - 1) ≤ 2 * ε ^ 2 / d ^ 2 := by
    rw [div_le_div_iff₀ hApos (by positivity)]
    have hd2 : 0 < d ^ 2 := by positivity
    have : 2 * (1 - γ) * d ^ 2 ≤ (π * ε) ^ 2 * d ^ 2 := by nlinarith
    have : (π * ε) ^ 2 * d ^ 2 = 2 * ε ^ 2 * ((π * d) ^ 2 / 2) := by ring
    nlinarith
  have hexp : 1 + 2 * (1 - γ) / (A - 1) ≤ Real.exp (2 * ε ^ 2 / d ^ 2) := by
    have := Real.add_one_le_exp (2 * ε ^ 2 / d ^ 2); linarith
  have hnn : 0 ≤ (A - 1) / (A + 1) := div_nonneg hApos.le (by linarith)
  exact hratio.trans (mul_le_mul_of_nonneg_left hexp hnn)

/-! ### The site weight -/

/-- `∂_y log|T_y(x)| = π/sinh π(y − x) + π/sinh π(y + x)` off the zeros. -/
theorem hasDerivAt_log_stripT {x y : ℝ} (h1 : y - x ≠ 0) (h2 : y + x ≠ 0) :
    HasDerivAt (fun y => Real.log (stripT y x))
      (π / Real.sinh (π * (y - x)) + π / Real.sinh (π * (y + x))) y := by
  have hcx := Real.cosh_pos (π * x)
  have hcy := Real.cosh_pos (π * y)
  have hs1 : Real.sinh (π * (y - x)) ≠ 0 := by
    rw [Ne, Real.sinh_eq_zero]; exact mul_ne_zero Real.pi_ne_zero h1
  have hs2 : Real.sinh (π * (y + x)) ≠ 0 := by
    rw [Ne, Real.sinh_eq_zero]; exact mul_ne_zero Real.pi_ne_zero h2
  have hprod : Real.sinh (π * (y - x)) * Real.sinh (π * (y + x)) =
      Real.cosh (π * y) ^ 2 - Real.cosh (π * x) ^ 2 := by
    rw [show π * (y - x) = π * y - π * x by ring, show π * (y + x) = π * y + π * x by ring,
      Real.sinh_sub, Real.sinh_add]
    have := Real.cosh_sq (π * x); have := Real.cosh_sq (π * y)
    nlinarith
  have hne : Real.cosh (π * x) - Real.cosh (π * y) ≠ 0 := by
    intro h
    have : Real.cosh (π * y) ^ 2 - Real.cosh (π * x) ^ 2 = 0 := by
      rw [show Real.cosh (π * y) = Real.cosh (π * x) by linarith]; ring
    rw [← hprod] at this
    exact mul_ne_zero hs1 hs2 this
  have hT : stripT y x ≠ 0 := div_ne_zero hne (by linarith)
  have hC : HasDerivAt (fun y => Real.cosh (π * y)) (Real.sinh (π * y) * π) y := by
    have h := (Real.hasDerivAt_cosh (π * y)).comp y ((hasDerivAt_id y).const_mul π)
    exact h.congr_deriv (by simp)
  have hTd : HasDerivAt (fun y => stripT y x)
      (-(2 * Real.cosh (π * x) * (Real.sinh (π * y) * π)) / (Real.cosh (π * x) + Real.cosh (π * y)) ^ 2) y := by
    unfold stripT
    refine (((hasDerivAt_const y (Real.cosh (π * x))).sub hC).div ((hasDerivAt_const y _).add hC)
      (by show Real.cosh (π * x) + Real.cosh (π * y) ≠ 0; linarith)).congr_deriv ?_
    simp only [Pi.add_apply, Pi.sub_apply]
    field_simp
    ring
  refine (hTd.log hT).congr_deriv ?_
  have hsum : Real.sinh (π * (y - x)) + Real.sinh (π * (y + x)) =
      2 * Real.sinh (π * y) * Real.cosh (π * x) := by
    rw [show π * (y - x) = π * y - π * x by ring, show π * (y + x) = π * y + π * x by ring,
      Real.sinh_sub, Real.sinh_add]; ring
  unfold stripT
  rw [div_add_div _ _ hs1 hs2, hprod, show π * Real.sinh (π * (y + x)) + Real.sinh (π * (y - x)) * π =
    π * (Real.sinh (π * (y - x)) + Real.sinh (π * (y + x))) by ring, hsum]
  have hplus : Real.cosh (π * x) + Real.cosh (π * y) ≠ 0 := by linarith
  have hdiff : Real.cosh (π * y) ^ 2 - Real.cosh (π * x) ^ 2 ≠ 0 := by
    rw [← hprod]; exact mul_ne_zero hs1 hs2
  field_simp
  ring

/-- Beyond the point, the site weight increases: `∂_y f_x(y) > 0` for `y > |x|`. -/
theorem log_stripT_deriv_pos {x y : ℝ} (hy : |x| < y) :
    0 < π / Real.sinh (π * (y - x)) + π / Real.sinh (π * (y + x)) := by
  have h1 : 0 < y - x := by linarith [le_abs_self x]
  have h2 : 0 < y + x := by linarith [neg_abs_le x]
  have := Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos h1)
  have := Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos h2)
  have := Real.pi_pos
  positivity

end GaloisForLFunctions.HagedornBootstrap
