import GaloisForLFunctions.HilbertMetric.Geometry.BonnetSurface

/-!
# Complex phase of the principal directions

For a symmetric real two-dimensional operator, the square of a unit
principal direction is the normalized trace-free Hessian symbol, with
opposite signs for the two eigenvalues. Squaring removes the sign of
the vector and therefore describes the unoriented eigenline.
-/

open Complex
open scoped ComplexConjugate ContDiff
namespace GaloisForLFunctions.HilbertMetric.Geometry.PrincipalLinePhase
noncomputable section

/-- The actual symmetric real matrix action in complex coordinates. -/
def symmetricAction (a b c : ℝ) (z : ℂ) : ℂ :=
  ((a * z.re + b * z.im : ℝ) : ℂ) + ((b * z.re + c * z.im : ℝ) : ℂ) * I

/-- Complex coordinate of the trace-free part of a symmetric matrix. -/
def symbol (a b c : ℝ) : ℂ := ((a - c : ℝ) : ℂ) + 2 * (b : ℂ) * I

theorem symmetricAction_decomposition (a b c : ℝ) (z : ℂ) :
    symmetricAction a b c z = ((a + c : ℝ) : ℂ) / 2 * z + symbol a b c / 2 * conj z := by
  apply Complex.ext <;> simp [symmetricAction, symbol, Complex.mul_re, Complex.mul_im] <;> ring

/-- The symbol vanishes exactly for scalar matrices. -/
theorem symbol_zero_iff (a b c : ℝ) : symbol a b c = 0 ↔ a = c ∧ b = 0 := by
  constructor
  · intro h
    have hr : a = c := by simpa [symbol, sub_eq_zero] using congrArg Complex.re h
    have hi : b = 0 := by simpa [symbol] using congrArg Complex.im h
    exact ⟨hr, hi⟩
  · rintro ⟨rfl, rfl⟩
    simp [symbol]

/-- The exact eigenvector equation after removing the orientation of a unit vector. -/
theorem eigenvector_iff_squared_phase (a b c lam : ℝ) {v : ℂ} (hv : ‖v‖ = 1) :
    symmetricAction a b c v = (lam : ℂ) * v ↔
      symbol a b c = ((2 * lam - a - c : ℝ) : ℂ) * v ^ 2 := by
  have hv0 : v ≠ 0 := by intro h; rw [h, norm_zero] at hv; norm_num at hv
  have hvc : v * conj v = 1 := by
    rw [Complex.mul_conj, ← Complex.sq_norm, hv]
    norm_num
  have hm : symmetricAction a b c v * v =
      ((a + c : ℝ) : ℂ) / 2 * v ^ 2 + symbol a b c / 2 := by
    rw [symmetricAction_decomposition]
    calc
      _ = ((a + c : ℝ) : ℂ) / 2 * v ^ 2 + symbol a b c / 2 * (v * conj v) := by ring
      _ = _ := by rw [hvc, mul_one]
  constructor
  · intro h
    rw [h] at hm
    push_cast
    push_cast at hm
    linear_combination -2 * hm
  · intro h
    apply mul_right_cancel₀ hv0
    rw [hm, h]
    push_cast
    ring

/-- The larger principal eigenvalue. -/
def eigenPlus (a b c : ℝ) : ℝ := (a + c + ‖symbol a b c‖) / 2

/-- The smaller principal eigenvalue. -/
def eigenMinus (a b c : ℝ) : ℝ := (a + c - ‖symbol a b c‖) / 2

/-- Distinct principal eigenvalues are exactly nonzero trace-free symbol. -/
theorem eigenMinus_lt_eigenPlus (a b c : ℝ) (h : symbol a b c ≠ 0) :
    eigenMinus a b c < eigenPlus a b c := by
  have hp := norm_pos_iff.mpr h
  unfold eigenMinus eigenPlus
  linarith only [hp]

/-- The larger-eigenvalue line is represented exactly by the normalized complex symbol. -/
theorem eigenPlus_iff_phase (a b c : ℝ) (h : symbol a b c ≠ 0) {v : ℂ} (hv : ‖v‖ = 1) :
    symmetricAction a b c v = (eigenPlus a b c : ℂ) * v ↔
      v ^ 2 = symbol a b c / (‖symbol a b c‖ : ℂ) := by
  have hn : (‖symbol a b c‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h)
  rw [eigenvector_iff_squared_phase a b c _ hv]
  have he : 2 * eigenPlus a b c - a - c = ‖symbol a b c‖ := by unfold eigenPlus; ring
  rw [he]
  constructor
  · intro he
    apply (eq_div_iff hn).mpr
    simpa only [mul_comm] using he.symm
  · intro he
    have hm := (eq_div_iff hn).mp he
    simpa only [mul_comm] using hm.symm

/-- The smaller-eigenvalue line is the orthogonal line, with opposite squared phase. -/
theorem eigenMinus_iff_phase (a b c : ℝ) (h : symbol a b c ≠ 0) {v : ℂ} (hv : ‖v‖ = 1) :
    symmetricAction a b c v = (eigenMinus a b c : ℂ) * v ↔
      v ^ 2 = -symbol a b c / (‖symbol a b c‖ : ℂ) := by
  have hn : (‖symbol a b c‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h)
  rw [eigenvector_iff_squared_phase a b c _ hv]
  have he : 2 * eigenMinus a b c - a - c = -‖symbol a b c‖ := by unfold eigenMinus; ring
  rw [he, Complex.ofReal_neg]
  constructor
  · intro he
    apply (eq_div_iff hn).mpr
    linear_combination he
  · intro he
    have hm := (eq_div_iff hn).mp he
    linear_combination hm

open StereographicFrame BonnetSurface BonnetSupport

/-- The conformal tangent frame applied to a complex coordinate vector. -/
def tangentFrame (p : ℝ × ℝ) (v : ℂ) : Space := v.re • tangentX p + v.im • tangentY p

theorem tangentFrame_injective (p : ℝ × ℝ) : Function.Injective (tangentFrame p) := by
  intro v w h
  obtain ⟨hxx, hyy, hxy⟩ := tangent_metric p
  have hyx : inner ℝ (tangentY p) (tangentX p) = 0 := by rw [real_inner_comm, hxy]
  have hx := congrArg (fun t => inner ℝ t (tangentX p)) h
  have hy := congrArg (fun t => inner ℝ t (tangentY p)) h
  simp only [tangentFrame, inner_add_left, inner_smul_left, starRingEnd_apply, star_trivial,
    hxx, hyy, hxy, hyx, mul_zero, add_zero, zero_add] at hx hy
  have hc : (2 / denominator p) ^ 2 ≠ 0 := pow_ne_zero 2
    (div_ne_zero (by norm_num) (denominator_pos p).ne')
  exact Complex.ext (mul_right_cancel₀ hc hx) (mul_right_cancel₀ hc hy)

theorem tangentFrame_real_mul (p : ℝ × ℝ) (lam : ℝ) (v : ℂ) :
    tangentFrame p ((lam : ℂ) * v) = lam • tangentFrame p v := by
  simp only [tangentFrame, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, add_zero, smul_add, mul_smul]

/-- The tangent frame is exactly the actual normal differential. -/
theorem normal_fderiv_eq_frame (p : ℝ × ℝ) (v : ℂ) :
    fderiv ℝ normal p (v.re, v.im) = tangentFrame p v := by
  have hn := (normal_smooth.differentiable (by simp) p).hasFDerivAt
  have hx := (hn.comp_hasDerivAt p.1
    ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))).deriv
  have hy := (hn.comp_hasDerivAt p.2
    ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))).deriv
  change deriv (fun t => normal (t, p.2)) p.1 = fderiv ℝ normal p (1, 0) at hx
  change deriv (fun t => normal (p.1, t)) p.2 = fderiv ℝ normal p (0, 1) at hy
  rw [(normal_partials p).1] at hx
  rw [(normal_partials p).2] at hy
  have he : (v.re, v.im) = v.re • ((1 : ℝ), (0 : ℝ)) + v.im • ((0 : ℝ), (1 : ℝ)) := by simp
  rw [he, map_add, map_smul, map_smul, ← hx, ← hy]
  rfl

/-- The actual surface differential is the radius matrix followed by the same conformal frame. -/
theorem surface_fderiv_eq_frame {ρ : ℝ × ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (p : ℝ × ℝ) (v : ℂ) :
    fderiv ℝ (surface ρ) p (v.re, v.im) =
      tangentFrame p (symmetricAction (radiusXX ρ p) (radiusXY ρ p) (radiusYY ρ p) v) := by
  rw [surface_fderiv_apply hρ, (surface_partials hρ p).1, (surface_partials hρ p).2]
  simp only [tangentFrame, symmetricAction, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, sub_zero, add_zero, zero_add, mul_one]
  module

/-- A principal direction of the actual support surface is precisely a radius-matrix eigenvector. -/
theorem surface_principal_direction_iff {ρ : ℝ × ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (p : ℝ × ℝ) (v : ℂ) (lam : ℝ) :
    fderiv ℝ (surface ρ) p (v.re, v.im) = lam • fderiv ℝ normal p (v.re, v.im) ↔
      symmetricAction (radiusXX ρ p) (radiusXY ρ p) (radiusYY ρ p) v = (lam : ℂ) * v := by
  rw [surface_fderiv_eq_frame hρ, normal_fderiv_eq_frame, ← tangentFrame_real_mul]
  exact (tangentFrame_injective p).eq_iff

/-- Squared phase identifies the larger-radius principal line of the actual surface. -/
theorem surface_principal_plus_iff_phase {ρ : ℝ × ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (p : ℝ × ℝ) (h : symbol (radiusXX ρ p) (radiusXY ρ p) (radiusYY ρ p) ≠ 0)
    {v : ℂ} (hv : ‖v‖ = 1) :
    fderiv ℝ (surface ρ) p (v.re, v.im) =
      eigenPlus (radiusXX ρ p) (radiusXY ρ p) (radiusYY ρ p) • fderiv ℝ normal p (v.re, v.im) ↔
      v ^ 2 = symbol (radiusXX ρ p) (radiusXY ρ p) (radiusYY ρ p) /
        (‖symbol (radiusXX ρ p) (radiusXY ρ p) (radiusYY ρ p)‖ : ℂ) := by
  rw [surface_principal_direction_iff hρ]
  exact eigenPlus_iff_phase _ _ _ h hv

#print axioms surface_principal_direction_iff
#print axioms surface_principal_plus_iff_phase
#print axioms symmetricAction_decomposition
#print axioms eigenvector_iff_squared_phase
#print axioms eigenPlus_iff_phase
#print axioms eigenMinus_iff_phase
end
end GaloisForLFunctions.HilbertMetric.Geometry.PrincipalLinePhase
