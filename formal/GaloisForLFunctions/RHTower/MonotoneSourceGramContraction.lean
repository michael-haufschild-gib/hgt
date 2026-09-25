import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# Decreasing source densities do not imply a Gram contraction

For even moments `m`, the raw odd-monomial Gram coefficients are
`Dᵢⱼ = m(i+j+1) / ((2i+1)! (2j+1)!)`. The sign-adjusted coefficients
of the denominator-cleared logarithmic moment kernel are the quadratic
expressions `cleared m i j`. Their difference is tested on indices `{1,2}`.

The equal mixture of uniform laws on `[-1,1]` and `[-4,4]` is an even,
nonnegative probability density decreasing on the positive half-line. Its
Gram difference is negative on the vector `(-13,17)`. Hence monotonicity of
a source density does not justify a positive-contraction representation of
its cleared logarithmic moment kernel.

For every nontrivial mixture of two distinct positive radii, the same
compression is nonnegative exactly when the explicit homogeneous radius
inequality in `form_nonneg_iff_radius_boundary` holds. This classifies the
compression, not the full infinite matrix. No sign conclusion about the
actual theta density or the Riemann hypothesis is asserted.
-/

namespace RHTower.MonotoneSourceGram
noncomputable section
open MeasureTheory Set

/-- Even moments of the symmetric uniform probability law of radius `r > 0`. -/
def uniformMoment (r : ℝ) (k : ℕ) : ℝ := r ^ (2 * k) / (2 * k + 1 : ℕ)
/-- Moment sequence of a mixture of two symmetric uniform laws. -/
def mixMoment (t a b : ℝ) (k : ℕ) : ℝ :=
  t * uniformMoment a k + (1 - t) * uniformMoment b k

/-- Coefficient of the raw odd-monomial Gram form. -/
def raw (m : ℕ → ℝ) (i j : ℕ) : ℝ :=
  m (i+j+1) / ((Nat.factorial (2*i+1) : ℝ) * Nat.factorial (2*j+1))

/-- Sign-adjusted coefficient after clearing the two source generating functions. -/
def cleared (m : ℕ → ℝ) (i j : ℕ) : ℝ :=
  2 * ∑ k ∈ Finset.range (min i j + 1),
    (i+j+1-2*k : ℕ) * m (i+j+1-k) * m k /
      ((Nat.factorial (2*(i+j+1-k)) : ℝ) * Nat.factorial (2*k))

/-- Raw Gram coefficient minus the cleared coefficient. -/
def gap (m : ℕ → ℝ) (i j : ℕ) : ℝ := raw m i j - cleared m i j

/-- The Gram difference restricted to coefficient indices one and two. -/
def form (m : ℕ → ℝ) (x y : ℝ) : ℝ :=
  gap m 1 1 * x^2 + 2 * gap m 1 2 * x*y + gap m 2 2 * y^2

/-- Determinant of the two-dimensional Gram difference. -/
def determinant (m : ℕ → ℝ) : ℝ := gap m 1 1 * gap m 2 2 - gap m 1 2 ^ 2

/-- Homogeneous polynomial determining the sign of the two-scale compression. -/
def radiusBoundary (A B : ℝ) : ℝ :=
  -3*A^4+36*A^3*B-2*A^2*B^2+36*A*B^3-3*B^4

/-- Direct integral evaluation identifies the moments with an actual uniform law. -/
theorem uniformMoment_integral (r : ℝ) (hr : r ≠ 0) (k : ℕ) :
    (∫ x in -r..r, x ^ (2*k)) / (2*r) = uniformMoment r k := by
  rw [integral_pow]
  simp only [uniformMoment, pow_succ, pow_mul]
  push_cast
  field_simp
  ring

/-- Every affine mixture has total mass one. -/
theorem mix_zero (t a b : ℝ) : mixMoment t a b 0 = 1 := by
  simp [mixMoment, uniformMoment]

/-- First diagonal coefficient of the two-scale Gram difference. -/
theorem gap11 (t a b : ℝ) :
    gap (mixMoment t a b) 1 1 =
      t*(1-t)*(a^2-b^2)^2*(a^2+b^2)/360 := by
  norm_num [gap, raw, cleared, mixMoment, uniformMoment, Finset.sum_range_succ,
    Nat.factorial]
  ring

/-- Mixed coefficient of the two-scale Gram difference. -/
theorem gap12 (t a b : ℝ) :
    gap (mixMoment t a b) 1 2 =
      t*(1-t)*(a^2-b^2)^2*(a^4+a^2*b^2+b^4)/7560 := by
  norm_num [gap, raw, cleared, mixMoment, uniformMoment, Finset.sum_range_succ,
    Nat.factorial]
  ring

/-- Second diagonal coefficient of the two-scale Gram difference. -/
theorem gap22 (t a b : ℝ) :
    gap (mixMoment t a b) 2 2 =
      t*(1-t)*(a^2-b^2)^2*(a^2+b^2)*(11*a^4+6*a^2*b^2+11*b^4)/1814400 := by
  norm_num [gap, raw, cleared, mixMoment, uniformMoment, Finset.sum_range_succ,
    Nat.factorial]
  ring

/-- Exact factorization of the two-scale compression determinant. -/
theorem determinant_eq (t a b : ℝ) :
    determinant (mixMoment t a b) =
      (t*(1-t))^2*(a^2-b^2)^4*radiusBoundary (a^2) (b^2)/4572288000 := by
  rw [determinant, gap11, gap12, gap22]
  unfold radiusBoundary
  ring

/-- Symmetric form of the radius boundary polynomial. -/
theorem radiusBoundary_eq (A B : ℝ) :
    radiusBoundary A B = 36*A*B*(A^2+B^2)+4*A^2*B^2-3*(A^2+B^2)^2 := by
  unfold radiusBoundary
  ring

/-- Exact negative witness for the equal mixture of radii one and four. -/
theorem counterexample : form (mixMoment (1/2) 1 4) (-13) 17 = -119221/32256 := by
  rw [form, gap11, gap12, gap22]
  norm_num

/-- The explicit Gram difference has a strictly negative direction. -/
theorem counterexample_neg : form (mixMoment (1/2) 1 4) (-13) 17 < 0 := by
  rw [counterexample]
  norm_num

/-- Density of the symmetric uniform law when the radius is positive. -/
def uniformDensity (r x : ℝ) : ℝ := if |x| ≤ r then (2*r)⁻¹ else 0

/-- Equal mixture of symmetric uniform densities of radii one and four. -/
def counterexampleDensity (x : ℝ) : ℝ :=
  (uniformDensity 1 x + uniformDensity 4 x)/2

/-- The counterexample density is even. -/
theorem density_even (x : ℝ) : counterexampleDensity (-x) = counterexampleDensity x := by
  simp [counterexampleDensity, uniformDensity]

/-- The counterexample density is nonnegative everywhere. -/
theorem density_nonneg (x : ℝ) : 0 ≤ counterexampleDensity x := by
  unfold counterexampleDensity uniformDensity
  split_ifs <;> norm_num

/-- The counterexample density decreases on the positive half-line. -/
theorem density_antitone : AntitoneOn counterexampleDensity (Ici 0) := by
  intro x hx y hy hxy
  simp only [mem_Ici] at hx hy
  simp only [counterexampleDensity, uniformDensity, abs_of_nonneg hx, abs_of_nonneg hy]
  split_ifs <;> norm_num at * <;> linarith


/-- The density has exactly the stated uniform moments. -/
theorem uniformDensity_moment (r : ℝ) (hr : 0 < r) (k : ℕ) :
    (∫ x : ℝ, x^(2*k)*uniformDensity r x) = uniformMoment r k := by
  have heq : (fun x : ℝ => x^(2*k)*uniformDensity r x) =
      (Icc (-r) r).indicator (fun x : ℝ => x^(2*k)/(2*r)) := by
    funext x
    by_cases hx : |x| ≤ r
    · have hm : x ∈ Icc (-r) r := abs_le.mp hx
      simp [uniformDensity, hx, hm, div_eq_mul_inv]
    · have hm : x ∉ Icc (-r) r := fun h => hx (abs_le.mpr h)
      simp [uniformDensity, hx, hm]
  rw [heq, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -r ≤ r),
    intervalIntegral.integral_div, uniformMoment_integral r hr.ne']


/-- All polynomial moments of the uniform density are integrable. -/
theorem integrable_uniformDensity_moment (r : ℝ) (hr : 0 < r) (k : ℕ) :
    Integrable (fun x : ℝ => x^(2*k)*uniformDensity r x) := by
  have heq : (fun x : ℝ => x^(2*k)*uniformDensity r x) =
      (Icc (-r) r).indicator (fun x : ℝ => x^(2*k)/(2*r)) := by
    funext x
    by_cases hx : |x| ≤ r
    · have hm : x ∈ Icc (-r) r := abs_le.mp hx
      simp [uniformDensity, hx, hm, div_eq_mul_inv]
    · have hm : x ∉ Icc (-r) r := fun h => hx (abs_le.mpr h)
      simp [uniformDensity, hx, hm]
  rw [heq, integrable_indicator_iff measurableSet_Icc]
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : -r ≤ r)).mp
    (((continuous_pow (2*k)).div_const (2*r)).intervalIntegrable _ _)

/-- The counterexample moments are exactly the two-scale mixture moments. -/
theorem density_moment (k : ℕ) :
    (∫ x : ℝ, x^(2*k)*counterexampleDensity x) = mixMoment (1/2) 1 4 k := by
  have heq : (fun x : ℝ => x^(2*k)*counterexampleDensity x) =
      (fun x : ℝ => (x^(2*k)*uniformDensity 1 x+x^(2*k)*uniformDensity 4 x)/2) := by
    funext x
    unfold counterexampleDensity
    ring
  rw [heq, MeasureTheory.integral_div, MeasureTheory.integral_add
      (integrable_uniformDensity_moment 1 (by norm_num) k)
      (integrable_uniformDensity_moment 4 (by norm_num) k),
    uniformDensity_moment 1 (by norm_num), uniformDensity_moment 4 (by norm_num)]
  unfold mixMoment
  ring

/-- The explicit density is normalized. -/
theorem density_mass : (∫ x : ℝ, counterexampleDensity x) = 1 := by
  have h := density_moment 0
  simpa [mixMoment, uniformMoment] using h

/-- Unconditional counterexample to raw Gram domination for even decreasing densities. -/
theorem exists_monotone_density_gap_negative :
    ∃ f : ℝ → ℝ, (∀ x, 0 ≤ f x) ∧ (∀ x, f (-x) = f x) ∧
      AntitoneOn f (Ici 0) ∧ (∫ x : ℝ, f x) = 1 ∧
        form (fun k => ∫ x : ℝ, x^(2*k)*f x) (-13) 17 < 0 := by
  refine ⟨counterexampleDensity, density_nonneg, density_even, density_antitone,
    density_mass, ?_⟩
  have hm : (fun k => ∫ x : ℝ, x^(2*k)*counterexampleDensity x) =
      mixMoment (1/2) 1 4 := by
    funext k
    exact density_moment k
  rw [hm]
  exact counterexample_neg


/-- Sharp determinant sign criterion, independent of the nontrivial mixing proportion. -/
theorem determinant_nonneg_iff_boundary {t a b : ℝ}
    (ht : 0 < t) (ht1 : t < 1) (hab : a^2 ≠ b^2) :
    0 ≤ determinant (mixMoment t a b) ↔
      3*(a^4+b^4)^2 ≤ 36*a^2*b^2*(a^4+b^4)+4*a^4*b^4 := by
  have hf : 0 < (t*(1-t))^2*(a^2-b^2)^4 := by
    have hn : a^2-b^2 ≠ 0 := sub_ne_zero.mpr hab
    have hp : 0 < (a^2-b^2)^2 := pow_two_pos_of_ne_zero hn
    have hp4 : 0 < (a^2-b^2)^4 := by nlinarith [sq_nonneg ((a^2-b^2)^2)]
    positivity
  rw [determinant_eq, le_div_iff₀ (by norm_num), zero_mul,
    mul_nonneg_iff_of_pos_left hf, radiusBoundary_eq]
  constructor <;> intro h <;> nlinarith [h]

/-- Completion of the square for the compressed Gram difference. -/
theorem form_completion (m : ℕ → ℝ) (x y : ℝ) :
    gap m 1 1 * form m x y =
      (gap m 1 1*x+gap m 1 2*y)^2 + determinant m*y^2 := by
  unfold form determinant
  ring

/-- A positive first pivot reduces the compressed sign to its determinant. -/
theorem form_nonneg_iff_determinant {m : ℕ → ℝ} (h : 0 < gap m 1 1) :
    (∀ x y : ℝ, 0 ≤ form m x y) ↔ 0 ≤ determinant m := by
  constructor
  · intro hpos
    have hv := hpos (-gap m 1 2) (gap m 1 1)
    have he : form m (-gap m 1 2) (gap m 1 1) =
        gap m 1 1 * determinant m := by
      unfold form determinant
      ring
    rw [he] at hv
    exact (mul_nonneg_iff_of_pos_left h).mp hv
  · intro hd x y
    have he := form_completion m x y
    have hs := sq_nonneg (gap m 1 1*x+gap m 1 2*y)
    have hp := mul_nonneg hd (sq_nonneg y)
    nlinarith

/-- Exact positivity classification of the two-scale compression. -/
theorem form_nonneg_iff_radius_boundary {t a b : ℝ}
    (ht : 0 < t) (ht1 : t < 1) (hab : a^2 ≠ b^2) :
    (∀ x y : ℝ, 0 ≤ form (mixMoment t a b) x y) ↔
      3*(a^4+b^4)^2 ≤ 36*a^2*b^2*(a^4+b^4)+4*a^4*b^4 := by
  have hn : a^2-b^2 ≠ 0 := sub_ne_zero.mpr hab
  have hp : 0 < (a^2-b^2)^2 := pow_two_pos_of_ne_zero hn
  have hs : 0 < a^2+b^2 := by nlinarith [sq_nonneg a, sq_nonneg b]
  have h : 0 < gap (mixMoment t a b) 1 1 := by
    rw [gap11]
    positivity
  exact (form_nonneg_iff_determinant h).trans (determinant_nonneg_iff_boundary ht ht1 hab)

end
end RHTower.MonotoneSourceGram
