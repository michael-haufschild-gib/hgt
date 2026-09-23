import GaloisForLFunctions.RHTower.PolynomialMomentFockWeightedInner

open MeasureTheory Set

namespace RHTower

noncomputable section

/-- Exact overlap integral of two complex-plane Gaussians with real centers. -/
theorem integral_complex_two_center_gaussian
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x y : ℝ) :
    (∫ z : ℂ, Real.exp (-(a * ‖z - (x : ℂ)‖ ^ (2 : ℕ) +
        b * ‖z - (y : ℂ)‖ ^ (2 : ℕ)))) =
      Real.pi / (a + b) *
        Real.exp (-(a * b / (a + b) * (x - y) ^ (2 : ℕ))) := by
  let c : ℝ := (a * x + b * y) / (a + b)
  have hab : 0 < a + b := add_pos ha hb
  have hcomplete (z : ℂ) :
      a * ‖z - (x : ℂ)‖ ^ (2 : ℕ) + b * ‖z - (y : ℂ)‖ ^ (2 : ℕ) =
        (a + b) * ‖z - (c : ℂ)‖ ^ (2 : ℕ) +
          a * b / (a + b) * (x - y) ^ (2 : ℕ) := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
      Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero]
    dsimp [c]
    field_simp [hab.ne']
    ring
  have hpoint (z : ℂ) :
      Real.exp (-(a * ‖z - (x : ℂ)‖ ^ (2 : ℕ) +
          b * ‖z - (y : ℂ)‖ ^ (2 : ℕ))) =
        Real.exp (-(a * b / (a + b) * (x - y) ^ (2 : ℕ))) *
          Real.exp (-(a + b) * ‖z - (c : ℂ)‖ ^ (2 : ℕ)) := by
    rw [hcomplete]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [funext hpoint, MeasureTheory.integral_const_mul]
  rw [integral_complex_gaussian_sub_real (a + b) c hab]
  ring

theorem integrable_complex_two_center_gaussian
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x y : ℝ) :
    Integrable (fun z : ℂ => Real.exp (-(a * ‖z - (x : ℂ)‖ ^ (2 : ℕ) +
      b * ‖z - (y : ℂ)‖ ^ (2 : ℕ)))) := by
  apply (integrable_complex_gaussian_sub_real a x ha).mono
  · have hcont : Continuous (fun z : ℂ =>
        Real.exp (-(a * ‖z - (x : ℂ)‖ ^ (2 : ℕ) +
          b * ‖z - (y : ℂ)‖ ^ (2 : ℕ)))) := by fun_prop
    exact hcont.aestronglyMeasurable
  · filter_upwards [] with z
    simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (by
      have hby : 0 ≤ b * ‖z - (y : ℂ)‖ ^ (2 : ℕ) :=
        mul_nonneg hb.le (sq_nonneg _)
      linarith)

/-- Squared modulus of weighted polarization is product of its two weighted square densities. -/
theorem normSq_polynomialMomentFockWeightedInner
    (m : ℝ) (hm : 2 ≤ m) (f g : MomentFock) (z : ℂ) :
    ‖polynomialMomentFockWeightedInner m hm f g z‖ ^ (2 : ℕ) =
      polynomialMomentFockWeightedNormSq m hm f z *
        polynomialMomentFockWeightedNormSq m hm g z := by
  unfold polynomialMomentFockWeightedInner polynomialMomentFockWeightedNormSq
  rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  ring

/-- Pointwise geometric-mean Gaussian bound for weighted normalized tangent polarization. -/
theorem norm_polynomialMomentFockWeightedInner_normalizedTangentVector_le_gaussian
    {m x y : ℝ} (hm : 4 ≤ m) (hx : 0 ≤ x) (hy : 0 ≤ y) (z : ℂ) :
    ‖polynomialMomentFockWeightedInner m (by linarith)
        (polynomialMomentFockNormalizedTangentVector m (by linarith) x)
        (polynomialMomentFockNormalizedTangentVector m (by linarith) y) z‖ ≤
      (Real.sqrt
          ((m * (1 + x ^ (2 : ℕ)) ^ (m / 2 - 1)) *
            (m * (1 + y ^ (2 : ℕ)) ^ (m / 2 - 1))) / Real.pi) *
        Real.exp (2 * (polynomialFockLocalBregmanConstant m / m)) *
        Real.exp (-(((m * (1 + x ^ (2 : ℕ)) ^ (m / 2 - 1)) *
              ‖z - (x : ℂ)‖ ^ (2 : ℕ) +
            (m * (1 + y ^ (2 : ℕ)) ^ (m / 2 - 1)) *
              ‖z - (y : ℂ)‖ ^ (2 : ℕ)) / 2)) := by
  let hm2 : 2 ≤ m := by linarith
  let uX : MomentFock := polynomialMomentFockNormalizedTangentVector m hm2 x
  let uY : MomentFock := polynomialMomentFockNormalizedTangentVector m hm2 y
  let cx : ℝ := m * (1 + x ^ (2 : ℕ)) ^ (m / 2 - 1)
  let cy : ℝ := m * (1 + y ^ (2 : ℕ)) ^ (m / 2 - 1)
  let C : ℝ := polynomialFockLocalBregmanConstant m / m
  let dx : ℝ := ‖z - (x : ℂ)‖ ^ (2 : ℕ)
  let dy : ℝ := ‖z - (y : ℂ)‖ ^ (2 : ℕ)
  let H : ℝ := (Real.sqrt (cx * cy) / Real.pi) * Real.exp (2 * C) *
    Real.exp (-((cx * dx + cy * dy) / 2))
  have hcx : 0 < cx := by dsimp [cx]; positivity
  have hcy : 0 < cy := by dsimp [cy]; positivity
  have hdx :=
    polynomialMomentFockWeightedNormSq_normalizedTangentVector_le_gaussian hm hx z
  have hdy :=
    polynomialMomentFockWeightedNormSq_normalizedTangentVector_le_gaussian hm hy z
  have hprod :
      polynomialMomentFockWeightedNormSq m hm2 uX z *
          polynomialMomentFockWeightedNormSq m hm2 uY z ≤
        ((cx / Real.pi) * Real.exp (2 * C) * Real.exp (-(cx * dx))) *
          ((cy / Real.pi) * Real.exp (2 * C) * Real.exp (-(cy * dy))) := by
    exact mul_le_mul
      (by simpa [uX, hm2, cx, C, dx] using hdx)
      (by simpa [uY, hm2, cy, C, dy] using hdy)
      (polynomialMomentFockWeightedNormSq_nonneg m hm2 uY z)
      (by positivity)
  have hsquare :
      ‖polynomialMomentFockWeightedInner m hm2 uX uY z‖ ^ (2 : ℕ) ≤ H ^ (2 : ℕ) := by
    rw [normSq_polynomialMomentFockWeightedInner]
    calc
      polynomialMomentFockWeightedNormSq m hm2 uX z *
          polynomialMomentFockWeightedNormSq m hm2 uY z
          ≤ ((cx / Real.pi) * Real.exp (2 * C) * Real.exp (-(cx * dx))) *
            ((cy / Real.pi) * Real.exp (2 * C) * Real.exp (-(cy * dy))) := hprod
      _ = H ^ (2 : ℕ) := by
        dsimp [H]
        simp only [mul_pow]
        rw [div_pow, Real.sq_sqrt (mul_nonneg hcx.le hcy.le)]
        field_simp [Real.pi_ne_zero]
        simp only [← Real.exp_nat_mul]
        rw [← Real.exp_add]
        congr 1
        ring
  have hH : 0 ≤ H := by dsimp [H]; positivity
  change ‖polynomialMomentFockWeightedInner m hm2 uX uY z‖ ≤ H
  nlinarith [norm_nonneg
    (polynomialMomentFockWeightedInner m hm2 uX uY z)]

/-- Explicit harmonic-curvature Gaussian decay of two normalized tangent-vector inner products. -/
theorem norm_inner_polynomialMomentFockNormalizedTangentVector_le_gaussianOverlap
    {m x y : ℝ} (hm : 4 ≤ m) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ‖inner ℂ
        (polynomialMomentFockNormalizedTangentVector m (by linarith) x)
        (polynomialMomentFockNormalizedTangentVector m (by linarith) y)‖ ≤
      (2 * Real.sqrt
          ((m * (1 + x ^ (2 : ℕ)) ^ (m / 2 - 1)) *
            (m * (1 + y ^ (2 : ℕ)) ^ (m / 2 - 1))) /
          ((m * (1 + x ^ (2 : ℕ)) ^ (m / 2 - 1)) +
            (m * (1 + y ^ (2 : ℕ)) ^ (m / 2 - 1)))) *
        Real.exp (2 * (polynomialFockLocalBregmanConstant m / m)) *
        Real.exp (-(((m * (1 + x ^ (2 : ℕ)) ^ (m / 2 - 1)) *
            (m * (1 + y ^ (2 : ℕ)) ^ (m / 2 - 1)) /
              (2 * ((m * (1 + x ^ (2 : ℕ)) ^ (m / 2 - 1)) +
                (m * (1 + y ^ (2 : ℕ)) ^ (m / 2 - 1))))) * (x - y) ^ (2 : ℕ))) := by
  let hm2 : 2 ≤ m := by linarith
  let uX : MomentFock := polynomialMomentFockNormalizedTangentVector m hm2 x
  let uY : MomentFock := polynomialMomentFockNormalizedTangentVector m hm2 y
  let cx : ℝ := m * (1 + x ^ (2 : ℕ)) ^ (m / 2 - 1)
  let cy : ℝ := m * (1 + y ^ (2 : ℕ)) ^ (m / 2 - 1)
  let C : ℝ := polynomialFockLocalBregmanConstant m / m
  let a : ℝ := cx / 2
  let b : ℝ := cy / 2
  let K : ℝ := Real.sqrt (cx * cy) / Real.pi * Real.exp (2 * C)
  let G : ℂ → ℝ := fun z => K *
    Real.exp (-((cx * ‖z - (x : ℂ)‖ ^ (2 : ℕ) +
      cy * ‖z - (y : ℂ)‖ ^ (2 : ℕ)) / 2))
  have hcx : 0 < cx := by dsimp [cx]; positivity
  have hcy : 0 < cy := by dsimp [cy]; positivity
  have ha : 0 < a := by dsimp [a]; linarith
  have hb : 0 < b := by dsimp [b]; linarith
  have hsum : 0 < cx + cy := add_pos hcx hcy
  have hGeq : G = fun z : ℂ => K *
      Real.exp (-(a * ‖z - (x : ℂ)‖ ^ (2 : ℕ) +
        b * ‖z - (y : ℂ)‖ ^ (2 : ℕ))) := by
    funext z
    dsimp [G, a, b]
    congr 2
    ring
  have hG : Integrable G := by
    rw [hGeq]
    exact (integrable_complex_two_center_gaussian ha hb x y).const_mul K
  have hpoint : ∀ z : ℂ,
      ‖polynomialMomentFockWeightedInner m hm2 uX uY z‖ ≤ G z := by
    intro z
    simpa [G, K, cx, cy, C, uX, uY, hm2] using
      norm_polynomialMomentFockWeightedInner_normalizedTangentVector_le_gaussian
        hm hx hy z
  have hexp :
      Real.exp (-(a * b / (a + b) * (x - y) ^ (2 : ℕ))) =
        Real.exp (-(cx * cy / (2 * (cx + cy)) * (x - y) ^ (2 : ℕ))) := by
    congr 1
    dsimp [a, b]
    field_simp [hsum.ne']
  have hGint :
      (∫ z : ℂ, G z) =
        (2 * Real.sqrt (cx * cy) / (cx + cy)) * Real.exp (2 * C) *
          Real.exp (-(cx * cy / (2 * (cx + cy)) * (x - y) ^ (2 : ℕ))) := by
    rw [hGeq, MeasureTheory.integral_const_mul,
      integral_complex_two_center_gaussian ha hb x y, hexp]
    dsimp [K, a, b]
    field_simp [Real.pi_ne_zero, hsum.ne']
  change ‖inner ℂ uX uY‖ ≤ _
  calc
    ‖inner ℂ uX uY‖ =
        ‖∫ z : ℂ, polynomialMomentFockWeightedInner m hm2 uX uY z‖ := by
      rw [integral_polynomialMomentFockWeightedInner]
    _ ≤ ∫ z : ℂ, G z :=
      MeasureTheory.norm_integral_le_of_norm_le hG (Filter.Eventually.of_forall hpoint)
    _ = (2 * Real.sqrt (cx * cy) / (cx + cy)) * Real.exp (2 * C) *
        Real.exp (-(cx * cy / (2 * (cx + cy)) * (x - y) ^ (2 : ℕ))) := hGint
    _ = _ := by rfl

end

end RHTower
