import GaloisForLFunctions.HTGeometry.GammaSymmetricSplitDecay
import GaloisForLFunctions.HTGeometry.ZetaTailBound
import GaloisForLFunctions.RHTower.XiRealAxisGrowth
import GaloisForLFunctions.RHTower.ZetaStripPolynomialBound
import GaloisForLFunctions.RHTower.Reflection
import GaloisForLFunctions.RHTower.XiHorizontalSliceTaylorPositivity


/-!
# Decay of the slice product along circles

For the slice product `g_t(x) = ξ(½+x+it) ξ(½−x+it)` at height `t` and a circle `|x| = R` with
`R ≤ t/2`, the point `x = a + ic` in the right half-plane has
`|g_t(x)| = |ξ(½+a+i(t+c))| |ξ(½+a+i(t−c))|` (functional equation and conjugation), while
`g_t(R) = |ξ(½+R+it)|²`.  Factorising `ξ = ½ s(s−1) π^{−s/2} Γ(s/2) ζ(s)`:

* the two `Γ` factors lose `(t/2)^{−(R−a)}` against the real point, by the symmetric-split law for
  the Stirling main term plus the complex Stirling difference;
* the `π` factors gain back `π^{R−a}`;
* the quadratic factors cost at most `exp(4(½+a)/t)`;
* the `ζ` factors cost the square of the ratio of an upper bound on the circle to a lower bound at
  `½+R+it`.

The result is `|g_t(Re^{iθ})| ≤ g_t(R) (B/m₀)² exp(−R(1−cos θ) log(t/2π) + E)` with an explicit
`E = 12R(1−cos θ+|sin θ|)/t + 4(½+R cos θ)/t`, and an instantiation with `ζ` bounds supplied:
factor `16` where `R cos θ ≥ 3/2`, `(4+12t)²` in general.  This is the tail estimate of the
saddle-point evaluation of the Taylor coefficients of `g_t`.
-/

open Complex Real

namespace RHTower

noncomputable section

/-- In the right half-plane `|ξ(s)| = |s(s−1)/2| · π^{−σ/2} |Γ(s/2)| · |ζ(s)|`. -/
theorem norm_xi_eq_factors {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ‖xi s‖ = ‖s * (s - 1) / 2‖ * (Real.pi ^ (-(s.re / 2)) * ‖Complex.Gamma (s / 2)‖)
      * ‖riemannZeta s‖ := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  rw [xi_eq_mul_completedRiemannZeta hs0 hs1, completedRiemannZeta_eq_Gammaℝ_mul hs,
    Complex.Gammaℝ, norm_mul, norm_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  have : (-s / 2).re = -(s.re / 2) := by simp [neg_div]
  rw [this]
  ring

/-- `ζ` is at least `1/2` in modulus on `Re s ≥ 3`. -/
theorem one_half_le_norm_riemannZeta_of_three_le_re {s : ℂ} (hs : 3 ≤ s.re) :
    1 / 2 ≤ ‖riemannZeta s‖ := by
  have h := GaloisForLFunctions.HTGeometry.norm_riemannZeta_sub_one_le_rpow (s := s) (by linarith)
  have h2 : (2 : ℝ) ^ (-s.re) ≤ 2 ^ (-(3 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h3 : (2 : ℝ) ^ (-(3 : ℝ)) = 1 / 8 := by
    rw [Real.rpow_neg (by norm_num)]; norm_num
  rw [h3] at h2
  have h4 := norm_sub_norm_le (1 : ℂ) (1 - riemannZeta s)
  simp only [norm_one, sub_sub_cancel] at h4
  rw [norm_sub_rev] at h
  have h5 : 4 * (2 : ℝ) ^ (-s.re) ≤ 1 / 2 := by linarith
  linarith

/-- On `Re s ≥ 1/2`, `|Im s| ≥ 2`, the crude bound `|ζ(s)| ≤ 2 + 4|Im s|`. -/
theorem norm_riemannZeta_le_of_half_le_re {σ y : ℝ} (hσ : 1 / 2 ≤ σ) (hy : 2 ≤ |y|) :
    ‖riemannZeta ((σ : ℂ) + (y : ℂ) * I)‖ ≤ 2 + 4 * |y| := by
  rcases le_or_gt σ 2 with h2 | h2
  · have := norm_riemannZeta_le_of_re_pos (by linarith) h2 hy
    have hdiv : 2 * |y| / σ ≤ 4 * |y| := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [abs_nonneg y]
    linarith
  · have := norm_riemannZeta_le_of_two_le_re (s := (σ : ℂ) + (y : ℂ) * I) (by simp; linarith)
    have hpi : Real.pi ^ 2 / 6 ≤ 2 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
    nlinarith [abs_nonneg y]

/-- `|s(s−1)/2|` in terms of `|s|` and `|s − 1|`. -/
theorem norm_mul_sub_one_div_two (s : ℂ) : ‖s * (s - 1) / 2‖ = ‖s‖ * ‖s - 1‖ / 2 := by
  rw [norm_div, norm_mul]; simp

/-- **Polynomial factor on a split.**  With abscissa `½ + a` (`a ≥ 0`) and ordinates `t ± c`,
`|c| ≤ t`, the two quadratic factors `|s(s−1)/2|` are at most the square of the factor at any point
of ordinate `t`, times `exp(4(½+a)/t)`. -/
theorem norm_quadratic_split_le {t a c σ₀ : ℝ} (ht : 0 < t) (ha : 0 ≤ a) (hc : |c| ≤ t) :
    ‖(((1 / 2 + a : ℝ) : ℂ) + ((t + c : ℝ) : ℂ) * I) * ((((1 / 2 + a : ℝ) : ℂ)
        + ((t + c : ℝ) : ℂ) * I) - 1) / 2‖
      * ‖(((1 / 2 + a : ℝ) : ℂ) + ((t - c : ℝ) : ℂ) * I) * ((((1 / 2 + a : ℝ) : ℂ)
        + ((t - c : ℝ) : ℂ) * I) - 1) / 2‖
      ≤ ‖((σ₀ : ℂ) + (t : ℂ) * I) * (((σ₀ : ℂ) + (t : ℂ) * I) - 1) / 2‖ ^ 2
        * Real.exp (4 * (1 / 2 + a) / t) := by
  have hcabs := abs_le.mp hc
  simp only [norm_mul_sub_one_div_two]
  have hle : ∀ x y : ℝ, ‖(x : ℂ) + (y : ℂ) * I‖ ≤ |x| + |y| := fun x y => by
    have := Complex.norm_le_abs_re_add_abs_im ((x : ℂ) + (y : ℂ) * I); simpa using this
  have hsub : ∀ x y : ℝ, ((x : ℂ) + (y : ℂ) * I) - 1 = ((x - 1 : ℝ) : ℂ) + (y : ℂ) * I := by
    intro x y; push_cast; ring
  have hge : ∀ x y : ℝ, |y| ≤ ‖(x : ℂ) + (y : ℂ) * I‖ := fun x y => by
    have := Complex.abs_im_le_norm ((x : ℂ) + (y : ℂ) * I); simpa using this
  have hA : |1 / 2 + a - 1| ≤ 1 / 2 + a := by rw [abs_le]; constructor <;> linarith
  have hB : |1 / 2 + a| = 1 / 2 + a := abs_of_nonneg (by linarith)
  rw [hsub, hsub, hsub]
  have n1 := hle (1 / 2 + a) (t + c)
  have n1' := hle (1 / 2 + a - 1) (t + c)
  have n2 := hle (1 / 2 + a) (t - c)
  have n2' := hle (1 / 2 + a - 1) (t - c)
  rw [abs_of_nonneg (show 0 ≤ t + c by linarith)] at n1 n1'
  rw [abs_of_nonneg (show 0 ≤ t - c by linarith)] at n2 n2'
  have m0 := hge σ₀ t
  have m0' := hge (σ₀ - 1) t
  rw [abs_of_pos ht] at m0 m0'
  set T := t + (1 / 2 + a) with hT
  have e1 : ‖((1 / 2 + a : ℝ) : ℂ) + ((t + c : ℝ) : ℂ) * I‖ * ‖((1 / 2 + a - 1 : ℝ) : ℂ)
      + ((t + c : ℝ) : ℂ) * I‖ ≤ (T + c) * (T + c) := by
    apply mul_le_mul (by linarith) (by linarith) (norm_nonneg _) (by linarith)
  have e2 : ‖((1 / 2 + a : ℝ) : ℂ) + ((t - c : ℝ) : ℂ) * I‖ * ‖((1 / 2 + a - 1 : ℝ) : ℂ)
      + ((t - c : ℝ) : ℂ) * I‖ ≤ (T - c) * (T - c) := by
    apply mul_le_mul (by linarith) (by linarith) (norm_nonneg _) (by linarith)
  have e0 : t * t ≤ ‖(σ₀ : ℂ) + (t : ℂ) * I‖ * ‖((σ₀ - 1 : ℝ) : ℂ) + (t : ℂ) * I‖ :=
    mul_le_mul m0 m0' ht.le (norm_nonneg _)
  have hprod : (T + c) * (T + c) * ((T - c) * (T - c)) ≤ T ^ 4 := by
    have h0 : 0 ≤ (T + c) * (T - c) := mul_nonneg (by linarith) (by linarith)
    have h1 : (T + c) * (T - c) ≤ T ^ 2 := by nlinarith [sq_nonneg c]
    nlinarith
  have hT4 : T ^ 4 ≤ t ^ 4 * Real.exp (4 * (1 / 2 + a) / t) := by
    have hT' : T ≤ t * Real.exp ((1 / 2 + a) / t) := by
      have h := Real.add_one_le_exp ((1 / 2 + a) / t)
      have e : t * ((1 / 2 + a) / t + 1) = T := by rw [hT]; field_simp; ring
      rw [← e]
      exact mul_le_mul_of_nonneg_left h ht.le
    calc T ^ 4 ≤ (t * Real.exp ((1 / 2 + a) / t)) ^ 4 := by gcongr
      _ = t ^ 4 * Real.exp (4 * (1 / 2 + a) / t) := by
        rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
  set X := ‖((1 / 2 + a : ℝ) : ℂ) + ((t + c : ℝ) : ℂ) * I‖ * ‖((1 / 2 + a - 1 : ℝ) : ℂ)
      + ((t + c : ℝ) : ℂ) * I‖
  set Y := ‖((1 / 2 + a : ℝ) : ℂ) + ((t - c : ℝ) : ℂ) * I‖ * ‖((1 / 2 + a - 1 : ℝ) : ℂ)
      + ((t - c : ℝ) : ℂ) * I‖
  set Z := ‖(σ₀ : ℂ) + (t : ℂ) * I‖ * ‖((σ₀ - 1 : ℝ) : ℂ) + (t : ℂ) * I‖
  have hX : 0 ≤ X := by positivity
  have hY : 0 ≤ Y := by positivity
  have hXY : X * Y ≤ T ^ 4 :=
    (mul_le_mul e1 e2 hY (by nlinarith)).trans hprod
  have hZ : t ^ 4 ≤ Z ^ 2 := by
    have := mul_le_mul e0 e0 (by positivity) (by positivity)
    nlinarith
  have hexp := Real.exp_pos (4 * (1 / 2 + a) / t)
  calc (‖((1 / 2 + a : ℝ) : ℂ) + ((t + c : ℝ) : ℂ) * I‖ * ‖((1 / 2 + a - 1 : ℝ) : ℂ)
      + ((t + c : ℝ) : ℂ) * I‖ / 2) * (‖((1 / 2 + a : ℝ) : ℂ) + ((t - c : ℝ) : ℂ) * I‖
        * ‖((1 / 2 + a - 1 : ℝ) : ℂ) + ((t - c : ℝ) : ℂ) * I‖ / 2) = X * Y / 4 := by ring
    _ ≤ t ^ 4 * Real.exp (4 * (1 / 2 + a) / t) / 4 := by
        have := hXY.trans hT4; linarith
    _ ≤ Z ^ 2 * Real.exp (4 * (1 / 2 + a) / t) / 4 := by gcongr
    _ = (‖(σ₀ : ℂ) + (t : ℂ) * I‖ * ‖((σ₀ - 1 : ℝ) : ℂ) + (t : ℂ) * I‖ / 2) ^ 2
        * Real.exp (4 * (1 / 2 + a) / t) := by ring

/-- **Gamma factor on a split**, multiplicative form.  For `t ≥ 8`, `0 ≤ a ≤ R`, `|c| ≤ t/2`:
`|Γ(s₁/2)| |Γ(s₂/2)| ≤ |Γ(s₀/2)|² exp(−(R−a) log(t/2) + 12(R−a+|c|)/t)` where
`s₀ = ½+R+it` and `s_{1,2} = ½+a+i(t±c)`. -/
theorem norm_Gamma_half_split_le {t R a c : ℝ} (ht : 8 ≤ t) (ha : 0 ≤ a) (haR : a ≤ R)
    (hc : |c| ≤ t / 2) :
    ‖Complex.Gamma ((((1 / 2 + a : ℝ) : ℂ) + ((t + c : ℝ) : ℂ) * I) / 2)‖
      * ‖Complex.Gamma ((((1 / 2 + a : ℝ) : ℂ) + ((t - c : ℝ) : ℂ) * I) / 2)‖
      ≤ ‖Complex.Gamma ((((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I) / 2)‖ ^ 2
        * Real.exp (-(R - a) * Real.log (t / 2) + 12 * (R - a + |c|) / t) := by
  have e₀ : (((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I) / 2
      = (((1 / 2 + R) / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I := by push_cast; ring
  have e₁ : (((1 / 2 + a : ℝ) : ℂ) + ((t + c : ℝ) : ℂ) * I) / 2
      = (((1 / 2 + a) / 2 : ℝ) : ℂ) + ((t / 2 + c / 2 : ℝ) : ℂ) * I := by push_cast; ring
  have e₂ : (((1 / 2 + a : ℝ) : ℂ) + ((t - c : ℝ) : ℂ) * I) / 2
      = (((1 / 2 + a) / 2 : ℝ) : ℂ) + ((t / 2 - c / 2 : ℝ) : ℂ) * I := by push_cast; ring
  rw [e₀, e₁, e₂]
  have hsplit := HTGeometry.log_norm_Gamma_split_le (X₀ := (1 / 2 + R) / 2)
    (X₁ := (1 / 2 + a) / 2) (Y := t / 2) (d := c / 2) (by linarith) (by linarith) (by linarith)
    (by rw [abs_div, abs_two]; linarith)
  set G₀ := ‖Complex.Gamma ((((1 / 2 + R) / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I)‖
  set G₁ := ‖Complex.Gamma ((((1 / 2 + a) / 2 : ℝ) : ℂ) + ((t / 2 + c / 2 : ℝ) : ℂ) * I)‖
  set G₂ := ‖Complex.Gamma ((((1 / 2 + a) / 2 : ℝ) : ℂ) + ((t / 2 - c / 2 : ℝ) : ℂ) * I)‖
  have hpos : ∀ x y : ℝ, 0 < x → 0 < ‖Complex.Gamma ((x : ℂ) + (y : ℂ) * I)‖ := fun x y hx =>
    norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by simpa using hx))
  have hG₀ : 0 < G₀ := hpos _ _ (by linarith)
  have hG₁ : 0 < G₁ := hpos _ _ (by linarith)
  have hG₂ : 0 < G₂ := hpos _ _ (by linarith)
  have eE : -2 * ((1 / 2 + R) / 2 - (1 / 2 + a) / 2) * Real.log (t / 2)
      + 12 * ((1 / 2 + R) / 2 - (1 / 2 + a) / 2 + |c / 2|) / (t / 2)
      = -(R - a) * Real.log (t / 2) + 12 * (R - a + |c|) / t := by
    rw [abs_div, abs_two]; field_simp; ring
  rw [eE] at hsplit
  set E := -(R - a) * Real.log (t / 2) + 12 * (R - a + |c|) / t
  calc G₁ * G₂ = Real.exp (Real.log G₁ + Real.log G₂) := by
        rw [Real.exp_add, Real.exp_log hG₁, Real.exp_log hG₂]
    _ ≤ Real.exp (2 * Real.log G₀ + E) := Real.exp_le_exp.mpr (by linarith)
    _ = G₀ ^ 2 * Real.exp E := by
        rw [Real.exp_add, show 2 * Real.log G₀ = Real.log (G₀ ^ 2) by
          rw [Real.log_pow]; push_cast; ring, Real.exp_log (by positivity)]

/-- The archimedean `π`-factor on a split: `π^{−σ₁/2} π^{−σ₁/2} = (π^{−σ₀/2})² π^{σ₀−σ₁}`. -/
theorem pi_rpow_split (R a : ℝ) :
    Real.pi ^ (-((1 / 2 + a) / 2)) * Real.pi ^ (-((1 / 2 + a) / 2))
      = (Real.pi ^ (-((1 / 2 + R) / 2))) ^ 2 * Real.exp ((R - a) * Real.log Real.pi) := by
  rw [Real.rpow_def_of_pos Real.pi_pos, Real.rpow_def_of_pos Real.pi_pos, ← Real.exp_add,
    ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1; push_cast; ring

/-- **Arc decay of `|ξ|` at height `t`.**  For `t ≥ 8`, `0 ≤ a ≤ R` and `|c| ≤ t/2`, the two
points `½ + a + i(t ± c)` carry at most the mass of the double point `½ + R + it`, times
`(t/2π)^{−(R−a)}`, the square of the ratio of the given `ζ` bounds, and
`exp(12(R−a+|c|)/t + 4(½+a)/t)` from the Stirling and polynomial corrections. -/
theorem norm_xi_split_le {t R a c B m₀ : ℝ} (ht : 8 ≤ t) (ha : 0 ≤ a) (haR : a ≤ R)
    (hc : |c| ≤ t / 2) (hm₀ : 0 < m₀)
    (hz₀ : m₀ ≤ ‖riemannZeta (((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I)‖)
    (hz₁ : ‖riemannZeta (((1 / 2 + a : ℝ) : ℂ) + ((t + c : ℝ) : ℂ) * I)‖ ≤ B)
    (hz₂ : ‖riemannZeta (((1 / 2 + a : ℝ) : ℂ) + ((t - c : ℝ) : ℂ) * I)‖ ≤ B) :
    ‖xi (((1 / 2 + a : ℝ) : ℂ) + ((t + c : ℝ) : ℂ) * I)‖
        * ‖xi (((1 / 2 + a : ℝ) : ℂ) + ((t - c : ℝ) : ℂ) * I)‖
      ≤ ‖xi (((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 * (B / m₀) ^ 2
        * Real.exp (-(R - a) * Real.log (t / (2 * Real.pi)) + 12 * (R - a + |c|) / t
          + 4 * (1 / 2 + a) / t) := by
  have ht0 : 0 < t := by linarith
  have hcabs := abs_le.mp hc
  have hfac : ∀ x y : ℝ, 0 < x → 0 < y →
      ‖xi ((x : ℂ) + (y : ℂ) * I)‖ = ‖((x : ℂ) + (y : ℂ) * I) * (((x : ℂ) + (y : ℂ) * I) - 1) / 2‖
        * (Real.pi ^ (-(x / 2)) * ‖Complex.Gamma (((x : ℂ) + (y : ℂ) * I) / 2)‖)
        * ‖riemannZeta ((x : ℂ) + (y : ℂ) * I)‖ := by
    intro x y hx hy
    have h1 : ((x : ℂ) + (y : ℂ) * I) ≠ 1 := by
      intro h; have := congrArg Complex.im h; simp at this; linarith
    rw [norm_xi_eq_factors (by simpa using hx) h1]
    simp
  rw [hfac _ _ (by linarith) ht0, hfac _ _ (by linarith) (by linarith),
    hfac _ _ (by linarith) (by linarith)]
  have hP := norm_quadratic_split_le (σ₀ := 1 / 2 + R) ht0 ha (c := c) (by linarith)
  have hG := norm_Gamma_half_split_le ht ha haR hc
  have hpi := pi_rpow_split R a
  set P₀ := ‖(((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I) * ((((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I) - 1) / 2‖
  set P₁ := ‖(((1 / 2 + a : ℝ) : ℂ) + ((t + c : ℝ) : ℂ) * I) * ((((1 / 2 + a : ℝ) : ℂ)
        + ((t + c : ℝ) : ℂ) * I) - 1) / 2‖
  set P₂ := ‖(((1 / 2 + a : ℝ) : ℂ) + ((t - c : ℝ) : ℂ) * I) * ((((1 / 2 + a : ℝ) : ℂ)
        + ((t - c : ℝ) : ℂ) * I) - 1) / 2‖
  set G₀ := ‖Complex.Gamma ((((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I) / 2)‖
  set G₁ := ‖Complex.Gamma ((((1 / 2 + a : ℝ) : ℂ) + ((t + c : ℝ) : ℂ) * I) / 2)‖
  set G₂ := ‖Complex.Gamma ((((1 / 2 + a : ℝ) : ℂ) + ((t - c : ℝ) : ℂ) * I) / 2)‖
  set Z₀ := ‖riemannZeta (((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I)‖
  set Z₁ := ‖riemannZeta (((1 / 2 + a : ℝ) : ℂ) + ((t + c : ℝ) : ℂ) * I)‖
  set Z₂ := ‖riemannZeta (((1 / 2 + a : ℝ) : ℂ) + ((t - c : ℝ) : ℂ) * I)‖
  set q₀ := Real.pi ^ (-((1 / 2 + R) / 2))
  set q₁ := Real.pi ^ (-((1 / 2 + a) / 2))
  have hB : 0 ≤ B := le_trans (norm_nonneg _) hz₁
  have hZ : Z₁ * Z₂ ≤ B ^ 2 := by rw [sq]; exact mul_le_mul hz₁ hz₂ (norm_nonneg _) hB
  have hq₀ : 0 < q₀ := Real.rpow_pos_of_pos Real.pi_pos _
  have hlogt : Real.log (t / (2 * Real.pi)) = Real.log (t / 2) - Real.log Real.pi := by
    rw [← Real.log_div (by positivity) Real.pi_pos.ne']; congr 1; field_simp
  have hE : Real.exp (-(R - a) * Real.log (t / (2 * Real.pi)) + 12 * (R - a + |c|) / t
        + 4 * (1 / 2 + a) / t)
      = Real.exp (-(R - a) * Real.log (t / 2) + 12 * (R - a + |c|) / t)
        * Real.exp ((R - a) * Real.log Real.pi) * Real.exp (4 * (1 / 2 + a) / t) := by
    rw [← Real.exp_add, ← Real.exp_add, hlogt]; congr 1; ring
  rw [hE]
  set e₁ := Real.exp (-(R - a) * Real.log (t / 2) + 12 * (R - a + |c|) / t)
  set e₂ := Real.exp ((R - a) * Real.log Real.pi)
  set e₃ := Real.exp (4 * (1 / 2 + a) / t)
  have he₁ : 0 < e₁ := Real.exp_pos _
  have he₂ : 0 < e₂ := Real.exp_pos _
  have he₃ : 0 < e₃ := Real.exp_pos _
  have hm2 : m₀ ^ 2 ≤ Z₀ ^ 2 := by gcongr
  have hlhs : P₁ * (q₁ * G₁) * Z₁ * (P₂ * (q₁ * G₂) * Z₂)
      = (P₁ * P₂) * (q₁ * q₁) * (G₁ * G₂) * (Z₁ * Z₂) := by ring
  rw [hlhs, hpi]
  have hA : 0 ≤ (P₁ * P₂) := by positivity
  have step1 : (P₁ * P₂) * (q₀ ^ 2 * e₂) * (G₁ * G₂) * (Z₁ * Z₂)
      ≤ (P₀ ^ 2 * e₃) * (q₀ ^ 2 * e₂) * (G₀ ^ 2 * e₁) * B ^ 2 := by
    apply mul_le_mul _ hZ (by positivity) (by positivity)
    apply mul_le_mul _ hG (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_right hP (by positivity)
  have step2 : (P₀ ^ 2 * e₃) * (q₀ ^ 2 * e₂) * (G₀ ^ 2 * e₁) * B ^ 2
      = (P₀ * (q₀ * G₀)) ^ 2 * m₀ ^ 2 * ((B / m₀) ^ 2 * (e₁ * e₂ * e₃)) := by
    rw [div_pow]; field_simp
  have step3 : (P₀ * (q₀ * G₀)) ^ 2 * m₀ ^ 2 * ((B / m₀) ^ 2 * (e₁ * e₂ * e₃))
      ≤ (P₀ * (q₀ * G₀)) ^ 2 * Z₀ ^ 2 * ((B / m₀) ^ 2 * (e₁ * e₂ * e₃)) := by
    gcongr
  calc _ ≤ _ := step1
    _ = _ := step2
    _ ≤ _ := step3
    _ = (P₀ * (q₀ * G₀) * Z₀) ^ 2 * (B / m₀) ^ 2 * (e₁ * e₂ * e₃) := by ring

/-- On a point `a + ic` the slice product has modulus `|ξ(½+a+i(t+c))| |ξ(½+a+i(t−c))|`: the second
factor is moved into the right half-plane by the functional equation and conjugation. -/
theorem norm_xiSliceProduct_eq (t a c : ℝ) :
    ‖xiSliceProduct t ((a : ℂ) + (c : ℂ) * I)‖
      = ‖xi (((1 / 2 + a : ℝ) : ℂ) + ((t + c : ℝ) : ℂ) * I)‖
        * ‖xi (((1 / 2 + a : ℝ) : ℂ) + ((t - c : ℝ) : ℂ) * I)‖ := by
  unfold xiSliceProduct
  rw [norm_mul]
  congr 1
  · congr 2; push_cast; ring
  · have e : (1 / 2 : ℂ) - ((a : ℂ) + (c : ℂ) * I) + (t : ℂ) * I
        = 1 - (starRingEnd ℂ) (((1 / 2 + a : ℝ) : ℂ) + ((t - c : ℝ) : ℂ) * I) := by
      apply Complex.ext <;> simp <;> ring
    rw [e, xi_one_sub, xi_conj, Complex.norm_conj]

/-- On the positive real axis the slice product is `|ξ(½+R+it)|²`. -/
theorem norm_xiSliceProduct_real (t R : ℝ) :
    ‖xiSliceProduct t (R : ℂ)‖ = ‖xi (((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  have := norm_xiSliceProduct_eq t R 0
  simp only [ofReal_zero, zero_mul, add_zero, sub_zero] at this
  rw [this, sq]

theorem re_ofReal_add_ofReal_mul_I_eq (x y : ℝ) : ((x : ℂ) + (y : ℂ) * I).re = x := by simp

/-- A point of the circle `|x| = R` in Cartesian form. -/
theorem ofReal_mul_exp_mul_I (R θ : ℝ) :
    (R : ℂ) * Complex.exp ((θ : ℂ) * I)
      = ((R * Real.cos θ : ℝ) : ℂ) + ((R * Real.sin θ : ℝ) : ℂ) * I := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  push_cast
  ring

/-- **Arc decay of the slice product.**  At height `t ≥ 8`, on the circle `|x| = R ≤ t/2` in the
right half-plane, with `ζ`-bounds `m₀ ≤ |ζ(½+R+it)|` and `|ζ(½+R cos θ + i(t ± R sin θ))| ≤ B`,
`|g_t(Re^{iθ})| ≤ g_t(R) (B/m₀)² exp(−R(1−cos θ) log(t/2π) + 12R(1−cos θ+|sin θ|)/t
+ 4(½+R cos θ)/t)`. -/
theorem norm_xiSliceProduct_circle_le {t R θ B m₀ : ℝ} (ht : 8 ≤ t) (hR : 0 ≤ R)
    (hRt : R ≤ t / 2) (hcos : 0 ≤ Real.cos θ) (hm₀ : 0 < m₀)
    (hz₀ : m₀ ≤ ‖riemannZeta (((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I)‖)
    (hz₁ : ‖riemannZeta (((1 / 2 + R * Real.cos θ : ℝ) : ℂ)
      + ((t + R * Real.sin θ : ℝ) : ℂ) * I)‖ ≤ B)
    (hz₂ : ‖riemannZeta (((1 / 2 + R * Real.cos θ : ℝ) : ℂ)
      + ((t - R * Real.sin θ : ℝ) : ℂ) * I)‖ ≤ B) :
    ‖xiSliceProduct t ((R : ℂ) * Complex.exp ((θ : ℂ) * I))‖
      ≤ ‖xiSliceProduct t (R : ℂ)‖ * (B / m₀) ^ 2
        * Real.exp (-(R * (1 - Real.cos θ)) * Real.log (t / (2 * Real.pi))
          + 12 * (R * (1 - Real.cos θ) + R * |Real.sin θ|) / t
          + 4 * (1 / 2 + R * Real.cos θ) / t) := by
  rw [ofReal_mul_exp_mul_I, norm_xiSliceProduct_eq, norm_xiSliceProduct_real]
  have hsin : |R * Real.sin θ| ≤ t / 2 := by
    rw [abs_mul, abs_of_nonneg hR]
    calc R * |Real.sin θ| ≤ R * 1 := by gcongr; exact Real.abs_sin_le_one θ
      _ ≤ t / 2 := by linarith
  have ha : R * Real.cos θ ≤ R := by
    have := Real.cos_le_one θ; nlinarith
  have h := norm_xi_split_le ht (mul_nonneg hR hcos) ha hsin hm₀ hz₀ hz₁ hz₂
  have e : -(R - R * Real.cos θ) * Real.log (t / (2 * Real.pi))
      + 12 * (R - R * Real.cos θ + |R * Real.sin θ|) / t + 4 * (1 / 2 + R * Real.cos θ) / t
      = -(R * (1 - Real.cos θ)) * Real.log (t / (2 * Real.pi))
        + 12 * (R * (1 - Real.cos θ) + R * |Real.sin θ|) / t
        + 4 * (1 / 2 + R * Real.cos θ) / t := by
    rw [abs_mul, abs_of_nonneg hR]; ring
  rw [e] at h
  exact h

/-- **Arc decay, `ζ` bounds supplied.**  For `t ≥ 8`, `5/2 ≤ R ≤ t/2` and `cos θ ≥ 0`: in general
the `ζ` ratio costs at most `(4 + 12t)²`; where `R cos θ ≥ 3/2` it costs at most `16`. -/
theorem norm_xiSliceProduct_circle_le_explicit {t R θ : ℝ} (ht : 8 ≤ t) (hR : 5 / 2 ≤ R)
    (hRt : R ≤ t / 2) (hcos : 0 ≤ Real.cos θ) :
    ‖xiSliceProduct t ((R : ℂ) * Complex.exp ((θ : ℂ) * I))‖
      ≤ ‖xiSliceProduct t (R : ℂ)‖
        * (if 3 / 2 ≤ R * Real.cos θ then 16 else (4 + 12 * t) ^ 2)
        * Real.exp (-(R * (1 - Real.cos θ)) * Real.log (t / (2 * Real.pi))
          + 12 * (R * (1 - Real.cos θ) + R * |Real.sin θ|) / t
          + 4 * (1 / 2 + R * Real.cos θ) / t) := by
  have hz₀ : 1 / 2 ≤ ‖riemannZeta (((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I)‖ :=
    one_half_le_norm_riemannZeta_of_three_le_re (by simp; linarith)
  have hR0 : 0 ≤ R := by linarith
  have hsinR : |R * Real.sin θ| ≤ t / 2 := by
    rw [abs_mul, abs_of_nonneg hR0]
    calc R * |Real.sin θ| ≤ R * 1 := by gcongr; exact Real.abs_sin_le_one θ
      _ ≤ t / 2 := by linarith
  have hsinabs := abs_le.mp hsinR
  have ha0 : 0 ≤ R * Real.cos θ := mul_nonneg hR0 hcos
  split_ifs with ha
  · have hz : ∀ y : ℝ, ‖riemannZeta (((1 / 2 + R * Real.cos θ : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤ 2 := by
      intro y
      have := norm_riemannZeta_le_of_two_le_re
        (s := ((1 / 2 + R * Real.cos θ : ℝ) : ℂ) + (y : ℂ) * I)
        (by rw [re_ofReal_add_ofReal_mul_I_eq]; linarith)
      nlinarith [Real.pi_lt_d2, Real.pi_pos]
    have h := norm_xiSliceProduct_circle_le ht hR0 hRt hcos (by norm_num : (0 : ℝ) < 1 / 2) hz₀
      (hz _) (hz _)
    convert h using 2
    norm_num
  · have hz : ∀ y : ℝ, t / 2 ≤ y → y ≤ 3 * t / 2 →
        ‖riemannZeta (((1 / 2 + R * Real.cos θ : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤ 2 + 6 * t := by
      intro y hy1 hy2
      have hy : 2 ≤ |y| := by rw [abs_of_nonneg (by linarith)]; linarith
      have := norm_riemannZeta_le_of_half_le_re (σ := 1 / 2 + R * Real.cos θ) (by linarith) hy
      rw [abs_of_nonneg (by linarith)] at this
      linarith
    have h := norm_xiSliceProduct_circle_le ht hR0 hRt hcos (by norm_num : (0 : ℝ) < 1 / 2) hz₀
      (hz _ (by linarith) (by linarith)) (hz _ (by linarith) (by linarith))
    convert h using 2
    field_simp
    ring

end

end RHTower
