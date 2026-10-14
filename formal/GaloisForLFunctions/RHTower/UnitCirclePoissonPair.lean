import GaloisForLFunctions.RHTower.ModularArcLineModelBlind

/-!
# The even `s = ½` Poisson pair of a point of the unit circle

For `z = c + iy` with `c² + y² = 1` and `y > 0` put

`P_z(x) = ((x − c)² + y²)^{−1/2} + ((x + c)² + y²)^{−1/2}`  (`circlePair c y x`),

the sum of the `s = ½` Poisson vectors `|x − z|^{−1}` and `|x + z̄|^{−1}` divided by `√y`.

* `circlePair_inv`: `P_z(1/x) = |x| P_z(x)`, because `(1/x − c)² + y² = ((x − c)² + y²)/x²` on the
  unit circle.
* `exp_half_mul_circlePair`: `e^{v/2} P_z(e^v) = 2^{−1/2} 𝒦_c(v)`, with
  `𝒦_c(v) = (cosh v + c)^{−1/2} + (cosh v − c)^{−1/2}` (`symCoshKernel`).
* `integral_circlePairDeriv_mul_sin`: `∫ P_z'(x) sin(ax) dx = −4a K₀(ay) cos(ac)` for `a > 0`.
* Bounds: `|P_z'(x)| ≤ max(1, y^{−2}) ((1 + (x − c)²)^{−1} + (1 + (x + c)²)^{−1})` and
  `𝒦_c(v) ≤ (2√2/y) (cosh v)^{−1/2}`, from `1 − |c| ≥ y²/2`.

These are the kernel facts behind superpositions of generators along the whole unit semicircle,
including the side arcs that run down to the cusp.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-- `P_z(x) = ((x − c)² + y²)^{−1/2} + ((x + c)² + y²)^{−1/2}`. -/
def circlePair (c y x : ℝ) : ℝ :=
  ((x - c) ^ 2 + y ^ 2) ^ (-(1 / 2) : ℝ) + ((x + c) ^ 2 + y ^ 2) ^ (-(1 / 2) : ℝ)

/-- `P_z'(x) = −(x − c)((x − c)² + y²)^{−3/2} − (x + c)((x + c)² + y²)^{−3/2}`. -/
def circlePairDeriv (c y x : ℝ) : ℝ :=
  -((x - c) * ((x - c) ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) +
    (x + c) * ((x + c) ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ))

theorem hasDerivAt_rpow_neg_half_shift {y : ℝ} (hy : 0 < y) (u x : ℝ) :
    HasDerivAt (fun x => ((x - u) ^ 2 + y ^ 2) ^ (-(1 / 2) : ℝ))
      (-((x - u) * ((x - u) ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ))) x := by
  have hA : 0 < (x - u) ^ 2 + y ^ 2 := by positivity
  have hd : HasDerivAt (fun x : ℝ => (x - u) ^ 2 + y ^ 2) (2 * (x - u)) x := by
    have := ((hasDerivAt_id x).sub_const u).pow 2
    simpa using this.add_const (y ^ 2)
  have h := hd.rpow_const (p := -(1 / 2)) (Or.inl hA.ne')
  refine h.congr_deriv ?_
  rw [show (-(1 / 2) : ℝ) - 1 = -(3 / 2) by norm_num]
  ring

theorem hasDerivAt_circlePair {c y : ℝ} (hy : 0 < y) (x : ℝ) :
    HasDerivAt (circlePair c y) (circlePairDeriv c y x) x := by
  have h1 := hasDerivAt_rpow_neg_half_shift hy c x
  have h2 := hasDerivAt_rpow_neg_half_shift hy (-c) x
  simp only [sub_neg_eq_add] at h2
  refine (h1.add h2).congr_deriv ?_
  unfold circlePairDeriv
  ring

theorem circlePair_neg (c y x : ℝ) : circlePair c y (-x) = circlePair c y x := by
  unfold circlePair
  rw [show (-x - c) ^ 2 = (x + c) ^ 2 by ring, show (-x + c) ^ 2 = (x - c) ^ 2 by ring, add_comm]

theorem circlePair_nonneg (c y x : ℝ) : 0 ≤ circlePair c y x := by
  unfold circlePair
  exact add_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by positivity) _)

theorem sq_add_eq_div_of_circle {c y : ℝ} (hcy : c ^ 2 + y ^ 2 = 1) {x : ℝ} (hx : x ≠ 0)
    (u : ℝ) (hu : u = c ∨ u = -c) :
    (1 / x - u) ^ 2 + y ^ 2 = ((x - u) ^ 2 + y ^ 2) / x ^ 2 := by
  have hu2 : u ^ 2 + y ^ 2 = 1 := by rcases hu with rfl | rfl <;> nlinarith
  field_simp
  nlinarith [hu2]

/-- **Inversion.**  `P_z(1/x) = |x| P_z(x)` on the unit circle. -/
theorem circlePair_inv {c y : ℝ} (hcy : c ^ 2 + y ^ 2 = 1) (hy : 0 < y) {x : ℝ} (hx : x ≠ 0) :
    circlePair c y (1 / x) = |x| * circlePair c y x := by
  unfold circlePair
  have hx2 : 0 < x ^ 2 := by positivity
  have key : ∀ u : ℝ, (u = c ∨ u = -c) →
      ((1 / x - u) ^ 2 + y ^ 2) ^ (-(1 / 2) : ℝ) =
        |x| * ((x - u) ^ 2 + y ^ 2) ^ (-(1 / 2) : ℝ) := by
    intro u hu
    have hA : 0 < (x - u) ^ 2 + y ^ 2 := by positivity
    rw [sq_add_eq_div_of_circle hcy hx u hu, Real.div_rpow hA.le hx2.le,
      Real.rpow_neg hx2.le, ← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs, div_inv_eq_mul, mul_comm]
  rw [key c (Or.inl rfl), show (1 / x + c) = 1 / x - (-c) by ring, key (-c) (Or.inr rfl),
    show x - -c = x + c by ring, mul_add]

/-- **The log-scale profile.**  `e^{v/2} P_z(e^v) = 2^{−1/2} 𝒦_c(v)`. -/
theorem exp_half_mul_circlePair {c y : ℝ} (hcy : c ^ 2 + y ^ 2 = 1) (hy : 0 < y) (v : ℝ) :
    Real.exp (v / 2) * circlePair c y (Real.exp v) =
      (Real.sqrt 2)⁻¹ * symCoshKernel c v := by
  have hc1 : |c| < 1 := by
    rw [abs_lt]; constructor <;> nlinarith
  have hcm : 0 < Real.cosh v - c := by
    have := Real.one_le_cosh v; linarith [(abs_lt.mp hc1).2]
  have hcp : 0 < Real.cosh v + c := by
    have := Real.one_le_cosh v; linarith [(abs_lt.mp hc1).1]
  have hev := Real.exp_pos v
  have e1 : ∀ u : ℝ, (u = c ∨ u = -c) →
      (Real.exp v - u) ^ 2 + y ^ 2 = 2 * Real.exp v * (Real.cosh v - u) := by
    intro u hu
    have hu2 : u ^ 2 + y ^ 2 = 1 := by rcases hu with rfl | rfl <;> nlinarith
    rw [Real.cosh_eq]
    have h1 : Real.exp v * Real.exp (-v) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [h1]
  have key : ∀ u : ℝ, (u = c ∨ u = -c) → 0 < Real.cosh v - u →
      Real.exp (v / 2) * ((Real.exp v - u) ^ 2 + y ^ 2) ^ (-(1 / 2) : ℝ) =
        (Real.sqrt 2)⁻¹ * (Real.cosh v - u) ^ (-1 / 2 : ℝ) := by
    intro u hu hpos
    rw [e1 u hu, Real.mul_rpow (by positivity) hpos.le, Real.mul_rpow (by norm_num) hev.le]
    have he : Real.exp (v / 2) * Real.exp v ^ (-(1 / 2) : ℝ) = 1 := by
      rw [← Real.exp_mul, ← Real.exp_add]; ring_nf; simp
    have h2 : (2 : ℝ) ^ (-(1 / 2) : ℝ) = (Real.sqrt 2)⁻¹ := by
      rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]
    rw [h2, show (-(1 / 2) : ℝ) = -1 / 2 by norm_num]
    calc Real.exp (v / 2) * ((Real.sqrt 2)⁻¹ * Real.exp v ^ (-1 / 2 : ℝ) *
          (Real.cosh v - u) ^ (-1 / 2 : ℝ))
        = (Real.sqrt 2)⁻¹ * (Real.exp (v / 2) * Real.exp v ^ (-(1 / 2) : ℝ)) *
            (Real.cosh v - u) ^ (-1 / 2 : ℝ) := by norm_num; ring
      _ = (Real.sqrt 2)⁻¹ * (Real.cosh v - u) ^ (-1 / 2 : ℝ) := by rw [he, mul_one]
  unfold circlePair symCoshKernel
  rw [mul_add, key c (Or.inl rfl) hcm, show Real.exp v + c = Real.exp v - (-c) by ring,
    key (-c) (Or.inr rfl) (by linarith), sub_neg_eq_add, mul_add, add_comm]

/-- The derivative kernel is controlled by two Cauchy profiles. -/
theorem abs_circlePairDeriv_le {c y : ℝ} (hy : 0 < y) (x : ℝ) :
    |circlePairDeriv c y x| ≤
      max 1 (1 / y ^ 2) * ((1 + (x - c) ^ 2)⁻¹ + (1 + (x + c) ^ 2)⁻¹) := by
  unfold circlePairDeriv
  rw [abs_neg]
  have h1 := abs_mul_rpow_le_inv (x := x - c) hy
  have h2 := abs_mul_rpow_le_inv (x := x + c) hy
  have hA : 0 ≤ ((x - c) ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) := Real.rpow_nonneg (by positivity) _
  have hB : 0 ≤ ((x + c) ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) := Real.rpow_nonneg (by positivity) _
  calc |(x - c) * ((x - c) ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) +
        (x + c) * ((x + c) ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ)|
      ≤ |x - c| * ((x - c) ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) +
          |x + c| * ((x + c) ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_nonneg hA, abs_of_nonneg hB]
    _ ≤ _ := by rw [mul_add]; exact add_le_add h1 h2

theorem abs_circlePairDeriv_le_const {c y : ℝ} (hy : 0 < y) (x : ℝ) :
    |circlePairDeriv c y x| ≤ 2 * max 1 (1 / y ^ 2) := by
  refine (abs_circlePairDeriv_le hy x).trans ?_
  have h1 : (1 + (x - c) ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg (x - c)])
  have h2 : (1 + (x + c) ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg (x + c)])
  have hm : 0 ≤ max 1 (1 / y ^ 2) := le_max_of_le_left zero_le_one
  nlinarith

/-- **Fourier coefficients of the derivative.**  `∫ P_z'(x) sin(ax) dx = −4a K₀(ay) cos(ac)`. -/
theorem integral_circlePairDeriv_mul_sin {c y a : ℝ} (hy : 0 < y) (ha : 0 < a) :
    ∫ x, circlePairDeriv c y x * Real.sin (a * x) =
      -(4 * a * kMoment 0 (a * y) * Real.cos (a * c)) := by
  have hi1 : Integrable fun x : ℝ => (x - c) * ((x - c) ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) *
      Real.sin (a * x) := by
    have h := (integrable_mul_rpow_mul_trig hy (g := fun w => Real.sin (a * (w + c)))
      (by fun_prop) fun w => Real.abs_sin_le_one _).comp_sub_right c
    simpa using h
  have hi2 : Integrable fun x : ℝ => (x + c) * ((x + c) ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) *
      Real.sin (a * x) := by
    have h := (integrable_mul_rpow_mul_trig hy (g := fun w => Real.sin (a * (w - c)))
      (by fun_prop) fun w => Real.abs_sin_le_one _).comp_add_right c
    simpa using h
  have e : (fun x => circlePairDeriv c y x * Real.sin (a * x)) = fun x =>
      -((x - c) * ((x - c) ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) * Real.sin (a * x) +
        (x + c) * ((x + c) ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) * Real.sin (a * x)) := by
    funext x; unfold circlePairDeriv; ring
  rw [e, integral_neg, integral_add hi1 hi2, integral_shift_mul_rpow_sin hy ha c]
  have h2 := integral_shift_mul_rpow_sin hy ha (-c)
  simp only [sub_neg_eq_add] at h2
  rw [h2, mul_neg, Real.cos_neg]
  ring

/-- `𝒦_c(v) ≤ (2√2/y) (cosh v)^{−1/2}` on the unit circle. -/
theorem symCoshKernel_le_of_circle {c y : ℝ} (hcy : c ^ 2 + y ^ 2 = 1) (hy : 0 < y) (v : ℝ) :
    symCoshKernel c v ≤ 2 * Real.sqrt 2 / y * Real.cosh v ^ (-(1 / 2) : ℝ) := by
  have hc1 : |c| < 1 := by rw [abs_lt]; constructor <;> nlinarith
  have hch := Real.one_le_cosh v
  have hδ : y ^ 2 / 2 ≤ 1 - |c| := by
    have h : (1 - |c|) * (1 + |c|) = y ^ 2 := by nlinarith [sq_abs c]
    nlinarith [abs_nonneg c]
  have hδ0 : 0 < 1 - |c| := by linarith
  have hbase : ∀ u : ℝ, |u| = |c| → (1 - |c|) * Real.cosh v ≤ Real.cosh v - u := by
    intro u hu
    have : u ≤ |c| := hu ▸ le_abs_self u
    nlinarith [mul_le_mul_of_nonneg_left hch (abs_nonneg c)]
  have hterm : ∀ u : ℝ, |u| = |c| →
      (Real.cosh v - u) ^ (-1 / 2 : ℝ) ≤ Real.sqrt 2 / y * Real.cosh v ^ (-(1 / 2) : ℝ) := by
    intro u hu
    have hb := hbase u hu
    have hpos : 0 < (1 - |c|) * Real.cosh v := by positivity
    calc (Real.cosh v - u) ^ (-1 / 2 : ℝ) ≤ ((1 - |c|) * Real.cosh v) ^ (-1 / 2 : ℝ) :=
          Real.rpow_le_rpow_of_nonpos hpos hb (by norm_num)
      _ = (1 - |c|) ^ (-1 / 2 : ℝ) * Real.cosh v ^ (-(1 / 2) : ℝ) := by
          rw [Real.mul_rpow hδ0.le (by positivity)]; norm_num
      _ ≤ Real.sqrt 2 / y * Real.cosh v ^ (-(1 / 2) : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
          calc (1 - |c|) ^ (-1 / 2 : ℝ) ≤ (y ^ 2 / 2) ^ (-1 / 2 : ℝ) :=
                Real.rpow_le_rpow_of_nonpos (by positivity) hδ (by norm_num)
            _ = Real.sqrt 2 / y := by
                rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_natCast,
                  ← Real.rpow_mul hy.le]
                norm_num
                rw [Real.rpow_neg_one, Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]
                field_simp
  unfold symCoshKernel
  have h1 := hterm (-c) (abs_neg c)
  have h2 := hterm c rfl
  rw [sub_neg_eq_add] at h1
  calc (Real.cosh v + c) ^ (-1 / 2 : ℝ) + (Real.cosh v - c) ^ (-1 / 2 : ℝ)
      ≤ Real.sqrt 2 / y * Real.cosh v ^ (-(1 / 2) : ℝ) +
          Real.sqrt 2 / y * Real.cosh v ^ (-(1 / 2) : ℝ) := add_le_add h1 h2
    _ = 2 * Real.sqrt 2 / y * Real.cosh v ^ (-(1 / 2) : ℝ) := by ring

theorem symCoshKernel_nonneg {c : ℝ} (hc : |c| ≤ 1) (v : ℝ) : 0 ≤ symCoshKernel c v := by
  have hch := Real.one_le_cosh v
  have h := abs_le.mp hc
  unfold symCoshKernel
  exact add_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by linarith) _)

end

end RHTower
