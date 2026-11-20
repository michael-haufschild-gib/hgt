import GaloisForLFunctions.HTGeometry.CosinePolynomialPurchaseCap
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The Gross–Witten–Wadia wall

At large `N` the eigenvalues of the thermal holonomy form a density on the circle whose Fourier
coefficients are the moments `uₙ`. With only the Polyakov loop `u₁ = u` switched on, the density is
`(1 + 2 Re(u e^{-iθ}))/2π`, and it is nonnegative exactly when `|u| ≤ 1/2`. The same sharp
criterion upgrades the corpus statement "a nonnegative degree-one cosine polynomial has
`a₁ ≤ a₀`" to the equivalence `|a₁| ≤ a₀`.

Beyond `u = 1/2` the density gaps and the Haar measure at fixed `|u₁| = u` costs

  `V(u) = u²` for `u ≤ 1/2`,  `V(u) = 1/4 − ½ log(2(1 − u))` for `1/2 ≤ u < 1`.

The two branches meet with equal value, slope `1` and curvature `2`; the third derivative jumps
from `0` to `8` (a third-order junction). The excess `V(u) − u²` is a wall that rises like
`(4/3)ε³` at `u = 1/2 + ε`: `(4/3)ε³ ≤ V − u² ≤ (4/3)ε³ + 8ε⁴/(1 − 2ε)`.
-/

noncomputable section

open Real

namespace GaloisForLFunctions.HagedornBootstrap

/-! ### Positivity of the one-mode density -/

/-- `1 + 2u cos θ ≥ 0` for every `θ` exactly when `|u| ≤ 1/2`. -/
theorem one_add_two_mul_cos_nonneg_iff (u : ℝ) :
    (∀ θ : ℝ, 0 ≤ 1 + 2 * u * Real.cos θ) ↔ |u| ≤ 1 / 2 := by
  constructor
  · intro h
    have h0 := h 0
    have hπ := h π
    rw [Real.cos_zero] at h0
    rw [Real.cos_pi] at hπ
    rw [abs_le]; constructor <;> linarith
  · intro hu θ
    have h1 := Real.neg_one_le_cos θ
    have h2 := Real.cos_le_one θ
    rw [abs_le] at hu
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 1 / 2 + u by linarith) (show 0 ≤ 1 + Real.cos θ by linarith),
      mul_nonneg (show (0 : ℝ) ≤ 1 / 2 - u by linarith) (show 0 ≤ 1 - Real.cos θ by linarith)]

/-- **The gap criterion.** The density `1 + 2 Re(u e^{-iθ})` with complex Polyakov loop `u` is
nonnegative everywhere exactly when `‖u‖ ≤ 1/2`. -/
theorem polyakovDensity_nonneg_iff (u : ℂ) :
    (∀ θ : ℝ, 0 ≤ 1 + 2 * (u * Complex.exp (-(θ * Complex.I))).re) ↔ ‖u‖ ≤ 1 / 2 := by
  constructor
  · intro h
    set A := Complex.arg u with hA
    have key := h (A + π)
    have hu : u * Complex.exp (-(((A + π : ℝ) : ℂ) * Complex.I)) = -((‖u‖ : ℝ) : ℂ) := by
      have hsplit : u * Complex.exp (-(((A + π : ℝ) : ℂ) * Complex.I)) =
          (‖u‖ : ℂ) * (Complex.exp (A * Complex.I) * Complex.exp (-(((A + π : ℝ) : ℂ) * Complex.I))) := by
        nth_rewrite 1 [← Complex.norm_mul_exp_arg_mul_I u]
        rw [← hA]; ring
      rw [hsplit, ← Complex.exp_add]
      push_cast
      rw [show (A : ℂ) * Complex.I + -(((A : ℂ) + (π : ℂ)) * Complex.I) = -((π : ℂ) * Complex.I) by ring,
        Complex.exp_neg, Complex.exp_pi_mul_I]
      simp
    rw [hu] at key
    simp only [Complex.neg_re, Complex.ofReal_re] at key
    linarith
  · intro hu θ
    have h1 : ‖u * Complex.exp (-(θ * Complex.I))‖ = ‖u‖ := by
      rw [norm_mul, show -((θ : ℂ) * Complex.I) = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I, mul_one]
    have h2 := Complex.abs_re_le_norm (u * Complex.exp (-(θ * Complex.I)))
    rw [h1] at h2
    have := neg_abs_le (u * Complex.exp (-(θ * Complex.I))).re
    linarith

/-- The degree-one cosine polynomials of the corpus. -/
theorem cosinePolynomial_one_eq (a : ℕ → ℝ) (θ : ℝ) :
    HTGeometry.cosinePolynomial a 1 θ = a 0 + a 1 * Real.cos θ := by
  simp [HTGeometry.cosinePolynomial, Finset.sum_range_succ]

/-- **Sharp degree-one Fejér criterion:** `a₀ + a₁ cos θ ≥ 0` for all `θ` iff `|a₁| ≤ a₀`. -/
theorem cosinePolynomial_one_nonneg_iff (a : ℕ → ℝ) :
    (∀ θ, 0 ≤ HTGeometry.cosinePolynomial a 1 θ) ↔ |a 1| ≤ a 0 := by
  simp_rw [cosinePolynomial_one_eq]
  constructor
  · intro h
    have h0 := h 0
    have hπ := h π
    rw [Real.cos_zero] at h0
    rw [Real.cos_pi] at hπ
    rw [abs_le]; constructor <;> linarith
  · intro hu θ
    have h1 := Real.neg_one_le_cos θ
    have h2 := Real.cos_le_one θ
    rw [abs_le] at hu
    nlinarith [mul_nonneg (show 0 ≤ a 0 + a 1 by linarith) (show 0 ≤ 1 + Real.cos θ by linarith),
      mul_nonneg (show 0 ≤ a 0 - a 1 by linarith) (show 0 ≤ 1 - Real.cos θ by linarith)]

/-- The one-mode density has total mass one ... -/
theorem integral_polyakovDensity (u : ℝ) :
    ∫ θ in (-π)..π, (1 + 2 * u * Real.cos θ) / (2 * π) = 1 := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have h2 : IntervalIntegrable (fun x : ℝ => 2 * u * Real.cos x) MeasureTheory.volume (-π) π := by
    apply Continuous.intervalIntegrable; fun_prop
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_add (f := fun _ => (1 : ℝ)) (g := fun x => 2 * u * Real.cos x)
      intervalIntegrable_const h2,
    intervalIntegral.integral_const_mul, integral_cos]
  simp
  field_simp
  ring

/-- ... and its first moment is the Polyakov loop `u`. -/
theorem integral_polyakovDensity_mul_cos (u : ℝ) :
    ∫ θ in (-π)..π, (1 + 2 * u * Real.cos θ) / (2 * π) * Real.cos θ = u := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hform : (fun θ : ℝ => (1 + 2 * u * Real.cos θ) / (2 * π) * Real.cos θ) =
      fun θ => (1 / (2 * π)) * Real.cos θ + (u / π) * Real.cos θ ^ 2 := by
    funext θ; field_simp
  have h1 : IntervalIntegrable (fun x : ℝ => (1 / (2 * π)) * Real.cos x) MeasureTheory.volume (-π) π := by
    apply Continuous.intervalIntegrable; fun_prop
  have h2 : IntervalIntegrable (fun x : ℝ => (u / π) * Real.cos x ^ 2) MeasureTheory.volume (-π) π := by
    apply Continuous.intervalIntegrable; fun_prop
  rw [hform, intervalIntegral.integral_add (f := fun x => (1 / (2 * π)) * Real.cos x)
      (g := fun x => (u / π) * Real.cos x ^ 2) h1 h2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_cos,
    integral_cos_sq]
  simp

/-! ### The Gross–Witten–Wadia potential -/

/-- The gapped branch `1/4 − ½ log(2(1 − u))`. -/
def gwwGapped (u : ℝ) : ℝ := 1 / 4 - Real.log (2 * (1 - u)) / 2

/-- The Haar cost of a Polyakov loop of modulus `u` at large `N`. -/
def gwwPotential (u : ℝ) : ℝ := if u ≤ 1 / 2 then u ^ 2 else gwwGapped u

/-- The derivative of `V`. -/
def gwwDeriv (u : ℝ) : ℝ := if u ≤ 1 / 2 then 2 * u else 1 / (2 * (1 - u))

theorem gwwGapped_half : gwwGapped (1 / 2) = 1 / 4 := by norm_num [gwwGapped]

theorem gwwPotential_of_le {u : ℝ} (h : u ≤ 1 / 2) : gwwPotential u = u ^ 2 := if_pos h

theorem gwwPotential_of_gt {u : ℝ} (h : 1 / 2 < u) : gwwPotential u = gwwGapped u :=
  if_neg (not_le.mpr h)

theorem gwwPotential_of_ge {u : ℝ} (h : 1 / 2 ≤ u) : gwwPotential u = gwwGapped u := by
  rcases h.lt_or_eq with h | h
  · exact gwwPotential_of_gt h
  · subst h; rw [gwwPotential_of_le le_rfl, gwwGapped_half]; norm_num

theorem gwwDeriv_of_le {u : ℝ} (h : u ≤ 1 / 2) : gwwDeriv u = 2 * u := if_pos h

theorem gwwDeriv_of_ge {u : ℝ} (h : 1 / 2 ≤ u) : gwwDeriv u = 1 / (2 * (1 - u)) := by
  rcases h.lt_or_eq with h | h
  · exact if_neg (not_le.mpr h)
  · subst h; rw [gwwDeriv_of_le le_rfl]; norm_num

theorem hasDerivAt_gwwGapped {u : ℝ} (hu : u < 1) :
    HasDerivAt gwwGapped (1 / (2 * (1 - u))) u := by
  have h1 : 2 * (1 - u) ≠ 0 := by linarith
  have h := (((hasDerivAt_id u).const_sub 1).const_mul 2).log h1
  refine ((h.div_const 2).const_sub (1 / 4)).congr_deriv ?_
  simp only [id]
  field_simp

theorem hasDerivAt_gwwGapped_deriv {u : ℝ} (hu : u < 1) :
    HasDerivAt (fun u : ℝ => 1 / (2 * (1 - u))) (1 / (2 * (1 - u) ^ 2)) u := by
  have h1 : 2 * (1 - u) ≠ 0 := by linarith
  have h : HasDerivAt (fun u : ℝ => 2 * (1 - u)) (-2) u := by
    refine (((hasDerivAt_id u).const_sub 1).const_mul 2).congr_deriv ?_; ring
  refine (h.inv h1).congr_deriv ?_ |>.congr_of_eventuallyEq ?_
  · field_simp
  · filter_upwards with v; simp [one_div]

theorem hasDerivAt_gwwGapped_second {u : ℝ} (hu : u < 1) :
    HasDerivAt (fun u : ℝ => 1 / (2 * (1 - u) ^ 2)) (1 / (1 - u) ^ 3) u := by
  have h0 : 1 - u ≠ 0 := by linarith
  have h1 : 2 * (1 - u) ^ 2 ≠ 0 := by positivity
  have h : HasDerivAt (fun u : ℝ => 2 * (1 - u) ^ 2) (-(4 * (1 - u))) u := by
    refine ((((hasDerivAt_id u).const_sub 1).pow 2).const_mul 2).congr_deriv ?_
    simp only [id]; push_cast; ring
  refine (h.inv h1).congr_deriv ?_ |>.congr_of_eventuallyEq ?_
  · field_simp
    ring
  · filter_upwards with v; simp [one_div]

/-- `V` is differentiable on `(−∞, 1)`, the two branches joining with slope `1` at `u = 1/2`. -/
theorem hasDerivAt_gwwPotential {u : ℝ} (hu : u < 1) :
    HasDerivAt gwwPotential (gwwDeriv u) u := by
  rcases lt_trichotomy u (1 / 2) with h | rfl | h
  · have hev : gwwPotential =ᶠ[nhds u] fun v => v ^ 2 := by
      filter_upwards [Iio_mem_nhds h] with v hv
      exact gwwPotential_of_le (le_of_lt hv)
    rw [gwwDeriv_of_le h.le]
    refine HasDerivAt.congr_of_eventuallyEq ?_ hev
    simpa using hasDerivAt_pow 2 u
  · rw [gwwDeriv_of_le le_rfl]
    have hL : HasDerivWithinAt gwwPotential (2 * (1 / 2)) (Set.Iic (1 / 2)) (1 / 2) := by
      have := (hasDerivAt_pow 2 (1 / 2 : ℝ)).hasDerivWithinAt (s := Set.Iic (1 / 2))
      refine (this.congr (fun v hv => gwwPotential_of_le hv) (gwwPotential_of_le le_rfl)).congr_deriv
        (by norm_num)
    have hR : HasDerivWithinAt gwwPotential (2 * (1 / 2)) (Set.Ici (1 / 2)) (1 / 2) := by
      have := (hasDerivAt_gwwGapped (u := 1 / 2) (by norm_num)).hasDerivWithinAt
        (s := Set.Ici (1 / 2))
      refine (this.congr (fun v hv => gwwPotential_of_ge hv) (gwwPotential_of_ge le_rfl)).congr_deriv
        (by norm_num)
    have := hL.union hR
    rwa [Set.Iic_union_Ici, hasDerivWithinAt_univ] at this
  · have hev : gwwPotential =ᶠ[nhds u] gwwGapped := by
      filter_upwards [Ioi_mem_nhds h] with v hv
      exact gwwPotential_of_gt hv
    rw [gwwDeriv_of_ge h.le]
    exact (hasDerivAt_gwwGapped hu).congr_of_eventuallyEq hev

/-- The curvature is continuous at the junction: `V'` has derivative `2` at `u = 1/2`. -/
theorem hasDerivAt_gwwDeriv_half : HasDerivAt gwwDeriv 2 (1 / 2) := by
  have hL : HasDerivWithinAt gwwDeriv 2 (Set.Iic (1 / 2)) (1 / 2) := by
    have := ((hasDerivAt_id (1 / 2 : ℝ)).const_mul 2).hasDerivWithinAt (s := Set.Iic (1 / 2))
    refine (this.congr (fun v hv => gwwDeriv_of_le hv) (gwwDeriv_of_le le_rfl)).congr_deriv
      (by norm_num)
  have hR : HasDerivWithinAt gwwDeriv 2 (Set.Ici (1 / 2)) (1 / 2) := by
    have := (hasDerivAt_gwwGapped_deriv (u := 1 / 2) (by norm_num)).hasDerivWithinAt
      (s := Set.Ici (1 / 2))
    refine (this.congr (fun v hv => gwwDeriv_of_ge hv) (gwwDeriv_of_ge le_rfl)).congr_deriv
      (by norm_num)
  have := hL.union hR
  rwa [Set.Iic_union_Ici, hasDerivWithinAt_univ] at this

/-- **Third-order junction.** On the ungapped side the third derivative is `0`; on the gapped
side the curvature `1/(2(1 − u)²)` has slope `1/(1 − u)³ = 8` at `u = 1/2`. -/
theorem gww_third_derivative_jump :
    HasDerivAt (fun u : ℝ => 1 / (2 * (1 - u) ^ 2)) 8 (1 / 2) ∧
      HasDerivAt (fun _ : ℝ => (2 : ℝ)) 0 (1 / 2) :=
  ⟨(hasDerivAt_gwwGapped_second (by norm_num)).congr_deriv (by norm_num), hasDerivAt_const _ _⟩

/-- The wall in the variable `t = 2ε`: `V(1/2 + ε) − (1/2 + ε)² = ½(−log(1 − t)) − t/2 − t²/4`. -/
theorem gwwWall_eq (ε : ℝ) :
    gwwGapped (1 / 2 + ε) - (1 / 2 + ε) ^ 2 =
      -Real.log (1 - 2 * ε) / 2 - (2 * ε) / 2 - (2 * ε) ^ 2 / 4 := by
  unfold gwwGapped
  rw [show 2 * (1 - (1 / 2 + ε)) = 1 - 2 * ε by ring]
  ring

/-- **The wall rises at least like `(4/3)ε³`.** -/
theorem gwwWall_ge {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε < 1 / 2) :
    4 / 3 * ε ^ 3 ≤ gwwGapped (1 / 2 + ε) - (1 / 2 + ε) ^ 2 := by
  rw [gwwWall_eq]
  have ht0 : 0 ≤ 2 * ε := by positivity
  have ht1 : |2 * ε| < 1 := by rw [abs_of_nonneg ht0]; linarith
  have hs := Real.hasSum_pow_div_log_of_abs_lt_one ht1
  have hle := sum_le_hasSum (Finset.range 3) (fun n _ => by positivity) hs
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hle
  norm_num at hle
  nlinarith

/-- **...and at most like `(4/3)ε³ + 8ε⁴/(1 − 2ε)`**, so `V − u² = (4/3)ε³ + O(ε⁴)`. -/
theorem gwwWall_le {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε < 1 / 2) :
    gwwGapped (1 / 2 + ε) - (1 / 2 + ε) ^ 2 ≤ 4 / 3 * ε ^ 3 + 8 * ε ^ 4 / (1 - 2 * ε) := by
  rw [gwwWall_eq]
  have ht0 : 0 ≤ 2 * ε := by positivity
  have ht1 : |2 * ε| < 1 := by rw [abs_of_nonneg ht0]; linarith
  have hb := Real.abs_log_sub_add_sum_range_le ht1 3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_of_nonneg ht0] at hb
  have hb' := (abs_le.mp hb).1
  have hpos : 0 < 1 - 2 * ε := by linarith
  have e4 : 8 * ε ^ 4 / (1 - 2 * ε) = (2 * ε) ^ (3 + 1) / (1 - 2 * ε) / 2 := by
    field_simp; ring
  rw [e4]
  norm_num at hb' ⊢
  nlinarith

/-- The wall is nonnegative: `u² ≤ V(u)` on `[0, 1)`. -/
theorem sq_le_gwwPotential {u : ℝ} (h1 : u < 1) : u ^ 2 ≤ gwwPotential u := by
  rcases le_or_gt u (1 / 2) with h | h
  · rw [gwwPotential_of_le h]
  · rw [gwwPotential_of_gt h]
    have hw := gwwWall_ge (ε := u - 1 / 2) (by linarith) (by linarith)
    rw [show 1 / 2 + (u - 1 / 2) = u by ring] at hw
    nlinarith [pow_nonneg (show (0 : ℝ) ≤ u - 1 / 2 by linarith) 3]

end GaloisForLFunctions.HagedornBootstrap
