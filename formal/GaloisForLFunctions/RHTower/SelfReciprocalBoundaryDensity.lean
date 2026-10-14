import GaloisForLFunctions.RHTower.LambdaPositiveFunctionalEquationOffLine
import GaloisForLFunctions.HTGeometry.TwoSidedExponentialMoments

/-!
# The spectral density of a self-reciprocal function is its boundary value on the unit circle

Let `F(ζ) = ∑ c_k ζ^k` with `∑ |c_k| < ∞` and let `h` be the even self-reciprocal function

  `h(x) = F(x²)` for `|x| ≤ 1`,  `h(x) = |x|⁻¹ F(x⁻²)` for `|x| > 1`,

so that `h(1/x) = |x| h(x)`.  With `ν_k = 2k + ½` the log-scale profile is
`e^{v/2} h(e^v) = ∑ c_k e^{-ν_k |v|}` and its cosine transform is

  `∫ cos(τv) e^{v/2} h(e^v) dv = ∑ c_k · 2ν_k / (ν_k² + τ²)
                               = (2 / cosh πτ) ∫_0^π cosh(τθ) K(θ) dθ`,

where `K(θ) = ∑ c_k cos(ν_k θ) = Re(e^{iθ/2} F(e^{2iθ}))` is the rotated boundary value of `F` on the
unit circle.  The second equality is the elementary integral
`∫_0^π cosh(τθ) cos(νθ) dθ = ν cosh(πτ) / (ν² + τ²)`, valid because `cos(νπ) = 0` and `sin(νπ) = 1`
for every `ν ∈ ½ + 2ℕ`.

Consequently the profile is strictly positive definite as soon as `K ≥ 0` on `[0, π]` and `K` is
positive somewhere (`integral_cos_mul_selfRecProfile_pos`).

## Main results

* `integral_cos_mul_selfRecProfile`: the cosine transform as a sum of Lorentzians.
* `integral_cosh_mul_selfRecDensity`: the hyperbolic-cosine transform of the boundary density.
* `integral_cos_mul_selfRecProfile_eq_density`: the spectral density law.
* `integral_cos_mul_selfRecProfile_pos`: strict positive definiteness from `K ≥ 0`.
* `exp_half_mul_selfRecLine`, `selfRecLine_inv`, `selfRecLine_neg`: the profile is the log-scale
  profile of the even self-reciprocal function `h`.
* `selfRecDensity_eq_re`: `K(θ) = Re(e^{iθ/2} F(e^{2iθ}))`.
-/

open MeasureTheory Set Filter

namespace RHTower

noncomputable section

/-- The exponents `ν_k = 2k + ½`. -/
def selfRecExponent (k : ℕ) : ℝ := 2 * k + 1 / 2

lemma one_half_le_selfRecExponent (k : ℕ) : 1 / 2 ≤ selfRecExponent k := by
  unfold selfRecExponent
  have : (0 : ℝ) ≤ k := k.cast_nonneg
  linarith

lemma selfRecExponent_pos (k : ℕ) : 0 < selfRecExponent k :=
  lt_of_lt_of_le (by norm_num) (one_half_le_selfRecExponent k)

/-- The log-scale profile `P(v) = ∑ c_k e^{-ν_k |v|}`. -/
def selfRecProfile (c : ℕ → ℝ) (v : ℝ) : ℝ :=
  ∑' k, c k * Real.exp (-(selfRecExponent k * |v|))

/-- The boundary density `K(θ) = ∑ c_k cos(ν_k θ)`. -/
def selfRecDensity (c : ℕ → ℝ) (θ : ℝ) : ℝ :=
  ∑' k, c k * Real.cos (selfRecExponent k * θ)

/-- The power series `F(t) = ∑ c_k t^k`. -/
def selfRecSeries (c : ℕ → ℝ) (t : ℝ) : ℝ := ∑' k, c k * t ^ k

/-- The even self-reciprocal function `h(x) = F(x²)` for `|x| ≤ 1`, `h(x) = |x|⁻¹F(x⁻²)` otherwise. -/
def selfRecLine (c : ℕ → ℝ) (x : ℝ) : ℝ :=
  if |x| ≤ 1 then selfRecSeries c (x ^ 2) else |x|⁻¹ * selfRecSeries c ((x ^ 2)⁻¹)

/-! ### The Lorentzian form of the cosine transform -/

lemma integrable_exp_neg_mul_abs_of_pos {ν : ℝ} (hν : 0 < ν) :
    Integrable fun v : ℝ => Real.exp (-(ν * |v|)) := by
  refine (_root_.HTGeometry.integrable_abs_pow_mul_exp_neg_abs 0 hν).congr
    (Eventually.of_forall fun v => ?_)
  simp [neg_mul]

/-- `∫ cos(τv) e^{-ν|v|} dv = 2ν / (ν² + τ²)`. -/
theorem integral_cos_mul_exp_neg_mul_abs_eq {ν : ℝ} (hν : 0 < ν) (τ : ℝ) :
    ∫ v : ℝ, Real.cos (τ * v) * Real.exp (-(ν * |v|)) = 2 * ν / (ν ^ 2 + τ ^ 2) := by
  have h1 : (fun v : ℝ => Real.cos (τ * v) * Real.exp (-(ν * |v|))) =
      fun v => (fun u => Real.exp (-(ν * u)) * Real.cos (τ * u)) |v| := by
    funext v
    show Real.cos (τ * v) * Real.exp (-(ν * |v|)) = Real.exp (-(ν * |v|)) * Real.cos (τ * |v|)
    rcases abs_choice v with h | h
    · rw [h, mul_comm]
    · rw [h, mul_neg τ v, Real.cos_neg, mul_comm]
  rw [h1, integral_comp_abs (f := fun u => Real.exp (-(ν * u)) * Real.cos (τ * u)),
    integral_Ioi_exp_neg_mul_cos hν]
  ring

/-- The cosine transform of the profile is a sum of Lorentzians:
`∫ cos(τv) P(v) dv = ∑ c_k · 2ν_k/(ν_k² + τ²)`. -/
theorem integral_cos_mul_selfRecProfile {c : ℕ → ℝ} (hc : Summable fun k => |c k|) (τ : ℝ) :
    ∫ v : ℝ, Real.cos (τ * v) * selfRecProfile c v =
      ∑' k, c k * (2 * selfRecExponent k / (selfRecExponent k ^ 2 + τ ^ 2)) := by
  set G : ℕ → ℝ → ℝ := fun k v =>
    c k * (Real.cos (τ * v) * Real.exp (-(selfRecExponent k * |v|))) with hG
  have hle : ∀ k v, ‖G k v‖ ≤ |c k| * Real.exp (-(selfRecExponent k * |v|)) := by
    intro k v
    rw [hG, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    gcongr
    calc |Real.cos (τ * v)| * Real.exp (-(selfRecExponent k * |v|))
        ≤ 1 * Real.exp (-(selfRecExponent k * |v|)) := by
          gcongr; exact Real.abs_cos_le_one _
      _ = _ := one_mul _
  have hexp : ∀ k, Integrable fun v : ℝ => |c k| * Real.exp (-(selfRecExponent k * |v|)) :=
    fun k => (integrable_exp_neg_mul_abs_of_pos (selfRecExponent_pos k)).const_mul |c k|
  have hint : ∀ k, Integrable (G k) := fun k =>
    (hexp k).mono' (by rw [hG]; fun_prop) (Eventually.of_forall (hle k))
  have hnorm : ∀ k, ∫ v, ‖G k v‖ ≤ 4 * |c k| := by
    intro k
    calc ∫ v, ‖G k v‖ ≤ ∫ v, |c k| * Real.exp (-(selfRecExponent k * |v|)) :=
          integral_mono (hint k).norm (hexp k) (hle k)
      _ = |c k| * (2 / selfRecExponent k) := by
          rw [integral_const_mul]
          congr 1
          have h := _root_.HTGeometry.integral_abs_evenPow_mul_exp_neg_abs 0
            (selfRecExponent_pos k)
          simp only [mul_zero, pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, zero_add,
            pow_one, neg_mul, mul_one] at h
          exact h
      _ ≤ |c k| * 4 := by
          gcongr
          rw [div_le_iff₀ (selfRecExponent_pos k)]
          linarith [one_half_le_selfRecExponent k]
      _ = 4 * |c k| := mul_comm _ _
  have hsum : Summable fun k => ∫ v, ‖G k v‖ :=
    Summable.of_nonneg_of_le (fun k => integral_nonneg fun v => norm_nonneg _) hnorm
      (hc.mul_left 4)
  have hrewrite : (fun v : ℝ => Real.cos (τ * v) * selfRecProfile c v) = fun v => ∑' k, G k v := by
    funext v
    rw [selfRecProfile, ← tsum_mul_left]
    congr 1
    funext k
    rw [hG]
    ring
  rw [hrewrite, ← integral_tsum_of_summable_integral_norm hint hsum]
  congr 1
  funext k
  rw [hG, integral_const_mul, integral_cos_mul_exp_neg_mul_abs_eq (selfRecExponent_pos k)]

/-! ### The hyperbolic-cosine transform of the boundary density -/

lemma cos_selfRecExponent_mul_pi (k : ℕ) : Real.cos (selfRecExponent k * Real.pi) = 0 := by
  have h : selfRecExponent k * Real.pi = Real.pi / 2 + k * (2 * Real.pi) := by
    unfold selfRecExponent; ring
  rw [h, Real.cos_add_nat_mul_two_pi, Real.cos_pi_div_two]

lemma sin_selfRecExponent_mul_pi (k : ℕ) : Real.sin (selfRecExponent k * Real.pi) = 1 := by
  have h : selfRecExponent k * Real.pi = Real.pi / 2 + k * (2 * Real.pi) := by
    unfold selfRecExponent; ring
  rw [h, Real.sin_add_nat_mul_two_pi, Real.sin_pi_div_two]

/-- `∫_0^π cosh(τθ) cos(ν_k θ) dθ = ν_k cosh(πτ) / (ν_k² + τ²)`. -/
theorem integral_cosh_mul_cos_selfRecExponent (k : ℕ) (τ : ℝ) :
    ∫ θ in (0 : ℝ)..Real.pi, Real.cosh (τ * θ) * Real.cos (selfRecExponent k * θ) =
      selfRecExponent k * Real.cosh (Real.pi * τ) / (selfRecExponent k ^ 2 + τ ^ 2) := by
  set ν := selfRecExponent k with hν
  have hden : 0 < ν ^ 2 + τ ^ 2 := by
    have := selfRecExponent_pos k
    positivity
  set A : ℝ → ℝ := fun θ =>
    (τ * Real.sinh (τ * θ) * Real.cos (ν * θ) + ν * Real.cosh (τ * θ) * Real.sin (ν * θ)) /
      (ν ^ 2 + τ ^ 2) with hA
  have hderiv : ∀ θ ∈ uIcc (0 : ℝ) Real.pi,
      HasDerivAt A (Real.cosh (τ * θ) * Real.cos (ν * θ)) θ := by
    intro θ _
    have hs : HasDerivAt (fun θ => Real.sinh (τ * θ)) (Real.cosh (τ * θ) * τ) θ :=
      (Real.hasDerivAt_sinh _).comp θ ((hasDerivAt_id θ).const_mul τ |>.congr_deriv (by simp))
    have hc : HasDerivAt (fun θ => Real.cosh (τ * θ)) (Real.sinh (τ * θ) * τ) θ :=
      (Real.hasDerivAt_cosh _).comp θ ((hasDerivAt_id θ).const_mul τ |>.congr_deriv (by simp))
    have hcos : HasDerivAt (fun θ => Real.cos (ν * θ)) (-Real.sin (ν * θ) * ν) θ :=
      (Real.hasDerivAt_cos _).comp θ ((hasDerivAt_id θ).const_mul ν |>.congr_deriv (by simp))
    have hsin : HasDerivAt (fun θ => Real.sin (ν * θ)) (Real.cos (ν * θ) * ν) θ :=
      (Real.hasDerivAt_sin _).comp θ ((hasDerivAt_id θ).const_mul ν |>.congr_deriv (by simp))
    have h := ((((hs.const_mul τ).mul hcos).add ((hc.const_mul ν).mul hsin)).div_const
      (ν ^ 2 + τ ^ 2))
    refine h.congr_deriv ?_
    field_simp
    ring
  have hcont : Continuous fun θ : ℝ => Real.cosh (τ * θ) * Real.cos (ν * θ) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _), hA]
  simp only [mul_zero, Real.sinh_zero, Real.sin_zero, Real.cosh_zero, Real.cos_zero]
  rw [hν, cos_selfRecExponent_mul_pi, sin_selfRecExponent_mul_pi]
  ring_nf

lemma abs_selfRecDensity_term_le (c : ℕ → ℝ) (k : ℕ) (θ : ℝ) :
    ‖c k * Real.cos (selfRecExponent k * θ)‖ ≤ |c k| := by
  rw [Real.norm_eq_abs, abs_mul]
  calc |c k| * |Real.cos (selfRecExponent k * θ)| ≤ |c k| * 1 := by
        gcongr; exact Real.abs_cos_le_one _
    _ = |c k| := mul_one _

theorem continuous_selfRecDensity {c : ℕ → ℝ} (hc : Summable fun k => |c k|) :
    Continuous (selfRecDensity c) :=
  continuous_tsum (fun k => by fun_prop) hc (abs_selfRecDensity_term_le c)

/-- `∫_0^π cosh(τθ) K(θ) dθ = cosh(πτ) ∑ c_k ν_k/(ν_k² + τ²)`. -/
theorem integral_cosh_mul_selfRecDensity {c : ℕ → ℝ} (hc : Summable fun k => |c k|) (τ : ℝ) :
    ∫ θ in (0 : ℝ)..Real.pi, Real.cosh (τ * θ) * selfRecDensity c θ =
      Real.cosh (Real.pi * τ) *
        ∑' k, c k * (selfRecExponent k / (selfRecExponent k ^ 2 + τ ^ 2)) := by
  set G : ℕ → ℝ → ℝ := fun k θ => Real.cosh (τ * θ) * (c k * Real.cos (selfRecExponent k * θ))
    with hG
  have hbound : ∀ k, ∀ᵐ θ ∂(volume : Measure ℝ), θ ∈ uIoc (0 : ℝ) Real.pi →
      ‖G k θ‖ ≤ Real.cosh (Real.pi * τ) * |c k| := by
    intro k
    refine Eventually.of_forall fun θ hθ => ?_
    rw [uIoc_of_le Real.pi_pos.le] at hθ
    rw [hG, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.cosh_pos _)]
    have hch : Real.cosh (τ * θ) ≤ Real.cosh (Real.pi * τ) := by
      rw [Real.cosh_le_cosh, abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hθ.1, mul_comm]
      gcongr
      exact hθ.2
    exact mul_le_mul hch (abs_selfRecDensity_term_le c k θ) (norm_nonneg _)
      (Real.cosh_pos _).le
  have hsumG : ∀ θ, HasSum (fun k => G k θ) (Real.cosh (τ * θ) * selfRecDensity c θ) := by
    intro θ
    have hs : Summable fun k => c k * Real.cos (selfRecExponent k * θ) :=
      hc.of_norm_bounded (abs_selfRecDensity_term_le c · θ)
    exact hs.hasSum.mul_left _
  have h := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (a := 0) (b := Real.pi)
    (fun k _ => Real.cosh (Real.pi * τ) * |c k|)
    (fun k => (by fun_prop : Continuous (G k)).aestronglyMeasurable) hbound
    (Eventually.of_forall fun _ _ => hc.mul_left _)
    intervalIntegrable_const
    (Eventually.of_forall fun θ _ => hsumG θ)
  rw [← h.tsum_eq, ← tsum_mul_left]
  congr 1
  funext k
  rw [hG]
  simp_rw [show ∀ θ, Real.cosh (τ * θ) * (c k * Real.cos (selfRecExponent k * θ)) =
      c k * (Real.cosh (τ * θ) * Real.cos (selfRecExponent k * θ)) from fun θ => by ring]
  rw [intervalIntegral.integral_const_mul, integral_cosh_mul_cos_selfRecExponent]
  ring

/-! ### The spectral density law and positivity -/

/-- **Spectral density law.** The cosine transform of the self-reciprocal profile is the
hyperbolic-cosine transform of the boundary density:
`∫ cos(τv) P(v) dv = (2 / cosh πτ) ∫_0^π cosh(τθ) K(θ) dθ`. -/
theorem integral_cos_mul_selfRecProfile_eq_density {c : ℕ → ℝ} (hc : Summable fun k => |c k|)
    (τ : ℝ) :
    ∫ v : ℝ, Real.cos (τ * v) * selfRecProfile c v =
      2 / Real.cosh (Real.pi * τ) *
        ∫ θ in (0 : ℝ)..Real.pi, Real.cosh (τ * θ) * selfRecDensity c θ := by
  rw [integral_cos_mul_selfRecProfile hc, integral_cosh_mul_selfRecDensity hc, ← mul_assoc,
    div_mul_cancel₀ _ (Real.cosh_pos _).ne', ← tsum_mul_left]
  congr 1
  funext k
  ring

/-- **Positivity from the boundary density.** If `K ≥ 0` on `[0, π]` and `K` is positive at some
point of `[0, π]`, the self-reciprocal profile is strictly positive definite. -/
theorem integral_cos_mul_selfRecProfile_pos {c : ℕ → ℝ} (hc : Summable fun k => |c k|)
    (hK : ∀ θ ∈ Icc (0 : ℝ) Real.pi, 0 ≤ selfRecDensity c θ)
    (hpos : ∃ θ ∈ Icc (0 : ℝ) Real.pi, 0 < selfRecDensity c θ) (τ : ℝ) :
    0 < ∫ v : ℝ, Real.cos (τ * v) * selfRecProfile c v := by
  rw [integral_cos_mul_selfRecProfile_eq_density hc]
  have hcont : Continuous fun θ => Real.cosh (τ * θ) * selfRecDensity c θ :=
    (by fun_prop : Continuous fun θ : ℝ => Real.cosh (τ * θ)).mul (continuous_selfRecDensity hc)
  have hint : 0 < ∫ θ in (0 : ℝ)..Real.pi, Real.cosh (τ * θ) * selfRecDensity c θ := by
    refine intervalIntegral.integral_pos Real.pi_pos hcont.continuousOn
      (fun θ hθ => mul_nonneg (Real.cosh_pos _).le (hK θ (Ioc_subset_Icc_self hθ))) ?_
    obtain ⟨θ, hθ, hθpos⟩ := hpos
    exact ⟨θ, hθ, mul_pos (Real.cosh_pos _) hθpos⟩
  exact mul_pos (div_pos two_pos (Real.cosh_pos _)) hint

/-! ### The profile of the self-reciprocal line function -/

lemma selfRecSeries_sq_exp (c : ℕ → ℝ) (u : ℝ) :
    selfRecSeries c (Real.exp u ^ 2) = ∑' k, c k * Real.exp (2 * k * u) := by
  unfold selfRecSeries
  congr 1
  funext k
  rw [← pow_mul, ← Real.exp_nat_mul]
  push_cast
  ring_nf

/-- The log-scale profile of `h` is `P`: `e^{v/2} h(e^v) = ∑ c_k e^{-ν_k|v|}`. -/
theorem exp_half_mul_selfRecLine (c : ℕ → ℝ) (v : ℝ) :
    Real.exp (v / 2) * selfRecLine c (Real.exp v) = selfRecProfile c v := by
  unfold selfRecLine selfRecProfile
  rw [abs_of_pos (Real.exp_pos v)]
  by_cases hv : v ≤ 0
  · rw [if_pos (Real.exp_le_one_iff.mpr hv), selfRecSeries_sq_exp, ← tsum_mul_left]
    congr 1
    funext k
    rw [abs_of_nonpos hv, mul_left_comm, ← Real.exp_add]
    congr 2
    unfold selfRecExponent
    ring
  · rw [not_le] at hv
    rw [if_neg (not_le.mpr (Real.one_lt_exp_iff.mpr hv)), ← Real.exp_neg,
      show (Real.exp v ^ 2)⁻¹ = Real.exp (-v) ^ 2 by rw [Real.exp_neg, inv_pow],
      selfRecSeries_sq_exp, ← mul_assoc, ← Real.exp_add, ← tsum_mul_left]
    congr 1
    funext k
    rw [abs_of_pos hv, mul_left_comm, ← Real.exp_add]
    congr 2
    unfold selfRecExponent
    ring

theorem selfRecLine_neg (c : ℕ → ℝ) (x : ℝ) : selfRecLine c (-x) = selfRecLine c x := by
  simp [selfRecLine, abs_neg]

/-- Self-reciprocity: `h(1/x) = |x| h(x)`. -/
theorem selfRecLine_inv (c : ℕ → ℝ) {x : ℝ} (hx : x ≠ 0) :
    selfRecLine c x⁻¹ = |x| * selfRecLine c x := by
  have hax : 0 < |x| := abs_pos.mpr hx
  unfold selfRecLine
  rw [abs_inv, inv_pow, inv_inv]
  rcases lt_trichotomy |x| 1 with h | h | h
  · rw [if_neg (not_le.mpr ((one_lt_inv₀ hax).mpr h)), if_pos h.le, inv_inv]
  · rw [h, inv_one, if_pos le_rfl, if_pos le_rfl, one_mul]
    have hx2 : x ^ 2 = 1 := by rw [← sq_abs, h, one_pow]
    rw [hx2, inv_one]
  · rw [if_pos (inv_le_one_of_one_le₀ h.le), if_neg (not_le.mpr h), ← mul_assoc,
      mul_inv_cancel₀ hax.ne', one_mul]

/-- The boundary density is the rotated boundary value of `F` on the unit circle:
`K(θ) = Re(e^{iθ/2} F(e^{2iθ}))`. -/
theorem selfRecDensity_eq_re {c : ℕ → ℝ} (hc : Summable fun k => |c k|) (θ : ℝ) :
    selfRecDensity c θ =
      (Complex.exp ((θ / 2 : ℝ) * Complex.I) *
        ∑' k, (c k : ℂ) * Complex.exp ((2 * θ : ℝ) * Complex.I) ^ k).re := by
  have hterm : ∀ k : ℕ, Complex.exp ((θ / 2 : ℝ) * Complex.I) *
      ((c k : ℂ) * Complex.exp ((2 * θ : ℝ) * Complex.I) ^ k) =
        (c k : ℂ) * Complex.exp ((selfRecExponent k * θ : ℝ) * Complex.I) := by
    intro k
    rw [← Complex.exp_nat_mul, mul_left_comm, ← Complex.exp_add]
    congr 2
    unfold selfRecExponent
    push_cast
    ring
  have hs : Summable fun k : ℕ =>
      (c k : ℂ) * Complex.exp ((selfRecExponent k * θ : ℝ) * Complex.I) := by
    refine hc.of_norm_bounded fun k => ?_
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [← tsum_mul_left]
  simp_rw [hterm]
  rw [Complex.re_tsum hs, selfRecDensity]
  congr 1
  funext k
  rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

end

end RHTower
