import GaloisForLFunctions.HTGeometry.HamburgerSquareSummable

/-!
# Hamburger's residue at `0` with logarithmic terms

Suppose the theta series `θ_a(x) = Σ a_n e^{−πn²x}` (`Σ ‖a_n‖/n² < ∞`) obeys an odd transformation
law with logarithmic correction terms,

`θ_a(x) = −x^{−1/2} θ_a(1/x) + P(log x) + x^{−1/2} Q(log x)`,  `P, Q` of degree `≤ 2`.

**Theorem** (`quadratic_log_coeffs_eq_zero_of_odd_coeffTheta_relation`). The coefficients of
`log x` and `log² x` in `P` vanish.

This is the residue step of Hamburger's theorem at `t = 0`, run with logarithms.
* **Laplace step.** Multiply by `e^{−πt²x}` and integrate. With `u = πt²x` and
  `E_{r,j} = ∫_0^∞ u^r log^j u e^{−u} du`, this gives
  `L_a(t) = −Σ a_n e^{−2πnt} + P̂(log πt²)/(πt) + Q̂(log πt²)/√π` for real `t > 0`, where
  `P̂(z) = p₀ + p₁(E_{0,1} − z) + p₂(E_{0,2} − 2E_{0,1} z + z²)` (`hamburgerSeries_eq_log_ofReal`).
* **Continuation.** Both sides are holomorphic on `Re t > 0` (principal logarithm), so the identity
  holds there.
* **Residue.** The dual series is `i`-periodic. As `t → 0⁺`, `t L_a(t + i) → a₁/(2π)` and
  `t L_a(t) → 0`, while `t Q̂(log πt²) → 0`. Hence `P̂(log π + 2 log t)` converges. A quadratic with
  a finite limit at `−∞` is constant, so `p₂ = 0` and then `p₁ = 0`.
-/

open Complex MeasureTheory Filter Topology Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## Logarithmic moments of the exponential -/

theorem abs_log_le_rpow_add {u : ℝ} (hu : 0 < u) :
    |Real.log u| ≤ 8 * u ^ (-(1 / 8 : ℝ)) + u := by
  rcases le_or_gt u 1 with h1 | h1
  · have hlog : Real.log u ≤ 0 := Real.log_nonpos hu.le h1
    rw [abs_of_nonpos hlog]
    have h := Real.log_le_rpow_div (x := u⁻¹) (inv_pos.mpr hu).le (by norm_num : (0 : ℝ) < 1 / 8)
    rw [Real.log_inv, Real.inv_rpow hu.le, ← Real.rpow_neg hu.le] at h
    have e : u ^ (-(1 / 8 : ℝ)) / (1 / 8) = 8 * u ^ (-(1 / 8 : ℝ)) := by ring
    have : 0 ≤ u := hu.le
    linarith
  · have hlog : 0 ≤ Real.log u := Real.log_nonneg h1.le
    rw [abs_of_nonneg hlog]
    have := Real.log_le_sub_one_of_pos hu
    have : 0 ≤ 8 * u ^ (-(1 / 8 : ℝ)) := by positivity
    linarith

theorem integrableOn_rpow_mul_exp_neg_mul' {s b : ℝ} (hs : -1 < s) (hb : 0 < b) :
    IntegrableOn (fun u : ℝ => u ^ s * Real.exp (-(b * u))) (Ioi 0) := by
  refine (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) hs le_rfl hb).congr_fun
    (fun u _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_one, neg_mul]

theorem abs_log_pow_le {u : ℝ} (hu : 0 < u) {j : ℕ} (hj : j ≤ 2) :
    |Real.log u| ^ j ≤ 1 + 128 * u ^ (-(1 / 4 : ℝ)) + 2 * u ^ (2 : ℝ) := by
  have hb := abs_log_le_rpow_add hu
  have h0 : 0 ≤ |Real.log u| := abs_nonneg _
  have hsq : |Real.log u| ^ 2 ≤ 128 * u ^ (-(1 / 4 : ℝ)) + 2 * u ^ (2 : ℝ) := by
    have e1 : (u ^ (-(1 / 8 : ℝ))) ^ 2 = u ^ (-(1 / 4 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hu.le]; norm_num
    have e2 : u ^ (2 : ℝ) = u ^ 2 := by norm_cast
    have hA : 0 ≤ u ^ (-(1 / 8 : ℝ)) := by positivity
    calc |Real.log u| ^ 2 ≤ (8 * u ^ (-(1 / 8 : ℝ)) + u) ^ 2 := pow_le_pow_left₀ h0 hb 2
      _ ≤ 2 * (8 * u ^ (-(1 / 8 : ℝ))) ^ 2 + 2 * u ^ 2 := by
          nlinarith [sq_nonneg (8 * u ^ (-(1 / 8 : ℝ)) - u)]
      _ = 128 * u ^ (-(1 / 4 : ℝ)) + 2 * u ^ (2 : ℝ) := by rw [mul_pow, e1, e2]; ring
  have hpos : 0 ≤ 128 * u ^ (-(1 / 4 : ℝ)) + 2 * u ^ (2 : ℝ) := by positivity
  interval_cases j
  · rw [pow_zero]; linarith
  · simp only [pow_one]; nlinarith [sq_nonneg (|Real.log u| - 1)]
  · linarith

/-- `u^r log^j u e^{−bu}` is integrable on `(0, ∞)` for `r > −3/4`, `j ≤ 2` and `b > 0`. -/
theorem integrableOn_rpow_mul_log_pow_mul_exp_neg_mul {r : ℝ} (hr : -3 / 4 < r) {j : ℕ} (hj : j ≤ 2)
    {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun u : ℝ => u ^ r * Real.log u ^ j * Real.exp (-(b * u))) (Ioi 0) := by
  have h1 := integrableOn_rpow_mul_exp_neg_mul' (s := r - 1 / 4) (by linarith) hb
  have h2 := integrableOn_rpow_mul_exp_neg_mul' (s := r + 2) (by linarith) hb
  have h3 := integrableOn_rpow_mul_exp_neg_mul' (s := r) (by linarith) hb
  refine (h3.add ((h1.const_mul 128).add (h2.const_mul 2))).mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable (fun u hu => ?_) measurableSet_Ioi
    have hu0 : (0 : ℝ) < u := hu
    refine ContinuousAt.continuousWithinAt ?_
    exact ((Real.continuousAt_rpow_const _ _ (Or.inl hu0.ne')).mul
      ((Real.continuousAt_log hu0.ne').pow j)).mul (by fun_prop)
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
    have hu0 : (0 : ℝ) < u := hu
    have hbd := abs_log_pow_le hu0 hj
    have hr0 : 0 < u ^ r := Real.rpow_pos_of_pos hu0 r
    have he : 0 < Real.exp (-(b * u)) := Real.exp_pos _
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hr0, abs_of_pos he, abs_pow]
    have e1 : u ^ r * u ^ (-(1 / 4 : ℝ)) = u ^ (r - 1 / 4) := by
      rw [← Real.rpow_add hu0]; ring_nf
    have e2 : u ^ r * u ^ (2 : ℝ) = u ^ (r + 2) := by rw [← Real.rpow_add hu0]
    calc u ^ r * |Real.log u| ^ j * Real.exp (-(b * u))
        ≤ u ^ r * (1 + 128 * u ^ (-(1 / 4 : ℝ)) + 2 * u ^ (2 : ℝ)) * Real.exp (-(b * u)) := by
          gcongr
      _ = u ^ r * Real.exp (-(b * u)) + (128 * (u ^ (r - 1 / 4) * Real.exp (-(b * u))) +
            2 * (u ^ (r + 2) * Real.exp (-(b * u)))) := by
          rw [← e1, ← e2]; ring

theorem integrableOn_rpow_mul_log_pow_mul_exp_neg {r : ℝ} (hr : -3 / 4 < r) {j : ℕ} (hj : j ≤ 2) :
    IntegrableOn (fun u : ℝ => u ^ r * Real.log u ^ j * Real.exp (-u)) (Ioi 0) := by
  refine (integrableOn_rpow_mul_log_pow_mul_exp_neg_mul hr hj one_pos).congr_fun
    (fun u _ => ?_) measurableSet_Ioi
  simp only [one_mul]

/-- `E_{r,j} = ∫_0^∞ u^r log^j u e^{−u} du`. -/
def logExpMoment (r : ℝ) (j : ℕ) : ℝ := ∫ u in Ioi (0 : ℝ), u ^ r * Real.log u ^ j * Real.exp (-u)

/-- **Scaling.** `∫_0^∞ x^r log^j x e^{−bx} dx = b^{−1−r} ∫_0^∞ u^r (log u − log b)^j e^{−u} du`. -/
theorem integral_rpow_mul_log_pow_mul_exp_neg_mul (r : ℝ) (j : ℕ) {b : ℝ} (hb : 0 < b) :
    ∫ x in Ioi (0 : ℝ), x ^ r * Real.log x ^ j * Real.exp (-(b * x)) =
      b⁻¹ * b ^ (-r) * ∫ u in Ioi (0 : ℝ), u ^ r * (Real.log u - Real.log b) ^ j * Real.exp (-u) := by
  set g : ℝ → ℝ := fun u => (u / b) ^ r * (Real.log u - Real.log b) ^ j * Real.exp (-u) with hg
  have hcomp := integral_comp_mul_left_Ioi g 0 hb
  rw [mul_zero, smul_eq_mul] at hcomp
  have hleft : ∫ x in Ioi (0 : ℝ), g (b * x) =
      ∫ x in Ioi (0 : ℝ), x ^ r * Real.log x ^ j * Real.exp (-(b * x)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : (0 : ℝ) < x := hx
    simp only [hg]
    rw [mul_div_cancel_left₀ _ hb.ne', Real.log_mul hb.ne' hx0.ne']
    ring_nf
  have hright : ∫ x in Ioi (0 : ℝ), g x =
      b ^ (-r) * ∫ u in Ioi (0 : ℝ), u ^ r * (Real.log u - Real.log b) ^ j * Real.exp (-u) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu0 : (0 : ℝ) < u := hu
    simp only [hg]
    rw [Real.div_rpow hu0.le hb.le, Real.rpow_neg hb.le]
    ring
  rw [← hleft, hcomp, hright]
  ring

/-- The Laplace transform of `x^r log^j x`, `j ≤ 2`, in terms of the moments `E_{r,i}`. -/
theorem integral_rpow_mul_log_pow_mul_exp_neg_mul_eq {r : ℝ} (hr : -3 / 4 < r) {b : ℝ} (hb : 0 < b) :
    (∫ x in Ioi (0 : ℝ), x ^ r * Real.log x ^ 0 * Real.exp (-(b * x))) =
        b⁻¹ * b ^ (-r) * logExpMoment r 0 ∧
      (∫ x in Ioi (0 : ℝ), x ^ r * Real.log x ^ 1 * Real.exp (-(b * x))) =
        b⁻¹ * b ^ (-r) * (logExpMoment r 1 - Real.log b * logExpMoment r 0) ∧
      (∫ x in Ioi (0 : ℝ), x ^ r * Real.log x ^ 2 * Real.exp (-(b * x))) =
        b⁻¹ * b ^ (-r) * (logExpMoment r 2 - 2 * Real.log b * logExpMoment r 1 +
          Real.log b ^ 2 * logExpMoment r 0) := by
  have i0 := integrableOn_rpow_mul_log_pow_mul_exp_neg hr (j := 0) (by norm_num)
  have i1 := integrableOn_rpow_mul_log_pow_mul_exp_neg hr (j := 1) (by norm_num)
  have i2 := integrableOn_rpow_mul_log_pow_mul_exp_neg hr (j := 2) (by norm_num)
  set L := Real.log b
  refine ⟨?_, ?_, ?_⟩
  · rw [integral_rpow_mul_log_pow_mul_exp_neg_mul r 0 hb]
    simp only [pow_zero, logExpMoment]
  · rw [integral_rpow_mul_log_pow_mul_exp_neg_mul r 1 hb]
    congr 1
    have e : (fun u : ℝ => u ^ r * (Real.log u - L) ^ 1 * Real.exp (-u)) =
        fun u => u ^ r * Real.log u ^ 1 * Real.exp (-u) - L * (u ^ r * Real.log u ^ 0 * Real.exp (-u)) := by
      funext u; ring
    have i0' : IntegrableOn (fun u : ℝ => L * (u ^ r * Real.log u ^ 0 * Real.exp (-u))) (Ioi 0) :=
      i0.const_mul L
    rw [e, integral_sub i1 i0', integral_const_mul]
    rfl
  · rw [integral_rpow_mul_log_pow_mul_exp_neg_mul r 2 hb]
    congr 1
    have e : (fun u : ℝ => u ^ r * (Real.log u - L) ^ 2 * Real.exp (-u)) =
        fun u => u ^ r * Real.log u ^ 2 * Real.exp (-u) -
          2 * L * (u ^ r * Real.log u ^ 1 * Real.exp (-u)) +
          L ^ 2 * (u ^ r * Real.log u ^ 0 * Real.exp (-u)) := by
      funext u; ring
    have i1' : IntegrableOn (fun u : ℝ => 2 * L * (u ^ r * Real.log u ^ 1 * Real.exp (-u))) (Ioi 0) :=
      i1.const_mul _
    have i0' : IntegrableOn (fun u : ℝ => L ^ 2 * (u ^ r * Real.log u ^ 0 * Real.exp (-u))) (Ioi 0) :=
      i0.const_mul _
    have i21 : IntegrableOn (fun u : ℝ => u ^ r * Real.log u ^ 2 * Real.exp (-u) -
        2 * L * (u ^ r * Real.log u ^ 1 * Real.exp (-u))) (Ioi 0) := i2.sub i1'
    rw [e, integral_add i21 i0', integral_sub i2 i1', integral_const_mul, integral_const_mul]
    rfl

/-! ## Laplace transforms of logarithmic polynomials -/

/-- `P(z) = p₀ + p₁ z + p₂ z²`. -/
def logQuadPoly (p₀ p₁ p₂ z : ℂ) : ℂ := p₀ + p₁ * z + p₂ * z ^ 2

/-- `P̂_r(z) = p₀ E_{r,0} + p₁ (E_{r,1} − z E_{r,0}) + p₂ (E_{r,2} − 2z E_{r,1} + z² E_{r,0})`: the
Laplace image of `x^r P(log x)` at `z = log b`. -/
def logLaplacePoly (r : ℝ) (p₀ p₁ p₂ z : ℂ) : ℂ :=
  p₀ * logExpMoment r 0 + p₁ * (logExpMoment r 1 - z * logExpMoment r 0) +
    p₂ * (logExpMoment r 2 - 2 * z * logExpMoment r 1 + z ^ 2 * logExpMoment r 0)

theorem logQuadPoly_log_mul_eq (r b : ℝ) (p₀ p₁ p₂ : ℂ) (x : ℝ) :
    ((x ^ r * Real.exp (-(b * x)) : ℝ) : ℂ) * logQuadPoly p₀ p₁ p₂ (Real.log x) =
      p₀ * ((x ^ r * Real.log x ^ 0 * Real.exp (-(b * x)) : ℝ) : ℂ) +
        p₁ * ((x ^ r * Real.log x ^ 1 * Real.exp (-(b * x)) : ℝ) : ℂ) +
        p₂ * ((x ^ r * Real.log x ^ 2 * Real.exp (-(b * x)) : ℝ) : ℂ) := by
  unfold logQuadPoly; push_cast; ring

theorem integrableOn_logQuadPoly_log_mul_exp {r : ℝ} (hr : -3 / 4 < r) {b : ℝ} (hb : 0 < b)
    (p₀ p₁ p₂ : ℂ) :
    IntegrableOn (fun x : ℝ => ((x ^ r * Real.exp (-(b * x)) : ℝ) : ℂ) *
      logQuadPoly p₀ p₁ p₂ (Real.log x)) (Ioi 0) := by
  have i0 := ((integrableOn_rpow_mul_log_pow_mul_exp_neg_mul hr (j := 0) (by norm_num) hb).ofReal
    (𝕜 := ℂ)).const_mul p₀
  have i1 := ((integrableOn_rpow_mul_log_pow_mul_exp_neg_mul hr (j := 1) (by norm_num) hb).ofReal
    (𝕜 := ℂ)).const_mul p₁
  have i2 := ((integrableOn_rpow_mul_log_pow_mul_exp_neg_mul hr (j := 2) (by norm_num) hb).ofReal
    (𝕜 := ℂ)).const_mul p₂
  have hs : IntegrableOn (fun x : ℝ => p₀ * ((x ^ r * Real.log x ^ 0 * Real.exp (-(b * x)) : ℝ) : ℂ) +
      p₁ * ((x ^ r * Real.log x ^ 1 * Real.exp (-(b * x)) : ℝ) : ℂ) +
      p₂ * ((x ^ r * Real.log x ^ 2 * Real.exp (-(b * x)) : ℝ) : ℂ)) (Ioi 0) := (i0.add i1).add i2
  exact hs.congr_fun (fun x _ => (logQuadPoly_log_mul_eq r b p₀ p₁ p₂ x).symm) measurableSet_Ioi

/-- `∫_0^∞ x^r e^{−bx} P(log x) dx = b^{−1−r} P̂_r(log b)`. -/
theorem integral_logQuadPoly_log_mul_exp {r : ℝ} (hr : -3 / 4 < r) {b : ℝ} (hb : 0 < b)
    (p₀ p₁ p₂ : ℂ) :
    ∫ x in Ioi (0 : ℝ), ((x ^ r * Real.exp (-(b * x)) : ℝ) : ℂ) * logQuadPoly p₀ p₁ p₂ (Real.log x) =
      ((b⁻¹ * b ^ (-r) : ℝ) : ℂ) * logLaplacePoly r p₀ p₁ p₂ (Real.log b) := by
  have r0 := integrableOn_rpow_mul_log_pow_mul_exp_neg_mul hr (j := 0) (by norm_num) hb
  have r1 := integrableOn_rpow_mul_log_pow_mul_exp_neg_mul hr (j := 1) (by norm_num) hb
  have r2 := integrableOn_rpow_mul_log_pow_mul_exp_neg_mul hr (j := 2) (by norm_num) hb
  have i0 : IntegrableOn (fun x : ℝ => p₀ * ((x ^ r * Real.log x ^ 0 * Real.exp (-(b * x)) : ℝ) : ℂ))
      (Ioi 0) := (r0.ofReal (𝕜 := ℂ)).const_mul p₀
  have i1 : IntegrableOn (fun x : ℝ => p₁ * ((x ^ r * Real.log x ^ 1 * Real.exp (-(b * x)) : ℝ) : ℂ))
      (Ioi 0) := (r1.ofReal (𝕜 := ℂ)).const_mul p₁
  have i2 : IntegrableOn (fun x : ℝ => p₂ * ((x ^ r * Real.log x ^ 2 * Real.exp (-(b * x)) : ℝ) : ℂ))
      (Ioi 0) := (r2.ofReal (𝕜 := ℂ)).const_mul p₂
  have i01 : IntegrableOn (fun x : ℝ => p₀ * ((x ^ r * Real.log x ^ 0 * Real.exp (-(b * x)) : ℝ) : ℂ) +
      p₁ * ((x ^ r * Real.log x ^ 1 * Real.exp (-(b * x)) : ℝ) : ℂ)) (Ioi 0) := i0.add i1
  obtain ⟨e0, e1, e2⟩ := integral_rpow_mul_log_pow_mul_exp_neg_mul_eq hr hb
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x _ => logQuadPoly_log_mul_eq r b p₀ p₁ p₂ x),
    integral_add i01 i2, integral_add i0 i1, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_complex_ofReal, integral_complex_ofReal, integral_complex_ofReal,
    e0, e1, e2]
  unfold logLaplacePoly
  push_cast
  ring

/-! ## The Laplace step with logarithmic terms -/

/-- **Laplace step.** Under the odd theta relation with logarithmic terms, for real `t > 0`,
`L_a(t) = −Σ a_n e^{−2πnt} + P̂_0(log πt²)/(πt) + Q̂_{−1/2}(log πt²)/√π`. -/
theorem hamburgerSeries_eq_log_ofReal {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ (2 : ℝ)) {p₀ p₁ p₂ q₀ q₁ q₂ : ℂ}
    (htheta : ∀ x : ℝ, 0 < x → coeffTheta a x =
      -((x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta a x⁻¹) + logQuadPoly p₀ p₁ p₂ (Real.log x) +
        (x : ℂ) ^ (-(1 / 2 : ℂ)) * logQuadPoly q₀ q₁ q₂ (Real.log x))
    {t : ℝ} (ht : 0 < t) :
    hamburgerSeries a t =
      -∑' n : ℕ, a (n + 1) * cexp (-(2 * Real.pi * ((n : ℂ) + 1) * t)) +
        logLaplacePoly 0 p₀ p₁ p₂ (Real.log (Real.pi * t ^ 2)) / (Real.pi * t) +
        logLaplacePoly (-(1 / 2)) q₀ q₁ q₂ (Real.log (Real.pi * t ^ 2)) / Real.sqrt Real.pi := by
  set B : ℝ := Real.pi * t ^ 2 with hB
  have hB0 : 0 < B := by positivity
  set e : ℝ → ℂ := fun x => ((Real.exp (-(Real.pi * t ^ 2) * x) : ℝ) : ℂ) with he_def
  have hD_int := integrableOn_dual_coeffTheta_mul_exp_of_sq a ha ht
  have hP_eq : ∀ x ∈ Ioi (0 : ℝ), logQuadPoly p₀ p₁ p₂ (Real.log x) * e x =
      ((x ^ (0 : ℝ) * Real.exp (-(B * x)) : ℝ) : ℂ) * logQuadPoly p₀ p₁ p₂ (Real.log x) := by
    intro x _
    simp only [he_def, hB, Real.rpow_zero, one_mul, neg_mul]; ring
  have hQ_eq : ∀ x ∈ Ioi (0 : ℝ),
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * logQuadPoly q₀ q₁ q₂ (Real.log x) * e x =
        ((x ^ (-(1 / 2) : ℝ) * Real.exp (-(B * x)) : ℝ) : ℂ) * logQuadPoly q₀ q₁ q₂ (Real.log x) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    have hcpow : (x : ℂ) ^ (-(1 / 2 : ℂ)) = ((x ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hx0.le]; push_cast; ring_nf
    simp only [he_def, hB, hcpow, neg_mul]; push_cast; ring
  have hP_int : IntegrableOn (fun x : ℝ => logQuadPoly p₀ p₁ p₂ (Real.log x) * e x) (Ioi 0) :=
    (integrableOn_logQuadPoly_log_mul_exp (r := 0) (by norm_num) hB0 p₀ p₁ p₂).congr_fun
      (fun x hx => (hP_eq x hx).symm) measurableSet_Ioi
  have hQ_int : IntegrableOn (fun x : ℝ =>
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * logQuadPoly q₀ q₁ q₂ (Real.log x) * e x) (Ioi 0) :=
    (integrableOn_logQuadPoly_log_mul_exp (r := -(1 / 2)) (by norm_num) hB0 q₀ q₁ q₂).congr_fun
      (fun x hx => (hQ_eq x hx).symm) measurableSet_Ioi
  have hIP : ∫ x in Ioi (0 : ℝ), logQuadPoly p₀ p₁ p₂ (Real.log x) * e x =
      ((B⁻¹ * B ^ (-(0 : ℝ)) : ℝ) : ℂ) * logLaplacePoly 0 p₀ p₁ p₂ (Real.log B) := by
    rw [setIntegral_congr_fun measurableSet_Ioi hP_eq]
    exact integral_logQuadPoly_log_mul_exp (by norm_num) hB0 p₀ p₁ p₂
  have hIQ : ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (-(1 / 2 : ℂ)) * logQuadPoly q₀ q₁ q₂ (Real.log x) * e x =
      ((B⁻¹ * B ^ (-(-(1 / 2)) : ℝ) : ℝ) : ℂ) * logLaplacePoly (-(1 / 2)) q₀ q₁ q₂ (Real.log B) := by
    rw [setIntegral_congr_fun measurableSet_Ioi hQ_eq]
    exact integral_logQuadPoly_log_mul_exp (by norm_num) hB0 q₀ q₁ q₂
  have hpt : ∀ x ∈ Ioi (0 : ℝ), coeffTheta a x * e x =
      -((x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta a x⁻¹ * e x) +
        (logQuadPoly p₀ p₁ p₂ (Real.log x) * e x +
          (x : ℂ) ^ (-(1 / 2 : ℂ)) * logQuadPoly q₀ q₁ q₂ (Real.log x) * e x) := by
    intro x hx; rw [htheta x hx]; ring
  have hPQ : IntegrableOn (fun x : ℝ => logQuadPoly p₀ p₁ p₂ (Real.log x) * e x +
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * logQuadPoly q₀ q₁ q₂ (Real.log x) * e x) (Ioi 0) := hP_int.add hQ_int
  have hsplit : ∫ x in Ioi (0 : ℝ), coeffTheta a x * e x =
      -(∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta a x⁻¹ * e x) +
        ((∫ x in Ioi (0 : ℝ), logQuadPoly p₀ p₁ p₂ (Real.log x) * e x) +
          ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (-(1 / 2 : ℂ)) * logQuadPoly q₀ q₁ q₂ (Real.log x) * e x) := by
    have hDn : IntegrableOn (fun x : ℝ => -((x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta a x⁻¹ * e x))
        (Ioi 0) := hD_int.neg
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_add hDn hPQ, integral_neg,
      integral_add hP_int hQ_int]
  have hL := (hasSum_integral_coeffTheta_mul_exp_of_sq a ha ht).tsum_eq
  have hD := (hasSum_integral_dual_coeffTheta_mul_exp_of_sq a ha ht).tsum_eq
  rw [hsplit, ← hD, hIP, hIQ] at hL
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hham : hamburgerSeries a t = (t : ℂ) * ∑' n : ℕ,
      a (n + 1) / ((Real.pi * (((n : ℝ) + 1) ^ 2 + t ^ 2) : ℝ) : ℂ) := by
    rw [hamburgerSeries, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    push_cast
    ring
  have hdual : ∑' n : ℕ, a (n + 1) *
      ((1 / t * Real.exp (-(2 * Real.pi * ((n : ℝ) + 1) * t)) : ℝ) : ℂ) =
      (1 / (t : ℂ)) * ∑' n : ℕ, a (n + 1) * cexp (-(2 * Real.pi * ((n : ℂ) + 1) * t)) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    push_cast
    ring
  have hsqrt : B ^ (-(-(1 / 2)) : ℝ) = Real.sqrt Real.pi * t := by
    rw [neg_neg, ← Real.sqrt_eq_rpow, hB, Real.sqrt_mul Real.pi_pos.le, Real.sqrt_sq ht.le]
  have hsq0 : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hs2 : ((Real.sqrt Real.pi : ℝ) : ℂ) ^ 2 = (Real.pi : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  rw [hham, hL, hdual, hsqrt, neg_zero, Real.rpow_zero, mul_one]
  simp only [hB]
  push_cast
  field_simp
  linear_combination (t : ℂ) * logLaplacePoly (-(1 / 2)) q₀ q₁ q₂
    ((Real.log (Real.pi * t ^ 2) : ℝ) : ℂ) * hs2

/-! ## Continuation to the right half-plane -/

/-- `log(π t²)` on `Re t > 0`, with the principal logarithm. -/
def piSqLog (t : ℂ) : ℂ := (Real.log Real.pi : ℂ) + 2 * Complex.log t

theorem piSqLog_ofReal {t : ℝ} (ht : 0 < t) :
    piSqLog t = ((Real.log (Real.pi * t ^ 2) : ℝ) : ℂ) := by
  unfold piSqLog
  rw [Real.log_mul Real.pi_pos.ne' (by positivity), Real.log_pow, ← Complex.ofReal_log ht.le]
  push_cast; ring

theorem differentiableOn_piSqLog : DifferentiableOn ℂ piSqLog {t : ℂ | 0 < t.re} := fun _ ht =>
  (((Complex.differentiableAt_log (Complex.mem_slitPlane_iff.mpr (Or.inl ht))).const_mul
    (2 : ℂ)).const_add _).differentiableWithinAt

theorem differentiableOn_logLaplacePoly_piSqLog (r : ℝ) (c₀ c₁ c₂ : ℂ) :
    DifferentiableOn ℂ (fun t => logLaplacePoly r c₀ c₁ c₂ (piSqLog t)) {t : ℂ | 0 < t.re} := by
  have h := differentiableOn_piSqLog
  unfold logLaplacePoly
  fun_prop

/-- **The Laplace identity on `Re t > 0`.** -/
theorem hamburgerSeries_eq_log {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ (2 : ℝ)) {p₀ p₁ p₂ q₀ q₁ q₂ : ℂ}
    (htheta : ∀ x : ℝ, 0 < x → coeffTheta a x =
      -((x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta a x⁻¹) + logQuadPoly p₀ p₁ p₂ (Real.log x) +
        (x : ℂ) ^ (-(1 / 2 : ℂ)) * logQuadPoly q₀ q₁ q₂ (Real.log x))
    {t : ℂ} (ht : 0 < t.re) :
    hamburgerSeries a t =
      -∑' n : ℕ, a (n + 1) * cexp (-(2 * Real.pi * ((n : ℂ) + 1) * t)) +
        logLaplacePoly 0 p₀ p₁ p₂ (piSqLog t) / (Real.pi * t) +
        logLaplacePoly (-(1 / 2)) q₀ q₁ q₂ (piSqLog t) / Real.sqrt Real.pi := by
  set U : Set ℂ := {t : ℂ | 0 < t.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have ha2 : Summable fun n : ℕ => ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2 := by
    have := summable_sq_of_rpow_two ha
    simpa using this
  have hf : AnalyticOnNhd ℂ (hamburgerSeries a) U :=
    (differentiableOn_hamburgerSeries ha2).analyticOnNhd hUo
  have hne : ∀ t ∈ U, (Real.pi : ℂ) * t ≠ 0 := fun t ht => by
    have ht' : 0 < t.re := ht
    refine mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) fun h => ?_
    rw [h, zero_re] at ht'
    exact lt_irrefl _ ht'
  have hg : AnalyticOnNhd ℂ (fun t : ℂ => -∑' n : ℕ, a (n + 1) *
      cexp (-(2 * Real.pi * ((n : ℂ) + 1) * t)) +
        logLaplacePoly 0 p₀ p₁ p₂ (piSqLog t) / (Real.pi * t) +
        logLaplacePoly (-(1 / 2)) q₀ q₁ q₂ (piSqLog t) / Real.sqrt Real.pi) U := by
    refine DifferentiableOn.analyticOnNhd ?_ hUo
    refine (((differentiableOn_expDualSeries (summable_sq_of_rpow_two ha)).neg).add
      ((differentiableOn_logLaplacePoly_piSqLog 0 p₀ p₁ p₂).div (by fun_prop) hne)).add
      ((differentiableOn_logLaplacePoly_piSqLog _ q₀ q₁ q₂).div_const _)
  have h1U : (1 : ℂ) ∈ U := by simp [hU]
  have hfreq : ∃ᶠ z in 𝓝[≠] (1 : ℂ), hamburgerSeries a z = -∑' n : ℕ, a (n + 1) *
      cexp (-(2 * Real.pi * ((n : ℂ) + 1) * z)) +
        logLaplacePoly 0 p₀ p₁ p₂ (piSqLog z) / (Real.pi * z) +
        logLaplacePoly (-(1 / 2)) q₀ q₁ q₂ (piSqLog z) / Real.sqrt Real.pi := by
    set u : ℕ → ℂ := fun k => ((1 + 1 / ((k : ℝ) + 1) : ℝ) : ℂ) with hu
    have hlim : Tendsto u atTop (𝓝[≠] (1 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun k => ?_⟩
      · have h := (tendsto_one_div_add_atTop_nhds_zero_nat).const_add (1 : ℝ)
        rw [add_zero] at h
        have h2 := (Complex.continuous_ofReal.tendsto 1).comp h
        rw [Complex.ofReal_one] at h2
        exact h2
      · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, hu]
        intro h
        have h' : (1 + 1 / ((k : ℝ) + 1) : ℝ) = 1 := by exact_mod_cast h
        have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith
    refine hlim.frequently (Frequently.of_forall fun k => ?_)
    have hk : (0 : ℝ) < 1 + 1 / ((k : ℝ) + 1) := by positivity
    simp only [hu]
    rw [piSqLog_ofReal hk]
    exact hamburgerSeries_eq_log_ofReal ha htheta hk
  exact hf.eqOn_of_preconnected_of_frequently_eq hg (convex_halfSpace_re_gt 0).isPreconnected
    h1U hfreq ht

/-! ## The residue at `0` -/

/-- A quadratic `c₂ g² + c₁ g + c₀` with a finite limit along `g → −∞` has `c₂ = c₁ = 0`. -/
theorem quadratic_coeffs_eq_zero_of_tendsto {α : Type*} {l : Filter α} [l.NeBot] {g : α → ℝ}
    (hg : Tendsto g l atBot) {c₀ c₁ c₂ L : ℂ}
    (h : Tendsto (fun x => c₂ * (g x : ℂ) ^ 2 + c₁ * (g x : ℂ) + c₀) l (𝓝 L)) :
    c₂ = 0 ∧ c₁ = 0 := by
  have hinv : Tendsto (fun x => (((g x)⁻¹ : ℝ) : ℂ)) l (𝓝 0) := by
    have := (Complex.continuous_ofReal.tendsto 0).comp (tendsto_inv_atBot_zero.comp hg)
    rw [Complex.ofReal_zero] at this
    exact this
  have hev : ∀ᶠ x in l, g x ≠ 0 := (hg.eventually (eventually_lt_atBot 0)).mono fun x hx => hx.ne
  have hc₂ : c₂ = 0 := by
    have h1 : Tendsto (fun x => (c₂ * (g x : ℂ) ^ 2 + c₁ * (g x : ℂ) + c₀) *
        (((g x)⁻¹ : ℝ) : ℂ) ^ 2) l (𝓝 (L * 0 ^ 2)) := h.mul (hinv.pow 2)
    have h2 : Tendsto (fun x => c₂ + c₁ * (((g x)⁻¹ : ℝ) : ℂ) + c₀ * (((g x)⁻¹ : ℝ) : ℂ) ^ 2) l
        (𝓝 (c₂ + c₁ * 0 + c₀ * 0 ^ 2)) :=
      (tendsto_const_nhds.add (hinv.const_mul c₁)).add ((hinv.pow 2).const_mul c₀)
    refine tendsto_nhds_unique (h2.congr' (hev.mono fun x hx => ?_)) (by simpa using h1) |>.symm.trans
      (by ring) |>.symm
    have hx' : (g x : ℂ) ≠ 0 := by exact_mod_cast hx
    push_cast
    field_simp
  refine ⟨hc₂, ?_⟩
  subst hc₂
  have h1 : Tendsto (fun x => (0 * (g x : ℂ) ^ 2 + c₁ * (g x : ℂ) + c₀) * (((g x)⁻¹ : ℝ) : ℂ)) l
      (𝓝 (L * 0)) := h.mul hinv
  have h2 : Tendsto (fun x => c₁ + c₀ * (((g x)⁻¹ : ℝ) : ℂ)) l (𝓝 (c₁ + c₀ * 0)) :=
    tendsto_const_nhds.add (hinv.const_mul c₀)
  refine tendsto_nhds_unique (h2.congr' (hev.mono fun x hx => ?_)) (by simpa using h1) |>.symm.trans
    (by ring) |>.symm
  have hx' : (g x : ℂ) ≠ 0 := by exact_mod_cast hx
  push_cast
  field_simp

theorem logExpMoment_zero_zero : logExpMoment 0 0 = 1 := by
  unfold logExpMoment
  simp only [Real.rpow_zero, pow_zero, one_mul]
  exact integral_exp_neg_Ioi_zero

/-- `t · z^k → 0` as `t → 0⁺`, for `z = log π + 2 log t` and `k ≤ 2`. -/
theorem tendsto_mul_logLaplacePoly_piSqLog (r : ℝ) (c₀ c₁ c₂ : ℂ) :
    Tendsto (fun t : ℝ => (t : ℂ) * logLaplacePoly r c₀ c₁ c₂ (piSqLog t)) (𝓝[>] 0) (𝓝 0) := by
  have hl1 : Tendsto (fun t : ℝ => t * Real.log t) (𝓝[>] 0) (𝓝 0) := by
    have := tendsto_log_mul_rpow_nhdsGT_zero (r := 1) one_pos
    refine this.congr' (eventually_nhdsWithin_of_forall fun t ht => ?_)
    simp only [Real.rpow_one]; ring
  have hl2 : Tendsto (fun t : ℝ => t * Real.log t ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have h := tendsto_log_mul_rpow_nhdsGT_zero (r := 1 / 2) (by norm_num)
    have := h.pow 2
    rw [zero_pow two_ne_zero] at this
    refine this.congr' (eventually_nhdsWithin_of_forall fun t ht => ?_)
    have ht0 : (0 : ℝ) < t := ht
    rw [mul_pow, ← Real.rpow_natCast (t ^ (1 / 2 : ℝ)), ← Real.rpow_mul ht0.le]
    norm_num; ring
  have ht : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  set Lp := Real.log Real.pi
  -- `t · z^j` for `z = Lp + 2 log t`
  have hz0 : Tendsto (fun t : ℝ => t * 1) (𝓝[>] 0) (𝓝 0) := by simpa using ht
  have hz1 : Tendsto (fun t : ℝ => t * (Lp + 2 * Real.log t)) (𝓝[>] 0) (𝓝 0) := by
    have := (ht.const_mul Lp).add (hl1.const_mul 2)
    simp only [mul_zero, add_zero] at this
    refine this.congr' (Eventually.of_forall fun t => ?_); ring
  have hz2 : Tendsto (fun t : ℝ => t * (Lp + 2 * Real.log t) ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have := ((ht.const_mul (Lp ^ 2)).add (hl1.const_mul (4 * Lp))).add (hl2.const_mul 4)
    simp only [mul_zero, add_zero] at this
    refine this.congr' (Eventually.of_forall fun t => ?_); ring
  have hC := fun (f : ℝ → ℝ) (hf : Tendsto f (𝓝[>] 0) (𝓝 0)) =>
    (Complex.continuous_ofReal.tendsto 0).comp hf
  have e : ∀ t : ℝ, 0 < t → (t : ℂ) * logLaplacePoly r c₀ c₁ c₂ (piSqLog t) =
      (c₀ * logExpMoment r 0 + c₁ * logExpMoment r 1 + c₂ * logExpMoment r 2) *
          (((t * 1 : ℝ)) : ℂ) -
        (c₁ * logExpMoment r 0 + 2 * c₂ * logExpMoment r 1) *
          ((t * (Lp + 2 * Real.log t) : ℝ) : ℂ) +
        c₂ * logExpMoment r 0 * ((t * (Lp + 2 * Real.log t) ^ 2 : ℝ) : ℂ) := by
    intro t ht0
    rw [piSqLog_ofReal ht0, Real.log_mul Real.pi_pos.ne' (by positivity), Real.log_pow]
    unfold logLaplacePoly
    push_cast
    ring
  have hlim := (((hC _ hz0).const_mul (c₀ * logExpMoment r 0 + c₁ * logExpMoment r 1 +
    c₂ * logExpMoment r 2)).sub ((hC _ hz1).const_mul (c₁ * logExpMoment r 0 +
      2 * c₂ * logExpMoment r 1))).add ((hC _ hz2).const_mul (c₂ * logExpMoment r 0))
  simp only [Function.comp_def, Complex.ofReal_zero, mul_zero, sub_zero, add_zero] at hlim
  exact hlim.congr' (eventually_nhdsWithin_of_forall fun t ht0 => (e t ht0).symm)

/-- **Hamburger's residue at `0` with logarithmic terms.** Under the odd theta relation
`θ_a(x) = −x^{−1/2} θ_a(1/x) + P(log x) + x^{−1/2} Q(log x)` (`Σ ‖a_n‖/n² < ∞`, `P, Q` quadratic),
the coefficients of `log x` and `log² x` in `P` vanish. -/
theorem quadratic_log_coeffs_eq_zero_of_odd_coeffTheta_relation {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ (2 : ℝ)) {p₀ p₁ p₂ q₀ q₁ q₂ : ℂ}
    (htheta : ∀ x : ℝ, 0 < x → coeffTheta a x =
      -((x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta a x⁻¹) + logQuadPoly p₀ p₁ p₂ (Real.log x) +
        (x : ℂ) ^ (-(1 / 2 : ℂ)) * logQuadPoly q₀ q₁ q₂ (Real.log x)) :
    p₂ = 0 ∧ p₁ = 0 := by
  have ha2 : Summable fun n : ℕ => ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2 := by
    have := summable_sq_of_rpow_two ha
    simpa using this
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  set R : ℂ → ℂ := fun t => logLaplacePoly 0 p₀ p₁ p₂ (piSqLog t) / (Real.pi * t) +
    logLaplacePoly (-(1 / 2)) q₀ q₁ q₂ (piSqLog t) / Real.sqrt Real.pi with hR
  have hper : ∀ t : ℂ, 0 < t.re →
      hamburgerSeries a (t + I) - hamburgerSeries a t = R (t + I) - R t := by
    intro t ht
    have ht' : 0 < (t + I).re := by simpa using ht
    rw [hamburgerSeries_eq_log ha htheta ht', hamburgerSeries_eq_log ha htheta ht]
    have hp : ∑' n : ℕ, a (n + 1) * cexp (-(2 * Real.pi * ((n : ℂ) + 1) * (t + I))) =
        ∑' n : ℕ, a (n + 1) * cexp (-(2 * Real.pi * ((n : ℂ) + 1) * t)) := by
      refine tsum_congr fun n => ?_
      rw [show -(2 * (Real.pi : ℂ) * ((n : ℂ) + 1) * (t + I)) =
        -(2 * Real.pi * ((n : ℂ) + 1) * t) + ((-((n : ℤ) + 1) : ℤ) : ℂ) * (2 * Real.pi * I) by
          push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    rw [hp]
    simp only [hR]
    ring
  -- limits along real `t → 0⁺`
  have hι : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[>] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
      (eventually_nhdsWithin_of_forall fun t ht => ?_)
    · have := (Complex.continuous_ofReal.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      simpa using this
    · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_eq_zero]
      exact (ht : (0 : ℝ) < t).ne'
  have hA := (tendsto_mul_hamburgerSeries_add_I ha2).comp hι
  have hB : Tendsto (fun t : ℝ => (t : ℂ) * hamburgerSeries a t) (𝓝[>] 0) (𝓝 0) := by
    have hz : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[>] 0) (𝓝 0) := hι.mono_right nhdsWithin_le_nhds
    have hL := ((tendsto_hamburgerSeries_zero ha2).comp hz)
    simpa using hz.mul hL
  have hIm : I ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inr (by simp))
  have hRc : ContinuousAt R I := by
    have hlog : ContinuousAt piSqLog I :=
      (((Complex.differentiableAt_log hIm).const_mul (2 : ℂ)).const_add _).continuousAt
    have hP : ContinuousAt (fun t => logLaplacePoly 0 p₀ p₁ p₂ (piSqLog t)) I := by
      unfold logLaplacePoly; fun_prop
    have hQ : ContinuousAt (fun t => logLaplacePoly (-(1 / 2)) q₀ q₁ q₂ (piSqLog t)) I := by
      unfold logLaplacePoly; fun_prop
    have hden : (Real.pi : ℂ) * I ≠ 0 := mul_ne_zero hπ I_ne_zero
    exact (hP.div (by fun_prop) hden).add (hQ.div_const _)
  have hC : Tendsto (fun t : ℝ => (t : ℂ) * R (t + I)) (𝓝[>] 0) (𝓝 0) := by
    have hz : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[>] 0) (𝓝 0) := hι.mono_right nhdsWithin_le_nhds
    have hshift : Tendsto (fun t : ℝ => (t : ℂ) + I) (𝓝[>] 0) (𝓝 I) := by
      simpa using hz.add_const I
    simpa using hz.mul (hRc.tendsto.comp hshift)
  have hD := tendsto_mul_logLaplacePoly_piSqLog (-(1 / 2)) q₀ q₁ q₂
  have hE : Tendsto (fun t : ℝ => logLaplacePoly 0 p₀ p₁ p₂ (piSqLog t) / Real.pi) (𝓝[>] 0)
      (𝓝 (0 - (a 1 / (2 * Real.pi) - 0) - 0 / Real.sqrt Real.pi)) := by
    have := ((hC.sub (hA.sub hB)).sub (hD.div_const (Real.sqrt Real.pi : ℂ)))
    refine this.congr' (eventually_nhdsWithin_of_forall fun t ht => ?_)
    have ht0 : (0 : ℝ) < t := ht
    have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
    have hp := hper t (by simpa using ht0)
    simp only [Function.comp_def]
    have e : (t : ℂ) * hamburgerSeries a (t + I) - (t : ℂ) * hamburgerSeries a t =
        (t : ℂ) * (R (t + I) - R t) := by rw [← hp]; ring
    rw [e]
    simp only [hR]
    field_simp
    ring
  -- the quadratic in `g t = log π + 2 log t`
  have hg : Tendsto (fun t : ℝ => Real.log Real.pi + 2 * Real.log t) (𝓝[>] 0) atBot :=
    tendsto_atBot_add_const_left _ _ (Real.tendsto_log_nhdsGT_zero.const_mul_atBot two_pos)
  have hq := quadratic_coeffs_eq_zero_of_tendsto hg
    (c₂ := p₂ * logExpMoment 0 0 / Real.pi)
    (c₁ := -(p₁ * logExpMoment 0 0 + 2 * p₂ * logExpMoment 0 1) / Real.pi)
    (c₀ := (p₀ * logExpMoment 0 0 + p₁ * logExpMoment 0 1 + p₂ * logExpMoment 0 2) / Real.pi)
    (hE.congr' (eventually_nhdsWithin_of_forall fun t ht => by
      have ht0 : (0 : ℝ) < t := ht
      rw [piSqLog_ofReal ht0, Real.log_mul Real.pi_pos.ne' (by positivity), Real.log_pow]
      unfold logLaplacePoly
      push_cast
      field_simp
      ring))
  rw [logExpMoment_zero_zero] at hq
  obtain ⟨h2, h1⟩ := hq
  have hp₂ : p₂ = 0 := by
    have := h2; push_cast at this; field_simp at this; simpa using this
  refine ⟨hp₂, ?_⟩
  rw [hp₂] at h1
  push_cast at h1
  field_simp at h1
  linear_combination -h1

end GaloisForLFunctions.HTGeometry
