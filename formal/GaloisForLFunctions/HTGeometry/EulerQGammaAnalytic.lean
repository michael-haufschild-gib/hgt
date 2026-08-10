import GaloisForLFunctions.HTGeometry.EulerQGammaLadder

/-!
# Analyticity of the arithmetic Dirichlet series

The series `D_σ(w) = ∑_m m^{-w}/∏_p (q_p;q_p)_{v_p(m)}` differentiates term by term on every
half-plane `Re w > x₀ > 1`: the differentiated terms are dominated by `log m · E · m^{-x₀}`, which
is summable because `log m ≤ m^δ/δ` for any `δ > 0`.  Hence `D_σ` is analytic on the whole
convergence chamber `Re w > 1`, which is what makes the zeta ladder a genuine analytic
factorisation of the Euler q-Gamma response.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

set_option maxHeartbeats 1000000

noncomputable section

/-! ## The half-plane -/

/-- The open half-plane `Re w > x₀`. -/
def eqgHalf (x₀ : ℝ) : Set ℂ := {w : ℂ | x₀ < w.re}

theorem isOpen_eqgHalf (x₀ : ℝ) : IsOpen (eqgHalf x₀) :=
  isOpen_lt continuous_const Complex.continuous_re

theorem convex_eqgHalf (x₀ : ℝ) : Convex ℝ (eqgHalf x₀) := convex_halfSpace_re_gt _

/-! ## Term-by-term differentiation -/

theorem log_natCast_nonneg (m : ℕ) : 0 ≤ Real.log (m : ℝ) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · exact Real.log_nonneg (by exact_mod_cast hm)

/-- The differentiated arithmetic term `−log m · m^{-w}/∏_p (q_p;q_p)_{v_p(m)}`. -/
def eqgTermDeriv (σ : EulerSigma) (w : ℂ) (m : ℕ) : ℂ :=
  if m = 0 then 0 else -((Real.log m : ℝ) : ℂ) * eqgTerm σ w m

theorem hasDerivAt_eqgTerm (σ : EulerSigma) (m : ℕ) (w : ℂ) :
    HasDerivAt (fun z : ℂ => eqgTerm σ z m) (eqgTermDeriv σ w m) w := by
  rcases eq_or_ne m 0 with rfl | hm
  · have hfun : (fun z : ℂ => eqgTerm σ z 0) = fun _ : ℂ => (0 : ℂ) := by
      funext z
      exact eqgTerm_zero σ z
    rw [hfun, eqgTermDeriv, if_pos rfl]
    exact hasDerivAt_const w 0
  have hmC : ((m : ℕ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    exact hm
  have hmR : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hm
  have hden : ((eqgDenom σ m : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact (eqgDenom_pos σ m).ne'
  have hcp : HasDerivAt (fun z : ℂ => ((m : ℕ) : ℂ) ^ (-z))
      (-(((m : ℕ) : ℂ) ^ (-w) * Complex.log ((m : ℕ) : ℂ))) w := by
    have hbase := (Complex.hasStrictDerivAt_const_cpow
      (x := ((m : ℕ) : ℂ)) (y := -w) (Or.inl hmC)).hasDerivAt
    have hneg : HasDerivAt (fun z : ℂ => -z) (-1 : ℂ) w := (hasDerivAt_id w).neg
    have hcomp := hbase.comp w hneg
    simpa [Function.comp_def] using hcomp
  have hfun : (fun z : ℂ => eqgTerm σ z m)
      = fun z : ℂ => ((m : ℕ) : ℂ) ^ (-z) / ((eqgDenom σ m : ℝ) : ℂ) := by
    funext z
    rw [eqgTerm, if_neg hm]
  rw [hfun]
  have hdiv := hcp.div_const ((eqgDenom σ m : ℝ) : ℂ)
  refine hdiv.congr_deriv ?_
  have hlogcast : Complex.log ((m : ℕ) : ℂ) = ((Real.log ((m : ℕ) : ℝ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg m)]
  rw [eqgTermDeriv, if_neg hm, eqgTerm, if_neg hm, hlogcast]
  field_simp

theorem norm_eqgTermDeriv (σ : EulerSigma) (w : ℂ) (m : ℕ) :
    ‖eqgTermDeriv σ w m‖ = Real.log m * eqgWeightRe σ w.re m := by
  rcases eq_or_ne m 0 with rfl | hm
  · rw [eqgTermDeriv, if_pos rfl, norm_zero, eqgWeightRe_zero, mul_zero]
  rw [eqgTermDeriv, if_neg hm, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (log_natCast_nonneg m), norm_eqgTerm]

/-- The dominating summand for the differentiated series. -/
def eqgDerivBound (σ : EulerSigma) (x₀ : ℝ) (m : ℕ) : ℝ :=
  Real.log m * (Real.exp (4 * eqgTail σ) * (m : ℝ) ^ (-x₀))

theorem eqgDerivBound_nonneg (σ : EulerSigma) (x₀ : ℝ) (m : ℕ) : 0 ≤ eqgDerivBound σ x₀ m := by
  rw [eqgDerivBound]
  refine mul_nonneg (log_natCast_nonneg m) ?_
  exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (Nat.cast_nonneg m) _)

theorem norm_eqgTermDeriv_le (σ : EulerSigma) {x₀ : ℝ} {w : ℂ} (hw : w ∈ eqgHalf x₀) (m : ℕ) :
    ‖eqgTermDeriv σ w m‖ ≤ eqgDerivBound σ x₀ m := by
  rcases eq_or_ne m 0 with rfl | hm
  · rw [eqgTermDeriv, if_pos rfl, norm_zero, eqgDerivBound]
    simp
  rw [norm_eqgTermDeriv, eqgDerivBound]
  refine mul_le_mul_of_nonneg_left ?_ (log_natCast_nonneg m)
  refine le_trans (eqgWeightRe_le σ w.re m) ?_
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
  refine Real.rpow_le_rpow_of_exponent_le hm1 ?_
  have hwre : x₀ < w.re := hw
  linarith

theorem summable_eqgDerivBound (σ : EulerSigma) {x₀ : ℝ} (hx₀ : 1 < x₀) :
    Summable (eqgDerivBound σ x₀) := by
  set δ : ℝ := (x₀ - 1) / 2 with hδ
  have hδ0 : 0 < δ := by
    rw [hδ]
    linarith
  have hexp : 1 < x₀ - δ := by
    rw [hδ]
    linarith
  have hmajor : Summable fun m : ℕ =>
      Real.exp (4 * eqgTail σ) / δ * (m : ℝ) ^ (-(x₀ - δ)) := by
    refine Summable.mul_left _ ?_
    have h : Summable fun m : ℕ => (((m : ℝ)) ^ (x₀ - δ))⁻¹ :=
      Real.summable_nat_rpow_inv.mpr hexp
    refine h.congr fun m => ?_
    rw [Real.rpow_neg (Nat.cast_nonneg m)]
  refine Summable.of_nonneg_of_le (eqgDerivBound_nonneg σ x₀) (fun m => ?_) hmajor
  have hlog : Real.log m ≤ (m : ℝ) ^ δ / δ :=
    Real.log_le_rpow_div (Nat.cast_nonneg m) hδ0
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hsplit : (m : ℝ) ^ δ * (m : ℝ) ^ (-x₀) = (m : ℝ) ^ (-(x₀ - δ)) := by
    rw [← Real.rpow_add' hm0 (by rw [hδ]; intro h; linarith)]
    congr 1
    ring
  rw [eqgDerivBound]
  calc Real.log m * (Real.exp (4 * eqgTail σ) * (m : ℝ) ^ (-x₀))
      ≤ ((m : ℝ) ^ δ / δ) * (Real.exp (4 * eqgTail σ) * (m : ℝ) ^ (-x₀)) := by
        refine mul_le_mul_of_nonneg_right hlog ?_
        exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hm0 _)
    _ = Real.exp (4 * eqgTail σ) / δ * ((m : ℝ) ^ δ * (m : ℝ) ^ (-x₀)) := by ring
    _ = Real.exp (4 * eqgTail σ) / δ * (m : ℝ) ^ (-(x₀ - δ)) := by rw [hsplit]

/-! ## Analyticity -/

theorem hasDerivAt_eqgDirichlet (σ : EulerSigma) {x₀ : ℝ} (hx₀ : 1 < x₀) {w : ℂ}
    (hw : w ∈ eqgHalf x₀) :
    HasDerivAt (eqgDirichlet σ) (∑' m : ℕ, eqgTermDeriv σ w m) w := by
  have hy₀ : ((x₀ + 1 : ℝ) : ℂ) ∈ eqgHalf x₀ := by
    simp only [eqgHalf, Set.mem_setOf_eq, Complex.ofReal_re]
    linarith
  have hsummable₀ : Summable fun m : ℕ => eqgTerm σ ((x₀ + 1 : ℝ) : ℂ) m := by
    refine summable_eqgTerm σ ?_
    simp only [Complex.ofReal_re]
    linarith
  exact hasDerivAt_tsum_of_isPreconnected (summable_eqgDerivBound σ hx₀) (isOpen_eqgHalf x₀)
    (convex_eqgHalf x₀).isPreconnected
    (fun m y _ => hasDerivAt_eqgTerm σ m y)
    (fun m y hy => norm_eqgTermDeriv_le σ hy m) hy₀ hsummable₀ hw

theorem differentiableOn_eqgDirichlet (σ : EulerSigma) {x₀ : ℝ} (hx₀ : 1 < x₀) :
    DifferentiableOn ℂ (eqgDirichlet σ) (eqgHalf x₀) :=
  fun _ hw => ((hasDerivAt_eqgDirichlet σ hx₀ hw).differentiableAt).differentiableWithinAt

/-- **The arithmetic Dirichlet series is analytic on the convergence chamber.** -/
theorem analyticAt_eqgDirichlet (σ : EulerSigma) {w : ℂ} (hw : 1 < w.re) :
    AnalyticAt ℂ (eqgDirichlet σ) w := by
  set x₀ : ℝ := (1 + w.re) / 2 with hx₀def
  have hx₀ : 1 < x₀ := by
    rw [hx₀def]
    linarith
  have hmem : w ∈ eqgHalf x₀ := by
    simp only [eqgHalf, Set.mem_setOf_eq, hx₀def]
    linarith
  have hanalytic : AnalyticOnNhd ℂ (eqgDirichlet σ) (eqgHalf x₀) :=
    (differentiableOn_eqgDirichlet σ hx₀).analyticOnNhd (isOpen_eqgHalf x₀)
  exact hanalytic w hmem

end

end GaloisForLFunctions.HTGeometry
