import GaloisForLFunctions.HTGeometry.GammaFiniteProjectiveLaw

/-!
# Vertical decay of the Gamma function

Adjoining `Γ` to the digamma differential field creates one exponential valuation direction: on a
fixed vertical tube `Γ` tends to zero, while every quotient of nonzero coefficients has only
algebraic-logarithmic size.  This file proves the decay unconditionally.

The mechanism is elementary.  Euler's integral bounds the complex Gamma function by the real Gamma
function of its abscissa, `‖Γ(s)‖ ≤ Γ(Re s)`, because the integrand only loses its phase.  The
recursion `Γ(s+1) = sΓ(s)` applied one step to the right converts that *bound* into *decay*:

`‖Γ(σ+it)‖ = ‖Γ(σ+1+it)‖ / ‖σ+it‖ ≤ Γ(σ+1) / t`.

Since `Γ` has no zeros, the limit is attained inside the punctured neighbourhood of `0`, which is the
form consumed by the Gamma monomial valuation.
-/

open Filter Topology MeasureTheory Set

namespace GaloisForLFunctions

/-- **Euler bound.**  On the open right half-plane the complex Gamma function is dominated by the
real Gamma function of its abscissa: the Euler integrand `e^{-x} x^{s-1}` has modulus
`e^{-x} x^{Re s - 1}`. -/
theorem norm_Gamma_le_real_Gamma_re {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs, Real.Gamma_eq_integral hs]
  simp only [Complex.GammaIntegral]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  have hx0 : (0 : ℝ) < x := hx
  have h1 : ‖((Real.exp (-x) : ℝ) : ℂ)‖ = Real.exp (-x) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [norm_mul, h1, Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.sub_re, Complex.one_re]

/-- **Vertical Gamma bound.**  For `σ > 0` and `t > 0`, `‖Γ(σ + it)‖ ≤ Γ(σ+1) / t`.  The Euler bound
is applied at abscissa `σ + 1` and pulled back by the recursion `Γ(s+1) = sΓ(s)`, whose factor `‖s‖`
is at least `t`. -/
theorem norm_Gamma_vertical_le {σ : ℝ} (hσ : 0 < σ) {t : ℝ} (ht : 0 < t) :
    ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ Real.Gamma (σ + 1) / t := by
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hsdef
  have hsre : s.re = σ := by simp [hsdef]
  have hsim : s.im = t := by simp [hsdef]
  have hsne : s ≠ 0 := by
    intro h
    rw [h] at hsim
    simp only [Complex.zero_im] at hsim
    linarith
  have hsucc : (s + 1).re = σ + 1 := by rw [Complex.add_re, Complex.one_re, hsre]
  have hbound : ‖Complex.Gamma (s + 1)‖ ≤ Real.Gamma (σ + 1) := by
    have hpos : 0 < (s + 1).re := by rw [hsucc]; linarith
    have := norm_Gamma_le_real_Gamma_re hpos
    rwa [hsucc] at this
  have hnorm : ‖s‖ * ‖Complex.Gamma s‖ = ‖Complex.Gamma (s + 1)‖ := by
    rw [Complex.Gamma_add_one s hsne, norm_mul]
  have hsge : t ≤ ‖s‖ := by
    have habs := Complex.abs_im_le_norm s
    rw [hsim, abs_of_pos ht] at habs
    exact habs
  rw [le_div_iff₀ ht]
  calc ‖Complex.Gamma s‖ * t
      ≤ ‖Complex.Gamma s‖ * ‖s‖ := mul_le_mul_of_nonneg_left hsge (norm_nonneg _)
    _ = ‖Complex.Gamma (s + 1)‖ := by rw [← hnorm]; ring
    _ ≤ Real.Gamma (σ + 1) := hbound

/-- **Vertical Gamma decay (§4, eq. 24).**  `Γ(σ + it) → 0` as `t → +∞`, for every `σ > 0`. -/
theorem Gamma_vertical_tendsto_zero {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun t : ℝ => Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)) atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (g := fun t : ℝ => Real.Gamma (σ + 1) / t)
    (Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact norm_Gamma_vertical_le hσ ht
  · exact tendsto_const_nhds.div_atTop tendsto_id

/-- `Γ` has no zeros in the open right half-plane, so its vertical decay happens inside the
punctured neighbourhood of `0`.  This is the form of eq. (24) consumed by the Gamma monomial
valuation, where the leading Gamma power has to be inverted. -/
theorem Gamma_vertical_tendsto_nhdsWithin_zero {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun t : ℝ => Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)) atTop
      (nhdsWithin 0 {(0 : ℂ)}ᶜ) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (Gamma_vertical_tendsto_zero hσ) (Eventually.of_forall fun t => ?_)
  have hpoles : ∀ p : ℕ, ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ -(p : ℂ) := by
    intro p heq
    have hre := congrArg Complex.re heq
    simp at hre
    linarith [Nat.cast_nonneg (α := ℝ) p]
  simpa using Complex.Gamma_ne_zero hpoles

/-- **Unconditional Gamma monomial valuation residue (§4, eq. 3).**  A Gamma-field element written
as `F = P(Γ)/Q(Γ)` with `P = X^u R`, `Q = X^v S` and `S(0) ≠ 0`, normalized by its dominant Gamma
powers, converges on every upper vertical line of positive abscissa to the residue `R(0)/S(0)` of
its digamma-field coefficients.  The vertical Gamma decay is no longer a hypothesis. -/
theorem gamma_monomial_valuation_residue_vertical
    (P Q R S : Polynomial ℂ) (u v : ℕ) {σ : ℝ} (hσ : 0 < σ)
    (hP : P = Polynomial.X ^ u * R) (hQ : Q = Polynomial.X ^ v * S) (hS0 : S.eval 0 ≠ 0) :
    Tendsto (fun t : ℝ =>
        (P.eval (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I))
            / (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ u)
          / (Q.eval (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I))
            / (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ v))
      atTop (nhds (R.eval 0 / S.eval 0)) :=
  gamma_monomial_valuation_residue P Q R S u v σ hP hQ hS0
    (Gamma_vertical_tendsto_nhdsWithin_zero hσ)

end GaloisForLFunctions
