import GaloisForLFunctions.RHTower.XiLogDerivFactorization
import GaloisForLFunctions.RHTower.GammaVerticalPhaseAsymptotic
import GaloisForLFunctions.RHTower.ZetaRealTraceDiscCount

/-!
# The vertical phase of `ξ` on the abscissa `2`

Taking real parts in the four-factor splitting of `ξ'/ξ` at `s = 2 + iy` and integrating in `y`
gives

`∫₀^T Re (ξ'/ξ)(2+iy) dy
   = ∫₀^T [2/(4+y²) + 1/(1+y²)] dy − (T/2) log π + Φ(T/2) + ∫₀^T Re (ζ'/ζ)(2+iy) dy`,

where `Φ` is the vertical Gamma phase.  The first and last terms are bounded — the first by the two
arctangents and the last because `Re ζ(2+iy) > 0` keeps the principal logarithm in a half-plane —
so the whole vertical contribution is `Φ(T/2) − (T/2) log π + O(1)`.
-/

open Complex Filter Topology intervalIntegral MeasureTheory

noncomputable section

namespace RHTower

/-! ## The pointwise splitting -/

theorem re_logDeriv_xi_two_add (y : ℝ) :
    (logDeriv xi ((2 : ℂ) + (y : ℂ) * I)).re
      = 2 / (4 + y ^ 2) + 1 / (1 + y ^ 2) - Real.log Real.pi / 2
        + (Complex.digamma ((1 : ℂ) + ((y / 2 : ℝ) : ℂ) * I)).re / 2
        + (logDeriv riemannZeta ((2 : ℂ) + (y : ℂ) * I)).re := by
  set s : ℂ := (2 : ℂ) + (y : ℂ) * I with hs
  have hre : s.re = 2 := by simp [hs]
  have him : s.im = y := by simp [hs]
  have hgt : 1 < s.re := by rw [hre]; norm_num
  have hhalf : s / 2 = (1 : ℂ) + ((y / 2 : ℝ) : ℂ) * I := by
    rw [hs]
    push_cast
    ring
  have hinv1 : ((1 : ℂ) / s).re = 2 / (4 + y ^ 2) := by
    rw [one_div, Complex.inv_re, Complex.normSq_apply, hre, him]
    norm_num
    ring_nf
  have hinv2 : ((1 : ℂ) / (s - 1)).re = 1 / (1 + y ^ 2) := by
    have hsub : (s - 1).re = 1 := by rw [Complex.sub_re, hre]; norm_num
    have hsubim : (s - 1).im = y := by rw [Complex.sub_im, him]; norm_num
    rw [one_div, Complex.inv_re, Complex.normSq_apply, hsub, hsubim]
    norm_num
    ring
  have hdiv2 : ∀ z : ℂ, (z / 2).re = z.re / 2 := by
    intro z
    simp
  rw [logDeriv_xi_fourFactor hgt, hhalf]
  simp only [Complex.add_re, Complex.sub_re, hdiv2, Complex.ofReal_re]
  rw [hinv1, hinv2]

/-! ## Continuity -/

theorem continuous_re_logDeriv_xi_two :
    Continuous fun y : ℝ => (logDeriv xi ((2 : ℂ) + (y : ℂ) * I)).re := by
  refine Complex.continuous_re.comp (continuous_iff_continuousAt.mpr fun y => ?_)
  have hs : ((2 : ℂ) + (y : ℂ) * I) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have hne : xi ((2 : ℂ) + (y : ℂ) * I) ≠ 0 := by
    refine xi_ne_zero_of_one_le_re ?_
    simp
  have hxi : AnalyticAt ℂ xi ((2 : ℂ) + (y : ℂ) * I) :=
    xi_analyticOnNhd_univ _ (Set.mem_univ _)
  have hquot : AnalyticAt ℂ (fun z => deriv xi z / xi z) ((2 : ℂ) + (y : ℂ) * I) :=
    hxi.deriv.div hxi hne
  have heq : logDeriv xi = fun z => deriv xi z / xi z := by
    funext z
    rw [logDeriv_apply]
  have hpath : ContinuousAt (fun u : ℝ => (2 : ℂ) + (u : ℂ) * I) y := by fun_prop
  rw [heq]
  exact ContinuousAt.comp (f := fun u : ℝ => (2 : ℂ) + (u : ℂ) * I) hquot.continuousAt hpath

theorem continuous_re_logDeriv_zeta_two :
    Continuous fun y : ℝ => (logDeriv riemannZeta ((2 : ℂ) + (y : ℂ) * I)).re := by
  refine Complex.continuous_re.comp (continuous_iff_continuousAt.mpr fun y => ?_)
  have hgt : 1 < ((2 : ℂ) + (y : ℂ) * I).re := by simp
  have hs1 : ((2 : ℂ) + (y : ℂ) * I) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have hne : riemannZeta ((2 : ℂ) + (y : ℂ) * I) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hgt
  have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hana : AnalyticOnNhd ℂ riemannZeta {z : ℂ | 1 < z.re} := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hopen
    refine (differentiableAt_riemannZeta ?_).differentiableWithinAt
    intro h
    rw [h] at hz
    simp at hz
  have hZ : AnalyticAt ℂ riemannZeta ((2 : ℂ) + (y : ℂ) * I) := hana _ hgt
  have hquot : AnalyticAt ℂ (fun z => deriv riemannZeta z / riemannZeta z)
      ((2 : ℂ) + (y : ℂ) * I) := hZ.deriv.div hZ hne
  have heq : logDeriv riemannZeta = fun z => deriv riemannZeta z / riemannZeta z := by
    funext z
    rw [logDeriv_apply]
  have hpath : ContinuousAt (fun u : ℝ => (2 : ℂ) + (u : ℂ) * I) y := by fun_prop
  rw [heq]
  exact ContinuousAt.comp (f := fun u : ℝ => (2 : ℂ) + (u : ℂ) * I) hquot.continuousAt hpath

/-! ## The integrated splitting -/

/-- **The vertical phase of `ξ` on the abscissa `2`.** -/
theorem integral_re_logDeriv_xi_two (T : ℝ) :
    (∫ y in (0 : ℝ)..T, (logDeriv xi ((2 : ℂ) + (y : ℂ) * I)).re)
      = (∫ y in (0 : ℝ)..T, (2 / (4 + y ^ 2) + 1 / (1 + y ^ 2)))
        - T * Real.log Real.pi / 2
        + gammaVerticalPhase 1 (T / 2)
        + ∫ y in (0 : ℝ)..T, (logDeriv riemannZeta ((2 : ℂ) + (y : ℂ) * I)).re := by
  have hc1 : Continuous fun y : ℝ => 2 / (4 + y ^ 2) + 1 / (1 + y ^ 2) := by
    have h1 : Continuous fun y : ℝ => 2 / (4 + y ^ 2) := by
      refine continuous_const.div (by fun_prop) fun y => ?_
      positivity
    have h2 : Continuous fun y : ℝ => 1 / (1 + y ^ 2) := by
      refine continuous_const.div (by fun_prop) fun y => ?_
      positivity
    exact h1.add h2
  have hcψ : Continuous fun y : ℝ =>
      (Complex.digamma ((1 : ℂ) + ((y / 2 : ℝ) : ℂ) * I)).re / 2 := by
    have h := (continuous_digammaVerticalRe (σ := 1) (by norm_num)).comp
      (continuous_id.div_const 2)
    exact h.div_const 2
  have hcζ := continuous_re_logDeriv_zeta_two
  have hsplit : (∫ y in (0 : ℝ)..T, (logDeriv xi ((2 : ℂ) + (y : ℂ) * I)).re)
      = (∫ y in (0 : ℝ)..T, ((2 / (4 + y ^ 2) + 1 / (1 + y ^ 2)) - Real.log Real.pi / 2
          + (Complex.digamma ((1 : ℂ) + ((y / 2 : ℝ) : ℂ) * I)).re / 2
          + (logDeriv riemannZeta ((2 : ℂ) + (y : ℂ) * I)).re)) := by
    refine intervalIntegral.integral_congr fun y _ => ?_
    exact re_logDeriv_xi_two_add y
  have e1 : (∫ y in (0 : ℝ)..T, ((2 / (4 + y ^ 2) + 1 / (1 + y ^ 2) - Real.log Real.pi / 2
        + (Complex.digamma ((1 : ℂ) + ((y / 2 : ℝ) : ℂ) * I)).re / 2)
        + (logDeriv riemannZeta ((2 : ℂ) + (y : ℂ) * I)).re))
      = (∫ y in (0 : ℝ)..T, (2 / (4 + y ^ 2) + 1 / (1 + y ^ 2) - Real.log Real.pi / 2
        + (Complex.digamma ((1 : ℂ) + ((y / 2 : ℝ) : ℂ) * I)).re / 2))
        + ∫ y in (0 : ℝ)..T, (logDeriv riemannZeta ((2 : ℂ) + (y : ℂ) * I)).re :=
    intervalIntegral.integral_add (((hc1.sub continuous_const).add hcψ).intervalIntegrable 0 T)
      (hcζ.intervalIntegrable 0 T)
  have e2 : (∫ y in (0 : ℝ)..T, ((2 / (4 + y ^ 2) + 1 / (1 + y ^ 2) - Real.log Real.pi / 2)
        + (Complex.digamma ((1 : ℂ) + ((y / 2 : ℝ) : ℂ) * I)).re / 2))
      = (∫ y in (0 : ℝ)..T, (2 / (4 + y ^ 2) + 1 / (1 + y ^ 2) - Real.log Real.pi / 2))
        + ∫ y in (0 : ℝ)..T, (Complex.digamma ((1 : ℂ) + ((y / 2 : ℝ) : ℂ) * I)).re / 2 :=
    intervalIntegral.integral_add ((hc1.sub continuous_const).intervalIntegrable 0 T)
      (hcψ.intervalIntegrable 0 T)
  have e3 : (∫ y in (0 : ℝ)..T, ((2 / (4 + y ^ 2) + 1 / (1 + y ^ 2)) - Real.log Real.pi / 2))
      = (∫ y in (0 : ℝ)..T, (2 / (4 + y ^ 2) + 1 / (1 + y ^ 2)))
        - ∫ _y in (0 : ℝ)..T, Real.log Real.pi / 2 :=
    intervalIntegral.integral_sub (hc1.intervalIntegrable 0 T)
      (continuous_const.intervalIntegrable 0 T)
  have hconst : (∫ _y in (0 : ℝ)..T, Real.log Real.pi / 2) = T * Real.log Real.pi / 2 := by
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    ring
  have hgamma : (∫ y in (0 : ℝ)..T,
      (Complex.digamma ((1 : ℂ) + ((y / 2 : ℝ) : ℂ) * I)).re / 2)
      = gammaVerticalPhase 1 (T / 2) := by
    rw [gammaVerticalPhase]
    have hsub := intervalIntegral.integral_comp_div
      (fun t : ℝ => (Complex.digamma ((1 : ℂ) + (t : ℂ) * I)).re / 2)
      (by norm_num : (2 : ℝ) ≠ 0) (a := 0) (b := T)
    rw [hsub]
    simp only [zero_div, smul_eq_mul]
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    have hpt : ((1 : ℝ) : ℂ) + (t : ℂ) * I = (1 : ℂ) + (t : ℂ) * I := by norm_num
    rw [hpt]
    ring
  rw [hsplit, e1, e2, e3, hconst, hgamma]

/-! ## The two bounded terms -/

theorem integral_rational_head (T : ℝ) :
    (∫ y in (0 : ℝ)..T, (2 / (4 + y ^ 2) + 1 / (1 + y ^ 2)))
      = Real.arctan (T / 2) + Real.arctan T := by
  have hc1 : Continuous fun y : ℝ => 2 / (4 + y ^ 2) := by
    refine continuous_const.div (by fun_prop) fun y => by positivity
  have hc2 : Continuous fun y : ℝ => 1 / (1 + y ^ 2) := by
    refine continuous_const.div (by fun_prop) fun y => by positivity
  rw [intervalIntegral.integral_add (hc1.intervalIntegrable 0 T) (hc2.intervalIntegrable 0 T)]
  have hsecond : (∫ y in (0 : ℝ)..T, 1 / (1 + y ^ 2)) = Real.arctan T := by
    rw [integral_one_div_one_add_sq, Real.arctan_zero, sub_zero]
  have hfirst : (∫ y in (0 : ℝ)..T, 2 / (4 + y ^ 2)) = Real.arctan (T / 2) := by
    have hsub := intervalIntegral.integral_comp_div
      (fun t : ℝ => 2 / (4 + (2 * t) ^ 2)) (by norm_num : (2 : ℝ) ≠ 0) (a := 0) (b := T)
    have hrw : (∫ y in (0 : ℝ)..T, 2 / (4 + y ^ 2))
        = ∫ y in (0 : ℝ)..T, 2 / (4 + (2 * (y / 2)) ^ 2) := by
      refine intervalIntegral.integral_congr fun y _ => ?_
      congr 2
      ring
    rw [hrw, hsub]
    simp only [zero_div, smul_eq_mul]
    have hval : (∫ t in (0 : ℝ)..(T / 2), 2 / (4 + (2 * t) ^ 2))
        = (1 / 2) * ∫ t in (0 : ℝ)..(T / 2), 1 / (1 + t ^ 2) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun t _ => ?_
      have hpos : (0 : ℝ) < 1 + t ^ 2 := by positivity
      field_simp
      ring
    rw [hval, integral_one_div_one_add_sq, Real.arctan_zero, sub_zero]
    ring
  rw [hfirst, hsecond]

theorem abs_integral_rational_head_le (T : ℝ) :
    |∫ y in (0 : ℝ)..T, (2 / (4 + y ^ 2) + 1 / (1 + y ^ 2))| ≤ Real.pi := by
  rw [integral_rational_head]
  have h1 := Real.arctan_lt_pi_div_two (T / 2)
  have h2 := Real.neg_pi_div_two_lt_arctan (T / 2)
  have h3 := Real.arctan_lt_pi_div_two T
  have h4 := Real.neg_pi_div_two_lt_arctan T
  rw [abs_le]
  constructor <;> linarith

/-! ## The zeta phase on the abscissa `2` -/

theorem hasDerivAt_log_zeta_two (y : ℝ) :
    HasDerivAt (fun u : ℝ => Complex.log (riemannZeta ((2 : ℂ) + (u : ℂ) * I)))
      ((riemannZeta ((2 : ℂ) + (y : ℂ) * I))⁻¹
        * (deriv riemannZeta ((2 : ℂ) + (y : ℂ) * I) * I)) y := by
  have hgt : 1 < ((2 : ℂ) + (y : ℂ) * I).re := by simp
  have hs1 : ((2 : ℂ) + (y : ℂ) * I) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have hslit : riemannZeta ((2 : ℂ) + (y : ℂ) * I) ∈ Complex.slitPlane := by
    refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
    have hcast : ((2 : ℂ) + (y : ℂ) * I) = ((2 : ℂ) + ((y : ℝ) : ℂ) * I) := rfl
    rw [hcast]
    exact re_riemannZeta_two_add_pos y
  have hpath : HasDerivAt (fun u : ℝ => (2 : ℂ) + (u : ℂ) * I) I y := by
    have h := ((Complex.ofRealCLM.hasDerivAt (x := y)).mul_const I).const_add (2 : ℂ)
    simpa using h
  have hz : HasDerivAt riemannZeta (deriv riemannZeta ((2 : ℂ) + (y : ℂ) * I))
      ((2 : ℂ) + (y : ℂ) * I) := (differentiableAt_riemannZeta hs1).hasDerivAt
  have hcomp : HasDerivAt (fun u : ℝ => riemannZeta ((2 : ℂ) + (u : ℂ) * I))
      (deriv riemannZeta ((2 : ℂ) + (y : ℂ) * I) * I) y := by
    have h := (hz.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt y hpath
    simpa [Function.comp_def, mul_comm] using h
  have hlog := ((Complex.hasDerivAt_log hslit).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt
    y hcomp
  simpa [Function.comp_def, mul_comm] using hlog

theorem abs_integral_re_logDeriv_zeta_two_le (T : ℝ) :
    |∫ y in (0 : ℝ)..T, (logDeriv riemannZeta ((2 : ℂ) + (y : ℂ) * I)).re| ≤ Real.pi := by
  have hderiv : ∀ y ∈ Set.uIcc (0 : ℝ) T,
      HasDerivAt (fun u : ℝ => (Complex.log (riemannZeta ((2 : ℂ) + (u : ℂ) * I))).im)
        ((logDeriv riemannZeta ((2 : ℂ) + (y : ℂ) * I)).re) y := by
    intro y _
    have h := hasDerivAt_log_zeta_two y
    have him := (Complex.imCLM.hasFDerivAt.comp_hasDerivAt y h)
    refine him.congr_deriv ?_
    simp only [Complex.imCLM_apply]
    rw [logDeriv_apply]
    have hzne : riemannZeta ((2 : ℂ) + (y : ℂ) * I) ≠ 0 := by
      have := re_riemannZeta_two_add_pos y
      intro hh
      rw [hh] at this
      simp at this
    set Z : ℂ := riemannZeta ((2 : ℂ) + (y : ℂ) * I) with hZ
    set D : ℂ := deriv riemannZeta ((2 : ℂ) + (y : ℂ) * I) with hD
    have hval : (Z⁻¹ * (D * I)).im = (D / Z).re := by
      rw [div_eq_mul_inv, mul_comm D Z⁻¹]
      rw [mul_comm (Z⁻¹) (D * I)]
      rw [mul_assoc]
      simp [Complex.mul_im, Complex.mul_re]
      ring
    exact hval
  have hcont : ContinuousOn
      (fun u : ℝ => (Complex.log (riemannZeta ((2 : ℂ) + (u : ℂ) * I))).im) (Set.uIcc 0 T) :=
    fun y hy => ((hderiv y hy).continuousAt).continuousWithinAt
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (continuous_re_logDeriv_zeta_two.intervalIntegrable 0 T)
  rw [hint]
  have harg : ∀ u : ℝ, |(Complex.log (riemannZeta ((2 : ℂ) + (u : ℂ) * I))).im| < Real.pi / 2 := by
    intro u
    rw [Complex.log_im]
    refine Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl ?_)
    exact re_riemannZeta_two_add_pos u
  have h1 := harg T
  have h2 := harg 0
  rw [abs_le] at *
  constructor <;> [skip; skip] <;>
    · rcases abs_lt.mp (harg T) with ⟨a1, a2⟩
      rcases abs_lt.mp (harg 0) with ⟨b1, b2⟩
      linarith

end RHTower
