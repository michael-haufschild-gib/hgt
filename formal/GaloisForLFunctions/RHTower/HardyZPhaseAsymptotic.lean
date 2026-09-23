import GaloisForLFunctions.RHTower.HardyZ
import GaloisForLFunctions.RHTower.HardyZThetaTrace
import GaloisForLFunctions.RHTower.DigammaVerticalLogAsymptotic
import GaloisForLFunctions.RHTower.TrigammaVertical
import GaloisForLFunctions.RHTower.WindingFloor

/-!
# The global Riemann--Siegel phase and its asymptotic velocity

The normalized Gamma phase underlying `hardyZ` has the exact logarithmic velocity
`gammaHardyPhaseRate`.  Integrating this real rate gives a global, branch-free phase lift
`gammaHardyTheta`; the original unitary phase is reconstructed from this lift up to its fixed
central orientation.

The existing vertical digamma and trigamma estimates then give the classical first-order law

`gammaHardyPhaseRate(t) = (1/2) log(t / (2*pi)) + o(1)`.

Here the error is bounded explicitly by `33/(16*t^(2 : ℕ)) + pi/(2*t)`, while the exact second jet is
the imaginary part of trigamma and has an unconditional `O(1/t)` bound.  Consequently the rate
tends to infinity and is eventually positive.  These statements close the archimedean phase and
first-derivative interfaces needed by future Riemann--Siegel and symmetric
approximate-functional-equation arguments.  They make no assertion about zeta zeros.
-/

noncomputable section

open Complex Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- The exact normalized-Gamma phase velocity is continuous on the whole real line. -/
theorem continuous_gammaHardyPhaseRate : Continuous gammaHardyPhaseRate := by
  have hdigamma : Continuous fun τ : ℝ => Complex.digamma (linePt τ / 2) := by
    rw [continuous_iff_continuousAt]
    intro τ
    have harg : 0 < (linePt τ / 2).re := by
      rw [re_div_two, linePt_re]
      norm_num
    have hinner : ContinuousAt (fun u : ℝ => linePt u / 2) τ :=
      (hasDerivAt_linePt τ).continuousAt.div_const 2
    exact ContinuousAt.comp (f := fun u : ℝ => linePt u / 2)
      (digamma_analyticOnNhd_re_pos _ harg).continuousAt hinner
  unfold gammaHardyPhaseRate
  exact ((Complex.continuous_re.comp hdigamma).div_const 2).sub continuous_const

/-- **Exact second-jet law for the global Gamma phase.**  The derivative of the phase velocity is
the negative imaginary part of trigamma at the quarter-shifted critical-line argument. -/
theorem hasDerivAt_gammaHardyPhaseRate (t : ℝ) :
    HasDerivAt gammaHardyPhaseRate
      (-(deriv Complex.digamma (linePt t / 2)).im / 4) t := by
  have hpos : 0 < (linePt t / 2).re := by
    rw [re_div_two, linePt_re]
    norm_num
  have houter := (digamma_analyticOnNhd_re_pos _ hpos).differentiableAt.hasDerivAt
  have hinner : HasDerivAt (fun u : ℝ => linePt u / 2) (I / 2) t :=
    (hasDerivAt_linePt t).div_const 2
  have hcomp := (houter.hasFDerivAt.restrictScalars ℝ).comp t hinner.hasFDerivAt
  have hpsi : HasDerivAt (fun u : ℝ => Complex.digamma (linePt u / 2))
      (deriv Complex.digamma (linePt t / 2) * (I / 2)) t := by
    simpa [Function.comp_def, mul_comm] using hcomp.hasDerivAt
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hpsi
  have hre' : HasDerivAt
      (fun u : ℝ => (Complex.digamma (linePt u / 2)).re)
      (deriv Complex.digamma (linePt t / 2) * (I / 2)).re t := by
    simpa only [Function.comp_apply] using! hre
  have hcoeff :
      (deriv Complex.digamma (linePt t / 2) * (I / 2)).re / 2 =
        -(deriv Complex.digamma (linePt t / 2)).im / 4 := by
    rw [Complex.mul_re]
    simp
    ring
  simpa only [gammaHardyPhaseRate, hcoeff] using!
    (hre'.div_const 2).sub_const (Real.log Real.pi / 2)

/-- The exact derivative form of the second-jet law. -/
theorem deriv_gammaHardyPhaseRate (t : ℝ) :
    deriv gammaHardyPhaseRate t = -(deriv Complex.digamma (linePt t / 2)).im / 4 :=
  (hasDerivAt_gammaHardyPhaseRate t).deriv

/-- The exact Gamma phase velocity is differentiable on the whole real line. -/
theorem differentiable_gammaHardyPhaseRate : Differentiable ℝ gammaHardyPhaseRate :=
  fun t => (hasDerivAt_gammaHardyPhaseRate t).differentiableAt

/-- The exact Gamma phase velocity has strictly positive derivative at every positive height. -/
theorem deriv_gammaHardyPhaseRate_pos {t : ℝ} (ht : 0 < t) :
    0 < deriv gammaHardyPhaseRate t := by
  rw [deriv_gammaHardyPhaseRate]
  have harg : linePt t / 2 = ((1 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I := by
    unfold linePt
    push_cast
    ring
  rw [harg]
  exact div_pos (neg_pos.mpr (deriv_digamma_vertical_im_neg
    (show (0 : ℝ) < 1 / 4 by norm_num) (half_pos ht))) (by norm_num)

/-- The derivative of the even Gamma phase velocity is odd. -/
@[simp] theorem deriv_gammaHardyPhaseRate_neg (t : ℝ) :
    deriv gammaHardyPhaseRate (-t) = -deriv gammaHardyPhaseRate t := by
  have houter : HasDerivAt gammaHardyPhaseRate (deriv gammaHardyPhaseRate (-t)) (-t) :=
    (hasDerivAt_gammaHardyPhaseRate (-t)).differentiableAt.hasDerivAt
  have hcomp : HasDerivAt (fun x : ℝ => gammaHardyPhaseRate (-x))
      (-deriv gammaHardyPhaseRate (-t)) t := by
    simpa only [Function.comp_def, mul_neg, mul_one] using
      houter.comp t (hasDerivAt_id t).neg
  have heq : (fun x : ℝ => gammaHardyPhaseRate (-x)) = gammaHardyPhaseRate :=
    funext gammaHardyPhaseRate_neg
  rw [heq] at hcomp
  have hbase : HasDerivAt gammaHardyPhaseRate (deriv gammaHardyPhaseRate t) t :=
    (hasDerivAt_gammaHardyPhaseRate t).differentiableAt.hasDerivAt
  have hu := hcomp.unique hbase
  linarith

/-- The exact Gamma phase velocity has strictly negative derivative at every negative height. -/
theorem deriv_gammaHardyPhaseRate_neg_of_neg {t : ℝ} (ht : t < 0) :
    deriv gammaHardyPhaseRate t < 0 := by
  have hpos := deriv_gammaHardyPhaseRate_pos (neg_pos.mpr ht)
  rw [← neg_neg t, deriv_gammaHardyPhaseRate_neg]
  linarith

/-- The derivative of the exact Gamma phase velocity vanishes at the reflection centre. -/
@[simp] theorem deriv_gammaHardyPhaseRate_zero : deriv gammaHardyPhaseRate 0 = 0 := by
  have h := deriv_gammaHardyPhaseRate_neg 0
  norm_num at h ⊢
  linarith

/-- The exact Gamma phase velocity is strictly increasing on the nonnegative half-line. -/
theorem strictMonoOn_gammaHardyPhaseRate :
    StrictMonoOn gammaHardyPhaseRate (Set.Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0)
  · intro x _
    exact (hasDerivAt_gammaHardyPhaseRate x).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici, Set.mem_Ioi] at hx
    exact deriv_gammaHardyPhaseRate_pos hx

/-- The exact Gamma phase velocity is strictly decreasing toward the reflection centre on the
nonpositive half-line. -/
theorem strictAntiOn_gammaHardyPhaseRate :
    StrictAntiOn gammaHardyPhaseRate (Set.Iic 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Iic 0)
  · intro x _
    exact (hasDerivAt_gammaHardyPhaseRate x).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Iic, Set.mem_Iio] at hx
    exact deriv_gammaHardyPhaseRate_neg_of_neg hx

/-- The reflection centre is the unique global minimum of the exact Gamma phase velocity. -/
theorem gammaHardyPhaseRate_zero_lt {t : ℝ} (ht : t ≠ 0) :
    gammaHardyPhaseRate 0 < gammaHardyPhaseRate t := by
  rcases lt_or_gt_of_ne ht with htneg | htpos
  · have h := strictMonoOn_gammaHardyPhaseRate
      (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr (neg_nonneg.mpr htneg.le))
      (neg_pos.mpr htneg)
    simpa using h
  · exact strictMonoOn_gammaHardyPhaseRate
      (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr htpos.le) htpos

/-- Equality with the central phase velocity detects the reflection centre exactly. -/
theorem gammaHardyPhaseRate_eq_zero_value_iff {t : ℝ} :
    gammaHardyPhaseRate t = gammaHardyPhaseRate 0 ↔ t = 0 := by
  constructor
  · intro h
    by_contra ht
    linarith [gammaHardyPhaseRate_zero_lt ht]
  · rintro rfl
    rfl

/-- **Central orientation law.**  The exact Gamma phase velocity is negative at the reflection
centre.  This is symbolic: strict positive-real monotonicity of `Re ψ` compares the quarter
argument with `ψ(1) = -γ`, while `γ > 1/2` and `log π > 0`. -/
theorem gammaHardyPhaseRate_zero_neg : gammaHardyPhaseRate 0 < 0 := by
  have hquarter := strictMonoOn_re_digamma_ofReal
    (show (1 / 4 : ℝ) ∈ Set.Ioi 0 by norm_num)
    (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)
    (show (1 / 4 : ℝ) < 1 by norm_num)
  have hone : (Complex.digamma (1 : ℂ)).re = -Real.eulerMascheroniConstant := by
    rw [Complex.digamma_one]
    simp
  have hgamma : 0 < Real.eulerMascheroniConstant :=
    lt_trans (by norm_num : (0 : ℝ) < 1 / 2) Real.one_half_lt_eulerMascheroniConstant
  have hlog : 0 < Real.log Real.pi := Real.log_pos (by linarith [Real.pi_gt_three])
  have hline : linePt 0 / 2 = ((1 / 4 : ℝ) : ℂ) := by
    unfold linePt
    norm_num
  unfold gammaHardyPhaseRate
  rw [hline]
  change (Complex.digamma (((1 / 4 : ℝ) : ℂ))).re <
    (Complex.digamma (1 : ℂ)).re at hquarter
  rw [hone] at hquarter
  linarith

/-- The global branch-free Riemann--Siegel phase obtained by integrating the exact Gamma phase
velocity from the reflection centre. -/
noncomputable def gammaHardyTheta (τ : ℝ) : ℝ :=
  ∫ u in 0..τ, gammaHardyPhaseRate u

/-- The derivative of the global phase lift is exactly the normalized-Gamma phase rate. -/
theorem hasDerivAt_gammaHardyTheta (τ : ℝ) :
    HasDerivAt gammaHardyTheta (gammaHardyPhaseRate τ) τ :=
  (continuous_gammaHardyPhaseRate.integral_hasStrictDerivAt 0 τ).hasDerivAt

/-- The derivative of the global phase lift, as a value relation. -/
@[simp] theorem deriv_gammaHardyTheta (τ : ℝ) :
    deriv gammaHardyTheta τ = gammaHardyPhaseRate τ :=
  (hasDerivAt_gammaHardyTheta τ).deriv

/-- The exact second derivative of the global phase lift. -/
theorem deriv_deriv_gammaHardyTheta (τ : ℝ) :
    deriv (deriv gammaHardyTheta) τ =
      -(deriv Complex.digamma (linePt τ / 2)).im / 4 := by
  have hfun : deriv gammaHardyTheta = gammaHardyPhaseRate :=
    funext deriv_gammaHardyTheta
  rw [hfun, deriv_gammaHardyPhaseRate]

/-- The global Riemann--Siegel phase lift is differentiable. -/
theorem differentiable_gammaHardyTheta : Differentiable ℝ gammaHardyTheta :=
  fun τ => (hasDerivAt_gammaHardyTheta τ).differentiableAt

/-- The global phase lift is odd because its velocity is even. -/
@[simp] theorem gammaHardyTheta_neg (τ : ℝ) :
    gammaHardyTheta (-τ) = -gammaHardyTheta τ := by
  unfold gammaHardyTheta
  calc
    (∫ u in 0..-τ, gammaHardyPhaseRate u) =
        ∫ u in τ..0, gammaHardyPhaseRate (-u) := by
          simpa only [neg_zero] using (intervalIntegral.integral_comp_neg
            (f := gammaHardyPhaseRate) (a := τ) (b := 0)).symm
    _ = ∫ u in τ..0, gammaHardyPhaseRate u := by
      apply intervalIntegral.integral_congr
      intro u _
      exact gammaHardyPhaseRate_neg u
    _ = -(∫ u in 0..τ, gammaHardyPhaseRate u) :=
      intervalIntegral.integral_symm 0 τ

/-- Prop interface for oddness of the global Riemann--Siegel phase lift. -/
theorem odd_gammaHardyTheta : Function.Odd gammaHardyTheta := gammaHardyTheta_neg

/-- The global branch-free phase is strictly convex on the nonnegative half-line. -/
theorem strictConvexOn_gammaHardyTheta :
    StrictConvexOn ℝ (Set.Ici 0) gammaHardyTheta := by
  have hmono : StrictMonoOn (deriv gammaHardyTheta) (interior (Set.Ici 0)) := by
    rw [interior_Ici]
    intro x hx y hy hxy
    rw [deriv_gammaHardyTheta, deriv_gammaHardyTheta]
    exact strictMonoOn_gammaHardyPhaseRate
      (Set.mem_Ici.mpr hx.le) (Set.mem_Ici.mpr hy.le) hxy
  exact hmono.strictConvexOn_of_deriv (convex_Ici 0)
    differentiable_gammaHardyTheta.continuous.continuousOn

/-- By reflection, the global branch-free phase is strictly concave on the nonpositive
half-line. -/
theorem strictConcaveOn_gammaHardyTheta :
    StrictConcaveOn ℝ (Set.Iic 0) gammaHardyTheta := by
  have hanti : StrictAntiOn (deriv gammaHardyTheta) (interior (Set.Iic 0)) := by
    rw [interior_Iic]
    intro x hx y hy hxy
    rw [deriv_gammaHardyTheta, deriv_gammaHardyTheta]
    exact strictAntiOn_gammaHardyPhaseRate
      (Set.mem_Iic.mpr hx.le) (Set.mem_Iic.mpr hy.le) hxy
  exact hanti.strictConcaveOn_of_deriv (convex_Iic 0)
    differentiable_gammaHardyTheta.continuous.continuousOn

/-- **Archimedean winding/Hardy-phase identification.**  The older envelope winding rate and the
exact normalized-Gamma phase velocity are the same real function. -/
theorem windingRate_eq_gammaHardyPhaseRate (t : ℝ) :
    windingRate t = gammaHardyPhaseRate t := by
  rw [windingRate_eq]
  rfl

/-- The envelope winding primitive based at the reflection centre is exactly the global
Riemann--Siegel phase lift. -/
theorem windingPhase_zero_eq_gammaHardyTheta (t : ℝ) :
    windingPhase 0 t = gammaHardyTheta t := by
  unfold windingPhase gammaHardyTheta
  apply intervalIntegral.integral_congr
  intro u _
  exact windingRate_eq_gammaHardyPhaseRate u

/-- The curvature datum of the envelope winding is exactly the derivative of the normalized-Gamma
phase velocity. -/
theorem windingRateDeriv_eq_deriv_gammaHardyPhaseRate (t : ℝ) :
    windingRateDeriv t = deriv gammaHardyPhaseRate t := by
  have hfun : windingRate = gammaHardyPhaseRate :=
    funext windingRate_eq_gammaHardyPhaseRate
  have hwind := hasDerivAt_windingRate t
  rw [hfun] at hwind
  exact hwind.unique
    (hasDerivAt_gammaHardyPhaseRate t).differentiableAt.hasDerivAt

/-- The central Gamma phase has positive real orientation.  This discharges the constant phase
left undetermined by integrating the logarithmic velocity. -/
@[simp] theorem gammaHardyPhase_zero : gammaHardyPhase 0 = 1 := by
  have hline : linePt 0 = ((1 / 2 : ℝ) : ℂ) := by
    unfold linePt
    norm_num
  let g : ℝ := Real.pi ^ (-(1 / 4 : ℝ)) * Real.Gamma (1 / 4)
  have hg : 0 < g := mul_pos (Real.rpow_pos_of_pos Real.pi_pos _)
    (Real.Gamma_pos_of_pos (by norm_num))
  have hG : Gammaℝ (((1 / 2 : ℝ) : ℂ)) = (g : ℂ) := by
    rw [Complex.Gammaℝ_def]
    have hexp : -(((1 / 2 : ℝ) : ℂ)) / 2 = (-(1 / 4 : ℝ) : ℂ) := by
      push_cast
      ring
    have harg : (((1 / 2 : ℝ) : ℂ)) / 2 = ((1 / 4 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hexp, harg, ← Complex.ofReal_neg,
      ← Complex.ofReal_cpow Real.pi_pos.le, Complex.Gamma_ofReal]
    exact_mod_cast rfl
  unfold gammaHardyPhase
  rw [hline, hG]
  simp [Real.norm_eq_abs, abs_of_pos hg, hg.ne']

private noncomputable def gammaHardyPhaseGauge (τ : ℝ) : ℂ :=
  gammaHardyPhase τ * Complex.exp (I * (gammaHardyTheta τ : ℂ))

private theorem hasDerivAt_gammaHardyPhaseGauge (τ : ℝ) :
    HasDerivAt gammaHardyPhaseGauge 0 τ := by
  have hthetaC : HasDerivAt (fun u : ℝ => (gammaHardyTheta u : ℂ))
      (gammaHardyPhaseRate τ : ℂ) τ := by
    simpa using! Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt τ
      (hasDerivAt_gammaHardyTheta τ)
  have hinner : HasDerivAt (fun u : ℝ => I * (gammaHardyTheta u : ℂ))
      (I * (gammaHardyPhaseRate τ : ℂ)) τ := hthetaC.const_mul I
  have hexp := hinner.cexp
  have hprod := (hasDerivAt_gammaHardyPhase τ).mul hexp
  have hprod' : HasDerivAt
      (fun u : ℝ =>
        gammaHardyPhase u * Complex.exp (I * (gammaHardyTheta u : ℂ)))
      ((-I * (gammaHardyPhaseRate τ : ℂ)) * gammaHardyPhase τ *
          Complex.exp (I * (gammaHardyTheta τ : ℂ)) +
        gammaHardyPhase τ *
          (Complex.exp (I * (gammaHardyTheta τ : ℂ)) *
            (I * (gammaHardyPhaseRate τ : ℂ)))) τ := by
    simpa only [Pi.mul_apply] using! hprod
  unfold gammaHardyPhaseGauge
  convert hprod' using 1
  ring

private theorem differentiable_gammaHardyPhaseGauge :
    Differentiable ℝ gammaHardyPhaseGauge :=
  fun τ => (hasDerivAt_gammaHardyPhaseGauge τ).differentiableAt

/-- **Exact global phase-gauge law.**  Multiplying the normalized Gamma phase by the positive
orientation character of its integrated real velocity leaves its central value. -/
theorem gammaHardyPhase_mul_exp_theta (τ : ℝ) :
    gammaHardyPhase τ * Complex.exp (I * (gammaHardyTheta τ : ℂ)) =
      gammaHardyPhase 0 := by
  have hconst := is_const_of_deriv_eq_zero differentiable_gammaHardyPhaseGauge
    (fun u => (hasDerivAt_gammaHardyPhaseGauge u).deriv) τ 0
  simpa [gammaHardyPhaseGauge, gammaHardyTheta] using hconst

/-- **Global branch-free phase reconstruction.**  The normalized Gamma phase is its fixed central
orientation times the exponential of the negative integrated Riemann--Siegel phase. -/
theorem gammaHardyPhase_eq_central_mul_exp_neg_theta (τ : ℝ) :
    gammaHardyPhase τ = gammaHardyPhase 0 *
      Complex.exp (-I * (gammaHardyTheta τ : ℂ)) := by
  have hgauge := gammaHardyPhase_mul_exp_theta τ
  have hexp : Complex.exp (I * (gammaHardyTheta τ : ℂ)) *
      Complex.exp (-I * (gammaHardyTheta τ : ℂ)) = 1 := by
    rw [← Complex.exp_add]
    convert Complex.exp_zero
    ring
  calc
    gammaHardyPhase τ = gammaHardyPhase τ * 1 := by ring
    _ = gammaHardyPhase τ *
        (Complex.exp (I * (gammaHardyTheta τ : ℂ)) *
          Complex.exp (-I * (gammaHardyTheta τ : ℂ))) := by rw [hexp]
    _ = (gammaHardyPhase τ * Complex.exp (I * (gammaHardyTheta τ : ℂ))) *
          Complex.exp (-I * (gammaHardyTheta τ : ℂ)) := by ring
    _ = gammaHardyPhase 0 * Complex.exp (-I * (gammaHardyTheta τ : ℂ)) := by
      rw [hgauge]

/-- **Exact global Gamma phase lift.**  Positivity at the reflection centre fixes the integrated
phase orientation, so no residual unit scalar remains. -/
theorem gammaHardyPhase_eq_exp_neg_theta (τ : ℝ) :
    gammaHardyPhase τ = Complex.exp (-I * (gammaHardyTheta τ : ℂ)) := by
  rw [gammaHardyPhase_eq_central_mul_exp_neg_theta, gammaHardyPhase_zero, one_mul]

/-- **Global exponential normal form.**  Every value reflected by the critical-line Gamma phase
is the negative phase exponential times its canonical real amplitude.  This single law applies
to zeta, finite Riemann--Siegel carriers, and symmetrized Euler--Maclaurin carriers. -/
theorem gammaPhaseReflected_eq_exp_neg_theta_mul_amplitude {τ : ℝ} {z : ℂ}
    (hz : IsPhaseReflected (gammaHardyPhase τ) z) :
    z = Complex.exp (-I * (gammaHardyTheta τ : ℂ)) *
      (phaseHalvedAmplitude (gammaHardyPhase τ) z : ℂ) := by
  calc
    z = gammaHardyPhase τ *
        (phaseHalvedAmplitude (gammaHardyPhase τ) z : ℂ) :=
      hz.eq_phase_mul_amplitude (gammaHardyPhase_isUnitary τ)
    _ = Complex.exp (-I * (gammaHardyTheta τ : ℂ)) *
        (phaseHalvedAmplitude (gammaHardyPhase τ) z : ℂ) := by
      congr 1
      exact gammaHardyPhase_eq_exp_neg_theta τ

/-- **Global phase-unwinding law.**  Multiplication by the positive phase exponential identifies
every Gamma-reflected complex value with its canonical embedded real amplitude. -/
theorem exp_theta_mul_gammaPhaseReflected_eq_amplitude {τ : ℝ} {z : ℂ}
    (hz : IsPhaseReflected (gammaHardyPhase τ) z) :
    Complex.exp (I * (gammaHardyTheta τ : ℂ)) * z =
      (phaseHalvedAmplitude (gammaHardyPhase τ) z : ℂ) := by
  have hvalue := gammaPhaseReflected_eq_exp_neg_theta_mul_amplitude hz
  calc
    Complex.exp (I * (gammaHardyTheta τ : ℂ)) * z =
        Complex.exp (I * (gammaHardyTheta τ : ℂ)) *
          (Complex.exp (-I * (gammaHardyTheta τ : ℂ)) *
            (phaseHalvedAmplitude (gammaHardyPhase τ) z : ℂ)) :=
      congrArg (fun w => Complex.exp (I * (gammaHardyTheta τ : ℂ)) * w) hvalue
    _ = (phaseHalvedAmplitude (gammaHardyPhase τ) z : ℂ) := by
      rw [← mul_assoc, ← Complex.exp_add]
      have hsum : I * (gammaHardyTheta τ : ℂ) +
          -I * (gammaHardyTheta τ : ℂ) = 0 := by ring
      rw [hsum, Complex.exp_zero, one_mul]

/-- **Classical branch-free Hardy-Z representation of zeta on the critical line.** -/
theorem riemannZeta_line_eq_exp_neg_theta_mul_hardyZ (τ : ℝ) :
    riemannZeta (linePt τ) =
      Complex.exp (-I * (gammaHardyTheta τ : ℂ)) * (hardyZ τ : ℂ) := by
  simpa [hardyZ] using gammaPhaseReflected_eq_exp_neg_theta_mul_amplitude
    (riemannZeta_line_isPhaseReflected τ)

/-- Unwinding the global phase of critical-line zeta yields Hardy Z exactly. -/
theorem exp_theta_mul_riemannZeta_line_eq_hardyZ (τ : ℝ) :
    Complex.exp (I * (gammaHardyTheta τ : ℂ)) * riemannZeta (linePt τ) =
      (hardyZ τ : ℂ) := by
  simpa [hardyZ] using exp_theta_mul_gammaPhaseReflected_eq_amplitude
    (riemannZeta_line_isPhaseReflected τ)

/-- The continuously oriented finite Riemann--Siegel carrier has the same exact phase lift as
zeta; all approximation error therefore lies in the real amplitude. -/
theorem gN_line_eq_exp_neg_theta_mul_gammaHardyCarrier (N : ℕ) (τ : ℝ) :
    gN N (linePt τ) = Complex.exp (-I * (gammaHardyTheta τ : ℂ)) *
      (gammaHardyCarrier N τ : ℂ) := by
  simpa [gammaHardyCarrier] using gammaPhaseReflected_eq_exp_neg_theta_mul_amplitude
    (gN_line_isGammaPhaseReflected N τ)

/-- The symmetrized Euler--Maclaurin carrier shares zeta's exact global phase; its normalization
targets twice the real Hardy value. -/
theorem semCarrier_line_eq_exp_neg_theta_mul_two_hardySEM (N : ℕ) (τ : ℝ) :
    semCarrier N (linePt τ) = Complex.exp (-I * (gammaHardyTheta τ : ℂ)) *
      (2 * hardySEM N τ : ℝ) := by
  rw [semCarrier_line_eq_two_mul_gammaHardyPhase_mul_hardySEM,
    gammaHardyPhase_eq_exp_neg_theta]

/-! ## First-jet normal forms and zero interfaces -/

/-- **Global first-jet exponential normal form.**  For every differentiable path carrying the
critical-line Gamma reflection, its complex derivative splits into the derivative of its canonical
real amplitude and the exact phase-velocity term.  This is the differential law shared by zeta and
all differentiable finite carriers. -/
theorem deriv_gammaPhaseReflected_eq_exp_neg_theta_mul
    {z : ℝ → ℂ} (hz : ∀ u, IsPhaseReflected (gammaHardyPhase u) (z u))
    (hdiff : Differentiable ℝ z) (t : ℝ) :
    deriv z t = Complex.exp (-I * (gammaHardyTheta t : ℂ)) *
      (((deriv (fun u => phaseHalvedAmplitude (gammaHardyPhase u) (z u)) t : ℝ) : ℂ) -
        I * (gammaHardyPhaseRate t : ℂ) *
          (phaseHalvedAmplitude (gammaHardyPhase t) (z t) : ℂ)) := by
  let A : ℝ → ℝ := fun u => phaseHalvedAmplitude (gammaHardyPhase u) (z u)
  have hA : Differentiable ℝ A :=
    differentiable_phaseHalvedAmplitude differentiable_gammaHardyPhase hdiff
  have hAC : HasDerivAt (fun u : ℝ => (A u : ℂ)) ((deriv A t : ℝ) : ℂ) t := by
    simpa using! Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t (hA t).hasDerivAt
  have hprod := (hasDerivAt_gammaHardyPhase t).mul hAC
  have hprod' : HasDerivAt (fun u => gammaHardyPhase u * (A u : ℂ))
      ((-I * (gammaHardyPhaseRate t : ℂ)) * gammaHardyPhase t * (A t : ℂ) +
        gammaHardyPhase t * ((deriv A t : ℝ) : ℂ)) t := by
    simpa only [Pi.mul_apply] using! hprod
  have hfun : z = fun u => gammaHardyPhase u * (A u : ℂ) := by
    funext u
    exact (hz u).eq_phase_mul_amplitude (gammaHardyPhase_isUnitary u)
  have hderiv := congrArg (fun f : ℝ → ℂ => deriv f t) hfun
  change deriv z t = deriv (fun u => gammaHardyPhase u * (A u : ℂ)) t at hderiv
  rw [hprod'.deriv] at hderiv
  change deriv z t = Complex.exp (-I * (gammaHardyTheta t : ℂ)) *
    (((deriv A t : ℝ) : ℂ) - I * (gammaHardyPhaseRate t : ℂ) * (A t : ℂ))
  calc
    deriv z t = (-I * (gammaHardyPhaseRate t : ℂ)) * gammaHardyPhase t * (A t : ℂ) +
        gammaHardyPhase t * ((deriv A t : ℝ) : ℂ) := hderiv
    _ = gammaHardyPhase t * (((deriv A t : ℝ) : ℂ) -
        I * (gammaHardyPhaseRate t : ℂ) * (A t : ℂ)) := by ring
    _ = Complex.exp (-I * (gammaHardyTheta t : ℂ)) *
        (((deriv A t : ℝ) : ℂ) -
          I * (gammaHardyPhaseRate t : ℂ) * (A t : ℂ)) := by
      rw [gammaHardyPhase_eq_exp_neg_theta]

/-- Unwinding the global phase identifies the complex first jet with the real amplitude jet plus
the single imaginary phase-velocity component. -/
theorem exp_theta_mul_deriv_gammaPhaseReflected_eq
    {z : ℝ → ℂ} (hz : ∀ u, IsPhaseReflected (gammaHardyPhase u) (z u))
    (hdiff : Differentiable ℝ z) (t : ℝ) :
    Complex.exp (I * (gammaHardyTheta t : ℂ)) * deriv z t =
      (((deriv (fun u => phaseHalvedAmplitude (gammaHardyPhase u) (z u)) t : ℝ) : ℂ) -
        I * (gammaHardyPhaseRate t : ℂ) *
          (phaseHalvedAmplitude (gammaHardyPhase t) (z t) : ℂ)) := by
  rw [deriv_gammaPhaseReflected_eq_exp_neg_theta_mul hz hdiff, ← mul_assoc,
    ← Complex.exp_add]
  have hsum : I * (gammaHardyTheta t : ℂ) + -I * (gammaHardyTheta t : ℂ) = 0 := by
    ring
  rw [hsum, Complex.exp_zero, one_mul]

/-- The real component of the unwound first jet is exactly the real-amplitude derivative. -/
theorem re_exp_theta_mul_deriv_gammaPhaseReflected_eq_amplitude_deriv
    {z : ℝ → ℂ} (hz : ∀ u, IsPhaseReflected (gammaHardyPhase u) (z u))
    (hdiff : Differentiable ℝ z) (t : ℝ) :
    (Complex.exp (I * (gammaHardyTheta t : ℂ)) * deriv z t).re =
      deriv (fun u => phaseHalvedAmplitude (gammaHardyPhase u) (z u)) t := by
  rw [exp_theta_mul_deriv_gammaPhaseReflected_eq hz hdiff]
  simp

/-- The imaginary component of the unwound first jet is exactly minus phase velocity times real
amplitude. -/
theorem im_exp_theta_mul_deriv_gammaPhaseReflected_eq_neg_rate_mul_amplitude
    {z : ℝ → ℂ} (hz : ∀ u, IsPhaseReflected (gammaHardyPhase u) (z u))
    (hdiff : Differentiable ℝ z) (t : ℝ) :
    (Complex.exp (I * (gammaHardyTheta t : ℂ)) * deriv z t).im =
      -gammaHardyPhaseRate t * phaseHalvedAmplitude (gammaHardyPhase t) (z t) := by
  rw [exp_theta_mul_deriv_gammaPhaseReflected_eq hz hdiff]
  simp

/-- **First-jet zero interface.**  At a zero of any differentiable Gamma-reflected path, its
complex derivative vanishes exactly when the derivative of its canonical real amplitude
vanishes.  The phase-velocity term disappears automatically at the zero. -/
theorem deriv_gammaPhaseReflected_eq_zero_iff_amplitude_deriv_of_zero
    {z : ℝ → ℂ} (hz : ∀ u, IsPhaseReflected (gammaHardyPhase u) (z u))
    (hdiff : Differentiable ℝ z) {t : ℝ} (hzero : z t = 0) :
    deriv z t = 0 ↔
      deriv (fun u => phaseHalvedAmplitude (gammaHardyPhase u) (z u)) t = 0 := by
  have hAzero : phaseHalvedAmplitude (gammaHardyPhase t) (z t) = 0 :=
    ((hz t).eq_zero_iff_amplitude_eq_zero (gammaHardyPhase_isUnitary t)).mp hzero
  have hvalue := exp_theta_mul_deriv_gammaPhaseReflected_eq hz hdiff t
  rw [hAzero] at hvalue
  simp only [ofReal_zero, mul_zero, sub_zero] at hvalue
  constructor
  · intro h
    rw [h, mul_zero] at hvalue
    exact_mod_cast hvalue.symm
  · intro h
    rw [h, ofReal_zero] at hvalue
    exact (mul_eq_zero.mp hvalue).resolve_left (Complex.exp_ne_zero _)

/-- The finite Riemann--Siegel carriers instantiate the same rotating-frame first-jet law. -/
theorem exp_theta_mul_deriv_gN_line (N : ℕ) (t : ℝ) :
    Complex.exp (I * (gammaHardyTheta t : ℂ)) *
        deriv (fun u : ℝ => gN N (linePt u)) t =
      ((deriv (gammaHardyCarrier N) t : ℝ) : ℂ) -
        I * (gammaHardyPhaseRate t : ℂ) * (gammaHardyCarrier N t : ℂ) := by
  change Complex.exp (I * (gammaHardyTheta t : ℂ)) *
        deriv (fun u : ℝ => gN N (linePt u)) t =
      ((deriv (fun u => phaseHalvedAmplitude (gammaHardyPhase u)
        (gN N (linePt u))) t : ℝ) : ℂ) -
        I * (gammaHardyPhaseRate t : ℂ) *
          (phaseHalvedAmplitude (gammaHardyPhase t) (gN N (linePt t)) : ℂ)
  exact exp_theta_mul_deriv_gammaPhaseReflected_eq
    (fun u => gN_line_isGammaPhaseReflected N u) (differentiable_gN_line N) t

/-- At a finite carrier zero, complex transversality is exactly real-amplitude transversality. -/
theorem deriv_gN_line_eq_zero_iff_deriv_gammaHardyCarrier_of_zero
    {N : ℕ} {t : ℝ} (hzero : gN N (linePt t) = 0) :
    deriv (fun u : ℝ => gN N (linePt u)) t = 0 ↔
      deriv (gammaHardyCarrier N) t = 0 :=
  deriv_gammaPhaseReflected_eq_zero_iff_amplitude_deriv_of_zero
    (fun u => gN_line_isGammaPhaseReflected N u) (differentiable_gN_line N) hzero

/-- The exact rotating-frame first jet of zeta on the critical line. -/
theorem exp_theta_mul_deriv_riemannZeta_line (t : ℝ) :
    Complex.exp (I * (gammaHardyTheta t : ℂ)) *
        deriv (fun u : ℝ => riemannZeta (linePt u)) t =
      ((deriv hardyZ t : ℝ) : ℂ) -
        I * (gammaHardyPhaseRate t : ℂ) * (hardyZ t : ℂ) := by
  change Complex.exp (I * (gammaHardyTheta t : ℂ)) *
        deriv (fun u : ℝ => riemannZeta (linePt u)) t =
      ((deriv (fun u => phaseHalvedAmplitude (gammaHardyPhase u)
        (riemannZeta (linePt u))) t : ℝ) : ℂ) -
        I * (gammaHardyPhaseRate t : ℂ) *
          (phaseHalvedAmplitude (gammaHardyPhase t) (riemannZeta (linePt t)) : ℂ)
  exact exp_theta_mul_deriv_gammaPhaseReflected_eq
    (fun u => riemannZeta_line_isPhaseReflected u) differentiable_riemannZeta_line t

/-- The real component of the rotating-frame zeta height derivative is Hardy Z prime. -/
theorem re_exp_theta_mul_deriv_riemannZeta_line (t : ℝ) :
    (Complex.exp (I * (gammaHardyTheta t : ℂ)) *
      deriv (fun u : ℝ => riemannZeta (linePt u)) t).re = deriv hardyZ t := by
  change (Complex.exp (I * (gammaHardyTheta t : ℂ)) *
      deriv (fun u : ℝ => riemannZeta (linePt u)) t).re =
    deriv (fun u => phaseHalvedAmplitude (gammaHardyPhase u) (riemannZeta (linePt u))) t
  exact re_exp_theta_mul_deriv_gammaPhaseReflected_eq_amplitude_deriv
    (fun u => riemannZeta_line_isPhaseReflected u) differentiable_riemannZeta_line t

/-- The imaginary component of the rotating-frame zeta height derivative is the exact
phase-velocity multiple of Hardy Z. -/
theorem im_exp_theta_mul_deriv_riemannZeta_line (t : ℝ) :
    (Complex.exp (I * (gammaHardyTheta t : ℂ)) *
      deriv (fun u : ℝ => riemannZeta (linePt u)) t).im =
        -gammaHardyPhaseRate t * hardyZ t := by
  change (Complex.exp (I * (gammaHardyTheta t : ℂ)) *
      deriv (fun u : ℝ => riemannZeta (linePt u)) t).im =
    -gammaHardyPhaseRate t *
      phaseHalvedAmplitude (gammaHardyPhase t) (riemannZeta (linePt t))
  exact im_exp_theta_mul_deriv_gammaPhaseReflected_eq_neg_rate_mul_amplitude
    (fun u => riemannZeta_line_isPhaseReflected u) differentiable_riemannZeta_line t

/-- At a critical-line zeta zero, the rotating-frame zeta height derivative is exactly the
embedded real Hardy-Z derivative. -/
theorem exp_theta_mul_deriv_riemannZeta_line_eq_deriv_hardyZ_of_zero
    {t : ℝ} (hzeta : riemannZeta (linePt t) = 0) :
    Complex.exp (I * (gammaHardyTheta t : ℂ)) *
        deriv (fun u : ℝ => riemannZeta (linePt u)) t =
      ((deriv hardyZ t : ℝ) : ℂ) := by
  rw [exp_theta_mul_deriv_riemannZeta_line,
    (riemannZeta_line_eq_zero_iff_hardyZ t).mp hzeta]
  simp

/-- The height derivative of critical-line zeta vanishes at a zeta zero exactly when the real
Hardy-Z derivative vanishes there. -/
theorem deriv_riemannZeta_line_eq_zero_iff_deriv_hardyZ_of_zero
    {t : ℝ} (hzeta : riemannZeta (linePt t) = 0) :
    deriv (fun u : ℝ => riemannZeta (linePt u)) t = 0 ↔ deriv hardyZ t = 0 :=
  deriv_gammaPhaseReflected_eq_zero_iff_amplitude_deriv_of_zero
    (fun u => riemannZeta_line_isPhaseReflected u) differentiable_riemannZeta_line hzeta

/-- The real-height derivative of zeta is its complex derivative times the vertical tangent. -/
theorem deriv_riemannZeta_line (t : ℝ) :
    deriv (fun u : ℝ => riemannZeta (linePt u)) t =
      deriv riemannZeta (linePt t) * I := by
  have hne : linePt t ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    rw [linePt_re, Complex.one_re] at hre
    norm_num at hre
  have houter := (differentiableAt_riemannZeta hne).hasDerivAt
  have hcomp := (houter.hasFDerivAt.restrictScalars ℝ).comp t
    (hasDerivAt_linePt t).hasFDerivAt
  simpa [Function.comp_def, mul_comm] using hcomp.hasDerivAt.deriv

/-- **Zeta/Hardy simple-zero interface.**  At a critical-line zero, the complex derivative of
zeta vanishes exactly when the real Hardy-Z derivative vanishes. -/
theorem deriv_riemannZeta_eq_zero_iff_deriv_hardyZ_of_zero
    {t : ℝ} (hzeta : riemannZeta (linePt t) = 0) :
    deriv riemannZeta (linePt t) = 0 ↔ deriv hardyZ t = 0 := by
  rw [← deriv_riemannZeta_line_eq_zero_iff_deriv_hardyZ_of_zero hzeta,
    deriv_riemannZeta_line, mul_eq_zero]
  simp

/-- **Zeta/positive-theta first-jet interface.**  At a critical-line zero, the complex zeta
derivative vanishes exactly when the derivative of the positive theta-cusp cosine representation
vanishes. -/
theorem deriv_riemannZeta_eq_zero_iff_deriv_thetaCuspCosineRepresentation_of_zero
    {t : ℝ} (hzeta : riemannZeta (linePt t) = 0) :
    deriv riemannZeta (linePt t) = 0 ↔
      deriv thetaCuspCosineRepresentation t = 0 := by
  exact (deriv_riemannZeta_eq_zero_iff_deriv_hardyZ_of_zero hzeta).trans
    (deriv_hardyZ_eq_zero_iff_deriv_thetaCuspCosineRepresentation_of_zero
      ((riemannZeta_line_eq_zero_iff_hardyZ t).mp hzeta))

/-- **Source-moment multiplicity criterion.**  A critical-line zeta zero is multiple exactly when
the positive theta source's first sine moment vanishes at the same height. -/
theorem deriv_riemannZeta_eq_zero_iff_thetaCuspFirstSineMoment_of_zero
    {t : ℝ} (hzeta : riemannZeta (linePt t) = 0) :
    deriv riemannZeta (linePt t) = 0 ↔
      (∫ x : ℝ in Set.Ioi 0,
        x * thetaCuspFullSource x * Real.sin (t * x)) = 0 := by
  exact (deriv_riemannZeta_eq_zero_iff_deriv_hardyZ_of_zero hzeta).trans
    (deriv_hardyZ_eq_zero_iff_thetaCuspFirstSineMoment_of_zero
      ((riemannZeta_line_eq_zero_iff_hardyZ t).mp hzeta))

/-- Equivalently, simplicity of a critical-line zeta zero is exact nonvanishing of the positive
theta source's first sine moment. -/
theorem deriv_riemannZeta_ne_zero_iff_thetaCuspFirstSineMoment_ne_zero_of_zero
    {t : ℝ} (hzeta : riemannZeta (linePt t) = 0) :
    deriv riemannZeta (linePt t) ≠ 0 ↔
      (∫ x : ℝ in Set.Ioi 0,
        x * thetaCuspFullSource x * Real.sin (t * x)) ≠ 0 :=
  not_congr (deriv_riemannZeta_eq_zero_iff_thetaCuspFirstSineMoment_of_zero hzeta)

/-- **Unconditional second-jet bound.**  The derivative of the exact Gamma phase velocity is
controlled by the existing vertical trigamma estimate. -/
theorem abs_deriv_gammaHardyPhaseRate_le {t : ℝ} (ht : 0 < t) :
    |deriv gammaHardyPhaseRate t| ≤ 1 / t ^ 2 + Real.pi / (4 * t) := by
  rw [deriv_gammaHardyPhaseRate]
  have harg : linePt t / 2 = ((1 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I := by
    unfold linePt
    push_cast
    ring
  have htri : ‖deriv Complex.digamma (linePt t / 2)‖ ≤
      1 / (t / 2) ^ 2 + Real.pi / (2 * (t / 2)) := by
    rw [harg]
    exact norm_deriv_digamma_vertical_le (show (0 : ℝ) < 1 / 4 by norm_num)
      (half_pos ht)
  calc
    |-(deriv Complex.digamma (linePt t / 2)).im / 4| ≤
        ‖deriv Complex.digamma (linePt t / 2)‖ / 4 := by
      rw [abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
      exact div_le_div_of_nonneg_right (Complex.abs_im_le_norm _) (by norm_num)
    _ ≤ (1 / (t / 2) ^ 2 + Real.pi / (2 * (t / 2))) / 4 := by
      exact div_le_div_of_nonneg_right htri (by norm_num)
    _ = 1 / t ^ 2 + Real.pi / (4 * t) := by
      field_simp [ht.ne']
      norm_num

/-- **Sharpened envelope-winding curvature bound.**  Identifying the winding rate with the Hardy
phase removes the spurious rational-envelope contribution from the older norm estimate. -/
theorem windingRateDeriv_abs_le_sharp {t : ℝ} (ht : 0 < t) :
    |windingRateDeriv t| ≤ 1 / t ^ 2 + Real.pi / (4 * t) := by
  rw [windingRateDeriv_eq_deriv_gammaHardyPhaseRate]
  exact abs_deriv_gammaHardyPhaseRate_le ht

/-- The same unconditional second-jet bound, stated directly for the global phase lift. -/
theorem abs_deriv_deriv_gammaHardyTheta_le {t : ℝ} (ht : 0 < t) :
    |deriv (deriv gammaHardyTheta) t| ≤ 1 / t ^ 2 + Real.pi / (4 * t) := by
  rw [deriv_deriv_gammaHardyTheta, ← deriv_gammaHardyPhaseRate]
  exact abs_deriv_gammaHardyPhaseRate_le ht

/-- The exact phase velocity differs from its radial logarithmic model by an explicit error. -/
theorem gammaHardyPhaseRate_sub_radial_log_bound {t : ℝ} (ht : 0 < t) :
    |gammaHardyPhaseRate t -
      ((1 / 4 : ℝ) * Real.log ((1 / 4 : ℝ) ^ 2 + (t / 2) ^ 2) -
        Real.log Real.pi / 2)| ≤ 2 / t ^ 2 + Real.pi / (2 * t) := by
  have hbase := re_digamma_vertical_bound_uncond
    (show (0 : ℝ) ≤ 1 / 4 by norm_num) (half_pos ht)
  have harg : linePt t / 2 = ((1 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I := by
    unfold linePt
    push_cast
    ring
  unfold gammaHardyPhaseRate
  rw [harg]
  let d : ℝ :=
    (Complex.digamma (((1 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I)).re
  let L : ℝ := Real.log ((1 / 4 : ℝ) ^ 2 + (t / 2) ^ 2)
  have hrewrite : d / 2 - Real.log Real.pi / 2 -
      ((1 / 4 : ℝ) * L - Real.log Real.pi / 2) = (d - (1 / 2 : ℝ) * L) / 2 := by
    ring
  rw [hrewrite, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    |d - (1 / 2 : ℝ) * L| / 2 ≤
        (1 / (t / 2) ^ 2 + Real.pi / (2 * (t / 2))) / 2 := by
      exact div_le_div_of_nonneg_right (by simpa [d, L] using hbase) (by norm_num)
    _ = 2 / t ^ 2 + Real.pi / (2 * t) := by
      field_simp [ht.ne']

/-- **Quantitative Riemann--Siegel phase-velocity law.**  The exact rate differs from the
conductor logarithm by an explicit unconditional `O(1/t)` bound. -/
theorem gammaHardyPhaseRate_sub_log_conductor_bound {t : ℝ} (ht : 0 < t) :
    |gammaHardyPhaseRate t - Real.log (t / (2 * Real.pi)) / 2| ≤
      33 / (16 * t ^ 2) + Real.pi / (2 * t) := by
  let radial : ℝ := (1 / 4 : ℝ) *
    Real.log ((1 / 4 : ℝ) ^ 2 + (t / 2) ^ 2) - Real.log Real.pi / 2
  have hrate : |gammaHardyPhaseRate t - radial| ≤
      2 / t ^ 2 + Real.pi / (2 * t) := by
    simpa [radial] using gammaHardyPhaseRate_sub_radial_log_bound ht
  have honepos : 0 < 1 + 1 / (4 * t ^ 2) := by positivity
  have hradarg : (1 / 4 : ℝ) ^ 2 + (t / 2) ^ 2 =
      (t / 2) ^ 2 * (1 + 1 / (4 * t ^ 2)) := by
    field_simp [ht.ne']
    ring
  have hcorr : radial - Real.log (t / (2 * Real.pi)) / 2 =
      (1 / 4 : ℝ) * Real.log (1 + 1 / (4 * t ^ 2)) := by
    unfold radial
    rw [hradarg, Real.log_mul (pow_ne_zero 2 (div_ne_zero ht.ne' (by norm_num))) honepos.ne',
      Real.log_pow, Real.log_div ht.ne' (mul_ne_zero (by norm_num) Real.pi_ne_zero),
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero,
      Real.log_div ht.ne' (by norm_num : (2 : ℝ) ≠ 0)]
    ring
  have hcorrnonneg : 0 ≤ radial - Real.log (t / (2 * Real.pi)) / 2 := by
    rw [hcorr]
    exact mul_nonneg (by norm_num) (Real.log_nonneg (by
      have : 0 ≤ 1 / (4 * t ^ 2) := by positivity
      linarith))
  have hcorrle : radial - Real.log (t / (2 * Real.pi)) / 2 ≤ 1 / (16 * t ^ 2) := by
    rw [hcorr]
    have hlog := Real.log_le_sub_one_of_pos honepos
    calc
      (1 / 4 : ℝ) * Real.log (1 + 1 / (4 * t ^ 2)) ≤
          (1 / 4 : ℝ) * ((1 + 1 / (4 * t ^ 2)) - 1) := by gcongr
      _ = 1 / (16 * t ^ 2) := by
        field_simp [ht.ne']
        ring
  calc
    |gammaHardyPhaseRate t - Real.log (t / (2 * Real.pi)) / 2| ≤
        |gammaHardyPhaseRate t - radial| +
          |radial - Real.log (t / (2 * Real.pi)) / 2| := by
      calc
        _ = |(gammaHardyPhaseRate t - radial) +
            (radial - Real.log (t / (2 * Real.pi)) / 2)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    _ ≤ (2 / t ^ 2 + Real.pi / (2 * t)) + 1 / (16 * t ^ 2) := by
      exact add_le_add hrate (by simpa [abs_of_nonneg hcorrnonneg] using hcorrle)
    _ = 33 / (16 * t ^ 2) + Real.pi / (2 * t) := by
      field_simp [ht.ne']
      ring

/-- The pre-existing winding floor, transported through the exact winding/Hardy identification,
gives a slightly sharper one-sided conductor bound than the symmetric absolute estimate. -/
theorem gammaHardyPhaseRate_ge_log_conductor {t : ℝ} (ht : 0 < t) :
    Real.log (t / (2 * Real.pi)) / 2 -
        (2 / t ^ 2 + Real.pi / (2 * t)) ≤ gammaHardyPhaseRate t := by
  have h := windingRate_ge ht
  rw [windingRate_eq_gammaHardyPhaseRate] at h
  calc
    Real.log (t / (2 * Real.pi)) / 2 -
        (2 / t ^ 2 + Real.pi / (2 * t)) =
      (Real.log (t / (2 * Real.pi)) - (4 / t ^ 2 + Real.pi / t)) / 2 := by ring
    _ ≤ gammaHardyPhaseRate t := h

/-- The phase velocity differs from its half-logarithmic main term by a quantity tending to zero. -/
theorem gammaHardyPhaseRate_sub_log_half_tendsto_zero :
    Tendsto (fun τ : ℝ => gammaHardyPhaseRate τ -
      (Real.log (τ / 2) / 2 - Real.log Real.pi / 2)) atTop (nhds 0) := by
  have hbase := re_digamma_vertical_sub_log_tendsto_zero (1 / 4) (by norm_num)
  have hhalf : Tendsto (fun τ : ℝ => τ / 2) atTop atTop :=
    tendsto_id.atTop_div_const (by norm_num)
  have hscaled := (hbase.comp hhalf).const_mul (1 / 2 : ℝ)
  simpa only [Function.comp_def, mul_zero] using hscaled.congr'
    (Filter.Eventually.of_forall fun τ => by
      unfold gammaHardyPhaseRate linePt
      have harg : ((((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) / 2) =
          ((1 / 4 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * I := by
        push_cast
        ring
      rw [harg]
      simp only [Function.comp_apply]
      ring)

/-- **Classical Riemann--Siegel phase-velocity asymptotic.** -/
theorem gammaHardyPhaseRate_sub_log_conductor_tendsto_zero :
    Tendsto (fun τ : ℝ => gammaHardyPhaseRate τ -
      Real.log (τ / (2 * Real.pi)) / 2) atTop (nhds 0) := by
  refine gammaHardyPhaseRate_sub_log_half_tendsto_zero.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with τ hτ
  rw [Real.log_div hτ.ne' (by positivity : (2 * Real.pi : ℝ) ≠ 0),
    Real.log_div hτ.ne' (by norm_num : (2 : ℝ) ≠ 0),
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero]
  ring

/-- **Asymptotic integration law.**  If a real function is differentiable on the positive ray
and its derivative tends to zero, then the function is `o(t)` at positive infinity.  This
discharges the derivative-to-value interface without a global differentiability hypothesis at the
origin. -/
theorem tendsto_div_atTop_zero_of_deriv_tendsto_zero
    {f : ℝ → ℝ} (hf : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ f x)
    (hderiv : Tendsto (fun x => deriv f x) atTop (nhds 0)) :
    Tendsto (fun x => f x / x) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop] at hderiv ⊢
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨T, hT⟩ := hderiv (ε / 3) hε3
  let T' := max T 1
  let X := max T' (3 * |f T'| / ε)
  refine ⟨X, fun x hx => ?_⟩
  have hTT' : T ≤ T' := le_max_left _ _
  have hT'one : 1 ≤ T' := le_max_right _ _
  have hT'pos : 0 < T' := lt_of_lt_of_le zero_lt_one hT'one
  have hT'x : T' ≤ x := (le_max_left _ _).trans hx
  have hxpos : 0 < x := hT'pos.trans_le hT'x
  have hderiv_bound : ∀ u ∈ Set.Ici T', ‖deriv f u‖ ≤ ε / 3 := by
    intro u hu
    have hTu : T ≤ u := hTT'.trans hu
    have huclose := hT u hTu
    simpa [dist_zero_right] using huclose.le
  have hmvt : |f x - f T'| ≤ (ε / 3) * (x - T') := by
    have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (s := Set.Ici T') (x := T') (y := x)
      (fun u hu => hf u (hT'pos.trans_le hu)) hderiv_bound (convex_Ici T')
      (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hT'x)
    simpa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hT'x)] using h
  have hvariation : |f x - f T'| / x ≤ ε / 3 := by
    apply (div_le_iff₀ hxpos).2
    exact hmvt.trans (mul_le_mul_of_nonneg_left (sub_le_self x hT'pos.le) hε3.le)
  have hanchorX : 3 * |f T'| / ε ≤ x := (le_max_right _ _).trans hx
  have hanchor : |f T'| / x ≤ ε / 3 := by
    apply (div_le_iff₀ hxpos).2
    have heq : |f T'| = (ε / 3) * (3 * |f T'| / ε) := by
      field_simp [hε.ne']
    rw [heq]
    exact mul_le_mul_of_nonneg_left hanchorX hε3.le
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hxpos]
  calc
    |f x| / x ≤ (|f x - f T'| + |f T'|) / x := by
      gcongr
      calc
        |f x| = |(f x - f T') + f T'| := by ring_nf
        _ ≤ |f x - f T'| + |f T'| := abs_add_le _ _
    _ = |f x - f T'| / x + |f T'| / x := by ring
    _ ≤ ε / 3 + ε / 3 := add_le_add hvariation hanchor
    _ < ε := by linarith

/-- The leading Riemann--Siegel phase model
`(t/2) log(t/(2*pi)) - t/2`. -/
noncomputable def gammaHardyThetaMain (t : ℝ) : ℝ :=
  t / 2 * Real.log (t / (2 * Real.pi)) - t / 2

/-- The derivative of the leading phase model on the positive ray. -/
theorem hasDerivAt_gammaHardyThetaMain {t : ℝ} (ht : 0 < t) :
    HasDerivAt gammaHardyThetaMain (Real.log (t / (2 * Real.pi)) / 2) t := by
  have hden : (2 * Real.pi : ℝ) ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  have harg := (hasDerivAt_id t).div_const (2 * Real.pi)
  have hlog := (Real.hasDerivAt_log (div_ne_zero ht.ne' hden)).comp t harg
  have hprod := ((hasDerivAt_id t).div_const 2).mul hlog
  have hlinear := (hasDerivAt_id t).div_const 2
  have hraw : HasDerivAt
      (fun u : ℝ => u / 2 * Real.log (u / (2 * Real.pi)) - u / 2)
      (1 / 2 * Real.log (t / (2 * Real.pi)) +
        t / 2 * ((t / (2 * Real.pi))⁻¹ * (1 / (2 * Real.pi))) - 1 / 2) t := by
    simpa only [Function.comp_apply, id_eq, Pi.mul_apply, Pi.sub_apply] using!
      hprod.sub hlinear
  have hcoeff :
      1 / 2 * Real.log (t / (2 * Real.pi)) +
          t / 2 * ((t / (2 * Real.pi))⁻¹ * (1 / (2 * Real.pi))) - 1 / 2 =
        Real.log (t / (2 * Real.pi)) / 2 := by
    field_simp [ht.ne', hden]
    ring
  simpa only [gammaHardyThetaMain, hcoeff] using! hraw

/-- **Classical Riemann--Siegel phase-value asymptotic.**  Integrating the exact velocity
asymptotic shows that the global branch-free phase differs from its leading model by `o(t)`. -/
theorem gammaHardyTheta_sub_main_div_tendsto_zero :
    Tendsto (fun t : ℝ => (gammaHardyTheta t - gammaHardyThetaMain t) / t)
      atTop (nhds 0) := by
  apply tendsto_div_atTop_zero_of_deriv_tendsto_zero
  · intro t ht
    exact (hasDerivAt_gammaHardyTheta t).differentiableAt.sub
      (hasDerivAt_gammaHardyThetaMain ht).differentiableAt
  · refine gammaHardyPhaseRate_sub_log_conductor_tendsto_zero.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact (((hasDerivAt_gammaHardyTheta t).sub
      (hasDerivAt_gammaHardyThetaMain ht)).deriv).symm

/-- Normalized form of the Riemann--Siegel phase-value asymptotic. -/
theorem gammaHardyTheta_div_sub_log_conductor_tendsto_zero :
    Tendsto (fun t : ℝ => gammaHardyTheta t / t -
      (Real.log (t / (2 * Real.pi)) / 2 - 1 / 2)) atTop (nhds 0) := by
  refine gammaHardyTheta_sub_main_div_tendsto_zero.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  unfold gammaHardyThetaMain
  field_simp [ht.ne']

/-- The normalized global phase grows without bound. -/
theorem gammaHardyTheta_div_tendsto_atTop :
    Tendsto (fun t : ℝ => gammaHardyTheta t / t) atTop atTop := by
  have hscale : Tendsto (fun t : ℝ => t / (2 * Real.pi)) atTop atTop :=
    tendsto_id.atTop_div_const (mul_pos (by norm_num) Real.pi_pos)
  have hlogHalf : Tendsto (fun t : ℝ => Real.log (t / (2 * Real.pi)) / 2)
      atTop atTop := (Real.tendsto_log_atTop.comp hscale).atTop_div_const (by norm_num)
  have hmain : Tendsto (fun t : ℝ =>
      Real.log (t / (2 * Real.pi)) / 2 - 1 / 2) atTop atTop := by
    simpa [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-(1 / 2 : ℝ)) hlogHalf
  have hsum := hmain.atTop_add gammaHardyTheta_div_sub_log_conductor_tendsto_zero
  exact hsum.congr' (Filter.Eventually.of_forall fun t => by ring)

/-- The global branch-free Riemann--Siegel phase tends to positive infinity. -/
theorem gammaHardyTheta_tendsto_atTop : Tendsto gammaHardyTheta atTop atTop := by
  have hprod := gammaHardyTheta_div_tendsto_atTop.atTop_mul_atTop₀ tendsto_id
  exact hprod.congr' <| by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    simp [id_eq, ht.ne']

/-- The normalized-Gamma phase velocity diverges to positive infinity. -/
theorem gammaHardyPhaseRate_tendsto_atTop :
    Tendsto gammaHardyPhaseRate atTop atTop := by
  have hscale : Tendsto (fun τ : ℝ => τ / (2 * Real.pi)) atTop atTop :=
    tendsto_id.atTop_div_const (mul_pos (by norm_num) Real.pi_pos)
  have hmain : Tendsto (fun τ : ℝ => Real.log (τ / (2 * Real.pi)) / 2)
      atTop atTop := (Real.tendsto_log_atTop.comp hscale).atTop_div_const (by norm_num)
  have hsum := hmain.atTop_add gammaHardyPhaseRate_sub_log_conductor_tendsto_zero
  exact hsum.congr' (Filter.Eventually.of_forall fun τ => by ring)

/-- The normalized-Gamma phase velocity is eventually strictly positive. -/
theorem eventually_gammaHardyPhaseRate_pos :
    ∀ᶠ τ : ℝ in atTop, 0 < gammaHardyPhaseRate τ :=
  gammaHardyPhaseRate_tendsto_atTop.eventually (eventually_gt_atTop 0)

/-- **Unique positive stationary-height law.**  The exact Gamma phase velocity crosses zero at
one and only one positive height.  Central negativity, divergence to `+∞`, continuity, and strict
positive-ray monotonicity discharge every auxiliary threshold hypothesis. -/
theorem existsUnique_pos_gammaHardyPhaseRate_eq_zero :
    ∃! T : ℝ, 0 < T ∧ gammaHardyPhaseRate T = 0 := by
  obtain ⟨x, hx, hxrate⟩ :=
    ((eventually_gt_atTop (0 : ℝ)).and eventually_gammaHardyPhaseRate_pos).exists
  obtain ⟨T, hTmem, hTzero⟩ := intermediate_value_Icc hx.le
    continuous_gammaHardyPhaseRate.continuousOn
    (Set.mem_Icc.mpr ⟨gammaHardyPhaseRate_zero_neg.le, hxrate.le⟩)
  have hTpos : 0 < T := by
    rcases hTmem with ⟨hTnonneg, -⟩
    exact lt_of_le_of_ne hTnonneg fun hTzero' => by
      subst T
      linarith [gammaHardyPhaseRate_zero_neg]
  refine ⟨T, ⟨hTpos, hTzero⟩, ?_⟩
  intro y hy
  exact (strictMonoOn_gammaHardyPhaseRate.injOn
    (Set.mem_Ici.mpr hTpos.le) (Set.mem_Ici.mpr hy.1.le)
    (hTzero.trans hy.2.symm)).symm

/-- **Exact Hardy-phase Morse law.**  Any positive zero of the phase velocity is the turning
height: the integrated phase is strictly decreasing before it and strictly increasing after it.
Together with `existsUnique_pos_gammaHardyPhaseRate_eq_zero`, this is unconditional. -/
theorem gammaHardyTheta_morseGeometry_of_rate_eq_zero {T : ℝ}
    (hTpos : 0 < T) (hTzero : gammaHardyPhaseRate T = 0) :
    StrictAntiOn gammaHardyTheta (Set.Icc 0 T) ∧
      StrictMonoOn gammaHardyTheta (Set.Ici T) := by
  constructor
  · apply strictAntiOn_of_deriv_neg (convex_Icc 0 T)
    · intro x _
      exact (hasDerivAt_gammaHardyTheta x).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc, Set.mem_Ioo] at hx
      rw [deriv_gammaHardyTheta]
      have h := strictMonoOn_gammaHardyPhaseRate
        (Set.mem_Ici.mpr hx.1.le) (Set.mem_Ici.mpr hTpos.le) hx.2
      linarith
  · apply strictMonoOn_of_deriv_pos (convex_Ici T)
    · intro x _
      exact (hasDerivAt_gammaHardyTheta x).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici, Set.mem_Ioi] at hx
      rw [deriv_gammaHardyTheta]
      have h := strictMonoOn_gammaHardyPhaseRate
        (Set.mem_Ici.mpr hTpos.le) (Set.mem_Ici.mpr (hTpos.le.trans hx.le)) hx
      linarith

/-- A positive stationary height is a global minimum of the exact Hardy phase on the nonnegative
half-line. -/
theorem gammaHardyTheta_minimum_le_of_rate_eq_zero {T t : ℝ}
    (hTpos : 0 < T) (hTzero : gammaHardyPhaseRate T = 0) (ht : 0 ≤ t) :
    gammaHardyTheta T ≤ gammaHardyTheta t := by
  obtain ⟨hanti, hmono⟩ := gammaHardyTheta_morseGeometry_of_rate_eq_zero hTpos hTzero
  by_cases htT : t ≤ T
  · exact hanti.antitoneOn (Set.mem_Icc.mpr ⟨ht, htT⟩)
      (Set.mem_Icc.mpr ⟨hTpos.le, le_rfl⟩) htT
  · have hTt : T ≤ t := le_of_not_ge htT
    exact hmono.monotoneOn (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hTt) hTt

/-- **Minimum-value Prop interface.**  On the nonnegative half-line, equality with the phase
minimum detects the unique stationary height. -/
theorem gammaHardyTheta_eq_minimum_iff_of_rate_eq_zero {T t : ℝ}
    (hTpos : 0 < T) (hTzero : gammaHardyPhaseRate T = 0) (ht : 0 ≤ t) :
    gammaHardyTheta t = gammaHardyTheta T ↔ t = T := by
  obtain ⟨hanti, hmono⟩ := gammaHardyTheta_morseGeometry_of_rate_eq_zero hTpos hTzero
  constructor
  · intro heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with htT | hTt
    · have h := hanti (Set.mem_Icc.mpr ⟨ht, htT.le⟩)
        (Set.mem_Icc.mpr ⟨hTpos.le, le_rfl⟩) htT
      linarith
    · have h := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hTt.le) hTt
      linarith
  · rintro rfl
    rfl

/-- **Canonical positive-tail phase coordinate.**  Once the (necessarily unique) positive
stationary height is named, the exact Hardy phase is a bijection from its increasing ray onto the
ray beginning at its global minimum. -/
theorem gammaHardyTheta_bijOn_Ici_of_rate_eq_zero {T : ℝ}
    (hTpos : 0 < T) (hTzero : gammaHardyPhaseRate T = 0) :
    Set.BijOn gammaHardyTheta (Set.Ici T) (Set.Ici (gammaHardyTheta T)) := by
  have hmono : StrictMonoOn gammaHardyTheta (Set.Ici T) :=
    (gammaHardyTheta_morseGeometry_of_rate_eq_zero hTpos hTzero).2
  refine ⟨?_, hmono.injOn, ?_⟩
  · intro x hx
    exact hmono.monotoneOn (Set.mem_Ici.mpr le_rfl) hx (Set.mem_Ici.mp hx)
  · intro y hy
    have hlarge : ∀ᶠ x : ℝ in atTop, y ≤ gammaHardyTheta x :=
      (tendsto_atTop.1 gammaHardyTheta_tendsto_atTop) y
    obtain ⟨x, hxT, hyx⟩ := ((eventually_ge_atTop T).and hlarge).exists
    obtain ⟨z, hz, hzy⟩ := intermediate_value_Icc hxT
      differentiable_gammaHardyTheta.continuous.continuousOn
      (Set.mem_Icc.mpr ⟨hy, hyx⟩)
    exact ⟨z, hz.1, hzy⟩

/-- The branch-free Riemann--Siegel phase is strictly increasing on some terminal ray. -/
theorem exists_gammaHardyTheta_strictMonoOn :
    ∃ T : ℝ, StrictMonoOn gammaHardyTheta (Set.Ici T) := by
  obtain ⟨T, hT, -⟩ := existsUnique_pos_gammaHardyPhaseRate_eq_zero
  exact ⟨T, (gammaHardyTheta_morseGeometry_of_rate_eq_zero hT.1 hT.2).2⟩

/-- **Terminal phase-coordinate law.**  On some terminal ray the global Riemann--Siegel phase is
a bijection onto the terminal ray beginning at its boundary value.  Thus every sufficiently large
phase level has one and only one positive-tail height, an exact Prop interface for Gram-point and
Riemann--Siegel arguments. -/
theorem exists_gammaHardyTheta_terminal_bijOn :
    ∃ T : ℝ, Set.BijOn gammaHardyTheta (Set.Ici T) (Set.Ici (gammaHardyTheta T)) := by
  obtain ⟨T, hT, -⟩ := existsUnique_pos_gammaHardyPhaseRate_eq_zero
  exact ⟨T, gammaHardyTheta_bijOn_Ici_of_rate_eq_zero hT.1 hT.2⟩

end RHTower
