import GaloisForLFunctions.RHTower.RoutePCompensatedMassRiccati
import GaloisForLFunctions.RHTower.CCMPrimeMomentFirstContact
import GaloisForLFunctions.RHTower.CCMUnitRieszCausalLaplaceBridge

/-!
# The actual prime-moment potential and its signed Laplace transform

The critical Chebyshev primitive gives the continuous logarithmic potential
`U(T) = exp(T/2) * (1 + J(T)/2) - 1`. It equals the literal arithmetic
expression `sqrt(exp T)*(primeMassHalf(exp T)+2)-exp T-psi(exp T)-1`.
Its absolutely convergent Laplace transform for real `s > 1` is
`-logDeriv zetaResidueUnit s / (s*(2*s-1))`.

Finite and infinite integration by parts retain the initial and terminal
terms. All source identities and admission statements are unconditional.
-/

noncomputable section
open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.RHTower
namespace RHTower

/-- The signed primitive of the actual normalized Chebyshev error. -/
def ccmPrimeMomentErrorPrimitive (T : ℝ) : ℝ :=
  ∫ t in (0:ℝ)..T, criticalMellinNormalizedChebyshevError t

/-- The continuous prime-moment potential in logarithmic coordinates. -/
def ccmPrimeMomentLogPotential (T : ℝ) : ℝ :=
  Real.exp (T/2) * (1 + ccmPrimeMomentErrorPrimitive T/2) - 1

private theorem error_integrable (a b : ℝ) :
    IntervalIntegrable criticalMellinNormalizedChebyshevError volume a b := by
  have hp := (Chebyshev.psi_mono.comp Real.exp_monotone).intervalIntegrable
    (a := a) (b := b) (μ := volume)
  have he := hp.sub (Real.continuous_exp.intervalIntegrable a b)
  have hm := he.mul_continuousOn
    (show Continuous (fun t : ℝ => Real.exp (-t/2)) by fun_prop).continuousOn
  convert! hm using 1
  ext t
  rw [criticalMellinNormalizedChebyshevError_eq_apertureError,
    criticalMellinChebyshevError_eq_exp]
  rfl

/-- The primitive is continuous despite the prime jumps in its driver. -/
theorem continuous_ccmPrimeMomentErrorPrimitive : Continuous ccmPrimeMomentErrorPrimitive :=
  intervalIntegral.continuous_primitive error_integrable 0

/-- Continuity of the full potential, including every admission time. -/
theorem continuous_ccmPrimeMomentLogPotential : Continuous ccmPrimeMomentLogPotential :=
  ((Real.continuous_exp.comp (continuous_id.div_const 2)).mul
    (continuous_const.add (continuous_ccmPrimeMomentErrorPrimitive.div_const 2))).sub continuous_const

private theorem error_bound (t : ℝ) :
    |criticalMellinNormalizedChebyshevError t| ≤ chebyshevDeficitConst * Real.exp (t/2) := by
  rw [criticalMellinNormalizedChebyshevError_eq_apertureError]
  exact abs_criticalMellinChebyshevError_le_exp_half t

private theorem integral_exp_half (a b : ℝ) :
    (∫ t in a..b, Real.exp (t/2)) = 2*Real.exp (b/2)-2*Real.exp (a/2) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t => 2*Real.exp (t/2))
  · intro t _
    convert! (((hasDerivAt_id t).div_const 2).exp).const_mul 2 using 1
    dsimp only [id_eq]
    ring
  · exact (show Continuous (fun t : ℝ => Real.exp (t/2)) by fun_prop).intervalIntegrable a b

private theorem primitive_bound {T : ℝ} (hT : 0 ≤ T) :
    |ccmPrimeMomentErrorPrimitive T| ≤ 2*chebyshevDeficitConst*Real.exp (T/2) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
    (f := criticalMellinNormalizedChebyshevError)
    (g := fun t => chebyshevDeficitConst*Real.exp (t/2)) hT
    (Eventually.of_forall fun t _ => by rw [Real.norm_eq_abs]; exact error_bound t)
    ((show Continuous (fun t : ℝ => chebyshevDeficitConst*Real.exp (t/2)) by
      fun_prop).intervalIntegrable 0 T)
  rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul, integral_exp_half] at h
  simp only [zero_div, Real.exp_zero] at h
  change |ccmPrimeMomentErrorPrimitive T| ≤ _ at h
  linarith [chebyshevDeficitConst_pos]

/-- An elementary envelope admitting the potential in its initial Laplace half-plane. -/
theorem ccmPrimeMomentLogPotential_bound {T : ℝ} (hT : 0 ≤ T) :
    |ccmPrimeMomentLogPotential T| ≤ (chebyshevDeficitConst+2)*Real.exp T := by
  have hp := primitive_bound hT
  have he : Real.exp (T/2) ≤ Real.exp T := Real.exp_le_exp.mpr (by linarith)
  have he1 := Real.one_le_exp hT
  have heq : Real.exp (T/2)*Real.exp (T/2) = Real.exp T := by
    rw [← Real.exp_add]; congr 1; ring
  unfold ccmPrimeMomentLogPotential
  calc
    |Real.exp (T/2)*(1+ccmPrimeMomentErrorPrimitive T/2)-1| ≤
        Real.exp (T/2)*(1+|ccmPrimeMomentErrorPrimitive T|/2)+1 := by
      have h := abs_add_le 1 (ccmPrimeMomentErrorPrimitive T/2)
      have hh := abs_sub (Real.exp (T/2)*(1+ccmPrimeMomentErrorPrimitive T/2)) 1
      rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_one] at hh
      norm_num only [abs_one, abs_div] at h
      nlinarith [Real.exp_pos (T/2)]
    _ ≤ (chebyshevDeficitConst+2)*Real.exp T := by
      have hscale : chebyshevDeficitConst*Real.exp (T/2)*Real.exp (T/2) =
          chebyshevDeficitConst*Real.exp T := by rw [mul_assoc, heq]
      nlinarith only [he, he1, hscale,
        mul_le_mul_of_nonneg_left hp (Real.exp_pos (T/2)).le]

private theorem weighted_error_integrable {a : ℝ} (ha : 1/2 < a) :
    IntegrableOn (fun t => Real.exp (-a*t)*criticalMellinNormalizedChebyshevError t) (Ioi 0) := by
  have hm := (exp_neg_integrableOn_Ioi 0 (by linarith : 0 < a-1/2)).const_mul
    chebyshevDeficitConst
  refine hm.mono' ((Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul
    measurable_criticalMellinNormalizedChebyshevError).aestronglyMeasurable ?_
  filter_upwards with t
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc Real.exp (-a*t)*|criticalMellinNormalizedChebyshevError t| ≤
      Real.exp (-a*t)*(chebyshevDeficitConst*Real.exp (t/2)) :=
        mul_le_mul_of_nonneg_left (error_bound t) (Real.exp_pos _).le
    _ = chebyshevDeficitConst*Real.exp (-(a-1/2)*t) := by
      rw [show -(a-1/2)*t = -a*t+t/2 by ring, Real.exp_add]; ring

private theorem weighted_primitive_integrable {a : ℝ} (ha : 1/2 < a) :
    IntegrableOn (fun t => Real.exp (-a*t)*ccmPrimeMomentErrorPrimitive t) (Ioi 0) := by
  have hm := (exp_neg_integrableOn_Ioi 0 (by linarith : 0 < a-1/2)).const_mul
    (2*chebyshevDeficitConst)
  refine hm.mono' ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
    continuous_ccmPrimeMomentErrorPrimitive).aestronglyMeasurable ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc Real.exp (-a*t)*|ccmPrimeMomentErrorPrimitive t| ≤
      Real.exp (-a*t)*(2*chebyshevDeficitConst*Real.exp (t/2)) :=
        mul_le_mul_of_nonneg_left (primitive_bound ht.le) (Real.exp_pos _).le
    _ = (2*chebyshevDeficitConst)*Real.exp (-(a-1/2)*t) := by
      rw [show -(a-1/2)*t = -a*t+t/2 by ring, Real.exp_add]; ring

private theorem primitive_parts {a R : ℝ} (ha : 0 < a) (hR : 0 ≤ R) :
    (∫ t in (0:ℝ)..R, Real.exp (-a*t)*ccmPrimeMomentErrorPrimitive t) =
      -(Real.exp (-a*R)/a)*ccmPrimeMomentErrorPrimitive R +
        (1/a)*∫ t in (0:ℝ)..R, Real.exp (-a*t)*criticalMellinNormalizedChebyshevError t := by
  let E : ℝ → ℝ := fun t => -(Real.exp (-a*t)/a)
  let P : ℝ → ℝ := ccmPrimeMomentErrorPrimitive
  have hi := error_integrable 0 R
  have hPac : AbsolutelyContinuousOnInterval P 0 R :=
    hi.absolutelyContinuousOnInterval_intervalIntegral (show (0:ℝ) ∈ uIcc 0 R by simp [hR])
  have hEcd : ContDiff ℝ 1 E := by dsimp [E]; fun_prop
  have hparts := hEcd.contDiffOn.absolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul hPac
  have hleft : (∫ t in (0:ℝ)..R, E t*deriv P t) =
      ∫ t in (0:ℝ)..R, E t*criticalMellinNormalizedChebyshevError t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hi.ae_hasDerivAt_integral] with t ht hmem
    have hd : HasDerivAt P (criticalMellinNormalizedChebyshevError t) t :=
      ht (uIoc_subset_uIcc hmem) 0 (by simp [hR])
    rw [hd.deriv]
  have hdE : ∀ t, deriv E t = Real.exp (-a*t) := by
    intro t
    have h1 : HasDerivAt (fun x : ℝ => -a*x) (-a) t := by
      simpa using (hasDerivAt_id t).const_mul (-a)
    have h2 : HasDerivAt (fun x : ℝ => Real.exp (-a*x)) (Real.exp (-a*t)*(-a)) t := h1.exp
    have hd : HasDerivAt E (-(Real.exp (-a*t)*(-a)/a)) t := (h2.div_const a).neg
    have he : -(Real.exp (-a*t)*(-a)/a) = Real.exp (-a*t) := by field_simp
    rw [he] at hd
    exact hd.deriv
  have hright : (∫ t in (0:ℝ)..R, deriv E t*P t) =
      ∫ t in (0:ℝ)..R, Real.exp (-a*t)*ccmPrimeMomentErrorPrimitive t := by
    apply intervalIntegral.integral_congr
    intro t _
    change deriv E t*P t = Real.exp (-a*t)*ccmPrimeMomentErrorPrimitive t
    rw [hdE]
  have hP0 : P 0 = 0 := by simp [P, ccmPrimeMomentErrorPrimitive]
  rw [hleft, hright, hP0, mul_zero, sub_zero] at hparts
  have hf : (∫ t in (0:ℝ)..R, E t*criticalMellinNormalizedChebyshevError t) =
      -(1/a)*∫ t in (0:ℝ)..R, Real.exp (-a*t)*criticalMellinNormalizedChebyshevError t := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp [E]; ring
  rw [hf] at hparts
  dsimp [E, P] at hparts
  linarith

private theorem primitive_laplace {a : ℝ} (ha : 1/2 < a) :
    (∫ t in Ioi (0:ℝ), Real.exp (-a*t)*ccmPrimeMomentErrorPrimitive t) =
      (1/a)*∫ t in Ioi (0:ℝ), Real.exp (-a*t)*criticalMellinNormalizedChebyshevError t := by
  have ha0 : 0 < a := by linarith
  have hL := intervalIntegral_tendsto_integral_Ioi 0 (weighted_primitive_integrable ha) tendsto_id
  have hR := (intervalIntegral_tendsto_integral_Ioi 0
    (weighted_error_integrable ha) tendsto_id).const_mul (1/a)
  have hB : Tendsto (fun R : ℝ => -(Real.exp (-a*R)/a)*ccmPrimeMomentErrorPrimitive R)
      atTop (𝓝 0) := by
    have h0 := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (by linarith : 0 < a-1/2))
    have hd := h0.const_mul (2*chebyshevDeficitConst/a)
    simp only [mul_zero] at hd
    refine squeeze_zero_norm' ?_ hd
    filter_upwards [eventually_ge_atTop (0:ℝ)] with R hR
    rw [norm_mul, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_div, abs_of_pos (Real.exp_pos _), abs_of_pos ha0]
    calc Real.exp (-a*R)/a*|ccmPrimeMomentErrorPrimitive R| ≤
        Real.exp (-a*R)/a*(2*chebyshevDeficitConst*Real.exp (R/2)) :=
          mul_le_mul_of_nonneg_left (primitive_bound hR) (by positivity)
      _ = (2*chebyshevDeficitConst/a)*Real.exp (-((a-1/2)*R)) := by
        rw [show -((a-1/2)*R) = -a*R+R/2 by ring, Real.exp_add]; ring
  have hh := hB.add hR
  rw [zero_add] at hh
  apply tendsto_nhds_unique _ hh
  refine hL.congr' ?_
  filter_upwards [eventually_ge_atTop (0:ℝ)] with R hR
  exact primitive_parts ha0 hR

/-- Exact signed Laplace transform of the actual potential, with both endpoints retained. -/
theorem ccmPrimeMomentLogPotential_laplace {s : ℝ} (hs : 1 < s) :
    ((∫ t in Ioi (0:ℝ), Real.exp (-s*t)*ccmPrimeMomentLogPotential t : ℝ) : ℂ) =
      -logDeriv zetaResidueUnit (s : ℂ) / ((s : ℂ)*(2*s-1)) := by
  have ha : 1/2 < s-1/2 := by linarith
  have hs0 : 0 < s := by linarith
  have hs' : 0 < s-1/2 := by linarith
  have heq : ∀ t : ℝ, Real.exp (-s*t)*ccmPrimeMomentLogPotential t =
      Real.exp (-(s-1/2)*t) +
        (1/2)* (Real.exp (-(s-1/2)*t)*ccmPrimeMomentErrorPrimitive t) - Real.exp (-s*t) := by
    intro t
    have he : Real.exp (-s*t)*Real.exp (t/2) = Real.exp (-(s-1/2)*t) := by
      rw [← Real.exp_add]; congr 1; ring
    unfold ccmPrimeMomentLogPotential
    linear_combination (1+ccmPrimeMomentErrorPrimitive t/2)*he
  simp_rw [heq]
  have hi : IntegrableOn (fun t => Real.exp (-(s-1/2)*t) +
      (1/2)*(Real.exp (-(s-1/2)*t)*ccmPrimeMomentErrorPrimitive t)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hs').add ((weighted_primitive_integrable ha).const_mul (1/2))
  rw [integral_sub hi (exp_neg_integrableOn_Ioi 0 hs0),
    integral_add (exp_neg_integrableOn_Ioi 0 hs') ((weighted_primitive_integrable ha).const_mul (1/2)),
    integral_const_mul, integral_exp_neg_mul_Ioi_real hs', integral_exp_neg_mul_Ioi_real hs0,
    primitive_laplace ha]
  have hE : ((∫ t in Ioi (0:ℝ), Real.exp (-(s-1/2)*t)*criticalMellinNormalizedChebyshevError t : ℝ) : ℂ) =
      -(logDeriv zetaResidueUnit (s : ℂ)+1)/(s : ℂ) := by
    have h := criticalNormalizedChebyshevErrorLaplace_eq_logDeriv
      (z := ((s-1/2 : ℝ) : ℂ)) (by simpa using ha)
    have hid : ((s-1/2 : ℝ) : ℂ)+1/2 = (s : ℂ) := by push_cast; ring
    rw [hid] at h
    rw [← h, criticalNormalizedChebyshevErrorLaplace, ← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards with t
    push_cast
    congr 2
    ring
  push_cast
  rw [hE]
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  have hd : 2*(s : ℂ)-1 ≠ 0 := by
    intro h; have hh := congrArg Complex.re h; simp at hh; linarith
  field_simp [hsC, hd]
  ring_nf
  have hd' : -1+(s : ℂ)*2 ≠ 0 := by convert hd using 1; ring
  linear_combination mul_inv_cancel₀ hd'

/-- Absolute admission of the real Laplace transform for exponent greater than one. -/
theorem integrable_ccmPrimeMomentLogPotential {s : ℝ} (hs : 1 < s) :
    IntegrableOn (fun t => Real.exp (-s*t)*ccmPrimeMomentLogPotential t) (Ioi 0) := by
  have hm := (exp_neg_integrableOn_Ioi 0 (by linarith : 0 < s-1)).const_mul
    (chebyshevDeficitConst+2)
  refine hm.mono' ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
    continuous_ccmPrimeMomentLogPotential).aestronglyMeasurable ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc Real.exp (-s*t)*|ccmPrimeMomentLogPotential t| ≤
      Real.exp (-s*t)*((chebyshevDeficitConst+2)*Real.exp t) :=
        mul_le_mul_of_nonneg_left (ccmPrimeMomentLogPotential_bound ht.le) (Real.exp_pos _).le
    _ = (chebyshevDeficitConst+2)*Real.exp (-(s-1)*t) := by
      rw [show -(s-1)*t = -s*t+t by ring, Real.exp_add]; ring

/-- The continuous potential is exactly the full finite von Mangoldt expression. -/
theorem ccmPrimeMomentLogPotential_eq_source {T : ℝ} (hT : 0 ≤ T) :
    ccmPrimeMomentLogPotential T =
      Real.sqrt (Real.exp T)*(primeMassHalf (Real.exp T)+2)-Real.exp T-
        Chebyshev.psi (Real.exp T)-1 := by
  have hm := vonMangoldt_criticalMellinError_identity (Real.exp T) (Real.one_le_exp hT)
  change criticalMellinPrimeMass T = _ at hm
  rw [criticalMellinPrimeMass_eq_primeMassHalf,
    criticalMellinError_integral_exp_substitution hT,
    ← intervalIntegral.integral_of_le hT] at hm
  change primeMassHalf (Real.exp T) = 2*Real.sqrt (Real.exp T)-1+
    criticalMellinNormalizedChebyshevError T+(1/2)*ccmPrimeMomentErrorPrimitive T at hm
  have heq : Real.exp (T/2)^2 = Real.exp T := by
    rw [pow_two, ← Real.exp_add]; congr 1; ring
  have hsqrt : Real.sqrt (Real.exp T) = Real.exp (T/2) := by
    rw [← heq, Real.sqrt_sq (Real.exp_pos _).le]
  have he : Real.exp (T/2)*criticalMellinNormalizedChebyshevError T =
      Chebyshev.psi (Real.exp T)-Real.exp T := by
    rw [criticalMellinNormalizedChebyshevError_eq_apertureError,
      criticalMellinChebyshevError_eq_exp]
    have hc : Real.exp (T/2)*Real.exp (-T/2) = 1 := by
      rw [← Real.exp_add, show T/2 + -T/2 = 0 by ring, Real.exp_zero]
    linear_combination (Chebyshev.psi (Real.exp T)-Real.exp T)*hc
  rw [hsqrt] at hm ⊢
  unfold ccmPrimeMomentLogPotential
  linear_combination -Real.exp (T/2)*hm - he - 2*heq

end RHTower
