import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspWignerPairHelmholtzForm
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Exact continuous prime main term of the critical theta Wigner kernel

The literal pair kernel at `σ = 1/2` is a positive constant times
`(1/4 - D²) cosh(t)^(-5/2)`. Its two-sided pairing against the continuous
prime density `exp(v/2) dv` is exactly the negative of that constant times
`cosh(t)^(-5/2)`. The proof retains both boundary terms and establishes
absolute integrability from exponential bounds.

This removes the continuous prime main term before estimating the signed
arithmetic remainder. It supplies no bound for that remainder or for the
full mixed-packet quadratic form.
-/

open Real MeasureTheory Set Filter Topology
namespace RHTower
namespace ThetaCuspWignerPrimeMainTerm


private noncomputable def f (x : ℝ) : ℝ := Real.cosh x ^ (-(5/2:ℝ))
private noncomputable def d (x : ℝ) : ℝ := -(5/2:ℝ) *
  (Real.cosh x ^ (-(7/2:ℝ)) * Real.sinh x)
private noncomputable def k (x : ℝ) : ℝ := (35/4:ℝ)*Real.cosh x^(-(9/2:ℝ)) - 6*f x

private lemma f_pos (x : ℝ) : 0 < f x := Real.rpow_pos_of_pos (Real.cosh_pos _) _
private lemma f_neg (x : ℝ) : f (-x) = f x := by simp [f]
private lemma d_neg (x : ℝ) : d (-x) = -d x := by simp [d]
private lemma k_neg (x : ℝ) : k (-x) = k x := by simp [k, f]

private lemma f_deriv (x : ℝ) : HasDerivAt f (d x) x := by
  convert hasDerivAt_thetaCuspWignerCoshPower (1/2) x using 1 <;>
    norm_num [f, d, thetaCuspWignerCoshPower]
  funext y
  norm_num [f, thetaCuspWignerCoshPower]

private lemma d_deriv (x : ℝ) : HasDerivAt d (f x/4-k x) x := by
  have h := hasDerivAt_deriv_thetaCuspWignerCoshPower (1/2) x
  norm_num at h
  convert h using 1
  · funext z
    dsimp [d]
    ring
  · dsimp [k, f]
    ring

private lemma d_abs (x : ℝ) : |d x| ≤ (5/2:ℝ)*f x := by
  have hs : |Real.sinh x| ≤ Real.cosh x := by
    have h := Real.cosh_sq_sub_sinh_sq x
    have h' := sq_abs (Real.sinh x)
    have hc := Real.cosh_pos x
    nlinarith [abs_nonneg (Real.sinh x)]
  have he : Real.cosh x^(-(7/2:ℝ))*Real.cosh x = f x := by
    have h := Real.rpow_add (Real.cosh_pos x) (-(7/2:ℝ)) 1
    rw [Real.rpow_one] at h
    norm_num at h
    exact h.symm
  calc |d x| = (5/2:ℝ)*(Real.cosh x^(-(7/2:ℝ))*|Real.sinh x|) := by
        norm_num [d, abs_mul, abs_of_pos (Real.rpow_pos_of_pos (Real.cosh_pos x) (-(7/2:ℝ)))]
    _ ≤ (5/2:ℝ)*(Real.cosh x^(-(7/2:ℝ))*Real.cosh x) := by gcongr
    _ = _ := by rw [he]

private lemma k_abs (x : ℝ) : |k x| ≤ 15*f x := by
  have he : Real.cosh x^(-(9/2:ℝ)) ≤ f x :=
    Real.rpow_le_rpow_of_exponent_le (Real.one_le_cosh x) (by norm_num)
  have hp : 0 < Real.cosh x^(-(9/2:ℝ)) := Real.rpow_pos_of_pos (Real.cosh_pos _) _
  have h : |(35/4:ℝ)*Real.cosh x^(-(9/2:ℝ))-6*f x| ≤
      |(35/4:ℝ)*Real.cosh x^(-(9/2:ℝ))|+|6*f x| := by
    simpa only [sub_zero, zero_sub, abs_neg] using
      abs_sub_le ((35/4:ℝ)*Real.cosh x^(-(9/2:ℝ))) 0 (6*f x)
  have hA : 0 < (35/4:ℝ)*Real.cosh x^(-(9/2:ℝ)) := mul_pos (by norm_num) hp
  rw [abs_of_pos hA, abs_of_pos (mul_pos (by norm_num) (f_pos x))] at h
  dsimp [k]
  nlinarith [f_pos x]

private lemma f_bound (x : ℝ) : f x ≤ 4*Real.exp (-2*x) := by
  have hcosh : Real.exp x ≤ 2*Real.cosh x := by
    rw [Real.cosh_eq]
    linarith [Real.exp_pos (-x)]
  have hexp : Real.exp x*Real.exp (-x)=1 := by rw [← Real.exp_add]; simp
  have hi : (Real.cosh x)⁻¹ ≤ 2*Real.exp (-x) := by
    rw [← one_div]
    apply (div_le_iff₀ (Real.cosh_pos x)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hcosh (Real.exp_pos (-x)).le]
  have hf : f x ≤ Real.cosh x^(-2:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (Real.one_le_cosh x) (by norm_num)
  have hr : Real.cosh x^(-2:ℝ) = ((Real.cosh x)⁻¹)^2 := by
    rw [show (-2:ℝ)=-(2:ℝ) by norm_num, Real.rpow_neg (Real.cosh_pos x).le]
    norm_num [Real.rpow_natCast, inv_pow]
  have he : Real.exp (-x)^2 = Real.exp (-2*x) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hsq := (sq_le_sq₀ (inv_nonneg.mpr (Real.cosh_pos x).le)
    (by positivity : 0 ≤ 2*Real.exp (-x))).mpr hi
  rw [hr] at hf
  nlinarith [he]

private lemma weighted_f_bound (t v : ℝ) :
    Real.exp (v/2)*f (t+v) ≤ 4*Real.exp (-2*t)*Real.exp (-(3/2:ℝ)*v) := by
  calc Real.exp (v/2)*f (t+v)
      ≤ Real.exp (v/2)*(4*Real.exp (-2*(t+v))) :=
        mul_le_mul_of_nonneg_left (f_bound _) (Real.exp_pos _).le
    _ = _ := by
      rw [show Real.exp (v/2)*(4*Real.exp (-2*(t+v))) =
        4*(Real.exp (v/2)*Real.exp (-2*(t+v))) by ring,
        ← Real.exp_add, mul_assoc, ← Real.exp_add]
      congr 2
      ring

private lemma weighted_f_tendsto (t : ℝ) :
    Tendsto (fun v : ℝ => Real.exp (v/2)*f (t+v)) atTop (𝓝 0) := by
  have he : Tendsto (fun v : ℝ => Real.exp (-(3/2:ℝ)*v)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_neg (by norm_num : -(3/2:ℝ)<0)).mpr tendsto_id)
  apply squeeze_zero (fun v => mul_nonneg (Real.exp_pos _).le (f_pos _).le) (weighted_f_bound t)
  simpa using he.const_mul (4*Real.exp (-2*t))

private lemma weighted_k_integrable (t : ℝ) :
    IntegrableOn (fun v : ℝ => Real.exp (v/2)*k (t+v)) (Ioi 0) := by
  have hp (r : ℝ) : Continuous (fun v : ℝ => Real.cosh (t+v)^r) :=
    (Real.continuous_cosh.comp (continuous_const.add continuous_id)).rpow_const
      (fun v => Or.inl (Real.cosh_pos (t+v)).ne')
  have hcont : Continuous (fun v : ℝ => Real.exp (v/2)*k (t+v)) :=
    (Real.continuous_exp.comp (continuous_id.div_const 2)).mul
      ((continuous_const.mul (hp (-(9/2:ℝ)))).sub
        (continuous_const.mul (hp (-(5/2:ℝ)))))
  refine Integrable.mono'
    ((integrableOn_exp_mul_Ioi (by norm_num : -(3/2:ℝ)<0) 0).const_mul
      (15*(4*Real.exp (-2*t)))) hcont.aestronglyMeasurable.restrict ?_
  filter_upwards with v
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have h1 := mul_le_mul_of_nonneg_left (k_abs (t+v)) (Real.exp_pos (v/2)).le
  have h2 := mul_le_mul_of_nonneg_left (weighted_f_bound t v) (by norm_num : (0:ℝ) ≤ 15)
  nlinarith only [h1, h2]

private noncomputable def B (t v : ℝ) : ℝ := Real.exp (v/2)*(d (t+v)-f (t+v)/2)

private lemma B_deriv (t v : ℝ) : HasDerivAt (B t) (-Real.exp (v/2)*k (t+v)) v := by
  have hd := (d_deriv (t+v)).comp v ((hasDerivAt_id v).const_add t)
  have hf := (f_deriv (t+v)).comp v ((hasDerivAt_id v).const_add t)
  have he := ((hasDerivAt_id v).div_const 2).exp
  refine (he.mul (hd.sub (hf.div_const 2))).congr_deriv ?_
  dsimp
  ring

private lemma B_tendsto (t : ℝ) : Tendsto (B t) atTop (𝓝 0) := by
  have hf := weighted_f_tendsto t
  have hd : Tendsto (fun v : ℝ => Real.exp (v/2)*d (t+v)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun v => ?_) (show
      Tendsto (fun v : ℝ => (5/2:ℝ)*(Real.exp (v/2)*f (t+v))) atTop (𝓝 0) from by
        simpa using hf.const_mul (5/2:ℝ))
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    nlinarith [mul_le_mul_of_nonneg_left (d_abs (t+v)) (Real.exp_pos (v/2)).le]
  have h := hd.sub (hf.div_const 2)
  simp only [zero_div, sub_zero] at h
  convert h using 1
  funext v
  dsimp [B]
  ring

private lemma positive_mainterm (t : ℝ) :
    (∫ v : ℝ in Ioi 0, Real.exp (v/2)*k (t+v)) = d t-f t/2 := by
  have hi : IntegrableOn (fun v : ℝ => -Real.exp (v/2)*k (t+v)) (Ioi 0) := by
    convert (weighted_k_integrable t).neg using 1
    funext v
    simp [neg_mul]
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (fun v _ => B_deriv t v)
    hi (B_tendsto t)
  simp only [B, zero_div, Real.exp_zero, add_zero, one_mul, zero_sub, neg_mul, integral_neg] at h
  linarith

private lemma negative_mainterm (t : ℝ) :
    (∫ v : ℝ in Ioi 0, Real.exp (v/2)*k (t-v)) = -d t-f t/2 := by
  have he : (fun v : ℝ => Real.exp (v/2)*k (t-v)) =
      (fun v : ℝ => Real.exp (v/2)*k (-t+v)) := by
    funext v
    rw [show t-v=-(-t+v) by ring, k_neg]
  rw [he, positive_mainterm, d_neg, f_neg]

/-- The full continuous prime main term is exactly a negative decaying secant power. -/
private theorem mainterm_exact (t : ℝ) :
    (∫ v : ℝ in Ioi 0, Real.exp (v/2)*(k (t+v)+k (t-v))) = -f t := by
  have hm : IntegrableOn (fun v : ℝ => Real.exp (v/2)*k (t-v)) (Ioi 0) := by
    have he : (fun v : ℝ => Real.exp (v/2)*k (t-v)) =
        (fun v : ℝ => Real.exp (v/2)*k (-t+v)) := by
      funext v
      rw [show t-v=-(-t+v) by ring, k_neg]
    rw [he]
    exact weighted_k_integrable (-t)
  simp_rw [mul_add]
  rw [integral_add (weighted_k_integrable t) hm, positive_mainterm, negative_mainterm]
  ring


private lemma actual_kernel (x : ℝ) : thetaCuspWignerPairKernel (1/2) x =
    ((2*Real.pi)^(-(1/2:ℝ))*Real.Gamma (5/2)/2)*k x := by
  rw [thetaCuspWignerPairKernel_eq_shifted_second_deriv,
    deriv_deriv_thetaCuspWignerCoshPower]
  norm_num [thetaCuspWignerCoshPower, k, f]
  ring_nf
  simp

end ThetaCuspWignerPrimeMainTerm

open ThetaCuspWignerPrimeMainTerm in
/-- The continuous prime main term of the literal critical Wigner pair kernel,
including both logarithmic displacements, has an exact negative decaying value. -/
theorem thetaCuspWignerPairKernel_continuousPrimeMainTerm (t : ℝ) :
    (∫ v : ℝ in Ioi 0, Real.exp (v/2)*
      (thetaCuspWignerPairKernel (1/2) (t+v)+thetaCuspWignerPairKernel (1/2) (t-v))) =
      -((2*Real.pi)^(-(1/2:ℝ))*Real.Gamma (5/2)/2)*thetaCuspWignerCoshPower (1/2) t := by
  simp_rw [actual_kernel]
  calc
    _ = ((2*Real.pi)^(-(1/2:ℝ))*Real.Gamma (5/2)/2) *
        (∫ v : ℝ in Ioi 0, Real.exp (v/2)*(k (t+v)+k (t-v))) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with v
      ring
    _ = _ := by
      rw [mainterm_exact]
      norm_num [f, thetaCuspWignerCoshPower]

end RHTower
