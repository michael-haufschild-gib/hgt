/-
Cubic cusp Fourier kernels adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicHyperbolicFourierKernel
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisensteinResidueSeries

/-!
# Fourier transforms of shifted cusp kernels

Factor each nonzero primitive row into a translated and scaled hyperbolic
kernel. Translation gives its exact trace phase, and height scaling gives
`v^(2-s)`. Translation invariance of the cusp fundamental domain also
proves orthogonality of every nontrivial dual-lattice character.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical ENNReal Pointwise
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi

def shiftedHeightKernel (v : ℝ) (s b z : ℂ) : ℂ :=
  (v:ℂ)^(-s)*hyperbolicKernel s ((z+b)/(v:ℂ))

lemma shiftedHeightKernel_integrable (v : ℝ) (hv : 0 < v) (s b : ℂ) (hs : 1 < s.re) :
    Integrable (shiftedHeightKernel v s b) := by
  have h := ((hyperbolicKernel_integrable s hs).comp_smul (inv_ne_zero hv.ne')).comp_add_right b
  apply (h.const_mul ((v:ℂ)^(-s))).congr
  exact Eventually.of_forall fun z => by
    simp only [shiftedHeightKernel,Complex.real_smul,Complex.ofReal_inv,div_eq_mul_inv,mul_comm]

lemma primitiveTerm_eq_shiftedHeightKernel (z : ℂ) (v : ℝ) (hv : 0 < v)
    (s : ℂ) (c d : O) (hc : c ≠ 0) :
    primitiveTerm z v s c d =
      (ringComplex (symbol c d)*(‖ringComplex c‖^2:ℝ) ^ (-s:ℂ))*
        shiftedHeightKernel v s (ringComplex d/ringComplex c) z := by
  have hc' := ringComplex_ne_zero hc
  have hnorm : 0 < ‖ringComplex c‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hc')
  have hfac : ringComplex c*z+ringComplex d =
      ringComplex c*(z+ringComplex d/ringComplex c) := by field_simp
  have heq : v/(‖ringComplex c*z+ringComplex d‖^2+‖ringComplex c‖^2*v^2) =
      ((‖ringComplex c‖^2*v)*(1+‖(z+ringComplex d/ringComplex c)/(v:ℂ)‖^2))⁻¹ := by
    rw [hfac,norm_mul,mul_pow,norm_div,Complex.norm_real,Real.norm_of_nonneg hv.le]
    field_simp
    ; ring
  unfold primitiveTerm shiftedHeightKernel hyperbolicKernel
  rw [heq,Complex.ofReal_inv,inv_cpow_ofReal_nonneg (by positivity),← Complex.cpow_neg]
  rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (mul_nonneg hnorm.le hv.le) (by positivity),
    Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg hnorm.le hv.le]
  ring

lemma primitiveTerm_integrable (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 1 < s.re)
    (c d : O) (hc : c ≠ 0) : Integrable (fun z => primitiveTerm z v s c d) := by
  simp_rw [primitiveTerm_eq_shiftedHeightKernel _ v hv s c d hc]
  exact (shiftedHeightKernel_integrable v hv s _ hs).const_mul _

lemma traceIntegral_translate (f : ℂ → ℂ) (b freq : ℂ) :
    (∫ z : ℂ,f (z+b)*tracePhase (-freq*z))=
      tracePhase (freq*b)*(∫ z : ℂ,f z*tracePhase (-freq*z)) := by
  have heq (z : ℂ) : f (z+b)*tracePhase (-freq*z)=
      tracePhase (freq*b)*(f (z+b)*tracePhase (-freq*(z+b))) := by
    rw [mul_left_comm (tracePhase (freq*b)),
      ← AddChar.map_add_eq_mul]
    congr 2
    ring
  simp_rw [heq]
  rw [integral_const_mul,integral_add_right_eq_self (fun z => f z*tracePhase (-freq*z)) b]

lemma traceIntegral_scale (v : ℝ) (hv : 0 < v) (s freq : ℂ) :
    (∫ z : ℂ,hyperbolicKernel s (z/(v:ℂ))*tracePhase (-freq*z))=
      (v:ℂ)^2*sourceFourierKernel s (freq*v) := by
  have heq (z : ℂ) : hyperbolicKernel s (z/(v:ℂ))*tracePhase (-freq*z)=
      (fun w : ℂ => hyperbolicKernel s w*tracePhase (-(freq*v)*w)) (v⁻¹ • z) := by
    simp only [Complex.real_smul,Complex.ofReal_inv]
    congr 2
    · ring
    · field_simp [Complex.ofReal_ne_zero.mpr hv.ne']
  simp_rw [heq]
  have h := Measure.integral_comp_inv_smul_of_nonneg (volume : Measure ℂ)
    (fun w : ℂ => hyperbolicKernel s w*tracePhase (-(freq*v)*w)) hv.le
  simpa only [Complex.finrank_real_complex,Complex.real_smul,Complex.ofReal_pow,sourceFourierKernel] using h

lemma traceIntegral_shiftedHeightKernel (v : ℝ) (hv : 0 < v) (s b freq : ℂ) :
    (∫ z : ℂ,shiftedHeightKernel v s b z*tracePhase (-freq*z))=
      (v:ℂ)^(2-s)*tracePhase (freq*b)*sourceFourierKernel s (freq*v) := by
  simp only [shiftedHeightKernel,mul_assoc]
  rw [integral_const_mul,traceIntegral_translate (fun z => hyperbolicKernel s (z/(v:ℂ))) b freq,
    traceIntegral_scale v hv s freq]
  have hp : (v:ℂ)^(-s)*(v:ℂ)^2=(v:ℂ)^(2-s) := by
    rw [← Complex.cpow_natCast,← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hv.ne')]
    congr 1
    ring
  calc
    _ = ((v:ℂ)^(-s)*(v:ℂ)^2)*tracePhase (freq*b)*sourceFourierKernel s (freq*v) := by ring
    _ = _ := by rw [hp]; ring
lemma period_integral_translation (f : ℂ → ℂ)
    (hperiod : ∀ (n : O) (z : ℂ), f (z+3*ringComplex n)=f z) (b : ℂ) :
    (∫ z in periodDomain,f (b+z))=∫ z in periodDomain,f z := by
  have hperiod' (n : periodLattice) (z : ℂ) : f (n+ᵥz)=f z := by
    obtain ⟨m,rfl⟩ := periodEquiv.surjective n
    change f (3*ringComplex m+z)=f z
    simpa only [add_comm] using hperiod m z
  have hD := periodDomain_fundamental.vadd_of_comm b
  have heq := periodDomain_fundamental.setIntegral_eq hD hperiod'
  have hchange := (measurePreserving_add_left volume b).setIntegral_image_emb
    (measurableEmbedding_const_vadd b) f periodDomain
  exact hchange.symm.trans heq.symm

lemma tracePhase_quarter_eq_neg_one : tracePhase (1/4:ℂ)=-1 := by
  change Complex.exp (2*Real.pi*Complex.I*((1/4:ℂ)+starRingEnd ℂ (1/4:ℂ)))=-1
  norm_num only [map_div₀,map_one,map_ofNat]
  convert Complex.exp_pi_mul_I using 1
  congr 1
  ring

lemma cuspFrequency_ne_zero (h : O) (hh : h ≠ 0) : cuspFrequency h ≠ 0 :=
  div_ne_zero (ringComplex_ne_zero hh) (mul_ne_zero (by norm_num) (ringComplex_ne_zero traceLambda_ne_zero))

theorem integral_cusp_character (h : O) :
    (∫ z in periodDomain,tracePhase (-cuspFrequency h*z))=
      if h=0 then ((9*Real.sqrt 3/2:ℝ):ℂ) else 0 := by
  by_cases hh : h=0
  · subst h
    simp only [cuspFrequency,map_zero,zero_div,neg_zero,zero_mul,
      AddChar.map_zero_eq_one,ite_true,setIntegral_const,measureReal_def,periodDomain_volume,
      ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ 9*Real.sqrt 3/2),Complex.real_smul,mul_one]
  · rw [if_neg hh]
    let freq := cuspFrequency h
    let b : ℂ := -(4*freq)⁻¹
    have hfreq : freq ≠ 0 := cuspFrequency_ne_zero h hh
    have harg : -freq*b=(1/4:ℂ) := by dsimp [b]; field_simp
    have hphase : tracePhase (-freq*b)=-1 := by rw [harg,tracePhase_quarter_eq_neg_one]
    have heq := period_integral_translation
      (fun z => tracePhase (-freq*z))
      (fun n z => cuspFrequency_negative_period h n z) b
    have hpoint (z : ℂ) : tracePhase (-freq*(b+z))=
        -tracePhase (-freq*z) := by
      rw [mul_add,AddChar.map_add_eq_mul,hphase,neg_one_mul]
    simp_rw [hpoint,integral_neg] at heq
    linear_combination (-1/2:ℂ)*heq

#print axioms primitiveTerm_integrable
#print axioms traceIntegral_shiftedHeightKernel
#print axioms integral_cusp_character
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
