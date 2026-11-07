/-
Cubic cusp Fourier periodization adapted from OpenAI's formalization,
Apache-2.0. See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.TheCubicCuspPeriodLattice
import GaloisForLFunctions.MetaplecticMobiusDescent.TheDifferentNormalizesTheTraceCharacter

/-!
# Fourier periodization with the actual trace normalization

The complex trace exponential is trivial on `(1+2ω)⁻¹O`. Frequencies in
`(3(1+2ω))⁻¹O` therefore pair with the actual cusp lattice `3O`.
Absolute integrability justifies Fourier unfolding on its fundamental domain.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein Eisenstein.Coordinates

/-- Exponentiate the real trace from the complex plane. -/
def tracePhase : AddChar ℂ ℂ where
  toFun z := Complex.exp (2*Real.pi*Complex.I*(z+starRingEnd ℂ z))
  map_zero_eq_one' := by simp
  map_add_eq_mul' z w := by
    rw [←Complex.exp_add]
    congr 1
    simp only [map_add]
    ring

lemma tracePhase_continuous : Continuous tracePhase := by
  change Continuous (fun z : ℂ => Complex.exp (2*Real.pi*Complex.I*(z+starRingEnd ℂ z)))
  fun_prop

lemma tracePhase_norm (z : ℂ) : ‖tracePhase z‖=1 := by
  change ‖Complex.exp (2*Real.pi*Complex.I*(z+starRingEnd ℂ z))‖=1
  rw [Complex.norm_exp]
  have hre : (2*Real.pi*Complex.I*(z+starRingEnd ℂ z)).re=0 := by
    simp [Complex.mul_re,Complex.mul_im]
  rw [hre,Real.exp_zero]

lemma complex_omega_conjugate : starRingEnd ℂ (ringComplex omega)=-1-ringComplex omega := by
  apply Complex.ext
  · simp only [Complex.conj_re,Complex.sub_re,Complex.neg_re,Complex.one_re]
    linarith only [complex_omega_coordinates.1]
  · simp

lemma complex_traceLambda_conjugate :
    starRingEnd ℂ (ringComplex traceLambda)=-ringComplex traceLambda := by
  simp only [traceLambda,map_add,map_mul,map_one,map_ofNat,complex_omega_conjugate]
  ring

lemma complexTrace_div_traceLambda (a b : ℤ) :
    ringComplex (eval a b)/ringComplex traceLambda+
      starRingEnd ℂ (ringComplex (eval a b)/ringComplex traceLambda)=(b:ℂ) := by
  have hd : ringComplex traceLambda≠0 := ringComplex_ne_zero traceLambda_ne_zero
  rw [map_div₀,complex_traceLambda_conjugate,ringComplex_eval]
  simp only [map_add,map_mul,map_intCast,complex_omega_conjugate]
  field_simp [hd]
  simp only [traceLambda,map_add,map_mul,map_one,map_ofNat]
  ring

lemma tracePhase_embedding_div_traceLambda (n : O) :
    tracePhase (ringComplex n/ringComplex traceLambda)=1 := by
  change Complex.exp (2*Real.pi*Complex.I*(ringComplex n/ringComplex traceLambda+
    starRingEnd ℂ (ringComplex n/ringComplex traceLambda)))=1
  rw [←eval_coords n,complexTrace_div_traceLambda]
  rw [mul_comm]
  exact Complex.exp_int_mul_two_pi_mul_I _

def cuspFrequency (h : O) : ℂ := ringComplex h/(3*ringComplex traceLambda)

lemma cuspFrequency_period (h n : O) :
    tracePhase (cuspFrequency h*(3*ringComplex n))=1 := by
  have heq : cuspFrequency h*(3*ringComplex n)=ringComplex (h*n)/ringComplex traceLambda := by
    rw [cuspFrequency,map_mul]
    field_simp
  rw [heq]
  exact tracePhase_embedding_div_traceLambda (h*n)

lemma cuspFrequency_negative_period (h n : O) (z : ℂ) :
    tracePhase (-cuspFrequency h*(z+3*ringComplex n))=
      tracePhase (-cuspFrequency h*z) := by
  rw [mul_add,AddChar.map_add_eq_mul]
  have hp : tracePhase (-cuspFrequency h*(3*ringComplex n))=1 := by
    rw [neg_mul,AddChar.map_neg_eq_inv,cuspFrequency_period,inv_one]
  rw [hp,mul_one]

lemma trace_mul_integrable (f : ℂ → ℂ) (hf : Integrable f) (freq : ℂ) :
    Integrable (fun z => f z*tracePhase (-freq*z)) := by
  have hchar : Continuous (fun z : ℂ => tracePhase (-freq*z)) := by
    change Continuous (fun z : ℂ => Complex.exp (2*Real.pi*Complex.I*
      ((-freq*z)+starRingEnd ℂ (-freq*z))))
    fun_prop
  refine hf.norm.mono' (hf.aestronglyMeasurable.mul hchar.aestronglyMeasurable) ?_
  exact Eventually.of_forall fun z => by simp only [norm_mul,tracePhase_norm,mul_one,le_refl]

lemma integrableOn_periodization (f : ℂ → ℂ) (hf : Integrable f) :
    IntegrableOn (fun z => ∑' n : O,f (z+3*ringComplex n)) periodDomain := by
  let : Countable O := Coordinates.coordinateEquiv.injective.countable
  have hm (n : O) : AEStronglyMeasurable (fun z => f (z+3*ringComplex n))
      (volume.restrict periodDomain) :=
    (hf.comp_add_right (3*ringComplex n)).aestronglyMeasurable.restrict
  refine ⟨AEStronglyMeasurable.tsum hm, ?_⟩
  change (∫⁻ z in periodDomain,‖∑' n : O,f (z+3*ringComplex n)‖ₑ)<⊤
  apply lt_of_le_of_lt (lintegral_mono fun z => enorm_tsum_le_tsum_enorm) _
  rw [lintegral_tsum (fun n => (hm n).enorm)]
  exact lt_top_iff_ne_top.mpr (periodization_lintegral_norm_ne_top f hf)

theorem integral_fourier_periodization (f : ℂ → ℂ) (hf : Integrable f) (h : O) :
    (∫ z in periodDomain,(∑' n : O,f (z+3*ringComplex n))*
      tracePhase (-cuspFrequency h*z))=
        ∫ z : ℂ,f z*tracePhase (-cuspFrequency h*z) := by
  have heq : (fun z : ℂ => (∑' n : O,f (z+3*ringComplex n))*
      tracePhase (-cuspFrequency h*z)) =
      (fun z : ℂ => ∑' n : O,f (z+3*ringComplex n)*
        tracePhase (-cuspFrequency h*(z+3*ringComplex n))) := by
    funext z
    simp only [cuspFrequency_negative_period,tsum_mul_right]
  rw [heq]
  exact integral_periodization _ (trace_mul_integrable f hf (cuspFrequency h))

#print axioms tracePhase_embedding_div_traceLambda
#print axioms cuspFrequency_period
#print axioms integral_fourier_periodization
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
