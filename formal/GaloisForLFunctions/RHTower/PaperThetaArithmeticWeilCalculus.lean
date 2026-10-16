import GaloisForLFunctions.RHTower.PaperThetaArithmeticHolomorphy
import GaloisForLFunctions.RHTower.CHMDComplexWeilForm
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! # Infinite theta synthesis and differentiation retain the full Weil form

Entire graph Taylor synthesis converges through the original signed Weil
energy. Its exact arithmetic expression retains both scalar components,
all prime powers and both polar moments. Along every affine complex line,
the full energy differentiates by the actual graph jet. Below full Xi
multiplicity, these graph jets are independent of the auxiliary cut.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex
open scoped InnerProductSpace

namespace RHTower.PaperThetaEndpoint
open CHMDDoobGraph

theorem cutArithmeticSection_jet_fullWeil (n : ℕ) (a : ℝ) (z : ℂ) :
    complexWeilEnergy (iteratedDeriv n (cutArithmeticSection a) z) =
      fullBVWeilExpression (fun x => (cutParameterJet n z a x).re) +
      fullBVWeilExpression (fun x => (cutParameterJet n z a x).im) :=
  complexWeilEnergy_eq_fullBV _ _ (cutArithmeticSection_jet_source n a z)
    (Complex.reCLM.lipschitz.comp_boundedVariationOn (boundedVariationOn_cutParameterJet n z a))
    (Complex.imCLM.lipschitz.comp_boundedVariationOn (boundedVariationOn_cutParameterJet n z a))

def cutArithmeticTaylorPartial (a : ℝ) (c z : ℂ) (N : ℕ) : ComplexArithmeticGraph :=
  ∑ n ∈ Finset.range N, (n.factorial : ℂ)⁻¹ • (z-c)^n •
    iteratedDeriv n (cutArithmeticSection a) c

theorem tendsto_cutArithmeticTaylorPartial (a : ℝ) (c z : ℂ) :
    Tendsto (cutArithmeticTaylorPartial a c z) atTop (𝓝 (cutArithmeticSection a z)) :=
  (hasSum_cutArithmeticSection_taylor a c z).tendsto_sum_nat

/-- Infinite synthesis passes through the full signed arithmetic form. -/
theorem tendsto_cutArithmeticTaylorPartial_fullWeil (a : ℝ) (c z : ℂ) :
    Tendsto (fun N => complexWeilEnergy (cutArithmeticTaylorPartial a c z N)) atTop
      (𝓝 (fullBVWeilExpression (fun x => (cutQuotient z a x).re) +
        fullBVWeilExpression (fun x => (cutQuotient z a x).im))) := by
  have he := cutArithmeticSection_jet_fullWeil 0 a z
  simp only [iteratedDeriv_zero, cutParameterJet] at he
  rw [← he]
  exact (continuous_complexWeilEnergy.tendsto _).comp
    (tendsto_cutArithmeticTaylorPartial a c z)

private theorem hasDerivAt_realWeilEnergy {F : ℝ → SourceGraph} {D : SourceGraph} {t : ℝ}
    (h : HasDerivAt F D t) :
    HasDerivAt (fun s => sourceWeilEnergy (F s)) (2*sourceWeilPair (F t) D) t := by
  have hs := sourceMap.hasFDerivAt.comp_hasDerivAt t h
  have hd := edgeMap.hasFDerivAt.comp_hasDerivAt t h
  have hc : HasDerivAt (fun s => sourceCoshMoment (F s)) (sourceCoshMoment D) t := by
    simpa only [sourceCoshMoment, inner_zero_left, add_zero, Function.comp_def] using!
      (hasDerivAt_const t (constantLift 1).val.fst).inner ℝ hs
  have hi : HasDerivAt (fun s => sourceSinhMoment (F s)) (sourceSinhMoment D) t := by
    simpa only [sourceSinhMoment, inner_zero_left, add_zero, Function.comp_def] using!
      (hasDerivAt_const t (sinhRatio_memLp.toLp sinhRatio)).inner ℝ hs
  have he := (((hd.inner ℝ hd).sub (hs.inner ℝ hs)).add
    (((hc.const_mul 2).mul hc))).sub (((hi.const_mul 2).mul hi))
  convert! he using 1
  simp only [sourceWeilPair, sourcePair, sourceCoshMoment, sourceSinhMoment, Function.comp_def,
    real_inner_comm (edgeMap D), real_inner_comm (sourceMap D)]
  ring

/-- The admitted derivative along any real affine parameter direction. -/
theorem hasDerivAt_cutArithmeticSection_line (a : ℝ) (c d : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => cutArithmeticSection a (c+(s:ℂ)*d))
      (d • deriv (cutArithmeticSection a) (c+(t:ℂ)*d)) t := by
  have hl : HasDerivAt (fun s : ℝ => c+(s:ℂ)*d) d t := by
    simpa only [one_mul, Complex.ofRealCLM_apply, Complex.ofReal_one] using
      (Complex.ofRealCLM.hasDerivAt.mul_const d).const_add c
  exact ((differentiable_cutArithmeticSection a) _).hasDerivAt.scomp t hl

/-- Parameter differentiation acts on the complete signed Weil form, without a sign premise. -/
theorem hasDerivAt_cutArithmetic_fullWeil (a : ℝ) (c d : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => complexWeilEnergy (cutArithmeticSection a (c+(s:ℂ)*d)))
      (2 * (sourceWeilPair
        (scalarGraphMap Complex.reCLM (cutArithmeticSection a (c+(t:ℂ)*d)))
        (scalarGraphMap Complex.reCLM (d • deriv (cutArithmeticSection a) (c+(t:ℂ)*d))) +
      sourceWeilPair
        (scalarGraphMap Complex.imCLM (cutArithmeticSection a (c+(t:ℂ)*d)))
        (scalarGraphMap Complex.imCLM (d • deriv (cutArithmeticSection a) (c+(t:ℂ)*d))))) t := by
  have h := hasDerivAt_cutArithmeticSection_line a c d t
  have hr := hasDerivAt_realWeilEnergy
    ((scalarGraphMap Complex.reCLM).hasFDerivAt.comp_hasDerivAt t h)
  have hi := hasDerivAt_realWeilEnergy
    ((scalarGraphMap Complex.imCLM).hasFDerivAt.comp_hasDerivAt t h)
  convert! hr.add hi using 1
  dsimp only [Function.comp_def]
  ring

/-- Native confluent graph jets below full Xi multiplicity require no cut choice. -/
theorem cutArithmeticSection_native_jet_cut_independent (rho : XiDivisorSupport)
    (j : Fin (xiSupportMultiplicity rho)) (a b : ℝ) :
    iteratedDeriv j.val (cutArithmeticSection a) (xiSpectralPointSupport rho) =
      iteratedDeriv j.val (cutArithmeticSection b) (xiSpectralPointSupport rho) := by
  apply CHMDComplexJump.source_injective
  apply Lp.ext
  filter_upwards [cutArithmeticSection_jet_source j.val a (xiSpectralPointSupport rho),
    cutArithmeticSection_jet_source j.val b (xiSpectralPointSupport rho)] with x ha hb
  rw [ha, hb, cutParameterJet_eq_native, cutParameterJet_eq_native]

/-- At the exact full multiplicity, the arithmetic graph still distinguishes every cut.
Passing to L² classes has not erased the first surviving native charge. -/
theorem cutArithmeticSection_terminal_jet_cut_injective (rho : XiDivisorSupport) :
    Function.Injective (fun a : ℝ => iteratedDeriv (xiSupportMultiplicity rho)
      (cutArithmeticSection a) (xiSpectralPointSupport rho)) := by
  have hlt (a b : ℝ) (hab : a < b) :
      iteratedDeriv (xiSupportMultiplicity rho) (cutArithmeticSection a)
          (xiSpectralPointSupport rho) ≠
        iteratedDeriv (xiSupportMultiplicity rho) (cutArithmeticSection b)
          (xiSpectralPointSupport rho) := by
    intro he
    have hs := congrArg (fun p : ComplexArithmeticGraph => p.val.fst) he
    have ha := cutArithmeticSection_jet_source (xiSupportMultiplicity rho) a
      (xiSpectralPointSupport rho)
    have hb := cutArithmeticSection_jet_source (xiSupportMultiplicity rho) b
      (xiSpectralPointSupport rho)
    rw [hs] at ha
    have hv := volume_absolutelyContinuous_mass.ae_eq (ha.symm.trans hb)
    obtain ⟨x, hx, heq⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      (isOpen_Ioo.measure_ne_zero volume (nonempty_Ioo.mpr hab)) (ae_restrict_of_ae hv)
    rw [cutParameterJet_right _ _ hx.1.le, cutParameterJet_left _ _ hx.2] at heq
    exact terminalParameterJet_jump_ne_zero rho x (sub_eq_zero.mpr heq)
  intro a b h
  rcases lt_trichotomy a b with hab | hab | hba
  · exact False.elim (hlt a b hab h)
  · exact hab
  · exact False.elim (hlt b a hba h.symm)

end RHTower.PaperThetaEndpoint
