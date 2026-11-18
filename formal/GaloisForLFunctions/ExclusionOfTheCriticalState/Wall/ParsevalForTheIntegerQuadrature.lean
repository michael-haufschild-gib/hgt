import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.SubcriticalMeanSquareOfTheIntegerQuadrature
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.RemovingSmallPrimesFromTheDensityReference
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Parseval for the exponentially tilted integer quadrature

A second tilt above the chosen one makes the tilted discrepancy absolutely
integrable on the positive ray. Integration by parts differentiates the
primitive and cancels its Mellin denominator.
-/

noncomputable section
open MeasureTheory Filter Set Topology Complex
open scoped FourierTransform
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri CriticalArithmeticCorrelationTheory HTGeometry

private theorem tilt_integrable_of_stronger_square_bound {D : ℝ → ℝ} (hm : Measurable D)
    (hi : IntegrableOn D (Iic 0)) {β μ : ℝ} (hβ : 0 ≤ β) (hlt : β < μ)
    (h2 : MemLp (fun t : ℝ => Real.exp (μ*t)*D t) 2) :
    Integrable (fun t : ℝ => Real.exp (β*t)*D t) := by
  have hneg : IntegrableOn (fun t : ℝ => Real.exp (β*t)*D t) (Iic 0) := by
    apply hi.norm.mono' (by fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
    rw [norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.2 (mul_nonpos_of_nonneg_of_nonpos hβ ht))
  have hExp : MemLp (fun t : ℝ => Real.exp ((β-μ)*t)) 2 (volume.restrict (Ioi 0)) := by
    apply (memLp_two_iff_integrable_sq_norm (by fun_prop)).2
    have he (t : ℝ) : ‖Real.exp ((β-μ)*t)‖^2 = Real.exp ((2*(β-μ))*t) := by
      rw [Real.norm_of_nonneg (Real.exp_pos _).le,pow_two,← Real.exp_add]; congr 1; ring
    simpa only [he] using integrableOn_exp_mul_Ioi (show 2*(β-μ)<0 by linarith only [hlt]) 0
  have hpos : IntegrableOn (fun t : ℝ => Real.exp (β*t)*D t) (Ioi 0) := by
    apply (hExp.integrable_mul (h2.mono_measure Measure.restrict_le_self)).congr
    exact Eventually.of_forall fun t => by
      change Real.exp ((β-μ)*t)*(Real.exp (μ*t)*D t)=_
      rw [← mul_assoc,← Real.exp_add,show (β-μ)*t+μ*t=β*t by ring]
  simpa only [Iic_union_Ioi,integrableOn_univ] using hneg.union hpos

/-- Fourier integration by parts for a first-order forced primitive with
absolutely integrable forcing and primitive. -/
private theorem fourier_forcing_of_primitive {B g : ℝ → ℂ} {σ : ℝ}
    (hi : Integrable B) (hg : Integrable g)
    (hd : ∀ t : ℝ, HasDerivAt B (-(σ:ℂ)*B t+g t) t) (ξ : ℝ) :
    𝓕 g ξ=((σ:ℂ)+((2*Real.pi*ξ:ℝ):ℂ)*I)*𝓕 B ξ := by
  have hd' : deriv B=fun t : ℝ => -(σ:ℂ)*B t+g t := funext fun t => (hd t).deriv
  have hi' : Integrable (deriv B) := by
    rw [hd']; exact (hi.const_mul (-(σ:ℂ))).add hg
  have he : g=deriv B+(σ:ℂ) • B := by funext t; simp only [hd',Pi.add_apply,Pi.smul_apply,smul_eq_mul]; ring
  have hadd : 𝓕 (deriv B+(σ:ℂ) • B) ξ = 𝓕 (deriv B) ξ + 𝓕 ((σ:ℂ) • B) ξ :=
    congrFun (VectorFourier.fourierIntegral_add (E := ℂ) (e := Real.fourierChar)
      (μ := (volume : Measure ℝ)) (L := innerₗ ℝ) Real.continuous_fourierChar (by fun_prop)
      hi' (hi.smul (σ:ℂ))) ξ
  have hsm : 𝓕 ((σ:ℂ) • B) ξ=(σ:ℂ) • 𝓕 B ξ :=
    congrFun (VectorFourier.fourierIntegral_const_smul (E := ℂ) Real.fourierChar volume (innerₗ ℝ) B (σ:ℂ)) ξ
  rw [he,hadd,hsm,Real.fourier_deriv hi (fun t => (hd t).differentiableAt) hi']
  simp only [smul_eq_mul]; push_cast; ring

/-- Exact Fourier transform and Parseval formula for the discrepancy of the
actual state at every subcritical tilt. -/
theorem criticalState_integer_quadrature_parseval {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal)) {F Φ : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W₀ F) (hc : Continuous Φ) (he : F =ᵐ[volume] Φ)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ u, |Φ u| ≤ K*Real.exp (2*u))
    {β : ℝ} (hβ : 0 ≤ β) (hβ' : β < 1/2) :
    let g := fun t : ℝ => (tiltedIntegerError Φ β t:ℂ)
    let Z := fun ξ : ℝ =>
      let s := ((1/2-β:ℝ):ℂ)+((2*Real.pi*ξ:ℝ):ℂ)*I
      riemannZeta s*negativeHalfLineLaplace (cx F) (1/2-s)
    Integrable g ∧ (∀ ξ, 𝓕 g ξ=Z ξ) ∧
      (∫ t, (tiltedIntegerError Φ β t)^2) = ∫ ξ, ‖Z ξ‖^2 := by
  let A := ∫ u, Real.exp (-u/2)*Φ u
  let D := fun t : ℝ => integerReferenceWave Φ t-Real.exp (t/2)*A
  let g := fun t : ℝ => (tiltedIntegerError Φ β t:ℂ)
  let B := fun t : ℝ => (weightedIntegerPrimitive Φ β t:ℂ)
  let σ := 1/2-β
  have hN := continuous_integerReferenceWave hc hK hb
  have hD : Continuous D := by dsimp only [D]; fun_prop
  have hDl : IntegrableOn D (Iic 0) := by
    have hexp := integrableOn_exp_mul_Iic (by norm_num : (0:ℝ)<1/2) 0
    apply (integerReference_integrableOn_left hc hb).sub
    simpa only [show ∀ t : ℝ, (1/2)*t=t/2 by intro t; ring] using hexp.mul_const A
  have hsub {a : ℝ} (ha : 0 ≤ a) (ha' : a < 1/2) : MemLp (tiltedIntegerError Φ a) 2 :=
    criticalState_subcritical_integer_error hW ht hF hc he hK hb ha ha'
  let μ := (β+1/2)/2
  have hμ : β < μ := by dsimp only [μ]; linarith only [hβ']
  have hμ' : μ < 1/2 := by dsimp only [μ]; linarith only [hβ']
  have hg : Integrable g := (tilt_integrable_of_stronger_square_bound hD.measurable hDl hβ hμ
    (hsub (hβ.trans hμ.le) hμ')).ofReal
  have h2 : MemLp g 2 := (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).2 (by
    simpa only [g,Complex.norm_real] using
      (memLp_two_iff_integrable_sq_norm (hsub hβ hβ').1).1 (hsub hβ hβ'))
  obtain ⟨hi,_,hFour⟩ := state_representative_integerPrimitive_fourier
    (criticalHalfLineEnergyDomain_of_groundState hF) hc he hK hb hβ hβ'
  have hderiv (t : ℝ) : HasDerivAt B (-(σ:ℂ)*B t+g t) t := by
    simpa only [B,g,σ,tiltedIntegerError,Complex.ofReal_add,Complex.ofReal_neg,Complex.ofReal_mul] using
      (hasDerivAt_weightedIntegerPrimitive hc hK hb β t).ofReal_comp
  have hresult (ξ : ℝ) :
      let s := (σ:ℂ)+((2*Real.pi*ξ:ℝ):ℂ)*I
      𝓕 g ξ = riemannZeta s*negativeHalfLineLaplace (cx F) (1/2-s) := by
    let s := (σ:ℂ)+((2*Real.pi*ξ:ℝ):ℂ)*I
    have hre : s.re=σ := by simp [s]
    have hs : s≠0 := fun e => by rw [e,zero_re] at hre; dsimp only [σ] at hre; linarith only [hre,hβ']
    have ha : (β:ℂ)-((2*Real.pi*ξ:ℝ):ℂ)*I=1/2-s := by dsimp only [s,σ]; push_cast; ring
    have h : 𝓕 B ξ=𝓕 (fun u : ℝ => ((Real.exp (β*u)*Φ u:ℝ):ℂ)) ξ*(riemannZeta s/s) := hFour ξ
    rw [fourier_tilted_state_rep he,ha] at h
    change 𝓕 B ξ=negativeHalfLineLaplace (cx F) (1/2-s)*(riemannZeta s/s) at h
    have hg' := fourier_forcing_of_primitive (σ := σ) hi hg hderiv ξ
    change 𝓕 g ξ=s*𝓕 B ξ at hg'
    change 𝓕 g ξ=riemannZeta s*negativeHalfLineLaplace (cx F) (1/2-s)
    rw [hg',h]; field_simp [hs] <;> ring
  refine ⟨hg,hresult,?_⟩
  have hval := (RHTower.integral_norm_sq_fourier_eq hg h2).symm
  simpa only [g,Complex.norm_real,Real.norm_eq_abs,sq_abs,hresult] using hval

#print axioms criticalState_integer_quadrature_parseval

/-- The state forced by failure of RH satisfies the same exact Parseval
identity on every subcritical line. -/
theorem riemannHypothesis_or_integer_quadrature_parseval : RiemannHypothesis ∨
    ∃ (W₀ : ℝ) (F Φ : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ Continuous Φ ∧ F =ᵐ[volume] Φ ∧
      ∀ β : ℝ, 0 ≤ β → β < 1/2 →
        let Z := fun ξ : ℝ =>
          let s := ((1/2-β:ℝ):ℂ)+((2*Real.pi*ξ:ℝ):ℂ)*I
          riemannZeta s*negativeHalfLineLaplace (cx F) (1/2-s)
        MemLp (tiltedIntegerError Φ β) 2 ∧
          (∫ t, (tiltedIntegerError Φ β t)^2) = ∫ ξ, ‖Z ξ‖^2 := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hr | ⟨W₀,F,hW,ht,hF⟩
  · exact Or.inl hr
  obtain ⟨_,_,Φ,hΦ,he,_,⟨C,hC,hb⟩,_⟩ := criticalState_exists_continuous_representative hW ht hF
  exact Or.inr ⟨W₀,F,Φ,hW,ht,hF,hΦ,he,fun _ hβ hβ' =>
    ⟨criticalState_subcritical_integer_error hW ht hF hΦ he hC hb hβ hβ',
     (criticalState_integer_quadrature_parseval hW ht hF hΦ he hC hb hβ hβ').2.2⟩⟩

#print axioms riemannHypothesis_or_integer_quadrature_parseval
end GaloisForLFunctions.ExclusionOfTheCriticalState
