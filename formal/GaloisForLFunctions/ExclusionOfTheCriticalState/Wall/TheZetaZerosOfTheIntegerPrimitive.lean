import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.IntegerQuadratureAsAFractionalPartConvolution
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.TheCriticalHalfLineStateHasNoBoundaryLaplaceZero

/-!
# Zeta zeros in the integer primitive of the actual state

Tilting the state gives the second Fourier factor in the lattice primitive.
On the closed right half-plane this factor never vanishes. Thus the observed
zero at any frequency on the left half of the critical strip is exactly a
zeta zero, including frequencies on the critical line.
-/

noncomputable section
open MeasureTheory Filter Set Topology Complex
open scoped FourierTransform
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri CriticalArithmeticCorrelationTheory HTGeometry

/-- Fourier transformation of the tilted representative gives the ground-state
Laplace value at the reflected imaginary frequency. -/
theorem fourier_tilted_state_rep {F Φ : ℝ → ℝ} (he : F =ᵐ[volume] Φ) (β ξ : ℝ) :
    𝓕 (fun u : ℝ => ((Real.exp (β*u)*Φ u:ℝ):ℂ)) ξ =
      negativeHalfLineLaplace (cx F) ((β:ℂ)-((2*Real.pi*ξ:ℝ):ℂ)*I) := by
  rw [Real.fourier_real_eq_integral_exp_smul,negativeHalfLineLaplace]
  apply integral_congr_ae
  filter_upwards [he] with u hu
  simp only [cx,hu,smul_eq_mul,Complex.ofReal_mul,Complex.ofReal_exp,← mul_assoc,← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Confinement of the ground-state representative supplies all the integrable
tilts required for the Fourier factorization of the integer primitive. -/
theorem state_representative_integerPrimitive_fourier {F Φ : ℝ → ℝ}
    (hd : CriticalHalfLineEnergyDomain F) (hΦ : Continuous Φ) (he : F =ᵐ[volume] Φ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u))
    {β : ℝ} (hβ : 0 ≤ β) (hβ' : β < 1/2) :
    let B := fun t : ℝ => (weightedIntegerPrimitive Φ β t:ℂ)
    Integrable B ∧ MemLp B 2 ∧ ∀ ξ : ℝ,
      let s := ((1/2-β:ℝ):ℂ)+((2*Real.pi*ξ:ℝ):ℂ)*I
      𝓕 B ξ = 𝓕 (fun u : ℝ => ((Real.exp (β*u)*Φ u:ℝ):ℂ)) ξ*(riemannZeta s/s) := by
  have hw {p : ℝ} (hp : -4 < p) : Integrable fun u => Real.exp (p*u)*Φ u := by
    apply (integrable_mul_rexp_of_domain hd hp).congr
    filter_upwards [he] with u hu
    rw [hu,mul_comm]
  have hp : Integrable fun u : ℝ => Real.exp (-u/2)*Φ u := by
    simpa only [show ∀ u : ℝ, (-1/2)*u=-u/2 by intro u; ring] using hw (by norm_num : (-4:ℝ)< -1/2)
  have hm : Integrable fun u : ℝ => Real.exp (u/2)*Φ u := by
    simpa only [show ∀ u : ℝ, (1/2)*u=u/2 by intro u; ring] using hw (by norm_num : (-4:ℝ)<1/2)
  exact weightedIntegerPrimitive_fourier hΦ hC hb hp hm hβ hβ' (hw (by linarith only [hβ]))

/-- Failure of RH gives a single confined state whose normalized integer
primitive records every zeta zero on 0 < Re s ≤ 1/2, with no extra zeros. -/
theorem riemannHypothesis_or_integerPrimitive_zero_set : RiemannHypothesis ∨
    ∃ (W₀ : ℝ) (F Φ : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ Continuous Φ ∧ F =ᵐ[volume] Φ ∧
      ∀ β : ℝ, 0 ≤ β → β < 1/2 →
        let B := fun t : ℝ => (weightedIntegerPrimitive Φ β t:ℂ)
        Integrable B ∧ MemLp B 2 ∧ ∀ ξ : ℝ,
          let s : ℂ := ((1/2-β:ℝ):ℂ)+((2*Real.pi*ξ:ℝ):ℂ)*I
          𝓕 B ξ = negativeHalfLineLaplace (cx F) (1/2-s)*(riemannZeta s/s) ∧
            (𝓕 B ξ=0 ↔ riemannZeta s=0) := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hr | ⟨W₀,F,hW,ht,hF⟩
  · exact Or.inl hr
  obtain ⟨_,_,Φ,hΦ,he,_,⟨C,hC,hb⟩,_⟩ := criticalState_exists_continuous_representative hW ht hF
  refine Or.inr ⟨W₀,F,Φ,hW,ht,hF,hΦ,he,fun β hβ hβ' => ?_⟩
  obtain ⟨hi,h2,hFour⟩ := state_representative_integerPrimitive_fourier
    (criticalHalfLineEnergyDomain_of_groundState hF) hΦ he hC hb hβ hβ'
  refine ⟨hi,h2,fun ξ => ?_⟩
  let s : ℂ := ((1/2-β:ℝ):ℂ)+((2*Real.pi*ξ:ℝ):ℂ)*I
  have hre : s.re=1/2-β := by simp [s]
  have hs : s ≠ 0 := fun e => by rw [e,zero_re] at hre; linarith only [hre,hβ']
  have harg : (β:ℂ)-((2*Real.pi*ξ:ℝ):ℂ)*I=1/2-s := by dsimp only [s]; push_cast; ring
  have hnon := criticalHalfLineGroundState_closedRightHalfPlaneLaplace_ne_zero hW ht hF
    (z := 1/2-s) (by simp [hre]; linarith only [hβ])
  have h : 𝓕 (fun t : ℝ => (weightedIntegerPrimitive Φ β t:ℂ)) ξ =
      𝓕 (fun u : ℝ => ((Real.exp (β*u)*Φ u:ℝ):ℂ)) ξ*(riemannZeta s/s) := hFour ξ
  rw [fourier_tilted_state_rep he,harg] at h
  refine ⟨h,?_⟩
  change (𝓕 (fun t : ℝ => (weightedIntegerPrimitive Φ β t:ℂ)) ξ=0 ↔ riemannZeta s=0)
  rw [h,mul_eq_zero,div_eq_zero_iff]
  simp only [hnon,hs,or_false,false_or]

#print axioms riemannHypothesis_or_integerPrimitive_zero_set
end GaloisForLFunctions.ExclusionOfTheCriticalState
