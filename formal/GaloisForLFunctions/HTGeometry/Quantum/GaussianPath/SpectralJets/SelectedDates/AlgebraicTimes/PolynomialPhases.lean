import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicTimes.ExponentialSums
import GaloisForLFunctions.RHTower.PiTranscendenceSetup
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ExactContacts.PhasePolynomial

/-! # No surviving phase polynomial at an algebraic physical time -/

open Set MeasureTheory Filter Topology MvPolynomial Finset
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicTimes
open ExactContacts
noncomputable section

def complexParameterEval {m : ℕ} (x : Fin m → ℝ) : Parameters m →+* ℂ :=
  Complex.ofRealHom.comp (parameterEval x)

private theorem phase_expansion {I K : Type*} [Fintype I] [CommRing K] (φ : K →+* ℂ)
    (p : MvPolynomial I K) (w : I → ℝ) (t : ℝ) :
    MvPolynomial.eval₂ φ (fun i => energyPhase (w i) t) p =
      ∑ j : p.support, φ (p.coeff j.val)*Complex.exp ((-Complex.I*(monomialFrequency w j.val:ℂ))*(t:ℂ)) := by
  classical
  rw [Finset.sum_coe_sort p.support (fun j => φ (p.coeff j)*Complex.exp
    ((-Complex.I*(monomialFrequency w j:ℂ))*(t:ℂ))),MvPolynomial.eval₂_eq']
  apply Finset.sum_congr rfl
  intro d _
  congr 1
  simp only [energyPhase,←Complex.exp_nat_mul,←Complex.exp_sum,monomialFrequency,Complex.ofReal_sum,
    Complex.ofReal_mul,Complex.ofReal_natCast,mul_sum,sum_mul]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- For a rationally independent spectrum, no phase polynomial over the
coupling coordinates vanishes at any nonzero algebraic time unless every
coefficient already specializes to zero. All polynomials and dates are
quantified after the draw. -/
theorem ae_phase_polynomials {m : ℕ} {I : Type*} [Fintype I] {U : Set (Fin m → ℝ)} (hU : IsOpen U)
    (w : I → (Fin m → ℝ) → ℝ) (ha : ∀ i, AnalyticOnNhd ℝ (w i) U)
    (halg : ∀ (q : Fin m → ℚ), (fun i => (q i:ℝ))∈U → ∀ i, IsAlgebraic ℚ ((w i (fun j => (q j:ℝ)):ℝ):ℂ)) :
    ∀ᵐ x ∂(volume : Measure (Fin m → ℝ)), x∈U → RationallyIndependentFrequency (fun i => w i x) →
      ∀ (p : MvPolynomial I (Parameters m)) (t : ℝ), t≠0 → IsAlgebraic (parameterField x) t →
      (∃ j∈p.support, complexParameterEval x (p.coeff j)≠0) →
        MvPolynomial.eval₂ (complexParameterEval x) (fun i => energyPhase (w i x) t) p≠0 := by
  classical
  letI : Countable (Parameters m) := AddMonoidAlgebra.coeff_injective.countable
  letI : Countable (MvPolynomial I (Parameters m)) := AddMonoidAlgebra.coeff_injective.countable
  have H (p : MvPolynomial I (Parameters m)) :
      ∀ᵐ x ∂(volume : Measure (Fin m → ℝ)), x∈U → RationallyIndependentFrequency (fun i => w i x) →
        ∀ t : ℝ, t≠0 → IsAlgebraic (parameterField x) t →
        (∃ j∈p.support, complexParameterEval x (p.coeff j)≠0) →
        MvPolynomial.eval₂ (complexParameterEval x) (fun i => energyPhase (w i x) t) p≠0 := by
    let a (j : ↥p.support) (x : Fin m → ℝ) := complexParameterEval x (p.coeff j.val)
    let λ' (j : ↥p.support) (x : Fin m → ℝ) := -Complex.I*(monomialFrequency (fun i => w i x) j.val:ℂ)
    have hac (j : ↥p.support) : AnalyticOnNhd ℝ (a j) U := fun x _ =>
      (Complex.ofRealCLM.analyticAt _).comp (analytic_parameterEval _ x)
    have hwa (j : ↥p.support) : AnalyticOnNhd ℝ (λ' j) U := by
      intro x hx
      apply analyticAt_const.mul
      apply (Complex.ofRealCLM.analyticAt _).comp
      exact Finset.analyticAt_fun_sum _ fun i _ => analyticAt_const.mul (ha i x hx)
    have alg (q : Fin m → ℚ) (hq : (fun i => (q i:ℝ))∈U) (j : ↥p.support) :
        IsAlgebraic ℚ (a j (fun i => (q i:ℝ))) ∧ IsAlgebraic ℚ (λ' j (fun i => (q i:ℝ))) := by
      let K := algebraicClosure ℚ ℂ
      constructor
      · change IsAlgebraic ℚ (((parameterEval (fun i => (q i:ℝ)) (p.coeff j.val)):ℝ):ℂ)
        rw [parameterEval_rat,RingHom.comp_apply]
        exact isAlgebraic_algebraMap _
      · apply mem_algebraicClosure_iff.mp
        apply K.mul_mem (K.neg_mem (mem_algebraicClosure_iff.mpr GaloisForLFunctions.RHTower.isAlgebraic_I))
        simp only [monomialFrequency,Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_natCast]
        exact K.sum_mem fun i _ => K.mul_mem (K.natCast_mem _) (mem_algebraicClosure_iff.mpr (halg q hq i))
    filter_upwards [ae_exponential_sum_ne_zero hU a λ' hac hwa alg] with x hx hu hi t ht htalg hcoef
    obtain ⟨j,hj,hne⟩ := hcoef
    have inj : Function.Injective (fun j => λ' j x) := by
      intro v u h
      apply Subtype.ext
      exact injective_monomialFrequency hi (Complex.ofReal_injective
        (mul_left_cancel₀ (neg_ne_zero.mpr Complex.I_ne_zero) h))
    rw [phase_expansion]
    exact hx hu inj ⟨⟨j,hj⟩,hne⟩ t ht htalg
  exact (ae_all_iff.mpr H).mono fun x h hu hi p => h p hu hi

#print axioms ae_phase_polynomials
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicTimes
