import GaloisForLFunctions.HTGeometry.GammaFactorialComposition
import GaloisForLFunctions.HTGeometry.DigammaGammaLocalHypertranscendence

namespace GaloisForLFunctions

open Complex Filter Topology

noncomputable section

theorem exists_polynomialJet_relation_on_rightHalfPlane_of_eventual_differentialRelation_outer_comp_Gamma
    (u : ℂ → ℂ) (hu : ∀ z ∈ rightHalfPlane, AnalyticAt ℂ u z)
    {r : ℕ} (P : MvPolynomial (Fin (r + 2)) ℂ) (hP0 : P ≠ 0)
    (hrel : ∀ x ∈ gammaFactorialMicroscopeDomain, ∀ᶠ n : ℕ in atTop,
      MvPolynomial.eval
        (Fin.cons (-(n : ℂ) + reciprocalGammaFactorialScale n * x)
          (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ)
            (fun z => u (Complex.Gamma z))
            (-(n : ℂ) + reciprocalGammaFactorialScale n * x))) P = 0) :
    ∃ G : MvPolynomial (Fin (r + 1)) (Polynomial ℂ),
      G ≠ 0 ∧ ∀ z ∈ rightHalfPlane,
        MvPolynomial.eval₂ (Polynomial.evalRingHom z)
          (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) u z) G = 0 := by
  obtain ⟨Q, hQ0, hQvan⟩ :=
    exists_nonzero_factorialInitialForm_of_eventual_differentialRelation
      (h := fun z => u (Complex.Gamma z))
      (f := outerReciprocalLimit u) (U := gammaFactorialMicroscopeDomain) P hP0 hrel
      (fun x hx j => iteratedDeriv_outerGamma_factorialBlowUp_tendsto u hu hx j)
  let G : MvPolynomial (Fin (r + 1)) (Polynomial ℂ) := mobiusJetPullback r Q
  have hGne : G ≠ 0 := mobiusJetPullback_ne_zero hQ0
  refine ⟨G, hGne, ?_⟩
  intro z hz
  have hx : -z⁻¹ ∈ gammaFactorialMicroscopeDomain :=
    neg_inv_mem_gammaFactorialMicroscopeDomain_of_mem_rightHalfPlane hz
  have hvalue := hQvan (-z⁻¹) hx
  have hmv : mobiusJetValue r u z =
      fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) (outerReciprocalLimit u) (-z⁻¹) := by
    funext j
    exact mobiusJetValue_outer_eq_limitJet u hu r z hz j
  rw [show G = mobiusJetPullback r Q from rfl, eval₂_mobiusJetPullback, hmv]
  exact hvalue

theorem no_eventual_differential_relation_outer_comp_Gamma
    (u : ℂ → ℂ) (hu : ∀ z ∈ rightHalfPlane, AnalyticAt ℂ u z)
    (hrigid : LocallyPolynomialJetRigidAt u 1)
    {r : ℕ} (P : MvPolynomial (Fin (r + 2)) ℂ) (hP0 : P ≠ 0) :
    ¬ ∀ x ∈ gammaFactorialMicroscopeDomain, ∀ᶠ n : ℕ in atTop,
      MvPolynomial.eval
        (Fin.cons (-(n : ℂ) + reciprocalGammaFactorialScale n * x)
          (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ)
            (fun z => u (Complex.Gamma z))
            (-(n : ℂ) + reciprocalGammaFactorialScale n * x))) P = 0 := by
  intro hrel
  obtain ⟨G, hG, hGvan⟩ :=
    exists_polynomialJet_relation_on_rightHalfPlane_of_eventual_differentialRelation_outer_comp_Gamma
      u hu P hP0 hrel
  apply (hrigid r G hG)
  have honePos : (1 : ℂ) ∈ rightHalfPlane := by simp [rightHalfPlane]
  filter_upwards [isOpen_rightHalfPlane.mem_nhds honePos] with z hz
  exact hGvan z hz

end

end GaloisForLFunctions
