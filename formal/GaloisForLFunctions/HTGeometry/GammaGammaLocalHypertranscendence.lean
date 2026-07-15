import GaloisForLFunctions.HTGeometry.GammaGammaFactorialBlowUp
import GaloisForLFunctions.HTGeometry.GammaFactorialCompositionLocal

namespace GaloisForLFunctions

open Complex Filter Topology

noncomputable section

def gammaGammaRegularSet : Set ℂ := digammaGammaRegularSet

theorem gammaGammaRegularSet_input_offPoles {z : ℂ}
    (hz : z ∈ gammaGammaRegularSet) : ∀ n : ℕ, z ≠ -(n : ℂ) := by
  exact digammaGammaRegularSet_input_offPoles hz

theorem analyticAt_Gamma_comp_Gamma {z : ℂ}
    (hz : z ∈ gammaGammaRegularSet) :
    AnalyticAt ℂ (fun w => Complex.Gamma (Complex.Gamma w)) z := by
  have hin := gammaGammaRegularSet_input_offPoles hz
  have hout : ∀ m : ℕ, Complex.Gamma z ≠ -(m : ℂ) := hz
  exact AnalyticAt.comp (f := Complex.Gamma) (x := z)
    (analyticAt_Gamma _ hout) (analyticAt_Gamma z hin)

theorem isOpen_gammaGammaRegularSet : IsOpen gammaGammaRegularSet := by
  exact isOpen_digammaGammaRegularSet

theorem gammaGammaRegularSet_compl_countable : gammaGammaRegularSetᶜ.Countable := by
  exact digammaGammaRegularSet_compl_countable

theorem gammaGammaRegularSet_isPreconnected : IsPreconnected gammaGammaRegularSet := by
  exact digammaGammaRegularSet_isPreconnected

theorem analyticAt_gammaGammaDifferentialEval (n : ℕ)
    (P : MvPolynomial (Fin (n + 2)) ℂ) {z : ℂ}
    (hz : z ∈ gammaGammaRegularSet) :
    AnalyticAt ℂ (fun w => MvPolynomial.eval
      (Fin.cons w (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ)
        (fun s => Complex.Gamma (Complex.Gamma s)) w)) P) z := by
  have hf := analyticAt_Gamma_comp_Gamma hz
  induction P using MvPolynomial.induction_on with
  | C c => simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => c) z)
  | add P Q hP hQ =>
      have heq : (fun w => MvPolynomial.eval
          (Fin.cons w (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ)
            (fun s => Complex.Gamma (Complex.Gamma s)) w)) (P + Q)) =
          fun w => MvPolynomial.eval
              (Fin.cons w (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ)
                (fun s => Complex.Gamma (Complex.Gamma s)) w)) P +
            MvPolynomial.eval
              (Fin.cons w (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ)
                (fun s => Complex.Gamma (Complex.Gamma s)) w)) Q := by
        funext w
        simp
      rw [heq]
      exact hP.add hQ
  | mul_X P i hP =>
      have heq : (fun w => MvPolynomial.eval
          (Fin.cons w (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ)
            (fun s => Complex.Gamma (Complex.Gamma s)) w))
              (P * MvPolynomial.X i)) =
          fun w => MvPolynomial.eval
              (Fin.cons w (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ)
                (fun s => Complex.Gamma (Complex.Gamma s)) w)) P *
            (Fin.cons w (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ)
              (fun s => Complex.Gamma (Complex.Gamma s)) w) : Fin (n + 2) → ℂ) i := by
        funext w
        simp
      rw [heq]
      refine hP.mul ?_
      induction i using Fin.cases with
      | zero =>
          simp only [Fin.cons_zero]
          exact analyticAt_id
      | succ j =>
          simp only [Fin.cons_succ]
          exact analyticAt_iteratedDeriv_of_analyticAt hf (j : ℕ)

theorem differentialRelation_GammaGamma_propagates
    {n : ℕ} {P : MvPolynomial (Fin (n + 2)) ℂ}
    {V : Set ℂ} (hVopen : IsOpen V) (hVne : V.Nonempty)
    (hVreg : V ⊆ gammaGammaRegularSet)
    (hrel : ∀ z ∈ V, MvPolynomial.eval
      (Fin.cons z (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ)
        (fun s => Complex.Gamma (Complex.Gamma s)) z)) P = 0) :
    ∀ z ∈ gammaGammaRegularSet, MvPolynomial.eval
      (Fin.cons z (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ)
        (fun s => Complex.Gamma (Complex.Gamma s)) z)) P = 0 := by
  let E : ℂ → ℂ := fun z => MvPolynomial.eval
    (Fin.cons z (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ)
      (fun s => Complex.Gamma (Complex.Gamma s)) z)) P
  obtain ⟨z₀, hz₀V⟩ := hVne
  have hz₀reg : z₀ ∈ gammaGammaRegularSet := hVreg hz₀V
  have han : AnalyticOnNhd ℂ E gammaGammaRegularSet := by
    intro z hz
    exact analyticAt_gammaGammaDifferentialEval n P hz
  letI : NeBot (𝓝[≠] z₀) := NormedField.nhdsNE_neBot z₀
  have hlocal : ∀ᶠ z in 𝓝 z₀, E z = 0 := by
    filter_upwards [hVopen.mem_nhds hz₀V] with z hz
    exact hrel z hz
  have hfreq : ∃ᶠ z in 𝓝[≠] z₀, E z = 0 :=
    (hlocal.filter_mono nhdsWithin_le_nhds).frequently
  exact han.eqOn_zero_of_preconnected_of_frequently_eq_zero
    gammaGammaRegularSet_isPreconnected hz₀reg hfreq

theorem eventually_factorialBlowUp_input_gammaGammaRegular
    {x : ℂ} (hx : x ∈ gammaFactorialMicroscopeDomain) :
    ∀ᶠ n : ℕ in atTop,
      (-(n : ℂ) + reciprocalGammaFactorialScale n * x) ∈ gammaGammaRegularSet := by
  have hx0 := gammaFactorialMicroscopeDomain_ne_zero hx
  have hGamma :=
    tendsto_Gamma_factorialBlowUp_locallyUniformlyOn_ne_zero.tendsto_at hx0
  have hRe : Tendsto
      (fun n : ℕ => (Complex.Gamma
        (-(n : ℂ) + reciprocalGammaFactorialScale n * x)).re)
      atTop (𝓝 (((-x)⁻¹ : ℂ).re)) :=
    Complex.continuous_re.continuousAt.tendsto.comp hGamma
  have hpos : 0 < (((-x)⁻¹ : ℂ).re) :=
    gammaFactorialMicroscopeDomain_inv_neg_re_pos hx
  filter_upwards [hRe.eventually (Ioi_mem_nhds hpos)] with n hn
  intro m heq
  have hre := congrArg Complex.re heq
  simp only [Complex.neg_re, Complex.natCast_re] at hre
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

theorem no_local_differential_relation_Gamma_comp_Gamma
    {V : Set ℂ} (hVopen : IsOpen V) (hVne : V.Nonempty)
    (hVreg : V ⊆ gammaGammaRegularSet) :
    ¬ DifferentiallyAlgebraicOn (fun z => Complex.Gamma (Complex.Gamma z)) V := by
  rintro ⟨r, P, hP0, hP⟩
  have hPreg := differentialRelation_GammaGamma_propagates
    hVopen hVne hVreg hP
  apply no_eventual_differential_relation_outer_comp_Gamma Complex.Gamma
    analyticAt_Gamma_on_rightHalfPlane locallyPolynomialJetRigidAt_Gamma P hP0
  intro x hx
  filter_upwards [eventually_factorialBlowUp_input_gammaGammaRegular hx] with n hn
  exact hPreg _ hn

end

end GaloisForLFunctions
