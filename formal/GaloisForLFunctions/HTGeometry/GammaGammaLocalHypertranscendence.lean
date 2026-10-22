import GaloisForLFunctions.HTGeometry.GammaGammaFactorialBlowUp
import GaloisForLFunctions.HTGeometry.GammaFactorialCompositionLocal

/-!
# Local hypertranscendence of `Γ ∘ Γ`

This module proves that `z ↦ Γ(Γ(z))` satisfies no algebraic differential equation
`P(z, f, f', …, f^(n)) = 0` on any nonempty open subset of its regular set, the set of `z` with
`Γ(z)` not a nonpositive integer. A relation on such an open set extends, by the identity theorem
on the connected regular set, to the whole regular set. The factorial blow-up points
`-n + ε_n x` (with `Re x < 0`, `ε_n = (-1)^(n+1) / n!`) eventually lie in the regular set, so the
relation holds eventually along them, which the local jet rigidity of `Γ` at `1` rules out.

## Main results

- `differentialRelation_GammaGamma_propagates`: a differential relation for `Γ ∘ Γ` on a nonempty
  open subset of the regular set holds on the whole regular set.
- `eventually_factorialBlowUp_input_gammaGammaRegular`: for `Re x < 0`, the points
  `-n + ε_n x` lie in the regular set for all large `n`.
- `no_local_differential_relation_Gamma_comp_Gamma`: `Γ ∘ Γ` is not differentially algebraic on
  any nonempty open subset of the regular set.

## Hypotheses

Unconditional. The open set must be nonempty and contained in the regular set of `Γ ∘ Γ`.
-/

namespace GaloisForLFunctions

open Complex Filter Topology

noncomputable section

/-- The regular set of `Γ ∘ Γ`: points `z` where `Γ(z)` is not a nonpositive integer. -/
def gammaGammaRegularSet : Set ℂ := digammaGammaRegularSet

theorem gammaGammaRegularSet_input_offPoles {z : ℂ}
    (hz : z ∈ gammaGammaRegularSet) : ∀ n : ℕ, z ≠ -(n : ℂ) := by
  exact digammaGammaRegularSet_input_offPoles hz

/-- `Γ ∘ Γ` is analytic at every point of its regular set. -/
theorem analyticAt_Gamma_comp_Gamma {z : ℂ}
    (hz : z ∈ gammaGammaRegularSet) :
    AnalyticAt ℂ (fun w => Complex.Gamma (Complex.Gamma w)) z := by
  have hin := gammaGammaRegularSet_input_offPoles hz
  have hout : ∀ m : ℕ, Complex.Gamma z ≠ -(m : ℂ) := hz
  exact AnalyticAt.comp (f := Complex.Gamma) (x := z)
    (analyticAt_Gamma _ hout) (analyticAt_Gamma z hin)

theorem isOpen_gammaGammaRegularSet : IsOpen gammaGammaRegularSet := by
  exact isOpen_digammaGammaRegularSet

/-- The complement of the regular set of `Γ ∘ Γ` is countable. -/
theorem gammaGammaRegularSet_compl_countable : gammaGammaRegularSetᶜ.Countable := by
  exact digammaGammaRegularSet_compl_countable

/-- The regular set of `Γ ∘ Γ` is preconnected, so the identity theorem applies on it. -/
theorem gammaGammaRegularSet_isPreconnected : IsPreconnected gammaGammaRegularSet := by
  exact digammaGammaRegularSet_isPreconnected

/-- For a polynomial `P`, the function `w ↦ P(w, f(w), …, f^(n)(w))` with `f = Γ ∘ Γ` is analytic
at every point of the regular set. -/
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

/-- Identity-theorem propagation: if `P(z, f, …, f^(n)) = 0` for `f = Γ ∘ Γ` on a nonempty open set
`V` inside the regular set, the relation holds on the entire regular set. -/
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

/-- For `Re x < 0`, the factorial blow-up point `-n + ε_n x` lies in the regular set of `Γ ∘ Γ`
for all large `n`, because `Γ` at these points tends to `1 / (-x)`, which has positive real part. -/
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

/-- Local hypertranscendence of `Γ ∘ Γ`: on no nonempty open set `V` contained in the regular set
does `Γ ∘ Γ` satisfy a nonzero polynomial differential equation `P(z, f, …, f^(n)) = 0`. -/
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
