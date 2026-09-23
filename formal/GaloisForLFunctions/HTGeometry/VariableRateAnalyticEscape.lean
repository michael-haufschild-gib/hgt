/-
# Escaping a moving-rate quadratic relation on one analytic chart

The chart-escape argument does not care that the quadratic rate is constant: what it uses is that
every factor of the labeling-orbit product is analytic on the chart.  A rate given by a polynomial
in the parameters is analytic, so the same identity-theorem argument applies verbatim, and the
chart point it produces is the one complex witness the parameter-space argument needs -- now for
the rate `κ Q(H)` that moves with the Hamiltonian.

Main results:
* `analyticOnNhd_evalMvPolynomial` — polynomial evaluation is analytic in the parameters.
* `exists_fieldQuadraticRateOrbitValue_ne_zero_of_analyticVariableRate` — the chart escape.
* `exists_mem_eval_variableRateObstructionPullback_ne_zero_of_analyticBranchEscape` — nowhere
  flatness at a moving rate.
-/
import GaloisForLFunctions.HTGeometry.QuadraticRateAnalyticEscape
import GaloisForLFunctions.HTGeometry.VariableRateMatrixObstruction

open Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The `σ`-relabeled quadratic-rate relation of an analytic branch family at a moving rate. -/
def permutedAnalyticVariableRate {I E : Type*} [Fintype I] (c : I → ℂ) (rate : E → ℂ)
    (branch : I → E → ℂ) (σ : Equiv.Perm I) (p : E) : ℂ :=
  (∑ i, c i * branch (σ i) p) ^ (2 : ℕ) - rate p * ∑ i, branch i p ^ (2 : ℕ)

theorem fieldQuadraticRateOrbitValue_variableRate {I E : Type*} [Fintype I] [DecidableEq I]
    (c : I → ℂ) (rate : E → ℂ) (branch : I → E → ℂ) (p : E) :
    fieldQuadraticRateOrbitValue c (rate p) (fun x => branch x p)
      = ∏ σ : Equiv.Perm I, permutedAnalyticVariableRate c rate branch σ p := by
  classical
  rfl

section Analytic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem analyticOnNhd_permutedAnalyticVariableRate {I : Type*} [Fintype I]
    (c : I → ℂ) {rate : E → ℂ} {branch : I → E → ℂ} {U : Set E}
    (hrate : AnalyticOnNhd ℂ rate U) (hbranch : ∀ x, AnalyticOnNhd ℂ (branch x) U)
    (σ : Equiv.Perm I) :
    AnalyticOnNhd ℂ (permutedAnalyticVariableRate c rate branch σ) U := by
  have h1 : AnalyticOnNhd ℂ (fun p => ∑ i, c i * branch (σ i) p) U :=
    Finset.analyticOnNhd_fun_sum _ fun i _ =>
      (analyticOnNhd_const (v := c i) (s := U)).mul (hbranch (σ i))
  have h2 : AnalyticOnNhd ℂ (fun p => ∑ i, branch i p ^ (2 : ℕ)) U :=
    Finset.analyticOnNhd_fun_sum _ fun i _ => (hbranch i).pow 2
  exact (h1.pow 2).sub (hrate.mul h2)

/-- **Chart escape at a moving rate.**  If no labeling of the quadratic-rate relation holds
identically on a connected chart of analytic branches, the labeling-orbit obstruction is somewhere
nonzero on the chart. -/
theorem exists_fieldQuadraticRateOrbitValue_ne_zero_of_analyticVariableRate {I : Type*}
    [Fintype I] [DecidableEq I] (c : I → ℂ) {rate : E → ℂ} {branch : I → E → ℂ} {U : Set E}
    (hUopen : IsOpen U) (hUconnected : IsPreconnected U) (hUnonempty : U.Nonempty)
    (hrate : AnalyticOnNhd ℂ rate U) (hbranch : ∀ x, AnalyticOnNhd ℂ (branch x) U)
    (hlabel : ∀ σ : Equiv.Perm I, ∃ p ∈ U, permutedAnalyticVariableRate c rate branch σ p ≠ 0) :
    ∃ p ∈ U, fieldQuadraticRateOrbitValue c (rate p) (fun x => branch x p) ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  have hprod : Set.EqOn
      (fun p => ∏ σ : Equiv.Perm I, permutedAnalyticVariableRate c rate branch σ p) 0 U := by
    intro p hp
    show (∏ σ : Equiv.Perm I, permutedAnalyticVariableRate c rate branch σ p) = 0
    rw [← fieldQuadraticRateOrbitValue_variableRate]
    exact hcon p hp
  obtain ⟨σ, -, hσ⟩ := exists_eqOn_zero_of_finsetProd_eqOn_zero
    (f := fun σ : Equiv.Perm I => permutedAnalyticVariableRate c rate branch σ)
    Finset.univ (fun σ _ => analyticOnNhd_permutedAnalyticVariableRate c hrate hbranch σ)
    hUconnected hUopen hUnonempty hprod
  obtain ⟨p, hp, hpne⟩ := hlabel σ
  exact hpne (hσ hp)

end Analytic

/-- Evaluation of a multivariate polynomial is analytic in its parameters. -/
theorem analyticOnNhd_evalMvPolynomial {m : ℕ} {U : Set (Fin m → ℂ)}
    (P : MvPolynomial (Fin m) ℂ) :
    AnalyticOnNhd ℂ (fun p : Fin m → ℂ => MvPolynomial.eval₂ (RingHom.id ℂ) p P) U := by
  induction P using MvPolynomial.induction_on with
  | C a =>
      have hfun : (fun p : Fin m → ℂ =>
          MvPolynomial.eval₂ (RingHom.id ℂ) p (MvPolynomial.C a)) = fun _ => a := by
        funext p
        simp
      rw [hfun]
      exact analyticOnNhd_const
  | add p q hp hq =>
      have hfun : (fun z : Fin m → ℂ => MvPolynomial.eval₂ (RingHom.id ℂ) z (p + q))
          = fun z : Fin m → ℂ => MvPolynomial.eval₂ (RingHom.id ℂ) z p
            + MvPolynomial.eval₂ (RingHom.id ℂ) z q := by
        funext z
        rw [MvPolynomial.eval₂_add]
      rw [hfun]
      exact hp.add hq
  | mul_X p a hp =>
      have hfun : (fun z : Fin m → ℂ =>
          MvPolynomial.eval₂ (RingHom.id ℂ) z (p * MvPolynomial.X a))
          = fun z : Fin m → ℂ => MvPolynomial.eval₂ (RingHom.id ℂ) z p * z a := by
        funext z
        rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
      rw [hfun]
      refine hp.mul fun x _ => ?_
      exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin m => ℂ) a).analyticAt x

/-- **The complex witness at a moving rate.**  A chart escape of every labeling produces one
complex parameter at which the variable-rate pullback is nonzero. -/
theorem exists_eval_variableRateObstructionPullback_ne_zero_of_analyticBranchEscape
    {m : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I (MvPolynomial (Fin m) ℂ)) (c : I → ℂ) (κ : MvPolynomial (Fin m) ℂ)
    {U : Set (Fin m → ℂ)} (hUopen : IsOpen U) (hUconnected : IsPreconnected U)
    (hUnonempty : U.Nonempty)
    (branch : I → (Fin m → ℂ) → ℂ)
    (hbranchA : ∀ x, AnalyticOnNhd ℂ (branch x) U)
    (hbranchInj : ∀ p ∈ U, Function.Injective fun x => branch x p)
    (hbranchRoot : ∀ x, ∀ p ∈ U,
      matrixCharpolyRelation
        (M.map (MvPolynomial.eval₂Hom (RingHom.id ℂ) p), branch x p) = 0)
    (hlabel : ∀ σ : Equiv.Perm I, ∃ p ∈ U,
      permutedAnalyticVariableRate c
        (fun q : Fin m → ℂ => MvPolynomial.eval₂ (RingHom.id ℂ) q κ) branch σ p ≠ 0) :
    ∃ z : Fin m → ℂ,
      MvPolynomial.eval₂ (RingHom.id ℂ) z (variableRateObstructionPullback M c κ) ≠ 0 := by
  obtain ⟨p, hp, hpne⟩ := exists_fieldQuadraticRateOrbitValue_ne_zero_of_analyticVariableRate c
    hUopen hUconnected hUnonempty (analyticOnNhd_evalMvPolynomial κ) hbranchA hlabel
  refine ⟨p, ?_⟩
  rw [eval_variableRateObstructionPullback M c κ p (fun x => branch x p) (hbranchInj p hp)
    (fun x => hbranchRoot x p hp)]
  exact hpne

/-- **Nowhere flatness at a moving rate.**  A chart escape of every labeling forces the
variable-rate obstruction to be nonzero somewhere inside every nonempty open set of real
parameters. -/
theorem exists_mem_eval_variableRateObstructionPullback_ne_zero_of_analyticBranchEscape
    {m : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I (MvPolynomial (Fin m) ℂ)) (c : I → ℂ) (κ : MvPolynomial (Fin m) ℂ)
    {U : Set (Fin m → ℂ)} (hUopen : IsOpen U) (hUconnected : IsPreconnected U)
    (hUnonempty : U.Nonempty)
    (branch : I → (Fin m → ℂ) → ℂ)
    (hbranchA : ∀ x, AnalyticOnNhd ℂ (branch x) U)
    (hbranchInj : ∀ p ∈ U, Function.Injective fun x => branch x p)
    (hbranchRoot : ∀ x, ∀ p ∈ U,
      matrixCharpolyRelation
        (M.map (MvPolynomial.eval₂Hom (RingHom.id ℂ) p), branch x p) = 0)
    (hlabel : ∀ σ : Equiv.Perm I, ∃ p ∈ U,
      permutedAnalyticVariableRate c
        (fun q : Fin m → ℂ => MvPolynomial.eval₂ (RingHom.id ℂ) q κ) branch σ p ≠ 0)
    {V : Set (Fin m → ℝ)} (hVopen : IsOpen V) (hVne : V.Nonempty) :
    ∃ p ∈ V, MvPolynomial.eval₂ (RingHom.id ℂ) (fun t => (p t : ℂ))
      (variableRateObstructionPullback M c κ) ≠ 0 :=
  exists_mem_eval_variableRateObstructionPullback_ne_zero M c κ
    (exists_eval_variableRateObstructionPullback_ne_zero_of_analyticBranchEscape M c κ
      hUopen hUconnected hUnonempty branch hbranchA hbranchInj hbranchRoot hlabel)
    hVopen hVne

end GaloisForLFunctions.HTGeometry
