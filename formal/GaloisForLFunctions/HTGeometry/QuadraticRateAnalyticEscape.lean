import GaloisForLFunctions.HTGeometry.QuadraticRateMatrixObstruction

/-!
# Escaping a quadratic-rate relation on one analytic chart

The labeling-orbit obstruction of a quadratic-rate relation is a finite product over the
labelings.  On a connected open chart carrying analytic eigenvalue branches every factor is
analytic, so if no single labeling holds identically on the chart the product is somewhere
nonzero there.  Feeding that chart point into the characteristic-coefficient pullback produces
the one complex witness the parameter-space argument needs.
-/

open Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The `σ`-relabeled quadratic-rate relation of an analytic branch family. -/
def permutedAnalyticQuadraticRate {I E : Type*} [Fintype I] (c : I → ℂ) (κ : ℂ)
    (branch : I → E → ℂ) (σ : Equiv.Perm I) (p : E) : ℂ :=
  (∑ i, c i * branch (σ i) p) ^ 2 - κ * ∑ i, branch i p ^ 2

theorem fieldQuadraticRateOrbitValue_branch {I E : Type*} [Fintype I] [DecidableEq I]
    (c : I → ℂ) (κ : ℂ)
    (branch : I → E → ℂ) (p : E) :
    fieldQuadraticRateOrbitValue c κ (fun x => branch x p)
      = ∏ σ : Equiv.Perm I, permutedAnalyticQuadraticRate c κ branch σ p := by
  classical
  rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem analyticOnNhd_permutedAnalyticQuadraticRate {I : Type*} [Fintype I]
    (c : I → ℂ) (κ : ℂ) {branch : I → E → ℂ} {U : Set E}
    (hbranch : ∀ x, AnalyticOnNhd ℂ (branch x) U) (σ : Equiv.Perm I) :
    AnalyticOnNhd ℂ (permutedAnalyticQuadraticRate c κ branch σ) U := by
  have h1 : AnalyticOnNhd ℂ (fun p => ∑ i, c i * branch (σ i) p) U :=
    Finset.analyticOnNhd_fun_sum _ fun i _ =>
      (analyticOnNhd_const (v := c i) (s := U)).mul (hbranch (σ i))
  have h2 : AnalyticOnNhd ℂ (fun p => ∑ i, branch i p ^ 2) U :=
    Finset.analyticOnNhd_fun_sum _ fun i _ => (hbranch i).pow 2
  exact (h1.pow 2).sub ((analyticOnNhd_const (v := κ) (s := U)).mul h2)

/-- **Chart escape.**  If no labeling of a quadratic-rate relation holds identically on a
connected chart of analytic branches, the labeling-orbit obstruction is somewhere nonzero on the
chart. -/
theorem exists_fieldQuadraticRateOrbitValue_ne_zero_of_analytic {I : Type*} [Fintype I]
    [DecidableEq I] (c : I → ℂ) (κ : ℂ) {branch : I → E → ℂ} {U : Set E}
    (hUopen : IsOpen U) (hUconnected : IsPreconnected U) (hUnonempty : U.Nonempty)
    (hbranch : ∀ x, AnalyticOnNhd ℂ (branch x) U)
    (hlabel : ∀ σ : Equiv.Perm I, ∃ p ∈ U, permutedAnalyticQuadraticRate c κ branch σ p ≠ 0) :
    ∃ p ∈ U, fieldQuadraticRateOrbitValue c κ (fun x => branch x p) ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  have hprod : Set.EqOn
      (fun p => ∏ σ : Equiv.Perm I, permutedAnalyticQuadraticRate c κ branch σ p) 0 U := by
    intro p hp
    show (∏ σ : Equiv.Perm I, permutedAnalyticQuadraticRate c κ branch σ p) = 0
    rw [← fieldQuadraticRateOrbitValue_branch]
    exact hcon p hp
  obtain ⟨σ, -, hσ⟩ := exists_eqOn_zero_of_finsetProd_eqOn_zero
    (f := fun σ : Equiv.Perm I => permutedAnalyticQuadraticRate c κ branch σ)
    Finset.univ (fun σ _ => analyticOnNhd_permutedAnalyticQuadraticRate c κ hbranch σ)
    hUconnected hUopen hUnonempty hprod
  obtain ⟨p, hp, hpne⟩ := hlabel σ
  exact hpne (hσ hp)

/-- **The complex witness.**  A chart escape of every labeling produces one complex parameter at
which the characteristic-coefficient pullback of the quadratic-rate obstruction is nonzero. -/
theorem exists_eval_quadraticRateObstructionPullback_ne_zero_of_analyticBranchEscape
    {m : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I (MvPolynomial (Fin m) ℂ)) (c : I → ℂ) (κ : ℂ)
    {U : Set (Fin m → ℂ)} (hUopen : IsOpen U) (hUconnected : IsPreconnected U)
    (hUnonempty : U.Nonempty)
    (branch : I → (Fin m → ℂ) → ℂ)
    (hbranchA : ∀ x, AnalyticOnNhd ℂ (branch x) U)
    (hbranchInj : ∀ p ∈ U, Function.Injective fun x => branch x p)
    (hbranchRoot : ∀ x, ∀ p ∈ U,
      matrixCharpolyRelation
        (M.map (MvPolynomial.eval₂Hom (RingHom.id ℂ) p), branch x p) = 0)
    (hlabel : ∀ σ : Equiv.Perm I, ∃ p ∈ U, permutedAnalyticQuadraticRate c κ branch σ p ≠ 0) :
    ∃ z : Fin m → ℂ,
      MvPolynomial.eval₂ (RingHom.id ℂ) z (quadraticRateObstructionPullback M c κ) ≠ 0 := by
  obtain ⟨p, hp, hpne⟩ := exists_fieldQuadraticRateOrbitValue_ne_zero_of_analytic c κ
    hUopen hUconnected hUnonempty hbranchA hlabel
  refine ⟨p, ?_⟩
  rw [eval_quadraticRateObstructionPullback M c κ p (fun x => branch x p) (hbranchInj p hp)
    (fun x => hbranchRoot x p hp)]
  exact hpne

/-- **Nowhere flatness.**  A chart escape of every labeling forces the quadratic-rate obstruction
to be nonzero somewhere inside every nonempty open set of real parameters. -/
theorem exists_mem_eval_quadraticRateObstructionPullback_ne_zero_of_analyticBranchEscape
    {m : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I (MvPolynomial (Fin m) ℂ)) (c : I → ℂ) (κ : ℂ)
    {U : Set (Fin m → ℂ)} (hUopen : IsOpen U) (hUconnected : IsPreconnected U)
    (hUnonempty : U.Nonempty)
    (branch : I → (Fin m → ℂ) → ℂ)
    (hbranchA : ∀ x, AnalyticOnNhd ℂ (branch x) U)
    (hbranchInj : ∀ p ∈ U, Function.Injective fun x => branch x p)
    (hbranchRoot : ∀ x, ∀ p ∈ U,
      matrixCharpolyRelation
        (M.map (MvPolynomial.eval₂Hom (RingHom.id ℂ) p), branch x p) = 0)
    (hlabel : ∀ σ : Equiv.Perm I, ∃ p ∈ U, permutedAnalyticQuadraticRate c κ branch σ p ≠ 0)
    {V : Set (Fin m → ℝ)} (hVopen : IsOpen V) (hVne : V.Nonempty) :
    ∃ p ∈ V, MvPolynomial.eval₂ (RingHom.id ℂ) (fun t => (p t : ℂ))
      (quadraticRateObstructionPullback M c κ) ≠ 0 :=
  exists_mem_eval_quadraticRateObstructionPullback_ne_zero M c κ
    (exists_eval_quadraticRateObstructionPullback_ne_zero_of_analyticBranchEscape M c κ
      hUopen hUconnected hUnonempty branch hbranchA hbranchInj hbranchRoot hlabel)
    hVopen hVne

end GaloisForLFunctions.HTGeometry
