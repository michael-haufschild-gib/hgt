import GaloisForLFunctions.HTGeometry.AnalyticMonicRootGerm
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
# Analytic polynomial division through a collapsing divisor

Ordinary leading-coefficient division becomes singular when a divisor loses
degree. If its constant coefficient remains nonzero, triangular division from
the constant term instead extends every quotient coefficient analytically.
A monic quotient of fixed degree therefore has an exact analytic extension,
without any simplicity assumption on its roots.
-/

open Filter Topology Polynomial

namespace GaloisForLFunctions.HTGeometry
noncomputable section

theorem analyticAt_polynomial_mul_coeff {p q : ℝ → ℂ[X]} {a : ℝ}
    (hp : ∀ i, AnalyticAt ℝ (fun t => (p t).coeff i) a)
    (hq : ∀ i, AnalyticAt ℝ (fun t => (q t).coeff i) a) (i : ℕ) :
    AnalyticAt ℝ (fun t => (p t * q t).coeff i) a := by
  simp only [coeff_mul]
  exact Finset.analyticAt_fun_sum _ (fun j _ => (hp j.1).mul (hq j.2))

theorem analyticAt_polynomial_prod_coeff {ι : Type*} (s : Finset ι)
    {p : ι → ℝ → ℂ[X]} {a : ℝ}
    (hp : ∀ j ∈ s, ∀ i, AnalyticAt ℝ (fun t => (p j t).coeff i) a) (i : ℕ) :
    AnalyticAt ℝ (fun t => (∏ j ∈ s, p j t).coeff i) a := by
  classical
  induction s using Finset.induction_on generalizing i with
  | empty => simpa using (analyticAt_const : AnalyticAt ℝ (fun _ : ℝ => (1 : ℂ[X]).coeff i) a)
  | @insert j s hjs ih =>
    simp only [Finset.prod_insert hjs]
    exact analyticAt_polynomial_mul_coeff
      (hp j (Finset.mem_insert_self _ _))
      (fun l => ih (fun v hv => hp v (Finset.mem_insert_of_mem hv)) l) i

private theorem coeff_mul_head (p q : ℂ[X]) (i : ℕ) :
    (p * q).coeff i = p.coeff 0 * q.coeff i +
      ∑ j : Fin i, p.coeff (j.val + 1) * q.coeff (i - (j.val + 1)) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [Finset.sum_range_succ']
  simp only [Nat.sub_zero]
  rw [Fin.sum_univ_eq_sum_range (fun j => p.coeff (j + 1) * q.coeff (i - (j + 1))) i]
  exact add_comm _ _

/-- Coefficients of a punctured quotient extend by triangular division at zero. -/
theorem analytic_quotient_coeff_germ {S E D : ℝ → ℂ[X]} {a : ℝ}
    (hS : ∀ i, AnalyticAt ℝ (fun t => (S t).coeff i) a)
    (hE : ∀ i, AnalyticAt ℝ (fun t => (E t).coeff i) a)
    (hE0 : (E a).coeff 0 ≠ 0)
    (hfact : ∀ᶠ t in 𝓝[≠] a, S t = E t * D t) (i : ℕ) :
    ∃ u : ℝ → ℂ, AnalyticAt ℝ u a ∧ (fun t => (D t).coeff i) =ᶠ[𝓝[≠] a] u := by
  classical
  induction i using Nat.strong_induction_on with
  | h i ih =>
    have hex (j : Fin i) := ih (i - (j.val + 1)) (by omega)
    choose u hu he using hex
    let v : ℝ → ℂ := fun t =>
      ((S t).coeff i - ∑ j : Fin i, (E t).coeff (j.val + 1) * u j t) / (E t).coeff 0
    refine ⟨v, ((hS i).sub (Finset.analyticAt_fun_sum _
      (fun j _ => (hE (j.val + 1)).mul (hu j)))).div (hE 0) hE0, ?_⟩
    filter_upwards [hfact, Filter.eventually_all.mpr he,
      ((hE 0).continuousAt.eventually_ne hE0).filter_mono nhdsWithin_le_nhds]
      with t ht heq hne
    dsimp [v]
    apply (eq_div_iff hne).mpr
    rw [ht, coeff_mul_head]
    have hsum : (∑ j : Fin i, (E t).coeff (j.val + 1) * (D t).coeff (i - (j.val + 1))) =
        ∑ j : Fin i, (E t).coeff (j.val + 1) * u j t := by
      exact Finset.sum_congr rfl (fun j _ => congrArg ((E t).coeff (j.val + 1) * ·) (heq j))
    rw [hsum]
    ring

/-- Fixed-degree monic quotients extend analytically even when the divisor
loses degree. The factorization survives at the contact itself. -/
theorem analytic_monic_factor_extension {S E D : ℝ → ℂ[X]} {a : ℝ} {n : ℕ}
    (hS : ∀ i, AnalyticAt ℝ (fun t => (S t).coeff i) a)
    (hE : ∀ i, AnalyticAt ℝ (fun t => (E t).coeff i) a)
    (hE0 : (E a).coeff 0 ≠ 0)
    (hfact : ∀ᶠ t in 𝓝[≠] a, S t = E t * D t)
    (hD : ∀ᶠ t in 𝓝[≠] a, (D t).Monic ∧ (D t).natDegree = n) :
    ∃ F : ℝ → ℂ[X], (∀ t, (F t).Monic ∧ (F t).natDegree = n) ∧
      (∀ i, AnalyticAt ℝ (fun t => (F t).coeff i) a) ∧
      F =ᶠ[𝓝[≠] a] D ∧ S a = E a * F a := by
  classical
  choose u hu he using fun i : Fin n => analytic_quotient_coeff_germ hS hE hE0 hfact i
  let F : ℝ → ℂ[X] := fun t => monicCoeffPolynomial n (fun i => u i t)
  have hF (t : ℝ) : (F t).Monic ∧ (F t).natDegree = n :=
    ⟨monic_monicCoeffPolynomial _ _, natDegree_monicCoeffPolynomial _ _⟩
  have hFa (i : ℕ) : AnalyticAt ℝ (fun t => (F t).coeff i) a := by
    simp only [F, monicCoeffPolynomial, coeff_add, finsetSum_coeff, coeff_C_mul]
    exact analyticAt_const.add (Finset.analyticAt_fun_sum _
      (fun j _ => (hu j).mul analyticAt_const))
  have hFD : F =ᶠ[𝓝[≠] a] D := by
    filter_upwards [Filter.eventually_all.mpr he, hD] with t ht hDt
    have hn := hDt.2
    have hrecon := monicCoeffPolynomial_coeff_of_monic (D t) hDt.1
    have hc : (fun i : Fin n => u i t) = fun i : Fin n => (D t).coeff i :=
      funext fun i => (ht i).symm
    dsimp [F]
    rw [hc]
    subst n
    exact hrecon
  refine ⟨F, hF, hFa, hFD, ?_⟩
  ext i
  have heq : (fun t => (S t).coeff i) =ᶠ[𝓝[≠] a] fun t => (E t * F t).coeff i := by
    filter_upwards [hfact, hFD] with t ht hFt
    rw [hFt, ht]
  exact tendsto_nhds_unique (hS i).continuousAt.continuousWithinAt.tendsto
    ((analyticAt_polynomial_mul_coeff hE hFa i).continuousAt.continuousWithinAt.tendsto.congr'
      heq.symm)

end
end GaloisForLFunctions.HTGeometry
