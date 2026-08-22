import GaloisForLFunctions.HTGeometry.FiniteAnalyticEscape
import GaloisForLFunctions.HTGeometry.RealFiniteAnalyticEscape
import Mathlib.Data.Fintype.Perm

/-!
# Simultaneous escape from every labeling of a **complex** spectral relation

`AnalyticSpectralRelationEscape` carries this for a balanced *integer* character.  The
real-relation rigidity behind metric recurrence exponents needs it for arbitrary complex (hence
real) coefficients, and nothing in the argument uses integrality: for a fixed coefficient vector
there are only finitely many labelings, so if each labeled relation is somewhere nonzero on one
connected analytic chart, a single point of that chart avoids all of them.

## Main results

* `permutedComplexRelation`, `permutedComplexCoefficient` — one labeling of the relation.
* `permutedComplexCoefficient_not_constant` — a nonzero balanced coefficient vector stays
  nonconstant after every relabeling.
* `exists_all_permutedComplexRelation_ne_zero` — the simultaneous escape.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- One labeling of a complex relation among analytic spectral branches. -/
def permutedComplexRelation {I P : Type*} [Fintype I]
    (c : I → ℂ) (branch : I → P → ℂ) (σ : Equiv.Perm I) (p : P) : ℂ :=
  ∑ i, c i * branch (σ i) p

/-- The coefficient packet on the fixed labeling corresponding to one relabeling. -/
def permutedComplexCoefficient {I : Type*} (c : I → ℂ) (σ : Equiv.Perm I) : I → ℂ :=
  fun j => c (σ.symm j)

theorem sum_permutedComplexCoefficient_eq_relation {I P : Type*} [Fintype I]
    (c : I → ℂ) (branch : I → P → ℂ) (σ : Equiv.Perm I) (p : P) :
    (∑ j, permutedComplexCoefficient c σ j * branch j p)
      = permutedComplexRelation c branch σ p := by
  symm
  apply Fintype.sum_equiv σ
  intro i
  simp [permutedComplexCoefficient]

/-- A nonzero balanced complex coefficient vector stays nonconstant after every relabeling. -/
theorem permutedComplexCoefficient_not_constant {I : Type*} [Fintype I] [Nonempty I]
    {c : I → ℂ} (hbalanced : ∑ i, c i = 0) (hc : c ≠ 0) (σ : Equiv.Perm I) :
    ¬ ∀ x y, permutedComplexCoefficient c σ x = permutedComplexCoefficient c σ y := by
  intro hconstant
  have hcconstant : ∀ i j, c i = c j := by
    intro i j
    have h := hconstant (σ i) (σ j)
    simpa [permutedComplexCoefficient] using h
  let i₀ : I := Classical.choice inferInstance
  have hsum : (∑ i, c i) = (Fintype.card I : ℂ) * c i₀ := by
    calc (∑ i, c i) = ∑ _i, c i₀ := Finset.sum_congr rfl fun i _ => hcconstant i i₀
      _ = (Fintype.card I : ℂ) * c i₀ := by simp
  have hmul : (Fintype.card I : ℂ) * c i₀ = 0 := by rw [← hsum]; exact hbalanced
  have hcard : (Fintype.card I : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card I ≠ 0)
  have hi₀ : c i₀ = 0 := (mul_eq_zero.mp hmul).resolve_left hcard
  exact hc (funext fun i => by rw [hcconstant i i₀, hi₀]; rfl)

theorem permutedComplexRelation_analyticOnNhd {I P : Type*} [Fintype I]
    [NormedAddCommGroup P] [NormedSpace ℂ P]
    (c : I → ℂ) (branch : I → P → ℂ) (U : Set P)
    (hbranch : ∀ i, AnalyticOnNhd ℂ (branch i) U) (σ : Equiv.Perm I) :
    AnalyticOnNhd ℂ (permutedComplexRelation c branch σ) U := by
  intro p hp
  apply Finset.analyticAt_fun_sum
  intro i _
  exact analyticAt_const.mul (hbranch (σ i) p hp)

/-- **Simultaneous escape.**  If every labeling of the relation is somewhere nonzero on one
connected analytic chart, then a single point of that chart escapes all of them. -/
theorem exists_all_permutedComplexRelation_ne_zero {I P : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup P] [NormedSpace ℂ P]
    (c : I → ℂ) (branch : I → P → ℂ) (U : Set P)
    (hUopen : IsOpen U) (hUconnected : IsPreconnected U) (hUnonempty : U.Nonempty)
    (hbranch : ∀ i, AnalyticOnNhd ℂ (branch i) U)
    (hlabel : ∀ σ : Equiv.Perm I, ∃ p ∈ U, permutedComplexRelation c branch σ p ≠ 0) :
    ∃ p ∈ U, ∀ σ : Equiv.Perm I, permutedComplexRelation c branch σ p ≠ 0 :=
  exists_forall_neZero_of_finite_analyticOnNhd_complex_local
    (fun σ => permutedComplexRelation c branch σ) U hUopen hUconnected hUnonempty
    (fun σ => permutedComplexRelation_analyticOnNhd c branch U hbranch σ) hlabel

theorem permutedComplexRelation_analyticOnNhd_real {I P : Type*} [Fintype I]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (c : I → ℂ) (branch : I → P → ℂ) (U : Set P)
    (hbranch : ∀ i, AnalyticOnNhd ℝ (branch i) U) (σ : Equiv.Perm I) :
    AnalyticOnNhd ℝ (permutedComplexRelation c branch σ) U := by
  intro p hp
  apply Finset.analyticAt_fun_sum
  intro i _
  exact analyticAt_const.mul (hbranch (σ i) p hp)

/-- **Simultaneous escape over a real parameter chart.**  This is the form a Hermitian family
supplies: the parameters are real, the branches complex-valued and real-analytic. -/
theorem exists_all_permutedComplexRelation_ne_zero_real {I P : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (c : I → ℂ) (branch : I → P → ℂ) (U : Set P)
    (hUopen : IsOpen U) (hUconnected : IsPreconnected U) (hUnonempty : U.Nonempty)
    (hbranch : ∀ i, AnalyticOnNhd ℝ (branch i) U)
    (hlabel : ∀ σ : Equiv.Perm I, ∃ p ∈ U, permutedComplexRelation c branch σ p ≠ 0) :
    ∃ p ∈ U, ∀ σ : Equiv.Perm I, permutedComplexRelation c branch σ p ≠ 0 :=
  exists_forall_neZero_of_finite_analyticOnNhd_real_local
    (fun σ => permutedComplexRelation c branch σ) U hUopen hUconnected hUnonempty
    (fun σ => permutedComplexRelation_analyticOnNhd_real c branch U hbranch σ) hlabel

end

end GaloisForLFunctions.HTGeometry
