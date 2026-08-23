import GaloisForLFunctions.RHTower.PrimeIsingArbitraryGraphGKSNoGo
import GaloisForLFunctions.HTGeometry.CoefficientJetRelation

/-!
# Bounded differential-complexity escape for completed Xi

Compact-open convergence of entire functions returns every finite holomorphic jet.  Combine this
with compactness of a normalized finite-dimensional coefficient sphere: a sequence of algebraic
differential relations whose monomial window is fixed has a nonzero limiting relation.  Therefore
its compact-open limit remains differentially algebraic.

Applied to the hypertranscendental completed Xi function, this gives a complexity escape law:
any convergent family of entire models must leave every fixed finite differential-monomial window.
Equivalently, after encoding every monomial of bounded derivative order and polynomial degree in
one such window, derivative order or nonlinear degree must become unbounded.

The coefficient vectors may vary arbitrarily with the model index.  Their `ℓ¹` normalization loses
no nonzero homogeneous relation, and prevents the compactness limit from degenerating to zero.
-/

open Filter Topology Set Metric
open scoped BigOperators

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

variable {N n : ℕ}

/-- Joint continuity when both coefficients and jet coordinates vary. -/
private theorem continuous_jointFrozenRelation
    (e : Fin N → (Fin (n + 2) →₀ ℕ)) :
    Continuous (fun p : (Fin N → ℂ) × (Fin (n + 2) → ℂ) =>
      frozenRelation (fun i j => e i j) p.1 p.2) := by
  refine continuous_finsetSum _ fun i _ => ?_
  refine ((continuous_apply i).comp continuous_fst).mul ?_
  refine continuous_finsetProd _ fun j _ => ?_
  exact ((continuous_apply j).comp continuous_snd).pow _

/-- The finite monomial sum used in the compactness argument evaluates to `frozenRelation`. -/
private theorem eval_sum_monomial_eq_frozenRelation
    (e : Fin N → (Fin (n + 2) →₀ ℕ)) (c : Fin N → ℂ)
    (y : Fin (n + 2) → ℂ) :
    MvPolynomial.eval y (∑ i : Fin N, MvPolynomial.monomial (e i) (c i)) =
      frozenRelation (fun i j => e i j) c y := by
  simp only [MvPolynomial.eval_sum, MvPolynomial.eval_monomial, frozenRelation]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  exact (e i).prod_fintype (fun j m => y j ^ m) (fun _ => pow_zero _)

/-- **Finite differential-law windows are compact-open closed.**

Let the entire functions `F k` converge compact-open to `f`.  Suppose every `F k` satisfies a
polynomial differential relation using the same injectively enumerated finite monomial window `e`,
while its coefficient vector `c k` may vary and is normalized in `ℓ¹`.  Then `f` satisfies a
nonzero limiting polynomial differential relation and is differentially algebraic.

Injectivity of `e` excludes cancellation between duplicate monomials.  The normalization supplies
the positive survivor of the compactness argument: the limiting polynomial cannot be zero. -/
theorem differentiallyAlgebraic_of_tendstoLocallyUniformly_of_uniformFiniteMonomialRelation
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (e : Fin N → (Fin (n + 2) →₀ ℕ)) (he : Function.Injective e)
    (c : ℕ → Fin N → ℂ)
    (hc : ∀ k, ∑ i : Fin N, ‖c k i‖ = 1)
    (hF : ∀ k, Differentiable ℂ (F k))
    (hrel : ∀ k z, frozenRelation (fun i j => e i j) (c k)
      (Fin.cons z (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) (F k) z)) = 0)
    (hconv : TendstoLocallyUniformly F f atTop) :
    GaloisForLFunctions.DifferentiallyAlgebraic f := by
  classical
  letI : ProperSpace (Fin N → ℂ) := FiniteDimensional.proper ℂ (Fin N → ℂ)
  have hmem : ∀ k, c k ∈ closedBall (0 : Fin N → ℂ) 1 := by
    intro k
    rw [mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by norm_num)]
    intro i
    calc
      ‖c k i‖ ≤ ∑ j : Fin N, ‖c k j‖ :=
        Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
      _ = 1 := hc k
  obtain ⟨cLimit, hcLimitBall, φ, hφ, hcLimit⟩ :=
    (isCompact_closedBall (0 : Fin N → ℂ) 1).tendsto_subseq hmem
  have hcPoint : ∀ i, Tendsto (fun k => c (φ k) i) atTop (nhds (cLimit i)) := by
    exact tendsto_pi_nhds.mp hcLimit
  have hnormLimit : Tendsto (fun k => ∑ i : Fin N, ‖c (φ k) i‖) atTop
      (nhds (∑ i : Fin N, ‖cLimit i‖)) := by
    apply tendsto_finsetSum
    intro i hi
    exact (hcPoint i).norm
  have hsumLimit : ∑ i : Fin N, ‖cLimit i‖ = 1 := by
    apply tendsto_nhds_unique hnormLimit
    simpa only [hc] using tendsto_const_nhds (x := (1 : ℝ))
  obtain ⟨i0, hi0⟩ : ∃ i, cLimit i ≠ 0 := by
    by_contra h
    push Not at h
    have hzero : ∑ i : Fin N, ‖cLimit i‖ = 0 := by simp [h]
    have : (0 : ℝ) = 1 := hzero.symm.trans hsumLimit
    exact zero_ne_one this
  let P : MvPolynomial (Fin (n + 2)) ℂ :=
    ∑ i : Fin N, MvPolynomial.monomial (e i) (cLimit i)
  have hP : P ≠ 0 := by
    intro hzero
    have hcoeff := congrArg (MvPolynomial.coeff (e i0)) hzero
    simp only [P, MvPolynomial.coeff_sum] at hcoeff
    simp only [MvPolynomial.coeff_monomial] at hcoeff
    rw [Finset.sum_eq_single i0] at hcoeff
    · apply hi0
      simpa using hcoeff
    · intro j hj hji
      rw [if_neg]
      exact fun hej => hji (he hej)
    · simp
  refine ⟨n, P, hP, ?_⟩
  intro z
  have hjet : Tendsto
      (fun k => Fin.cons z
        (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) (F (φ k)) z))
      atTop
      (nhds ((Fin.cons z
        (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z)) : Fin (n + 2) → ℂ)) := by
    rw [tendsto_pi_nhds]
    intro j
    refine Fin.cases ?_ (fun q => ?_) j
    · exact tendsto_const_nhds
    · rw [Fin.cons_succ]
      have hderiv := GaloisForLFunctions.iteratedDeriv_tendsto_of_locallyUniform
        isOpen_univ (tendstoLocallyUniformlyOn_univ.mpr hconv)
        (Filter.Eventually.of_forall fun k => (hF k).differentiableOn)
        (q : ℕ) (Set.mem_univ z)
      exact hderiv.comp hφ.tendsto_atTop
  have hjoint := hcLimit.prodMk_nhds hjet
  have hrelationLimit : Tendsto
      (fun k => frozenRelation (fun i j => e i j) (c (φ k))
        (Fin.cons z
          (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) (F (φ k)) z)))
      atTop
      (nhds (frozenRelation (fun i j => e i j) cLimit
        (Fin.cons z
          (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z)))) :=
    ((continuous_jointFrozenRelation e).tendsto _).comp hjoint
  have hzeroLimit : Tendsto
      (fun k => frozenRelation (fun i j => e i j) (c (φ k))
        (Fin.cons z
          (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) (F (φ k)) z)))
      atTop (nhds 0) := by
    simpa only [hrel] using tendsto_const_nhds (x := (0 : ℂ))
  have hlimitRoot : frozenRelation (fun i j => e i j) cLimit
      (Fin.cons z (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z)) = 0 :=
    tendsto_nhds_unique hrelationLimit hzeroLimit
  rw [eval_sum_monomial_eq_frozenRelation]
  exact hlimitRoot

/-- **Completed-Xi bounded-complexity escape.**  A sequence of entire models obeying relations in
one fixed finite differential-monomial window, with nonzero coefficient vectors normalized in
`ℓ¹`, cannot converge compact-open to completed Xi.  Thus a successful convergent theory must send
derivative order, polynomial degree, or both to infinity. -/
theorem not_tendstoLocallyUniformly_unitCentralXiC_of_uniformFiniteMonomialRelation
    (F : ℕ → ℂ → ℂ)
    (e : Fin N → (Fin (n + 2) →₀ ℕ)) (he : Function.Injective e)
    (c : ℕ → Fin N → ℂ)
    (hc : ∀ k, ∑ i : Fin N, ‖c k i‖ = 1)
    (hF : ∀ k, Differentiable ℂ (F k))
    (hrel : ∀ k z, frozenRelation (fun i j => e i j) (c k)
      (Fin.cons z (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) (F k) z)) = 0) :
    ¬ TendstoLocallyUniformly F unitCentralXiC atTop := by
  intro hconv
  exact unitCentralXiC_hypertranscendental
    (differentiallyAlgebraic_of_tendstoLocallyUniformly_of_uniformFiniteMonomialRelation
      e he c hc hF hrel hconv)

end GaloisForLFunctions.RHTower
