/-
# Recognising homogeneity from the evaluation, and dominating a product by one factor

Two elementary facts complete the transversality-tail elimination.

First, a polynomial whose evaluation scales like a power is homogeneous of that degree: comparing
the scaling of the homogeneous components as a polynomial identity in the scaling parameter kills
every other component.  This supplies the homogeneity hypothesis of the shell sublevel bound
without tracking degrees through the construction.

Second, on a compact space a continuous cofactor is bounded, so a product of a continuous function
with a nonnegative observable is dominated by a constant multiple of that observable.  This supplies
the domination hypothesis of the transferred sublevel bound.

Main results:
* `isHomogeneous_of_eval_smul` — **the converse: scaling of the evaluation forces homogeneity**.
* `exists_bound_of_continuous_cofactor` — **a continuous cofactor is a constant on a compact space**.
-/
import GaloisForLFunctions.HTGeometry.PolynomialSublevelSphere
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial

variable {N : ℕ}

/-- **The converse.**  A polynomial whose evaluation scales like a power is homogeneous. -/
theorem isHomogeneous_of_eval_smul {d : ℕ} {G : MvPolynomial (Fin N) ℝ}
    (h : ∀ t : ℝ, ∀ x : Fin N → ℝ,
      MvPolynomial.eval (fun i => t * x i) G = t ^ d * MvPolynomial.eval x G) :
    G.IsHomogeneous d := by
  classical
  set D := G.totalDegree with hD
  have hcomp : ∀ x : Fin N → ℝ, ∀ t : ℝ,
      (∑ j ∈ Finset.range (D + 1), t ^ j *
        MvPolynomial.eval x ((MvPolynomial.homogeneousComponent j) G))
        = t ^ d * MvPolynomial.eval x G := by
    intro x t
    rw [← h t x]
    conv_rhs => rw [← MvPolynomial.sum_homogeneousComponent G]
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ =>
      (eval_smul_of_isHomogeneous (MvPolynomial.homogeneousComponent_isHomogeneous j G) t x).symm
  have hzero : ∀ (j : ℕ), j ∈ Finset.range (D + 1) → j ≠ d →
      (MvPolynomial.homogeneousComponent j) G = 0 := by
    intro j hj hjd
    refine MvPolynomial.funext fun x => ?_
    have hpoly : (∑ k ∈ Finset.range (D + 1),
          Polynomial.C (MvPolynomial.eval x ((MvPolynomial.homogeneousComponent k) G))
            * Polynomial.X ^ k)
        = Polynomial.C (MvPolynomial.eval x G) * Polynomial.X ^ d := by
      refine Polynomial.funext fun t => ?_
      have hL : (∑ k ∈ Finset.range (D + 1),
            Polynomial.C (MvPolynomial.eval x ((MvPolynomial.homogeneousComponent k) G))
              * Polynomial.X ^ k).eval t
          = ∑ k ∈ Finset.range (D + 1), t ^ k *
              MvPolynomial.eval x ((MvPolynomial.homogeneousComponent k) G) := by
        rw [Polynomial.eval_finsetSum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
          mul_comm]
      have hR : (Polynomial.C (MvPolynomial.eval x G) * Polynomial.X ^ d).eval t
          = t ^ d * MvPolynomial.eval x G := by
        rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
          mul_comm]
      rw [hL, hR]
      exact hcomp x t
    have hcoeff := congrArg (fun p : Polynomial ℝ => p.coeff j) hpoly
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      mul_ite, mul_one, mul_zero] at hcoeff
    rw [Finset.sum_ite_eq (Finset.range (D + 1)) j
      (fun k => MvPolynomial.eval x ((MvPolynomial.homogeneousComponent k) G))] at hcoeff
    rw [if_pos hj, if_neg hjd] at hcoeff
    simpa using hcoeff
  have hGeq : G = (MvPolynomial.homogeneousComponent d) G := by
    conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent G]
    by_cases hdD : d ∈ Finset.range (D + 1)
    · rw [Finset.sum_eq_single d (fun j hj hjd => hzero j hj hjd) (fun hc => absurd hdD hc)]
    · have hall : ∀ j ∈ Finset.range (D + 1), (MvPolynomial.homogeneousComponent j) G = 0 := by
        intro j hj
        exact hzero j hj (fun hc => hdD (hc ▸ hj))
      rw [Finset.sum_congr rfl hall, Finset.sum_const_zero]
      have hGz : G = 0 := by
        conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent G]
        rw [Finset.sum_congr rfl hall, Finset.sum_const_zero]
      rw [hGz, map_zero]
  rw [hGeq]
  exact MvPolynomial.homogeneousComponent_isHomogeneous d G

/-- **A continuous cofactor is a constant on a compact space.** -/
theorem exists_bound_of_continuous_cofactor {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [Nonempty X] {F h g : X → ℝ} (hg : Continuous g) (hh : ∀ x, 0 ≤ h x)
    (hF : ∀ x, F x = g x * h x) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, |F x| ≤ C * h x := by
  obtain ⟨x₀, -, hmax⟩ := (isCompact_univ (X := X)).exists_isMaxOn (Set.univ_nonempty)
    (hg.abs.continuousOn)
  refine ⟨1 + |g x₀|, by positivity, fun x => ?_⟩
  have hle : |g x| ≤ |g x₀| := hmax (Set.mem_univ x)
  calc |F x| = |g x| * h x := by rw [hF x, abs_mul, abs_of_nonneg (hh x)]
    _ ≤ (1 + |g x₀|) * h x := by
        refine mul_le_mul_of_nonneg_right ?_ (hh x)
        linarith

end

end GaloisForLFunctions.HTGeometry
