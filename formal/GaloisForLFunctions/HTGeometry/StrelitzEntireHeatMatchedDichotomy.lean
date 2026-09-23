import GaloisForLFunctions.HTGeometry.StrelitzJetCurveMatchedDichotomy

/-!
# Matched Strelitz dichotomy for an order-two entire-heat anchor

This module composes the exact entire-heat numerical-root construction with the exhaustive local
Newton-edge analysis.  No branch, boundedness, Newton-face, or convergence hypothesis is added.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter
open GaloisForLFunctions

variable {a : ℕ → ℂ}

/-- An assumed order-two ADE for an infinite entire-heat anchor produces the full exact Wiman
sequence and selected-root data, together with the exhaustive conclusion: either normalized
nonzero roots converge cofinally to a nonzero root of their exact Newton edge, or exact zero roots
recur cofinally and the observed second logarithmic jet tends to zero there. -/
theorem exists_strelitzJetCurveMatchedDichotomy_of_order_two_entireHeat_isMaximumOnCircle
    (ha : EntireCoeffs a)
    (hheat : ∀ t z : ℂ, Summable (fun n : ℕ =>
      a n * Complex.exp (-(4 * (Real.pi : ℂ) ^ (2 : ℕ)) * (n : ℂ) ^ (2 : ℕ) * t)
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z)))
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0)
    (hDA : DifferentiallyAlgebraicOfOrder (coeffFun a) 2) :
    ∃ S : MvPolynomial (Fin 2) ℂ, S ≠ 0 ∧
      1 ≤ (strelitzJetCurvePolynomial S).natDegree ∧
      ∃ (x : ℕ → ℝ) (z root : ℕ → ℂ),
        (∀ n : ℕ, (n : ℝ) ≤ x n) ∧
        (∀ n : ℕ, ‖z n‖ = Real.exp (x n)) ∧
        (∀ n : ℕ, maxTerm a (Real.exp (x n)) ≤ ‖coeffFun a (z n)‖) ∧
        (∀ n : ℕ, coeffFun a (z n) ≠ 0) ∧
        (∀ n : ℕ, ‖eulerLogDeriv (coeffFun a) (z n) -
            (centralIndex a (Real.exp (x n)) : ℂ)‖
          ≤ (1 / ((n : ℝ) + 1)) * (centralIndex a (Real.exp (x n)) : ℝ)) ∧
        (∀ n : ℕ, ‖eulerLogDerivSecond (coeffFun a) (z n)‖
          ≤ (1 / ((n : ℝ) + 1)) * (centralIndex a (Real.exp (x n)) : ℝ) ^ (2 : ℕ)) ∧
        Tendsto x atTop atTop ∧
        Tendsto (fun n => ‖eulerLogDeriv (coeffFun a) (z n)‖) atTop atTop ∧
        (∀ᶠ n : ℕ in atTop,
          (strelitzJetCurveSpecialization S
            (eulerLogDeriv (coeffFun a) (z n))).IsRoot (root n)) ∧
        Tendsto (fun n =>
          ‖eulerLogDerivSecond (coeffFun a) (z n) - root n‖) atTop (nhds 0) ∧
        (HasStrelitzJetCurveMatchedNewtonEdgeLimit S
            (fun n => eulerLogDeriv (coeffFun a) (z n)) root ∨
          ∃ ns : ℕ → ℕ, StrictMono ns ∧
            (∀ k, root (ns k) = 0) ∧
            Tendsto (fun k => ‖eulerLogDerivSecond (coeffFun a) (z (ns k))‖)
              atTop (nhds 0)) ∧
        (∀ n : ℕ, ∀ w : ℂ, ‖w‖ = ‖z n‖ →
          ‖coeffFun a w‖ ≤ ‖coeffFun a (z n)‖) := by
  obtain ⟨S, hS, hdegree, x, z, root, hx, hz, hfloor, hfz, hu, hv,
    hxTop, huTop, hroot, hclose, hmaxCircle⟩ :=
    exists_strelitzJetCurveRoots_tendsto_of_order_two_entireHeat_isMaximumOnCircle
      ha hheat htrans hDA
  have hrTop : Tendsto (fun n => Real.exp (x n)) atTop atTop :=
    Real.tendsto_exp_atTop.comp hxTop
  have hνTop : Tendsto (fun n => centralIndex a (Real.exp (x n))) atTop atTop :=
    (tendsto_centralIndex_atTop ha htrans).comp hrTop
  have hdichotomy := strelitzJetCurve_matchedNewtonEdge_or_zeroBranch hS hνTop hu hroot hclose
  exact ⟨S, hS, hdegree, x, z, root, hx, hz, hfloor, hfz, hu, hv,
    hxTop, huTop, hroot, hclose, hdichotomy, hmaxCircle⟩

/-- An assumed order-two ADE for an infinite entire-heat anchor produces the full exact Wiman
sequence and selected-root data, together with the exhaustive conclusion: either normalized
nonzero roots converge cofinally to a nonzero root of their exact Newton edge, or exact zero roots
recur cofinally and the observed second logarithmic jet tends to zero there. -/
theorem exists_strelitzJetCurveMatchedDichotomy_of_order_two_entireHeat
    (ha : EntireCoeffs a)
    (hheat : ∀ t z : ℂ, Summable (fun n : ℕ =>
      a n * Complex.exp (-(4 * (Real.pi : ℂ) ^ (2 : ℕ)) * (n : ℂ) ^ (2 : ℕ) * t)
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z)))
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0)
    (hDA : DifferentiallyAlgebraicOfOrder (coeffFun a) 2) :
    ∃ S : MvPolynomial (Fin 2) ℂ, S ≠ 0 ∧
      1 ≤ (strelitzJetCurvePolynomial S).natDegree ∧
      ∃ (x : ℕ → ℝ) (z root : ℕ → ℂ),
        (∀ n : ℕ, (n : ℝ) ≤ x n) ∧
        (∀ n : ℕ, ‖z n‖ = Real.exp (x n)) ∧
        (∀ n : ℕ, maxTerm a (Real.exp (x n)) ≤ ‖coeffFun a (z n)‖) ∧
        (∀ n : ℕ, coeffFun a (z n) ≠ 0) ∧
        (∀ n : ℕ, ‖eulerLogDeriv (coeffFun a) (z n) -
            (centralIndex a (Real.exp (x n)) : ℂ)‖
          ≤ (1 / ((n : ℝ) + 1)) * (centralIndex a (Real.exp (x n)) : ℝ)) ∧
        (∀ n : ℕ, ‖eulerLogDerivSecond (coeffFun a) (z n)‖
          ≤ (1 / ((n : ℝ) + 1)) * (centralIndex a (Real.exp (x n)) : ℝ) ^ (2 : ℕ)) ∧
        Tendsto x atTop atTop ∧
        Tendsto (fun n => ‖eulerLogDeriv (coeffFun a) (z n)‖) atTop atTop ∧
        (∀ᶠ n : ℕ in atTop,
          (strelitzJetCurveSpecialization S
            (eulerLogDeriv (coeffFun a) (z n))).IsRoot (root n)) ∧
        Tendsto (fun n =>
          ‖eulerLogDerivSecond (coeffFun a) (z n) - root n‖) atTop (nhds 0) ∧
        (HasStrelitzJetCurveMatchedNewtonEdgeLimit S
            (fun n => eulerLogDeriv (coeffFun a) (z n)) root ∨
          ∃ ns : ℕ → ℕ, StrictMono ns ∧
            (∀ k, root (ns k) = 0) ∧
            Tendsto (fun k => ‖eulerLogDerivSecond (coeffFun a) (z (ns k))‖)
              atTop (nhds 0)) := by
  obtain ⟨S, hS, hdegree, x, z, root, hx, hz, hfloor, hfz, hu, hv,
    hxTop, huTop, hroot, hclose, hdichotomy, _⟩ :=
    exists_strelitzJetCurveMatchedDichotomy_of_order_two_entireHeat_isMaximumOnCircle
      ha hheat htrans hDA
  exact ⟨S, hS, hdegree, x, z, root, hx, hz, hfloor, hfz, hu, hv,
    hxTop, huTop, hroot, hclose, hdichotomy⟩

end

end GaloisForLFunctions.HTGeometry
