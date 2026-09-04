import GaloisForLFunctions.HTGeometry.StrelitzAngularCurvature
import GaloisForLFunctions.HTGeometry.StrelitzJetCurveSlopeSign

/-!
# Maximum-point signs in the Strelitz slope trichotomy

The Wiman points used by the complete local Newton package are genuine maximum-modulus points.
Consequently their first Euler logarithmic jets are real and their second Euler logarithmic jets
have nonnegative real part.  This module retains those exact sign facts in the full unconditional
order-two entire-heat package.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter
open GaloisForLFunctions

/-- Exact angular first- and second-jet signs at a sequence of maximum-modulus points. -/
structure StrelitzMaximumPointJetSigns (a : ℕ → ℂ) (z : ℕ → ℂ) : Prop where
  mem_circleMaximumSet : ∀ n : ℕ, z n ∈ circleMaximumSet (coeffFun a)
  firstJet_im_eq_zero : ∀ n : ℕ, (eulerLogDeriv (coeffFun a) (z n)).im = 0
  secondJet_re_nonneg : ∀ n : ℕ, 0 ≤ (eulerLogDerivSecond (coeffFun a) (z n)).re

variable {a : ℕ → ℂ}

/-- Under exactly the order-two entire-heat assumptions, the complete Strelitz slope-sign
trichotomy can be realized at genuine maximum-modulus points.  At every selected point the first
Euler logarithmic jet is real and the second has nonnegative real part. -/
theorem exists_strelitzMaximumPointSlopeSignTrichotomy_of_order_two_entireHeat
    (ha : EntireCoeffs a)
    (hheat : ∀ t z : ℂ, Summable (fun n : ℕ =>
      a n * Complex.exp (-(4 * (Real.pi : ℂ) ^ 2) * (n : ℂ) ^ 2 * t)
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
          ≤ (1 / ((n : ℝ) + 1)) * (centralIndex a (Real.exp (x n)) : ℝ) ^ 2) ∧
        Tendsto x atTop atTop ∧
        Tendsto (fun n => ‖eulerLogDeriv (coeffFun a) (z n)‖) atTop atTop ∧
        (∀ᶠ n : ℕ in atTop,
          (strelitzJetCurveSpecialization S
            (eulerLogDeriv (coeffFun a) (z n))).IsRoot (root n)) ∧
        Tendsto (fun n =>
          ‖eulerLogDerivSecond (coeffFun a) (z n) - root n‖) atTop (nhds 0) ∧
        (HasStrelitzJetCurveMatchedNewtonEdgeLimitWith (fun p => 0 ≤ p ∧ p < 2) S
              (fun n => eulerLogDeriv (coeffFun a) (z n)) root ∨
          (HasStrelitzJetCurveMatchedNewtonEdgeLimitWith (fun p => p < 0) S
                (fun n => eulerLogDeriv (coeffFun a) (z n)) root ∧
            ∃ idx : ℕ → ℕ, StrictMono idx ∧
              Tendsto (fun n => ‖root (idx n)‖) atTop (nhds 0) ∧
              Tendsto (fun n => ‖eulerLogDerivSecond (coeffFun a) (z (idx n))‖)
                atTop (nhds 0)) ∨
          ((Polynomial.X ∣ strelitzJetCurvePolynomial S) ∧
            ∃ ns : ℕ → ℕ, StrictMono ns ∧
              (∀ k, root (ns k) = 0) ∧
              Tendsto (fun k => ‖eulerLogDerivSecond (coeffFun a) (z (ns k))‖)
                atTop (nhds 0))) ∧
        StrelitzMaximumPointJetSigns a z := by
  obtain ⟨S, hS, hdegree, x, z, root, hx, hz, hfloor, hfz, hu, hv,
    hxTop, huTop, hroot, hclose, htri, hmaxCircle⟩ :=
    exists_strelitzJetCurveSlopeSignTrichotomy_of_order_two_entireHeat_isMaximumOnCircle
      ha hheat htrans hDA
  have hmax : ∀ n : ℕ, z n ∈ circleMaximumSet (coeffFun a) := hmaxCircle
  have hz0 : ∀ n : ℕ, z n ≠ 0 := by
    intro n hzn
    have hexpzero : Real.exp (x n) = 0 := by
      simpa [hzn] using (hz n).symm
    exact Real.exp_ne_zero (x n) hexpzero
  have him : ∀ n : ℕ, (eulerLogDeriv (coeffFun a) (z n)).im = 0 := by
    intro n
    exact eulerLogDeriv_im_eq_zero_of_mem_circleMaximumSet
      ha (hz0 n) (hfz n) (hmax n)
  have hre : ∀ n : ℕ, 0 ≤ (eulerLogDerivSecond (coeffFun a) (z n)).re := by
    intro n
    exact eulerLogDerivSecond_re_nonneg_of_mem_circleMaximumSet ha (hfz n) (hmax n)
  exact ⟨S, hS, hdegree, x, z, root, hx, hz, hfloor, hfz, hu, hv,
    hxTop, huTop, hroot, hclose, htri, ⟨hmax, him, hre⟩⟩

end

end GaloisForLFunctions.HTGeometry
