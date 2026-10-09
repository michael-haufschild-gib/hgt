import GaloisForLFunctions.HTGeometry.QKrawtchoukCompanionOperator
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.Normed.Algebra.GelfandFormula

/-!
# Norm-resolvent convergence for the balanced companion limit

Every finite and limiting companion operator is self-adjoint, so every
pole `a + i exp(b)` lies in its resolvent set. The actual resolvents use
the convention `(J-z)⁻¹`. Continuity of inversion in the operator norm
upgrades the companion operator limit to norm-resolvent convergence.

This strengthens the strong-resolvent conclusion of arXiv:2609.24149,
Theorem 8.2, for the balanced fixed-shape family constructed here.
-/

noncomputable section
open Filter
open scoped Topology

namespace HTGeometry

local notation "H" => lp (fun _ : ℕ => ℂ) 2
local notation "Op" => H →L[ℂ] H

private theorem nonreal_mem (A : Op) (hA : IsSelfAdjoint A) (a b : ℝ) :
    Complex.mk a (Real.exp b) ∈ resolventSet ℂ A := by
  by_contra hz
  have hs : Complex.mk a (Real.exp b) ∈ spectrum ℂ A := hz
  have hi := hA.im_eq_zero_of_mem_spectrum hs
  exact (Real.exp_pos b).ne' hi

private theorem inverse_pair (A : Op) (hA : IsSelfAdjoint A) (a b : ℝ) (f : H) :
    A ((-resolvent A (Complex.mk a (Real.exp b))) f) -
        Complex.mk a (Real.exp b) • ((-resolvent A (Complex.mk a (Real.exp b))) f) = f ∧
      (-resolvent A (Complex.mk a (Real.exp b)))
        (A f - Complex.mk a (Real.exp b) • f) = f := by
  let z := Complex.mk a (Real.exp b)
  have hz : IsUnit (algebraMap ℂ Op z - A) := nonreal_mem A hA a b
  have hshift : A - z • (1 : Op) = -(algebraMap ℂ Op z - A) := by
    rw [Algebra.algebraMap_eq_smul_one]
    abel
  have hr : (A - z • (1 : Op)) * (-resolvent A z) = 1 := by
    rw [hshift, neg_mul_neg]
    exact Ring.mul_inverse_cancel _ hz
  have hl : (-resolvent A z) * (A - z • (1 : Op)) = 1 := by
    rw [hshift, neg_mul_neg]
    exact Ring.inverse_mul_cancel _ hz
  constructor
  · simpa only [mul_apply_eq_comp, sub_apply, smul_apply, one_apply_eq_self] using
      congrArg (fun T : Op => T f) hr
  · simpa only [mul_apply_eq_comp, sub_apply, smul_apply, one_apply_eq_self] using
      congrArg (fun T : Op => T f) hl

/-- The actual resolvent of the limiting companion Jacobi operator. -/
def alSalamCarlitzResolvent (t u a b : ℝ) : Op :=
  -resolvent (alSalamCarlitzJacobiCLM t u) (Complex.mk a (Real.exp b))

/-- The actual resolvent of the extended finite companion matrix. -/
def qKrawtchoukCompanionResolvent (t u : ℝ) (K : ℕ) (a b : ℝ) : Op :=
  -resolvent (qKrawtchoukCompanionJacobiCLM t u K) (Complex.mk a (Real.exp b))

/-- The limiting resolvent is a two-sided inverse at every parametrized nonreal pole. -/
theorem alSalamCarlitzResolvent_inverse (t u a b : ℝ) (f : H) :
    alSalamCarlitzJacobiCLM t u (alSalamCarlitzResolvent t u a b f) -
        Complex.mk a (Real.exp b) • alSalamCarlitzResolvent t u a b f = f ∧
      alSalamCarlitzResolvent t u a b
        (alSalamCarlitzJacobiCLM t u f - Complex.mk a (Real.exp b) • f) = f :=
  inverse_pair _ (alSalamCarlitzJacobiCLM_isSelfAdjoint t u) a b f

/-- The finite resolvents are two-sided inverses on the entire common sequence space. -/
theorem qKrawtchoukCompanionResolvent_inverse (t u : ℝ) (K : ℕ) (a b : ℝ) (f : H) :
    qKrawtchoukCompanionJacobiCLM t u K (qKrawtchoukCompanionResolvent t u K a b f) -
        Complex.mk a (Real.exp b) • qKrawtchoukCompanionResolvent t u K a b f = f ∧
      qKrawtchoukCompanionResolvent t u K a b
        (qKrawtchoukCompanionJacobiCLM t u K f - Complex.mk a (Real.exp b) • f) = f :=
  inverse_pair _ (qKrawtchoukCompanionJacobiCLM_isSelfAdjoint t u K) a b f

/-- The companion resolvents converge in operator norm, with no spectral premise. -/
theorem qKrawtchoukCompanionResolvent_norm_tendsto (t u a b : ℝ) :
    Tendsto (fun K => qKrawtchoukCompanionResolvent t u K a b) atTop
      (𝓝 (alSalamCarlitzResolvent t u a b)) := by
  have h := ((spectrum.hasFDerivAt_resolvent
    (nonreal_mem _ (alSalamCarlitzJacobiCLM_isSelfAdjoint t u) a b)).continuousAt.tendsto.comp
      (qKrawtchoukCompanionJacobiCLM_tendsto t u)).neg
  simpa only [alSalamCarlitzResolvent, qKrawtchoukCompanionResolvent, Function.comp_def] using h

end HTGeometry
