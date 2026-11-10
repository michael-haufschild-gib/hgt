import GaloisForLFunctions.HyperbolicArakelovTheory.TheHyperbolicGreenKernelOfTheWeightedAdelicCarrier
import GaloisForLFunctions.HTGeometry.ConstitutiveDependentLpGaugeTransport

/-!
# Adelic symmetry of the mixed hyperbolic Green kernel

Finite adelic transport acts isometrically on square-summable charges and
commutes with the actual weighted adjacency. The square-root iteration,
its norm limit, and the exponential preserve this symmetry. Both the Green
kernel and its Robin finite part therefore respect every adelic isometry.
-/

set_option autoImplicit false
noncomputable section
open Filter NormedSpace
open scoped Classical Topology
namespace GaloisForLFunctions.HyperbolicArakelovTheory.WeightedAdelicGreen
open FullAdelic CoupledProductObstruction SurfaceOfSpecZ

/-- Pullback of charges by an actual finite adelic isometry. -/
def adelicChargeTransport (a : FiniteAdelicGroup) : ChargeOperator :=
  (HTGeometry.lpDependentDomCongrIsometry (𝕜 := ℝ) (p := 2)
    (E := fun _ : FiniteVertices => ℝ) (by norm_num) (MulAction.toPerm a)).toContinuousLinearMap

theorem adelicChargeTransport_apply (a : FiniteAdelicGroup) (f : ChargeSpace)
    (y : FiniteVertices) : adelicChargeTransport a f y = f (a • y) := rfl

theorem adjacency_commutes_transport (a : FiniteAdelicGroup) :
    Commute adjacencyOperator (adelicChargeTransport a) := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext y
  change adjacencyOperator (adelicChargeTransport a f) y = adjacencyOperator f (a • y)
  rw [adjacencyOperator_apply, adjacencyOperator_apply, adjacency_smul]
  rfl

private theorem root_iterate_commutes_transport (a : FiniteAdelicGroup) (n : ℕ) :
    Commute (rootStep^[n] 0) (adelicChargeTransport a) := by
  induction n with
  | zero => exact Commute.zero_left _
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change ((2 * rootScale)⁻¹ • (adjacencyOperator +
      (rootStep^[n] 0) * (rootStep^[n] 0))) * adelicChargeTransport a =
      adelicChargeTransport a * ((2 * rootScale)⁻¹ • (adjacencyOperator +
        (rootStep^[n] 0) * (rootStep^[n] 0)))
    rw [smul_mul_assoc, mul_smul_comm, add_mul, mul_add, (adjacency_commutes_transport a).eq]
    congr 2
    rw [mul_assoc, ih.eq, ← mul_assoc, ih.eq, mul_assoc]

/-- The norm limit of adjacency polynomials preserves finite adelic symmetry. -/
theorem rootRemainder_commutes_transport (a : FiniteAdelicGroup) :
    Commute rootRemainder (adelicChargeTransport a) := by
  have h₁ := tendsto_rootStep_iterate.mul_const (adelicChargeTransport a)
  have he : (fun n : ℕ => (rootStep^[n] 0) * adelicChargeTransport a) =
      (fun n : ℕ => adelicChargeTransport a * (rootStep^[n] 0)) :=
    funext fun n => (root_iterate_commutes_transport a n).eq
  have h₂ : Tendsto (fun n : ℕ => (rootStep^[n] 0) * adelicChargeTransport a) atTop
      (𝓝 (adelicChargeTransport a * rootRemainder)) := by
    rw [he]
    exact tendsto_rootStep_iterate.const_mul (adelicChargeTransport a)
  exact tendsto_nhds_unique h₁ h₂

theorem hyperbolicRoot_commutes_transport (a : FiniteAdelicGroup) :
    Commute hyperbolicRoot (adelicChargeTransport a) := by
  change (rootScale • (1 : ChargeOperator) - rootRemainder) * adelicChargeTransport a =
    adelicChargeTransport a * (rootScale • (1 : ChargeOperator) - rootRemainder)
  rw [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
    (rootRemainder_commutes_transport a).eq]

theorem hyperbolicEvolution_commutes_transport (r : ℝ) (a : FiniteAdelicGroup) :
    Commute (hyperbolicEvolution r) (adelicChargeTransport a) :=
  (((hyperbolicRoot_commutes_transport a).neg_left).smul_left r).exp_left

theorem adelicChargeTransport_single (a : FiniteAdelicGroup) (x : FiniteVertices) :
    adelicChargeTransport a (lp.single 2 (a • x) (1 : ℝ)) = lp.single 2 x 1 := by
  apply lp.ext
  funext y
  rw [adelicChargeTransport_apply]
  by_cases hy : y = x
  · subst y
    rw [lp.single_apply_self, lp.single_apply_self]
  · have hne : a • y ≠ a • x := fun h => hy ((MulAction.injective a) h)
    rw [lp.single_apply_ne (E := fun _ : FiniteVertices => ℝ) 2 (a • x) 1 hne,
      lp.single_apply_ne (E := fun _ : FiniteVertices => ℝ) 2 x 1 hy]

private theorem matrix_entry_smul (T : ChargeOperator) (a : FiniteAdelicGroup)
    (hT : Commute T (adelicChargeTransport a)) (x y : FiniteVertices) :
    T (lp.single 2 (a • x) (1 : ℝ)) (a • y) = T (lp.single 2 x 1) y := by
  have h := congrArg (fun S : ChargeOperator => S (lp.single 2 (a • x) (1 : ℝ)) y) hT.eq
  change T (adelicChargeTransport a (lp.single 2 (a • x) (1 : ℝ))) y =
    T (lp.single 2 (a • x) (1 : ℝ)) (a • y) at h
  rw [adelicChargeTransport_single] at h
  exact h.symm

theorem mixedGreenEntry_smul (r : ℝ) (a : FiniteAdelicGroup) (x y : FiniteVertices) :
    mixedGreenEntry r (a • x) (a • y) = mixedGreenEntry r x y :=
  matrix_entry_smul (mixedGreen r) a
    ((hyperbolicEvolution_commutes_transport r a).smul_left (hyperbolicGreen 1 r)) x y

theorem mixedRobinEntry_smul (a : FiniteAdelicGroup) (x y : FiniteVertices) :
    mixedRobinEntry (a • x) (a • y) = mixedRobinEntry x y := by
  change -(1 / (4 * Real.pi)) * hyperbolicRoot (lp.single 2 (a • x) (1 : ℝ)) (a • y) =
    -(1 / (4 * Real.pi)) * hyperbolicRoot (lp.single 2 x (1 : ℝ)) y
  rw [matrix_entry_smul hyperbolicRoot a (hyperbolicRoot_commutes_transport a) x y]

theorem regularizedMixedEntry_smul (r : ℝ) (a : FiniteAdelicGroup) (x y : FiniteVertices) :
    regularizedMixedEntry r (a • x) (a • y) = regularizedMixedEntry r x y := by
  simp only [regularizedMixedEntry, mixedRobinEntry_smul, mixedGreenEntry_smul]

/-- Simultaneous adelic isometries preserve the kernel, including its finite part. -/
theorem regularizedMixedKernel_smul (g : AdelicGroup) (x y : GlobalSpace) :
    regularizedMixedKernel (g • x) (g • y) = regularizedMixedKernel x y := by
  change regularizedMixedEntry (h3Dist (h3Act g.1 x.1) (h3Act g.1 y.1))
    (g.2 • x.2) (g.2 • y.2) = regularizedMixedEntry (h3Dist x.1 y.1) x.2 y.2
  rw [CoupledProductObstruction.h3Dist_h3Act, regularizedMixedEntry_smul]

theorem regularizedMixedKernel_symm (x y : GlobalSpace) :
    regularizedMixedKernel x y = regularizedMixedKernel y x := by
  unfold regularizedMixedKernel regularizedMixedEntry
  rw [h3Dist_comm x.1 y.1, mixedGreenEntry_symm, mixedRobinEntry_symm]

#print axioms rootRemainder_commutes_transport
#print axioms regularizedMixedKernel_smul
#print axioms regularizedMixedKernel_symm
end GaloisForLFunctions.HyperbolicArakelovTheory.WeightedAdelicGreen
