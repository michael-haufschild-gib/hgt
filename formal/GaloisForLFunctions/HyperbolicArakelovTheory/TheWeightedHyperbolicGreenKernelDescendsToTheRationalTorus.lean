import GaloisForLFunctions.HyperbolicArakelovTheory.TheHyperbolicGreenKernelHasUniformAdelicDecay
import GaloisForLFunctions.HyperbolicArakelovTheory.TheRationalTorusHasSummableAdelicProfiles
import GaloisForLFunctions.HyperbolicArakelovTheory.TheHyperbolicGreenKernelRespectsAdelicIsometries
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# The weighted Green kernel on the rational-torus quotient

Strictly tempered adelic profiles dominate the mixed Green entries uniformly
at archimedean collisions whenever the finite vertices differ. Their rational
height sum converges; equal finite vertices give only finitely many exceptions.
Thus the full rational-torus orbit sum converges absolutely on every pair of
points. Adelic covariance gives symmetry and descent in both arguments.
-/

set_option autoImplicit false
noncomputable section
open Filter Matrix
open scoped Classical BigOperators Topology
namespace GaloisForLFunctions.HyperbolicArakelovTheory.WeightedAdelicGreen
open FullAdelic CoupledProductObstruction SurfaceOfSpecZ

/-- The conjugated rational split torus, with its multiplicative parametrization. -/
def rationalTorusEmbedding : ℚˣ →* AdelicGroup where
  toFun q := (torusElem (q : ℚ) q.ne_zero).1
  map_one' := by
    have hd : OppositeAdelic.diagonal 1 (by norm_num) = 1 := by
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [OppositeAdelic.diagonal]
    change conjugateEmbedding (OppositeAdelic.diagonal 1 _) = 1
    rw [hd, map_one]
  map_mul' q r := by
    change conjugateEmbedding (OppositeAdelic.diagonal ((q : ℚ) * r) _) =
      conjugateEmbedding (OppositeAdelic.diagonal (q : ℚ) _) *
        conjugateEmbedding (OppositeAdelic.diagonal (r : ℚ) _)
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [OppositeAdelic.diagonal, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

/-- Absolute convergence on the full carrier, including the finitely many equal-fibre terms. -/
theorem summable_norm_torusGreen (x y : GlobalSpace) :
    Summable (fun q : ℚˣ => ‖regularizedMixedKernel x (rationalTorusEmbedding q • y)‖) := by
  apply summable_of_isBigO (summable_barrierProfile_rationalTorus x.2 y.2)
  refine Asymptotics.IsBigO.of_bound (barrierRemainder / (4 * Real.pi)) ?_
  have he : ∀ᶠ q : ℚˣ in cofinite, x.2 ≠ rationalTorusFinite q • y.2 := by
    apply Filter.eventually_cofinite.mpr
    simpa only [not_not] using finite_rationalTorus_equal_fibres x.2 y.2
  filter_upwards [he] with q hq
  have hb := regularizedMixedEntry_bound
    (h3Dist_nonneg x.1 (rationalTorusEmbedding q • y).1) hq
  change ‖‖regularizedMixedEntry (h3Dist x.1 (rationalTorusEmbedding q • y).1)
      x.2 (rationalTorusFinite q • y.2)‖‖ ≤
    (barrierRemainder / (4 * Real.pi)) * ‖barrierProfile x.2 (rationalTorusFinite q • y.2)‖
  simpa only [norm_norm, Real.norm_eq_abs, abs_of_nonneg hb.1,
    abs_of_pos (barrierProfile_pos x.2 (rationalTorusFinite q • y.2))] using hb.2

theorem summable_torusGreen (x y : GlobalSpace) :
    Summable (fun q : ℚˣ => regularizedMixedKernel x (rationalTorusEmbedding q • y)) :=
  (summable_norm_torusGreen x y).of_norm

/-- The absolutely convergent orbit sum, with the canonical Robin value at collisions. -/
def torusGreenSum (x y : GlobalSpace) : ℝ :=
  ∑' q : ℚˣ, regularizedMixedKernel x (rationalTorusEmbedding q • y)

private theorem green_torus_move_left (r q : ℚˣ) (x y : GlobalSpace) :
    regularizedMixedKernel (rationalTorusEmbedding r • x) (rationalTorusEmbedding q • y) =
      regularizedMixedKernel x (rationalTorusEmbedding (r⁻¹ * q) • y) := by
  have hy : rationalTorusEmbedding q • y =
      rationalTorusEmbedding r • (rationalTorusEmbedding (r⁻¹ * q) • y) := by
    rw [← mul_smul, ← map_mul, mul_inv_cancel_left]
  rw [hy, regularizedMixedKernel_smul]

/-- Simultaneous covariance becomes invariance of the first argument after reindexing. -/
theorem torusGreenSum_left (r : ℚˣ) (x y : GlobalSpace) :
    torusGreenSum (rationalTorusEmbedding r • x) y = torusGreenSum x y := by
  unfold torusGreenSum
  simp_rw [green_torus_move_left]
  exact (Equiv.mulLeft r⁻¹).tsum_eq (fun q =>
    regularizedMixedKernel x (rationalTorusEmbedding q • y))

/-- Multiplication of the orbit parameter gives invariance of the second argument. -/
theorem torusGreenSum_right (r : ℚˣ) (x y : GlobalSpace) :
    torusGreenSum x (rationalTorusEmbedding r • y) = torusGreenSum x y := by
  unfold torusGreenSum
  simp_rw [← mul_smul, ← map_mul]
  exact (Equiv.mulRight r).tsum_eq (fun q =>
    regularizedMixedKernel x (rationalTorusEmbedding q • y))

/-- Kernel symmetry and inversion of the rational parameter give orbit-sum symmetry. -/
theorem torusGreenSum_symm (x y : GlobalSpace) : torusGreenSum x y = torusGreenSum y x := by
  have ht (q : ℚˣ) :
      regularizedMixedKernel x (rationalTorusEmbedding q • y) =
        regularizedMixedKernel y (rationalTorusEmbedding q⁻¹ • x) := by
    rw [regularizedMixedKernel_symm]
    have h := green_torus_move_left q 1 y x
    simpa only [map_one, one_smul, mul_one] using h
  unfold torusGreenSum
  simp_rw [ht]
  exact (Equiv.inv ℚˣ).tsum_eq (fun q =>
    regularizedMixedKernel y (rationalTorusEmbedding q • x))

def rationalTorusGroup : Subgroup AdelicGroup := rationalTorusEmbedding.range

theorem torusGreenSum_subgroup_left (g : rationalTorusGroup) (x y : GlobalSpace) :
    torusGreenSum (g • x) y = torusGreenSum x y := by
  obtain ⟨q, hq⟩ := g.property
  change torusGreenSum ((g : AdelicGroup) • x) y = _
  rw [← hq, torusGreenSum_left]

theorem torusGreenSum_subgroup_right (g : rationalTorusGroup) (x y : GlobalSpace) :
    torusGreenSum x (g • y) = torusGreenSum x y := by
  obtain ⟨q, hq⟩ := g.property
  change torusGreenSum x ((g : AdelicGroup) • y) = _
  rw [← hq, torusGreenSum_right]

/-- Orbits of the rational split torus on the full archimedean and finite carrier. -/
abbrev RationalTorusCarrier := Quotient (MulAction.orbitRel rationalTorusGroup GlobalSpace)

/-- The symmetric Green sum descended in both arguments to the rational-torus quotient. -/
def torusQuotientGreen (x y : RationalTorusCarrier) : ℝ :=
  Quotient.liftOn₂ x y torusGreenSum (by
    rintro x y x' y' ⟨g, rfl⟩ ⟨h, rfl⟩
    rw [torusGreenSum_subgroup_left, torusGreenSum_subgroup_right])

theorem torusQuotientGreen_mk (x y : GlobalSpace) :
    torusQuotientGreen (Quotient.mk _ x) (Quotient.mk _ y) = torusGreenSum x y := rfl

theorem torusQuotientGreen_symm (x y : RationalTorusCarrier) :
    torusQuotientGreen x y = torusQuotientGreen y x := by
  induction x using Quotient.inductionOn with
  | h x =>
    induction y using Quotient.inductionOn with
    | h y => exact torusGreenSum_symm x y

#print axioms summable_norm_torusGreen
#print axioms torusGreenSum_left
#print axioms torusGreenSum_right
#print axioms torusQuotientGreen_symm
end GaloisForLFunctions.HyperbolicArakelovTheory.WeightedAdelicGreen
