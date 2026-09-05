import GaloisForLFunctions.HTGeometry.NoncommutativeAbelDevelopment
import GaloisForLFunctions.RHTower.EulerDeletionQuasiShuffleConvergence

/-!
# Literal Euler-deletion histories in complete normed algebras

The literal coefficients are `1 - (q+1) * indicator ((q+1) divides n+1)`. Their partial sums
are bounded by `q`. For every `Re s > 0`, the weights `(n+1)^(-s)` tend to zero and have
summable successive differences. The noncommutative Abel theorem therefore constructs an
invertible chronological exponential limit after any continuous real-linear map into a complete
real normed algebra. The limit commutes with continuous algebra homomorphisms.

No zero, chosen divisor, second-level coherence, or unproved arithmetic bound is an input.
This is a source completion theorem, not a proof that the completed history is the identity
and not a proof of critical-line selection. It treats one deletion modulus at a time; it does
not identify the different moduli's histories or construct their joint universal signature.
The exponential lift is explicit: no identification with the raw quasi-shuffle lift of the
discrete jumps is asserted. In particular its convergence is not a bracket-preservation theorem.
-/

noncomputable section
open Filter Topology
open scoped BigOperators

namespace RHTower
open GaloisForLFunctions.HTGeometry.NoncommutativeAbel

def realDeletionCoefficient (q n : ℕ) : ℝ :=
  (blockDeletionCoefficient (q + 1) (n + 1) : ℝ)

theorem realDeletionCoefficient_partialSum_bound (q N : ℕ) :
    |coefficientSum (realDeletionCoefficient q) N| ≤ q := by
  have heq : ((coefficientSum (realDeletionCoefficient q) N : ℝ) : ℂ) =
      ∑ n ∈ Finset.range N, eulerDeletionDirichletCoefficient q n := by
    simp [coefficientSum, realDeletionCoefficient, eulerDeletionDirichletCoefficient]
  have hb := eulerDeletionDirichletCoefficient_partialSum_norm_le q N
  rw [← heq] at hb
  simpa only [Complex.norm_real, Real.norm_eq_abs] using hb

def arithmeticDirichletWeight (s : ℂ) (n : ℕ) : ℂ :=
  (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)

theorem arithmeticDirichletWeight_tendsto_zero {s : ℂ} (hs : 0 < s.re) :
    Tendsto (arithmeticDirichletWeight s) atTop (nhds 0) := by
  have hr := (GaloisForLFunctions.RHTower.tendsto_rpow_neg_nat_atTop hs).comp
    (tendsto_add_atTop_nat 1)
  have hnorm (n : ℕ) : ‖arithmeticDirichletWeight s n‖ = ((n : ℝ) + 1) ^ (-s.re) := by
    change ‖(((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)‖ = _
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    simp only [Complex.neg_re]
  apply squeeze_zero_norm (fun n => (hnorm n).le)
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using hr

theorem arithmeticDirichletWeight_summable_variation {s : ℂ} (hs : 0 < s.re) :
    Summable (fun n => ‖arithmeticDirichletWeight s n - arithmeticDirichletWeight s (n + 1)‖) := by
  simpa [arithmeticDirichletWeight, Nat.cast_add, add_assoc, one_add_one_eq_two] using
    GaloisForLFunctions.RHTower.summable_norm_cpow_increment hs

def eulerDeletionDevelopment {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    (q : ℕ) (s : ℂ) (L : ℂ →L[ℝ] A) : ℕ → A :=
  orderedProduct (fun n => NormedSpace.exp
    (realDeletionCoefficient q n • L (arithmeticDirichletWeight s n)))

theorem eulerDeletionDevelopment_converges_to_unit
    {A : Type*} [NormedRing A] [NormOneClass A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (q : ℕ) {s : ℂ} (hs : 0 < s.re) (L : ℂ →L[ℝ] A) :
    ∃ P : A, IsUnit P ∧ Tendsto (eulerDeletionDevelopment q s L) atTop (nhds P) := by
  apply ordered_exponential_converges_to_unit
    (realDeletionCoefficient_partialSum_bound q)
  · simpa only [Function.comp_def, map_zero] using
      L.continuous.tendsto (0 : ℂ) |>.comp (arithmeticDirichletWeight_tendsto_zero hs)
  · apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      ((arithmeticDirichletWeight_summable_variation hs).mul_left ‖L‖)
    rw [← map_sub]
    exact L.le_opNorm _

section Limit
variable {A : Type*} [NormedRing A] [NormOneClass A] [NormedAlgebra ℝ A] [CompleteSpace A]

def eulerDeletionDevelopmentLimit (q : ℕ) (s : {z : ℂ // 0 < z.re})
    (L : ℂ →L[ℝ] A) : A :=
  Classical.choose (eulerDeletionDevelopment_converges_to_unit q s.property L)

theorem isUnit_eulerDeletionDevelopmentLimit (q : ℕ) (s : {z : ℂ // 0 < z.re})
    (L : ℂ →L[ℝ] A) : IsUnit (eulerDeletionDevelopmentLimit q s L) :=
  (Classical.choose_spec (eulerDeletionDevelopment_converges_to_unit q s.property L)).1

theorem tendsto_eulerDeletionDevelopment (q : ℕ) (s : {z : ℂ // 0 < z.re})
    (L : ℂ →L[ℝ] A) :
    Tendsto (eulerDeletionDevelopment q s.val L) atTop (nhds (eulerDeletionDevelopmentLimit q s L)) :=
  (Classical.choose_spec (eulerDeletionDevelopment_converges_to_unit q s.property L)).2

variable {B : Type*} [NormedRing B] [NormOneClass B] [NormedAlgebra ℝ B] [CompleteSpace B]
local instance : NormedAlgebra ℚ A := .restrictScalars ℚ ℝ A
local instance : NormedAlgebra ℚ B := .restrictScalars ℚ ℝ B

omit [NormOneClass A] [NormOneClass B] [CompleteSpace B] in
theorem map_eulerDeletionDevelopment (φ : A →A[ℝ] B) (q : ℕ) (s : ℂ)
    (L : ℂ →L[ℝ] A) (N : ℕ) :
    φ (eulerDeletionDevelopment q s L N) =
      eulerDeletionDevelopment q s (φ.toContinuousLinearMap.comp L) N := by
  change φ.toAlgHom.toMonoidHom (orderedProduct _ N) = _
  rw [orderedProduct_map]
  unfold eulerDeletionDevelopment
  congr 1
  funext n
  change φ (NormedSpace.exp _) = _
  rw [NormedSpace.map_exp φ φ.continuous, map_smul]
  rfl

theorem map_eulerDeletionDevelopmentLimit (φ : A →A[ℝ] B) (q : ℕ)
    (s : {z : ℂ // 0 < z.re}) (L : ℂ →L[ℝ] A) :
    φ (eulerDeletionDevelopmentLimit q s L) =
      eulerDeletionDevelopmentLimit q s (φ.toContinuousLinearMap.comp L) := by
  apply tendsto_nhds_unique _ (tendsto_eulerDeletionDevelopment q s _)
  have h := (φ.continuous.tendsto _).comp (tendsto_eulerDeletionDevelopment q s L)
  simpa only [Function.comp_def, map_eulerDeletionDevelopment] using h

end Limit
end RHTower
