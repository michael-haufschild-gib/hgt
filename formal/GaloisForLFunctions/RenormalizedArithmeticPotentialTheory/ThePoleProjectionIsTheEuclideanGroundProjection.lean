import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.HorizonKernelEuclideanIdentities
import GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity.TheSelectiveGardingInequality

/-!
# The arithmetic pole projection is the Euclidean ground projection

The reciprocal-square-root pole has harmonic squared mass. Normalizing it
identifies the arithmetic pole subtraction with the orthogonal Euclidean
projection. Its norm contracts and its literal prime defect is unchanged.
-/

noncomputable section

open Finset
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open SelectiveMultiscaleArithmeticPositivity

/-- The reciprocal-square-root pole on the actual positive horizon. -/
def horizonPoleVector (N : ℕ) : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  horizonProfileVector (fun n => 1 / Real.sqrt n) N

/-- The pole normalized by its exact harmonic mass. -/
def normalizedHorizonPoleVector (N : ℕ) : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  (Real.sqrt (harmonicMass N))⁻¹ • horizonPoleVector N

/-- Orthogonal removal of the normalized pole direction. -/
def horizonPoleProjection {N : ℕ} (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  x - ⟪x, normalizedHorizonPoleVector N⟫ • normalizedHorizonPoleVector N

theorem horizonPoleVector_norm_sq (N : ℕ) : ‖horizonPoleVector N‖ ^ 2 = harmonicMass N := by
  rw [horizonPoleVector, horizonProfileVector_norm_sq, harmonicMass]
  refine sum_congr rfl fun n _ => ?_
  rw [div_pow, one_pow, Real.sq_sqrt (Nat.cast_nonneg n)]

theorem one_le_harmonicMass {N : ℕ} (hN : 1 ≤ N) : 1 ≤ harmonicMass N := by
  have h := single_le_sum (f := fun n : ℕ => 1 / (n : ℝ))
    (fun n _ => by positivity) (mem_Icc.mpr ⟨le_rfl, hN⟩ : 1 ∈ Icc 1 N)
  simpa only [Nat.cast_one, div_one, harmonicMass] using h

theorem normalizedHorizonPoleVector_norm {N : ℕ} (hN : 1 ≤ N) :
    ‖normalizedHorizonPoleVector N‖ = 1 := by
  have hH := harmonicMass_pos hN
  have hs : ‖normalizedHorizonPoleVector N‖ ^ 2 = 1 := by
    rw [normalizedHorizonPoleVector, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      inv_pow, Real.sq_sqrt hH.le, horizonPoleVector_norm_sq, inv_mul_cancel₀ hH.ne']
  nlinarith only [hs, norm_nonneg (normalizedHorizonPoleVector N)]

/-- The normalized pole coordinate is the arithmetic harmonic sum divided by its mass root. -/
theorem inner_normalizedHorizonPoleVector {N : ℕ}
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ⟪x, normalizedHorizonPoleVector N⟫ =
      SelectiveMultiscaleArithmeticPositivity.harmonicSum N (primeHorizonExtension x) / Real.sqrt (harmonicMass N) := by
  have hraw : ⟪x, horizonPoleVector N⟫ = SelectiveMultiscaleArithmeticPositivity.harmonicSum N (primeHorizonExtension x) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, SelectiveMultiscaleArithmeticPositivity.harmonicSum]
    change (∑ n : PrimeHorizonIndex N, (1 / Real.sqrt (n : ℕ)) * x n) = _
    rw [← sum_coe_sort (Icc 1 N) (fun n => primeHorizonExtension x n / Real.sqrt n)]
    exact sum_congr rfl fun n _ => by rw [primeHorizonExtension_coe]; ring
  rw [normalizedHorizonPoleVector, real_inner_smul_right, hraw]
  ring

/-- Arithmetic and Euclidean pole removal agree on every horizon coordinate. -/
theorem horizonPoleProjection_eq_profile {N : ℕ} (hN : 1 ≤ N)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    horizonPoleProjection x = horizonProfileVector (poleProj N (primeHorizonExtension x)) N := by
  have hH := harmonicMass_pos hN
  ext n
  change x n - ⟪x, normalizedHorizonPoleVector N⟫ *
      ((Real.sqrt (harmonicMass N))⁻¹ * (1 / Real.sqrt (n : ℕ))) =
    primeHorizonExtension x n - SelectiveMultiscaleArithmeticPositivity.harmonicSum N (primeHorizonExtension x) /
      harmonicMass N / Real.sqrt (n : ℕ)
  rw [inner_normalizedHorizonPoleVector, primeHorizonExtension_coe]
  congr 1
  calc
    _ = SelectiveMultiscaleArithmeticPositivity.harmonicSum N (primeHorizonExtension x) /
        (Real.sqrt (harmonicMass N) * Real.sqrt (harmonicMass N)) / Real.sqrt (n : ℕ) := by ring
    _ = _ := by rw [Real.mul_self_sqrt hH.le]

private theorem extension_profile_on_horizon (a : ℕ → ℝ) {N n : ℕ}
    (hn : n ∈ Icc 1 N) : primeHorizonExtension (horizonProfileVector a N) n = a n := by
  rw [primeHorizonExtension, dif_pos hn]
  rfl

/-- The projected vector lies on the literal harmonic hyperplane. -/
theorem harmonicSum_horizonPoleProjection {N : ℕ} (hN : 1 ≤ N)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    SelectiveMultiscaleArithmeticPositivity.harmonicSum N (primeHorizonExtension (horizonPoleProjection x)) = 0 := by
  rw [horizonPoleProjection_eq_profile hN]
  have heq : SelectiveMultiscaleArithmeticPositivity.harmonicSum N
      (primeHorizonExtension (horizonProfileVector (poleProj N (primeHorizonExtension x)) N)) =
      SelectiveMultiscaleArithmeticPositivity.harmonicSum N (poleProj N (primeHorizonExtension x)) := by
    unfold SelectiveMultiscaleArithmeticPositivity.harmonicSum
    exact sum_congr rfl fun n hn => by rw [extension_profile_on_horizon _ hn]
  rw [heq, harmonicSum_poleProj hN]

private theorem poleDefect_eq_of_on_horizon {N : ℕ} {x y : ℕ → ℝ}
    (hxy : ∀ n ∈ Icc 1 N, x n = y n) : poleDefect N x = poleDefect N y := by
  unfold poleDefect
  refine sum_congr rfl fun m hm => sum_congr rfl fun t ht => ?_
  have hm1 := (mem_Icc.mp hm).1
  have ht1 := (mem_Icc.mp ht).1
  have hmt : m * t ∈ Icc 1 N := by
    refine mem_Icc.mpr ⟨Nat.mul_pos hm1 ht1, ?_⟩
    simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hm1).mp (mem_Icc.mp ht).2
  rw [hxy m hm, hxy (m * t) hmt]

/-- The exact prime defect ignores orthogonal subtraction of the pole. -/
theorem poleDefect_horizonPoleProjection {N : ℕ} (hN : 1 ≤ N)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    poleDefect N (primeHorizonExtension (horizonPoleProjection x)) =
      poleDefect N (primeHorizonExtension x) := by
  rw [horizonPoleProjection_eq_profile hN]
  calc
    _ = poleDefect N (poleProj N (primeHorizonExtension x)) :=
      poleDefect_eq_of_on_horizon (fun n hn => extension_profile_on_horizon _ hn)
    _ = _ := poleDefect_poleProj _ _

/-- Pole removal contracts the actual Euclidean squared norm. -/
theorem horizonPoleProjection_norm_sq_le {N : ℕ} (hN : 1 ≤ N)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ‖horizonPoleProjection x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  rw [horizonPoleProjection_eq_profile hN, horizonProfileVector_norm_sq,
    sum_sq_poleProj hN, sum_primeHorizonExtension_sq]
  exact sub_le_self _ (div_nonneg (sq_nonneg _) (harmonicMass_pos hN).le)

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
