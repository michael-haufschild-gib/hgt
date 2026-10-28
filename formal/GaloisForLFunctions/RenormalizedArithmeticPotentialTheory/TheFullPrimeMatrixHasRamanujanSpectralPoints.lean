import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheRamanujanPoleProfilesArePrimeQuasimodes
import GaloisForLFunctions.HTGeometry.HermitianResidualFindsAnEigenvalue
import GaloisForLFunctions.ArithmeticIntersectionTheory.TheTorsionFormHasPolynomiallyManyPositiveSquares

/-!
# Actual spectral points of the full prime matrix

The literal prime kernel on every integer in the horizon is a real Hermitian
matrix. Ramanujan quasimodes have logarithmic squared norm and negligible
residual, forcing eigenvalues near their arithmetic trial energies.
-/

noncomputable section

open Filter Topology Finset

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticIntersectionTheory ArithmeticEffectivityTheory

/-- Every positive integer up to the actual horizon, with no sieve restriction. -/
abbrev PrimeHorizonIndex (N : ℕ) := ↥(Icc 1 N)

/-- The literal finite prime matrix on the full integer horizon. -/
def fullPrimeMatrix (N : ℕ) : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ :=
  fun n j => weilPrimeKernel n j

theorem fullPrimeMatrix_isHermitian (N : ℕ) : (fullPrimeMatrix N).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro n j
  exact weilPrimeKernel_symm j n

/-- The actual finite Ramanujan vector in Euclidean coordinates. -/
def ramanujanHorizonVector (m N : ℕ) : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  WithLp.toLp 2 (fun n => ramanujanPoleProfile m n)

theorem ramanujanHorizonVector_norm_sq (m N : ℕ) :
    ‖ramanujanHorizonVector m N‖ ^ 2 =
      ∑ n ∈ Icc 1 N, ramanujanPoleProfile m n ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  exact Finset.sum_coe_sort (Icc 1 N) (fun n => ramanujanPoleProfile m n ^ 2)

theorem fullPrimeMatrix_apply_ramanujanHorizonVector (m N : ℕ) (n : PrimeHorizonIndex N) :
    (Matrix.toEuclideanLin (fullPrimeMatrix N) (ramanujanHorizonVector m N)) n =
      ∑ j ∈ Icc 1 N, weilPrimeKernel n j * ramanujanPoleProfile m j := by
  change (∑ j : PrimeHorizonIndex N, weilPrimeKernel n j * ramanujanPoleProfile m j) = _
  exact Finset.sum_coe_sort (Icc 1 N) (fun j => weilPrimeKernel n j * ramanujanPoleProfile m j)

/-- The Euclidean residual is exactly the row residual summed over the integer horizon. -/
theorem ramanujanHorizonVector_residual_norm_sq (m N : ℕ) :
    ‖Matrix.toEuclideanLin (fullPrimeMatrix N) (ramanujanHorizonVector m N) -
      (Real.log N - ramanujanAdjunctionEnergy m) • ramanujanHorizonVector m N‖ ^ 2 =
      ∑ n ∈ Icc 1 N,
        ((∑ j ∈ Icc 1 N, weilPrimeKernel n j * ramanujanPoleProfile m j) -
          (Real.log N - ramanujanAdjunctionEnergy m) * ramanujanPoleProfile m n) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  trans ∑ n : PrimeHorizonIndex N,
    ((∑ j ∈ Icc 1 N, weilPrimeKernel n j * ramanujanPoleProfile m j) -
      (Real.log N - ramanujanAdjunctionEnergy m) * ramanujanPoleProfile m n) ^ 2
  · apply sum_congr rfl
    intro n _
    change ((Matrix.toEuclideanLin (fullPrimeMatrix N) (ramanujanHorizonVector m N)) n -
      (Real.log N - ramanujanAdjunctionEnergy m) * ramanujanPoleProfile m n) ^ 2 = _
    rw [fullPrimeMatrix_apply_ramanujanHorizonVector]
  · exact Finset.sum_coe_sort (Icc 1 N) (fun n =>
      ((∑ j ∈ Icc 1 N, weilPrimeKernel n j * ramanujanPoleProfile m j) -
        (Real.log N - ramanujanAdjunctionEnergy m) * ramanujanPoleProfile m n) ^ 2)

theorem tendsto_ramanujanHorizonVector_norm_sq {m : ℕ} (hm : 0 < m) :
    Tendsto (fun N : ℕ => ‖ramanujanHorizonVector m N‖ ^ 2 / Real.log N) atTop (𝓝 1) := by
  simpa only [ramanujanHorizonVector_norm_sq] using tendsto_ramanujanPoleProfile_sq hm

theorem tendsto_ramanujanHorizonVector_residual_norm_sq {m : ℕ} (hm : 0 < m) :
    Tendsto (fun N : ℕ =>
      ‖Matrix.toEuclideanLin (fullPrimeMatrix N) (ramanujanHorizonVector m N) -
        (Real.log N - ramanujanAdjunctionEnergy m) • ramanujanHorizonVector m N‖ ^ 2 /
          Real.log N) atTop (𝓝 0) := by
  simpa only [ramanujanHorizonVector_residual_norm_sq] using tendsto_ramanujanPoleProfile_residual_sq hm

/-- Every fixed arithmetic energy is approached by actual eigenvalues of the
literal full prime matrix, after subtracting the common logarithmic divergence. -/
theorem eventually_fullPrimeMatrix_eigenvalue_near {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∃ i : PrimeHorizonIndex N,
      |(fullPrimeMatrix_isHermitian N).eigenvalues i -
        (Real.log N - ramanujanAdjunctionEnergy m)| < ε := by
  have hres := tendsto_ramanujanHorizonVector_residual_norm_sq hm
  have hnorm := (tendsto_ramanujanHorizonVector_norm_sq hm).const_mul (ε ^ 2)
  have hlt := hres.eventually_lt hnorm (by simpa only [mul_one] using pow_pos hε 2)
  filter_upwards [hlt, eventually_ge_atTop 2] with N hN hN2
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hstrict :
      ‖Matrix.toEuclideanLin (fullPrimeMatrix N) (ramanujanHorizonVector m N) -
        (Real.log N - ramanujanAdjunctionEnergy m) • ramanujanHorizonVector m N‖ ^ 2 <
      ε ^ 2 * ‖ramanujanHorizonVector m N‖ ^ 2 := by
    rw [← mul_div_assoc] at hN
    exact (div_lt_div_iff_of_pos_right hlog).mp hN
  exact HTGeometry.exists_eigenvalue_abs_sub_lt_of_residual_sq_lt
    (fullPrimeMatrix_isHermitian N) (ramanujanHorizonVector m N)
    (Real.log N - ramanujanAdjunctionEnergy m) hε.le hstrict

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

