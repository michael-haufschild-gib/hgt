import GaloisForLFunctions.HTGeometry.SimpleClockRankOneAlgebraSaturation
import GaloisForLFunctions.RHTower.GammaJacobiTailConnectionTransgression
import GaloisForLFunctions.RHTower.VonMangoldtWeightedMarginalBoundaryAnomaly

/-!
# Gamma--Jacobi Euler-tail cyclic-reader no-go

The completed Euler clock has distinct labels on every finite prime packet.  Every Gamma--Jacobi
Szegő aperture loss is rank one, and its boundary vector is nonzero at every prime.  These two
source objects therefore generate the full finite matrix algebra.  Infinite Krein signature cannot
create a proper finite cyclic anomaly algebra around them.

The canonical von Mangoldt Toeplitz counterreader illustrates the forced alternative: its first
off-diagonal coefficient is strictly negative, hence it is not cyclic against even the two-jet
degree clock.  That noncyclic boundary coefficient is exactly what absorbs positive opening flux.
-/

namespace RHTower

open GaloisForLFunctions

noncomputable section

/-- Completed Euler logarithmic clock on a finite prime packet. -/
def gammaJacobiPrimeEulerClock
    {I : Type*} [Fintype I] [DecidableEq I]
    (prime : I → Nat.Primes) : Matrix I I ℝ :=
  Matrix.diagonal (fun i => Real.log (prime i : ℝ))

/-- Rank-one `SR-47` aperture-loss matrix on a finite prime packet. -/
def gammaJacobiPrimeTailApertureLoss
    {I : Type*} [Fintype I]
    (prime : I → Nat.Primes) (K : ℕ) : Matrix I I ℝ :=
  fun i j =>
    gammaOddJacobiTailBoundaryReadout K (Real.log (prime i : ℝ)) *
      gammaOddJacobiTailBoundaryReadout K (Real.log (prime j : ℝ))

theorem gammaJacobiPrimeTailApertureLoss_eq_hardyTail_sub_succ
    {I : Type*} [Fintype I]
    (prime : I → Nat.Primes) (K : ℕ) (i j : I) :
    gammaJacobiPrimeTailApertureLoss prime K i j =
      gammaOddJacobiHardyTailKernel K
          (Real.log (prime i : ℝ)) (Real.log (prime j : ℝ)) -
        gammaOddJacobiHardyTailKernel (K + 1)
          (Real.log (prime i : ℝ)) (Real.log (prime j : ℝ)) := by
  have hi : 0 < Real.log (prime i : ℝ) :=
    Real.log_pos (by exact_mod_cast (prime i).prop.one_lt)
  have hj : 0 < Real.log (prime j : ℝ) :=
    Real.log_pos (by exact_mod_cast (prime j).prop.one_lt)
  rw [gammaOddJacobiHardyTailKernel_sub_succ K hi hj]
  rfl

theorem gammaJacobiPrimeEulerLabel_injective
    {I : Type*} (prime : I → Nat.Primes) (hprime : Function.Injective prime) :
    Function.Injective (fun i => Real.log (prime i : ℝ)) := by
  intro i j hij
  have hexp := congrArg Real.exp hij
  rw [Real.exp_log (by exact_mod_cast (prime i).prop.pos : (0 : ℝ) < (prime i : ℝ)),
    Real.exp_log (by exact_mod_cast (prime j).prop.pos : (0 : ℝ) < (prime j : ℝ))] at hexp
  apply hprime
  apply Subtype.ext
  exact_mod_cast hexp

theorem gammaOddJacobiTailBoundaryReadout_prime_ne_zero
    (p : Nat.Primes) (K : ℕ) :
    gammaOddJacobiTailBoundaryReadout K (Real.log (p : ℝ)) ≠ 0 := by
  have hpLog : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.prop.one_lt)
  rw [gammaOddJacobiTailBoundaryReadout_eq K hpLog]
  exact pow_ne_zero _ (tanh_pos_of_pos hpLog).ne'

/-- **Route M finite algebra saturation.**  On every injectively labelled finite prime packet,
completed Euler multiplication and one exact Gamma--Jacobi tail transgression generate every
matrix.  The conclusion is independent of any Hilbert or Krein metric. -/
theorem gammaJacobiTail_euler_generatedSubalgebra_eq_top
    {I : Type*} [Fintype I] [DecidableEq I]
    (prime : I → Nat.Primes) (hprime : Function.Injective prime) (K : ℕ) :
    Algebra.adjoin ℝ
        {gammaJacobiPrimeEulerClock prime,
          gammaJacobiPrimeTailApertureLoss prime K} = ⊤ := by
  simpa only [gammaJacobiPrimeEulerClock, gammaJacobiPrimeTailApertureLoss] using
    GaloisForLFunctions.HTGeometry.simpleClock_rankOne_generatedSubalgebra_eq_top
      (fun i => Real.log (prime i : ℝ))
      (fun i => gammaOddJacobiTailBoundaryReadout K (Real.log (prime i : ℝ)))
      (gammaJacobiPrimeEulerLabel_injective prime hprime)
      (fun i => gammaOddJacobiTailBoundaryReadout_prime_ne_zero (prime i) K)

/-- First off-diagonal coefficient of every nonempty finite-aperture canonical counterreader is
strictly negative. -/
theorem finiteVonMangoldtHankelToeplitzCounterweight_one_neg
    (M : ℕ) (hM : 0 < M) :
    HTGeometry.hankelToeplitzCounterweight
        (finiteVonMangoldtSuccessorRelativeMoment M) 1 < 0 := by
  rw [HTGeometry.hankelToeplitzCounterweight_succ]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, mul_zero, add_zero]
  have h3 := finiteVonMangoldtSuccessorRelativeMoment_pos M 3 hM (by omega)
  have h4 := finiteVonMangoldtSuccessorRelativeMoment_pos M 4 hM (by omega)
  exact div_neg_of_neg_of_pos (neg_neg_of_pos h4) (mul_pos (by norm_num) h3)

/-- The cofinal source counterreader retains the same strict first off-diagonal anomaly. -/
theorem vonMangoldtHankelToeplitzCounterweight_one_neg :
    HTGeometry.hankelToeplitzCounterweight
        vonMangoldtSuccessorRelativeMoment 1 < 0 := by
  rw [HTGeometry.hankelToeplitzCounterweight_succ]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, mul_zero, add_zero]
  have h3 := vonMangoldtSuccessorRelativeMoment_pos 3 (by omega)
  have h4 := vonMangoldtSuccessorRelativeMoment_pos 4 (by omega)
  exact div_neg_of_neg_of_pos (neg_neg_of_pos h4) (mul_pos (by norm_num) h3)

/-- The actual finite-aperture Toeplitz counterreader is not cyclic against the simple two-jet
degree clock.  Its nonzero boundary row is therefore an anomaly, not a hidden cyclic trace. -/
theorem finiteVonMangoldtCounterreader_not_clockCyclic
    (M : ℕ) (hM : 0 < M) :
    ¬ HTGeometry.MatrixDensityClockCyclic
        (finiteVonMangoldtJetDensity
          (finiteVonMangoldtHankelToeplitzCounterDensity M) 2)
        (fun i : Fin 2 => (i : ℝ)) := by
  intro hcyc
  have hclock : Function.Injective (fun i : Fin 2 => (i : ℝ)) := by
    intro i j hij
    apply Fin.ext
    change ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) at hij
    exact_mod_cast hij
  have hzero := HTGeometry.matrixDensityClockCyclic_offDiagonal_eq_zero
    _ _ hclock hcyc (show (0 : Fin 2) ≠ 1 by decide)
  have hneg := finiteVonMangoldtHankelToeplitzCounterweight_one_neg M hM
  have hdensity :
      finiteVonMangoldtJetDensity
          (finiteVonMangoldtHankelToeplitzCounterDensity M) 2 0 1 =
        HTGeometry.hankelToeplitzCounterweight
          (finiteVonMangoldtSuccessorRelativeMoment M) 1 := by
    simp [finiteVonMangoldtJetDensity,
      finiteVonMangoldtHankelToeplitzCounterDensity,
      HTGeometry.hankelToeplitzCounterDensity]
  rw [hdensity] at hzero
  linarith

/-- The cofinal Toeplitz counterreader is likewise noncyclic already on its first two jet
coordinates. -/
theorem vonMangoldtCounterreader_not_clockCyclic :
    ¬ HTGeometry.MatrixDensityClockCyclic
        (finiteVonMangoldtJetDensity
          vonMangoldtHankelToeplitzCounterDensity 2)
        (fun i : Fin 2 => (i : ℝ)) := by
  intro hcyc
  have hclock : Function.Injective (fun i : Fin 2 => (i : ℝ)) := by
    intro i j hij
    apply Fin.ext
    change ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) at hij
    exact_mod_cast hij
  have hzero := HTGeometry.matrixDensityClockCyclic_offDiagonal_eq_zero
    _ _ hclock hcyc (show (0 : Fin 2) ≠ 1 by decide)
  have hneg := vonMangoldtHankelToeplitzCounterweight_one_neg
  have hdensity :
      finiteVonMangoldtJetDensity vonMangoldtHankelToeplitzCounterDensity 2 0 1 =
        HTGeometry.hankelToeplitzCounterweight
          vonMangoldtSuccessorRelativeMoment 1 := by
    simp [finiteVonMangoldtJetDensity, vonMangoldtHankelToeplitzCounterDensity,
      HTGeometry.hankelToeplitzCounterDensity]
  rw [hdensity] at hzero
  linarith

end

end RHTower
