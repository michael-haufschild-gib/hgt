import GaloisForLFunctions.RHTower.Suzuki.SuzukiNonabelianCartanWardCompletion
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCauchyReporterSecantTransitionCoreEscape
import GaloisForLFunctions.HTGeometry.ZetaVerticalAlmostPeriodic

/-!
# Growing-rank Cartan fission of the Suzuki transition core

The fixed-rank Suzuki completion cannot absorb the divergent positive reporter-secant transition
core.  This file implements the surviving non-scalar alternative: every retained ordered prime
pair gets its own determinant-one rank-two Stokes block.  The cell variable is half the literal
Cauchy pair term, so the total linear Cartan mass is exactly the transition-core energy and retains
both source labels and their coefficients.

The quadratic counterterm cancels the second Taylor grade of the block log.  The remaining cubic
mass is uniformly bounded because each cell is at most the product of its two critical Mellin
weights and the cubes of those weights are summable.  Thus the completed growing-rank observable
differs from the divergent transition core by a uniformly bounded nonnegative error while itself
still diverging.  This is not a bounded scalar correction and therefore lies outside the
fixed-scale no-go.

What is not proved here is the remaining arithmetic admission theorem: this growing-rank signed
carrier must still descend through the completed Gamma/polar rectangular source law with a
uniformly lower-semibounded selected residual.
-/

open Complex
open scoped BigOperators

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Cubes of the critical Mellin prime weights are summable. -/
theorem summable_criticalMellinAtomWeight_cube :
    Summable (fun n : ℕ => _root_.RHTower.criticalMellinAtomWeight n ^ 3) := by
  have hmajor := HTGeometry.summable_log_pow_div_nat_rpow 3
    (sigma := (3 / 2 : ℝ)) (by norm_num)
  refine Summable.of_nonneg_of_le
    (fun n => pow_nonneg (_root_.RHTower.criticalMellinAtomWeight_nonneg' n) 3)
    (fun n => ?_) hmajor
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [_root_.RHTower.criticalMellinAtomWeight]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hvm := ArithmeticFunction.vonMangoldt_le_log (n := n)
  have hvm0 : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
    ArithmeticFunction.vonMangoldt_nonneg
  have hlog0 : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn)
  rw [criticalMellinAtomWeight_eq_vonMangoldt_div_sqrt]
  calc
    ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) ^ 3 ≤
        (Real.log n / Real.sqrt n) ^ 3 :=
      pow_le_pow_left₀ (div_nonneg hvm0 hsqrt.le)
        (div_le_div_of_nonneg_right hvm hsqrt.le) 3
    _ = Real.log n ^ 3 / (n : ℝ) ^ (3 / 2 : ℝ) := by
      rw [div_pow]
      congr 1
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast,
        ← Real.rpow_mul (Nat.cast_nonneg n)]
      norm_num

/-- Ordered prime pairs in the positive reporter-secant transition sector. -/
noncomputable def suzukiTransitionCorePairSet (N : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (suzukiNaturalAperturePairSet N).filter
    (fun ij => ¬ suzukiNaturalApertureTransitionSeparated N ij)

/-- Half of the literal source-labelled reporter-secant pair term. -/
def suzukiTransitionCoreCartanCell (N : ℕ) (ij : ℕ × ℕ) : ℝ :=
  suzukiNaturalApertureCauchyPairTerm N ij / 2

/-- Stokes amplitude whose squared norm is one transition Cartan cell. -/
def suzukiTransitionCoreStokesAmplitude (N : ℕ) (ij : ℕ × ℕ) : ℂ :=
  (Real.sqrt (suzukiTransitionCoreCartanCell N ij) : ℂ)

/-- Independent determinant-one rank-two block attached to an ordered source pair. -/
def suzukiTransitionCoreStokesFissionCell (N : ℕ) (ij : ℕ × ℕ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  suzukiRankTwoStokesFissionCell
    (suzukiTransitionCoreStokesAmplitude N ij)

@[simp] theorem det_suzukiTransitionCoreStokesFissionCell
    (N : ℕ) (ij : ℕ × ℕ) :
    (suzukiTransitionCoreStokesFissionCell N ij).det = 1 := by
  exact det_suzukiRankTwoStokesFissionCell _

/-- Uniform two bound for the reporter-secant Cauchy Gram factor. -/
theorem suzukiReporterSecantCauchyGram_le_two (p q : NNReal) :
    suzukiReporterSecantCauchyGram p q ≤ 2 := by
  have hnonneg (x : ℝ) : 0 ≤ cauchyHalfExponentialKernel x := by
    exact (Real.exp_pos _).le
  have hle (x : ℝ) : cauchyHalfExponentialKernel x ≤ 1 := by
    rw [cauchyHalfExponentialKernel]
    exact Real.exp_le_one_iff.mpr (by linarith [abs_nonneg x])
  rw [suzukiReporterSecantCauchyGram]
  linarith [hnonneg ((p : ℝ) - 2 * q),
    hnonneg (2 * (p : ℝ) - q), hle ((p : ℝ) - q),
    hle (2 * (p : ℝ) - 2 * q)]

theorem suzukiTransitionCoreCartanCell_nonneg
    {N : ℕ} {ij : ℕ × ℕ}
    (hij : ij ∈ suzukiTransitionCorePairSet N) :
    0 ≤ suzukiTransitionCoreCartanCell N ij := by
  classical
  rw [suzukiTransitionCorePairSet, Finset.mem_filter] at hij
  have hwi : 0 ≤ (suzukiNaturalAperturePrimeWeight N ij.1 : ℝ) :=
    (suzukiNaturalAperturePrimeWeight N ij.1).property
  have hwj : 0 ≤ (suzukiNaturalAperturePrimeWeight N ij.2 : ℝ) :=
    (suzukiNaturalAperturePrimeWeight N ij.2).property
  have hgram :=
    suzukiReporterSecantCauchyGram_pos_of_not_transitionSeparated hij.2
  rw [suzukiTransitionCoreCartanCell,
    suzukiNaturalApertureCauchyPairTerm]
  positivity

theorem suzukiTransitionCoreCartanCell_le_weightProduct
    {N : ℕ} {ij : ℕ × ℕ}
    (_hij : ij ∈ suzukiTransitionCorePairSet N) :
    suzukiTransitionCoreCartanCell N ij ≤
      (suzukiNaturalAperturePrimeWeight N ij.1 : ℝ) *
        (suzukiNaturalAperturePrimeWeight N ij.2 : ℝ) := by
  have hwi : 0 ≤ (suzukiNaturalAperturePrimeWeight N ij.1 : ℝ) :=
    (suzukiNaturalAperturePrimeWeight N ij.1).property
  have hwj : 0 ≤ (suzukiNaturalAperturePrimeWeight N ij.2 : ℝ) :=
    (suzukiNaturalAperturePrimeWeight N ij.2).property
  have hgram := suzukiReporterSecantCauchyGram_le_two
    (suzukiNaturalApertureLag N ij.1)
    (suzukiNaturalApertureLag N ij.2)
  rw [suzukiTransitionCoreCartanCell,
    suzukiNaturalApertureCauchyPairTerm, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  calc
    (suzukiNaturalAperturePrimeWeight N ij.1 : ℝ) *
          suzukiReporterSecantCauchyGram
            (suzukiNaturalApertureLag N ij.1)
            (suzukiNaturalApertureLag N ij.2) *
        (suzukiNaturalAperturePrimeWeight N ij.2 : ℝ) ≤
      (suzukiNaturalAperturePrimeWeight N ij.1 : ℝ) * 2 *
        (suzukiNaturalAperturePrimeWeight N ij.2 : ℝ) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hgram hwi) hwj
    _ = 2 * ((suzukiNaturalAperturePrimeWeight N ij.1 : ℝ) *
        (suzukiNaturalAperturePrimeWeight N ij.2 : ℝ)) := by ring
    _ = (suzukiNaturalAperturePrimeWeight N ij.1 : ℝ) *
        (suzukiNaturalAperturePrimeWeight N ij.2 : ℝ) * 2 := by ring

/-- The visible diagonal of each block is exactly one plus its literal Cartan cell. -/
theorem suzukiTransitionCoreStokesFissionCell_zero_zero
    {N : ℕ} {ij : ℕ × ℕ}
    (hij : ij ∈ suzukiTransitionCorePairSet N) :
    suzukiTransitionCoreStokesFissionCell N ij 0 0 =
      ((1 + suzukiTransitionCoreCartanCell N ij : ℝ) : ℂ) := by
  classical
  rw [suzukiTransitionCoreStokesFissionCell,
    suzukiRankTwoStokesFissionCell_zero_zero,
    suzukiTransitionCoreStokesAmplitude]
  have hx := suzukiTransitionCoreCartanCell_nonneg hij
  push_cast
  simp
  exact_mod_cast (by simpa [pow_two] using Real.sq_sqrt hx)

def suzukiTransitionCoreStokesLinearMass (N : ℕ) : ℝ :=
  ∑ ij ∈ suzukiTransitionCorePairSet N,
    suzukiTransitionCoreCartanCell N ij

def suzukiTransitionCoreStokesLogMass (N : ℕ) : ℝ :=
  ∑ ij ∈ suzukiTransitionCorePairSet N,
    Real.log (1 + suzukiTransitionCoreCartanCell N ij)

def suzukiTransitionCoreStokesQuadraticCounterterm (N : ℕ) : ℝ :=
  ∑ ij ∈ suzukiTransitionCorePairSet N,
    suzukiTransitionCoreCartanCell N ij ^ 2

def suzukiTransitionCoreStokesCubicRemainderMass (N : ℕ) : ℝ :=
  ∑ ij ∈ suzukiTransitionCorePairSet N,
    suzukiStokesCartanCubicRemainder
      (suzukiTransitionCoreCartanCell N ij)

/-- Coefficient-faithful conservation: twice the fissioned linear mass is the literal core. -/
theorem suzukiTransitionCoreStokesLinearMass_two_mul_eq (N : ℕ) :
    2 * suzukiTransitionCoreStokesLinearMass N =
      suzukiNaturalApertureTransitionCoreCauchyEnergy N := by
  classical
  rw [suzukiTransitionCoreStokesLinearMass,
    suzukiNaturalApertureTransitionCoreCauchyEnergy,
    suzukiTransitionCorePairSet, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [suzukiTransitionCoreCartanCell]
  ring

/-- Exact third-order Taylor decomposition of the fissioned Cartan log. -/
theorem suzukiTransitionCoreStokesLogMass_eq (N : ℕ) :
    suzukiTransitionCoreStokesLogMass N =
      suzukiTransitionCoreStokesLinearMass N -
        suzukiTransitionCoreStokesQuadraticCounterterm N / 2 +
          suzukiTransitionCoreStokesCubicRemainderMass N := by
  simp only [suzukiTransitionCoreStokesLogMass,
    suzukiTransitionCoreStokesLinearMass,
    suzukiTransitionCoreStokesQuadraticCounterterm,
    suzukiTransitionCoreStokesCubicRemainderMass,
    suzukiStokesCartanCubicRemainder, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, Finset.sum_div]
  ring

/-- Nonlinear growing-rank observable after the exact quadratic counterterm. -/
def suzukiTransitionCoreCompletedStokesFissionObservable (N : ℕ) : ℝ :=
  2 * suzukiTransitionCoreStokesLogMass N +
    suzukiTransitionCoreStokesQuadraticCounterterm N

/-- The completed observable is the exact transition core plus twice the cubic remainder. -/
theorem suzukiTransitionCoreCompletedStokesFissionObservable_eq (N : ℕ) :
    suzukiTransitionCoreCompletedStokesFissionObservable N =
      suzukiNaturalApertureTransitionCoreCauchyEnergy N +
        2 * suzukiTransitionCoreStokesCubicRemainderMass N := by
  rw [suzukiTransitionCoreCompletedStokesFissionObservable,
    suzukiTransitionCoreStokesLogMass_eq,
    ← suzukiTransitionCoreStokesLinearMass_two_mul_eq]
  ring

theorem suzukiTransitionCoreStokesCubicRemainderMass_nonneg (N : ℕ) :
    0 ≤ suzukiTransitionCoreStokesCubicRemainderMass N := by
  rw [suzukiTransitionCoreStokesCubicRemainderMass]
  exact Finset.sum_nonneg fun ij hij =>
    suzukiStokesCartanCubicRemainder_nonneg
      (suzukiTransitionCoreCartanCell_nonneg hij)

/-- Finite-cutoff cubic mass is controlled by the square of the prime-weight cube sum. -/
theorem suzukiTransitionCoreStokesCubicRemainderMass_le_partialCube (N : ℕ) :
    suzukiTransitionCoreStokesCubicRemainderMass N ≤
      (∑ n ∈ Finset.Icc 2 N,
        _root_.RHTower.criticalMellinAtomWeight n ^ 3) ^ 2 / 3 := by
  classical
  calc
    suzukiTransitionCoreStokesCubicRemainderMass N ≤
        ∑ ij ∈ suzukiTransitionCorePairSet N,
          suzukiTransitionCoreCartanCell N ij ^ 3 / 3 := by
      rw [suzukiTransitionCoreStokesCubicRemainderMass]
      exact Finset.sum_le_sum fun ij hij =>
        suzukiStokesCartanCubicRemainder_le
          (suzukiTransitionCoreCartanCell_nonneg hij)
    _ ≤ ∑ ij ∈ suzukiTransitionCorePairSet N,
          ((suzukiNaturalAperturePrimeWeight N ij.1 : ℝ) *
            (suzukiNaturalAperturePrimeWeight N ij.2 : ℝ)) ^ 3 / 3 := by
      exact Finset.sum_le_sum fun ij hij =>
        div_le_div_of_nonneg_right
          (pow_le_pow_left₀ (suzukiTransitionCoreCartanCell_nonneg hij)
            (suzukiTransitionCoreCartanCell_le_weightProduct hij) 3)
          (by norm_num)
    _ ≤ ∑ ij ∈ suzukiNaturalAperturePairSet N,
          ((suzukiNaturalAperturePrimeWeight N ij.1 : ℝ) *
            (suzukiNaturalAperturePrimeWeight N ij.2 : ℝ)) ^ 3 / 3 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro ij hij
        rw [suzukiTransitionCorePairSet] at hij
        exact (Finset.mem_filter.mp hij).1
      · intro ij _hij _hnot
        positivity
    _ = (∑ n ∈ Finset.Icc 2 N,
          _root_.RHTower.criticalMellinAtomWeight n ^ 3) ^ 2 / 3 := by
      rw [suzukiNaturalAperturePairSet, Finset.sum_product]
      change (∑ x ∈ Finset.Icc 2 N, ∑ y ∈ Finset.Icc 2 N,
        (_root_.RHTower.criticalMellinAtomWeight x *
          _root_.RHTower.criticalMellinAtomWeight y) ^ 3 / 3) = _
      simp only [mul_pow]
      calc
        (∑ x ∈ Finset.Icc 2 N, ∑ y ∈ Finset.Icc 2 N,
            _root_.RHTower.criticalMellinAtomWeight x ^ 3 *
              _root_.RHTower.criticalMellinAtomWeight y ^ 3 / 3) =
            ∑ x ∈ Finset.Icc 2 N,
              (_root_.RHTower.criticalMellinAtomWeight x ^ 3 / 3) *
                ∑ y ∈ Finset.Icc 2 N,
                  _root_.RHTower.criticalMellinAtomWeight y ^ 3 := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y hy
          ring
        _ = _ := by
          simp only [div_eq_mul_inv, ← Finset.sum_mul]
          ring

/-- Cubic nonlinear error is bounded independently of source cutoff. -/
theorem exists_uniform_bound_suzukiTransitionCoreStokesCubicRemainderMass :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      suzukiTransitionCoreStokesCubicRemainderMass N ≤ C := by
  let S : ℝ := ∑' n : ℕ, _root_.RHTower.criticalMellinAtomWeight n ^ 3
  refine ⟨S ^ 2 / 3 + 1, by nlinarith [sq_nonneg S], fun N => ?_⟩
  have hpartial :
      (∑ n ∈ Finset.Icc 2 N,
        _root_.RHTower.criticalMellinAtomWeight n ^ 3) ≤ S := by
    exact summable_criticalMellinAtomWeight_cube.sum_le_tsum
      (Finset.Icc 2 N) (fun n _hn =>
        pow_nonneg (_root_.RHTower.criticalMellinAtomWeight_nonneg' n) 3)
  have hpartial0 : 0 ≤ ∑ n ∈ Finset.Icc 2 N,
      _root_.RHTower.criticalMellinAtomWeight n ^ 3 := by
    exact Finset.sum_nonneg fun n _hn =>
      pow_nonneg (_root_.RHTower.criticalMellinAtomWeight_nonneg' n) 3
  calc
    suzukiTransitionCoreStokesCubicRemainderMass N ≤
        (∑ n ∈ Finset.Icc 2 N,
          _root_.RHTower.criticalMellinAtomWeight n ^ 3) ^ 2 / 3 :=
      suzukiTransitionCoreStokesCubicRemainderMass_le_partialCube N
    _ ≤ S ^ 2 / 3 := by
      exact div_le_div_of_nonneg_right
        (pow_le_pow_left₀ hpartial0 hpartial 2) (by norm_num)
    _ ≤ S ^ 2 / 3 + 1 := by linarith

/-- The completed nonlinear carrier stays within a uniform distance of the literal transition
core. -/
theorem exists_uniform_bound_abs_suzukiTransitionCoreCompletedStokesFissionObservable_sub_core :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      |suzukiTransitionCoreCompletedStokesFissionObservable N -
        suzukiNaturalApertureTransitionCoreCauchyEnergy N| ≤ C := by
  rcases exists_uniform_bound_suzukiTransitionCoreStokesCubicRemainderMass with
    ⟨C, hC, hbound⟩
  refine ⟨2 * C, by positivity, fun N => ?_⟩
  have hid :
      suzukiTransitionCoreCompletedStokesFissionObservable N -
          suzukiNaturalApertureTransitionCoreCauchyEnergy N =
        2 * suzukiTransitionCoreStokesCubicRemainderMass N := by
    rw [suzukiTransitionCoreCompletedStokesFissionObservable_eq]
    ring
  rw [hid, abs_of_nonneg (mul_nonneg (by norm_num)
    (suzukiTransitionCoreStokesCubicRemainderMass_nonneg N))]
  nlinarith [hbound N]

theorem suzukiNaturalApertureTransitionCoreCauchyEnergy_le_completedStokesFissionObservable
    (N : ℕ) :
    suzukiNaturalApertureTransitionCoreCauchyEnergy N ≤
      suzukiTransitionCoreCompletedStokesFissionObservable N := by
  rw [suzukiTransitionCoreCompletedStokesFissionObservable_eq]
  nlinarith [suzukiTransitionCoreStokesCubicRemainderMass_nonneg N]

/-- Growing-rank fission does not disguise the forbidden core as a bounded scalar correction: its
completed observable retains the same cofinal escape. -/
theorem tendsto_suzukiTransitionCoreCompletedStokesFissionObservable_eight_mul_atTop :
    Filter.Tendsto (fun n : ℕ =>
      suzukiTransitionCoreCompletedStokesFissionObservable (8 * n))
      Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop]
  intro B
  filter_upwards [
    tendsto_suzukiNaturalApertureTransitionCoreCauchyEnergy_eight_mul_atTop.eventually_ge_atTop B]
    with n hn
  exact hn.trans
    (suzukiNaturalApertureTransitionCoreCauchyEnergy_le_completedStokesFissionObservable
      (8 * n))

end

end GaloisForLFunctions.RHTower
