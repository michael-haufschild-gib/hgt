import GaloisForLFunctions.RHTower.Suzuki.SuzukiWardAtomicContinuousLightWeld
import GaloisForLFunctions.RHTower.Suzuki.SuzukiValuationDepthLightCoercivity
import GaloisForLFunctions.RHTower.Suzuki.SuzukiNaturalApertureCauchyEnergyEscape
import GaloisForLFunctions.RHTower.CriticalPrimeSourceSchattenIdeal
import GaloisForLFunctions.RHTower.JordanFloorSymbolLaw
import GaloisForLFunctions.HTGeometry.ReflectedPrimeHistoryReserve
import GaloisForLFunctions.HTGeometry.Sl2ElementaryFactorization

/-!
# Suzuki nonabelian Cartan--Ward completion

The center-blind additive wall current misses half of every prime-power wall at height zero.
This file puts that missing negative-light energy into the Cartan coordinate of a literal
opposite-root `SL₂` Stokes pair.  One independent rank-two block is used for each finite source
label; this is the block-diagonal wild-fission carrier, not a product of all source factors in one
shared plane.

For aperture `A` and integer label `n`, the Cartan increment is

`x_A(n) = criticalMellinAtomWeight(n) * reporter(log A, log n) / 2`.

On prime powers it is exactly reporter-weighted Suzuki negative-light energy.  The Levi logarithm
has the forced expansion

`log(1+x) = x - x^(2 : ℕ)/2 + R_3(x)`,

where the total positive cubic remainder is uniformly bounded in `A`.  After adding the quadratic
counterterm and the literal regular-screw Gamma mass, the completed Cartan observable is exactly
Suzuki Green plus that uniformly bounded positive remainder.

No RH premise, Xi-zero data, fitted coefficient, or infinite source product is used.
-/

open Complex
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry
open _root_.RHTower

/-! ## Rank-two opposite-root Stokes cell -/

/-- Opposite-root rank-two Stokes pair. -/
def suzukiRankTwoStokesFissionCell (a : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  sl2UPlus a * sl2UMinus (star a)

/-- Every local fission cell lies in `SL₂`. -/
@[simp] theorem det_suzukiRankTwoStokesFissionCell (a : ℂ) :
    (suzukiRankTwoStokesFissionCell a).det = 1 := by
  rw [suzukiRankTwoStokesFissionCell, Matrix.det_mul, det_uPlus, det_uMinus, one_mul]

/-- The positive Levi coordinate created by opposite-root fusion is `1 + a a*`. -/
theorem suzukiRankTwoStokesFissionCell_zero_zero (a : ℂ) :
    suzukiRankTwoStokesFissionCell a 0 0 = 1 + a * star a := by
  rw [suzukiRankTwoStokesFissionCell, sl2UPlus, sl2UMinus, Matrix.mul_fin_two]
  simp

/-! ## Literal Suzuki center increment -/

/-- Reporter-weighted center negative-light energy, extended to all natural labels by von
Mangoldt's zero values off prime powers. -/
def suzukiCenterStokesCartanCell (A n : ℕ) : ℝ :=
  criticalMellinAtomWeight n *
      unitRieszSuzukiReporter (Real.log A) (Real.log n) / 2

/-- On a literal prime-power wall, the Cartan increment is exactly the forced negative-light
energy after Suzuki reporter dressing. -/
theorem suzukiCenterStokesCartanCell_primePower_eq_negativeLight
    (A : ℕ) (p : Nat.Primes) (e : ℕ) :
    suzukiCenterStokesCartanCell A (xiGammaEulerValuationNat (p, e)) =
      unitRieszSuzukiReporter (Real.log A)
          (Real.log (xiGammaEulerValuationNat (p, e))) *
        normSq (suzukiCriticalWallNegativeLightAmplitude 0 p e) := by
  have hnegative :
      normSq (suzukiCriticalWallNegativeLightAmplitude 0 p e) =
        criticalMellinAtomWeight (xiGammaEulerValuationNat (p, e)) / 2 := by
    rw [normSq_suzukiCriticalWallNegativeLightAmplitude_eq]
    rw [criticalMellinAtomWeight_eq_vonMangoldt_div_sqrt]
    simp
  rw [suzukiCenterStokesCartanCell, hnegative]
  ring

/-- The source amplitude used in the local Stokes pair. -/
def suzukiCenterStokesAmplitude (A n : ℕ) : ℂ :=
  (Real.sqrt (suzukiCenterStokesCartanCell A n) : ℂ)

theorem suzukiCenterStokesCartanCell_nonneg
    {A n : ℕ} (hA : 2 ≤ A) (hn : n ∈ Finset.Icc 2 A) :
    0 ≤ suzukiCenterStokesCartanCell A n := by
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two (Finset.mem_Icc.mp hn).1)
  have hApos : (0 : ℝ) < A := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hA)
  have hnA : (n : ℝ) ≤ A := by exact_mod_cast (Finset.mem_Icc.mp hn).2
  have hlog : Real.log n ≤ Real.log A :=
    Real.strictMonoOn_log.monotoneOn hnpos hApos hnA
  exact div_nonneg
    (mul_nonneg (criticalMellinAtomWeight_nonneg' n)
      (unitRieszSuzukiReporter_nonneg_of_mem hlog)) (by norm_num)

/-- Source Stokes fusion has Levi coordinate exactly `1+x_A(n)` on the physical packet. -/
theorem suzukiRankTwoStokesFissionCell_source_zero_zero
    {A n : ℕ} (hA : 2 ≤ A) (hn : n ∈ Finset.Icc 2 A) :
    suzukiRankTwoStokesFissionCell (suzukiCenterStokesAmplitude A n) 0 0 =
      ((1 + suzukiCenterStokesCartanCell A n : ℝ) : ℂ) := by
  rw [suzukiRankTwoStokesFissionCell_zero_zero, suzukiCenterStokesAmplitude]
  have hx := suzukiCenterStokesCartanCell_nonneg hA hn
  push_cast
  simp
  have hsqrt : Real.sqrt (suzukiCenterStokesCartanCell A n) *
      Real.sqrt (suzukiCenterStokesCartanCell A n) =
        suzukiCenterStokesCartanCell A n := by
    simpa [pow_two] using Real.sq_sqrt hx
  exact_mod_cast hsqrt

/-- One Cartan increment is bounded by the common aperture envelope. -/
theorem suzukiCenterStokesCartanCell_le
    {A n : ℕ} (hA : 2 ≤ A) (hn : n ∈ Finset.Icc 2 A) :
    suzukiCenterStokesCartanCell A n ≤ Real.log A / (2 * Real.sqrt A) := by
  have hA0 : 0 < A := lt_of_lt_of_le Nat.zero_lt_two hA
  have hn0 : 0 < n := lt_of_lt_of_le Nat.zero_lt_two (Finset.mem_Icc.mp hn).1
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hnA : (n : ℝ) ≤ A := by exact_mod_cast (Finset.mem_Icc.mp hn).2
  have hlog : Real.log n ≤ Real.log A :=
    Real.strictMonoOn_log.monotoneOn hnR hAR hnA
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg (by
    exact_mod_cast (by omega : 1 ≤ A))
  have hsqrt : 0 < Real.sqrt (A : ℝ) := Real.sqrt_pos.2 hAR
  have hshift : -(Real.log A - Real.log n) / 2 ≤ 0 := by linarith
  have hexp : Real.exp (-(Real.log A - Real.log n) / 2) ≤ 1 := by
    simpa using Real.exp_le_exp.mpr hshift
  have hfactor : 0 ≤ 1 - Real.exp (-(Real.log A - Real.log n) / 2) := by linarith
  have hvm : ArithmeticFunction.vonMangoldt n ≤ Real.log A :=
    ArithmeticFunction.vonMangoldt_le_log.trans hlog
  have hquot : ArithmeticFunction.vonMangoldt n / Real.sqrt A ≤
      Real.log A / Real.sqrt A :=
    div_le_div_of_nonneg_right hvm hsqrt.le
  have hquot0 : 0 ≤ ArithmeticFunction.vonMangoldt n / Real.sqrt A :=
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg hsqrt.le
  have hlogquot0 : 0 ≤ Real.log A / Real.sqrt A := div_nonneg hlogA hsqrt.le
  rw [suzukiCenterStokesCartanCell, unitRieszSuzuki_prime_term hA0 hn0]
  calc
    ((ArithmeticFunction.vonMangoldt n / Real.sqrt A) *
        (1 - Real.exp (-(Real.log A - Real.log n) / 2))) / 2 ≤
        ((Real.log A / Real.sqrt A) * 1) / 2 := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul hquot (by
            have hexp0 := Real.exp_pos (-(Real.log A - Real.log n) / 2)
            linarith : 1 - Real.exp (-(Real.log A - Real.log n) / 2) ≤ 1)
          hfactor hlogquot0) (by norm_num)
    _ = Real.log A / (2 * Real.sqrt A) := by ring

/-! ## Cubic Cartan remainder -/

/-- Third-order-renormalized logarithm of one positive Cartan coordinate. -/
def suzukiStokesCartanCubicRemainder (x : ℝ) : ℝ :=
  Real.log (1 + x) - x + x ^ 2 / 2

theorem suzukiStokesCartanCubicRemainder_nonneg
    {x : ℝ} (hx : 0 ≤ x) : 0 ≤ suzukiStokesCartanCubicRemainder x := by
  rcases hx.eq_or_lt with rfl | hx
  · simp [suzukiStokesCartanCubicRemainder]
  · have h := le_of_lt (log_one_add_gt_quadratic hx)
    unfold suzukiStokesCartanCubicRemainder
    linarith

theorem suzukiStokesCartanCubicRemainder_le
    {x : ℝ} (hx : 0 ≤ x) : suzukiStokesCartanCubicRemainder x ≤ x ^ 3 / 3 := by
  rcases hx.eq_or_lt with rfl | hx
  · simp [suzukiStokesCartanCubicRemainder]
  · have h := le_of_lt (log_one_add_lt_cubic hx)
    unfold suzukiStokesCartanCubicRemainder
    linarith

/-! ## Finite block-diagonal Levi determinant and Gamma completion -/

def suzukiStokesCartanLinearMass (A : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 A, suzukiCenterStokesCartanCell A n

def suzukiStokesCartanLogMass (A : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 A, Real.log (1 + suzukiCenterStokesCartanCell A n)

def suzukiStokesCartanQuadraticCounterterm (A : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 A, suzukiCenterStokesCartanCell A n ^ 2

def suzukiStokesCartanCubicRemainderMass (A : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 A,
    suzukiStokesCartanCubicRemainder (suzukiCenterStokesCartanCell A n)

/-- The linear Cartan mass is exactly half of Suzuki's finite prime outgoing charge. -/
theorem suzukiStokesCartanLinearMass_eq_primeOutgoingCharge_half
    {A : ℕ} (hA : 2 ≤ A) :
    suzukiStokesCartanLinearMass A = unitRieszCoherentPrimeOutgoingCharge A / 2 := by
  simp only [suzukiStokesCartanLinearMass, suzukiCenterStokesCartanCell]
  rw [← Finset.sum_div, unitRieszSuzuki_prime_sum hA]

/-- The finite Levi logarithm is its linear mass minus the forced quadratic counterterm plus the
positive cubic remainder. -/
theorem suzukiStokesCartanLogMass_eq_linear_sub_quadratic_add_remainder (A : ℕ) :
    suzukiStokesCartanLogMass A =
      suzukiStokesCartanLinearMass A -
        suzukiStokesCartanQuadraticCounterterm A / 2 +
          suzukiStokesCartanCubicRemainderMass A := by
  simp only [suzukiStokesCartanLogMass, suzukiStokesCartanLinearMass,
    suzukiStokesCartanQuadraticCounterterm, suzukiStokesCartanCubicRemainderMass,
    suzukiStokesCartanCubicRemainder, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_div]
  ring

theorem suzukiStokesCartanCubicRemainderMass_nonneg
    {A : ℕ} (hA : 2 ≤ A) : 0 ≤ suzukiStokesCartanCubicRemainderMass A := by
  rw [suzukiStokesCartanCubicRemainderMass]
  exact Finset.sum_nonneg fun n hn =>
    suzukiStokesCartanCubicRemainder_nonneg
      (suzukiCenterStokesCartanCell_nonneg hA hn)

/-- Elementary aperture bound before absorbing the logarithmic numerator. -/
theorem suzukiStokesCartanCubicRemainderMass_le_log_cube_div_sqrt
    {A : ℕ} (hA : 2 ≤ A) :
    suzukiStokesCartanCubicRemainderMass A ≤
      Real.log A ^ 3 / (24 * Real.sqrt A) := by
  have hA0 : (0 : ℝ) < A := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hA)
  have hsqrt : 0 < Real.sqrt (A : ℝ) := Real.sqrt_pos.2 hA0
  have hlog : 0 ≤ Real.log A := Real.log_nonneg (by
    exact_mod_cast (by omega : 1 ≤ A))
  have hcard : (Finset.Icc 2 A).card ≤ A := by
    simp only [Nat.card_Icc]
    omega
  calc
    suzukiStokesCartanCubicRemainderMass A ≤
        ∑ n ∈ Finset.Icc 2 A, suzukiCenterStokesCartanCell A n ^ 3 / 3 := by
      rw [suzukiStokesCartanCubicRemainderMass]
      exact Finset.sum_le_sum fun n hn =>
        suzukiStokesCartanCubicRemainder_le
          (suzukiCenterStokesCartanCell_nonneg hA hn)
    _ ≤ ∑ _n ∈ Finset.Icc 2 A,
        (Real.log A / (2 * Real.sqrt A)) ^ 3 / 3 := by
      apply Finset.sum_le_sum
      intro n hn
      exact div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (suzukiCenterStokesCartanCell_nonneg hA hn)
          (suzukiCenterStokesCartanCell_le hA hn) 3) (by norm_num)
    _ = ((Finset.Icc 2 A).card : ℝ) *
        ((Real.log A / (2 * Real.sqrt A)) ^ 3 / 3) := by simp
    _ ≤ (A : ℝ) * ((Real.log A / (2 * Real.sqrt A)) ^ 3 / 3) := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ = Real.log A ^ 3 / (24 * Real.sqrt A) := by
      field_simp [hsqrt.ne']
      rw [Real.sq_sqrt hA0.le]
      ring

/-- The total nonlinear Stokes correction is bounded uniformly over all natural apertures. -/
theorem exists_uniform_bound_suzukiStokesCartanCubicRemainderMass :
    ∃ C : ℝ, 0 < C ∧ ∀ A : ℕ, 2 ≤ A →
      suzukiStokesCartanCubicRemainderMass A ≤ C := by
  obtain ⟨C, hC, hlogC⟩ := exists_const_log_pow_le_rpow 3 (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨C, hC, ?_⟩
  intro A hA
  have hA0 : (0 : ℝ) < A := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hA)
  have hsqrt : 0 < Real.sqrt (A : ℝ) := Real.sqrt_pos.2 hA0
  have hpow := hlogC A (by omega : 1 ≤ A)
  have hrpow : (A : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt A := by
    rw [Real.sqrt_eq_rpow]
  rw [hrpow] at hpow
  calc
    suzukiStokesCartanCubicRemainderMass A ≤
        Real.log A ^ 3 / (24 * Real.sqrt A) :=
      suzukiStokesCartanCubicRemainderMass_le_log_cube_div_sqrt hA
    _ ≤ C / 24 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 24)]
      nlinarith
    _ ≤ C := by nlinarith

/-- Completed finite Cartan observable: twice the Levi logarithm, the forced quadratic
counterterm, and the literal regular-screw Gamma subtraction. -/
def suzukiCompletedStokesCartanWardObservable (A : ℕ) : ℝ :=
  2 * suzukiStokesCartanLogMass A +
    suzukiStokesCartanQuadraticCounterterm A -
      suzukiUnitRieszRegularWardMass (Real.log A)

/-- **Nonabelian Cartan--Ward completion.**  The completed Stokes observable is Suzuki Green plus
a uniformly bounded positive cubic remainder. -/
theorem suzukiCompletedStokesCartanWardObservable_eq_green_add_remainder
    (N : ℕ) :
    suzukiCompletedStokesCartanWardObservable (N + 2) =
      unitRieszSuzukiGreen (Real.log ((N + 2 : ℕ) : ℝ)) +
        2 * suzukiStokesCartanCubicRemainderMass (N + 2) := by
  rw [suzukiCompletedStokesCartanWardObservable,
    suzukiStokesCartanLogMass_eq_linear_sub_quadratic_add_remainder,
    suzukiStokesCartanLinearMass_eq_primeOutgoingCharge_half (by omega),
    unitRieszSuzukiGreen_eq_primeCharge_sub_regularWardMass]
  ring

end

end GaloisForLFunctions.RHTower
