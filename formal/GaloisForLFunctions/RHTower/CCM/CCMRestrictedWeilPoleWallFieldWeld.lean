import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPoleEntryAgeSource
import GaloisForLFunctions.RHTower.CCM.CCMGuinandWeilPrimeEntryWallFieldWeld
import GaloisForLFunctions.RHTower.CCM.CCMCriticalMellinGrowingCumulative

/-!
# Literal restricted-Weil pole / Suzuki wall-energy weld

Each prime-power correction to the two restricted-Weil parity poles is the
nonnegative critical-Mellin wall energy multiplied by an exact signed
hyperbolic response. The factorization retains entry delay and common aging.
-/

open Set MeasureTheory
open scoped BigOperators
noncomputable section
namespace RHTower

/-- Signed propagation response of one critical-Mellin wall energy in the odd pole. -/
def ccmWeilOddWallEnergyResponse (n : ℕ) (s : ℝ) : ℝ :=
  4 * Real.exp (Real.log n / 2) *
      (1 - Real.exp (-(Real.log n / 2))) ^ (2 : ℕ) * (s - Real.log n / 2) -
    8 * ccmWeilPoleAgeKernel (s - Real.log n / 2)

/-- Signed propagation response of one critical-Mellin wall energy in the even pole. -/
def ccmWeilEvenWallEnergyResponse (n : ℕ) (s : ℝ) : ℝ :=
  -4 * Real.exp (Real.log n / 2) *
      (1 + Real.exp (-(Real.log n / 2))) ^ (2 : ℕ) * (s - Real.log n / 2) -
    8 * ccmWeilPoleAgeKernel (s - Real.log n / 2)

/-- Decaying half-density converts ordinary Mangoldt mass back to critical wall energy. -/
theorem vonMangoldt_mul_exp_neg_log_half_eq_criticalMellinAtomWeight
    {n : ℕ} (hn : 0 < n) :
    ArithmeticFunction.vonMangoldt n * Real.exp (-(Real.log n / 2)) =
      criticalMellinAtomWeight n := by
  rw [← criticalMellinAtomWeight_mul_exp_log_half hn]
  rw [mul_assoc, ← Real.exp_add]
  have hz : Real.log n / 2 + -(Real.log n / 2) = 0 := by ring
  rw [hz, Real.exp_zero, mul_one]

/-- Exact odd entry impulse in critical-Mellin wall-energy normalization. -/
theorem ccmWeilOddPrimeEntrySlope_eq_criticalMellinWallEnergy
    (n : ℕ) (hn : 2 ≤ n) :
    ccmWeilOddPrimeEntrySlope n =
      4 * criticalMellinAtomWeight n * Real.exp (Real.log n / 2) *
        (1 - Real.exp (-(Real.log n / 2))) ^ (2 : ℕ) := by
  unfold ccmWeilOddPrimeEntrySlope
  rw [← criticalMellinAtomWeight_mul_exp_log_half (by omega : 0 < n)]
  ring

/-- Exact even entry-impulse magnitude in the same wall-energy normalization. -/
theorem ccmWeilEvenPrimeEntrySlopeMagnitude_eq_criticalMellinWallEnergy
    (n : ℕ) (hn : 2 ≤ n) :
    ccmWeilEvenPrimeEntrySlopeMagnitude n =
      4 * criticalMellinAtomWeight n * Real.exp (Real.log n / 2) *
        (1 + Real.exp (-(Real.log n / 2))) ^ (2 : ℕ) := by
  unfold ccmWeilEvenPrimeEntrySlopeMagnitude
  rw [← criticalMellinAtomWeight_mul_exp_log_half (by omega : 0 < n)]
  ring

/-- Common hyperbolic age loss is exactly eight wall-energy units times its kernel. -/
theorem ccmWeilPrimeAgeLoss_eq_criticalMellinWallEnergy
    (n : ℕ) (hn : 2 ≤ n) (s : ℝ) :
    ccmWeilPrimeAgeLoss n s =
      8 * criticalMellinAtomWeight n *
        ccmWeilPoleAgeKernel (s - Real.log n / 2) := by
  unfold ccmWeilPrimeAgeLoss
  calc
    8 * ArithmeticFunction.vonMangoldt n * Real.exp (-(Real.log n / 2)) *
          ccmWeilPoleAgeKernel (s - Real.log n / 2) =
        8 * (ArithmeticFunction.vonMangoldt n * Real.exp (-(Real.log n / 2))) *
          ccmWeilPoleAgeKernel (s - Real.log n / 2) := by ring
    _ = _ := by
      rw [vonMangoldt_mul_exp_neg_log_half_eq_criticalMellinAtomWeight
        (by omega : 0 < n)]

/-- Full odd prime atom, including logarithmic delay and aging, is one signed wall response. -/
theorem ccmWeilOddPrimeAtom_eq_criticalMellinWallEnergy
    (n : ℕ) (hn : 2 ≤ n) (s : ℝ) :
    2 * (-ccmWeilPolePrimeDiagonalAtom n s + ccmWeilPolePrimeCrossAtom n s) =
      criticalMellinAtomWeight n * ccmWeilOddWallEnergyResponse n s := by
  rw [ccmWeilOddPrimeAtom_eq_tangent_sub_age n hn,
    ccmWeilOddPrimeEntrySlope_eq_criticalMellinWallEnergy n hn,
    ccmWeilPrimeAgeLoss_eq_criticalMellinWallEnergy n hn]
  unfold ccmWeilOddWallEnergyResponse
  ring

/-- Full even prime atom is same wall energy with opposite tangent and common age loss. -/
theorem ccmWeilEvenPrimeAtom_eq_criticalMellinWallEnergy
    (n : ℕ) (hn : 2 ≤ n) (s : ℝ) :
    2 * (-ccmWeilPolePrimeDiagonalAtom n s - ccmWeilPolePrimeCrossAtom n s) =
      criticalMellinAtomWeight n * ccmWeilEvenWallEnergyResponse n s := by
  rw [ccmWeilEvenPrimeAtom_eq_tangent_sub_age n hn,
    ccmWeilEvenPrimeEntrySlopeMagnitude_eq_criticalMellinWallEnergy n hn,
    ccmWeilPrimeAgeLoss_eq_criticalMellinWallEnergy n hn]
  unfold ccmWeilEvenWallEnergyResponse
  ring

/-- At a canonical prime power, critical-Mellin energy is literal zero-height Suzuki wall energy. -/
theorem criticalMellinAtomWeight_primePower_eq_wallFieldEnergy
    (p : Nat.Primes) (e : ℕ) :
    criticalMellinAtomWeight (xiGammaEulerValuationNat (p, e)) =
      Complex.normSq (suzukiCriticalWallField 0 p e) := by
  rw [criticalMellinAtomWeight_primePower_eq_sq_suzukiCriticalEntryWallBareAmplitude,
    normSq_suzukiCriticalWallField_zero]

/-- Canonical odd pole atom as actual Suzuki wall-field energy response. -/
theorem ccmWeilOddPrimeAtom_primePower_eq_suzukiWallFieldEnergy
    (p : Nat.Primes) (e : ℕ) (s : ℝ) :
    2 * (-ccmWeilPolePrimeDiagonalAtom (xiGammaEulerValuationNat (p, e)) s +
        ccmWeilPolePrimeCrossAtom (xiGammaEulerValuationNat (p, e)) s) =
      Complex.normSq (suzukiCriticalWallField 0 p e) *
        ccmWeilOddWallEnergyResponse (xiGammaEulerValuationNat (p, e)) s := by
  have hn := one_lt_xiGammaEulerValuationNat p e
  rw [ccmWeilOddPrimeAtom_eq_criticalMellinWallEnergy _
      (by omega : 2 ≤ xiGammaEulerValuationNat (p, e)) s,
    criticalMellinAtomWeight_primePower_eq_wallFieldEnergy]

/-- Canonical even pole atom as actual Suzuki wall-field energy response. -/
theorem ccmWeilEvenPrimeAtom_primePower_eq_suzukiWallFieldEnergy
    (p : Nat.Primes) (e : ℕ) (s : ℝ) :
    2 * (-ccmWeilPolePrimeDiagonalAtom (xiGammaEulerValuationNat (p, e)) s -
        ccmWeilPolePrimeCrossAtom (xiGammaEulerValuationNat (p, e)) s) =
      Complex.normSq (suzukiCriticalWallField 0 p e) *
        ccmWeilEvenWallEnergyResponse (xiGammaEulerValuationNat (p, e)) s := by
  have hn := one_lt_xiGammaEulerValuationNat p e
  rw [ccmWeilEvenPrimeAtom_eq_criticalMellinWallEnergy _
      (by omega : 2 ≤ xiGammaEulerValuationNat (p, e)) s,
    criticalMellinAtomWeight_primePower_eq_wallFieldEnergy]

/-- Exact finite odd pole as smooth prime--polar--Gamma term plus signed wall responses. -/
theorem ccmWeilOddPole_eq_criticalMellinWallEnergySuperposition
    (a : SuzukiPositiveAperture) :
    ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a (-1)) =
      2 * (ccmWeilPoleDiagonalSmooth a.1 - ccmWeilPoleCrossSmooth a.1) +
        ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
          criticalMellinAtomWeight n * ccmWeilOddWallEnergyResponse n a.1 := by
  rw [ccmWeilOddPole_eq_entry_age_balance]
  calc
    2 * (ccmWeilPoleDiagonalSmooth a.1 - ccmWeilPoleCrossSmooth a.1) +
          ccmWeilOddEntryTangentBudget a - ccmWeilPrimeAgeBudget a =
        2 * (ccmWeilPoleDiagonalSmooth a.1 - ccmWeilPoleCrossSmooth a.1) +
          (ccmWeilOddEntryTangentBudget a - ccmWeilPrimeAgeBudget a) := by ring
    _ = 2 * (ccmWeilPoleDiagonalSmooth a.1 - ccmWeilPoleCrossSmooth a.1) +
        ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
          (ccmWeilOddPrimeEntrySlope n * (a.1 - Real.log n / 2) -
            ccmWeilPrimeAgeLoss n a.1) := by
      unfold ccmWeilOddEntryTangentBudget ccmWeilPrimeAgeBudget
      rw [Finset.sum_sub_distrib]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro n hn
      rw [ccmWeilOddPrimeEntrySlope_eq_criticalMellinWallEnergy n
          (Finset.mem_Icc.mp hn).1,
        ccmWeilPrimeAgeLoss_eq_criticalMellinWallEnergy n
          (Finset.mem_Icc.mp hn).1]
      unfold ccmWeilOddWallEnergyResponse
      ring

/-- Exact finite even pole with opposite tangent response and same wall-energy age loss. -/
theorem ccmWeilEvenPole_eq_criticalMellinWallEnergySuperposition
    (a : SuzukiPositiveAperture) :
    ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a 1) =
      2 * (ccmWeilPoleDiagonalSmooth a.1 + ccmWeilPoleCrossSmooth a.1) +
        ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
          criticalMellinAtomWeight n * ccmWeilEvenWallEnergyResponse n a.1 := by
  rw [ccmWeilEvenPole_eq_entry_age_balance]
  calc
    2 * (ccmWeilPoleDiagonalSmooth a.1 + ccmWeilPoleCrossSmooth a.1) -
          ccmWeilEvenEntryTangentBudget a - ccmWeilPrimeAgeBudget a =
        2 * (ccmWeilPoleDiagonalSmooth a.1 + ccmWeilPoleCrossSmooth a.1) +
          (-ccmWeilEvenEntryTangentBudget a - ccmWeilPrimeAgeBudget a) := by ring
    _ = 2 * (ccmWeilPoleDiagonalSmooth a.1 + ccmWeilPoleCrossSmooth a.1) +
        ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
          (-ccmWeilEvenPrimeEntrySlopeMagnitude n * (a.1 - Real.log n / 2) -
            ccmWeilPrimeAgeLoss n a.1) := by
      have hneg :
          -(∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
              ccmWeilEvenPrimeEntrySlopeMagnitude n * (a.1 - Real.log n / 2)) =
            ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
              -ccmWeilEvenPrimeEntrySlopeMagnitude n * (a.1 - Real.log n / 2) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro n hn
        ring
      unfold ccmWeilEvenEntryTangentBudget ccmWeilPrimeAgeBudget
      rw [Finset.sum_sub_distrib, hneg]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro n hn
      rw [ccmWeilEvenPrimeEntrySlopeMagnitude_eq_criticalMellinWallEnergy n
          (Finset.mem_Icc.mp hn).1,
        ccmWeilPrimeAgeLoss_eq_criticalMellinWallEnergy n
          (Finset.mem_Icc.mp hn).1]
      unfold ccmWeilEvenWallEnergyResponse
      ring

/-! ## Hyperbolic Green residual -/

private theorem ccmWeilOddWallEnergyResponse_coefficient (h : ℝ) :
    4 * Real.exp h * (1 - Real.exp (-h)) ^ (2 : ℕ) = 8 * (Real.cosh h - 1) := by
  have hexp : Real.exp h * Real.exp (-h) = 1 := by
    rw [← Real.exp_add]
    simp
  have hexp_sq : Real.exp h * Real.exp (-h) ^ (2 : ℕ) = Real.exp (-h) := by
    calc
      Real.exp h * Real.exp (-h) ^ (2 : ℕ) =
          (Real.exp h * Real.exp (-h)) * Real.exp (-h) := by ring
      _ = Real.exp (-h) := by rw [hexp]; simp
  calc
    4 * Real.exp h * (1 - Real.exp (-h)) ^ (2 : ℕ) =
        4 * (Real.exp h - 2 * (Real.exp h * Real.exp (-h)) +
          Real.exp h * Real.exp (-h) ^ (2 : ℕ)) := by ring
    _ = 4 * (Real.exp h - 2 + Real.exp (-h)) := by simp [hexp, hexp_sq]
    _ = 8 * (Real.cosh h - 1) := by rw [Real.cosh_eq]; ring

private theorem ccmWeilEvenWallEnergyResponse_coefficient (h : ℝ) :
    4 * Real.exp h * (1 + Real.exp (-h)) ^ (2 : ℕ) = 8 * (Real.cosh h + 1) := by
  have hexp : Real.exp h * Real.exp (-h) = 1 := by
    rw [← Real.exp_add]
    simp
  have hexp_sq : Real.exp h * Real.exp (-h) ^ (2 : ℕ) = Real.exp (-h) := by
    calc
      Real.exp h * Real.exp (-h) ^ (2 : ℕ) =
          (Real.exp h * Real.exp (-h)) * Real.exp (-h) := by ring
      _ = Real.exp (-h) := by rw [hexp]; simp
  calc
    4 * Real.exp h * (1 + Real.exp (-h)) ^ (2 : ℕ) =
        4 * (Real.exp h + 2 * (Real.exp h * Real.exp (-h)) +
          Real.exp h * Real.exp (-h) ^ (2 : ℕ)) := by ring
    _ = 4 * (Real.exp h + 2 + Real.exp (-h)) := by simp [hexp, hexp_sq]
    _ = 8 * (Real.cosh h + 1) := by rw [Real.cosh_eq]; ring

/-- Odd pole response in centered hyperbolic coordinates. -/
theorem ccmWeilOddWallEnergyResponse_eq_hyperbolic (n : ℕ) (s : ℝ) :
    ccmWeilOddWallEnergyResponse n s =
      8 * ((s - Real.log n / 2) * Real.cosh (Real.log n / 2) -
        Real.sinh (s - Real.log n / 2)) := by
  unfold ccmWeilOddWallEnergyResponse ccmWeilPoleAgeKernel
  rw [ccmWeilOddWallEnergyResponse_coefficient]
  ring

/-- Even pole response in centered hyperbolic coordinates. -/
theorem ccmWeilEvenWallEnergyResponse_eq_hyperbolic (n : ℕ) (s : ℝ) :
    ccmWeilEvenWallEnergyResponse n s =
      -8 * ((s - Real.log n / 2) * Real.cosh (Real.log n / 2) +
        Real.sinh (s - Real.log n / 2)) := by
  unfold ccmWeilEvenWallEnergyResponse ccmWeilPoleAgeKernel
  rw [show -4 * Real.exp (Real.log n / 2) *
      (1 + Real.exp (-(Real.log n / 2))) ^ (2 : ℕ) =
      -(4 * Real.exp (Real.log n / 2) *
        (1 + Real.exp (-(Real.log n / 2))) ^ (2 : ℕ)) by ring,
    ccmWeilEvenWallEnergyResponse_coefficient]
  ring

/-- First derivative of the odd pole response. -/
theorem hasDerivAt_ccmWeilOddWallEnergyResponse (n : ℕ) (s : ℝ) :
    HasDerivAt (ccmWeilOddWallEnergyResponse n)
      (8 * (Real.cosh (Real.log n / 2) -
        Real.cosh (s - Real.log n / 2))) s := by
  have hf : ccmWeilOddWallEnergyResponse n = fun t =>
      8 * ((t - Real.log n / 2) * Real.cosh (Real.log n / 2) -
        Real.sinh (t - Real.log n / 2)) := by
    funext t
    exact ccmWeilOddWallEnergyResponse_eq_hyperbolic n t
  rw [hf]
  have hu : HasDerivAt (fun t : ℝ => t - Real.log n / 2) 1 s :=
    (hasDerivAt_id s).sub_const _
  convert! ((hu.mul_const (Real.cosh (Real.log n / 2))).sub hu.sinh).const_mul 8 using 1
  ring

/-- First derivative of the even pole response. -/
theorem hasDerivAt_ccmWeilEvenWallEnergyResponse (n : ℕ) (s : ℝ) :
    HasDerivAt (ccmWeilEvenWallEnergyResponse n)
      (-8 * (Real.cosh (Real.log n / 2) +
        Real.cosh (s - Real.log n / 2))) s := by
  have hf : ccmWeilEvenWallEnergyResponse n = fun t =>
      -8 * ((t - Real.log n / 2) * Real.cosh (Real.log n / 2) +
        Real.sinh (t - Real.log n / 2)) := by
    funext t
    exact ccmWeilEvenWallEnergyResponse_eq_hyperbolic n t
  rw [hf]
  have hu : HasDerivAt (fun t : ℝ => t - Real.log n / 2) 1 s :=
    (hasDerivAt_id s).sub_const _
  convert! ((hu.mul_const (Real.cosh (Real.log n / 2))).add hu.sinh).const_mul (-8) using 1
  ring

/-- Odd and even pole responses have the same second derivative. -/
theorem deriv_deriv_ccmWeilOddWallEnergyResponse (n : ℕ) (s : ℝ) :
    deriv (deriv (ccmWeilOddWallEnergyResponse n)) s =
      -8 * Real.sinh (s - Real.log n / 2) := by
  have hfirst : deriv (ccmWeilOddWallEnergyResponse n) = fun t =>
      8 * (Real.cosh (Real.log n / 2) -
        Real.cosh (t - Real.log n / 2)) := by
    funext t
    exact (hasDerivAt_ccmWeilOddWallEnergyResponse n t).deriv
  rw [hfirst]
  have hu : HasDerivAt (fun t : ℝ => t - Real.log n / 2) 1 s :=
    (hasDerivAt_id s).sub_const _
  have hd := ((hasDerivAt_const s (Real.cosh (Real.log n / 2))).sub hu.cosh).const_mul 8
  have hderiv : deriv (fun t : ℝ =>
      8 * (Real.cosh (Real.log n / 2) - Real.cosh (t - Real.log n / 2))) s =
      8 * -Real.sinh (s - Real.log n / 2) := by
    simpa only [Pi.sub_apply, zero_sub, mul_one] using hd.deriv
  rw [hderiv]
  ring

/-- Even response has the same hyperbolic forcing as the odd response. -/
theorem deriv_deriv_ccmWeilEvenWallEnergyResponse (n : ℕ) (s : ℝ) :
    deriv (deriv (ccmWeilEvenWallEnergyResponse n)) s =
      -8 * Real.sinh (s - Real.log n / 2) := by
  have hfirst : deriv (ccmWeilEvenWallEnergyResponse n) = fun t =>
      -8 * (Real.cosh (Real.log n / 2) +
        Real.cosh (t - Real.log n / 2)) := by
    funext t
    exact (hasDerivAt_ccmWeilEvenWallEnergyResponse n t).deriv
  rw [hfirst]
  have hu : HasDerivAt (fun t : ℝ => t - Real.log n / 2) 1 s :=
    (hasDerivAt_id s).sub_const _
  have hd := ((hasDerivAt_const s (Real.cosh (Real.log n / 2))).add hu.cosh).const_mul (-8)
  simpa only [Pi.add_apply, zero_add, mul_one] using hd.deriv

/-- Hyperbolic Green residual of one odd pole response is the raw triangular factor. -/
theorem ccmWeilOddWallEnergyResponse_green_triangle (n : ℕ) (s : ℝ) :
    ccmWeilOddWallEnergyResponse n s -
        deriv (deriv (ccmWeilOddWallEnergyResponse n)) s =
      4 * Real.cosh (Real.log n / 2) * (2 * s - Real.log n) := by
  rw [ccmWeilOddWallEnergyResponse_eq_hyperbolic,
    deriv_deriv_ccmWeilOddWallEnergyResponse]
  ring

/-- Even pole response has the opposite raw triangular Green residual. -/
theorem ccmWeilEvenWallEnergyResponse_green_triangle (n : ℕ) (s : ℝ) :
    ccmWeilEvenWallEnergyResponse n s -
        deriv (deriv (ccmWeilEvenWallEnergyResponse n)) s =
      -(4 * Real.cosh (Real.log n / 2) * (2 * s - Real.log n)) := by
  rw [ccmWeilEvenWallEnergyResponse_eq_hyperbolic,
    deriv_deriv_ccmWeilEvenWallEnergyResponse]
  ring

/-- Coefficient-faithful odd residual: normalization removes exactly the hyperbolic carrier. -/
theorem ccmWeilOddWallEnergyResponse_normalized_green_triangle (n : ℕ) (s : ℝ) :
    (ccmWeilOddWallEnergyResponse n s -
        deriv (deriv (ccmWeilOddWallEnergyResponse n)) s) /
        (4 * Real.cosh (Real.log n / 2)) = 2 * s - Real.log n := by
  rw [ccmWeilOddWallEnergyResponse_green_triangle]
  exact mul_div_cancel_left₀ _
    (ne_of_gt (by positivity : 0 < 4 * Real.cosh (Real.log n / 2)))

/-- Coefficient-faithful even residual differs only by orientation. -/
theorem ccmWeilEvenWallEnergyResponse_normalized_green_triangle (n : ℕ) (s : ℝ) :
    (ccmWeilEvenWallEnergyResponse n s -
        deriv (deriv (ccmWeilEvenWallEnergyResponse n)) s) /
        (4 * Real.cosh (Real.log n / 2)) = -(2 * s - Real.log n) := by
  rw [ccmWeilEvenWallEnergyResponse_green_triangle]
  have hne : 4 * Real.cosh (Real.log n / 2) ≠ 0 :=
    ne_of_gt (by positivity : 0 < 4 * Real.cosh (Real.log n / 2))
  field_simp [hne]

end RHTower
