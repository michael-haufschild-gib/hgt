import GaloisForLFunctions.RHTower.XiGammaSixFilteredBoundaryControl
import GaloisForLFunctions.RHTower.HedenmalmThetaGammaSixWoldCarrier

/-!
# Gamma Hessian domination by the Wold--Jordan harmonic source carrier

The log-smooth Heat--Cassini residual cannot dominate the literal Gamma-six boundary Hessian:
the former decays, while the latter has a positive harmonic-prime tail off neutral grade.  The
correct nondecaying source observable is the finite-shell-derived theta/Gamma Wold--Jordan
carrier.  Its square is exactly one source-selected scalar times `1 / p`.

This module proves an unconditional two-sided harmonic comparison and an explicit
coefficient-faithful majorant.  Prime labels, Xi multiplicity copies, Gamma depth, and both
reflection orientations remain literal.  The majorant is intentionally not claimed summable:
its summability is exactly horizontal neutrality.
-/

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- Squared coefficient of the literal theta/Gamma Wold--Jordan harmonic carrier. -/
def xiGammaSixWoldJordanHarmonicWeight (q : XiZeroCopy) : ℝ :=
  4 * sourceHorizontalWoldPrimeClockUniversalProfile
    (primeDepthBVWoldXiCenteredRate q.1) ^ 2

theorem xiGammaSixWoldJordanHarmonicWeight_nonneg (q : XiZeroCopy) :
    0 ≤ xiGammaSixWoldJordanHarmonicWeight q := by
  rw [xiGammaSixWoldJordanHarmonicWeight]
  positivity

theorem xiGammaSixWoldJordanHarmonicWeight_eq_zero_iff (q : XiZeroCopy) :
    xiGammaSixWoldJordanHarmonicWeight q = 0 ↔
      primeDepthBVWoldXiCenteredRate q.1 = 0 := by
  simp [xiGammaSixWoldJordanHarmonicWeight,
    sourceHorizontalWoldPrimeClockUniversalProfile_eq_zero_iff]

theorem thetaGammaSixWoldHorizontalCarrier_sq_eq_weight_div
    (p : Nat.Primes) (q : XiZeroCopy) :
    thetaGammaSixWoldHorizontalCarrier p q ^ 2 =
      xiGammaSixWoldJordanHarmonicWeight q / (p : ℝ) := by
  rw [thetaGammaSixWoldHorizontalCarrier_sq,
    xiGammaSixWoldJordanHarmonicWeight]

/-- Exact two-sided harmonic comparison. Same prime, Xi copy, and Gamma depth occur on both
sides; no asymptotic relabelling is used. -/
theorem gammaSixFilteredBoundarySecondJet_woldJordan_twoSided
    {m : ℕ} (hm : 1 ≤ m) (q : XiZeroCopy) (p : Nat.Primes) :
    gammaSixFilteredBoundaryHarmonicConstant m q *
          thetaGammaSixWoldHorizontalCarrier p q ^ 2 ≤
        xiGammaSixWoldJordanHarmonicWeight q *
          gammaSixFilteredBoundarySecondJet m q p ∧
      xiGammaSixWoldJordanHarmonicWeight q *
          gammaSixFilteredBoundarySecondJet m q p ≤
        (Real.log 2 / (m : ℝ) ^ 2) *
          thetaGammaSixWoldHorizontalCarrier p q ^ 2 := by
  have hA : 0 ≤ xiGammaSixWoldJordanHarmonicWeight q :=
    xiGammaSixWoldJordanHarmonicWeight_nonneg q
  constructor
  · calc
      gammaSixFilteredBoundaryHarmonicConstant m q *
          thetaGammaSixWoldHorizontalCarrier p q ^ 2 =
          xiGammaSixWoldJordanHarmonicWeight q *
            (gammaSixFilteredBoundaryHarmonicConstant m q * (1 / (p : ℝ))) := by
              rw [thetaGammaSixWoldHorizontalCarrier_sq_eq_weight_div]
              ring
      _ ≤ xiGammaSixWoldJordanHarmonicWeight q *
          gammaSixFilteredBoundarySecondJet m q p :=
        mul_le_mul_of_nonneg_left
          (gammaSixFilteredBoundaryHarmonicConstant_mul_one_div_le hm q p) hA
  · calc
      xiGammaSixWoldJordanHarmonicWeight q *
          gammaSixFilteredBoundarySecondJet m q p ≤
          xiGammaSixWoldJordanHarmonicWeight q *
            ((Real.log 2 / (m : ℝ) ^ 2) * (1 / (p : ℝ))) :=
        mul_le_mul_of_nonneg_left
          (gammaSixFilteredBoundarySecondJet_le_harmonic hm q p) hA
      _ = (Real.log 2 / (m : ℝ) ^ 2) *
          thetaGammaSixWoldHorizontalCarrier p q ^ 2 := by
        rw [thetaGammaSixWoldHorizontalCarrier_sq_eq_weight_div]
        ring

/-- Explicit source-derived coefficient that turns the Wold--Jordan square into a literal
majorant. At the neutral fibre both carrier and Hessian vanish; total division sets the unused
coefficient to zero. -/
def xiGammaSixWoldJordanHessianDominationConstant
    (m : ℕ) (q : XiZeroCopy) : ℝ :=
  (Real.log 2 / (m : ℝ) ^ 2) / xiGammaSixWoldJordanHarmonicWeight q

/-- Literal Wold--Jordan source majorant for the Gamma boundary Hessian. -/
def xiGammaSixWoldJordanHessianMajorant
    (m : ℕ) (q : XiZeroCopy) (p : Nat.Primes) : ℝ :=
  xiGammaSixWoldJordanHessianDominationConstant m q *
    thetaGammaSixWoldHorizontalCarrier p q ^ 2

/-- Unconditional coefficient-faithful domination of the literal Gamma boundary Hessian by the
literal nondecaying theta/Gamma Wold--Jordan source carrier. -/
theorem gammaSixFilteredBoundarySecondJet_le_woldJordanMajorant
    {m : ℕ} (hm : 1 ≤ m) (q : XiZeroCopy) (p : Nat.Primes) :
    gammaSixFilteredBoundarySecondJet m q p ≤
      xiGammaSixWoldJordanHessianMajorant m q p := by
  let A := xiGammaSixWoldJordanHarmonicWeight q
  by_cases hA : A = 0
  · have ht : primeDepthBVWoldXiCenteredRate q.1 = 0 := by
      exact (xiGammaSixWoldJordanHarmonicWeight_eq_zero_iff q).1 hA
    have hB : gammaSixFilteredBoundarySecondJet m q p = 0 := by
      rw [gammaSixFilteredBoundarySecondJet_eq_factorized hm q p, ht]
      norm_num
    rw [hB]
    have hmajor : xiGammaSixWoldJordanHessianMajorant m q p = 0 := by
      rw [xiGammaSixWoldJordanHessianMajorant,
        xiGammaSixWoldJordanHessianDominationConstant]
      change (Real.log 2 / (m : ℝ) ^ 2) / A * _ = 0
      rw [hA]
      simp
    rw [hmajor]
  · have hupper :=
      gammaSixFilteredBoundarySecondJet_le_harmonic hm q p
    calc
      gammaSixFilteredBoundarySecondJet m q p ≤
          (Real.log 2 / (m : ℝ) ^ 2) * (1 / (p : ℝ)) := hupper
      _ = xiGammaSixWoldJordanHessianMajorant m q p := by
        rw [xiGammaSixWoldJordanHessianMajorant,
          xiGammaSixWoldJordanHessianDominationConstant,
          thetaGammaSixWoldHorizontalCarrier_sq_eq_weight_div]
        change _ = (Real.log 2 / (m : ℝ) ^ 2) / A * (A / (p : ℝ))
        field_simp [hA]

/-- Finite source packets inherit the same coefficient-faithful domination. -/
theorem sum_gammaSixFilteredBoundarySecondJet_le_woldJordanMajorant
    {m : ℕ} (hm : 1 ≤ m) (q : XiZeroCopy) (F : Finset Nat.Primes) :
    ∑ p ∈ F, gammaSixFilteredBoundarySecondJet m q p ≤
      ∑ p ∈ F, xiGammaSixWoldJordanHessianMajorant m q p := by
  exact Finset.sum_le_sum fun p _ =>
    gammaSixFilteredBoundarySecondJet_le_woldJordanMajorant hm q p

/-- Domination coefficient is invariant under the functional-equation reflection. -/
theorem xiGammaSixWoldJordanHessianDominationConstant_copyReflect
    (m : ℕ) (q : XiZeroCopy) :
    xiGammaSixWoldJordanHessianDominationConstant m (xiZeroCopyReflectEquiv q) =
      xiGammaSixWoldJordanHessianDominationConstant m q := by
  rw [xiGammaSixWoldJordanHessianDominationConstant,
    xiGammaSixWoldJordanHessianDominationConstant,
    xiGammaSixWoldJordanHarmonicWeight,
    xiGammaSixWoldJordanHarmonicWeight,
    primeDepthBVWoldXiCenteredRate_copyReflect,
    sourceHorizontalWoldPrimeClockUniversalProfile_neg]
  ring

/-- The coefficient-faithful majorant preserves both reflection orientations. -/
theorem xiGammaSixWoldJordanHessianMajorant_copyReflect
    (m : ℕ) (q : XiZeroCopy) (p : Nat.Primes) :
    xiGammaSixWoldJordanHessianMajorant m (xiZeroCopyReflectEquiv q) p =
      xiGammaSixWoldJordanHessianMajorant m q p := by
  rw [xiGammaSixWoldJordanHessianMajorant,
    xiGammaSixWoldJordanHessianMajorant,
    xiGammaSixWoldJordanHessianDominationConstant_copyReflect,
    thetaGammaSixWoldHorizontalCarrier_copyReflect]
  ring

/-- Literal Gamma boundary Hessian itself is reflection-even on the two retained Xi sheets. -/
theorem gammaSixFilteredBoundarySecondJet_copyReflect
    {m : ℕ} (hm : 1 ≤ m) (q : XiZeroCopy) (p : Nat.Primes) :
    gammaSixFilteredBoundarySecondJet m (xiZeroCopyReflectEquiv q) p =
      gammaSixFilteredBoundarySecondJet m q p := by
  rw [gammaSixFilteredBoundarySecondJet_eq_factorized hm,
    gammaSixFilteredBoundarySecondJet_eq_factorized hm,
    primeDepthBVWoldXiCenteredRate_copyReflect, abs_neg]

/-- Hostile classification: the new majorant is the correct harmonic source class, not a hidden
summable residual. Its summability is exactly neutral horizontal grade. -/
theorem summable_xiGammaSixWoldJordanHessianMajorant_iff
    {m : ℕ} (hm : 1 ≤ m) (q : XiZeroCopy) :
    Summable (xiGammaSixWoldJordanHessianMajorant m q) ↔
      primeDepthBVWoldXiCenteredRate q.1 = 0 := by
  constructor
  · intro hsum
    by_contra ht
    have hA : 0 < xiGammaSixWoldJordanHarmonicWeight q := by
      have hAnn := xiGammaSixWoldJordanHarmonicWeight_nonneg q
      exact lt_of_le_of_ne hAnn
        (Ne.symm (fun h => ht ((xiGammaSixWoldJordanHarmonicWeight_eq_zero_iff q).1 h)))
    have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
    have hC : 0 < xiGammaSixWoldJordanHessianDominationConstant m q := by
      rw [xiGammaSixWoldJordanHessianDominationConstant]
      exact div_pos (div_pos (Real.log_pos one_lt_two) (sq_pos_of_pos hm0)) hA
    have hscaled := hsum.mul_left
      (xiGammaSixWoldJordanHessianDominationConstant m q)⁻¹
    have hcarrier : Summable (fun p : Nat.Primes =>
        thetaGammaSixWoldHorizontalCarrier p q ^ 2) := by
      refine hscaled.congr fun p => ?_
      rw [xiGammaSixWoldJordanHessianMajorant]
      field_simp [hC.ne']
    exact ht ((summable_sq_thetaGammaSixWoldHorizontalCarrier_iff q).1 hcarrier)
  · intro ht
    have hzero : xiGammaSixWoldJordanHessianMajorant m q = 0 := by
      funext p
      rw [xiGammaSixWoldJordanHessianMajorant,
        xiGammaSixWoldJordanHessianDominationConstant]
      have hA : xiGammaSixWoldJordanHarmonicWeight q = 0 :=
        (xiGammaSixWoldJordanHarmonicWeight_eq_zero_iff q).2 ht
      rw [hA]
      simp
    rw [hzero]
    exact summable_zero

end

end RHTower.HedenmalmThetaSource
