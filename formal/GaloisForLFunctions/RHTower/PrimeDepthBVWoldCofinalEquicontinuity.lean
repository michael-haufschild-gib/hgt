import GaloisForLFunctions.RHTower.PrimeDepthBVWoldSourceNormalSchattenBridge

/-!
# Cofinal source-normal equicontinuity selector

Deep BV--Wold anomalies converge to zero in the all-prime `ℓ¹` mass.  Nevertheless the squared
physical Gamma deattenuation transports every depth-`n+2` anomaly exactly back to the same
depth-one coordinate.  Consequently a depth-uniform bound for these source-normal inverse maps
forces the centered anomaly to vanish.

This is a quantitative replacement for the too-coarse graph-domain producer.  It does not assume
that the depth-one family is summable.  It asks only for a uniform coordinate bound on the exact
source-normal transports.  Existing finite Route-J transport has growing scalar gain, so it does
not discharge this condition.
-/

namespace RHTower

noncomputable section

open Filter
open PrimitivePromotedCofinalDepth

/-- Centered `r`-step source-normal transport.  The square records the two polarized legs. -/
def primeDepthBVWoldSourceNormalCofinalCenteredTransport
    (sourceDepth r : ℕ) (f : Nat.Primes → ℝ) (p : Nat.Primes) : ℝ :=
  criticalDepthDeattenuation (p, sourceDepth) r ^ 2 * f p

/-- The source-normal transport multiplier is the exact prime power required by Wold depth. -/
theorem primeDepthBVWoldSourceNormalCofinalCenteredTransport_eq
    (sourceDepth r : ℕ) (f : Nat.Primes → ℝ) (p : Nat.Primes) :
    primeDepthBVWoldSourceNormalCofinalCenteredTransport sourceDepth r f p =
      (p : ℝ) ^ r * f p := by
  rw [primeDepthBVWoldSourceNormalCofinalCenteredTransport,
    criticalDepthDeattenuation_sq]

/-- Exact Wold depth conversion for an arbitrary number of depth steps. -/
theorem primePow_mul_woldCoeff_add
    (p : Nat.Primes) (e r : ℕ) :
    (p : ℝ) ^ r * woldCoeff (e + r) p = woldCoeff e p := by
  have hp0 : (p : ℝ) ≠ 0 := by
    exact_mod_cast p.2.ne_zero
  rw [woldCoeff, woldCoeff, pow_add]
  field_simp [hp0]

/-- Equivalent geometric-decay form of the multi-depth Wold conversion. -/
theorem woldCoeff_add_eq_inv_pow_mul
    (p : Nat.Primes) (e r : ℕ) :
    woldCoeff (e + r) p = (p : ℝ)⁻¹ ^ r * woldCoeff e p := by
  have hp0 : (p : ℝ) ≠ 0 := by
    exact_mod_cast p.2.ne_zero
  have hpow : ((p : ℝ)) ^ r ≠ 0 := pow_ne_zero r hp0
  rw [← primePow_mul_woldCoeff_add p e r, inv_pow, inv_mul_cancel_left₀ hpow]

/-- Source-normal cofinal transport recovers the same centered coefficient at recorded depth. -/
theorem sourceNormalCofinalCenteredTransport_smul_woldCoeff
    (a : ℝ) (sourceDepth e r : ℕ) (p : Nat.Primes) :
    primeDepthBVWoldSourceNormalCofinalCenteredTransport sourceDepth r
        (fun q => a * woldCoeff (e + r) q) p =
      a * woldCoeff e p := by
  rw [primeDepthBVWoldSourceNormalCofinalCenteredTransport_eq]
  calc
    (p : ℝ) ^ r * (a * woldCoeff (e + r) p) =
        a * ((p : ℝ) ^ r * woldCoeff (e + r) p) := by ring
    _ = a * woldCoeff e p := by rw [primePow_mul_woldCoeff_add]

/-- Every depth-`n+2` centered anomaly returns to the fixed depth-one coordinate. -/
theorem sourceNormalCofinalCenteredTransport_from_deep
    (a : ℝ) (sourceDepth n : ℕ) (p : Nat.Primes) :
    primeDepthBVWoldSourceNormalCofinalCenteredTransport sourceDepth (n + 1)
        (fun q => a * woldCoeff (n + 2) q) p =
      a * woldCoeff 1 p := by
  simpa only [show 1 + (n + 1) = n + 2 by omega] using
    sourceNormalCofinalCenteredTransport_smul_woldCoeff
      a sourceDepth 1 (n + 1) p

/-- The same exact cofinal transport identity for the actual Xi atlas after subtracting the
physical/unit-double trace-class seam. -/
theorem sourceNormalCofinalCenteredTransport_relativeLogCoefficient
    (rho : XiDivisorSupport) (sourceDepth n : ℕ) (p : Nat.Primes) :
    primeDepthBVWoldSourceNormalCofinalCenteredTransport sourceDepth (n + 1)
        (fun q => primeDepthBVWoldXiRelativeLogCoefficient rho (n + 2) q -
          woldRemainder q) p =
      primeDepthBVWoldXiCenteredRate rho * woldCoeff 1 p := by
  have hcentered : (fun q =>
      primeDepthBVWoldXiRelativeLogCoefficient rho (n + 2) q - woldRemainder q) =
      (fun q => primeDepthBVWoldXiCenteredRate rho * woldCoeff (n + 2) q) := by
    funext q
    rw [primeDepthBVWoldXiRelativeLogCoefficient_eq]
    ring
  rw [hcentered]
  exact sourceNormalCofinalCenteredTransport_from_deep
    (primeDepthBVWoldXiCenteredRate rho) sourceDepth n p

/-- All-prime `ℓ¹` mass of the centered depth-`e` coefficient.  It is used only at `e ≥ 2`, where
the defining family is summable. -/
def primeDepthBVWoldCenteredL1Mass (a : ℝ) (e : ℕ) : ℝ :=
  ∑' p : Nat.Primes, |a| * woldCoeff e p

/-- Deep centered anomalies vanish in `ℓ¹`.  This is the compactness half of the new selector. -/
theorem primeDepthBVWoldCenteredL1Mass_tendsto_zero (a : ℝ) :
    Tendsto (fun n : ℕ => primeDepthBVWoldCenteredL1Mass a (n + 2))
      atTop (nhds 0) := by
  have hsum : Summable (fun p : Nat.Primes => |a| * woldCoeff 2 p) :=
    (summable_woldCoeff_of_two_le (e := 2) le_rfl).mul_left |a|
  change Tendsto (fun n : ℕ => ∑' p : Nat.Primes, |a| * woldCoeff (n + 2) p)
    atTop (nhds 0)
  rw [show (0 : ℝ) = ∑' _p : Nat.Primes, (0 : ℝ) by simp]
  apply tendsto_tsum_of_dominated_convergence hsum
  · intro p
    have hpInv0 : 0 ≤ (p : ℝ)⁻¹ := by positivity
    have hpInv1 : (p : ℝ)⁻¹ < 1 := by
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast p.2.one_lt)
    have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hpInv0 hpInv1
    have hscaled : Tendsto
        (fun n : ℕ => |a| * ((p : ℝ)⁻¹ ^ n * woldCoeff 2 p)) atTop (nhds 0) := by
      simpa using (hpow.mul_const (woldCoeff 2 p)).const_mul |a|
    have hfun : (fun n : ℕ => |a| * woldCoeff (n + 2) p) =
        fun n : ℕ => |a| * ((p : ℝ)⁻¹ ^ n * woldCoeff 2 p) := by
      funext n
      rw [show n + 2 = 2 + n from Nat.add_comm n 2, woldCoeff_add_eq_inv_pow_mul]
    rw [hfun]
    exact hscaled
  · filter_upwards with n
    intro p
    have hpInv0 : 0 ≤ (p : ℝ)⁻¹ := by positivity
    have hpInv1 : (p : ℝ)⁻¹ ≤ 1 := by
      exact (inv_lt_one_of_one_lt₀ (by exact_mod_cast p.2.one_lt)).le
    have hpow : (p : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ hpInv0 hpInv1
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (abs_nonneg a) (woldCoeff_nonneg (n + 2) p)),
      show n + 2 = 2 + n by omega, woldCoeff_add_eq_inv_pow_mul]
    have hstep : (p : ℝ)⁻¹ ^ n * woldCoeff 2 p ≤ woldCoeff 2 p := by
      calc (p : ℝ)⁻¹ ^ n * woldCoeff 2 p ≤ 1 * woldCoeff 2 p :=
            mul_le_mul_of_nonneg_right hpow (woldCoeff_nonneg 2 p)
        _ = woldCoeff 2 p := one_mul _
    exact mul_le_mul_of_nonneg_left hstep (abs_nonneg a)

/-- Quantitative missing producer.  The exact inverse-depth source transports must have one
depth-independent bound from deep input `ℓ¹` mass to every returned coordinate. -/
def PrimeDepthBVWoldCofinalSourceNormalEquicontinuity
    (sourceDepth : ℕ) (a : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ p : Nat.Primes,
    |primeDepthBVWoldSourceNormalCofinalCenteredTransport sourceDepth (n + 1)
        (fun q => a * woldCoeff (n + 2) q) p| ≤
      C * primeDepthBVWoldCenteredL1Mass a (n + 2)

/-- **Cofinal equicontinuity selector.**  A uniform source-normal inverse-depth bound exists on
the Wold orbit exactly when the centered scalar vanishes. -/
theorem cofinalSourceNormalEquicontinuity_iff_zero
    (sourceDepth : ℕ) (a : ℝ) :
    PrimeDepthBVWoldCofinalSourceNormalEquicontinuity sourceDepth a ↔ a = 0 := by
  constructor
  · rintro ⟨C, _hC, hbound⟩
    let p2 : Nat.Primes := ⟨2, Nat.prime_two⟩
    have htend : Tendsto
        (fun n : ℕ => C * primeDepthBVWoldCenteredL1Mass a (n + 2))
        atTop (nhds 0) := by
      simpa using (primeDepthBVWoldCenteredL1Mass_tendsto_zero a).const_mul C
    have hle : |a * woldCoeff 1 p2| ≤ 0 := by
      apply ge_of_tendsto htend
      filter_upwards with n
      rw [← sourceNormalCofinalCenteredTransport_from_deep a sourceDepth n p2]
      exact hbound n p2
    have hproduct : a * woldCoeff 1 p2 = 0 :=
      abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
    exact (mul_eq_zero.mp hproduct).resolve_right (woldCoeff_pos 1 p2).ne'
  · rintro rfl
    refine ⟨0, le_rfl, ?_⟩
    intro n p
    simp [primeDepthBVWoldSourceNormalCofinalCenteredTransport,
      primeDepthBVWoldCenteredL1Mass]

/-- Xi-labelled form of the quantitative source producer. -/
def PrimeDepthBVWoldXiCofinalSourceNormalEquicontinuity
    (sourceDepth : ℕ) (rho : XiDivisorSupport) : Prop :=
  PrimeDepthBVWoldCofinalSourceNormalEquicontinuity sourceDepth
    (primeDepthBVWoldXiCenteredRate rho)

/-- Pointwise Xi selector: cofinal equicontinuity is exactly critical-line placement. -/
theorem xiCofinalSourceNormalEquicontinuity_iff_re_eq_half
    (sourceDepth : ℕ) (rho : XiDivisorSupport) :
    PrimeDepthBVWoldXiCofinalSourceNormalEquicontinuity sourceDepth rho ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [PrimeDepthBVWoldXiCofinalSourceNormalEquicontinuity,
    cofinalSourceNormalEquicontinuity_iff_zero,
    primeDepthBVWoldXiCenteredRate_eq_zero_iff]

/-- Global cofinal source-normal equicontinuity over the Xi divisor. -/
def PrimeDepthBVWoldXiGlobalCofinalSourceNormalEquicontinuity
    (sourceDepth : ℕ) : Prop :=
  ∀ rho : XiDivisorSupport,
    PrimeDepthBVWoldXiCofinalSourceNormalEquicontinuity sourceDepth rho

/-- Global classifier.  This theorem identifies the exact quantitative producer still required;
it is not an RH proof. -/
theorem xiGlobalCofinalSourceNormalEquicontinuity_iff_riemannHypothesis
    (sourceDepth : ℕ) :
    PrimeDepthBVWoldXiGlobalCofinalSourceNormalEquicontinuity sourceDepth ↔
      RiemannHypothesis := by
  constructor
  · intro h
    apply rh_iff_xi_ne_zero_right.mpr
    intro z hz hzero
    let rho : XiDivisorSupport :=
      ⟨z, mem_xi_divisor_support_of_eq_zero hzero⟩
    have hline : z.re = 1 / 2 :=
      (xiCofinalSourceNormalEquicontinuity_iff_re_eq_half sourceDepth rho).1 (h rho)
    linarith [mem_rightHalf.mp hz]
  · intro hRH rho
    exact (xiCofinalSourceNormalEquicontinuity_iff_re_eq_half sourceDepth rho).2
      (xi_divisor_support_re_eq_half_of_rh hRH rho)

end

end RHTower
