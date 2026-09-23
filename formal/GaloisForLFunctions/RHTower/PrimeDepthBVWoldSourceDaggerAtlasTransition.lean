import GaloisForLFunctions.RHTower.PrimeDepthBVWoldGradedDet2ScalarDescentBoundary
import GaloisForLFunctions.RHTower.MobiusThetaPhysicalParacyclicSourceNullHomology

/-!
# Source-dagger / BV-Wold atlas transition

The Route-R three-depth graded-`det₂` correction and Route-L's source-dagger
mate monodromy are not transverse observations.  At every prime they are
finite-isogenous.  At prime two the Route-R correction is an exact positive
eighth root of the Route-L monodromy.

The same transition rewrites the actual CCM cofinal source-homology defect
as the Route-R anomaly defect times a strictly positive cyclotomic factor.
Consequently these nominally different route outputs have the same radical;
placing them in parallel cannot improve conservativity.  All results are
unconditional and pointwise before any RH quantification.
-/

open Complex

namespace RHTower

noncomputable section

/-- Graded-`det₂` correction on the first three Wold depths at one prime. -/
def primeDepthBVWoldPrimeTriangleAnomaly
    (a : ℝ) (p : Nat.Primes) : ℝ :=
  primeDepthBVWoldGradedDet2Anomaly a (p, 0) (p, 1) (p, 2)

/-- Graded-`det₂` correction on three consecutive depths at one prime. -/
def primeDepthBVWoldPrimeConsecutiveTriangleAnomaly
    (a : ℝ) (p : Nat.Primes) (e : ℕ) : ℝ :=
  primeDepthBVWoldGradedDet2Anomaly a (p, e) (p, e + 1) (p, e + 2)

/-- Every consecutive-depth area is the depth-zero area scaled by `p⁻ᵉ`. -/
theorem primeDepthBVWoldConsecutiveIncrementArea_primeConsecutiveTriangle
    (p : Nat.Primes) (e : ℕ) :
    primeDepthBVWoldConsecutiveIncrementArea
        (p, e) (p, e + 1) (p, e + 2) =
      -(1 - ((p.1 : ℝ)⁻¹)) ^ (3 : ℕ) * ((p.1 : ℝ)⁻¹) ^ e *
        Real.log (p.1 : ℝ) := by
  rw [primeDepthBVWoldConsecutiveIncrementArea_eq_curvature,
    primeDepthBVWoldAdditiveCurvature,
    primeDepthBVWoldConnection, primeDepthBVWoldConnection,
    primeDepthBVWoldConnection,
    primeDepthBVFirstTraceDepthWeight_eq,
    primeDepthBVFirstTraceDepthWeight_eq,
    primeDepthBVFirstTraceDepthWeight_eq,
    xiGammaEulerPrimitivePrimeDepthLogClock_apply,
    xiGammaEulerPrimitivePrimeDepthLogClock_apply,
    xiGammaEulerPrimitivePrimeDepthLogClock_apply]
  push_cast
  ring

/-- Closed form of the all-depth prime-triangle anomaly. -/
theorem primeDepthBVWoldPrimeConsecutiveTriangleAnomaly_eq
    (a : ℝ) (p : Nat.Primes) (e : ℕ) :
    primeDepthBVWoldPrimeConsecutiveTriangleAnomaly a p e =
      Real.exp (a * (1 - ((p.1 : ℝ)⁻¹)) ^ (3 : ℕ) *
        ((p.1 : ℝ)⁻¹) ^ e * Real.log (p.1 : ℝ)) := by
  rw [primeDepthBVWoldPrimeConsecutiveTriangleAnomaly,
    primeDepthBVWoldGradedDet2Anomaly,
    primeDepthBVWoldConsecutiveIncrementArea_primeConsecutiveTriangle]
  congr 1
  ring

/-- Prime-depth anomalies form a coherent Kummer root tower. -/
theorem primeDepthBVWoldPrimeConsecutiveTriangleAnomaly_succ_pow
    (a : ℝ) (p : Nat.Primes) (e : ℕ) :
    primeDepthBVWoldPrimeConsecutiveTriangleAnomaly a p (e + 1) ^ p.1 =
      primeDepthBVWoldPrimeConsecutiveTriangleAnomaly a p e := by
  rw [primeDepthBVWoldPrimeConsecutiveTriangleAnomaly_eq,
    primeDepthBVWoldPrimeConsecutiveTriangleAnomaly_eq,
    ← Real.exp_nat_mul]
  congr 1
  have hp0 : (p.1 : ℝ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  have hcancel : (p.1 : ℝ) * (p.1 : ℝ)⁻¹ = 1 :=
    mul_inv_cancel₀ hp0
  rw [pow_succ ((p.1 : ℝ)⁻¹) e]
  calc
    _ =
      (a * (1 - (p.1 : ℝ)⁻¹) ^ (3 : ℕ) *
          ((p.1 : ℝ)⁻¹) ^ e * Real.log (p.1 : ℝ)) *
        ((p.1 : ℝ) * (p.1 : ℝ)⁻¹) := by ring
    _ = a * (1 - (p.1 : ℝ)⁻¹) ^ (3 : ℕ) *
        ((p.1 : ℝ)⁻¹) ^ e * Real.log (p.1 : ℝ) := by
      rw [hcancel, mul_one]

/-- The scalar anomaly root tower is strictly coherent at every finite
depth, so it carries no higher same-prime power-associator defect. -/
theorem primeDepthBVWoldPrimeConsecutiveTriangleAnomaly_add_pow
    (a : ℝ) (p : Nat.Primes) (e k : ℕ) :
    primeDepthBVWoldPrimeConsecutiveTriangleAnomaly a p (e + k) ^
        (p.1 ^ k) =
      primeDepthBVWoldPrimeConsecutiveTriangleAnomaly a p e := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.add_succ, pow_succ p.1 k, mul_comm, pow_mul,
        primeDepthBVWoldPrimeConsecutiveTriangleAnomaly_succ_pow,
        ih]

/-- Every depth level is finite-isogenous to the same Route-L mate gain. -/
theorem primeDepthBVWoldPrimeConsecutiveTriangleAnomaly_pow_eq_mateGain_pow
    (s : ℂ) (p : Nat.Primes) (e : ℕ) :
    primeDepthBVWoldPrimeConsecutiveTriangleAnomaly
          (2 * s.re - 1) p e ^ (p.1 ^ (e + 3)) =
      deningerHalfDensityMateGain p.1 s ^ ((p.1 - 1) ^ (3 : ℕ)) := by
  rw [primeDepthBVWoldPrimeConsecutiveTriangleAnomaly_eq,
    deningerHalfDensityMateGain,
    ← Real.exp_nat_mul, ← Real.exp_nat_mul]
  congr 1
  have hp1 : 1 ≤ p.1 := p.2.one_le
  rw [Nat.cast_pow, Nat.cast_pow, Nat.cast_sub hp1, inv_pow]
  have hp0 : (p.1 : ℝ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  field_simp [hp0]
  ring

/-- Every level of the scalar Kummer tower has the same critical-line
triviality radical. -/
theorem primeDepthBVWoldPrimeConsecutiveTriangleAnomaly_eq_one_iff_re_eq_half
    (s : ℂ) (p : Nat.Primes) (e : ℕ) :
    primeDepthBVWoldPrimeConsecutiveTriangleAnomaly
        (2 * s.re - 1) p e = 1 ↔
      s.re = 1 / 2 := by
  rw [primeDepthBVWoldPrimeConsecutiveTriangleAnomaly_eq,
    Real.exp_eq_one_iff]
  have hp1 : (1 : ℝ) < p.1 := by exact_mod_cast p.2.one_lt
  have hb : 0 < 1 - ((p.1 : ℝ)⁻¹) :=
    sub_pos.mpr (inv_lt_one_of_one_lt₀ hp1)
  have hlog : 0 < Real.log (p.1 : ℝ) := Real.log_pos hp1
  have hcoeff :
      0 < (1 - ((p.1 : ℝ)⁻¹)) ^ (3 : ℕ) *
        ((p.1 : ℝ)⁻¹) ^ e * Real.log (p.1 : ℝ) := by
    positivity
  rw [show
    (2 * s.re - 1) * (1 - ((p.1 : ℝ)⁻¹)) ^ (3 : ℕ) *
        ((p.1 : ℝ)⁻¹) ^ e * Real.log (p.1 : ℝ) =
      (2 * s.re - 1) *
        ((1 - ((p.1 : ℝ)⁻¹)) ^ (3 : ℕ) *
          ((p.1 : ℝ)⁻¹) ^ e * Real.log (p.1 : ℝ)) by ring,
    mul_eq_zero]
  simp only [ne_of_gt hcoeff, or_false]
  constructor <;> intro h <;> linarith

/-- Depth zero recovers the original prime triangle. -/
theorem primeDepthBVWoldPrimeConsecutiveTriangleAnomaly_zero
    (a : ℝ) (p : Nat.Primes) :
    primeDepthBVWoldPrimeConsecutiveTriangleAnomaly a p 0 =
      primeDepthBVWoldPrimeTriangleAnomaly a p := by
  rfl

/-- The all-prime three-depth area is the cube of the Wold boundary mass
times the prime log-clock, with negative orientation. -/
theorem primeDepthBVWoldConsecutiveIncrementArea_primeTriangle
    (p : Nat.Primes) :
    primeDepthBVWoldConsecutiveIncrementArea (p, 0) (p, 1) (p, 2) =
      -(1 - ((p.1 : ℝ)⁻¹)) ^ (3 : ℕ) * Real.log (p.1 : ℝ) := by
  rw [primeDepthBVWoldConsecutiveIncrementArea_eq_curvature,
    primeDepthBVWoldAdditiveCurvature,
    primeDepthBVWoldConnection, primeDepthBVWoldConnection,
    primeDepthBVWoldConnection,
    primeDepthBVFirstTraceDepthWeight_eq,
    primeDepthBVFirstTraceDepthWeight_eq,
    primeDepthBVFirstTraceDepthWeight_eq,
    xiGammaEulerPrimitivePrimeDepthLogClock_apply,
    xiGammaEulerPrimitivePrimeDepthLogClock_apply,
    xiGammaEulerPrimitivePrimeDepthLogClock_apply]
  norm_num
  ring

/-- Closed form of the prime-triangle anomaly. -/
theorem primeDepthBVWoldPrimeTriangleAnomaly_eq
    (a : ℝ) (p : Nat.Primes) :
    primeDepthBVWoldPrimeTriangleAnomaly a p =
      Real.exp (a * (1 - ((p.1 : ℝ)⁻¹)) ^ (3 : ℕ) * Real.log (p.1 : ℝ)) := by
  rw [primeDepthBVWoldPrimeTriangleAnomaly,
    primeDepthBVWoldGradedDet2Anomaly,
    primeDepthBVWoldConsecutiveIncrementArea_primeTriangle]
  congr 1
  ring

/-- Route-R anomaly and Route-L mate monodromy are primewise
finite-isogenous. -/
theorem primeDepthBVWoldPrimeTriangleAnomaly_pow_eq_mateGain_pow
    (s : ℂ) (p : Nat.Primes) :
    primeDepthBVWoldPrimeTriangleAnomaly (2 * s.re - 1) p ^ (p.1 ^ (3 : ℕ)) =
      deningerHalfDensityMateGain p.1 s ^ ((p.1 - 1) ^ (3 : ℕ)) := by
  rw [primeDepthBVWoldPrimeTriangleAnomaly_eq,
    deningerHalfDensityMateGain,
    ← Real.exp_nat_mul, ← Real.exp_nat_mul]
  congr 1
  have hp1 : 1 ≤ p.1 := p.2.one_le
  rw [Nat.cast_pow, Nat.cast_pow, Nat.cast_sub hp1]
  have hp0 : (p.1 : ℝ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  field_simp [hp0]
  ring

/-- Every prime chart has the same triviality radical on centered rate. -/
theorem primeDepthBVWoldPrimeTriangleAnomaly_eq_one_iff_mateGain
    (s : ℂ) (p : Nat.Primes) :
    primeDepthBVWoldPrimeTriangleAnomaly (2 * s.re - 1) p = 1 ↔
      deningerHalfDensityMateGain p.1 s = 1 := by
  rw [primeDepthBVWoldPrimeTriangleAnomaly_eq,
    deningerHalfDensityMateGain, Real.exp_eq_one_iff,
    Real.exp_eq_one_iff]
  have hp1 : (1 : ℝ) < p.1 := by exact_mod_cast p.2.one_lt
  have hb : 1 - ((p.1 : ℝ)⁻¹) ≠ 0 :=
    ne_of_gt (sub_pos.mpr (inv_lt_one_of_one_lt₀ hp1))
  constructor
  · intro h
    have h' : (1 - ((p.1 : ℝ)⁻¹)) ^ (3 : ℕ) *
        ((2 * s.re - 1) * Real.log (p.1 : ℝ)) = 0 := by
      calc
        _ = (2 * s.re - 1) * (1 - ((p.1 : ℝ)⁻¹)) ^ (3 : ℕ) *
            Real.log (p.1 : ℝ) := by ring
        _ = 0 := h
    exact (mul_eq_zero.mp h').resolve_left (pow_ne_zero 3 hb)
  · intro h
    calc
      (2 * s.re - 1) * (1 - ((p.1 : ℝ)⁻¹)) ^ (3 : ℕ) *
          Real.log (p.1 : ℝ) =
        (1 - ((p.1 : ℝ)⁻¹)) ^ (3 : ℕ) *
          ((2 * s.re - 1) * Real.log (p.1 : ℝ)) := by ring
      _ = 0 := by rw [h, mul_zero]

/-- At prime two, the Route-R anomaly is an exact eighth root of Route-L
mate monodromy. -/
theorem primeDepthBVWoldPrimeTwoTriangleAnomaly_pow_eight
    (s : ℂ) :
    primeDepthBVWoldPrimeTriangleAnomaly (2 * s.re - 1)
        ⟨2, Nat.prime_two⟩ ^ (8 : ℕ) =
      deningerHalfDensityMateGain 2 s := by
  simpa using
    primeDepthBVWoldPrimeTriangleAnomaly_pow_eq_mateGain_pow s
      ⟨2, Nat.prime_two⟩

/-- Dyadic Route-R anomaly and Route-L mate monodromy have the same
triviality locus. -/
theorem primeDepthBVWoldPrimeTwoTriangleAnomaly_eq_one_iff_mateGain
    (s : ℂ) :
    primeDepthBVWoldPrimeTriangleAnomaly (2 * s.re - 1)
        ⟨2, Nat.prime_two⟩ = 1 ↔
      deningerHalfDensityMateGain 2 s = 1 := by
  rw [primeDepthBVWoldPrimeTriangleAnomaly_eq,
    deningerHalfDensityMateGain, Real.exp_eq_one_iff,
    Real.exp_eq_one_iff]
  norm_num

/-- The common anomaly/monodromy radical is exactly the critical line. -/
theorem primeDepthBVWoldPrimeTriangleAnomaly_eq_one_iff_re_eq_half
    (s : ℂ) (p : Nat.Primes) :
    primeDepthBVWoldPrimeTriangleAnomaly (2 * s.re - 1) p = 1 ↔
      s.re = 1 / 2 := by
  exact
    (primeDepthBVWoldPrimeTriangleAnomaly_eq_one_iff_mateGain s p).trans
      (deningerHalfDensityMateGain_eq_one_iff_re_eq_half p.2.two_le s)

/-- Positive dyadic transition factor relating the anomaly defect to its
eighth-power monodromy defect. -/
def primeDepthBVWoldPrimeTwoCyclotomicAmplifier (s : ℂ) : ℝ :=
  let A := primeDepthBVWoldPrimeTriangleAnomaly (2 * s.re - 1)
    ⟨2, Nat.prime_two⟩
  A ^ (7 : ℕ) + A ^ (6 : ℕ) + A ^ (5 : ℕ) + A ^ (4 : ℕ) + A ^ (3 : ℕ) + A ^ (2 : ℕ) + A + 1

theorem primeDepthBVWoldPrimeTwoCyclotomicAmplifier_pos (s : ℂ) :
    0 < primeDepthBVWoldPrimeTwoCyclotomicAmplifier s := by
  rw [primeDepthBVWoldPrimeTwoCyclotomicAmplifier]
  have hA : 0 < primeDepthBVWoldPrimeTriangleAnomaly (2 * s.re - 1)
      ⟨2, Nat.prime_two⟩ := by
    rw [primeDepthBVWoldPrimeTriangleAnomaly_eq]
    exact Real.exp_pos _
  positivity

theorem primeDepthBVWoldPrimeTwoTriangleAnomaly_pow_sub_one_factor
    (s : ℂ) :
    primeDepthBVWoldPrimeTriangleAnomaly (2 * s.re - 1)
          ⟨2, Nat.prime_two⟩ ^ (8 : ℕ) - 1 =
      (primeDepthBVWoldPrimeTriangleAnomaly (2 * s.re - 1)
          ⟨2, Nat.prime_two⟩ - 1) *
        primeDepthBVWoldPrimeTwoCyclotomicAmplifier s := by
  rw [primeDepthBVWoldPrimeTwoCyclotomicAmplifier]
  ring

/-- Actual CCM cofinal source-homology readout at clock two is the Route-R
anomaly defect times a strictly positive cyclotomic transition. -/
theorem ccmMobiusThetaCofinalSourceHomologyLanding_readout_eq_anomalyFactor
    (k m : ℕ) (s w : ℂ)
    (x : CCMRationalAdelicDegreeOneCyclicSource) :
    tateClockCofinalRelativeH1Equiv m
        (ccmMobiusThetaCofinalSourceHomologyLanding 2 k m s w x) =
      (((primeDepthBVWoldPrimeTriangleAnomaly (2 * s.re - 1)
            ⟨2, Nat.prime_two⟩ - 1) *
          primeDepthBVWoldPrimeTwoCyclotomicAmplifier s : ℝ) : ℂ) *
        iteratedDeriv k XiC w * ccmRationalAdelicDegreeOneTrace x := by
  rw [ccmMobiusThetaCofinalSourceHomologyLanding_readout]
  have hpow := primeDepthBVWoldPrimeTwoTriangleAnomaly_pow_eight s
  have hpowC := congrArg (fun y : ℝ => (y : ℂ)) hpow
  have hfactor :=
    primeDepthBVWoldPrimeTwoTriangleAnomaly_pow_sub_one_factor s
  have hfactorC := congrArg (fun y : ℝ => (y : ℂ)) hfactor
  push_cast at hpowC ⊢
  push_cast at hfactorC
  rw [← hpowC, hfactorC]

end

end RHTower
