import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.CoprimePrimeChargeTail
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.CoprimePrimeChargeScales
import GaloisForLFunctions.ArithmeticCouplingTheory.ReceivingCharges.CompleteFormMoments

/-!
# The fixed-mode part of the receiving tail vanishes

The product rule leaves the prime input multiplied by the fixed mode's
unfinished generator. Its pointwise square is bounded independently of
the horizon. The prime incidence moment therefore makes this entire
remainder tend to zero even before physical normalization.
-/

noncomputable section

open Finset Filter Topology
open scoped Classical

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory RenormalizedArithmeticPotentialTheory
  ArithmeticIntersectionTheory SelectiveMultiscaleArithmeticPositivity

/-- A fixed conductor's horizon-independent square bound for its own tail. -/
def fibreModeTailCost (m : ℕ) : ℝ :=
  2 * sourceBound m ^ 2 +
    2 * primeActivityMass m * ((m : ℝ) * (Real.log m + tameDifferent m))

theorem fibreModeTailCost_nonneg (m : ℕ) : 0 ≤ fibreModeTailCost m := by
  have hD := tameDifferent_nonneg m
  have hA := primeActivityMass_nonneg m
  have hL := Real.log_natCast_nonneg m
  unfold fibreModeTailCost
  positivity

/-- The small prime input multiplying the receiving conductor's own tail. -/
def fibreBaseTailProfile (m Q N : ℕ) (t : ℝ) (n : ℕ) : ℝ :=
  incidencePacket (fibrePrimes m Q) (fun _ => t / fibreScale m Q) n *
    normalizedModeDilationTail m (N / n) n

/-- The base-mode tail costs only the harmonic incidence moment of its prime input. -/
theorem fibreBaseTailProfile_norm_sq_le {m : ℕ} (hm : 0 < m)
    (Q N : ℕ) (t : ℝ) :
    ‖packetVector (fibreBaseTailProfile m Q N t) N‖ ^ 2 ≤
      fibreModeTailCost m * (t / fibreScale m Q) ^ 2 * harmonicMass N *
        (4 * (∑ p ∈ fibrePrimes m Q, 1 / (p : ℝ)) ^ 2 +
          2 * ∑ p ∈ fibrePrimes m Q, 1 / (p : ℝ)) := by
  rw [packetVector_norm_sq]
  calc
    _ ≤ fibreModeTailCost m * ∑ n ∈ Icc 1 N,
        incidencePacket (fibrePrimes m Q) (fun _ => t / fibreScale m Q) n ^ 2 / (n : ℝ) := by
      rw [mul_sum]
      apply sum_le_sum
      intro n _
      rw [fibreBaseTailProfile, mul_pow]
      exact (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (normalizedModeDilationTail_sq_le hm (N / n) n)
          (sq_nonneg _)) (Nat.cast_nonneg n)).trans_eq (by dsimp only [fibreModeTailCost]; ring)
    _ ≤ _ := (mul_le_mul_of_nonneg_left
      (incidencePacket_const_harmonic_square_le (P := fibrePrimes m Q)
        (fun p hp => (mem_fibrePrimes.mp hp).2.1) (t / fibreScale m Q) N)
      (fibreModeTailCost_nonneg m)).trans_eq (by ring)

/-- The unnormalized fixed-mode tail term already tends to zero on coherent polynomial families. -/
theorem tendsto_fibreBaseTailProfile_norm_sq {m : ℕ} (hm : 0 < m)
    {a d : ℕ} (ha : 0 < a) (had : a ≤ d) (t : ℝ) :
    Tendsto (fun X : ℕ =>
      ‖packetVector (fibreBaseTailProfile m (X ^ a) (X ^ d) t) (X ^ d)‖ ^ 2)
      atTop (𝓝 0) := by
  have hlim := (tendsto_fibreIncidencePolynomialMoment_cost hm ha had t
    (r := 0) (by norm_num)).const_mul (fibreModeTailCost m)
  simp only [Real.rpow_zero, one_mul, mul_zero] at hlim
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [] with X
  have hH : harmonicMass (X ^ d) ≤ Real.log (X ^ d : ℕ) + 1 := by
    have h := harmonic_le_one_add_log (X ^ d)
    have he : (harmonic (X ^ d) : ℝ) = harmonicMass (X ^ d) := by
      simpa only [harmonicMass, one_div] using
        _root_.RHTower.RegularizedDivisorHarmonic.harmonic_cast_eq_sum (X ^ d)
    rw [he] at h
    linarith only [h]
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  refine (fibreBaseTailProfile_norm_sq_le hm (X ^ a) (X ^ d) t).trans ?_
  have h := mul_le_mul_of_nonneg_left hH
    (show 0 ≤ fibreModeTailCost m * (t / fibreScale m (X ^ a)) ^ 2 by
      exact mul_nonneg (fibreModeTailCost_nonneg m) (sq_nonneg _))
  exact (mul_le_mul_of_nonneg_right h
    (show 0 ≤ 4 * (∑ p ∈ fibrePrimes m (X ^ a), 1 / (p : ℝ)) ^ 2 +
      2 * ∑ p ∈ fibrePrimes m (X ^ a), 1 / (p : ℝ) by positivity)).trans_eq (by ring)

/-- Physical coordinates of the vanishing fixed-mode tail term. -/
def fibreBaseTailVector (m Q N : ℕ) (t : ℝ) : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  (Real.sqrt (Real.log N))⁻¹ • packetVector (fibreBaseTailProfile m Q N t) N

theorem fibreBaseTailVector_norm_sq (m Q N : ℕ) (t : ℝ) :
    ‖fibreBaseTailVector m Q N t‖ ^ 2 =
      ‖packetVector (fibreBaseTailProfile m Q N t) N‖ ^ 2 / Real.log N := by
  rw [fibreBaseTailVector, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    inv_pow, Real.sq_sqrt (Real.log_natCast_nonneg N)]
  ring

/-- The base-mode term disappears in physical norm. -/
theorem tendsto_fibreBaseTailVector_norm {m : ℕ} (hm : 0 < m)
    {a d : ℕ} (ha : 0 < a) (had : a ≤ d) (t : ℝ) :
    Tendsto (fun X : ℕ => ‖fibreBaseTailVector m (X ^ a) (X ^ d) t‖) atTop (𝓝 0) := by
  have hNd : Tendsto (fun X : ℕ => X ^ d) atTop atTop :=
    tendsto_pow_atTop (ha.trans_le had).ne'
  have hsq : Tendsto (fun X : ℕ => ‖fibreBaseTailVector m (X ^ a) (X ^ d) t‖ ^ 2)
      atTop (𝓝 0) := by
    simpa only [fibreBaseTailVector_norm_sq, Function.comp_def] using
      (tendsto_fibreBaseTailProfile_norm_sq hm ha had t).div_atTop
        ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).comp hNd)
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsq.sqrt

#print axioms fibreBaseTailProfile_norm_sq_le
#print axioms tendsto_fibreBaseTailVector_norm

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
