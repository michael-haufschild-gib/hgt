import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesGlobalMeanFirstTrace

open Real Set Filter Topology
open scoped BigOperators
noncomputable section
namespace RHTower.HedenmalmThetaSource

/-- Root-scale coefficient of the literal cofinal source majorant. -/
def gammaSewnCriticalPluckerRootBudgetConstant : ℝ :=
  Real.sqrt ((368640 * gammaSewnCriticalAdjacentPrime_aperture ^ 2 /
    gammaSewnCriticalAdjacentPrime_gap ^ 4) /
      gammaSewnCriticalAdjacentPrime_CofinalDenominator)

theorem sqrt_gammaSewnCriticalAdjacentPrime_PluckerBlockWeight_le (z : ℕ × ℕ) :
    Real.sqrt (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z) ≤
      gammaSewnCriticalPluckerRootBudgetConstant *
        (1 / gammaSewnCriticalAdjacentPrime_depthScale z.1) *
        (Real.log (gammaSewnCriticalAdjacentPrime_lower z.2 : ℝ) ^ 2 /
          (gammaSewnCriticalAdjacentPrime_lower z.2 : ℝ) ^ 2) := by
  let C := 368640 * gammaSewnCriticalAdjacentPrime_aperture ^ 2 /
    gammaSewnCriticalAdjacentPrime_gap ^ 4
  let D := gammaSewnCriticalAdjacentPrime_CofinalDenominator
  let c := gammaSewnCriticalAdjacentPrime_depthScale z.1
  let p : ℝ := gammaSewnCriticalAdjacentPrime_lower z.2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hD : 0 < D := gammaSewnCriticalAdjacentPrime_CofinalDenominator_pos
  have hc : 0 < c := gammaSewnCriticalAdjacentPrime_depthScale_pos _
  have hle := div_le_div_of_nonneg_right (criticalAdjacent_denominatorTerm_le z) hD.le
  change gammaSewnCriticalAdjacentPrime_DenominatorTerm z / D ≤
    (C * (1 / c ^ 2) * (Real.log p ^ 4 / p ^ 4)) / D at hle
  have hsq : gammaSewnCriticalPluckerRootBudgetConstant ^ 2 = C / D :=
    Real.sq_sqrt (div_nonneg hC hD.le)
  apply (Real.sqrt_le_iff).2
  constructor
  · exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (by positivity)) (by positivity)
  · change gammaSewnCriticalAdjacentPrime_DenominatorTerm z / D ≤
      (gammaSewnCriticalPluckerRootBudgetConstant * (1 / c) * (Real.log p ^ 2 / p ^ 2)) ^ 2
    rw [mul_pow, mul_pow, hsq]
    convert hle using 1; ring

set_option maxHeartbeats 800000 in
theorem summable_gammaSewnCriticalPluckerRootBudgetMajor :
    Summable (fun z : ℕ × ℕ =>
      (1 / gammaSewnCriticalAdjacentPrime_depthScale z.1 ^ 2) *
        (Real.log (gammaSewnCriticalAdjacentPrime_lower z.2 : ℝ) ^ 2 /
          (gammaSewnCriticalAdjacentPrime_lower z.2 : ℝ) ^ 2)) := by
  have he : Summable (fun e : ℕ => 1 / gammaSewnCriticalAdjacentPrime_depthScale e ^ 2) := by
    have h := (Real.summable_one_div_nat_add_rpow (1 / 2) 2).mpr
      (by norm_num : (1 : ℝ) < 2)
    exact h.congr fun e => by simp [gammaSewnCriticalAdjacentPrime_depthScale]
  have hp : Summable (fun n : ℕ =>
      Real.log (gammaSewnCriticalAdjacentPrime_lower n : ℝ) ^ 2 /
        (gammaSewnCriticalAdjacentPrime_lower n : ℝ) ^ 2) := by
    have hnat := HTGeometry.summable_log_pow_div_nat_rpow 2
      (sigma := (2 : ℝ)) (by norm_num)
    have hprime : Summable (fun p : Nat.Primes => Real.log (p : ℝ) ^ 2 / (p : ℝ) ^ 2) := by
      refine (hnat.subtype (fun n : ℕ => n.Prime)).congr fun p => ?_
      simp [Function.comp_apply]
    exact hprime.comp_injective RHTower.nthPrimeSubtype_injective
  exact summable_mul_of_summable_norm he.norm hp.norm

/-- Depth-sensitive coefficient-root mass. The bare square roots of the block weights are not
used: reciprocal depth is retained before summation. -/
theorem summable_sqrt_gammaSewnCriticalAdjacentPrime_PluckerBlockWeight_div_depth :
    Summable (fun z : ℕ × ℕ =>
      Real.sqrt (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z) / ((z.1 : ℝ) + 1)) := by
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun z => ?_)
    (summable_gammaSewnCriticalPluckerRootBudgetMajor.mul_left
      gammaSewnCriticalPluckerRootBudgetConstant)
  have hz := sqrt_gammaSewnCriticalAdjacentPrime_PluckerBlockWeight_le z
  have hc : 0 < gammaSewnCriticalAdjacentPrime_depthScale z.1 :=
    gammaSewnCriticalAdjacentPrime_depthScale_pos _
  have hce : gammaSewnCriticalAdjacentPrime_depthScale z.1 ≤ (z.1 : ℝ) + 1 := by
    unfold gammaSewnCriticalAdjacentPrime_depthScale
    linarith
  calc
    _ ≤ Real.sqrt (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z) /
        gammaSewnCriticalAdjacentPrime_depthScale z.1 :=
      div_le_div_of_nonneg_left (Real.sqrt_nonneg _) hc hce
    _ ≤ (gammaSewnCriticalPluckerRootBudgetConstant *
        (1 / gammaSewnCriticalAdjacentPrime_depthScale z.1) *
        (Real.log (gammaSewnCriticalAdjacentPrime_lower z.2 : ℝ) ^ 2 /
          (gammaSewnCriticalAdjacentPrime_lower z.2 : ℝ) ^ 2)) /
        gammaSewnCriticalAdjacentPrime_depthScale z.1 :=
      div_le_div_of_nonneg_right hz hc.le
    _ = _ := by ring

theorem sqrt_gammaSewnCriticalPrimeDepthPacket_node_le_depth
    (e : ℕ) (p q : Nat.Primes) (i : Fin 4) :
    Real.sqrt (gammaSewnCriticalPrimeDepthPacket_node e p q i) ≤
      (Real.log 2)⁻¹ / ((e : ℝ) + 1) := by
  have hp (p : Nat.Primes) (k : ℕ) :
      Real.sqrt (RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode
        (1 / 2) (p, k)) ≤ (Real.log 2)⁻¹ / ((k : ℝ) + 1) := by
    rw [RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode_depth_eq,
      Real.sqrt_div (RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode_pos
        (by norm_num) _).le, Real.sqrt_sq (by positivity)]
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply (Real.sqrt_le_iff).2
    exact ⟨by positivity,
      RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode_le
        (by norm_num) (by norm_num) _⟩
  have hs (p : Nat.Primes) :
      Real.sqrt (RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode
        (1 / 2) (p, e + 1)) ≤ (Real.log 2)⁻¹ / ((e : ℝ) + 1) := by
    refine (hp p (e + 1)).trans ?_
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by push_cast; linarith)
  fin_cases i
  · exact hp p e
  · exact hs p
  · exact hp q e
  · exact hs q

/-- Literal prime-depth incidence roots are summable, preserving all four coordinates. -/
theorem summable_gammaSewnCriticalPluckerRootIncidence (i : Fin 4) :
    Summable (fun z : ℕ × ℕ =>
      Real.sqrt (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z) *
        Real.sqrt (gammaSewnCriticalPrimeDepthPacket_node z.1
          (gammaSewnCriticalAdjacentPrime_lower z.2)
          (gammaSewnCriticalAdjacentPrime_upper z.2) i)) := by
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun z => ?_)
    (summable_sqrt_gammaSewnCriticalAdjacentPrime_PluckerBlockWeight_div_depth.mul_right
      (Real.log 2)⁻¹)
  calc
    _ ≤ Real.sqrt (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z) *
        ((Real.log 2)⁻¹ / ((z.1 : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left (sqrt_gammaSewnCriticalPrimeDepthPacket_node_le_depth _ _ _ i)
        (Real.sqrt_nonneg _)
    _ = _ := by ring

end RHTower.HedenmalmThetaSource
