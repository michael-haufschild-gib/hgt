import GaloisForLFunctions.RHTower.CCM.CCMPrimeDeficitBoundaryNoetherBalance

/-!
# Reflected impulse work of the actual Möbius field

The critical boundary defect is the sum of each actual momentum impulse
against the field at its reflected time. This is an exact signed work
formula; no decorrelation or favorable sign is assumed.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace RHTower

def ccmPrimeDeficitBoundaryImpulseWork (m k : ℕ) (T : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 (m + 3 * k),
    logarithmicLongTail m moebiusCoeff n * Real.exp (-(Real.log n / 2)) *
      ccmPrimeDeficitBoundaryPosition m k (T - Real.log n)

theorem mellinPrefix_reflectedCurrent_entry_jump
    (w v : ℕ → ℝ) (N M : ℕ) (T : ℝ) :
    mellinPrefixPosition w N (T - Real.log (M + 1 : ℕ)) *
        mellinPrefixMomentum v (M + 1) (Real.log (M + 1 : ℕ)) -
      mellinPrefixPosition w N (T - Real.log (M + 1 : ℕ)) *
        mellinPrefixMomentum v M (Real.log (M + 1 : ℕ)) =
      v (M + 1) * Real.exp (-(Real.log (M + 1 : ℕ) / 2)) *
        mellinPrefixPosition w N (T - Real.log (M + 1 : ℕ)) := by
  rw [← mul_sub, mellinPrefixMomentum_entry_jump]
  ring

theorem ccmPrimeDeficitBoundaryImpulseWork_eq_reflection (m k : ℕ) (T : ℝ) :
    ccmPrimeDeficitBoundaryImpulseWork m k T = Real.exp (-(T / 2)) *
      ∫ s in (0 : ℝ)..T, ccmPrimeDeficitBoundaryExpProfile m k s *
        ccmPrimeDeficitBoundaryCountProfile m k (T - s) := by
  unfold ccmPrimeDeficitBoundaryImpulseWork ccmPrimeDeficitBoundaryExpProfile
    ccmPrimeDeficitBoundaryCountProfile
  rw [integral_logarithmicFiniteExponentialEntry_pair]
  simp_rw [ccmPrimeDeficitBoundaryPosition_eq_ramp_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  have hap : (0 : ℝ) < a := by exact_mod_cast (Finset.mem_Icc.mp ha).1
  have hbp : (0 : ℝ) < b := by exact_mod_cast (Finset.mem_Icc.mp hb).1
  have he : Real.exp (-(Real.log a / 2)) * Real.exp (-((T - Real.log a) / 2)) =
      Real.exp (-(T / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [Nat.cast_mul, Real.log_mul hap.ne' hbp.ne', sub_add_eq_sub_sub]
  calc
    _ = (Real.exp (-(Real.log a / 2)) * Real.exp (-((T - Real.log a) / 2))) *
        (logarithmicLongTail m moebiusCoeff a * logarithmicLongTail m moebiusCoeff b *
          logarithmicExponentialRamp (T - Real.log a - Real.log b)) := by ring
    _ = _ := by rw [he]

/-- The full signed normalized defect is literal reflected impulse work. -/
theorem ccmLogChebyshevDeficitPrimitive_sub_truncatedAction_critical_eq_impulseWork
    {m k : ℕ} (hm : 0 < m) (hk : 3 * k ≤ m) {T : ℝ} (h0 : 0 ≤ T)
    (hT : T ≤ 2 * Real.log (m + k : ℕ)) :
    Real.exp (-(T / 2)) *
      (ccmLogChebyshevDeficitPrimitive T - ccmPrimeDeficitTruncatedAction m T) =
        ccmPrimeDeficitBoundaryImpulseWork m k T := by
  rw [ccmPrimeDeficitBoundaryImpulseWork_eq_reflection,
    ccmLogChebyshevDeficitPrimitive_sub_truncatedAction_eq_reflection hm hk h0 hT]

end RHTower
