import GaloisForLFunctions.RHTower.XiCoordinate
import GaloisForLFunctions.RHTower.BesselWeightedPrimitive

/-!
# The compact-range primitive transported to the exterior variable

The bounded-radius weighted Bessel primitive is proved in the phase variable.  The Dunster
substitution carries it to the exterior variable, where the integrand is the speed-weighted Bessel
form of the Liouville–Green model.  The transport is exact: the phase of the compact exterior range
`[1,2]` stays below `2`, which is precisely the radius bound the estimate needs.

With the model's own `sqrt c` normalization the rate is `1/c`, one full power of the frequency,
rather than the `c^{-3/2}` of the phase-variable statement.
-/

noncomputable section

open Set

namespace GaloisForLFunctions.RHTower

/-- **The transported primitive.**  The speed-weighted Bessel integral over a compact exterior range
is of size `c^{-3/2}`, uniformly in the endpoint. -/
theorem abs_integral_xiTransported_le {s X c M : ℝ} {B B' : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hX1 : 1 ≤ X) (hX2 : X ≤ 2) (hc : 0 < c)
    (hB : ∀ r ∈ uIcc (0 : ℝ) (xiEndpointPhase s X), HasDerivAt B (B' r) r)
    (hB'c : ContinuousOn B' (uIcc (0 : ℝ) (xiEndpointPhase s X)))
    (hMB : ∀ r ∈ uIcc (0 : ℝ) (xiEndpointPhase s X), |B r| ≤ M)
    (hMB' : ∀ r ∈ uIcc (0 : ℝ) (xiEndpointPhase s X), |B' r| ≤ M) :
    |∫ x in (1 : ℝ)..X, xiSpeed s x *
        (xiEndpointPhase s x * B (xiEndpointPhase s x)
          * besselJ0 (c * xiEndpointPhase s x))|
      ≤ 648 * M / (c * Real.sqrt c) := by
  have hR0 : 0 ≤ xiEndpointPhase s X := by
    rw [← xiEndpointPhase_one s]
    exact (strictMonoOn_xiEndpointPhase hs0 hs1).monotoneOn (mem_Ici.mpr le_rfl)
      (mem_Ici.mpr hX1) hX1
  have hR : xiEndpointPhase s X ≤ 2 := xiEndpointPhase_le_two hs0 (by linarith) hX1 hX2
  rw [← intervalIntegral_comp_xiEndpointPhase hs0 hs1 hX1
    (fun r : ℝ => r * B r * besselJ0 (c * r))]
  exact abs_integral_mul_besselJ0_le hc hR0 hR hB hB'c hMB hMB'

/-- **The normalized transported primitive.**  With the model's `sqrt c` normalization the rate is
one full power of the frequency, which is the form the compact endpoint estimate takes. -/
theorem abs_integral_xiTransported_normalized_le {s X c M : ℝ} {B B' : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hX1 : 1 ≤ X) (hX2 : X ≤ 2) (hc : 0 < c)
    (hB : ∀ r ∈ uIcc (0 : ℝ) (xiEndpointPhase s X), HasDerivAt B (B' r) r)
    (hB'c : ContinuousOn B' (uIcc (0 : ℝ) (xiEndpointPhase s X)))
    (hMB : ∀ r ∈ uIcc (0 : ℝ) (xiEndpointPhase s X), |B r| ≤ M)
    (hMB' : ∀ r ∈ uIcc (0 : ℝ) (xiEndpointPhase s X), |B' r| ≤ M) :
    |∫ x in (1 : ℝ)..X, Real.sqrt c * (xiSpeed s x *
        (xiEndpointPhase s x * B (xiEndpointPhase s x)
          * besselJ0 (c * xiEndpointPhase s x)))|
      ≤ 648 * M / c := by
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hss : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc.le
  have hbase := abs_integral_xiTransported_le hs0 hs1 hX1 hX2 hc hB hB'c hMB hMB'
  rw [intervalIntegral.integral_const_mul, abs_mul, abs_of_pos hsc]
  have hM0 : 0 ≤ M := by
    have h0 : (0 : ℝ) ∈ uIcc (0 : ℝ) (xiEndpointPhase s X) := left_mem_uIcc
    exact le_trans (abs_nonneg (B 0)) (hMB 0 h0)
  have hstep : Real.sqrt c * |∫ x in (1 : ℝ)..X, xiSpeed s x *
      (xiEndpointPhase s x * B (xiEndpointPhase s x)
        * besselJ0 (c * xiEndpointPhase s x))|
      ≤ Real.sqrt c * (648 * M / (c * Real.sqrt c)) :=
    mul_le_mul_of_nonneg_left hbase hsc.le
  refine le_trans hstep (le_of_eq ?_)
  field_simp

end GaloisForLFunctions.RHTower
