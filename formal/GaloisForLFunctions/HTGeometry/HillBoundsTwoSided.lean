import GaloisForLFunctions.HTGeometry.HillEnergyTwoSided
import GaloisForLFunctions.HTGeometry.HillMassiveFrequency

/-!
# The fibrewise bounds in both time directions

The pointwise bounds on the oscillator were proved on a forward interval. With the two-sided energy
estimate they hold for every time, with `|t|` in the exponential — which is what a probe needs, since
it must be nonvanishing on a two-sided neighbourhood of its event.

The frequency behaviour is unchanged: the datum `(1,0)` still costs nothing in the frequency, and its
velocity still costs one power.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

section Generic

variable {ω dω u du ddu : ℝ → ℝ} {K : ℝ}

/-- The square root of the energy, bounded in both directions. -/
theorem sqrt_hillEnergy_le_abs (hω : ∀ t, HasDerivAt ω (dω t) t) (hu : ∀ t, HasDerivAt u (du t) t)
    (hdu : ∀ t, HasDerivAt du (ddu t) t) (heq : ∀ t, ddu t + ω t ^ 2 * u t = 0)
    (hωpos : ∀ t, 0 < ω t) (hK : ∀ t, |dω t| ≤ K * ω t) (t : ℝ) :
    Real.sqrt (hillEnergy ω u du t) ≤
      Real.sqrt (hillEnergy ω u du 0) * Real.exp (K * |t|) := by
  have hgron := hillEnergy_le_abs hω hu hdu heq hωpos hK t
  have hfactor : Real.exp (2 * K * |t|) = Real.exp (K * |t|) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hfactor] at hgron
  refine (Real.sqrt_le_sqrt hgron).trans_eq ?_
  rw [Real.sqrt_mul (hillEnergy_nonneg ω u du 0), Real.sqrt_sq (Real.exp_nonneg _)]

end Generic

section Massive

variable {c dc : ℝ → ℝ} {m K C S : ℝ}

/-- The energy of the massive fibre, in both directions. -/
theorem hillEnergy_massive_le_abs (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ t, HasDerivAt c (dc t) t) (hcpos : ∀ t, 0 < c t) (hK : ∀ t, |dc t| ≤ K * c t)
    (hC : ∀ r, c r ^ 2 ≤ C ^ 2) (hs : s ^ 2 ≤ S ^ 2) (y₀ : ℝ × ℝ) (t : ℝ) :
    hillEnergy (massiveFreq m c s) (hillSolution (massiveFreq m c s) y₀)
        (hillSolutionDeriv (massiveFreq m c s) y₀) t ≤
      hillEnergy (massiveFreq m c s) (hillSolution (massiveFreq m c s) y₀)
        (hillSolutionDeriv (massiveFreq m c s) y₀) 0 * Real.exp (2 * K * |t|) := by
  have hM1 : (1 : ℝ) ≤ max 1 (m ^ 2 + C ^ 2 * S ^ 2) := le_max_left _ _
  have hMb : ∀ r, massiveFreq m c s r ^ 2 ≤ max 1 (m ^ 2 + C ^ 2 * S ^ 2) := fun r =>
    (massiveFreq_sq_le hm hC hs r).trans (le_max_right _ _)
  exact hillEnergy_le_abs (fun r => hasDerivAt_massiveFreq hm hcd s r)
    (hasDerivAt_hillSolution (continuous_massiveFreq hc m s) hM1 hMb y₀)
    (hasDerivAt_hillSolutionDeriv (continuous_massiveFreq hc m s) hM1 hMb y₀)
    (fun r => hillEquation (massiveFreq m c s) y₀ r) (fun r => massiveFreq_pos hm c s r)
    (fun r => abs_deriv_massiveFreq_le hm hcpos hK s r) t

/-- **The massive oscillator with datum `(1,0)`, bounded in both directions and uniformly in the
spatial frequency.** -/
theorem abs_hillSolution_massive_le_abs (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ t, HasDerivAt c (dc t) t) (hcpos : ∀ t, 0 < c t) (hK : ∀ t, |dc t| ≤ K * c t)
    (hC : ∀ r, c r ^ 2 ≤ C ^ 2) (hs : s ^ 2 ≤ S ^ 2) (t : ℝ) :
    |hillSolution (massiveFreq m c s) (1, 0) t| ≤ max 1 (c 0 / c t) * Real.exp (K * |t|) := by
  have hM1 : (1 : ℝ) ≤ max 1 (m ^ 2 + C ^ 2 * S ^ 2) := le_max_left _ _
  have hMb : ∀ r, massiveFreq m c s r ^ 2 ≤ max 1 (m ^ 2 + C ^ 2 * S ^ 2) := fun r =>
    (massiveFreq_sq_le hm hC hs r).trans (le_max_right _ _)
  have hcont := continuous_massiveFreq (m := m) hc s
  have hsplit := mul_abs_le_sqrt_hillEnergy
    (ω := massiveFreq m c s) (u := hillSolution (massiveFreq m c s) (1, 0))
    (du := hillSolutionDeriv (massiveFreq m c s) (1, 0))
    (fun r => massiveFreq_pos hm c s r) t
  have hsqrt := sqrt_hillEnergy_le_abs (fun r => hasDerivAt_massiveFreq hm hcd s r)
    (hasDerivAt_hillSolution hcont hM1 hMb (1, 0))
    (hasDerivAt_hillSolutionDeriv hcont hM1 hMb (1, 0))
    (fun r => hillEquation (massiveFreq m c s) (1, 0) r) (fun r => massiveFreq_pos hm c s r)
    (fun r => abs_deriv_massiveFreq_le hm hcpos hK s r) t
  rw [hillEnergy_cos_zero hcont hM1 hMb, Real.sqrt_sq (le_of_lt (massiveFreq_pos hm c s 0))]
    at hsqrt
  have hωpos : 0 < massiveFreq m c s t := massiveFreq_pos hm c s t
  have hratio := massiveFreq_le_mul (m := m) hcpos s t
  have hE : (0 : ℝ) ≤ Real.exp (K * |t|) := le_of_lt (Real.exp_pos _)
  have hstep : massiveFreq m c s t * |hillSolution (massiveFreq m c s) (1, 0) t|
      ≤ (max 1 (c 0 / c t) * Real.exp (K * |t|)) * massiveFreq m c s t := by
    refine (hsplit.trans hsqrt).trans ?_
    have h1 : massiveFreq m c s 0 * Real.exp (K * |t|)
        ≤ (max 1 (c 0 / c t) * massiveFreq m c s t) * Real.exp (K * |t|) :=
      mul_le_mul_of_nonneg_right hratio hE
    calc massiveFreq m c s 0 * Real.exp (K * |t|)
        ≤ (max 1 (c 0 / c t) * massiveFreq m c s t) * Real.exp (K * |t|) := h1
      _ = (max 1 (c 0 / c t) * Real.exp (K * |t|)) * massiveFreq m c s t := by ring
  refine le_of_mul_le_mul_right ?_ hωpos
  calc |hillSolution (massiveFreq m c s) (1, 0) t| * massiveFreq m c s t
      = massiveFreq m c s t * |hillSolution (massiveFreq m c s) (1, 0) t| := by ring
    _ ≤ (max 1 (c 0 / c t) * Real.exp (K * |t|)) * massiveFreq m c s t := hstep

/-- **Its velocity, in both directions.** -/
theorem abs_hillSolutionDeriv_massive_le_abs (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ t, HasDerivAt c (dc t) t) (hcpos : ∀ t, 0 < c t) (hK : ∀ t, |dc t| ≤ K * c t)
    (hC : ∀ r, c r ^ 2 ≤ C ^ 2) (hs : s ^ 2 ≤ S ^ 2) (t : ℝ) :
    |hillSolutionDeriv (massiveFreq m c s) (1, 0) t| ≤
      massiveFreq m c s 0 * Real.exp (K * |t|) := by
  have hM1 : (1 : ℝ) ≤ max 1 (m ^ 2 + C ^ 2 * S ^ 2) := le_max_left _ _
  have hMb : ∀ r, massiveFreq m c s r ^ 2 ≤ max 1 (m ^ 2 + C ^ 2 * S ^ 2) := fun r =>
    (massiveFreq_sq_le hm hC hs r).trans (le_max_right _ _)
  have hcont := continuous_massiveFreq (m := m) hc s
  have hsplit := abs_deriv_le_sqrt_hillEnergy
    (ω := massiveFreq m c s) (u := hillSolution (massiveFreq m c s) (1, 0))
    (du := hillSolutionDeriv (massiveFreq m c s) (1, 0)) t
  have hsqrt := sqrt_hillEnergy_le_abs (fun r => hasDerivAt_massiveFreq hm hcd s r)
    (hasDerivAt_hillSolution hcont hM1 hMb (1, 0))
    (hasDerivAt_hillSolutionDeriv hcont hM1 hMb (1, 0))
    (fun r => hillEquation (massiveFreq m c s) (1, 0) r) (fun r => massiveFreq_pos hm c s r)
    (fun r => abs_deriv_massiveFreq_le hm hcpos hK s r) t
  rw [hillEnergy_cos_zero hcont hM1 hMb, Real.sqrt_sq (le_of_lt (massiveFreq_pos hm c s 0))]
    at hsqrt
  exact hsplit.trans hsqrt

end Massive

end GaloisForLFunctions.HTGeometry
