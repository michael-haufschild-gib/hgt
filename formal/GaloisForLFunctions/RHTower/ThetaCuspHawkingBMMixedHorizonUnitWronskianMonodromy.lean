import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMMixedHorizonIntegratedOpticalForm

/-!
# Unit-Wronskian normalization of mixed BM horizon monodromy

At mixed Birmingham--Mokhtari Frobenius order `N`, the regular branch begins with `z^(N+1)`.
Against the constant singular branch, the Sturm Wronskian of this leading monomial tends to
`N+1`, not one.  Thus a raw logarithmic monodromy coefficient multiplying `z^(N+1)` differs by
the exact positive factor `N+1` from its unit-Wronskian coefficient.

This module proves that normalization factor and applies it to the corpus mixed-horizon monodromy.
The correction preserves strict positivity and nonvanishing but is mandatory before comparing the
Frobenius coefficient with a unit-Wronskian Green or QNM cokernel normalization.

`[BRIDGE] [PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED]`
-/

open Complex Real Set Filter Topology

namespace RHTower

noncomputable section

/-- Sturm Wronskian of leading constant and raw regular `z^(N+1)` Frobenius monomials. -/
def d4BMMixedHorizonLeadingFrobeniusWronskian
    (n k : ℕ) (z : ℝ) : ℝ :=
  d4BMMixedHorizonSturmP n k z *
    (d4BMMixedHorizonFrobeniusOrder n k + 1 : ℝ) *
      z ^ d4BMMixedHorizonFrobeniusOrder n k

/-- Exact interior formula for the leading Frobenius Wronskian. -/
theorem d4BMMixedHorizonLeadingFrobeniusWronskian_eq
    (n k : ℕ) {z : ℝ} (hz : z ≠ 0) :
    d4BMMixedHorizonLeadingFrobeniusWronskian n k z =
      (d4BMMixedHorizonFrobeniusOrder n k + 1 : ℝ) *
        Real.sqrt (1 - z) := by
  rw [d4BMMixedHorizonLeadingFrobeniusWronskian,
    d4BMMixedHorizonSturmP]
  field_simp [pow_ne_zero _ hz]

/-- Raw regular Frobenius branch has horizon Wronskian normalization `N+1`. -/
theorem tendsto_d4BMMixedHorizonLeadingFrobeniusWronskian_zero
    (n k : ℕ) :
    Tendsto (d4BMMixedHorizonLeadingFrobeniusWronskian n k)
      (𝓝[>] 0)
      (𝓝 (d4BMMixedHorizonFrobeniusOrder n k + 1 : ℝ)) := by
  let N := d4BMMixedHorizonFrobeniusOrder n k
  have heq : d4BMMixedHorizonLeadingFrobeniusWronskian n k =ᶠ[𝓝[Set.Ioi 0] 0]
      fun z : ℝ => (N + 1 : ℝ) * Real.sqrt (1 - z) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact d4BMMixedHorizonLeadingFrobeniusWronskian_eq n k (ne_of_gt hz)
  have ht : Tendsto (fun z : ℝ => (N + 1 : ℝ) * Real.sqrt (1 - z))
      (𝓝 0) (𝓝 (N + 1 : ℝ)) := by
    simpa using (show ContinuousAt
      (fun z : ℝ => (N + 1 : ℝ) * Real.sqrt (1 - z)) 0 by fun_prop).tendsto
  exact (ht.mono_left inf_le_left).congr' heq.symm

/-- Mixed BM monodromy coefficient after conversion to leading unit-Wronskian regular branch. -/
def d4BMMixedHorizonUnitWronskianMonodromyJump
    (n k : ℕ) (chi : ℝ) : ℂ :=
  (d4BMMixedHorizonFrobeniusOrder n k + 1 : ℂ) *
    d4BMMixedHorizonCounterclockwiseMonodromyJump n k chi

/-- Leading regular Frobenius monomial divided by its horizon Wronskian `N+1`. -/
def d4BMMixedHorizonLeadingUnitWronskianRegularBranch
    (n k : ℕ) (z : ℂ) : ℂ :=
  z ^ (d4BMMixedHorizonFrobeniusOrder n k + 1) /
    (d4BMMixedHorizonFrobeniusOrder n k + 1 : ℂ)

/-- Raw and unit-Wronskian monodromy representations are exactly the same radial jump. -/
theorem d4BMMixedHorizonMonodromy_raw_eq_unitWronskian
    (n k : ℕ) (chi : ℝ) (z : ℂ) :
    d4BMMixedHorizonCounterclockwiseMonodromyJump n k chi *
        z ^ (d4BMMixedHorizonFrobeniusOrder n k + 1) =
      d4BMMixedHorizonUnitWronskianMonodromyJump n k chi *
        d4BMMixedHorizonLeadingUnitWronskianRegularBranch n k z := by
  rw [d4BMMixedHorizonUnitWronskianMonodromyJump,
    d4BMMixedHorizonLeadingUnitWronskianRegularBranch]
  have hN : (d4BMMixedHorizonFrobeniusOrder n k + 1 : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero (d4BMMixedHorizonFrobeniusOrder n k)
  field_simp [hN]

/-- Exact positive-imaginary formula after unit-Wronskian normalization. -/
theorem d4BMMixedHorizonUnitWronskianMonodromyJump_eq
    (n k : ℕ) (chi : ℝ) :
    d4BMMixedHorizonUnitWronskianMonodromyJump n k chi =
      Complex.I * (((d4BMMixedHorizonFrobeniusOrder n k + 1 : ℕ) : ℝ) *
        (2 * Real.pi * d4BMMixedHorizonFrobeniusWeight n k chi) : ℂ) := by
  rw [d4BMMixedHorizonUnitWronskianMonodromyJump,
    d4BMMixedHorizonCounterclockwiseMonodromyJump_eq]
  push_cast
  ring

/-- Unit-Wronskian normalization preserves strict positive orientation. -/
theorem d4BMMixedHorizonUnitWronskianMonodromyJump_im_pos
    (n k : ℕ) (chi : ℝ) :
    0 < (d4BMMixedHorizonUnitWronskianMonodromyJump n k chi).im := by
  rw [d4BMMixedHorizonUnitWronskianMonodromyJump_eq]
  simp
  have hN : 0 < (d4BMMixedHorizonFrobeniusOrder n k + 1 : ℝ) := by positivity
  exact mul_pos hN
    (mul_pos (by positivity) (d4BMMixedHorizonFrobeniusWeight_pos n k chi))

end

end RHTower
