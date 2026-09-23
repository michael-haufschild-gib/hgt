import GaloisForLFunctions.HTGeometry.CriticalClockSourceUniversality

/-!
# Total budget of the unit-rate exponential clock

The three truncated moments of `CriticalClockSourceUniversality` are cut at a threshold `u`.
Letting the threshold exhaust the clock gives their totals: mass one, overlap zero, and cut
energy exactly **four**.  Since the truncated moments are functionals of the `Exp(1)` law alone,
these totals are class invariants of every nonnegative Mellin source with a simple pole at
`σ = 1`.
-/

open Filter
open scoped Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

private theorem tendsto_one_add_sq_mul_exp_neg :
    Tendsto (fun u : ℝ => (1 + u ^ (2 : ℕ)) * Real.exp (-u)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun u : ℝ => Real.exp (-u)) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero
  have h2 : Tendsto (fun u : ℝ => u ^ (2 : ℕ) * Real.exp (-u)) atTop (𝓝 0) :=
    Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2
  have h := h1.add h2
  rw [add_zero] at h
  exact h.congr fun u => by ring

/-- The unit-rate exponential clock has total mass one. -/
theorem tendsto_exponentialCutMass_atTop :
    Tendsto exponentialCutMass atTop (𝓝 1) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℝ))).sub
    Real.tendsto_exp_neg_atTop_nhds_zero
  rw [sub_zero] at h
  exact h.congr fun u => rfl

/-- The cut overlap of the pointed Fisher score with the exponential clock vanishes in total:
the score is centred. -/
theorem tendsto_exponentialCutOverlap_atTop :
    Tendsto exponentialCutOverlap atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).const_mul (2 : ℝ)
  rw [mul_zero] at h
  exact h.congr fun u => by simp [exponentialCutOverlap, pow_one]

/-- **Four units.**  The total cut energy of the pointed Fisher score under the unit-rate
exponential clock is exactly four.  This is the class-invariant value of the four-unit incidence
budget of every nonnegative Mellin source with a simple pole at `σ = 1`. -/
theorem tendsto_exponentialCutEnergy_atTop :
    Tendsto exponentialCutEnergy atTop (𝓝 4) := by
  have h := (((tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℝ))).sub
    tendsto_one_add_sq_mul_exp_neg).const_mul (4 : ℝ))
  rw [sub_zero, mul_one] at h
  exact h.congr fun u => rfl

end GaloisForLFunctions.HTGeometry
