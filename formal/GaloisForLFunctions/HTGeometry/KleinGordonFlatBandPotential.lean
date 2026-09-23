import GaloisForLFunctions.HTGeometry.KleinGordonDiagonalClosedForm

/-!
# A potential that flattens the frequency on a band

The shifted frequency of a real diagonal potential is `Ω² = ⟨ξ⟩² − p`. Choosing

`p(ξ) = ‖ξ‖²` for `‖ξ‖ ≤ √b`, `0` beyond,

makes `Ω = 1` identically on that band, and `|p| ≤ b` there because the band is exactly where `‖ξ‖²`
does not exceed `b`. On such a band the shifted symbols lose their dependence on the frequency:

`cos(tΩ)χ = (cos t)χ`,   `(sin(tΩ)/Ω)χ = (sin t)χ`.

A clock started from data in that band therefore runs at a single frequency — the first step towards an
exactly periodic clock, and towards showing the eigen-class of the Floquet theory is not empty.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section FlatPotential

variable {b : ℝ}

/-- The potential that flattens the frequency below `√b`. -/
def kgFlatPot (b : ℝ) (ξ : E) : ℝ := if ‖ξ‖ ≤ Real.sqrt b then ‖ξ‖ ^ (2 : ℕ) else 0

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem measurable_kgFlatPot (b : ℝ) : Measurable (kgFlatPot (E := E) b) :=
  Measurable.ite (measurableSet_le continuous_norm.measurable measurable_const)
    (continuous_norm.measurable.pow_const 2) measurable_const

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem abs_kgFlatPot_le (hb0 : 0 ≤ b) (ξ : E) : |kgFlatPot b ξ| ≤ b := by
  rw [kgFlatPot]
  split
  · rename_i hξ
    rw [abs_of_nonneg (sq_nonneg _)]
    have hsq : ‖ξ‖ ^ (2 : ℕ) ≤ Real.sqrt b ^ (2 : ℕ) := by
      have := norm_nonneg ξ
      nlinarith [Real.sqrt_nonneg b]
    rwa [Real.sq_sqrt hb0] at hsq
  · simpa using hb0

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **On its band the flattening potential makes the shifted frequency one.** -/
theorem kgShiftedFreq_kgFlatPot {ξ : E} (hξ : ‖ξ‖ ≤ Real.sqrt b) :
    kgShiftedFreq (fun ζ : E => -(kgFlatPot b ζ)) ξ = 1 := by
  have hpot : kgFlatPot b ξ = ‖ξ‖ ^ (2 : ℕ) := by
    rw [kgFlatPot, if_pos hξ]
  have hfreq : kgFreq ξ ^ (2 : ℕ) = 1 + ‖ξ‖ ^ (2 : ℕ) := by
    rw [kgFreq, Real.sq_sqrt (by positivity)]
  rw [kgShiftedFreq, hpot, hfreq]
  have harg : 1 + ‖ξ‖ ^ (2 : ℕ) + -‖ξ‖ ^ (2 : ℕ) = 1 := by ring
  rw [harg, Real.sqrt_one]

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **On its band the shifted cosine symbol is a constant.** -/
theorem kgShiftedCos_kgFlatPot_lowPass (t : ℝ) (ξ : E) :
    kgShiftedCos (fun ζ : E => -(kgFlatPot b ζ)) t ξ * kgLowPass (Real.sqrt b) ξ
      = ((Real.cos t : ℝ) : ℂ) * kgLowPass (Real.sqrt b) ξ := by
  rw [kgLowPass]
  split
  · rename_i hξ
    rw [mul_one, mul_one, kgShiftedCos, kgShiftedFreq_kgFlatPot hξ, mul_one]
  · rw [mul_zero, mul_zero]

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **On its band the shifted sine symbol is a constant.** -/
theorem kgShiftedSinOverFreq_kgFlatPot_lowPass (t : ℝ) (ξ : E) :
    kgShiftedSinOverFreq (fun ζ : E => -(kgFlatPot b ζ)) t ξ * kgLowPass (Real.sqrt b) ξ
      = ((Real.sin t : ℝ) : ℂ) * kgLowPass (Real.sqrt b) ξ := by
  rw [kgLowPass]
  split
  · rename_i hξ
    rw [mul_one, mul_one, kgShiftedSinOverFreq, kgShiftedFreq_kgFlatPot hξ, mul_one,
      div_one]
  · rw [mul_zero, mul_zero]

end FlatPotential

end GaloisForLFunctions.HTGeometry
