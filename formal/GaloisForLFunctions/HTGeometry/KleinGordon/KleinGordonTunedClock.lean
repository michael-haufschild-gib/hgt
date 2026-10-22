import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonDiagonalVelocityBound

/-!
# Clocks of tunable rate

The flattening construction has a free parameter. For any rate `c` with `1 ≤ c² ≤ 1 + b` the potential

`p(ξ) = ⟨ξ⟩² − c²` on `‖ξ‖ ≤ √(c² − 1 + b)`, `0` beyond,

is admissible — its size is at most `b` exactly on that band — and makes the shifted frequency
identically `c` there. The clock started from data in the band is then the plane rotation at rate `c`,

`u(t) = cos(ct)Px + (sin(ct)/c)Py`,

exactly periodic with period `2π/c`. The strength of the potential thus buys a whole interval of clock
rates, `1 ≤ c ≤ √(1+b)`; the case `c = 1` is the earlier flattening potential.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section TunedClock

variable {b c : ℝ}

/-- The potential that tunes the frequency to `c` on its band. -/
def kgTunedPot (b c : ℝ) (ξ : E) : ℝ :=
  if ‖ξ‖ ≤ Real.sqrt (c ^ (2 : ℕ) - 1 + b) then kgFreq ξ ^ (2 : ℕ) - c ^ (2 : ℕ) else 0

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem measurable_kgTunedPot (b c : ℝ) : Measurable (kgTunedPot (E := E) b c) :=
  Measurable.ite (measurableSet_le continuous_norm.measurable measurable_const)
    ((((continuous_kgFreq (E := E)).measurable).pow_const 2).sub measurable_const)
    measurable_const

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem kgFreq_sq_eq (ξ : E) : kgFreq ξ ^ (2 : ℕ) = 1 + ‖ξ‖ ^ (2 : ℕ) := by
  rw [kgFreq, Real.sq_sqrt (by positivity)]

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **The tuned potential is admissible.** -/
theorem abs_kgTunedPot_le (hb0 : 0 ≤ b) (hc1 : 1 ≤ c ^ (2 : ℕ)) (hcb : c ^ (2 : ℕ) ≤ 1 + b) (ξ : E) :
    |kgTunedPot b c ξ| ≤ b := by
  rw [kgTunedPot]
  split
  · rename_i hξ
    have hrange : ‖ξ‖ ^ (2 : ℕ) ≤ c ^ (2 : ℕ) - 1 + b := by
      have hnn : (0 : ℝ) ≤ c ^ (2 : ℕ) - 1 + b := by linarith
      have hsq : ‖ξ‖ ^ (2 : ℕ) ≤ Real.sqrt (c ^ (2 : ℕ) - 1 + b) ^ (2 : ℕ) := by
        have := norm_nonneg ξ
        nlinarith [Real.sqrt_nonneg (c ^ (2 : ℕ) - 1 + b)]
      rwa [Real.sq_sqrt hnn] at hsq
    have hnn2 : (0 : ℝ) ≤ ‖ξ‖ ^ (2 : ℕ) := sq_nonneg _
    rw [kgFreq_sq_eq, abs_le]
    constructor
    · linarith
    · linarith
  · simpa using hb0

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **On its band the tuned potential makes the shifted frequency `c`.** -/
theorem kgShiftedFreq_kgTunedPot (hc0 : 0 < c) {ξ : E}
    (hξ : ‖ξ‖ ≤ Real.sqrt (c ^ (2 : ℕ) - 1 + b)) :
    kgShiftedFreq (fun ζ : E => -(kgTunedPot b c ζ)) ξ = c := by
  have hpot : kgTunedPot b c ξ = kgFreq ξ ^ (2 : ℕ) - c ^ (2 : ℕ) := by
    rw [kgTunedPot, if_pos hξ]
  rw [kgShiftedFreq, hpot]
  have harg : kgFreq ξ ^ (2 : ℕ) + -(kgFreq ξ ^ (2 : ℕ) - c ^ (2 : ℕ)) = c ^ (2 : ℕ) := by ring
  rw [harg, Real.sqrt_sq hc0.le]

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- On its band the shifted cosine symbol is the constant `cos (c t)`. -/
theorem kgShiftedCos_kgTunedPot_lowPass (hc0 : 0 < c) (t : ℝ) (ξ : E) :
    kgShiftedCos (fun ζ : E => -(kgTunedPot b c ζ)) t ξ
        * kgLowPass (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) ξ
      = ((Real.cos (t * c) : ℝ) : ℂ) * kgLowPass (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) ξ := by
  rw [kgLowPass]
  split
  · rename_i hξ
    rw [mul_one, mul_one, kgShiftedCos, kgShiftedFreq_kgTunedPot hc0 hξ]
  · rw [mul_zero, mul_zero]

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- On its band the shifted sine symbol is the constant `sin (c t) / c`. -/
theorem kgShiftedSinOverFreq_kgTunedPot_lowPass (hc0 : 0 < c) (t : ℝ) (ξ : E) :
    kgShiftedSinOverFreq (fun ζ : E => -(kgTunedPot b c ζ)) t ξ
        * kgLowPass (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) ξ
      = ((Real.sin (t * c) / c : ℝ) : ℂ) * kgLowPass (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) ξ := by
  rw [kgLowPass]
  split
  · rename_i hξ
    rw [mul_one, mul_one, kgShiftedSinOverFreq, kgShiftedFreq_kgTunedPot hc0 hξ]
  · rw [mul_zero, mul_zero]

end TunedClock

end GaloisForLFunctions.HTGeometry
