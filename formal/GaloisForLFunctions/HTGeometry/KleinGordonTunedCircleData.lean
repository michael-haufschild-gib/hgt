import GaloisForLFunctions.HTGeometry.KleinGordonTunedMonodromy

/-!
# The complex datum that rotates by a phase

The plane rotation of the tuned clock has complex eigenvectors. Starting the clock from the pair
`(Px, −icPx)` makes both field and velocity acquire the same scalar factor

`k(t) = cos(ct) − i sin(ct)`,

a point of the unit circle. This is the datum that will exhibit `k` as an attained Floquet multiplier
at every period, not only the value one.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section CircleData

variable {b c : ℝ}

/-- The phase acquired by the tuned clock in time `t`. -/
def kgTunedPhase (c t : ℝ) : ℂ :=
  ((Real.cos (t * c) : ℝ) : ℂ) - Complex.I * ((Real.sin (t * c) : ℝ) : ℂ)

theorem norm_kgTunedPhase (c t : ℝ) : ‖kgTunedPhase c t‖ = 1 := by
  have hexp : kgTunedPhase c t = Complex.exp (((-(t * c) : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.exp_mul_I, kgTunedPhase, Complex.ofReal_cos, Complex.ofReal_sin]
    push_cast
    rw [Complex.cos_neg, Complex.sin_neg]
    ring
  rw [hexp]
  simpa using Complex.norm_exp_ofReal_mul_I (-(t * c))

set_option maxHeartbeats 1000000 in
/-- **The tuned clock started from the complex datum acquires a phase.** -/
theorem kgShiftedField_kgTunedPot_circle (hc0 : 0 < c) (hc1 : 1 ≤ c ^ (2 : ℕ))
    (x : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgShiftedField (measurable_kgTunedPot (E := E) b c) (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x
        ((-(Complex.I * (c : ℂ))) • x) t
      = kgTunedPhase c t • kgLowPassOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x := by
  have hcne : (c : ℂ) ≠ 0 := by
    simpa using ne_of_gt hc0
  rw [kgShiftedField_kgTunedPot hc0 hc1, map_smul, smul_smul, kgTunedPhase, ← add_smul]
  congr 1
  push_cast
  field_simp
  ring

set_option maxHeartbeats 1000000 in
/-- **So does its velocity.** -/
theorem kgShiftedVel_kgTunedPot_circle (hb0 : 0 ≤ b) (hb1 : b < 1) (hc0 : 0 < c)
    (hc1 : 1 ≤ c ^ (2 : ℕ)) (hcb : c ^ (2 : ℕ) ≤ 1 + b) (x : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgShiftedVel (measurable_kgTunedPot (E := E) b c) hb0 hb1
        (abs_kgTunedPot_le hb0 hc1 hcb) (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x
        ((-(Complex.I * (c : ℂ))) • x) t
      = kgTunedPhase c t
        • ((-(Complex.I * (c : ℂ))) • kgLowPassOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x) := by
  rw [kgShiftedVel_kgTunedPot hb0 hb1 hc0 hc1 hcb, map_smul, smul_smul, smul_smul,
    kgTunedPhase, ← neg_smul, ← add_smul]
  congr 1
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

end CircleData

end GaloisForLFunctions.HTGeometry
