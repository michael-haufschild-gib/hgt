/-
Exact ordinate support for displaced cosh quartet envelopes.

Moving either vertical zero lattice horizontally preserves the full set of
imaginary parts.  This is the support-level core of the ordinate-measure
invariance used by the transverse-divisor relocation witness.
-/
import GaloisForLFunctions.RHTower.CoshQuartetEnvelopeMultiplicity

open Complex

namespace RHTower

/-- Every displaced quartet envelope has the same zero ordinates as the central envelope. -/
theorem coshQuartetEnvelope_zero_im_iff_zero_im_zero (a y : ℝ) :
    (∃ z : ℂ, coshQuartetEnvelope a z = 0 ∧ z.im = y) ↔
      ∃ z : ℂ, coshQuartetEnvelope 0 z = 0 ∧ z.im = y := by
  constructor
  · rintro ⟨z, hz, him⟩
    rcases coshQuartetEnvelope_eq_zero_iff.mp hz with ⟨k, hk⟩ | ⟨k, hk⟩
    · refine ⟨-((2 * k + 1 : ℂ) * Real.pi / 2) * I, ?_, ?_⟩
      · apply coshQuartetEnvelope_eq_zero_iff.mpr
        left
        refine ⟨k, ?_⟩
        simp
      · rw [hk] at him
        simpa using him
    · refine ⟨-((2 * k + 1 : ℂ) * Real.pi / 2) * I, ?_, ?_⟩
      · apply coshQuartetEnvelope_eq_zero_iff.mpr
        left
        refine ⟨k, ?_⟩
        simp
      · rw [hk] at him
        simpa using him
  · rintro ⟨z, hz, him⟩
    rcases coshQuartetEnvelope_eq_zero_iff.mp hz with ⟨k, hk⟩ | ⟨k, hk⟩
    · refine ⟨(a : ℂ) - ((2 * k + 1 : ℂ) * Real.pi / 2) * I, ?_, ?_⟩
      · apply coshQuartetEnvelope_eq_zero_iff.mpr
        left
        exact ⟨k, rfl⟩
      · rw [hk] at him
        simpa using him
    · refine ⟨(a : ℂ) - ((2 * k + 1 : ℂ) * Real.pi / 2) * I, ?_, ?_⟩
      · apply coshQuartetEnvelope_eq_zero_iff.mpr
        left
        exact ⟨k, rfl⟩
      · rw [hk] at him
        simpa using him

/-- Horizontal displacements preserve the entire zero-ordinate support. -/
theorem coshQuartetEnvelope_zero_im_iff_zero_im (a b y : ℝ) :
    (∃ z : ℂ, coshQuartetEnvelope a z = 0 ∧ z.im = y) ↔
      ∃ z : ℂ, coshQuartetEnvelope b z = 0 ∧ z.im = y :=
  (coshQuartetEnvelope_zero_im_iff_zero_im_zero a y).trans
    (coshQuartetEnvelope_zero_im_iff_zero_im_zero b y).symm

end RHTower
