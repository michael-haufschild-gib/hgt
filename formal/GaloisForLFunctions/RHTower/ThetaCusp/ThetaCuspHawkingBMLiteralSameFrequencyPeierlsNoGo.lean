import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCuspIndicialSelection

/-!
# Frequency wall for the literal same-frequency Peierls stitch

The constructed physical Einstein stream is on shell at `w = 2 * physicalRate`.
The literal causal projected stream and its Einstein current instead require
`3 / 2 < w.re`.  This leaf proves those two exact interfaces cannot be sewn at
one frequency.  It does not rule out a separately proved continuation or the
existing off-shell frequency-defect boundary cochain.
-/

namespace RHTower.D4BMLiteralSameFrequencyPeierls

open D4BMCuspProjection

noncomputable section

/-- The physical Einstein stream's on-shell time frequency is strictly left of `-4`. -/
theorem onShell_frequency_re_lt_neg_four (q : XiZeroCopy) (branch : Bool) :
    (2 * physicalRate q branch).re < -4 := by
  have hs := physicalRate_re_bounds q branch
  norm_num at hs ⊢
  linarith

/-- Hence the literal causal projected-stream chamber cannot be instantiated at that frequency. -/
theorem onShell_frequency_not_causal_stream_chamber (q : XiZeroCopy) (branch : Bool) :
    ¬ (3 / 2 : ℝ) < (2 * physicalRate q branch).re := by
  have hs := onShell_frequency_re_lt_neg_four q branch
  linarith

end
end RHTower.D4BMLiteralSameFrequencyPeierls
