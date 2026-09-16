import GaloisForLFunctions.RHTower.XiWardSchwarzCapKernel

/-!
# Schwarz reflection of the exact Ward cap kernel

The literal two-weight cap is anti-Schwarz under height reversal.  Pairing it
with the reflected completed source therefore produces a real signed cap
charge.  This is an exact structural constraint, not a source bound: it rules
out parity as a route to the required moving-window cancellation.
-/

open Complex

namespace RHTower

noncomputable section

/-- Height reversal sends the literal Schwarz cap kernel to its negative
conjugate. -/
theorem xiWardSchwarzCapDifference_neg_height (tau s x : ℝ) :
    xiWardSchwarzCapDifference tau s (-x) =
      -starRingEnd ℂ (xiWardSchwarzCapDifference tau s x) := by
  unfold xiWardSchwarzCapDifference
  rw [map_sub]
  rw [starRingEnd_self_apply]
  simp only [neg_neg, neg_sub]

end

end RHTower
