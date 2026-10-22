# SP-E parabolic bridge — own research facts

- `SPEQuantileRieszParabolicBridge.lean` proves, for every `M ≥ 3`, that the completed
  source-faithful SP-E Riesz transport is exactly the finite sum of literal matched prime-polar
  quadrature defects plus the Riesz readout of the terminal-completed parabolic codiagonal, less
  the already-required lower correction.  The theorem is
  `speCompletedQuantileRieszTransport_eq_matchedQuadratureDefect_add_completedParabolic`.
- The identity retains all physical terms: quantile reporter cells `0` and `1` vanish exactly;
  the physical terminal reporter equals the negative parabolic-terminal Riesz readout; no
  terminal interval is dropped.
- The bridge is unconditional.  Scratch `#print axioms` reports only Lean's standard
  `propext`, `Classical.choice`, and `Quot.sound`.
- Consequence for route SP-E: the prior scalar signed-displacement obstruction is not the full
  current.  Remaining quantitative work is precisely cofinal control, after division by `M`, of
  the terminal-completed parabolic Riesz readout.  This bridge alone does not imply RH.
- `SPEQuantileRieszMatchedDefectControl.lean` removes the other term unconditionally:
  `abs_normalized_speQuantileRieszMatchedQuadratureDefectPrefix_le` gives an explicit fixed bound
  for the matched-defect prefix divided by `M`.  Its clipped profile agrees exactly with the
  literal Riesz profile on every physical matched cell in the head; clipping does not change the
  source defect being bounded.  Axiom audit again reports only Lean standard axioms.
- `SPEQuantileRieszParabolicPhysicalWall.lean` proves the exact physical-wall/source decomposition.
  If `C` is the terminal-completed codiagonal and `B` its literal source boundary at aperture
  `M`, then `B₀ · Riesz(C) = -⟨C,B⟩ + (√M·B₀-B₁)C₁ + B₂C₀`.  The first term is the complete
  cross-prime current (finite strict-cross current less the full terminal interaction).  Existing
  corpus bounds control none of the remaining two gauge terms.  Thus source-centering alone is
  insufficient; the surviving SP-E hard core is simultaneous, cutoff-uniform control of the
  cross current, physical/source barycenter transport, and terminal mass mismatch.
- The two exported physical-wall decomposition theorems build and their `#print axioms` audit
  contains only `propext`, `Classical.choice`, and `Quot.sound`.
