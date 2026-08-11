# Calibration-Spectrum Mechanics (2026-08-11)

Higher pivot beyond route work and scalar Marked Variation Dynamics. For positive envelope `e`, coherent output `c`, and unit calibrator `u`, define `R(e,c;u)=e-Re(conj(u)c)`.

Exact laws:
- nonnegative when `e>=|c|`;
- coherent phase attains ground `e-|c|`; every unit phase lies above it;
- values at `1,-1,i,-i` reconstruct `e`, `Re c`, `Im c`;
- positive observers transport full spectra linearly;
- optimization after observation minus optimization before observation equals positive observer loss `S|c|-|Sc|`;
- marked defect has exact nonnegative source ancestry against final coherent phase;
- serial defect splits exactly into inherited source residual plus observer-created phase frustration;
- conservative refinement translates the entire spectrum vertically;
- cosine response is stationary at selected phase and its second-response stiffness is `|c|`; local minus observed stiffness equals observer loss.

Files:
- Stage1: `docs/drafts/pipeline/1-in-progress/universal-law-field/calibration-spectrum-mechanics/calibration-spectrum-mechanics-field-programme.md`
- Stage2: `docs/drafts/pipeline/2-fully-proven/universal-law-field/calibration-spectrum-mechanics/calibration-spectrum-reconstruction-observer-exchange-ancestry-and-stiffness-law.md`
- Stage3: `docs/drafts/pipeline/3-formalized/universal-law-field/calibration-spectrum-mechanics/calibration-spectrum-reconstruction-observer-exchange-ancestry-and-stiffness-law-formalized.md`
- Lean: `formal/GaloisForLFunctions/HTGeometry/CalibrationSpectrumMechanics.lean`
- wired in `formal/GaloisForLFunctions/HTGeometry/UniversalLawField.lean`

Verification:
- direct `lake env lean` pass;
- final `lake build GaloisForLFunctions.HTGeometry.UniversalLawField` pass, 11,613 jobs;
- axiom audit only `propext`, `Classical.choice`, `Quot.sound`;
- full lint target clean but global exit nonzero due unrelated unwired concurrent RHTower/HTGeometry modules and stale generated indexes.

Hostile scope: spectrum alone is equivalent to `(e,c)` and would be repackaging. Nontrivial field content is operational exchange, ancestry, generation transport, and stiffness prediction. No RH selector. Next RH gate: construct a pre-zero source-defined global calibration section and a jointly faithful observer family whose zero response forces source alignment; then compute route realization to show alignment iff criticality.