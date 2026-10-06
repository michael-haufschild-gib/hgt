# TT C84 — First complete finite-clock kinetic control

- Stage: formalized; direct production and imported declaration audits passed.
- Parent: `../1-in-progress/tt-kinetic-contraction-source.md`.
- Route: TT, complete third-slope source positivity.

For every real h,r,Z, the full source satisfies

    reducedKineticControl h (9-r*h²) Z 0 = h⁴*F(h,r).

The exact polynomial F is strictly positive on 0<=h<=4/5,
0<=r<=361/25. Therefore the complete first reduced kinetic control is
strictly positive throughout 0<h<=4/5,0<=r<=361/25, independently of Z.
There is no source-sign or RH premise; domain constraints are explicit.
The rectangle includes some negative-drift states and is a sufficient
certificate, not an equivalence to the nonlinear boundary s rectangle.

The proof retains all ten drift cells. Fifty full signed cofactor/block
products assemble the ten complex cells; per-cell real conversion precedes
the whole defect substitution. All212 resulting monomials enter F. Exact
unscaled tensor Bernstein reconstruction has degree32 in clock and degree9
in defect. Every one of its330 coefficients is strictly positive. No sampling,
external coefficient arithmetic, truncated jet or enlarged proof limit is used.

Production:40 leaves,585 declarations, all audited by direct
`lake --old env lean` and imported `#print axioms` in /tmp. Only propext,
Classical.choice and Quot.sound occur. All leaves wired exactly once; no
umbrella/full build. Manifest `/tmp/tt_c84_production_manifest.json`, final
report `/tmp/tt_c84_final_audit_report.json`. The C84 lint snapshot reported22 unrelated
umbrella reachability errors and no C84 errors.

Principal leaves: ThetaCuspRatioKineticFirstSourceDefect,
ThetaCuspRatioKineticFirstTensorReconstruction,
ThetaCuspRatioKineticFirstControlPositive.
Capstone: `HTGeometry.ThetaRatioKineticContraction.reducedKineticControl_zero_pos`.

Open: other full finite-clock controls/source value, full source quadratic,
fourth Schur gap, compact/adverse-ray join, integrated/all-rank closure, RH.
Next conjecture: exact triangular interval contraction plus full nonterminal
controls at a fixed kinetic endpoint; the exact nonlinear boundary controls
the terminal value. No second-control or full-source sign is asserted.
