# TT C85 — Complete second kinetic control and interval contraction

- Stage: formalized; direct production and imported declaration audits passed.
- Parent: `../1-in-progress/tt-kinetic-contraction-source.md`.
- Route: TT, full third-slope source positivity.

For every real h,r,Z with0<h<=4/5,0<=r<=361/25,0<=Z<=1/3,

    0 < reducedKineticControl h (9-r*h²) Z 1.

The proof retains the complete source, all ten drift cells and every lower
clock term. Fifty signed product cells assemble the full second kinetic row.
At Z=1/3, exact clock division gives control1=h⁴*F1(h,r). F1 contains all220
monomials and is strictly positive on the closed clock/defect rectangle:
its exact degree34-by9 tensor Bernstein reconstruction has all350 coefficients
strictly positive. There is no sampling, external coefficient arithmetic,
truncated source, source-sign/RH premise or enlarged proof limit.

Exact triangular contraction, for every i<=19 and all real h,v,Z,t:

    control(h,v,tZ,i) = Bernstein_i
      (k |-> control(h,v,Z,k)*degreeElevationCoefficient(19,k,i))(t).

The binomial chain identity proves this law unconditionally. For i=1,
C84's positive control0 and the new fixed-endpoint control1 give positivity
for the entire0<=Z<=1/3 interval. The stronger rectangular certificate includes
some unphysical negative-drift states; no equivalence to the nonlinear
boundary parameter rectangle is asserted.

Production:41 new second-control leaves/609 declarations plus the audited
subdivision leaf/four declarations:42 leaves/613 declarations. Every direct
`lake --old env lean` audit is warning-free; imported `#print axioms` audits
in /tmp use only propext, Classical.choice and Quot.sound. All leaves wired
once; no umbrella/full build. Manifest `/tmp/tt_c85_production_manifest.json`,
final report `/tmp/tt_c85_final_audit_report.json`. The lint snapshot reports
six unrelated errors (five reachability gaps and one Kuznetsov proof-debt
statement), none in C85. Global lint is not clean.

Principal leaves: ThetaCuspRatioKineticControlSubdivision,
ThetaCuspRatioKineticSecondTensorReconstruction,
ThetaCuspRatioKineticSecondControlPositive.
Capstone: `HTGeometry.ThetaRatioKineticContraction.reducedKineticControl_one_pos`.

Open: remaining controls/full interior source value, full source quadratic,
fourth Schur gap, compact/adverse-ray join, integrated/all-rank closure, RH.
Next attack assembles every remaining full source row, supporting both all
nonterminal control signs and a full kinetic-curvature certificate. No
curvature sign is inferred from seam linearity or terminal restrictions.
