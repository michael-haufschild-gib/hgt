# TT C86 — Exact kinetic clock principal and curvature

- Stage: 3-formalized.
- Type: THEOREM (Lean).
- Parent: `../1-in-progress/tt-kinetic-contraction-source.md`.
- Route: TT, complete third-slope source sign.

Let C=6844157203887991842733489140006912. For every complex r,z,

    eval (basePoint 0 r z) compactSlope = 9*C*(1-9*z²).

This is the entire zero-clock value after the previously proved h⁴ clock
factor, with no drift or kinetic terms discarded. The full compact minor
has zero-clock value

    142586608414333163390281023750144*(1+z)*(1-3*z),

independent of r. Exact second-clock/first-drift moment jets identify the
cross-core after rank-one cancellation. The defect field preserves the
clock-zero ideal, so its action descends to this complete minor polynomial;
applying it gives the stated source identity.

The real normalized principal G(z)=C*(1-9*z²) satisfies:

- G(z)>0 for0<=z<1/3, and G(1/3)=0.
- G'(z)=-18*C*z and G''(z)=-18*C<0 for every real z.
- G(z)-C*(1-3*z)²*(1+6*z)=18*C*z²*(1-3*z), strictly positive for0<z<1/3.

The last identity falsifies the speculative cubic principal and supplies its
exact positive replacement. See `../5-failed/tt-cubic-kinetic-clock-principal.md`.
It does not falsify finite-clock concavity or any source-value/RH statement.

Production leaves: `ThetaCuspRatioKineticClockPrincipalJets` and
`ThetaCuspRatioKineticClockPrincipal`;28 declarations. Both direct
`lake --old env lean` audits passed warning-free. Every imported declaration
was audited through /tmp; only propext, Classical.choice and Quot.sound occur.
Both leaves are wired once; no umbrella/full build. Final evidence:
`/tmp/tt_c86_principal_final_audit_report.json` and
`/tmp/tt_c86_principal_production_axioms.log`. The lint snapshot has eight
unrelated reachability errors, none in these leaves; global lint is not clean.

Open: complete finite-clock curvature/source sign, full source quadratic,
fourth Schur gap, compact join, integrated/all-rank closure and RH. The next
sign test retains every term of the last negative-curvature Bernstein control;
no finite-clock sign follows solely from this clock-zero identity.
