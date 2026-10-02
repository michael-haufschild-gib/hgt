# Universal nonpositive two-node source feedback

Status: falsified for actual center-anchored inverse-Gram coefficients;
positive survivor formalized. Both final direct leaf audits pass without
diagnostics, and both leaves are wired into RHTower.

## Rejected shortcut

The proposed first-axis barrier shortcut was `α≤s`, with
`α=uᵀM⁻¹u` and s the logarithmic source secant. The literal source instead
satisfies `α(0,z)>s(0,z,0)` for every z>0.

The source-specific strict diagonal-tail comparison gives
`p(z)/z<k(z)²/H(z,z)`, and the exact inverse-Gram square decomposition
gives `k(z)²/H(z,z)≤α(0,z)`. Thus this is a theorem about actual projection
coefficients. It does not falsify the compensated barrier `(α-s)B<k(y)E`.

## Positive survivor

`ThetaTwoNodeSignedSturmEnergy.lean` proves the exact signed energy and
the identity `α-s=-(s/α)∫wG²`. `ThetaTwoNodeCenterFeedback.lean` proves
the inverse-Gram square decomposition, negative actual representer energy
for every center-anchored pair, and exact positive signed energy
`det(M)α` for the old-span source-zero packet. The literal two-node signed
form has both signs. These are dependency-closed proofs with targeted
builds passing and all 26 public results audited for standard Lean axioms
only. No additional premise or axiom supplies the missing compensation.

## Remaining research

Use actual projection orthogonality for compensation, or prove the literal
four-point source inequality in RN-P-7i to control the center-anchored
projection coefficients. Arbitrary-rank positivity and RH remain open.
