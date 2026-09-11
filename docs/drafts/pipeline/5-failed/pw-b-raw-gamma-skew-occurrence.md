# PW-B unchanged Gamma/Möbius field as a skew scalar mode

- **ID:** PW-B-RAW-GAMMA-SKEW-OCCURRENCE-2026-09-11
- **Stage:** 5-failed
- **Scope:** The unchanged field M_z in the explicit equation K_z=lambda*M_z. PW-B and corrected/distributional source realizations remain live.

The complete signed source satisfies M_z/Q->1 and E_z/Q->0 for every
complex z. The actual reflected nonlocal current has a finite limit
after division by Q. Its retained adjoint-contact term therefore gives
K_z/(Q*log(x))->-2, while every scalar multiple of M_z has zero limit
at this scale. This excludes the stated ansatz for all z and lambda;
no numerical evidence or assumed operator closure enters the proof.

**Positive survivor and second pass.** Adding the explicit logarithmic
ground correction2*c*log(x)*Q gives exact leading limit2*c-2. The scalar
equation with ground-subtracted field M_z-c*Q forces c=1. Thus the
obstruction determines the unique possible ground-subtraction
coefficient. At that coefficient the leading limit vanishes for every
z, so it cannot select Xi zeros. The surviving task is the complete
corrected equation and its original source/domain realization, not
another assertion of scalar occurrence for M_z.

**Paper proof:** Dependency-closed through the complete source-series
and kernel endpoint limits. **Lean:** All8 public declarations, including
both exact leading laws and the correction classification, pass the
standard-only scratch axiom audit. Targeted leaf build, all-name
source/API checks, exact scratch-body comparison and final repository
lint passed; see the [formal theorem card](../3-formalized/pw-b-gamma-skew-source-endpoint.md).
No full adjoint, physical selection principle, corrected eigenfunction,
Xi occurrence or Ward balance is claimed.
