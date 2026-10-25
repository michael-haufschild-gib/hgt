# Genuine Meyer source surface and linear-degree Riemann–Roch

- **ID:** genuine-meyer-source-surface-has-linear-degree-riemann-roch
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** Q-II; genuine Poisson cohomology and ordinary convolution trace.
- **Statement:** The actual Meyer intersection surface has a descended linear trace degree supplying RR. Its degree cone has Bézout, ampleness, or additive closure exactly under RH; numerical and principal equivalence agree exactly under Xi simplicity.
- **Status:** Actual-file Lean check and nine transitive axiom audits passed; wired into the programme umbrella. External novelty unverified.

## Actual surface and degree

Cycles are two real fibre coordinates together with an actual all-weight complex
Meyer source, viewed as a real vector space. The two degrees include the actual
pole readings. The pairing is the hyperbolic product of these degrees minus

    delta(g,h)=Re Tr(T(g)T(h#)).

Centering the Mellin transform identifies this product trace exactly with the
existing Xi–Weil polarization. The pairing is symmetric and bilinear, and the
usual two fibres form a polar surface. Genuine Poisson boundaries give principal
cycles after the corresponding pole-coordinate corrections.

Ordinary trace descends as a complex-linear degree to genuine cohomology. Its
reading on the actual product g*h# is exactly delta(g,h). Consequently the
graded degree cone is the closed positive cone, without a positivity premise.
Its Riemann–Roch axiom is unconditional.

## Exact positivity boundary

At an off-line Xi point rho, actual causal value sources at rho and its reflected
point give a difference with trace square equal to minus the sum of the two
positive multiplicities. This is a genuine negative source, without an abstract
realization premise. Conversely RH makes Xi–Weil square polarization nonnegative.
Thus the surface Hodge index is exactly RH.

The polar-surface results then identify each of Bézout, ampleness, and additive
closure of this degree cone with RH. A descended linear degree therefore supplies
RR but does not itself prove the sign required for the other axioms.

## Principal versus numerical classes

The source trace radical consists exactly of vanishing zeroth Xi values, whereas
genuine Poisson boundaries require every multiplicity-bounded lower jet to vanish.
Both pole degrees must also vanish for a cycle to be numerically trivial. It
follows that numerical equivalence agrees with genuine principal equivalence
exactly when every Xi point is simple. Positive faithful ordinary trace requires
both RH and simplicity. Neither condition is asserted to hold.

## Lean certificate

Module: `ArithmeticCastelnuovoSeveri/MeyerSourceIntersectionSurface.lean`.
Actual command: `lake --old env lean GaloisForLFunctions/ArithmeticCastelnuovoSeveri/MeyerSourceIntersectionSurface.lean`, from `formal/`.
All audited endpoints use only `propext`, `Classical.choice`, and `Quot.sound`:

- `meyerProductTrace_eq_xiWeilPolarization`
- `meyerOffLinePacket_trace_neg`
- `meyerScalingSurface_hodgeIndex_iff`
- `meyerDegreeSourceCone_riemannRoch`
- `meyerDegreeSourceCone_bezout_iff`
- `meyerDegreeSourceCone_ample_iff`
- `meyerDegreeSourceCone_add_closed_iff`
- `meyerScalingSurface_radical_eq_principal_iff_simple`
- `meyerSourceTrace_positive_faithful_iff`

Dependencies are the actual source representation, genuine Xi division, finite
causal interpolation, ordinary trace-radical classification, and polar-surface
cone criteria. No strengthened premise or new trusted computation is introduced.
The missing olean is built only for the actual degree and flow leaves importing
this module; no umbrella build is run.

This is an exact answer for the stated linear degree, not an independent proof
of simultaneous RR and Bézout on the original full surface. Full Q-II remains open.
