# TT: unbounded-order diagonal sign repair

- **ID:** tt-center-jet-sign-oscillation
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Route:** TT, complete signed theta current
- **Conjecture:** C49

## Actual-source conjecture

Write Phi for the complete theta source and J_k(0) for its signed native
reflection jet of order 2k at the center. Conjecture: for every N there
are k,l>=N with J_k(0)<0<J_l(0). Thus pointwise all-rank positivity
cannot be obtained by changing only off-diagonal entries, or by repairing
only finitely many diagonal orders. Integrated positivity remains open.

## Corpus-derived paper mechanism

`ThetaOddCuspDerivativeFlatness` proves all complex odd-theta derivatives
vanish on a non-tangential approach to its odd cusp.
`ThetaCuspImaginaryEndpoint` identifies the actual imaginary-axis arc,
its cone, and endpoint pi/4. `ThetaCuspComplexWard` expresses the complete
source as (P''-P/4)/2 with P(z)=exp(z/2)*theta(i*exp(2z)).
The finite higher chain rule and product rule therefore give flatness
of every source derivative along the arc, without truncating its atoms.

For F(y)=Phi(i*y)^2, holomorphy on |y|<pi/4 gives its Taylor series;
its coefficient of y^(2k) is J_k(0)/(2k)!, and odd coefficients vanish.
If these coefficients were eventually nonnegative, differentiating past
the exceptional prefix would give a power series with nonnegative terms.
Every positive term prevents that derivative from tending to zero at
pi/4. Hence all tail coefficients would vanish, leaving a polynomial.
All-order endpoint flatness makes that polynomial zero, contrary to
Phi(0)>0. Apply the same argument to -F for the opposite sign.

Endpoint value zero alone is insufficient for this argument. All-order
flatness, the full Taylor disk, and the native-jet identification are
separate proof obligations; none may be assumed.

## Positive survivor and next producer

The proposed survivor is an exact unbounded-order sign classification
for the actual source and a necessary diagonal repair at unbounded
orders. C48's rank-eight residual sign is still unresolved; this
conjecture addresses its proposed all-rank off-diagonal-only extension.
After establishing the obstruction, attack a source-selected diagonal
flux that pays these negatives while retaining zero integrated flux.

## Status

2026-10-02: the complete paper argument and positive-center interval
corollary are formalized and audited. Modules:

- `ThetaCuspImaginaryAllOrderFlatness`: all potential, source and source-square
  derivatives tend to zero at the actual imaginary odd cusp.
- `ThetaCuspNativeCenterJetOscillation`: exact rotated even-jet identification,
  rotated all-order flatness, `thetaCuspNativeCenterJet_sign_oscillation`,
  and `thetaCuspNative_negative_diagonals_unbounded`.

Both targeted `lake build --old +GaloisForLFunctions.RHTower.<module>`
commands passed (leaf times 38s and 115s). Both final
`lake env lean GaloisForLFunctions/RHTower/<module>.lean` checks passed.
The separate /tmp axiom audit passed for all seven public theorems, each
using only `[propext, Classical.choice, Quot.sound]`. No proof holes,
added axioms, heartbeat increases, numerical experiments, full builds or
umbrella builds. Both leaves are wired into RHTower; index refresh passed.

Global `scripts/formal_tools.py lint --check-generated` returned 1 on
eleven unrelated unreachable modules: CCMApertureChainProfile,
CCMApertureTranslationChains, CCMExponentialRampPrimeMoment,
CCMExponentialRampSourceDissipation, CCMExponentialRampTerminalEntropy,
CCMRetainedChainKernelLower, DivisorSourceLogPhase,
MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines,
ThetaMovingShellFirstOrderPhase, and ZetaZeroDensityPowerSaving.
No owned-leaf or stale-index error was reported. Scoped whitespace checks
passed. This is not a globally clean lint claim.

The proof uses real parts of the complex Taylor series, so it does not
silently assume reality of intermediate derivatives. For each m beyond
the proposed one-signed cutoff, Taylor's nonnegative terms imply
Re F^(m)(0)<=Re F^(m)(x). The endpoint limit makes this coefficient zero.
Once all tail coefficients vanish, the Taylor series for the preceding
derivative is constant; its flat limit kills that constant. Finite
descending induction reaches F(0)=0, a contradiction. Negating F treats
the other sign. Parity and the exact imaginary-rotation derivative law
identify the remaining even jets with the actual native signed jets.

Corpus search on imaginary boundary/Taylor signs returned partial,
mostly irrelevant matches. No exhaustive novelty claim. Direct reads
verified the source identities and all-order odd-cusp flatness used here.
