# TG-C9.7: theta polarization and cubic displacement on the actual graph

- **ID:** TG-C9.7-20261002-01a0
- **Stage:** 1-in-progress
- **Type:** RESEARCH PARENT / theta classification certified, mixed-prime cubic open
- **Parent:** `../3-formalized/tg-fourier-jet-closed-neutral-domain.md`

## Hard question after C9.6

The original neutral N is now proved closed and unbounded. This alone does not
exclude boundedness of a polynomial assembled from several unbounded source maps.
Attack the actual cubic before claiming that the completed transgression fails.

## Corpus basis

`PrimeBurnolFourierJetNeutralGraph` gives the exact even source domain and unbounded N,
including every literal single-prime core. `PrimeBurnolThetaModularHolonomy` defines
the actual prime-dependent theta block U=[[v,-c],[c,v]], v=sech(a log(p)/2),
c=tanh(a log(p)/2), with v²+c²=1. `SourceFrameModularHolonomy` fixes the orientation
Q=U P U^-1. `ModularCubicProjectionTransgression` and `ModularCubicProjectionCrossIdentity`
give the exact noncommutative cubic associator and its five commutator channels.

Deep search `Burnol prime Gamma Fourier cubic transgression boundary index` returned
partial results (reranking deadline, malformed filter JSON); no absence conclusion.
Lexical follow-up for cubic/unbounded/projection returned the actual cubic cross identity,
restricted-projection cubic continuity, and weighted modular trace cancellation.
The latter does not establish boundedness or domain closure of this new graph cubic.

## Next conjectures and paper attack

1. Source swap S(f,g)=(g,f) extends isometrically to G. On the actual even source,
   E(g,f)=(F E(f,g).1,F E(f,g).2): prove evenness of the separate M images and use
   F²=1 there. Inputs swap isometrically too. This requires no inverse to E.
2. For a fixed prime, the literal theta polarization on finite depth coefficients
   has the exact original-domain expression
   `Q=c² I+(v²-c²)N+vc S`.
   Thus Q has a bounded extension exactly when v²=c²: the exceptional survivor is
   `(I+S)/2` or `(I-S)/2`. In all other cases a bounded Q would recover bounded N.
   Prove the statement on the literal finite core using its exact graph closure.
3. The actual displacement satisfies `(Q-N)²=c² I`, hence
   `(Q-N)³=c²(Q-N)`. For c≠0 its cubic cannot extend boundedly: its coefficient
   of N is -2c⁴, while the I and S terms are bounded. This is an exact qualitative
   cancellation test, not a numerical bound optimization.

The full-source theta classification, actual frame orientation, exact displacement cube
and its literal prime-core obstruction are now Lean-certified; see the final record below.
The finite-core theta boundedness equivalence itself is not separately asserted.

## Remaining harder cubic problem

Even success on the displacement does not settle the COMPLETE associator
`(R-N)³-(R-Q)³-(Q-N)³`, with R obtained from the full literal Gram modular action.
The first two terms might cancel its unbounded part. Next identify that action on the
common invariant source core, keep every prime/Fourier cross term, and test those five
commutator channels jointly. Do not insert boundedness assumptions or select a Xi-zero
dependent reporter. Gamma–Xi, Hardy-index and sub-unit producer gaps remain open.

## Certified discovery: the balanced full cubic cancels

For the cubic, use the finite Gram of the TWO ACTUAL JET OUTPUTS, keeping the
input-and-output graph norm separately as the topology for extension. Source
swap applies physical Fourier to both outputs, so its matrix commutes with this full Gram, including every
cross term. At v²=c², the actual theta Q is a scalar combination of I and source swap.
Consequently the full Gram modular action fixes Q: R=C^-1 Q C=Q. The COMPLETE
associator is then exactly zero, although (Q-N)³ remains unbounded on the cofinal graph.

This supplies a concrete positive survivor and prevents an incorrect universal cubic
no-go based on neutral/displacement unboundedness. The finite actual output Gram,
its positivity/invertibility and exact frame orientation are now Lean-certified.
Away from balance, the complete cubic remains the hard
open question; no generic trace cancellation establishes its domain or boundedness.

Search `Fourier graph swap theta projection cubic displacement` was partial at
decomposition; it retrieved the actual source graph definitions. Search `Gram matrix
positive definite injective finite sum inner products` was partial at reranking and
returned existing Gram positivity ingredients. Current mathlib's gram positivity and
positive-definite-plus-semidefinite addition APIs are being checked directly.

## Working checkpoint, now audited

`PrimeBurnolFourierJetThetaDomain` now passes a foreground production leaf check.
It proves the actual source swap is isometric, preserves the completed even graph,
and implements the theta source formula. Actual rotation/inverse orientation is
checked. Theta admits a graph bound exactly when visibility²=contrast²; the cubic
displacement admits one exactly at theta parameter zero. These are exact structural
classifications, with no numerical experiment or optimized estimate. The combined
axiom audit now passes with the finite-cubic leaf.

The finite-cubic production leaf defines the full two-output Gram, proves its positivity
from actual Fourier-pair independence, and certifies balanced complete cancellation.
The final statement is unconditional existence, for each prime, of a positive
theta parameter making every literal finite packet's COMPLETE associator zero while
its cubic displacement has no bound on that SAME literal prime core. This statement
is now certified. A common parameter cannot simply be chosen separately at each
prime; the mixed-prime source remains a separate obligation.

## Final certified checkpoint

Canonical result and audit record:
`../3-formalized/tg-fourier-jet-theta-cubic-classification.md`.
Both new production leaves and all 29 added/exposed public axiom audits pass, using
only the standard three foundations. Literal finite coefficient action, complete
single-prime cancellation, same-core displacement obstruction and balancing-prime
uniqueness are included. Bounded displacement is retired with that positive survivor:
`../5-failed/tg-fourier-jet-bounded-cubic-displacement.md`.

The theta graph-closure conjecture is now certified in
`../3-formalized/tg-prime-theta-graph-closure.md`: the finite two-prime action is
single-valued, but its closure is G×G at every nonzero parameter and the closed neutral
graph at zero. A closed extension exists exactly at zero. The next active conjecture
is `tg-fourier-jet-mixed-cubic-closure.md`, keeping the COMPLETE varying-prime cubic.
General mixed-prime cubic cancellation and Gamma–Xi/Hardy/sub-unit production remain
open. This research parent stays open for that complete cubic.
