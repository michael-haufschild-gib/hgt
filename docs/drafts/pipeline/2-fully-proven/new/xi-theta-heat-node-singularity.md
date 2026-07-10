# The infinite theta reader is forced to be singular at the compactified heat boundary

- **ID:** xi-theta-heat-node-singularity
- **Stage:** 2-fully-proven
- **Type:** THEOREM / READER-CATEGORY OBSTRUCTION, [PROVED HERE]
- **Date:** 2026-07-10
- **Lean:** formal/GaloisForLFunctions/RHTower/XiThetaHeatNodeObstruction.lean
- **Parent:** ../../5-failed/theta-composite-heat-reader.md

## Medalist lens

The missing reader can be sought in three categories:

1. [CONJECTURE] an analytic moment symbol in the compactified node x=exp(-pi m squared);
2. [BRIDGE] a limit of finite Lagrange moment interpolants;
3. [CONJECTURE] a Hardy/Blaschke symbol in the uncompactified rate z=m squared.

The first category would be the cheapest and would avoid building half-plane Hardy theory. It must
therefore be attacked first.

## Compactified square spectrum

Define

x_m=exp(-pi m^2),    m>=1.                                  (1)

Then

x_m>0,    x_m -> 0.                                         (2)

A compactified moment-series reader holomorphic on a connected domain containing zero and all
nodes would have a symbol F with delta interpolation

F(x_n)=1,

F(x_m)=0 for every m!=n.                                    (3)

## Theorem A [PROVED]: connected holomorphic symbols cannot omit one node

Let U be a preconnected subset of the complex plane containing zero and every x_m. Let F be
holomorphic on a neighborhood of every point of U. If

F(x_m)=0

for every positive m other than a fixed n, then

F(x_n)=0.                                                    (4)

### Proof

The zero sequence x_m with m tending to infinity lies in the punctured neighborhoods of zero and
accumulates at zero. The isolated-zero theorem gives two alternatives at zero:

1. F vanishes on a neighborhood of zero; or
2. F is nonzero on a punctured neighborhood of zero.

The second alternative contradicts the tail of the zero sequence. Hence F vanishes near zero.
The identity theorem propagates this equality across U, including x_n, proving (4). Taking U to
be the complex plane gives the entire-symbol corollary.

## Corollary B [PROVED NEW]: no connected holomorphic compactified delta reader

There is no F satisfying (3) that is holomorphic on a connected compactified domain containing
zero and every node. In particular, there is no entire such F.

Therefore finite polynomial moment readers cannot converge locally uniformly on such a domain to
a holomorphic delta symbol while retaining exact interpolation on the infinite square spectrum.

## The forced singularity

The obstruction is not that interpolation is impossible. It is that a compactified moment symbol
defined across a connected domain containing the nodes cannot be analytic through the boundary
x=0.

Under the rate coordinate

z=-(1/pi)log x,

the accumulation point x=0 is sent to z=infinity, while x_m is sent to m squared. The half-plane
Blaschke reader lives precisely in this uncompactified rate plane. For any reader admitting a
connected compactified moment symbol, nonanalyticity at x=0 is therefore forced by the infinite
delta constraints, not an artifact of one construction.

## Attack verdict

 retains the infinite delta data.
 compactified heat boundary.
- [FALSIFIED] Build the infinite reader as a moment-generating symbol holomorphic on a connected
  compactified domain containing zero and all nodes.
- [FALSIFIED] A locally uniform limit of finite polynomial readers on that domain remains
  holomorphic and retains the infinite delta data.
- [PROVED OBSTRUCTION] Every exact reader admitting such a compactified moment symbol must be
  singular or nonanalytic at the compactified heat boundary.
- [SELECTED] Work in the uncompactified rate half-plane, where the square nodes escape to infinity
  and the Blaschke condition sum 1/m squared is compatible with interpolation.

## Novelty and significance gate

- **Parent theorem:** isolated zeros and the identity theorem are classical.
- **New project obstruction:** compactifying the exact heat atoms from the completed source turns
  the infinite coefficient constraints into a forced boundary singularity theorem. It decides
  which holomorphic compactified reader category is possible before any Hardy construction.
- **Significance:** this prevents replacing the missing Paley-Wiener reader by an easier analytic
  moment series. Within the connected holomorphic-symbol model, the rate plane is mathematically
  forced.

## Open core

[OPEN CORE] Construct the fixed-index reader in the uncompactified rate half-plane and identify its
source-side L2 representative. If it admits a connected compactified moment symbol, that symbol
must carry the singularity proved here.

## Gates

- [x] 0 -> 1: competing reader categories and the accumulation constraint isolated.
- [x] 1 -> 2: node convergence and connected-domain holomorphic-reader obstruction proved.
- [x] 2 -> 3: formalized and axiom-audited.
- [ ] 3 -> 4: requires the singular rate-plane reader and reflected Perron composition.
