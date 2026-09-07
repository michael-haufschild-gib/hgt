# CCM-FU: growing coupled prime batches

- **Stage:** 3-formalized
- **Type:** [BRIDGE] / derived theorem candidate
- **Parent:** [adaptive prime ceiling](../1-in-progress/ccm-fu-adaptive-prime-ceiling.md)
- **Result:** Unconditional growing batches of actual coupled prime packets, with every selected prefix under one fixed quadratic energy ceiling.

## Full proof chain and obligation

Guinand–Weil source → marked rectangular current → affine Suzuki checkpoints
→ signed curvature → prime–polar–Gamma/unit-Riesz boundary → Xi-screw Green
→ RH. Complete adaptive source coverage remains the missing arithmetic bound.
Fixed scalar reserves cannot repair the inherited middle-singleton sector.

The exact quotient-packet identity in `MobiusDivisorQuotientWindowOrder`
retains an entire smaller field, not just its head. Prepare a fixed finite
prime core while leaving prime two unprocessed. At child cutoffs inside that
core, the only possible labels are empty and {2}. Later primes therefore
supply coupled two-coordinate packets, and their two adjacent endpoint
fields determine the clipped packet exactly.

## Frozen diagnostic

Use the actual complete signed source S(K). With all child primes except two
processed, the {2} coordinate equals the sum of actual channels whose labels
contain two; the head is the sum of those whose labels do not. Evaluate these
two coordinates for every child cutoff K from 2 through 512. Determine whether
the packet directions positively span the plane, and extract the smallest
strict finite witness if present. Compare direct label grouping with exact
prime-two clipped reflection as an independent check.

Run only on RunPod, with multicore Python and a 120-second foreground timeout.
Download script, all profiles and summary to the computations directory.
The diagnostic is not a Lean premise and cannot certify a source estimate.

## Formalization gate

If a strict witness exists, prove its actual source signs and determinant
inequalities analytically, retaining both clipped endpoints. Then determine
whether finite packet rounding and ordering convert its macroscopic prime
windows into a bounded-energy coupled batch. A positive spanning statement
alone is not a complete adaptive order or SD1. If spanning fails, establish
an exact source separator before drawing a general conclusion.

## Evidence and selected analytic construction

The bounded RunPod screen completed in 0.0185 seconds with eight workers on
a 32-core host. Its first strict three-direction witness is K=2,3,13;
direct grouping and prime-two clipped reflection agree to absolute error
below 1e-17 throughout all 511 inspected profiles. The frozen output is in
[the computation directory](../2-fully-proven/computations/ccm-fu-coupled-prime-packets-2026-09-07/summary.json).

For the analytic proof use K=2,7,14: the first vector has positive head and
zero second coordinate, the second has both coordinates negative, and the
third has negative head and positive second coordinate. The source at seven
already has an analytic certificate. At fourteen, prime-two reflection gives
its second coordinate as minus sqrt(2) times the head at seven. Negativity
of the complete source at fourteen follows from the existing source box at
eleven and analytic bounds on the next three source increments. This avoids
using any numerical profile value or a new table of individual channels.
The fixed core is all primes below fifteen except two. Positive spanning, uniform clipping, actual macroscopic-window transport and
growing bounded-energy batch selection are formal. Exhaustive source coverage
and complete adaptive ordering remain open.

## Uniform source-direction margin

This bridge is chosen to advance the existing complete adaptive source bound;
it does not replace or weaken that primary obligation. Its statement follows
the available source identities and is not a new universal conjecture.

For the three sign-certified profiles V2=(a,0), V7=(b,c), V14=(d,e),
with a>0, b<0, c<0, d<0, e>0, every nonzero test vector has positive
pairing with at least one profile. Their positive circuit has weights
`(dc-be)/a`, `e`, `-c`. The maximum of the three pairings is strictly
positive on the compact unit sphere. Its positive minimum supplies a
uniform margin proportional to the test-vector norm. A sufficiently small
perturbation of each profile preserves half that margin, providing the
needed tolerance for the exact adjacent-cutoff interpolation.

The intended common parent scale is `14(b+1)N`. Three macroscopic prime
windows near its quotients two, seven and fourteen copy these profiles.
The core below fifteen excluding two fixes their child fields while leaving
actual coupling to the {2} coordinate. Finite selection, exact energy accounting and the lower bound on batch length
are formal. The resulting partial order must not be presented as a complete
source schedule.

## Exact energy mechanism

Once the complementary child core is processed, an available prime packet
has only empty and {2} child coordinates. If the current coordinates are
`x=(F(empty),F({2}))` and its reflected packet is `v`, the complete energy
change on consuming that prime is exactly `2 dot(x,v)`. The packet's own
retained squares cancel the squares created in the receiving coordinates.
Thus three available packets whose opposite directions span the plane
always permit a nonincreasing-energy step, including equality at `x=0`.
This is control of complete energy, including the nonempty coordinate.

Primes in the three macroscopic windows are inactive at every child cutoff
through fifteen. Consuming any selection of them therefore leaves all three
child profiles fixed. A greedy selection can continue until one pool is
exhausted, giving at least the minimum of their cardinalities in safe steps.
Common-window quotient/clipping control, prime supply, finite greedy endurance
and the fixed core's energy budget are formal. This mechanism still leaves
other source primes unprocessed.

## Dependency-closed paper proof

1. Set `P0=primes_below(15) \ {2}` and `V_K=(F_(K,P0)(empty),F_(K,P0)({2}))`.
   Every other child label vanishes for `K<=15`. The original channel bound
   at eleven gives `S(11)<=-28/100`. The exact complete-source Abel identity
   adds the next three increments to obtain S(14). Analytic estimates give
   `psiDefect(11)<=1/2`, `psiDefect(12)<=0`, `psiDefect(13)<=6/5`,
   `sqrt(12)-sqrt(11)<=3/20`, and `sqrt(14)-sqrt(13)<=7/50`.
   All clock increments are nonnegative, hence `S(14)<=-37/1000<0`.
   These estimates use exact von Mangoldt values and proved logarithm and
   Euler--Mascheroni bounds, never saved profile values.
2. The actual signs are `V2=(a,0)`, `V7=(b,c)`, `V14=(d,e)` with
   `a>0`, `b,c,d<0`, `e>0`. The signs at seven are already certified;
   prime-two reflection gives `e=-sqrt(2)*b`, and `d=S(14)-e<0`.
   The positive circuit weights are `(dc-be)/a`, `e`, `-c`.
   Quadrant cases show every nonzero test vector has positive pairing with
   one of these three source vectors.
3. The maximum pairing has a positive minimum on the compact unit sphere.
   Its homogeneity gives margin `c0*norm(z)` everywhere. For the product
   norm, pairing error is at most `2*norm(z)*norm(delta)`. Put
   `D_K=V_(K+1)-V_K` and `B0=1+norm(D2)+norm(D7)+norm(D14)`.
   Independent clipping weights in `[0,c0/(4B0)]` preserve half the margin.
4. Choose one integer `b>=15` with `140/b` below this tolerance. At parent
   `M=14(b+1)N`, use prime windows `(7bN,7(b+1)N]`, `(2bN,2(b+1)N]`,
   and `(bN,(b+1)N]`. Their exact quotients are respectively 2, 7 and 14.
   Rationalizing the clock differences and using
   `sqrt(K+1)-sqrt(K)>=1/10` for `1<=K<=14` gives `b*w<=140`.
   Every pool prime is at least fifteen and below M.
5. Any selected pool subset is inactive at all child cutoffs through
   fifteen. Each next copied field therefore retains the same two
   interpolated coordinates. Its exact complete-energy change is
   `-2*sqrt(p)*dot(x,V_K(w))`, where x is the current head/{2} pair.
   The square of the removed copied field cancels the receiving square.
   Among one available prime from each window, the margin supplies a
   nonnegative pairing and hence a nonincreasing-energy step.
6. Before the selected cardinality reaches the minimum of the three pool
   cardinalities, every pool still has an unused prime. Induction produces
   a distinct list of that minimum length; every prefix stays below the
   initial prepared-core energy. Each preparation merger costs at most a
   factor two, the core has at most fifteen primes, and the original
   diagonal is at most `722*M^2`. Thus every selected prefix is bounded by
   `2^15*722*M^2`, independently of N and the selected length.
7. The corpus prime-window theorem implies that each fixed nontrivial
   multiplicative window eventually has at least any prescribed finite
   number of primes. Its three integer dilations have the same property.
   Their minimum cardinality therefore tends to infinity.

## Lean certificate

- `ThreePlaneSourceMargin`: uniform planar margin and perturbation control.
- `PartialSubsetEnergyOrder`: finite safe-step extraction with every prefix bounded.
- `MobiusDivisorCoupledTwoSourceCone`: actual source signs, positive circuit,
  uniform directional margin and common clipping tolerance.
- `MobiusDivisorCoupledTwoPrimeBatches`: exact two-coordinate energy change,
  actual clipped descent, fixed-window source supply, unconditional bounded
  batches and eventual growth of their guaranteed capacity.

All four leaves passed foreground `lake env lean` checks, with only needed
new oleans emitted. All 26 new public declarations were audited once via a
scratch import: only `propext`, `Classical.choice`, and `Quot.sound` occur.
All four modules are wired into the umbrella; no full or umbrella build ran.
`scripts/formal_tools.py lint` passed, with existing large-file warnings.
Numerical evidence remains guidance only.

## Remaining RH obligation

These lists leave prime two and other source primes unprocessed. Neither
arbitrarily long safe partial orders nor this fixed two-coordinate control
implies a cofinal complete order. Must propagate source-derived control while
changing the retained field and consuming the remaining primes, within a
uniform budget. SD1, the complete adaptive ceiling and RH remain open.
