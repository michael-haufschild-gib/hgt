# Route L: fixed negative Mellin amplification of damped sources

- **ID:** L-C42
- **Date:** 2026-09-11
- **Stage:** 3-formalized
- **Type:** THEOREM / uniform full-source growth, nonconvergence and compact escape
- **Depends on:** [C41 literal damped residual](../3-formalized/route-l-damped-prime-green-residual.md), [C40 original Meyer Mellin continuity](../3-formalized/route-l-cofinal-green-source-limit.md)
- **RH status:** unproved

Chain: complete original Green/BV source → fixed-reader agreement →
conormal vanishing → RH. C41 attacks the actual approximate prime kernel.
Its single-circle contraction does not supply a source limit. This attack
tests the entire normalized source at one fixed negative Mellin point.

## Exact finite-product proof

For an original prime p, L=log(p), and 0≤a≤1, the actual paired multiplier is

`A_(L,a)(s)=(1-exp(-(a+s)L))(1-exp(-(a+1-s)L))`.

At s=-4 set U=exp((4-a)L), V=exp(-(a+5)L). Then

`U≥p^3≥8`, `0<V≤p^(-5)≤1/32`.

Therefore `|A_(L,a)(-4)|=(U-1)(1-V)≥217/32`.
At every actual Xi point rho, the open-strip placement gives
`|exp(-(a+rho)L)|≤1` and `|exp(-(a+1-rho)L)|≤1`.
Hence `0<|A_(L,a)(rho)|≤4`, and

`|A_(L,a)(-4)/A_(L,a)(rho)|≥217/128>1`.

Let g_(P,a) be the actual finite ordered product of paired damped source
operators applied to the original reflected Gaussian g0. Repetitions are
retained. Exact Mellin transport and nonvanishing of M(g0) give

`|M(g_(P,a))(-4)/M(g_(P,a))(rho)|`
`≥(217/128)^length(P) * |M(g0)(-4)/M(g0)(rho)|`.

The last Gaussian factor is strictly positive. Thus for any source family
with lengths tending to infinity and damping eventually in [0,1], Xi
normalization to reading one forces this fixed negative reading to diverge.
This includes any vanishing nonnegative damping, regardless of whether
its prime-circle residuals vanish. Continuity of literal M(-4) in the
ORIGINAL Meyer topology then forces escape from every compact set and
excludes every source limit there.

This is a positive quantitative survivor: a fixed original-source
functional detects growth with an explicit uniform factor per original
prime/depth. It is stronger than merely noting failure of an upper bound.
No numerical experiment or critical-line assumption enters the proof.

## Verified actual sources and explicit limit families

`formal/GaloisForLFunctions/RHTower/DeningerDampedPrimeMellinGrowth.lean`
constructs the literal ordered finite source product, proves its entire
Mellin formula and weighted-reflection fixedness, and normalizes by its
nonzero actual Xi reading. The uniform negative-coordinate estimate applies
to the whole source, retaining all original primes and repeated depths.

For any list family whose lengths tend to infinity and any varying damping
sequence in [0,1], the norm of the fixed original-source reading at -4 tends
to infinity. Its continuity gives compact escape and excludes every
original-Meyer source limit. Cofinal prime lists have lengths tending to
infinity; the proof passes through their finite-set cardinalities.

The module includes original prime prefixes and repeated depths of one
original prime. The explicit positive choice `a_n=1/(n+1)` is proved to
tend to zero, and the corresponding original-prime prefix source is proved
to have no Meyer limit and to escape every compact set. These explicit
corollaries have no cofinality, growth, source-admission or RH premise.

## Verification

Final scratch `lake env lean /tmp/route_l_damped_c42.lean` passed with no
errors or warnings. It is byte-identical to the final module: 317 lines,
21 public theorems and four definitions. The targeted audit
`lake build GaloisForLFunctions.RHTower.DeningerDampedPrimeMellinGrowth`
passed; only the new leaf was built (69 seconds, 11944 dependency-graph
jobs). One umbrella import and 25 public declarations with zero
cross-module name collisions were verified. Global lint and index refresh
passed. No full/umbrella build, numerical experiment, axiom-print command,
added axiom or proof placeholder was used. All owned Lean/research
processes finished.

## Boundary and next pivot

This excludes the proposed product limit with damping in [0,1]
in the original Meyer space, including the explicit vanishing choice. It does not exclude a weaker distributional
source topology where M(-4) is discontinuous, nor prove the original
physical boundary vanishes. Any such weaker source must still admit the
complete Green/BV boundary and its original fixed physical reader; a
meromorphic Euler continuation does not establish that admission.

The September 2026 [Chebyshev amplification paper](https://arxiv.org/html/2609.09033v1)
motivated testing a fixed point outside the controlled measurement region.
The inequalities above follow directly from C41's literal source multiplier;
no pseudo-density, positivity or spectral-gap premise is transferred.


## Corpus audit

The negative-evaluation deep/method query inspected all 20 candidate lemmas
and 20 source arguments, plus coverage and empty generated idea/ingredient
lists. Generation 875031; semantic 2353393/2354062. The report is partial
(deadline, filter/judge, background source refresh), stored at
`/tmp/route_l_damped_c41_negative_anchor_deep.json`. Mellin continuation
hits require half-plane or Sonin-admission premises; none identifies an
original-Meyer limit of this finite product. C40 already supplies the exact
original-source continuous functional needed for the proposed divergence
proof.


## Next concrete source

[The actual half-density limit](route-l-damped-half-density-source-limit.md)
is now closed: the literal original-prime Gaussian source converges to a
nonzero vector in unquotiented L2 for every fixed damping greater than one
half, with an explicit tail error and positive lower bound. The finite
source factors have their exact adjoint-square energy identity. No supplied
source/limit identification or probability normalization enters.

[Weighted admission and original boundary](../1-in-progress/route-l-damped-weighted-source-boundary.md)
now attacks the same limit's Mellin readings, complete Green/BV domain and
fixed physical reader. Full damped Xi-field/Green/Sonin identification and
continuation toward zero damping remain open.
