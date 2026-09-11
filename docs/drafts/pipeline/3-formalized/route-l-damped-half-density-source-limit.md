# Route L: actual damped half-density source beyond the Meyer limit

- **ID:** L-C43
- **Date:** 2026-09-11
- **Stage:** 3-formalized
- **Type:** THEOREM / actual nonzero half-density source limit and quantitative error
- **Depends on:** [C42 negative Mellin growth](../3-formalized/route-l-damped-negative-mellin-escape.md), C39 fixed source transport
- **RH status:** unproved

Chain: complete original Green/BV source → fixed-reader agreement →
conormal vanishing → RH. C42's fixed negative detector excludes the
bounded-damping finite product limit in the ORIGINAL Meyer topology.
The next source candidate must be constructed in an actual weaker space,
with its complete boundary and fixed reader identified there.

## Closed actual source construction

Use the literal weighted embedding `H_c g(t)=exp(c*t)g(t)` into logarithmic
L2. The exact source flow becomes `H_c(T_d g)=exp(c*d) U_(-d) H_c(g)`,
where the repository's translation with parameter b is `f(t+b)`.
At c=1/2, the original paired prime defect is therefore

`E_(p,a)=(Id-w_p U_(-log p))(Id-w_p U_(log p))`,
`w_p=p^(-a-1/2)`.

These are the two literal source factors, with no probability normalization.
Their adjoint relation is proved directly against the original measure-
preserving translations. For every f and 0<=w_p<=1,

`(1-w_p)^2 ||f|| <= ||E_(p,a)f|| <= exp(2*w_p)||f||`,
`||E_(p,a)f-f|| <= 3*w_p||f||`.

Define `F_N=H_(1/2)(g_(primesLE N,a))` from C42's ACTUAL source, with each
original prime used once. Faithfulness of the literal entire Mellin transform
identifies the exact successor source: apply E at N+1 when N+1 is prime,
and leave F_N unchanged otherwise. This proves the recurrence for the
original finite-set presentation, without assuming a source/limit comparison.

For a>1/2 let `w(n)=1_(n prime) n^(-a-1/2)` and
`B=exp(2*sum_(n>=1) w(n))*||F_0||`. The real p-series gives summability.
The exact recurrence gives `||F_N||<=B` and

`||F_(N+1)-F_N|| <= 3*w(N+1)*B`.

Consequently F_N is Cauchy in ACTUAL unquotiented L2. Its limit has a
quantitative tail error bounded by the corresponding summable prime tail.
For nonvanishing, retain the lower product: its limit is
`exp(sum_(n>=1) log(1-w(n)))>0`. The original half-density Gaussian is
nonzero, so the source limit has strictly positive norm. At a=1 this yields
an explicit nonzero limit with no supplied convergence, cofinality,
source-incidence, RH or critical-line premise.

This direct whole-source argument replaces the proposed Mobius-series
construction as the immediate proof. It proves the actual vector limit;
it does not yet identify an operator-norm product or its arithmetic inverse.
The earlier Mobius proposal remains a separate possible identification:
for sigma=a+1/2>1 the unnormalized translation series with coefficients
mu(n)n^(-sigma) and n^(-sigma) should be inverse operators after absolutely
convergent divisor regrouping. No such inverse theorem is claimed here.

## Remaining comparison obligations

1. Identify literal Mellin readings in the open strip at a=1. The exact
   general-weight source conjugacy above supplies the next mechanism:
   weighted control should hold when `1-a<c<a`. Prove the actual weighted
   source limits and compatible representatives, then justify the Mellin
   integrals and every retained divisor jet. Plain half-density L2 does not
   admit off-axis Mellin evaluation as a continuous functional.
2. Admit endpoint weights c=0,1 and ORIGINAL unweighted prime-circle sums
   separately. Interior-strip convergence alone does not establish them.
3. Extend the ORIGINAL complete Green/BV boundary and its fixed physical
   reader to the actual weaker source, retaining all prime/depth/copy data,
   unchanged Gamma residue normalization and nonzero Xi leading coefficient.
4. Calculate the full discrepancy before continuing damping. A nonzero
   source limit and positivity do not supply a vanishing physical image.

## Lean verification

`formal/GaloisForLFunctions/RHTower/DeningerDampedHalfDensitySourceLimit.lean`
contains 486 lines: 25 public theorems, 10 definitions, one abbreviation and
seven private lemmas. Scratch `lake env lean /tmp/route_l_c43_halfdensity.lean`
passed without errors or warnings. The final targeted audit
`lake build GaloisForLFunctions.RHTower.DeningerDampedHalfDensitySourceLimit`
passed; only this new leaf was built (40 seconds, 11945 dependency-graph jobs).
One umbrella import and 36 public declarations without cross-module name
collisions were verified. Global lint passed. The index refresh passed,
updating the three generated Lean API documents and three changed sources.
The new card links and targeted whitespace diff check passed. All owned
Lean and research jobs finished; no owned Lean process remains.

The general-weight source flow and literal half-density paired conjugacy
are closed. The final concrete theorem is
`deningerDampingOne_original_source_limit`; its witness is the actual
`deningerDampedHalfDensityLimit`, not an unrelated supplied Hilbert vector.
`deningerDampedHalfDensityPrefix_error_bound` retains the exact summable tail,
and `deningerDampedHalfDensityLimit_ne_zero` uses the positive lower product.
`deningerHalfDensityPairedPrime_energy` proves the adjoint-square energy
identity for every original finite factor. No complete infinite operator
positivity or inverse theorem is claimed.

No full/umbrella build, numerical experiment, axiom-print command, added
axiom or proof placeholder was used.

## Next exact attack

[Weighted source and original boundary](../1-in-progress/route-l-damped-weighted-source-boundary.md)
contains the next proof mechanism and its admission obligations. The general
weighted conjugacy changes the two prime weights separately; it must not
be treated as an isometry off the half-density weight.

## Hard continuation obstacle

The operator-norm convergence argument uses a>1/2. It gives no uniform
source bound as damping decreases to zero. On the Fourier line, the
candidate multiplier is `1/|zeta(a+1/2+i tau)|^2`, with the frequency scale
to be matched exactly to the repository's Fourier convention. Continuation
through a zeta zero would introduce a pole; a source-admission or energy
bound excluding such poles cannot be assumed. The missing original
Green/BV-to-fixed-reader comparison must produce that control, or expose
the precise additional boundary term. Positivity in the initial convergence
chamber alone does not cross this obstacle.


## Checked corpus anchors and search coverage

- `InfiniteMobiusSignedChannel.lean` 214–269 constructs a summable actual
  logarithmic L2 shift series and its norm bound. Its coefficients are
  `signedMobiusProbability`, divided by `squarefreeMobiusTotal(sigma)`.
  Recover the literal unnormalized arithmetic coefficient before matching
  B; do not transfer the normalized contraction directly. The total is
  positive and equals a zeta ratio in that module.
- `L2MellinUnitary.lean` 92 defines `MellinL2.additiveTranslationUnitary`
  by pullback along `realTranslationEquiv`, which is addition on the right.
  Thus its parameter b gives `f(t+b)=U_(-b)f(t)`. The existing signed
  average at parameter `-log(n)` supplies `U_(log n)`, the mate orientation
  of B above. Its adjoint supplies B after restoring the arithmetic total.
  Match this identity explicitly before transporting finite factors.
- `ZetaTwoShiftContraction.lean` 180 is a normalized corrected composition,
  not the unnormalized inverse C proposed above.
- Do not identify the separate quotient L1 half-density completion with the
  unquotiented actual L2 source used here.

Deep/method report `/tmp/route_l_damped_c43_halfdensity_deep.json`: all 20
candidate lemmas and 20 source arguments inspected. Generation 875271,
semantic 2354488/2354488, partial because of deadline/coverage and background
source refresh. Suggested convolution and floor-sum ingredients were not
verified and are not used as premises. The earlier distributional search
`/tmp/route_l_damped_c42_distribution_deep.json`, generation 875206,
semantic 2354317/2354317, was partial due to source refresh. Its rectangle
residue ingredients require pole and boundary admission; they do not
construct the present limit or control damping continuation.

## Current source/method search and distant-paper checks

`/tmp/route_l_c43_operator_product_deep.json` searched the complete indexed
corpus for summable translation operators and original finite factors.
All 20 candidate lemmas, 20 source arguments, two generated ideas and the
proposed ingredient group were inspected. Generation 875394; semantic
2354686/2354686. Partial only because source refresh remained active. The
generated coupling/Euler-product group does not prove convergence and is
not used as a premise. Exact checked mathlib bodies instead supply the
summable-successive-distance criterion and the positive real log-product.

Broad single-word searches `factorization`, `resolvent`, `damping` found:

- [Lavi, September 1](https://arxiv.org/abs/2609.00894): generalized-series
  factorization under support-order restrictions; no established transfer.
- [Chaudhary, September 9](https://arxiv.org/abs/2609.10391): product spectra
  and symmetric-function identities; no source-domain result transferred.
- [Chen, August 26](https://arxiv.org/html/2608.25458v1): Section 3 relates
  weighted resolvent bounds to an unweighted estimate, but its spectral
  bound requires uniform Fourier decay on regular level surfaces. The
  original source has not supplied that hypothesis; no estimate imported.
- [Vega Coso, August 15](https://arxiv.org/html/2608.15140v1): weighted
  reflection conjugates a concrete Markov model. The claimed spectral
  duality is tied to a resolvent intertwining law and original boundary
  fluxes; no Markov symmetry or vanishing source flux is transferred.

The last two papers reinforce testing the actual conjugation and boundary
terms. The present inequalities and convergence proof use literal source
identities and checked corpus lemmas, independently of those papers.
