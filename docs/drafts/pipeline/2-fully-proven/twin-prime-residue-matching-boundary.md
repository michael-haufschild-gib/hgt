# Relative centering becomes an exact residue matching

- **ID:** twin-prime-residue-matching-boundary
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / NO-GO with positive survivor; classical finite geometry
- **Source:** [fixed-determinant normalization](../1-in-progress/twin-prime-fixed-determinant-uniformity.md)
  and [coupled centering](twin-prime-coupled-residue-centering.md).
- **Statement:** A growing congruence modulus can turn the rough-shift operator into a matching. An explicit bounded second row then attains its full positive mass, even with the actual Liouville first row.

## Exact strengthening under attack

The proved paper centering estimate is normalized by the ambient horizon
`Y`. Could its arbitrary bounded second-row formulation instead hold,
uniformly in the modulus `l`, after normalization by `Y/l`?

Specifically, replace `1/Y` by `l/Y` in the coupled-centering statement,
retaining its `O(L^(-21/20))` bound and its freedom to choose any second
row `g` with `|g|<=1`. The first row is the actual Liouville function,
the shift multiplier is `h=1`, the residue is `r(z)=z mod l`, and all
shift coefficients equal one. These are already enough to refute the
strengthening. This is not the fixed-determinant two-Möbius conjecture.

## Complete positive survivor

For natural `D,K`, put `l=4D+1`, `Y=l(K+1)`, and

`P_D={p prime : D<p<=floor(6D/5)}`,
`g_D(w)=lambda(w-floor((w mod l)/2))`.

Use the arithmetic convention `lambda(0)=0`. Thus `|g_D(w)|<=1`
for every natural `w`; no cancellation property of this row is assumed.
Define the finite coupled correlation

`S(D,K,g)=sum_(p in P_D) (1/p)
   sum_(1<=v<=Y) 1_(v mod l=p) lambda(v)g(v+p)`.

The exact identity is

`S(D,K,g_D)=(K+1) sum_(p in P_D) 1/p`.                 (1)

Moreover every real unit-bounded second row obeys

`|S(D,K,g)| <= (K+1) sum_(p in P_D) 1/p`.              (2)

Consequently (1) is the exact maximum, not only a lower estimate.
The same row works for every horizon multiple `K+1`.

### Finite proof

Every `p in P_D` satisfies `0<p<=2D`, hence `2p<l`. If
`v mod l=p`, then `(v+p) mod l=2p`, so

`g_D(v+p)=lambda(v+p-p)=lambda(v)`.

Since `v>=1`, the summand's two Liouville factors multiply to one.
The selected integers in `[1,l(K+1)]` are exactly

`v=l k+p`, `0<=k<K+1`.

This follows from Euclidean division, using `0<p<l`; it includes
both endpoints without an error term. There are exactly `K+1`
selected terms for each prime. Summation proves (1).
For (2), each selected product has modulus at most one and the
reciprocal weights are nonnegative. Triangle inequality gives the
same count. This proves sharpness.

The incidence interpretation is literal: different `p` have disjoint
input classes `p mod l` and disjoint output classes `2p mod l`.
Thus these edges form a partial matching, and the second row can
align every edge independently. No analytic oscillation survives
in this arbitrary-row norm.

### Arithmetic mass

The already certified theorem
`TwinPrime.lowerFactorPrimes_log_mass_tendsto` gives

`sum_(p in P_D) log p >= D/10`

for all sufficiently large `D`. For every such prime,

`p log p <= 2D log(2D)`.

Multiplying by `1/p`, summing, and dividing by the positive
`2D log(2D)` proves

`sum_(p in P_D) 1/p >= 1/(20 log(2D))`.                (3)

Combining (1)--(3), uniformly for every `K`, gives

`(l/Y) S(D,K,g_D) >= 1/(20 log(2D))`.                 (4)

All inputs are finite identities or the existing unconditional PNT
certificate. No conjectural input or unknown analytic premise enters.

## Failure on the proposed centering scales

Take `D=ceil(exp L)` as `L` tends to infinity. These prime shifts
are all rough past `exp(L^0.99)`, and their block lies within the
allowed bounds `exp(L^0.995)/2 <= D <= exp(2L)`. Choose `K` as
large as needed so `Y=l(K+1)>=exp(L^A/2)` for any prescribed
`A>=1000`. Formula (4) is bounded below by a positive constant
times `1/L`. That cannot be `O(L^(-21/20))` uniformly in the
second row and modulus. The lower bound has no horizon error.

**Verdict: FALSE** for the universal relative-centering strengthening.
The strongest positive survivor is the exact matching norm (1)--(2),
together with its unconditional prime-mass lower bound (4).
It requires a two-row arithmetic mechanism in any relative estimate;
even a perfect one-row short-sum theorem cannot overcome this matching.

## Corpus and external-parent audit

Corpus searches for relative-density affine correlation, residue-class
counts, Liouville norms, and weighted matching norms precede mathlib.
The Liouville identities and the existing prime-block PNT theorem were
checked at source. No correlation premise is used.

Theorem 1.3 of the checked primary
[Matomäki--Radziwiłł--Tao paper](https://arxiv.org/pdf/1503.05121v3)
averages short exponential sums over the ambient starting-point range.
It does not assert the false relative progression estimate above.
The existing coupled-centering paper deduction remains compatible
with this example: its `1/Y` normalization adds the factor `1/l`.

No new number-theoretic knowledge is claimed. This is an exact finite
operator boundary for the proposed transfer, using a classical prime
mass consequence. It does not refute cancellation with both rows fixed
to Möbius or Liouville, and does not prove any positive twin-prime mass.

## Gates

- [x] Exact conjecture, explicit attack and failure on its own scales.
- [x] Positive survivor with dependency-closed paper proof.
- [ ] Unconditional Lean certificate and transitive axiom audit.
- [ ] Close only the universal transfer route; retain the actual-row target.

## Log

- 2026-10-23 — Constructed the residue-decoding second row and proved
  exact saturation. The fixed-determinant cancellation target and
  twin-prime infinitude remain open.
