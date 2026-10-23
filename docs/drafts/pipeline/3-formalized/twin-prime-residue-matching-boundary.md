# Relative centering becomes an exact residue matching

- **ID:** twin-prime-residue-matching-boundary
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / NO-GO with positive survivor; classical finite geometry
- **Lean:** `formal/GaloisForLFunctions/twin-prime/SemiprimeEnergy.lean`
- **Source:** [fixed-determinant normalization](../1-in-progress/twin-prime-fixed-determinant-uniformity.md)
  and [coupled centering](../2-fully-proven/twin-prime-coupled-residue-centering.md).
- **Statement:** A growing congruence modulus can turn the rough-shift operator into a matching. An explicit bounded second row then attains its full positive mass, even with the actual Liouville first row.

## Exact strengthening under attack

The proved paper centering estimate is normalized by the ambient horizon
`Y`. Could its arbitrary bounded second-row formulation instead hold,
uniformly in the modulus `l`, after normalization by `Y/l`?

Specifically, replace `1/Y` by `l/Y` in the coupled-centering statement,
retaining its `O(L^(-21/20))` bound and its freedom to choose any second
row `g` with `|g|<=1`. The first row is the actual Liouville function,
the shift multiplier is `h=4`, the residue is `r(z)=c z mod l`, and all
shift coefficients equal one. These are already enough to refute the
strengthening. This is not the fixed-determinant two-Möbius conjecture.

## Complete positive survivor

For natural `D,K`, put `a=4D+6`, `c=4D+2`, `l=ac`,
`Y=l(K+1)`, and

`P_D={p prime : D<p<=floor(6D/5)}`,
`g_D(w)=lambda(w-4 floor((w mod l)/a))`.

The primitive reduced frame `(a,1;c,1)` has determinant exactly
four. It is the actual canonical odd-cofactor frame for
`m=2D+1`, `k=2D+3`; these cofactors are coprime and exceed one
when `D>=1`. Thus the example retains the target's determinant
and intercept geometry.

Use the arithmetic convention `lambda(0)=0`. Thus `|g_D(w)|<=1`
for every natural `w`; no cancellation property of this row is assumed.
Define the finite coupled correlation

`S(D,K,g)=sum_(p in P_D) (1/p)
   sum_(1<=v<=Y) 1_(v mod l=c p) lambda(v)g(v+4p)`.

The exact identity is

`S(D,K,g_D)=(K+1) sum_(p in P_D) 1/p`.                 (1)

Moreover every real unit-bounded second row obeys

`|S(D,K,g)| <= (K+1) sum_(p in P_D) 1/p`.              (2)

Consequently (1) is the exact maximum, not only a lower estimate.
The same row works for every horizon multiple `K+1`.

### Finite proof

Every `p in P_D` satisfies `0<p<=2D<c<a`. If
`v mod l=cp`, then `(v+4p) mod l=(c+4)p=ap<ac=l`, so

`g_D(v+4p)=lambda(v+4p-4p)=lambda(v)`.

Since `v>=1`, the summand's two Liouville factors multiply to one.
The selected integers in `[1,l(K+1)]` are exactly

`v=l k+cp`, `0<=k<K+1`.

This follows from Euclidean division, using `0<cp<l`; it includes
both endpoints without an error term. There are exactly `K+1`
selected terms for each prime. Summation proves (1).
For (2), each selected product has modulus at most one and the
reciprocal weights are nonnegative. Triangle inequality gives the
same count. This proves sharpness.

The incidence interpretation is literal: different `p` have disjoint
input classes `cp mod l` and disjoint output classes `ap mod l`.
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

For every fixed positive slope exponent `eta`, `K` can also be
chosen so `a,c <= (Y/l)^eta`. Thus restricting the slopes to a
polynomially small range relative to the sample length does not
repair this arbitrary-row strengthening.

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
- [x] Unconditional Lean certificate and transitive axiom audit.
- [x] Close only the universal transfer route; retain the actual-row target.

## Certificate

The foreground leaf command passed:

`lake --old env lean GaloisForLFunctions/twin-prime/SemiprimeEnergy.lean`

All six capstones passed transitive axiom audits with exactly
`[propext, Classical.choice, Quot.sound]`:

- `TwinPrime.abs_residueMatchingRow_le_one`;
- `TwinPrime.residueMatchingCorrelation_saturated`;
- `TwinPrime.abs_residueMatchingCorrelation_le`;
- `TwinPrime.eventually_residueMatchingPrimeMass_ge`;
- `TwinPrime.residueMatchingRelative_eq_primeMass`;
- `TwinPrime.residueMatchingRelative_not_isLittleO`.

The sharp bound takes second rows valued in the real unit interval,
the natural domain of this finite operator. Its saturating row is
explicit and its bound is proved. No analytic cancellation premise
is assumed. The reciprocal-mass lower bound uses the existing proved
PNT consequence in the same leaf. The last theorem rules out
`o(1/log(2D))` along every choice of complete-block horizons `K(D)`.
The leaf's umbrella import already exists; no umbrella was compiled.
Audit directives were removed without changing proofs.

The [failed universal transfer](../5-failed/twin-prime-universal-relative-centering.md)
is closed with this positive survivor. The actual two-row target remains open.

## Log

- 2026-10-23 — Constructed the residue-decoding second row and proved
  exact saturation. The fixed-determinant cancellation target and
  twin-prime infinitude remain open.
- 2026-10-23 — Strengthened the construction to the canonical
  determinant-four frame before the final certificate. Full leaf
  and six transitive axiom audits passed. No new scientific
  cancellation theorem or twin-prime infinitude proof is claimed.
