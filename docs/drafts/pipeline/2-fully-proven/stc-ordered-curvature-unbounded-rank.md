# Ordered cross-prime curvature has unbounded exterior rank

- **ID:** `stc-ordered-curvature-unbounded-rank`
- **Stage:** 2-fully-proven (paper)
- **Type:** structural no-go with a four-channel positive survivor
- **Routes:** STC, RHist, cross-prime Gamma-six/Sonin source lift
- **Status:** `[PROVED HERE ON PAPER] [FOUR-CHANNEL IDENTITY FORMALIZED] [RANK THEOREM LEAN PENDING] [NOT AN RH PROOF]`

## Reinterpretation

The analytic reflection-odd scalar `c_pq(g)` in
`RouteRCrossPrimeStokesCalkinPolarHandoff.lean` is symmetric in `p,q`.
At a nonneutral grade it is a sum of only four separable one-prime
channels. The ordered seam, however, places `+c_pq` above and `-c_pq`
below the diagonal. This order sign turns the low-rank symmetric kernel
into an alternating matrix of arbitrarily large rank. Pair curvature
therefore cannot be represented by *any fixed finite number* of
one-prime exterior sections across all prime packets, even if the
universal second section in the current STC seam is replaced.

This is a theorem about directly assigning the existing analytic
`c_pq` to every prime pair. The literal Gamma exterior has the
all-prime **scalar** calibration proved in
`stc-all-prime-gamma-stokes-pair-bridge.md`; this rank result does not
identify a single all-prime Sonin operator or establish its Calkin
bound.

## Exact four-channel identity

For `g≠0` and `p>1`, put `t_p=g log(p)/2` and

```text
u_p = sinh(t_p) cosh(t_p),
v_p = sinh(t_p)^2,
w_p = cosh(t_p)/sinh(t_p).
```

Then for `p,q>1`,

```text
c_pq(g) = -2 [u_p + u_q + v_p w_q + w_p v_q].       (1)
```

Indeed the regularized ratio in the corpus is
`R_pq=sinh(t_q)/sinh(t_p)`. Insert this and
`sinh(t_p+t_q)=sinh(t_p)cosh(t_q)+cosh(t_p)sinh(t_q)`
into `c_pq=-2 sinh(t_p+t_q)(R_pq+R_pq⁻¹)` and expand.
For any finite set of primes, the *symmetric* matrix `(c_pq)` has
column space in the span of `1,u,v,w`, hence rank at most four.
At `g=0`, every entry is zero. Identity (1) is checked in Lean in
`RouteRCrossPrimeStokesFourChannelObstruction.lean`.

## Theorem: unbounded rank after ordering

Fix any real `g≠0`. For every even integer `n≥2`, there are
`n` increasing primes `p₁<⋯<pₙ` such that the alternating matrix

```text
Aᵢⱼ =  c_(pᵢ,pⱼ)(g)  if i<j,
Aᵢⱼ = -c_(pⱼ,pᵢ)(g)  if i>j,
Aᵢᵢ = 0
```

has rank `n`. In particular, the direct all-pair curvature assignment
cannot be the matrix of a fixed finite-dimensional alternating form
evaluated on one-prime sections at that grade.

### Proof

Take `n` consecutive primes starting at `P`, and let `P→∞` through
primes. The prime number theorem implies each `pᵢ/P→1` for fixed
`n`: for every `ε>0`, the interval `[P,(1+ε)P]` contains at least
`n` primes when `P` is large. Write `t=g log(P)/2` and
`δᵢ=g log(pᵢ/P)/2`. Then `δᵢ→0` and `t→+∞` or `-∞` according to
the sign of `g`. The hyperbolic addition formula gives

```text
sinh(t+δᵢ)/sinh(t) → 1,
sinh(2t+δᵢ+δⱼ)/sinh(2t) → 1.
```

Consequently `R_(pᵢ,pⱼ)(g)→1` and

```text
c_(pᵢ,pⱼ)(g) / [-4 sinh(g log P)] → 1        (i<j).   (2)
```

The normalized ordered matrix therefore tends entrywise to `Sₙ`,
with `+1` above and `-1` below its diagonal. For even `n`, `Sₙ` is
invertible: if `Sₙx=0`, subtracting adjacent row equations gives
`xᵢ₊₁=-xᵢ`; the first row then gives `-x₁=0` because the alternating
sum of `n` entries is zero. Thus `x=0`. By continuity of the
determinant, the normalized ordered matrix is invertible for all
sufficiently large `P`. Multiplication by the nonzero normalizer
preserves rank.

An alternating form on a fixed `k`-dimensional one-prime channel
space produces a pair matrix of rank at most `k`; choose even `n>k`.

## Route consequence and exact open obligation

The four-channel symmetric identity is real structure, but it cannot
be inserted into a fixed finite exterior seam by assigning its
ordered entries directly. The order sign itself carries unbounded
rank. A viable all-prime source architecture must either provide this
chronological/order degree of freedom, prove a nontrivial pair
correction that changes the ordered kernel, or derive a different
source-to-Calkin observable. The next decisive source question is
whether the Gamma-six all-prime orientation Gram produces the
ordered kernel above, and if so whether its Calkin norm has the
sub-root bound needed at actual Xi zeros. Neither statement is
established here.

Unbounded finite-packet rank is not, by itself, an essential-spectrum
mechanism. The source-weighted ordered curvature is Hilbert--Schmidt
and compact throughout its sharp admitted prime-`ℓ²` chamber
`u>2|g|`; outside that chamber its columns fail to lie in `ℓ²`.
The proof and exact scope are in
`stc-gamma-prime-hilbert-chamber.md`. Thus a direct ordered matrix on
this carrier cannot supply the nonzero Calkin seam, even though its
finite ranks grow without bound. The source-to-Sonin question remains
open for a different boundary construction.

## Audit

- Lean checks exact identity (1) and the three-prime coboundary
  obstruction in `RouteRCrossPrimeStokesFourChannelObstruction.lean`.
- The fixed-grade rank theorem uses the prime number theorem and
  elementary continuity; the corpus already proves the needed
  relative-gap consequence as `prime_between` in
  `GaloisForLFunctions/PNTPlus/Consequences.lean`. Its Lean
  formalization is pending.
- Deep corpus search found the pair scalar and fixed-pair source
  calibration, but no existing theorem for this ordered-rank claim.
  A separate deep search for an all-prime Gamma orientation packet
  completed without finding a source-to-ordered-kernel identity.
  The rank search had partial coverage; external priority is not
  claimed.
