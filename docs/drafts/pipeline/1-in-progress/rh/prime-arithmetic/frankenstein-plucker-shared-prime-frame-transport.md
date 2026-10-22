# Frankenstein Pluecker shared-prime frame transport

- **ID:** `FR-PSPFT-1`
- **Stage:** `1-in-progress`
- **Type:** source-derived non-equivariant transport bridge
- **Status:** `[BRIDGE] [PAPER-PROVED] [LEAN EXACT-BUILT] [UMBRELLA-WIRED] [NOT RH]`
- **Lean target:**
  `formal/GaloisForLFunctions/RHTower/FrankensteinPluckerSharedPrimeFrameTransport.lean`

## Heavy-conjecture loop

1. **Identity transport between neighboring packet fibres. — FAIL, LEAN-PROVED.**  Literal lower
   and upper left/right reporters differ with opposite nonzero coefficients on explicit pair
   labels.  The connection cannot be deleted.
2. **Choose any rank-one map sending right reporter to next left reporter. — REJECTED AS THEATRE.**
   Such map exists abstractly but is not source-forced and can manufacture desired cancellation.
3. **Normalize every physical reporter to universal incidence, apply shared-prime pair swap, then
   rescale. — SURVIVES.**  All normalizing factors are literal positive source coefficients, and
   swap is forced by overlap `(p_n,p_(n+1)) -> (p_(n+1),p_(n+2))`.

## Frozen construction

Let `c_(s,t,i)` be coefficient of coordinate `i` in selected-pair difference `s-t`.  For packet
`z=(e,n)`, define positive frame scale

```text
q_(z,s,t,i)
  = sqrt(D_z) sqrt(pi_z(s) pi_z(t) / 2) sqrt(node_z(i)).
```

Literal physical coordinate reporter factors exactly as

```text
rho_(z,s,t,i) = q_(z,s,t,i) c_(s,t,i).
```

Swap prime pairs by vertex permutation

```text
sigma4 = [2,3,0,1]
```

and induced unordered-pair permutation

```text
sigma6 = [5,1,3,2,4,0].
```

Both are involutions and pure incidence obeys

```text
c_(s,t,i) = c_(sigma6(s),sigma6(t),sigma4(i)).
```

Therefore for arbitrary packets `z,z'`, exact coefficient-faithful relation is

```text
q_(z',sigma6(s),sigma6(t),sigma4(i)) rho_(z,s,t,i)
  = q_(z,s,t,i) rho_(z',sigma6(s),sigma6(t),sigma4(i)).
```

Because both scales are positive, canonical transport multiplier is their ratio.  It maps every
literal reporter exactly, not merely up to norm or covariance.  Specializations `i=2 -> 0` and
`i=3 -> 1`, with `z=(e,n)` and `z'=(e,n+1)`, identify lower and upper realizations of same shared
prime/depth coordinate.

## Paper proof

First factorization follows by unfolding pair-dispersion feature and diagonal node congruence.
Every scale factor is positive: P-G84 denominator term, P-G91 probabilities, divisor `2`, and P-G92
nodes are all strictly positive.  Pair permutations follow by enumerating six unordered pairs of
four coordinates.  Membership in selected pair is invariant under simultaneous vertex/pair swap,
giving incidence identity.  Substitute two reporter factorizations and commute scalar factors to
obtain cross-multiplied transport.  Divide by nonzero old scale for ratio form.

## Honest boundary

This is source-derived non-identity transport missing from identity-fibre current.  It kills local
frame mismatch in transported coordinates while preserving literal coefficients.  It does not yet
prove global transported prefix convergence, connection cancellation at infinity, completed Xi
target identification, or RH.  Those remain hostile gates after formalization.

## Metric-compatible strengthening

Hostile audit rejected ordinary norm preservation: transport coefficient is positive but not
generally one.  Literal reporter scale instead defines canonical variable fibre norm

```text
||x||_(z,s,t,i) = ||x|| / q_(z,s,t,i).
```

Lean proves physical reporter has exactly universal-incidence norm in this metric and canonical
transport is an exact isometry between source and swapped target fibres.  Coefficient variation is
therefore stored in metric density, not erased.  Reverse transports multiply to one.  More
strongly, two consecutive swapped transports cancel intermediate frame exactly and leave only
direct endpoint scale ratio; there is no extra two-step holonomy.

## Hostile global audit

Local mismatch is closed, but original `frankensteinPluckerCofinalCurrent` sums fixed `(s,t)`
labels in ordinary scalar metric.  It is not definitionally same as parity-swapped, variable-metric
covariant sum.  Claiming energies equal would be false.  Next surviving gate is construction of
metric direct-limit carrier over adjacent-prime line, followed by proof that transported cumulative
current converges and lands in independently completed Xi source target.  Flatness and local
isometry are now proved inputs; global landing remains arithmetic producer, not formal transport.

## Verification

```text
lake env lean GaloisForLFunctions/RHTower/FrankensteinPluckerSharedPrimeFrameTransport.lean
lake build GaloisForLFunctions.RHTower.FrankensteinPluckerSharedPrimeFrameTransport
```

Both pass; exact leaf build completed at `[12750/12750]`.  Umbrella was wired but not built.
Capstones use only `propext`, `Classical.choice`, and `Quot.sound`.  Repository-wide lint is
currently red because concurrent untracked Sieve/Suzuki/HTGeometry modules are not yet umbrella
reachable; lint output contains no error naming either Frankenstein module, and targeted forbidden
declaration scan is clean.
