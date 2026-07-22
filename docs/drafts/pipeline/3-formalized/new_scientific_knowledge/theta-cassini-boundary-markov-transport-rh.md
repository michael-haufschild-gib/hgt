# Theta--Cassini boundary Markov transport to RH

- **ID:** `theta-cassini-boundary-markov-transport-rh`
- **Stage:** 3-formalized
- **Type:** `[CANDIDATE NEW SOURCE-SPECIFIC BRIDGE] [CONDITIONAL RH CAPSTONE]`
- **Depends on:** `XiSquaredSeamCassiniResolventSourceLaw.lean`,
  `CompletedSeamCompactMarkovGermCapstone.lean`
- **Statement:** A single finite positive compact Markov measure matching the genuine inward
  theta response only near the Euler-safe Cassini boundary `u=0` analytically transports to the
  centered completed-seam Markov germ at `u=1`, and therefore proves RH.

## Exact predecessor

Let `Psi=xiSquaredSeamCassiniSource` and

```text
H(u) = -2 logDeriv(Psi)(u).
```

The corpus proves on `0<u<1`

```text
H(u) = thetaCuspCassiniInwardCoordinateResponse(u),       (1)
```

and proves `Psi(u) != 0` on the entire closed segment `0<=u<=1`.  Suppose there are a finite
positive measure `mu` and `0<B<1/2`, carried by `[0,B]`, such that on a one-sided neighborhood of
`u=0`,

```text
thetaCuspCassiniInwardCoordinateResponse(u)
  = integral 1/(1-x*(u-1)) dmu(x).                        (2)
```

The shift by `u-1` is load-bearing: the same measure is already in the centered reciprocal-square
coordinate, but `(2)` is tested where the theta source is genuine and Euler-safe.

Then

```text
completedSeamMomentGerm(z)
  = integral 1/(1-x*z) dmu(x) near z=0,                  (3)
```

so the compact-Markov capstone proves RH.

## Paper proof

1. Compact support and `B<1/2` make the shifted Markov function
   `F(u)=compactMarkovTransform(mu,u-1)` analytic on the ball `|u-1|<1/(2B)`, which contains the
   whole segment `[0,1]`.
2. Premise `(2)` says `F` is an inward analytic extension of the genuine theta response.  Existing
   one-sided identity-principle theorem therefore identifies `F` with the canonical Cassini
   moment germ near `u=0`; the existing resolvent law identifies that germ with `H`.
3. `Psi` is nonzero on `[0,1]`: for `u<1`, write `t=sqrt(1-u)>0` and use
   `Psi(u)=XiC(-t I)` together with the proved zero-free negative-imaginary ray; at `u=1`, use
   `Psi(1)=XiC(0)!=0`.
4. The segment is compact and the intersection of `{Psi!=0}` with
   `{|u-1|<1/(2B)}` is open.  Hence some closed thickening of `[0,1]` stays inside that
   intersection.  Its open thickening is convex.  Both `H` and `F` are analytic there.
5. The analytic identity principle transports their equality from a neighborhood of `u=0` to a
   neighborhood of `u=1`.
6. Substitute `u=1+z`.  The exact centered source identity
   `completedSeamMomentGerm(z)=H(1+z)` gives `(3)`, and the existing compact-Markov theorem gives
   RH.

## New reduction

The global Frullani/source-comparison problem is not an independent right-side core for compact
carriers.  Once a source-built positive measure satisfies the exact kernel identity locally at the
Euler-safe boundary, analytic transport forces the critical-center identity.  Remaining live work
is therefore the local coupled theta--prime--Gamma measure construction and its positivity; a
second comparison at the center would be redundant.

This does not make the measure unconditional.  It moves the rightmost premise to the only region
where the genuine theta response and Euler source are already formalized without continuation.

## Hostile audit

- Equality of finitely many jets is insufficient; `(2)` is germ equality on the one-sided source
  interval.
- `B<1/2` is a clean sufficient aperture ensuring one common analytic disk contains the transport
  segment.  It is compatible with the corpus's unconditional reciprocal-square bound `2/41`.
- Positivity is not inferred by analytic continuation.  It is assumed once, at the source boundary,
  for one fixed measure and preserved because the measure itself never changes.
- No Xi zeros or divisor coordinates occur in the predecessor proposition.
- A separated polar measure cannot satisfy this premise: the formal polar-quarter barrier still
  requires pole--zeta cancellation before positivity.

## Novelty audit

Targeted searches through current Xi/Thorin, incomplete-Gamma, theta-kernel, and Markovian-cycle
work found Thorin/RH equivalences and theta source formulas, but not this Cassini zero-free-tube
transport from an Euler-boundary Markov germ to the centered RH capstone.  Priority remains
`[NOVELTY-UNVERIFIED]`; claim is corpus-level structural novelty, not a literature priority claim.

## Gates

- [x] 0 → 1: exact source boundary, centered consumer, and shared measure fixed
- [x] 1 → 2: dependency-closed paper proof above
- [x] 2 → 3: `ThetaCuspCassiniMarkovBoundaryTransport.lean` formalizes the zero-free segment,
  convex-tube transport, and RH connector
- [ ] 3 → 4: independent novelty review

## Log

- 2026-07-22 — derived Euler-boundary-to-center transport; global Core-C comparison isolated as
  redundant for compact source carriers.
- 2026-07-22 — Lean proof completed and imported by the `RHTower` umbrella.
