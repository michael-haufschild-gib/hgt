# Prime-height commutator has a noncompact Calkin ghost

- **ID:** `stc-prime-height-commutator-calkin-ghost`
- **Stage:** 3-formalized
- **Type:** operator obstruction with source-specific survivor
- **Routes:** STC, RHist, Gamma/Sonin
- **Status:** `[PROVED ON PAPER] [FORMALIZED IN LEAN] [NOT AN RH PROOF]`

## The source is a Sylvester equation

Fix valuation depth `e`, put `n=e+1`, and let
`B_p=xiGammaEulerPrimitiveBoundaryAmplitude 0 (p,e)>0` and
`h_p=n log(p)/2`. At horizontal grade `g`, define one-prime channels

```text
u_p=B_p sinh(g log(p)/2),
v_p=B_p cosh(g log(p)/2)
```

and the symmetric pair kernel

```text
Q_pq(g)=u_p v_q+v_p u_q
       =B_p B_q sinh[g(log p+log q)/2].
```

The literal equal-depth, reflection-odd Gamma exterior from
`stc-all-prime-gamma-stokes-pair-bridge.md` satisfies the exact
entrywise equation

```text
S_pq,e(g)=-(h_p-h_q)Q_pq(g).                           (1)
```

For each finite prime packet, if `H=diag(h_p)`, then `S=-[H,Q]`.
The exact scalar identity and two-channel factorization of `Q` are
checked in `DeningerGammaAllPrimeStokesPairBridge.lean`. Thus the
source-to-target problem contains an inverse Sylvester problem:
recover `Q` from its prime-height commutator, then apply the analytic
Stokes gauge and source-amplitude normalization. Equation (1)
identifies the operation; it does not bound its inverse.

## Theorem: a noncompact operator with compact commutator

Let `ℋ=ℓ²({primes})` and let `H` be the selfadjoint multiplication
operator `H e_p=h_p e_p`, with its natural domain. There exists a
bounded selfadjoint `X` such that

```text
X is not compact,
X(D(H)) ⊆ D(H),
[H,X] on D(H) extends to a compact bounded operator.          (2)
```

### Proof

The formal corpus proves a relative prime-gap consequence of the
prime number theorem as `prime_between` in
`GaloisForLFunctions/PNTPlus/Consequences.lean`. Choose disjoint
ordered prime pairs `p_k<q_k`, tending to infinity, with
`δ_k=h_{q_k}-h_{p_k}→0`. For example, at stage `k` take a prime
`p_k` beyond all previous pairs and the threshold for the interval
`(p_k,(1+ε_k)p_k)`, where `ε_k↓0`, then select `q_k` in that interval.
Since `δ_k≤n log(1+ε_k)/2`, the gaps vanish.

Define `X` to swap `e_{p_k}` with `e_{q_k}` on each two-dimensional
pair block and to vanish on unused prime coordinates. Then `X` is
bounded, selfadjoint, and has norm one. It is not compact because
`X e_{p_k}=e_{q_k}` is an orthonormal sequence. On pair block `k`,
the commutator `[H,X]` has off-diagonal entries `-δ_k,δ_k` and norm
`δ_k`. The direct sum of these blocks is bounded and compact: its
finite-block truncations converge in operator norm, with tail norm
`sup_{k>N}δ_k→0`. Call this compact extension `K`. On finite-support
vectors, `HXx=XHx+Kx`. Approximate any `x∈D(H)` by finite-support
vectors in the graph norm of `H`; boundedness of `X,K` and closedness
of `H` then give `Xx∈D(H)` and the same identity there, proving (2).

Therefore the prime-height commutator is **not faithful modulo
compacts** on its natural bounded-operator domain: a nonzero Calkin
class `[X]` has compact commutator. No general Calkin lower bound
`‖[X]‖≤C‖[[H,X]]‖` can invert this derivation.

## What survives

The actual source kernel `Q` is highly structured on every finite
packet, with the two one-prime channels above. Its critical source
amplitudes are not even square-summable on the full prime-depth
carrier: `summable_sq_xiGammaEulerPrimitiveBoundaryAmplitude_iff`
in `EulerPrimitiveJointDepthHilbertSource.lean` places Hilbert
summability strictly at positive displacement. Thus no bounded
all-prime completion of `Q` on the naive `ℓ²` prime carrier is
asserted. The ghost operator does not show that this particular
arithmetic kernel lies in the commutator's kernel. It shows
that equation (1) alone cannot transfer a Calkin bound from the
literal exterior to `Q` or to the Sonin target. A successful STC or
RHist proof must add a source-derived rule excluding near-collision
swap modes, or a further noncompact chronological reporter that sees
them, and then establish the required sub-root bound on actual Xi
divisors. This is the precise place where a singular observation may
be necessary; declaring an inverse from (1) would assume the hard
step.

The sharper source-specific classification in
`stc-gamma-prime-hilbert-chamber.md` shows that this raw critical
two-channel kernel has no bounded operator realization at nonzero
grade, whereas every admitted displaced extension is finite-rank
compact. Even a scalar renormalization approaching the sharp Hilbert
wall has only the zero bounded strong limit. Thus the general
commutator ghost should not be mistaken for the raw source's own
Calkin class; any nonzero essential-spectrum construction must create
a genuinely new, source-faithful collective boundary operator.

## Audit

- Formal source identity and two-channel factorization:
  `DeningerGammaAllPrimeStokesPairBridge.lean`.
- Formal relative prime-gap ingredient: `prime_between` in
  `GaloisForLFunctions/PNTPlus/Consequences.lean`.
- The infinite Hilbert-space construction is dependency-closed on
  paper and Lean formalization is pending.
- Deep corpus searches found the source and gap ingredients but no
  exact theorem for (2). Search coverage was partial; no external
  novelty claim is made.

## Log

- 2026-09-27: Sylvester form on packets, the ghost operator (2) with domain invariance, compact commutator, selfadjointness, norm and essential norm, and the no-Calkin-inverse corollary formalized unconditionally (`STCPrimeHeightCalkinGhost.lean`); certificate `stc-prime-height-commutator-calkin-ghost-formalized.md`; moved to stage 3.
