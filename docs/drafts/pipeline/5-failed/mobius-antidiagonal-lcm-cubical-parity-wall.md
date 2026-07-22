# LCM cubical filtration and cross-rank parity wall

- **ID:** `mobius-antidiagonal-lcm-cubical-parity-wall`
- **Stage:** 5-failed
- **Type:** FALSIFIED SOURCE MECHANISM; paper-proved structural classification
- **Source:** `OPEN-SOURCE-001` in `../1-in-progress/mobius-additive-frontier-research-ledger.md`
- **Statement:** Grouping the signed Mertens antidiagonal by squarefree least common multiple gives
  an exact cubical persistent-Euler law and a universal saturated bulk, but positive semiprime
  blocks already have cubic-over-logarithmic mass.  The required saving must occur across lcm
  parity ranks, where the first local differential is exactly the known one-prime tent law.

## Goal

Write

```text
w_N(t)=(N-t+1)_+,
U(N)=sum_(m,n>=1) mu(m)mu(n) w_N(m+n).
```

For squarefree `ell`, define its lcm block

```text
B_(ell,N)=sum_(lcm(m,n)=ell) mu(m)mu(n) w_N(m+n).       (1)
```

Every contributing `m,n` is squarefree, so `(1)` partitions `U(N)` exactly over squarefree
`ell`.

## Cubical persistent-Euler law `[PAPER-PROVED]`

Let `P(ell)` be the prime set of `ell`.  Regard a face of the cube on `P(ell)` as an assignment of
each prime to one of three states:

```text
L   (present only in m),
R   (present only in n),
*   (present in both).
```

Put

```text
m(F)=product_(p in states L or *) p,
n(F)=product_(p in states R or *) p.
```

This is a bijection between cube faces and ordered divisor pairs with lcm `ell`.  Its face
dimension is the number of common-prime states `*`.  If `k=omega(ell)`, then

```text
mu(ell)mu(m(F))mu(n(F))
 = (-1)^k (-1)^(k+dim F)
 = (-1)^(dim F).                                        (2)
```

For an integer `t`, let `K_(ell,t)` contain exactly the cube faces satisfying
`m(F)+n(F)<=t`.  Resolving one `*` state to `L` or `R` removes that prime from one coordinate and
strictly lowers the sum.  Hence `K_(ell,t)` is a cubical subcomplex.  Since

```text
w_N(c)=sum_(t=0)^N 1_(c<=t),
```

equation `(2)` gives the exact law

```text
mu(ell) B_(ell,N) = sum_(t=0)^N chi(K_(ell,t)).          (3)
```

Thus an lcm block is not a mysterious arithmetic packet: it is integrated Euler characteristic of
a canonical product-sum filtration of one Boolean cube.

## Universal saturation law `[PAPER-PROVED]`

If `N>=2 ell`, every divisor pair in `(1)` lies inside the ramp and

```text
w_N(m+n)=N+1-m-n.
```

Primewise summation over the three states gives

```text
sum_(lcm(m,n)=ell) mu(m)mu(n)=mu(ell),                  (4)
sum_(lcm(m,n)=ell) mu(m)mu(n)m=mu(ell),                 (5)
```

and the same formula with `n`.  For `(5)`, the local contribution of a prime `p` is

```text
(-p) + (-1) + p = -1
```

from the states `L,R,*`; multiplying over the prime set gives `mu(ell)`.  Therefore

```text
B_(ell,N)=mu(ell)(N-1)  whenever N>=2 ell.              (6)
```

The complete saturated bulk is consequently

```text
sum_(ell<=N/2) B_(ell,N)=(N-1)M(floor(N/2)),            (7)
```

whose absolute value is at most `N^2` unconditionally.  All RH-level difficulty is localized to
the supercritical lcm boundary `ell>N/2`.

## Semiprime positive-mass wall `[PAPER-PROVED]`

Take distinct primes

```text
N/5 <= p,q <= N/4.
```

For large `N`, `pq>N`, while `p+q<=N/2`.  Among the pairs with lcm `pq`, only `(p,q)` and `(q,p)`
can satisfy `m+n<=N`; every other pair contains `pq` as one coordinate.  Since `mu(p)mu(q)=1`,

```text
B_(pq,N)=2 w_N(p+q) >= N.                               (8)
```

The prime number theorem gives

```text
#{p prime : N/5<=p<=N/4} >> N/log N.
```

Summing `(8)` over unordered distinct prime pairs yields

```text
sum_(ell: omega(ell)=2) max(B_(ell,N),0)
  >> N^3/(log N)^2.                                    (9)
```

Thus no termwise lcm-block upper bound, positive-part estimate, cubical Betti majorant, or argument
that discards negative lcm ranks can prove `OPEN-SOURCE-001`.  One full power of cancellation must
occur between different values of `ell` and, specifically, between opposite values of
`(-1)^omega(ell)`.

## Collision with the existing prime-tent law

Pairing lcm layers `ell` and `p*ell` for a prime absent from `ell` amounts to resolving the four
possibilities for whether `p` occurs in `m` and `n`.  At the ordered-pair level this is exactly the
Euler-prime removal used by `MERTENS-PRIME-TENT-001`.  Prime `2` gives the unique first
coefficientwise-positive transfer.  Attempting a second adjacent-rank differential is exactly the
already-proved two-prime negative-lobe wall.

The lcm filtration therefore supplies a topological normal form for that theorem, not an independent
way around it.  Any surviving lcm argument would need a genuinely nonlocal cancellation across
many lcm ranks; asserting such cancellation is the source problem rather than a consequence of
`(3)`.

## Hostile audit

1. The bulk formula `(7)` is useful localization but does not control the boundary.
2. Cubical Euler characteristic is signed.  Replacing it by total Betti number loses the negative
   rank cancellation and is refuted quantitatively by `(9)`.
3. A source estimate on the sum of positive lcm blocks is strictly false at RH scale by `(9)`.
4. Pairing adjacent lcm ranks by one fixed prime is not new; it is the prime-removal tent.
5. Iterating fixed-prime pairing cannot be declared positive because the two-prime transfer has a
   proved negative coefficient.

## No-go closure

- **Exact killing theorem/mechanism:** positive semiprime lcm blocks have mass
  `Omega(N^3/log^2 N)`, so blockwise positivity overpays by a full power; adjacent-rank repair is
  exactly the exhausted prime-tent mechanism.
- **Strongest positive survivor:** exact persistent-Euler identity `(3)`, universal saturation
  `(6)`, and bulk/boundary decomposition `(7)`.
- **New insight:** the lcm bulk is harmless without RH.  The entire source resides in cross-rank
  cancellation on `ell>N/2`, and semiprimes quantify the cancellation debt that odd lcm ranks must
  pay.
- **Status:** paper proof dependency-closed; no novelty claim.  The parent lcm/gcd-sum and cubical
  Euler theories are classical, and the source-facing adjacent-rank mechanism collides with an
  existing formalized theorem.  Lean deferred under the admission rule because this is a normal
  form/no-go, not a new unconditional source estimate.

## Literature boundary

- General gcd/lcm summation is established parent theory; no claim is made that regrouping by lcm
  is new.
- Current direct Möbius additive-convolution work still treats the binary source through explicit
  formulas under RH-type hypotheses; it does not supply the cross-rank estimate required after
  `(9)`.
- Focused searches did not locate `(3)` or `(6)` verbatim.  Search absence is not a priority proof,
  and neither identity is promoted as new scientific knowledge.

## Log

- 2026-07-22 — cubical law and saturation proved; semiprime positive-mass wall proved; lcm
  positivity route retired after collision with the one-prime tent classification.
