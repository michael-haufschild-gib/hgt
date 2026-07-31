# Sonin aperture area rigidity and positive restriction-defect law

- **ID:** `sonin-aperture-area-rigidity-and-restriction-defect`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / SOURCE NO-GO WITH POSITIVE SURVIVOR
- **Scientific status:** `[PAPER-PROVED] [CORPUS-NEW WELD] [NOVELTY UNVERIFIED] [NOT RH]`
- **Parent:** `sonin-principal-relative-trace-splitting.md`
- **Statement:** Symmetric Sonin apertures carry the exact unitary invariant `8a^2`, so distinct
  apertures cannot be related by unitary transport of the projection correction.  Under the
  canonical nested restriction, every diagonal prime Gram corner instead obeys an exact positive
  defect factorization through the Sonin layer lost between the two apertures.  In every strict
  crossing regime that transition, and its positive Gram defect, are noncompact; the defect cannot
  lie in the Schatten-1 relative ideal.

## Frontier attacked

Finite-prime principal/relative splitting is now exact.  Its first remaining source gate was
"aperture compatibility."  Two natural meanings must be distinguished:

1. unitary covariance, which would identify finite parts by trace invariance;
2. canonical restriction along the nested Sonin carriers.

The first is impossible.  The second is not invariant: it has an exact positive defect.  Thus a
cofinal Suzuki/Burnol construction must carry this defect as an additional aperture cocycle; it
cannot declare aperture independence or use unitary trace invariance.

No numerical experiment is used.  The hostile test is exact operator algebra.

## Setup

For `a>0`, let

```text
K_a = {f even : f=0 on [-a,a] and Fourier(f)=0 on [-a,a]},
Q_a = orthogonal projection onto K_a,
C_a = Q_a-(1-A_a-R_a).
```

Here `A_a,R_a` are the physical and Fourier forbidden projections.  For a prime scale `p>1`, let
`D_p=U_p+U_p*`, and put

```text
B_a(p) = (1-Q_a) D_p Q_a,
G_a(p,q) = B_a(p)* B_a(q)
           = Q_a D_p (1-Q_a) D_q Q_a.                  (1)
```

## Theorem A: exact aperture-area rigidity

The corpus proves the exact Hilbert--Schmidt identity

```text
||C_a||_HS^2 = 8 a^2.                                  (2)
```

Hilbert--Schmidt norm is invariant under unitary conjugacy.  Hence, for `a,b>0` and every unitary
`U`,

```text
U C_a U* = C_b  ==>  8a^2=8b^2  ==>  a=b.              (3)
```

Conversely, at `a=b` the identity unitary works.  Therefore

```text
there exists U with U C_a U*=C_b  <->  a=b.             (4)
```

This is stronger than failure of the physical dilation gauge: no unitary whatsoever can transport
the exact correction between distinct positive apertures.

### Proof of Hilbert--Schmidt invariance

Write `U_*T=UTU*`.  Left composition by `U` preserves every output norm.  For right composition,
take adjoints:

```text
||TU*||_HS^2 = ||(TU*)*||_HS^2
             = ||UT*||_HS^2
             = ||T*||_HS^2
             = ||T||_HS^2.                              (5)
```

Combining the two equalities proves `||U_*T||_HS^2=||T||_HS^2`.  Applying this to `(2)` gives
`a^2=b^2`; positivity of `a,b` gives `a=b`.

## Theorem B: exact nested restriction law

If `0<a<=b`, then `K_b subset K_a`, hence

```text
Q_b Q_a = Q_a Q_b = Q_b.                               (6)
```

The inclusion is literal: vanishing on the larger physical interval implies vanishing on the
smaller interval, and the same statement applied after Fourier transform gives the Fourier half.

Compress `(1)` from aperture `a` to `K_b`.  Using `(6)` gives

```text
G_b(p,q)-Q_b G_a(p,q) Q_b
  = Q_b D_p (Q_a-Q_b) D_q Q_b.                          (7)
```

For the diagonal `q=p`, `D_p` and `Q_a-Q_b` are self-adjoint, while `(6)` gives
`(Q_a-Q_b)^2=Q_a-Q_b`.  Thus, with

```text
X_(a,b,p)=(Q_a-Q_b)D_pQ_b,
```

equation `(7)` becomes the exact factorization

```text
G_b(p,p)-Q_b G_a(p,p) Q_b = X_(a,b,p)* X_(a,b,p) >= 0. (8)
```

Equivalently, canonical aperture restriction is exact precisely when the lost-layer transition
`X_(a,b,p)` vanishes.  No asymptotic estimate or compact-error quotient enters.

## Theorem C: strict crossing is a new noncompact principal channel

Assume

```text
0<a<b<p a.                                               (9)
```

Choose `d` with `a<d<b`.  The inverse-dilated exterior shell sequence `f_n` is orthonormal and
weakly tends to zero.  The aperture-`b` boundary corner sends it asymptotically to normalized shell
vectors `v_n` supported between `a` and `d`.  Those vectors are asymptotically fixed by `Q_a`.
Using `(6)` gives the exact identity

```text
X_(a,b,p)=Q_a (1-Q_b)D_pQ_b,                             (10)
```

and therefore

```text
||X_(a,b,p)f_n-v_n|| -> 0,       ||v_n||=1.             (11)
```

Every compact `K` sends the weakly null orthonormal sequence `f_n` to zero in norm.  Hence

```text
1 <= ||X_(a,b,p)-K||                                    (12)
```

for every compact `K`.  In particular `X_(a,b,p)` is noncompact.  If `X*X` were compact, the
C*-identity in the Calkin algebra would force `X` compact.  Thus `(8)` is also noncompact.

Consequently the aperture restriction defect is not a residual trace-class correction.  It is a
new principal boundary channel forced by aperture growth.

## Theorem D: every strict aperture pair has a prime obstruction

Let `0<a<b`.  Choose a natural number `n>b/a`, then a prime `p>=n`.  Therefore

```text
1<p,             b<p a.                                  (13)
```

Theorem C applies at this genuine prime scale.  For every strict positive aperture pair there is
therefore a prime `p` such that

```text
G_b(p,p)-Q_bG_a(p,p)Q_b  is noncompact,                 (14)
```

and hence does not belong to the exact principal-relative ideal `I_b`.  Equivalently, no `K in
I_b` can satisfy

```text
G_b(p,p)=Q_bG_a(p,p)Q_b+K.                               (15)
```

This removes any aperture-schedule loophole: no strict enlargement preserves all prime diagonal
corners modulo the Schatten-1 relative ideal.

## Theorem E: principal-shell closure and aperture-anomaly cocycle

Write

```text
Delta_(a,b;r)=G_b(r,r)-Q_b G_a(r,r) Q_b.
```

For every nested triple `a<=b<=c`, restriction is not ordinarily additive but obeys the exact
compressed cocycle law

```text
Delta_(a,c;r)=Delta_(b,c;r)+Q_c Delta_(a,b;r) Q_c.       (16)
```

Now assume the common strict crossing chamber

```text
0<a<b<c<r a.                                             (17)
```

Let `S(u,v)` be the sum of the physical and Fourier shell projections from `u` to `v`, and let
`=r` denote equality modulo the concrete Sonin Schatten-1 ideal generated by exact projection
corrections and finite time--band blocks.  Then

```text
Delta_(a,b;r) =r S(r a,r b).                              (18)
```

The right side is not a new generator.  It is the operator of the canonical live Sonin window at
base `b`, with floor `r a`, ceiling `r b`, and scale one.  Canonical zero/live windows are closed
under multiplication modulo the same Schatten-1 ideal.  Therefore the already constructed
principal normal-state algebra is closed under every strict-crossing diagonal aperture defect.

Its cyclic logarithmic reader gives

```text
tau(S(r a,r b))
  =log(r b)-log(r a)
  =log b-log a.                                           (19)
```

Thus the principal anomaly is independent of the prime/dilation scale once crossing occurs.  It
is additive along aperture flags:

```text
Delta_(a,c;r) =r Delta_(a,b;r)+Delta_(b,c;r),             (20)
tau_(a,c)=tau_(a,b)+tau_(b,c).
```

Equations `(16)` and `(20)` isolate the complete remaining obstruction.  The curvature

```text
Kappa_(a,b,c;r)
  =Delta_(a,c;r)-Delta_(a,b;r)-Delta_(b,c;r)              (21)
```

lies in the concrete Schatten-1 ideal.  Hence the noncompact principal aperture anomaly is flat;
after its logarithmic shell character is removed, all failure of strict aperture additivity is an
ordinary trace-class scalar channel.  The next theorem is no longer construction of an enlarged
principal algebra.  It is computation of `Tr Kappa` and proof that the cutoff-dependent Burnol
conductor cancels precisely that scalar cocycle on the semilocal source graph.

## Theorem F: exact orbital-mass conservation

The principal cocycle is not an extra mass requiring archimedean cancellation.  At aperture `b`,
the total diagonal shell splits exactly as bounded operators:

```text
S(b,r b)=S(b,r a)+S(r a,r b).                            (22)
```

All three shells are canonical scale-one live normal windows.  Therefore the faithful cyclic
reader gives

```text
tau(S(b,r a))+tau(S(r a,r b))
  =[log(r a)-log b]+[log(r b)-log(r a)]
  =log r
  =tau(S(b,r b)).                                        (23)
```

Thus restriction transfers the exact aperture mass `log(b/a)` from the retained shell to the lost
shell while conserving the original prime orbital mass `log r`.  Burnol cancellation is needed,
if at all, only for the ordinary trace of `Kappa`, never for the noncompact principal logarithmic
channel.

## Consequence for the Suzuki lane

Equations `(4)` and `(8)` close a false branch and expose the replacement invariant:

```text
distinct apertures
  -> no unitary identification of exact Sonin corrections
  -> canonical restriction adds a positive lost-layer Gram defect
  -> in every strict crossing regime that defect is noncompact
  -> every strict aperture pair has a genuine prime in that regime.
```

Therefore the finite-prime signed anomaly cannot be promoted cofinally either by saying aperture
is a unitary gauge or by putting the entire restriction defect into the trace-class relative term.
However Theorem E closes the stronger principal-algebra question positively: the defect's
noncompact class is already a canonical scale-one principal shell, and the normal-state algebra
already carries its cyclic reader.  Cofinal compatibility is reduced to the trace-class curvature
`(21)`, its ordinary trace, and the matching Burnol counterterm.

This theorem proves noncompactness in the cofinal crossing chamber `(9)`; it does not classify the
noncrossing chamber, attach the Burnol term, or prove RH.  It removes both unitary covariance and
trace-class restriction compatibility unconditionally in the chamber relevant to aperture growth.

## Novelty audit

- Hilbert--Schmidt norm invariance under unitary conjugacy: standard operator theory.
- Exact energy `(2)`: existing project theorem.
- Source-specific synthesis `(4)`: corpus-new no-go; external novelty unverified.
- Exact Sonin restriction defect `(7)` and positive diagonal factorization `(8)`: corpus-new;
  external novelty unverified.
- Sharp compact-distance law `(12)` and noncompact positive defect: corpus-new. Targeted
  primary-source search found adjacent Sonin scaling and semilocal-carrier results but no matching
  nested-aperture factorization or compact-distance theorem; external novelty remains provisional.
- Universal prime obstruction `(13)`--`(15)`: corpus-new source-closure theorem; external novelty
  remains provisional.
- Principal-relative shell normal form `(18)`, exact compressed cocycle `(16)`, scale-free
  logarithmic character `(19)`, and trace-class curvature reduction `(21)`: corpus-new synthesis.
  Targeted primary-source search found the semilocal Sonin carrier, scaling intertwining, prolate
  operators, and conductor graph, but no matching aperture-anomaly theorem. External priority
  remains provisional pending specialist review.

## Gates

- [x] prior Sonin aperture and failed-route corpus searched
- [x] exact hostile test; no computation
- [x] unitary aperture covariance disproved
- [x] canonical restriction survivor derived
- [x] strict-crossing defect proved noncompact and separated from relative ideal
- [x] every strict aperture pair shown to fail relative compatibility at a genuine prime
- [x] falsify absorption of the lost-layer defect into the trace-class relative ideal
- [x] identify the defect modulo the exact relative ideal with a canonical live principal shell
- [x] prove canonical normal-state multiplication closes modulo the exact relative ideal
- [x] prove exact compressed cocycle, additive principal cocycle, and logarithmic aperture character
- [x] prove exact retained/lost operator and cyclic orbital-mass conservation
- [x] isolate all remaining aperture curvature in the trace-class relative ideal
- [ ] compute the ordinary trace of the aperture curvature
- [ ] prove exact cancellation by the cutoff-dependent Burnol conductor on the semilocal graph
- [ ] prove completed coercivity or terminally retire the source class

## Log

- 2026-07-22 — paper proof closed.  Aperture compatibility split into impossible unitary
  covariance and exact positive canonical restriction defect.
- 2026-07-22 — strict crossing upgraded the survivor: lost-layer transition has compact distance
  at least one, so its positive Gram defect is noncompact and cannot be absorbed into Schatten-1.
- 2026-07-22 — Archimedean natural selection plus Euclid upgraded the chamber result to a
  universal prime obstruction: every strict aperture enlargement exits the principal-relative
  source class.
- 2026-07-22 — stronger positive survivor proved: the noncompact defect is already a canonical
  scale-one live principal shell modulo the exact relative ideal. Aperture loss is an additive
  logarithmic principal cocycle; its entire curvature is trace class. The former enlarged-algebra
  gate is closed, leaving one explicit scalar Burnol-cancellation problem.
- 2026-07-22 — exact retained/lost conservation closes the principal anomaly completely:
  aperture restriction preserves `log r`; only `Tr Kappa` remains for the Burnol weld.
