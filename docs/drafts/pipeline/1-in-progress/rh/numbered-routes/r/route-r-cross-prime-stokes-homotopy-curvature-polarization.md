# Route R cross-prime Stokes-homotopy curvature polarization

- **ID:** `route-r-cross-prime-stokes-homotopy-curvature-polarization`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Source:** Route R rational-adelic prime-orbit Stokes homotopies and the fixed degree-six
  Wold--Green modular boundary
- **Statement:** The reflection-odd mixed curvature of the forward `p` and reflected `q` Stokes
  homotopies is a source-defined positive polar coordinate whose normalized square is exactly the
  Route R modular anomaly at `n=pq`; for `(p,q)=(2,3)` it is the fixed `B_6` anomaly.

## Goal

Construct the enlarged nonfunctorial positive-polar handoff left open by C33 of
`route-r-prepolar-horizontal-carrier-annihilation.md`.  Construction must use numerical ordered
prime data before Xi specialization, evade the hyperbolic central-gauge blindness of the intrinsic
pre-polar package, and identify its positive square with the already fixed physical modular
anomaly.  It must not claim the missing annihilation.

## Gates

- [x] 0 -> 1 in-progress: source-pure scalar model, hostile false-flatness test, and exact polar
  identity
- [x] complete division-free paper calculation on the modular coefficient line
- [x] land both oriented scalar curvatures on the fixed two-prime Sonin-compressed Euler
  commutator and prove the quantitative Calkin lower bound
- [x] lift the scalar calculation coefficient-faithfully to the actual finite rational-adelic
  cross-prime source before quotienting
- [x] prove that this lift cannot descend through singular corona, a bounded Hausdorff completion,
  or an operator-norm summable all-prime correction
- [ ] prove or dependency-close an independent source law annihilating the reflected curvature on
  the actual Xi landing
- [ ] 1 -> 2 fully-proven: operator lift and source-purity audit closed
- [ ] 2 -> 3 formalized after the shared Lean refactor
- [ ] 3 -> 4 publication-ready: novelty and exposition audit

## Source construction

Fix distinct ordinary primes `p,q` and a free real modular grade `a`.  On a normalized
one-dimensional coefficient line, let the forward `p` dilation and reflected `q` dilation act by

```text
u_p(a) = p^(-a),                  u_q^vee(a) = q^a.
```

Away from `a=0`, directional Stokes homotopies normalized by

```text
R_p (u_p(a)-1) = 1,              R_q^vee (u_q^vee(a)-1) = 1
```

are forced.  Their mixed curvature on that line is

```text
Omega_pq(a)
  = R_p (u_q^vee(a)-1) - R_q^vee (u_p(a)-1)
  = (q^a-1)/(p^(-a)-1) - (p^(-a)-1)/(q^a-1).
```

This is a numerical two-direction object, not a predicate on the intrinsic differential/cup/
Kummer package.  At nonzero grade both directional differences are invertible on the coefficient
line, so a Stokes shear annihilating the relevant difference vanishes there.  Thus the scalar
curvature is independent of the observer freedom which survives on the singular central fibre.

Define its reflection-odd part

```text
Delta_pq(a) = Omega_pq(a) - Omega_pq(-a).
```

Let `shc(x)=sinh(x)/x` for `x!=0` and `shc(0)=1`, and put

```text
A = a*log(p)/2,
B = a*log(q)/2,
g_pq(a)
  = (log(q)/log(p)) * shc(B)/shc(A)
      + (log(p)/log(q)) * shc(A)/shc(B).
```

Every factor in the two summands is strictly positive, so `g_pq(a)>0` for every real `a`.

## Conjecture / proof-or-failure loop

### C1 -- commuting prime dilations make the directional Stokes homotopies flat

`[FALSIFIED]`.  Commutativity gives `(u_p-1)(u_q^vee-1)=(u_q^vee-1)(u_p-1)`; it does not identify
the two directional inverses.  On the normalized coefficient line the curvature above is forced
and generically nonzero.  Calling it zero would insert the desired selector.

### C2 -- Haar-shift invariance makes the curvature a complete global observer

`[FALSIFIED AS STATED]`.  Adding one all-prime invariant Haar functional does not change the mixed
curvature, but the formal single-prime observer torsor is larger: independent coinvariant shears
change it by a Koszul coboundary.  A global operator lift must therefore retain the full two-prime
Koszul class, not merely compare chosen scalar primitives.

### C3 -- forward/reflected curvature supplies the missing positive polar datum

`[PROVED HERE, SCALAR SOURCE LINE]`.  This survives both hostile tests.  It uses ordered numerical
prime directions, is singular at the central fibre before taking its reflection-odd finite part,
and is not invariant under the hyperbolic automorphism class excluded by C33.

## Exact theorem

For every real `a`, with the value at `a=0` defined by continuous extension,

```text
Delta_pq(a) = -2*sinh(a*log(p*q)/2) * g_pq(a).             (1)
```

Consequently

```text
Delta_pq(a)^2
  = (p*q)^2 * g_pq(a)^2
      * [4*(p*q)^(-2)*sinh(a*log(p*q)/2)^2].               (2)
```

The bracket is exactly the reflected Wold--Green modular anomaly

```text
-Phi_a(B_(p*q))*Phi_(-a)(B_(p*q)).                         (3)
```

Therefore the positive source polarization

```text
Q_pq(a,c) = |c|^2 * Delta_pq(a)^2 / ((p*q)^2*g_pq(a)^2)
```

is unconditional, coefficient-faithful away from its radical, and satisfies

```text
Q_pq(a,c)
  = |c|^2 * [-Phi_a(B_(p*q))*Phi_(-a)(B_(p*q))] >= 0,
Q_pq(a,c)=0  <->  a=0 or c=0.                             (4)
```

For `p=2`, `q=3`, equation `(4)` is the fixed degree-six physical polar square.

### Proof

For `a!=0`, write `L=log(p)`, `M=log(q)`, `d=a(L+M)/2`, and

```text
r = sinh(a*M/2)/sinh(a*L/2) > 0.
```

Using `exp(2x)-1=2 exp(x)sinh(x)` gives

```text
(q^a-1)/(p^(-a)-1) = -exp(d)*r,
(p^(-a)-1)/(q^a-1) = -exp(-d)/r.
```

Hence

```text
Omega_pq(a)  = -exp(d)*r + exp(-d)/r,
Omega_pq(-a) = -exp(-d)*r + exp(d)/r.
```

Subtracting yields

```text
Delta_pq(a) = -(exp(d)-exp(-d))*(r+1/r)
             = -2*sinh(d)*(r+1/r).
```

The identities

```text
r   = (M/L)*shc(a*M/2)/shc(a*L/2),
1/r = (L/M)*shc(a*L/2)/shc(a*M/2)
```

identify `r+1/r` with `g_pq(a)` and extend the formula through `a=0`.  Positivity of `shc`,
`L`, and `M` proves `g_pq(a)>0`.  Squaring `(1)` gives `(2)`; the existing Route R modular normal
form gives `(3)`, and `(4)` follows.  No Xi zero or critical-line premise appears.

## Frontier effect

This closes two previously separate pieces of the enlarged Route R handoff at scalar source level:

1. **construction:** ordered forward/reflected Stokes homotopies create a nonfunctorial positive
   polarization from numerical prime data;
2. **identification:** its division-free square is exactly the fixed physical modular anomaly, not
   another detector with the same zero set.

It does **not** prove RH.  Mixed Stokes curvature is nonzero off center, so ordinary flatness cannot
annihilate it.  Remaining theorem is precise: lift `(1)` to the actual two-prime rational-adelic
Koszul/Stokes class, then prove an independent global source boundary/index law kills its
reflection-odd class on the actual Xi landing.  Any proof that assumes that flatness, reflected
equality, physical cyclic descent, or critical-line placement is circular.

The first half is now closed only in the correct pre-quotient sense.  Actual finite arithmetic
cross-prime coefficients land faithfully in the fixed Calkin receiver, but this map provably does
not factor through singular corona or any continuous completion killing the old source boundary.
An operator-norm summable all-prime tail cannot cancel it either.  Therefore “source exactness
kills the lifted curvature” is false.  Remaining law must be a new cutoff-dependent/unbounded
multi-place Poisson self-product comparison, not another Koszul descent.

The fixed compression receiver is now explicit.  The two oriented values
`(Omega_23(a),Omega_23(-a))` serve as coefficients of the literal two-prime Euler source.  Their
Sonin-compressed commutator is the negative orientation Gram, and its Calkin distance from every
compact operator is at least `|Delta_23(a)|/sqrt(6)`.  Hence its Calkin norm squared dominates
`6*g_23(a)^2` times the degree-six physical anomaly, and it is compact exactly at neutral grade.
This closes the scalar-to-fixed-compression landing, not the rational-adelic Koszul comparison or
the independent compactness theorem.  Full proof:
`route-r-cross-prime-stokes-calkin-compression-landing.md`.

## Novelty and collision audit

- Existing Route R two--three Gamma modules construct a reflection-odd Gamma exterior and classify
  its zero set.  They do not form the mixed curvature of the two prime-orbit Stokes homotopies or
  identify its normalized square with the degree-six modular anomaly.
- C33 excludes polarizations natural under every hyperbolic central gauge.  This construction
  deliberately uses the ordered numerical directions `(p,q^vee)` and their directional inverses,
  so it lies in the allowed nonfunctorial survivor class.
- The scalar algebra is elementary and is not claimed as external novelty.  Candidate project-new
  content is its exact realization on the literal rational-adelic Stokes/Koszul operators and its
  Route R modular-square identification.

## Log

- 2026-08-11 -- C1 flatness and C2 naive gauge-invariance claims falsified; C3 exact scalar polar
  identity proved.  Lean corpus remained read-only during refactor.
- 2026-08-11 -- fixed Sonin compression landing proved: the two-prime compressed commutator has
  Calkin distance at least `|Delta_23(a)|/sqrt(6)` and is compact exactly at neutral grade.  The
  remaining source theorem is compactness, not operator selection.
- 2026-08-11 -- actual arithmetic pre-quotient lift proved and its descent classified: singular
  corona kills the required finite atom, bounded descent is zero by density, and norm-summable
  all-prime cancellation is excluded by infinite Calkin injectivity.
