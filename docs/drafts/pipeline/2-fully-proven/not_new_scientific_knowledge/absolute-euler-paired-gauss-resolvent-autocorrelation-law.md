# Absolute-Euler paired Xi energy is a Gauss-resolvent budget against prime autocorrelations

- **ID:** `absolute-euler-paired-gauss-resolvent-autocorrelation-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[VALUE RELATION]`, `[TOP-DOWN SOURCE DECOMPOSITION]`
- **Scientific status:** `[PROVED HERE] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parents:** `xi-orientation-euler-safe-paired-cauchy-completeness.md`,
  `critical-logderivative-euler-safe-depoissonized-weil-stationarity.md`, and
  `../../3-formalized/not_new_scientific_knowledge/infinite-signed-digamma-herglotz-pointing.md`

## Goal

Expand the remaining absolute-Euler paired-Cauchy source inequality into elementary half-line
objects without passing through Xi zeros or a limiting divisor measure.  The result separates the
archimedean Gauss resolvents from the prime-log translations and shows exactly why Herglotz
pointing of the digamma residues does not, by itself, prove the paired Weil sign.

## The universal paired transform

For a holomorphic value function `g` on a right half-plane, put

```text
P[g](w,u)
 =2 Re(
    (g(w)+conj(g(u)))/(w+conj(u))
    -(g(w)+g(u))/(w+u)).                                  (1)
```

Fix finitely many nodes `w_j` with `Re(w_j)>1/2` and real coefficients `r_j`.  Define

```text
E(x)=sum_j r_j exp(-w_j x),
y(x)=Im E(x),
A=integral_0^infinity y(x)^2 dx.                         (2)
```

For a real number `a` such that none of the denominators below vanishes, define

```text
Z_a=Im sum_j r_j/(w_j+a),
y_a(x)=Im sum_j r_j exp(-w_j x)/(w_j+a),
B_a=integral_0^infinity y_a(x)^2 dx.                     (3)
```

`[PROVED]` For every real constant `c`, real pole location `a`, positive lag `tau`, and positive
coefficient `d`, the finite quadratic forms of `(1)` satisfy

```text
sum_(j,k) r_j r_k P[c](w_j,w_k)
  =8 c A,                                                  (4)

sum_(j,k) r_j r_k P[w |-> c/(w+a)](w_j,w_k)
  =4 c Z_a^2+8 a c B_a,                                   (5)

sum_(j,k) r_j r_k P[-d exp(-tau .)](w_j,w_k)
  =-8 d integral_0^infinity y(x+tau)y(x) dx.              (6)
```

Equations `(4)`--`(6)` are exact, not estimates.

### Proof

The Laplace identity

```text
1/(w+conj(u))=integral_0^infinity exp(-w x)exp(-conj(u)x) dx
```

turns the two divided-difference blocks in `(1)` into respectively a Hermitian square and a
bilinear square.  Their difference is

```text
|F|^2-Re(F^2)=2(Im F)^2.                                  (7)
```

For the Cauchy atom, use

```text
(1/(w+a)+1/(v+a))/(w+v)
 =1/((w+a)(v+a))
  +2a/((w+a)(v+a)(w+v)).                                  (8)
```

Equation `(7)` applied to the rank-one term and to the Laplace term proves `(5)`.  Equation `(4)`
is the same calculation without the resolvent factors.  For `(6)`, translation by `tau` gives the
two correlations

```text
Re integral E(x+tau)conj(E(x)) dx,
Re integral E(x+tau)E(x) dx,
```

whose difference is `2 integral y(x+tau)y(x) dx`, with the sign and factor in `(6)`.

## Exact completed Xi source formula

Write

```text
X(w)=xi(1/2+w),
L(w)=X'(w)/X(w).                                          (9)
```

On `Re(w)>1/2`, ordinary absolute Euler convergence gives

```text
L(w)
 =1/(w+1/2)+1/(w-1/2)-1/2 log(pi)
  +1/2 psi(1/4+w/2)
  -sum_(m>=2) Lambda(m)m^(-1/2)exp(-w log(m)).            (10)
```

Gauss's reciprocal-difference expansion is

```text
1/2 psi(1/4+w/2)
 =-gamma/2
  +sum_(n>=0)[1/(2(n+1))-1/(w+2n+1/2)].                 (11)
```

Put `a_n=2n+1/2`.  Combining `(4)`--`(6)` with `(10)`--`(11)` yields the exact quadratic identity

```text
sum_(j,k) r_j r_k P[L](w_j,w_k)

 =4 Z_(1/2)^2+4 B_(1/2)
  +4 Z_(-1/2)^2-4 B_(-1/2)
  -4(log(pi)+gamma) A

  +sum_(n>=0)
     [4/(n+1) A-4 Z_(a_n)^2-8 a_n B_(a_n)]

  -8 sum_(m>=2) Lambda(m)m^(-1/2)
       integral_0^infinity y(x+log(m))y(x) dx.            (12)
```

The Gauss line in `(12)` is a compensated series: its constant and polar pieces must remain inside
the same bracket.  Local normal convergence of the Gauss series, already formalized in
`ExplicitDigammaOrientationLimit.lean`, justifies termwise application to each finite packet.
Absolute Euler convergence and the exponential decay of `E` justify the prime correlation sum.

Thus the remaining paired-Cauchy theorem is the concrete source inequality

```text
boundary resolvent budget
 + compensated Gauss-resolvent budget
 >= prime-log autocorrelation budget                         (13)
```

for every rational damped-sine packet `y`.  By the parent completeness theorem, `(13)` for that
countable family implies RH.

## Polar orientation versus contact normalization

Equations `(4)` and `(5)` expose a distinction hidden by ordinary Herglotz language.  For `a>=0`,
the upper-half-plane Herglotz Cauchy atom has negative residue,

```text
g(w)=-1/(w+a),
```

but its paired quadratic is nonpositive:

```text
Q_P[g]=-4 Z_a^2-8a B_a.                                  (14)
```

Reversing only that residue by adding `2/(w+a)` adds the positive square

```text
8 Z_a^2+16a B_a.                                         (15)
```

However, a real constant is invisible to the Herglotz imaginary part and changes the paired form
by the nonzero contact mass `(4)`.  This matters for the two signed digamma models already in the
formal corpus.  Let

```text
G_0(w)=sum_(n>=0)[1/(n+1)-1/(w+n+1/2)].                  (16)
```

For a finite set `J`, let `G_J^pole` reverse the residues by adding `2/(w+n+1/2)`, as in
`explicitDigammaFiniteOrientation`, and let `G_J^Gauss` reverse the entire regularized Gauss
summands, as in the finite-support specialization of `signedDigammaBooleanCompletion`.  Then

```text
G_J^pole-G_J^Gauss=2 sum_(n in J)1/(n+1),                (17)

Q_P[G_J^pole]-Q_P[G_J^Gauss]
 =16(sum_(n in J)1/(n+1)) A.                             (18)
```

Both sources have the same pole residues and the same imaginary part, but their paired energies
differ by a strictly positive zero-frequency mass on every nonzero sine packet.  Therefore the
new infinite signed-digamma Herglotz chamber theorem controls the polar orientation exactly, but it
cannot discharge the Xi paired-Cauchy sign until the canonical real contact normalization is
retained.

This is the positive content of the obstruction:

```text
digamma Herglotz pointing
 + canonical Gauss contact normalization
 + prime-log autocorrelation domination
 -> paired absolute-Euler passivity
 -> RH.                                                     (19)
```

The first two objects in `(19)` are now explicit.  The third arrow is the remaining arithmetic
source theorem.

## Corpus and literature boundary

- `HTGeometry/ExplicitDigammaOrientationLimit.lean` proves local normal convergence of every
  bounded signed Gauss completion and the exact infinite Herglotz chamber.
- `RHTower/XiWeilResolventSource.lean` supplies the absolute-Euler prime--Gamma Cauchy values.
- `xi-orientation-euler-safe-paired-cauchy-completeness.md` proves that the rational damped-sine
  packets in `(12)` are complete for RH.
- The Gauss/digamma representation is classical; the integral form is recorded in
  [DLMF 5.9.12](https://dlmf.nist.gov/5.9.E12).
- The completed terminal form is the Weil explicit-formula quadratic on this restricted test
  space.  The present result is an exact source-coordinate expansion, not a new proof of Weil's
  criterion.

The located semilocal literature constructs quasi-inner completed local products and Sonin
spaces, but does not prove the prime autocorrelation domination `(13)` or identify it with a
semilocal connection curvature.  In particular, individual finite primes remain non-quasi-inner;
see Connes--Consani, [*Quasi-inner functions and local factors*](https://arxiv.org/abs/2008.10974).

## Lean decision

No Lean file is added under the active no-computation boundary.  The reusable formal target is the
generic atom/constant/lag triple `(4)`--`(6)`, followed by the finite-packet Gauss partial-sum
identity.  Stage 3 promotion requires targeted verification and is intentionally not claimed.

## Gates

- [x] universal constant paired law proved
- [x] universal real Cauchy-atom paired law proved
- [x] universal exponential-lag autocorrelation law proved
- [x] completed Xi prime--Gamma packet formula derived
- [x] signed-digamma polar/contact normalization split derived
- [x] exact remaining prime autocorrelation domination isolated
- [ ] formalize the finite algebraic/Laplace identities
- [ ] prove `(13)` from an independent arithmetic source constraint
- [ ] deduce RH
