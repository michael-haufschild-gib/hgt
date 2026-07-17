# Gamma conductor Schur residual has strictly positive coherence

- **ID:** `gamma-conductor-schur-residual-positive-coherence`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper and Lean 4) / FORBIDDEN-COMBINATION LAW
- **Scientific status:** `[LEAN-FORMALIZED] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
  `[NEEDS NOVELTY AUDIT] [NOT AN RH PROOF]`
- **Lean core:**
  `formal/GaloisForLFunctions/RHTower/GammaConductorSchurResidual.lean`
- **Parents:**
  `../../1-in-progress/ccm-gamma-conductor-schur-capacity-law.md`;
  `../../1-in-progress/rectangular-semilocal-finite-part-curvature-rh.md`
- **Statement:** The canonical Gamma covariance has an entrywise strictly positive Schur residual
  after its centered second-moment conductor is eliminated.  Thus it cannot use the cancellation
  available to an abstract positive covariance; its conductor-coupled scalar coherence grows at
  least polynomially on dyadic prime packets.  The viable cofinal realization must keep this
  covariance channel-resolved or cancel it in an indefinite principal-relative object before
  taking a norm or scalar trace.

## Exact theorem

Let

```text
phi(t)=(cosh t)^(-1/2),
A(t)=1-phi(t)^2,
C(t)=-(3/4)phi(t)tanh(t)^2,
B=3/2,
G(t,u)=phi(t-u)-phi(t)phi(u).                              (1)
```

These are respectively the Gamma characteristic, Fourier-mode variance, covariance with the
centered second spectral moment, conductor variance, and two-frequency covariance.  The Schur
residual after eliminating the scalar conductor is

```text
R_0(t,u)=G(t,u)-C(t)C(u)/B.                               (2)
```

For `t,u>0`, put `x=tanh(t)tanh(u)`.  Then `0<x<1` and

```text
R_0(t,u)
 =phi(t)phi(u)[(1-x)^(-1/2)-1-(3/8)x^2]                  (3)
 >0.                                                      (4)
```

More quantitatively,

```text
R_0(t,u)>=phi(t)phi(u) x/8.                               (5)
```

Thus the residual kernel is not only positive semidefinite as a Schur complement: every pair of
positive frequencies has strictly positive residual covariance.

## Proof

The hyperbolic subtraction identity gives

```text
cosh(t-u)=cosh(t)cosh(u)(1-tanh(t)tanh(u)),               (6)
```

and hence

```text
phi(t-u)=phi(t)phi(u)(1-x)^(-1/2).                        (7)
```

Since `C(t)C(u)/B=(3/8)phi(t)phi(u)x^2`, equations `(2)` and `(7)` prove `(3)`.

For `0<x<1`, convexity of `y |-> y^(-1/2)`, or Bernoulli's inequality followed by inversion,
gives

```text
(1-x)^(-1/2)>1+x/2.                                      (8)
```

Moreover `x/2-(3/8)x^2>=x/8`.  Substitution in `(3)` proves `(4)` and `(5)`.

## Dyadic prime-packet consequence

Normalize the prime covariance and conductor cross by

```text
K_(p,q)=G(log p,log q)/sqrt(A(log p)A(log q)),
v_p=C(log p)/sqrt(A(log p)).                              (9)
```

Let `F_X={p prime:X<=p<=2X}` with `X>=5`.  For `p,q in F_X`,

```text
|log p-log q|<=log 2,
phi(log p)phi(log q)<=2/X,
K_(p,q)>=2/5,                                             (10)
|v_p v_q|>=9/(1024X).                                     (11)
```

All `v_p` have the same sign.  Hence

```text
sum_(p!=q in F_X) K_(p,q)v_pv_q
 >=9 |F_X|(|F_X|-1)/(2560X).                              (12)
```

By the prime number theorem, `|F_X|` is asymptotic to `X/log X`, so the right side is

```text
>> X/(log X)^2.                                           (13)
```

It is not `X^o(1)`.  Therefore the raw canonical Gamma covariance, scalarized with a fixed
positive coefficient in the conductor-coupled direction, cannot itself be the all-epsilon
subpower rectangular defect.

This does **not** exclude the Gamma Gram as a positive finite-level carrier.  It excludes only the
step that sums all its coherent off-diagonal entries into the RH error with one sign.

## Positive survivor

The same covariance is harmless when kept channel-resolved.  If a common-source column

```text
C:H_source -> directSum_p H_p                               (14)
```

is Hilbert--Schmidt, then `C*C` is positive trace class and

```text
Tr(C*C)=sum_p ||C_p||_2^2.                                 (15)
```

The off-diagonal blocks `C_p C_q*` remain present in the operator-valued output Gram but are not
summed by the trace in `(15)`.  The existing `SoninCoupledPrimeResidual.lean` realizes exactly
this architecture for prime powers of exponent at least two.  Its cross-prime overlap energies
are summable and its mixed second invariant is nonnegative.

The exponent-one principal shell is not square-summable and is absent from that construction.
Consequently the live source theorem is now sharply localized:

```text
principal exponent-one Euler shell
 + Burnol/Gamma conductor
 -> indefinite principal-relative cancellation before scalarization
 -> channel-resolved trace-class residual
 -> all-epsilon subpower rectangular defect.              (16)
```

The new theorem proves why the middle subtraction in `(16)` is structurally necessary.  It does
not construct it.

## Programme-3 nonproduct content

For an abstract positive block

```text
[K v]
[v* B] >=0,                                                (17)
```

the Schur residual `K-vv*/B` may use negative off-diagonal entries and polygon cancellation while
remaining positive semidefinite.  The Gamma realization forbids that combination: source
specificity forces every positive-frequency residual entry to be positive.  Thus

```text
positive covariance marginal
 + Gamma characteristic marginal
 + centered-conductor marginal
```

does not realize the full abstract positive-completion moduli.  Equation `(3)` cuts out a strict
joint-realization locus.  This is a genuine forbidden-combination theorem of research programme 3,
not another list of marginal invariants.

## Lean theorem surface

The unconditional module proves:

- `gammaConductorSchurResidualBracket_pos`;
- `semilocalArchimedeanCharacteristic_sub_factorization`;
- `gammaConductorModeSchurResidual_eq`;
- `gammaConductorModeSchurResidual_pos`.

The proof uses the already formalized Gamma characteristic/covariance formulas, hyperbolic
factorization, and Bernoulli's inequality.  It has no `sorry`, `admit`, axiom, opacity, unsafe
declaration, numerical computation, Xi-zero data, or RH premise.

The dyadic counting consequence `(12)--(13)` is paper-proved.  It is not needed to certify the
new joint-realization law `(3)--(4)`, and no broad prime-asymptotic Lean layer is added solely for
that corollary.

## Novelty boundary

Schur complements and Gamma Fourier transforms are classical.  Targeted corpus and primary-source
searches did not locate the exact entrywise residual identity `(3)`, its strict positive-frequency
consequence, or the conductor-direction dyadic growth law `(12)`.  Independent literature and
expert audit are still required before claiming scientific novelty.
