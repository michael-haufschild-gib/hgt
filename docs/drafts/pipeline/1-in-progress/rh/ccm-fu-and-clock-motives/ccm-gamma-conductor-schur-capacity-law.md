# A scalar Gamma conductor cannot dominate the cofinal prime covariance

- **ID:** `ccm-gamma-conductor-schur-capacity-law`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper and Lean core complete)
- **Scientific status:** `[LEAN-FORMALIZED] [NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Source:** the archimedean cyclic characteristic in
  `SoninSemilocalTwoPlaceAssociation.lean`, the independently resolved prime channels, and the
  Schur-complement criterion for positive block forms
- **Statement:** For the actual Gamma cyclic measure, the normalized prime-mode covariance with
  the centered second-moment conductor has harmonic size at the prime logarithms. Consequently no
  fixed scalar Gamma conductor block can dominate all independently resolved prime channels,
  regardless of positive diagonal damping. A cofinal CCM construction must carry growing or
  infinite archimedean channel capacity, or retain a non-diagonal prime covariance before the
  positive square.  The sharp accumulated scalar cost is
  `(9/8) log log X + C_Gamma + o(1)` over primes `p<=X`.

## Setup

Put

```text
phi(t)=(cosh t)^(-1/2),
A(t)=1-phi(t)^2,
C(t)=-(3/4)phi(t)tanh(t)^2.                                (1)
```

Here `A(t)` is the variance of the Fourier mode `exp(i t S)` under the normalized Gamma cyclic
measure, and `C(t)` is its covariance with the centered second spectral moment. Both formulas are
source-defined; the second is already represented in Lean as
`semilocalArchimedeanSecondMomentCovarianceKernel`.

For positive diagonal damping `d(t)>0`, the independently resolved prime block and its conductor
cross have entries

```text
A_p=d(log p)^2 A(log p),
c_p=d(log p) C(log p).                                    (2)
```

A scalar conductor variance `B` gives the finite block

```text
M_F = [ diag(A_p)  c ]
      [ c*          B ].                                  (3)
```

The theorem is that `M_F>=0` forces a lower bound on `B` which diverges cofinally.

## Exact arithmetic cost

For a prime `p`, elementary hyperbolic identities give

```text
phi(log p)^2=2p/(p^2+1),
tanh(log p)=(p^2-1)/(p^2+1),                              (4)
```

and therefore

```text
R_p
 =|C(log p)|^2/A(log p)
 =(9/8) p(p-1)^2(p+1)^4/(p^2+1)^4.                       (5)
```

The damping in `(2)` cancels exactly:

```text
|c_p|^2/A_p=R_p.                                         (6)
```

For `p>=2`, the elementary bounds

```text
p-1>=p/2,
p+1>=p,
p^2+1<=2p^2                                              (7)
```

give

```text
R_p>=9/(512p).                                           (8)
```

Thus `sum_p R_p` diverges by Euler's divergence of the reciprocal-prime series.

## Sharp harmonic capacity law

The exact rational value `(5)` has the expansion

```text
R_p = 9/(8p) + 9/(4p^2) - 45/(8p^3) + O(p^(-4)).           (8a)
```

In particular,

```text
R_p - 9/(8p) = O(p^(-2)),
p R_p -> 9/8.                                               (8b)
```

The correction series is therefore absolutely convergent over the primes.  Let `B_1` be the
Meissel--Mertens prime constant and define the Gamma capacity constant

```text
C_Gamma = (9/8) B_1 + sum_p (R_p-9/(8p)).                  (8c)
```

Mertens's prime reciprocal theorem now gives the sharp cofinal value law

```text
sum_(p<=X) R_p = (9/8) log log X + C_Gamma + o(1).          (8d)
```

Thus `9/8` is the exact archimedean capacity density per unit prime harmonic mass.  The earlier
lower bound `(8)` proves divergence without prime asymptotics; `(8d)` identifies its true scale and
leading coefficient.

## Schur-complement consequence

Because every `A_p>0`, positivity of `(3)` is equivalent to

```text
B>=sum_(p in F)|c_p|^2/A_p=sum_(p in F)R_p.              (9)
```

Hence no fixed finite `B` makes `(3)` positive for all finite prime sets. More quantitatively, any
cofinal scalar-conductor realization must allocate

```text
B_F>=sum_(p in F)R_p>=9/512 sum_(p in F)1/p -> infinity. (10)
```

## Positive covariance-concentration law

The complementary case can also be stated positively and quantitatively. Normalize the prime
coordinates so that their covariance matrix `K_F` has diagonal one, and put

```text
u_p=C(log p)/sqrt(A(log p)),
S_F=sum_(p in F)u_p^2=sum_(p in F)R_p.                   (10a)
```

Suppose the full prime--conductor quadratic block

```text
sum_(p,q)K_F(p,q)x_p x_q
 +2y sum_p u_p x_p+B y^2                              (10b)
```

is nonnegative for all `x,y`, with fixed `B>0`. Testing `(10b)` on
`x=u`, `y=-S_F/B` gives

```text
sum_(p,q)K_F(p,q)u_pu_q>=S_F^2/B.                       (10c)
```

Since the diagonal contribution is exactly `S_F`, the coherent off-diagonal covariance is forced
to satisfy

```text
sum_(p!=q)K_F(p,q)u_pu_q>=S_F^2/B-S_F.                  (10d)
```

Thus a fixed-capacity successful construction does not merely need some unspecified non-diagonal
correction. It must carry a cofinally concentrating prime covariance whose energy in the
conductor-coupled direction grows at least quadratically in the accumulated harmonic Schur cost.
This is the surviving positive architecture exhibited abstractly by a genuine Gram family.

## Canonical Gamma Gram realization

The normalized archimedean cyclic measure supplies such a full finite block canonically. Let `S`
have characteristic function `phi`, and put

```text
X_p=exp(i log(p) S)-phi(log p),
Y=S^2-1/2.                                                (10e)
```

The Taylor coefficients of `phi` give

```text
E[S^2]=1/2,
E[S^4]=7/4,
||Y||_2^2=3/2.                                           (10f)
```

Consequently the Gram family `{X_p}_p union {Y}` has prime block

```text
G_(p,q)=phi(log q-log p)-phi(log p)phi(log q),            (10g)
```

diagonal `A(log p)`, cross vector `C(log p)`, and conductor capacity `B=3/2`. After normalizing
`K_(p,q)=G_(p,q)/sqrt(A_pA_q)`, equations `(10c)`--`(10d)` become

```text
sum_(p,q)K_(p,q)u_pu_q >= (2/3)S_F^2,
sum_(p!=q)K_(p,q)u_pu_q >= (2/3)S_F^2-S_F.               (10h)
```

Thus the full Gamma covariance is an explicit positive finite-level carrier with the required
cofinal concentration. The remaining CCM problem is not positivity of this Gram block. It is to
derive the same marked covariance from the Gauss-paired local-ratio/quantized-differential source
and perform an exact principal-relative subtraction of its cross-prime energy so that the trace is
the additive Euler explicit-formula source without destroying `(10h)` or divisor-sensitive Pick
inertia.

The source-side replacement is now explicit in
`../../../3-formalized/not_new_scientific_knowledge/ccm/ccm-local-ratio-second-order-covariance-charge.md`.
The full local-ratio product has a canonical
higher-than-linear kernel anomaly with quadratic diagonal vanishing and cofinally divergent central
curvature. A successful Gauss descent need not identify that kernel literally with the Gamma Gram
`(10g)`; it must construct a pointed positive/relative lift with the same conductor-capacity and
index-faithfulness properties.

This is a positive carrier law. A successful CCM block factorization must provide at least one of:

```text
cofinally growing/infinite Gamma conductor energy;
one or more archimedean channels per growing prime packet, as in Gauss factorization;
a non-diagonal prime covariance whose inverse changes the Schur cost;
or a principal-relative/semifinite trace in which `(3)` is not scalarized first. (11)
```

The theorem closes the tempting construction in which one fixed Gamma observable is coupled
independently to every prime channel. It would not exclude the Gauss-paired product, a full
operator-valued covariance, or the three-grade Sonin relative carrier.

## Formal theorem

The unconditional Lean module
`formal/GaloisForLFunctions/RHTower/GammaConductorSchurCapacity.lean` proves:

- the exact characteristic, variance, covariance-square, and Schur-cost formulas `(4)`--`(5)`;
- the rational profile of the Schur cost and the sharp limit `p R_p -> 9/8` along the primes;
- strict positivity of every prime variance;
- the lower bound `(8)` and nonsummability of `p |-> R_p`;
- the cofinal form `forall B, exists F, B < sum_(p in F) R_p`;
- exact damping cancellation `(6)`;
- the abstract finite scalar Schur-capacity theorem obtained by testing the quadratic form on
  `x_p=-c_p/A_p`, `y=1`;
- the specialization `(9)` for every finite family of primes and every positive diagonal damping.
- the coherent covariance lower bounds `(10c)`--`(10d)` for every positive full block with fixed
  scalar conductor capacity.

The strongest formal conclusion is
`gammaConductorOffDiagonalCovarianceEnergy_lower`, together with
`gammaConductorFiniteCapacity_of_quadratic_nonneg`. No RH statement, zeta-zero premise, numerical
input, hidden axiom, or matrix-positivity oracle occurs in their proofs.

## Literature and architecture audit

Connes--Consani prove that a product with `m` finite places becomes quasi-inner by splitting the
single archimedean ratio into `m` Gauss-paired quasi-inner factors. Their construction therefore
already grows the archimedean channel count with the finite prime set. The theorem above supplies a
quantitative necessity result for the independently resolved diagonal-covariance model: one fixed
scalar Gamma conductor has harmonic total Schur cost and cannot replace that growth.

The current spectral-triple construction uses finite self-adjoint operators and reports numerical
convergence of their spectra and regularized determinants; its authors state that rigorous
cofinal convergence to the zeta zeros or normalized determinants to `Xi` remains the proof-bearing
step. The present theorem does not settle that step. It says that any proof of it through an
independent-prime positive block must expose growing/infinite conductor capacity or a genuinely
operator-valued relative covariance.

A targeted search found the classical ingredients separately--Gamma Fourier covariance,
finite-dimensional Schur complements, Euler's reciprocal-prime divergence, and the Gauss-paired
quasi-inner factorization--but not this exact damping-invariant cofinal capacity statement, its
sharp density `9/8`, or the constant `(8c)`. That is not sufficient for a novelty declaration;
independent expert and citation audit remains required.

Primary route references:

- Connes--Consani, [*Quasi-inner functions and local factors*](https://arxiv.org/abs/2008.10974).
- Connes--Consani, [*Weil positivity and Trace formula, the archimedean
  place*](https://arxiv.org/abs/2006.13771).
- Connes--Consani, [*The Scaling Hamiltonian*](https://arxiv.org/abs/1910.14368).
- Connes--Consani--Moscovici, [*Zeta Spectral Triples*](https://arxiv.org/abs/2511.22755).

## Gates

- [x] verify the exact formulas `(4)`--`(5)` without asymptotic shortcuts
- [x] prove the uniform lower bound `(8)`
- [x] prove the scalar Schur-complement capacity law `(9)`
- [x] formalize the arithmetic cost and nonsummability in Lean
- [x] complete a targeted covariance-operator and semilocal literature audit
- [x] integrate the growing archimedean-capacity obligation into the CCM value architecture
- [ ] independent expert audit of scientific novelty
- [ ] construct the surviving growing-channel contraction
- [ ] transport its divisor-sensitive index to the restricted-Weil/screw operator
- [ ] RH
