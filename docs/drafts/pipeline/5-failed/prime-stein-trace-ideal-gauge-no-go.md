# Prime--Stein trace-ideal gauge no-go

- **ID:** `prime-stein-trace-ideal-gauge-no-go`
- **Stage:** 5-failed / retired as an independent RH route
- **Type:** NO-GO THEOREM with positive universal survivor
- **Source:** hostile audit of `prime-space-inertia-law`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Verdict:** Reciprocal-prime sampling, trace-class damping, rank-two Stein displacement,
  cyclicity, and the Fredholm determinant do not create a new RH mechanism.  After an invertible
  diagonal congruence on every finite packet, the construction is exactly the already-known
  critical logarithmic-derivative Cauchy kernel.

## Candidate that was attacked

Put

```text
X(z)=xi(1/2+z),
L(z)=X'(z)/X(z),
q_p=1/p,
y_p=(1+q_p)/(1-q_p),
g_(p,r)=(p-1)(r-1)/((p+1)(r+1)(pr-1)),
B_(p,r)=g_(p,r)(L(y_p)+L(y_r)).                         (1)
```

The proposed route was

```text
absolute Euler data -> rank-two Stein state B -> prove B>=0 -> RH.       (2)
```

The audit tested whether any arrow before `B>=0` adds arithmetic content unavailable in the
classical Euler-ray kernel

```text
J(x,y)=(L(x)+L(y))/(x+y).                               (3)
```

It does not.

## Theorem A: universal Cauchy--Stein gauge

Let `I` be any index set.  Choose arbitrary real disk nodes `q_i`, arbitrary nonzero boundary
amplitudes `a_i`, and arbitrary real responses `lambda_i`, with denominators below nonzero.  Define

```text
x_i=(1+q_i)/(1-q_i),
G_(i,j)=a_i*a_j/(1-q_i*q_j),
K_(i,j)=G_(i,j)(lambda_i+lambda_j),
c_i=sqrt(2)*a_i/(1-q_i).                                (4)
```

Then, identically,

```text
G_(i,j)-q_i*q_j*G_(i,j)=a_i*a_j,                        (5)

K_(i,j)-q_i*q_j*K_(i,j)
 =(lambda_i*a_i)*a_j+a_i*(lambda_j*a_j),                (6)

K_(i,j)=c_i*c_j*(lambda_i+lambda_j)/(x_i+x_j).          (7)
```

Thus rank-one carrier displacement, rank-two response displacement, and Cauchy congruence are
automatic for every Cayley-parametrized sample family.  No primality, Euler product, functional
equation, or zeta input occurs.

If the `q_i` are distinct and every `a_i` is nonzero, the translated boundary coordinates
`a_i q_i^n` form a weighted Vandermonde system on every finite packet.  Hence finite minimality is
also generic.  If the nodes have an interior accumulation point and the response comes from a
holomorphic logarithmic derivative, diagonal recovery plus the identity theorem gives
faithfulness modulo constants.  This too is a uniqueness-set fact, not arithmetic structure.

### Prime specialization

Take

```text
a_p=q_p(1-q_p)/(1+q_p).                                 (8)
```

Then `(4)` gives exactly the carrier `g_(p,r)` in `(1)`, and

```text
c_p=sqrt(2)q_p/(1+q_p)=sqrt(2)/(p+1).                   (9)
```

Therefore every finite Prime--Stein matrix is the positive diagonal congruence

```text
B_F=diag(c_p)_(p in F) * (J(y_p,y_r))_(p,r in F)
      * diag(c_p)_(p in F).                             (10)
```

Sylvester inertia makes `(10)` sign- and index-preserving.  The Möbius/Gamma amplitude disappears
from the positivity question.

## Theorem B: trace-class compactification is a free gauge

Let `K=(K_(m,n))` be any finite-valued Hermitian kernel on a countable set indexed by positive
integers.  Put

```text
M_n=max(1, |K_(i,j)| : 1<=i,j<=n),
d_n=2^(-n)/M_n.                                         (11)
```

For `i<=j`,

```text
|d_i K_(i,j) d_j| <= 2^(-i-j).                          (12)
```

Hence the matrix `T_(i,j)=d_i K_(i,j)d_j` is absolutely summable entrywise and therefore defines
a trace-class operator on `ell2`.  Every `d_n` is positive, so every finite principal matrix of
`T` is congruent to the corresponding principal matrix of `K` and has exactly the same inertia.
Consequently

```text
sup_F n_-(T_F)=sup_F n_-(K_F).                           (13)
```

Thus any countable Hermitian kernel can be made trace class without changing a single finite
sign certificate.  Trace-classness and the associated Fredholm determinant cannot by themselves
be evidence of a new RH mechanism.  The reciprocal-prime weights in `(9)` are a pleasant explicit
gauge, but their role is only compactification.

## Exact collision with existing corpus

The corpus already proves

```text
ind_-(J)=sum_(xi(rho)=0, Re rho>1/2)m(rho),              (14)
RH iff J>=0.                                             (15)
```

It also proves that restriction to any analytic uniqueness set preserves negative squares.  The
prime nodes are distinct and converge to the interior point `1`; hence

```text
ind_-(J restricted to {y_p})=ind_-(J).                  (16)
```

Equations `(10)`, `(14)`, and `(16)` give the Prime--Stein inertia theorem immediately.  This is
the same localization mechanism already classified as bridge-only in:

- `euler-pick-inertia-offline-zero-count.md`;
- `ccm-infinitesimal-real-euler-ray-logderivative-index-law.md`;
- `critical-logderivative-euler-safe-cauchy-loss-law.md`.

The aperture flow is the existing shifted Euler-ray Pick family with the same diagonal gauge.
The Fredholm positive-root count is the spectral theorem applied after the free trace-class
compactification in Theorem B.  Neither changes the open positivity content.

## Honest attempt to prove RH through the route

### Attack 1: solve the Stein equation

Because `sup_p |q_p|=1/2`, the Stein equation has the unique trace-class solution

```text
B=sum_(n>=0) Q^n(a v*+v a*)Q^n.                         (17)
```

This solves existence and uniqueness, but not positivity.  By `(10)`, positivity of the solution
is exactly positivity of `J` on a uniqueness set and therefore exactly RH.  Standard Stein
passivity cannot infer `B>=0` because the forcing `a v*+v a*` is not positive in general.  The
rank-two formula has moved no part of the RH sign.

### Attack 2: prove positivity Euler factor by Euler factor

For a finite prime `ell`, the local logarithmic derivative on the centered Euler ray is

```text
E_ell'(y)/E_ell(y)
 =-(log ell)*ell^(-1/2-y)/(1-ell^(-1/2-y))<0.            (18)
```

Hence each local Prime--Stein summand has negative diagonal.  The completed response is an
archimedean term plus these negative Euler terms.  Termwise positive summation is impossible;
the desired sign is a global archimedean--prime cancellation.  Proving that cancellation in all
matrix degrees is precisely `(15)`.

### Attack 3: use low displacement rank or cyclicity

Rank-two displacement does not bound ordinary rank or negative index.  The universal law `(6)`
produces the same displacement rank for arbitrary response data, including data with indefinite
Cauchy matrices.  Cyclicity only says the realization has no redundant state; it supplies no
positive-real inequality.

### Attack 4: finite determinants and spectral flow

The corpus proves unconditionally that every one-node and two-node matrix of `J` is positive,
even if RH is false, while a single hypothetical off-critical orbit is detected at three nodes.
Thus the first open sign is a genuinely three-node correlation.  Prime sampling, trace damping,
and Fredholm packaging preserve this frontier exactly; they do not move it backward.

## Failure statement

The proposed implication

```text
new arithmetic Prime--Stein structure -> tractable passivity theorem -> RH
```

fails at its first arrow.  After stripping invertible diagonal gauges, all claimed structure is
generic Cauchy/Schur realization theory.  The remaining inequality is not a new antecedent from
which RH follows; it is the existing critical logarithmic-derivative positive-real criterion.

This does **not** disprove RH or the Prime--Stein inequality.  It falsifies the claim that the
construction opens a distinct route to proving it.

## Positive survivor

The exact survivor is the **universal Cauchy--Stein response law** `(4)`--`(7)` together with the
trace-ideal gauge theorem `(11)`--`(13)`.  It is useful as a screening principle:

> A countable RH kernel does not acquire new arithmetic content merely because a diagonal gauge
> makes it trace class, cyclic, low-displacement-rank, or Fredholm-determinantal.  A genuine new
> route must prove a sign-changing statement before that gauge, or introduce a source constraint
> not erased by finite diagonal congruence.

The survivor is mathematically clean but conservatively classified as not new scientific
knowledge: it composes elementary diagonal damping, Sylvester inertia, Cayley algebra, classical
Schur realization, and analytic uniqueness.

## Internal verification status

The universal displacement, response additivity, diagonal faithfulness, Cayley congruence, finite
matrix congruence, and exact prime specialization are certified in the internal proof layer.  The
paper-facing verdict does not depend on mentioning that layer.

## Gates

- [x] derive universal arbitrary-node displacement law
- [x] prove exact arbitrary-node Cauchy congruence
- [x] prove prime carrier is a literal specialization
- [x] prove trace-class compactification can be imposed on every countable kernel
- [x] identify exact collision with existing Euler-ray index theorem
- [x] attack Stein passivity, Euler-local positivity, cyclicity, and Fredholm escape routes
- [x] extract positive universal screening theorem
- [x] retire Prime--Stein as independent RH route
- [ ] seek a source constraint surviving diagonal-congruence erasure

## Log

- 2026-07-22 -- Hostile audit found the Prime--Stein carrier to be an arbitrary-node Schur carrier.
- 2026-07-22 -- Universal Cauchy--Stein algebra and exact prime specialization certified.
- 2026-07-22 -- Trace-class/Fredholm layer proved to be a freely imposable diagonal gauge.
- 2026-07-22 -- Route retired: positivity remains exactly the pre-existing Euler-ray RH kernel.
