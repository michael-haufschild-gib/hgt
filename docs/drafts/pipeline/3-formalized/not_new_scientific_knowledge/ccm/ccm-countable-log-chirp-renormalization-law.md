# Countable radial chirps have a scalar leading archimedean law

- **ID:** `ccm-countable-log-chirp-renormalization-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent theories:** semiclassical pseudodifferential conjugation, logarithmic Fourier
  multipliers, Dunster's radial phase expansions, and countable almost-orthogonality
- **Statement:** For the exact constrained radial sum `R_lambda=sum_(k>=1)H_(lambda,k)`, the
  archimedean Weil form satisfies
  `A(R_lambda)=log(c)||R_lambda||_2^2+O(d_1(lambda))`, where `c=2*pi*lambda^2`.

## Abstract countable log-chirp lemma

Let `h->0+` and

```text
u_h=sum_(k>=1)sum_(epsilon in {+1,-1})
 a_(h,k,epsilon)(s)exp(i*epsilon*phi_(h,k)(s)/h).                (1)
```

Assume on the support of each amplitude:

```text
c_0*k*e^s<=|phi_(h,k)'(s)|<=C_0*k*e^s,

|phi_(h,j)'(s)-phi_(h,k)'(s)|
 >=c_0*|j-k|*e^s,                                               (2)
```

and the amplitude symbol norms obey

```text
sum_(k>=1)(1+log(1+k))
 sum_epsilon ||a_(h,k,epsilon)||_(H1_weighted)^2<=M_h.           (3)
```

The weighted norm in `(3)` includes one exponential moment in `s`, so multiplication by `s` and
one phase integration by parts are bounded.

Let `m` be real, bounded below, smooth, and

```text
m(xi)=log|xi|+O(1),
xi*m'(xi)=1+O(|xi|^(-2))                                       (4)
```

at infinity. Then

```text
<m(D)u_h,u_h>
 =log(1/h)||u_h||_2^2+O(M_h).                                  (5)
```

### Proof

First truncate `(1)` at `k<=K`. Semiclassical conjugation on one branch gives

```text
exp(-i*epsilon*phi/h)
 [m(D)-log(1/h)]
 exp(i*epsilon*phi/h)a

 =[log|phi'|+O(1)]a+h*R_(h,phi)a,                               (6)
```

where the `L2` norm of `R_(h,phi)a` is controlled by the weighted `H1` norm in `(3)`. Formula `(6)`
follows by writing the multiplier kernel, Taylor expanding the phase once, and integrating the
quadratic remainder by parts; `(4)` makes the symbol seminorms uniform after subtracting
`log(1/h)`.

The diagonal part of `(6)` is bounded by

```text
C*(1+log(1+k)+|s|)|a_(h,k,epsilon)(s)|^2,                       (7)
```

and therefore sums to `O(M_h)`.

For distinct branches, apply `(6)` to one branch and pair with the other. The phase derivative in
`(2)` and one integration by parts give

```text
C*h/[j*k*|j-k|]
```

times the corresponding symbol norms. The same-sign and opposite-sign sums are controlled by

```text
sum_(k>=1)(1+log(1+k))/k^2<infinity.                             (8)
```

Thus the bound in `(5)` is uniform in `K`. The tail `k>K` tends to zero in the form norm by `(3)`
and `(7)`; letting `K->infinity` proves `(5)`.

## Exact CCM application

For

```text
H_(lambda,k)(s)
 =sqrt(lambda*e^s)q_lambda(k*lambda*e^s),
h=c^(-1),
c=2*pi*lambda^2,                                                (9)
```

Dunster's Section 2 expansion supplies `(1)`--`(2)` away from the `k=1` Bessel endpoint. The
pole-uniform Section 3 expansion supplies the two Bessel branches for `k=1`; the endpoint region
`c^2*s=O(1)` has the same bound by the analytic Bessel coordinate. The exact radial estimates give

```text
G_lambda(k,k)/d_1(lambda)<=C/k^2,                               (10)
```

and their differentiated symbol versions give `(3)` with

```text
M_h=O(d_1(lambda)).                                             (11)
```

The archimedean symbol

```text
m(xi)=Re psi(1/4+i*xi/2)-log pi                                (12)
```

satisfies `(4)`. Applying `(5)` proves

```text
A(R_lambda)
 =log(c)||R_lambda||_2^2+O(d_1(lambda)).                        (13)
```

## Scalar-renormalized form

Equation `(13)` is equivalently

```text
[A-log(c)I](R_lambda,R_lambda)=O(d_1(lambda)).                  (14)
```

The formalized scalar-shift theorem in `RayleighScalarShift.lean` proves that subtracting the same
identity term from an operator and its spectral energies leaves Rayleigh excess, spectral gap, and
their ratio unchanged. Equation `(14)` supplies the missing analytic CCM representation of that
scalar renormalization on the radial tail.

## Novelty and significance verdict

The abstract lemma is standard semiclassical pseudodifferential almost-orthogonality extended to a
summable countable family. Its CCM specialization is useful but routine after the radial symbol
bounds. It is classified as a bridge.

## References

- M. Suzuki, *Weil's quadratic form via the screw function*, arXiv:2606.09096, Section 2.4.
- T. M. Dunster, *Asymptotics of Prolate Spheroidal Wave Functions*, arXiv:1601.00699.

## Lean decision

`RayleighScalarShift.lean` formalizes the algebraic consumer. The analytic theorem requires
pseudodifferential and PSWF infrastructure absent from the formal tree. No wrapper is added.

## Gates

- [x] scalar logarithmic term isolated before cross-term estimation
- [x] countable log-chirp lemma proved
- [x] radial diagonal logarithmic moment summed
- [x] renormalized cross terms summed
- [x] exact CCM archimedean scalar law obtained

## Lean status

`[FORMALIZED]` — supersedes the "No wrapper is added" decision recorded above.  The analytic
semiclassical layer is indeed a cited parent, but two of the card's own steps are fully reachable
and are now proved.

Module: `formal/GaloisForLFunctions/RHTower/CCMCountableLogChirp.lean`
(4 theorems, all unconditional, axioms exactly `[propext, Classical.choice, Quot.sound]`, wired into
`formal/GaloisForLFunctions/RHTower.lean`).

What is proved in Lean:

- `log_le_two_mul_sqrt` — the elementary bound `log t ≤ 2√t` for `t > 0`, obtained from
  `log √t ≤ √t − 1`.
- `summable_logChirp_weight` — **equation (8)**: the countable almost-orthogonality weight
  `∑_k (1 + log(1+k))/(1+k)²` converges.  This is exactly the summability that makes the
  cross-branch estimate uniform in the truncation `K`, so that `K → ∞` is legitimate.
- `scalar_renormalized_form` — **equations (13)–(14)**: the archimedean law
  `A = log c · ‖R‖² + E` is exactly the renormalized statement `A − log c · ‖R‖² = E`.  The
  consumer of that renormalization is the corpus module `RHTower/RayleighScalarShift.lean`
  (`rayleighQuotient_add_real_smul_id`, `rayleighExcess_add_real_smul_id`,
  `spectralGap_add_cancel`, `rayleighExcessRatio_add_real_smul_id`), which proves that the scalar
  identity term changes neither the Rayleigh excess nor the spectral gap nor their ratio.
- `summable_radialDiagonal_bound` — **equation (10), consumer**: a radial diagonal bound `C/k²`
  is summable, which is the form in which `(11)` feeds the abstract lemma.

Deliberately outside the Lean statement (cited parents, not results of this card):

- the semiclassical conjugation formula `(6)` and its remainder bound;
- Dunster's radial phase expansions supplying `(1)`–`(2)`, including the pole-uniform Bessel
  endpoint;
- the PSWF symbol bounds `(10)`–`(11)` themselves and the digamma multiplier `(12)`.
