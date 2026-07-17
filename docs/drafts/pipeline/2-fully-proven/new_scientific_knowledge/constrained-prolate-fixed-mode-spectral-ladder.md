# The constrained prolate fixed-mode spectral ladder

- **ID:** `constrained-prolate-fixed-mode-spectral-ladder`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Scientific status:** `[PROVED HERE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`, provisional pending
  independent proof and literature review; `[NOT AN RH PROOF]`
- **Parent:** `constrained-prolate-two-mode-ground-state.md`
- **Statement:** Every fixed low eigenvalue of the positive-even prolate leakage operator compressed
  to the vanishing-integral hyperplane has an explicit asymptotic scale and an explicit limiting
  Hermite contrast eigenvector. Adjacent constrained eigenvalues separate by `lambda^8`, equivalently
  by the fourth power of the finite-prime cutoff `c=lambda^2`.

## Result in context

Connes--Consani--Moscovici use the unique vanishing-integral combination of the prolate modes
`h_(0,lambda)` and `h_(4,lambda)` as an educated approximation to the ground state of the truncated
Weil form. The parent card proves that this vector is asymptotically selected by the exact
vanishing-integral prolate concentration problem.

The same constrained problem contains a full fixed-depth ladder. Its eigenvectors are not arbitrary
higher-mode corrections. They converge to an explicit orthogonal family obtained by Gram--Schmidt
from the values at zero of `h_0,h_4,h_8,...`, and its eigenvalues inherit the rigid Fuchs scale
separation. This supplies a quantitative spectral fingerprint for the still-open transfer from the
prolate model to the true finite-prime Weil operator.

## Setup

Use the notation of the parent card. In the positive even compressed-Fourier sector, put

```text
e_j(lambda)=h_(4j,lambda),
B_lambda e_j=d_j(lambda)e_j,
d_j=1-chi_(4j)(lambda)^2,
ell_j(lambda)=integral_R e_j(lambda)(x) dx.
```

Then

```text
0<d_0<d_1<...<1,   d_j -> 1 as j -> infinity,
sum_(j>=0) ell_j(lambda)^2 <= 2*lambda.                 (1)
```

Let

```text
M_lambda={f : <f,ell(lambda)>=0}
```

and let `C_lambda` be the compression of `B_lambda` to `M_lambda`. Write its discrete eigenvalues
below `1` in increasing order as

```text
mu_0(lambda)<mu_1(lambda)<... .                         (2)
```

For fixed `j`, prolate-to-Hermite convergence gives

```text
ell_j(lambda) -> a_j=h_(4j)(0),                         (3)
```

in the Fourier normalization used by CCM. These numbers are nonzero and satisfy

```text
a_j^2=a_0^2 q_j,
a_0^2=sqrt(2),
q_j=binom(4j,2j)/16^j.                                 (4)
```

Put

```text
Q_k=sum_(j=0)^k q_j,
theta_k=Q_k/Q_(k+1).                                   (5)
```

Fuchs' fixed-index asymptotic gives, for every fixed `j`,

```text
d_j(lambda)
  ~ A_(4j) lambda^(8j+1) exp(-4*pi*lambda^2),
A_(4j)>0.                                               (6)
```

In particular, adjacent fixed scales obey

```text
d_j/d_(j+1)=O(lambda^(-8)).                             (7)
```

## Theorem

`[PROVED HERE]` Fix `k>=0`. For all sufficiently large `lambda`, there is exactly one constrained
eigenvalue `mu_k(lambda)` in `(d_k(lambda),d_(k+1)(lambda))`, and

```text
mu_k(lambda)/d_(k+1)(lambda) -> theta_k=Q_k/Q_(k+1).    (8)
```

Consequently,

```text
mu_(k+1)/mu_k
  ~ [Q_(k+1)^2/(Q_k Q_(k+2))] * [d_(k+2)/d_(k+1)]
  ~ C_k lambda^8                                       (9)
```

for an explicit constant `C_k>0`. With the finite-prime parameter `c=lambda^2`, every fixed
adjacent ratio is asymptotic to a positive constant times `c^4`.

Let `v_(k,lambda)` be a unit eigenvector for `mu_k`. After a choice of sign, its coefficient vector
in the prolate basis converges in `ell^2` to the normalization of

```text
w_k=(-a_0,-a_1,...,-a_k,S_k/a_(k+1),0,0,...),
S_k=sum_(j=0)^k a_j^2.                                 (10)
```

The limit vectors are mutually orthogonal and lie in the limiting vanishing-integral hyperplane:

```text
<w_k,a>=0,
<w_k,w_m>=0 for k!=m.                                  (11)
```

Thus the complete fixed-depth constrained spectrum selects a canonical orthogonal Hermite contrast
ladder, not only the first `h_0`--`h_4` contrast.

### Exact identification with the CCM Gram--Schmidt ladder

`[PROVED HERE; BRIDGE]` The limiting vectors in `(10)` are exactly the ordered Gram--Schmidt
orthogonalization of the raw Hermite contrasts used in the Connes--Consani construction.

Indeed, put

```text
r_m=a_0 e_m-a_m e_0,   m>=1.                            (10a)
```

These are the Hermite limits of CCM's even prolate combinations

```text
psi_(2m) psi_0(0)-psi_0 psi_(2m)(0).
```

For fixed `m`, the vectors `r_1,...,r_(m-1)` span the codimension-one subspace

```text
{x in span(e_0,...,e_(m-1)) : sum_(j=0)^(m-1) a_j x_j=0}.
```

The vector `w_(m-1)` from `(10)` is orthogonal to every `r_j`, `j<m`, lies in
`span(r_1,...,r_m)`, and has a nonzero `e_m` coordinate. It is therefore, up to normalization and
sign, the `m`-th Gram--Schmidt vector. Thus the spectral ladder does not merely resemble the
published numerical prolate orthogonalization: it selects its exact fixed-mode Hermite limit.

The first two constants are

```text
q_0=1,
q_1=3/8,
q_2=35/128,
Q_0=1,
Q_1=11/8,
Q_2=211/128.                                           (12)
```

Hence

```text
mu_0/d_1 -> 8/11,
mu_1/d_2 -> 176/211,
mu_1/mu_0 ~ (242/211)*(d_2/d_1).                       (13)
```

## Proof

### 1. Secular roots give the constrained eigenvalues

For `mu` outside the diagonal spectrum, a constrained eigenvector satisfies

```text
(B_lambda-mu)v in span{ell(lambda)}.
```

Its coordinates are therefore, up to one common scalar,

```text
v_j=ell_j/(d_j-mu),                                    (14)
```

and the constraint is the secular equation

```text
F_lambda(mu)=sum_(j>=0) ell_j^2/(d_j-mu)=0.            (15)
```

On `(d_k,d_(k+1))`, the series and its derivative converge locally uniformly. The tail denominators
are uniformly separated from zero and `(1)` supplies square summability. Moreover

```text
F_lambda'(mu)=sum_(j>=0) ell_j^2/(d_j-mu)^2>0.         (16)
```

For fixed `k`, equation `(3)` makes `ell_k` and `ell_(k+1)` nonzero for all sufficiently large
`lambda`. Thus `F_lambda` tends to `-infinity` at the left endpoint and to `+infinity` at the right
endpoint. It has exactly one root there. Codimension-one min--max interlacing identifies these roots,
in order, with the eigenvalues in `(2)`.

### 2. Rescale one spectral interval

Set

```text
H_(k,lambda)(x)
  =d_(k+1) F_lambda(x*d_(k+1)),   0<x<1.               (17)
```

For `x` in a fixed compact subinterval of `(0,1)`, split `(17)` after `j=k+1`. The finite part is

```text
sum_(j=0)^k ell_j^2/(d_j/d_(k+1)-x)
  +ell_(k+1)^2/(1-x).                                  (18)
```

By `(3)` and `(7)`, it converges locally uniformly to

```text
H_k(x)=-S_k/x+a_(k+1)^2/(1-x).                         (19)
```

For the infinite tail, monotonicity of `d_j`, `(1)`, and `(7)` give

```text
0 <= d_(k+1) sum_(j>=k+2) ell_j^2/(d_j-x*d_(k+1))
   <= 2*lambda*d_(k+1)/(d_(k+2)-x*d_(k+1))
   = O(lambda^(-7)) -> 0.                              (20)
```

Thus `H_(k,lambda)->H_k` locally uniformly. The limit is strictly increasing and has the unique zero

```text
x=S_k/(S_k+a_(k+1)^2)=Q_k/Q_(k+1)=theta_k.             (21)
```

The unique zeros of the strictly increasing approximants therefore converge to `theta_k`. This proves
`(8)`. Dividing two consecutive instances of `(8)` and using `(6)` proves `(9)`. Substitution of
`(12)` gives `(13)`.

### 3. The eigenvectors converge to the contrast ladder

At `mu=mu_k`, multiply the coordinate vector `(14)` by `d_(k+1)`. For every fixed head coordinate,
`(3)`, `(7)`, and `(8)` give

```text
d_(k+1) ell_j/(d_j-mu_k) -> -a_j/theta_k,     j<=k,
d_(k+1) ell_(k+1)/(d_(k+1)-mu_k)
  -> a_(k+1)/(1-theta_k).                               (22)
```

The squared tail norm is bounded by

```text
d_(k+1)^2 sum_(j>=k+2) ell_j^2/(d_j-mu_k)^2
  <= 2*lambda*d_(k+1)^2/(d_(k+2)-d_(k+1))^2
  = O(lambda^(-15)) -> 0.                              (23)
```

After multiplying the limit in `(22)` by `theta_k`, its first `k+1` entries are `-a_j`, while its
last entry is

```text
theta_k*a_(k+1)/(1-theta_k)=S_k/a_(k+1).                (24)
```

Normalization proves `(10)`. Finally,

```text
<w_k,a>=-S_k+(S_k/a_(k+1))*a_(k+1)=0.                  (25)
```

If `m<k`, then `w_m` is supported through coordinate `m+1`, where `w_k` still has coefficient
`-a_(m+1)`. Hence

```text
<w_m,w_k>
  =sum_(j=0)^m a_j^2-(S_m/a_(m+1))*a_(m+1)
  =0.                                                   (26)
```

This proves `(11)` and completes the theorem.

## Attack and route boundary

- `[SEARCH]` Projection of a concentration operator to the kernel of linear constraints is standard.
  Kennedy--Kabal's 1986 maximum-energy window theorem is a direct parent for that finite-dimensional
  formulation.
- `[SEARCH]` Secular equations, rank-one interlacing, and Fuchs' fixed-index prolate asymptotics are
  parent theory.
- `[PROVED HERE]` The full fixed-`k` combination of the infinite Bessel tail, the `lambda^8` scale
  separation, the exact constants `Q_k/Q_(k+1)`, and the limiting orthogonal Hermite contrast ladder.
- `[PROVED HERE]` The all-depth spectral fingerprint `(9)`, including the explicit first excited
  constants `(13)`.
- `[PROVED HERE; BRIDGE]` The eigenvector limits are exactly the ordered Gram--Schmidt limits of the
  raw even CCM prolate contrasts, so the new spectral ladder and the published numerical comparison
  use the same canonical vectors rather than two analogous bases.
- `[NOT PROVED]` The true finite-prime Weil eigenvalues or eigenvectors obey this ladder. The theorem
  supplies the prolate side of a comparison theorem; it does not supply the Weil-to-prolate transfer.
- `[NOT PROVED]` Simplicity or positivity of the true continuous Weil ground state for every cutoff.

The fake local spectral proof now fails at one exact sentence:

```text
the finite-prime Weil low-spectrum has the same fixed-depth projective asymptotics as C_lambda.
```

Neither small Rayleigh value nor ordinary form convergence proves this. The relevant gaps themselves
vanish like `exp(-4*pi*lambda^2)` times a polynomial, so the transfer must be relative to the full
minuscule ladder, not additive at a polynomial error scale.

Even proving that sentence would not cross the cofinal RH boundary. The formalized
`finite-prime-logarithmic-boundary-transfer` theorem additionally requires a source-defined
holomorphic determinant or characteristic family `F_N` which converges locally uniformly and
zero-preservingly to `Xi`, together with sub-log-square reflected energy on every approximant zero
fiber. The ladder is a local spectral fingerprint that such a construction must retain; it is not
itself a divisor-transfer theorem.

## Novelty and significance audit

### Parent-theory gate

Erasing the RH vocabulary leaves a linearly constrained diagonal compact-operator problem. Generic
projection and interlacing theory do not determine `(8)`--`(13)`: the result uses the simultaneous
fixed-index Fuchs hierarchy, the nonzero Hermite evaluation coordinates, and a uniform infinite-tail
estimate. The general constrained-window literature formulates the projected eigenproblem but does
not supply this fixed-aperture asymptotic ladder.

### Literature gate through July 2026

The preliminary audit covered:

1. CCM's *Zeta Spectral Triples* and their cited Fuchs/prolate sources;
2. Connes's February 2026 account of the higher near-radical Weil eigenvectors and its Gram--Schmidt
   construction;
3. Groskin's June 2026 revision, which reports finite-Weil spectral gaps but no prolate-basis theorem;
4. continuous and discrete constrained Slepian concentration, including prescribed spectral values
   and nulls;
5. fixed-index and nonasymptotic prolate eigenvalue literature; and
6. exact searches for the constants `176/211`, `242/211`, an all-fixed-mode vanishing-integral
   ladder, and `lambda^8` constrained spectral separation.

No equivalent statement or stronger result was located. The closest constraint parent projects the
operator to a nullspace. The closest RH parent reports numerical higher-vector agreement. Neither
derives the asymptotic eigenvalues, the Hermite contrast family, or the `c^4` adjacent-gap law.

### Significance gate

Passed provisionally at moderate strength. The theorem upgrades one canonical ground-state seed to
an entire fixed-depth spectral model and gives exact quantities against which the finite-Weil spectrum
can be compared. The `c^4` law is a falsifiable transfer fingerprint rather than a qualitative analogy.
It does not cross the final Weil-to-prolate bridge and is not an RH proof.

Scientific novelty remains provisional until independent experts have checked both the proof and the
literature classification.

## Lean decision

The **existence-and-uniqueness half of Theorem `(8)`** — "there is exactly one constrained eigenvalue
`mu_k` in `(d_k, d_(k+1))`" — is formalized axiom-clean, and for the *full infinite* prolate diagonal
operator (arbitrary index set), not a finite secular-equation shadow:
`GaloisForLFunctions.secular_exists_root` (a root of the secular equation
`F(mu) = sum_j ell_j^2/(d_j - mu) = 0` exists in each gap between consecutive leakage values with
nonzero coordinate) and `secular_root_unique` (it is unique, since `F` is strictly monotone —
`secular_strictMonoOn`); the ladder interlacing `d_k <= mu_k <= d_(k+1)` across three consecutive
scales is `secular_interlacing` (`ProlateSecularEquation.lean`).  The base ratio limit specializes to
`theta_0 = q_0/(q_0+q_1) = 1/(1 + binom(4,2)/16) = 8/11 = ccm_groundState_weight_eq`.

The exact all-depth **two-mode Fuchs model** of limit `(8)` is now formalized in
`TwoModeFuchsLimit.lean`.  The theorem `constrainedProlateHermiteTheta_eq_square_ratio` identifies
the aggregated head weight with `theta_k`, and
`constrainedProlate_fixedMode_twoMode_fuchs_ratio` proves for every `k` that the corresponding
normalized two-mode secular root tends to `theta_k`.  The complementary gap law is
`constrainedProlate_fixedMode_twoMode_fuchs_gap_ratio`, with limit `1-theta_k`; its quantified
corollary `constrainedProlate_fixedMode_twoMode_fuchs_gap_eventually_ge` proves that every
`c < 1-theta_k` is eventually a lower bound for the unnormalized gap after multiplication by the
dominant Fuchs leakage.  These are unconditional theorems about the exact Fuchs-rate model, not
assumptions about the true prolate operator.

What remains unformalized is the passage from that model to the card's exact constrained
eigenvalue `mu_k`: Fuchs fixed-index asymptotics for the actual leakages, normalized
prolate-to-Hermite convergence `ell_j -> a_j`, and the uniform infinite-tail secular estimate.
Those analytic inputs are also needed for the exact `lambda^8` adjacent-level asymptotics `(9)`.

`formal/GaloisForLFunctions/RHTower/ConstrainedProlateHermiteContrast.lean` now formalizes the
complete limiting Hermite algebra used by that missing analytic passage. It defines the actual
weights `q_j=choose(4j,2j)/16^j`, the positive coordinates with
`a_j^2=sqrt(2)q_j`, the partial sums `Q_k`, and `theta_k=Q_k/Q_(k+1)`. It proves unconditionally
that every explicit vector `w_k` satisfies the vanishing-integral constraint, that distinct `w_k`
are mutually orthogonal, and that `w_k` is orthogonal to every preceding raw CCM contrast. It also
certifies

```text
q_0=1, q_1=3/8, q_2=35/128,
Q_0=1, Q_1=11/8, Q_2=211/128,
theta_0=8/11, theta_1=176/211,
Q_1^2/(Q_0 Q_2)=242/211.
```

Thus equations `(4)`, `(5)`, and the exact algebraic content of `(10)`--`(13)` are now in Lean.
The remaining gate is specifically the concrete analytic convergence from the actual prolate
operator to this ladder; it is not replaced by an asymptotic hypothesis.

## Gates

- [x] exact all-fixed-mode theorem stated
- [x] complete paper proof including the infinite tail
- [x] exact first two constants and adjacent-gap law
- [x] parent-theory and rediscovery attack
- [x] preliminary literature audit through July 2026
- [x] provisional significance gate
- [x] all-depth aggregated two-mode Fuchs limits `theta_k` and `1-theta_k` formalized in Lean
- [x] quantified eventual lower bound for every constant below the all-depth Fuchs gap limit
- [ ] transfer the all-depth Fuchs model to the exact infinite-dimensional constrained ladder
- [ ] independent proof review
- [ ] independent literature review
- [ ] true finite-prime Weil spectral-ladder transfer
- [ ] Lean analytic-operator/asymptotic infrastructure
