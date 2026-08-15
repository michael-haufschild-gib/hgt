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

`formal/GaloisForLFunctions/RHTower/HermiteContrastLp.lean` upgrades that algebra to genuine
Hilbert-space objects, unconditionally.  Each contrast vector is supported on the first `k+2`
coordinates, hence lies in `ell^2` (`memℓp_constrainedProlateHermiteContrast`); the `ell^2` inner
product of two contrast vectors is exactly the algebraic pairing (`inner_hermiteContrastLp`), so
`(11)` holds as genuine orthogonality in `ell^2` (`inner_hermiteContrastLp_eq_zero`); no contrast
vector vanishes, its top coordinate being `S_k/a_(k+1)` (`hermiteContrastLp_ne_zero`); and the
normalized ladder is an orthonormal system (`orthonormal_hermiteContrastUnit`).  The exact squared
norm is computed in closed form,

```text
||w_k||^2 = sqrt(2) * Q_k * Q_(k+1) / q_(k+1)                (norm_sq_hermiteContrastLp_eq)
```

so the normalization appearing in `(10)` is explicit rather than implicit.  The raw CCM contrasts
`r_m = a_0 e_m - a_m e_0` are likewise placed in `ell^2` (they are supported on two coordinates),
and `inner_hermiteContrastLp_rawHermiteContrastLp_eq_zero` proves `<w_k, r_m> = 0` in `ell^2` for
every `0 < m <= k`.  Together with the mutual orthogonality of the ladder this exhibits `w_k` as
the Gram--Schmidt orthogonalization of the raw family as an identity between genuine Hilbert-space
vectors, which is the `[PROVED HERE; BRIDGE]` claim above.

The direction is moreover PINNED, unconditionally:
`eq_smul_constrainedProlateHermiteContrast_of_orthogonal` proves that any vector supported on the
first `k+2` coordinates which is orthogonal to the constraint and to every preceding raw contrast
is a scalar multiple of `w_k`.  The raw conditions force `x_m a_0 = x_0 a_m` for `m <= k`, so the
head is proportional to `(a_0,...,a_k)`, and the constraint then determines the top coordinate as
`-(x_0/a_0) S_k/a_(k+1)`.  This is the finite-dimensional uniqueness the eigenvector limit must
reproduce; it removes the apparent `(k+1)`-dimensional freedom in the depth-`k` head plane.
Transported to `ell^2` (`eq_smul_hermiteContrastLp_of_orthogonal`) and combined with
normalization, this yields `eq_pm_hermiteContrastUnit_of_orthogonal`: a UNIT vector of `ell^2`
supported on the first `k+2` coordinates and orthogonal to the constraint and to every preceding
raw contrast equals `+/-` the normalized ladder vector.  That is precisely the card's phrase "the
unique unit vector up to sign", now a theorem rather than a description.

The pinning is moreover QUANTITATIVE, and exactly so.  Because the uniqueness argument is an exact
computation it survives perturbation with no compactness step:
`sub_smul_hermiteContrast_head_eq_raw` proves that for `0 < m <= k` the deviation of `x_m` from the
ladder direction, multiplied by `a_0`, EQUALS the raw pairing `<x, r_m>`; and
`sub_smul_hermiteContrast_top_mul` gives the corresponding exact identity for the top coordinate in
terms of the constraint pairing corrected by the head defects.  A convergence proof therefore has
only to drive the orthogonality defects to zero -- the passage from "defects small" to "close to the
ladder" is an identity, not an estimate.

This supplies the LIMIT side of `(10)`--`(11)` as `ell^2` data.

`formal/GaloisForLFunctions/RHTower/ConstrainedProlateDepthVectorLimit.lean` now completes the
exact-root assembly under the named analytic contract.  It proves square-summability of every
fixed-depth secular eigenvector, convergence of every finite-head coordinate ratio, collapse of
the full offset tail, and the strong `ell^2` limit after scaling by the zeroth coordinate
(`ClockEnvelope.ccm_depth_rescaled_secularLp_tendsto_hermiteContrast`).  The normalized capstone
`ClockEnvelope.ccm_depth_normalized_rescaled_secularLp_tendsto_hermiteContrastUnit` proves that
the resulting unit eigenvector converges strongly to `-hermiteContrastUnit k`; the minus sign is
the canonical orientation forced by the negative zeroth coordinate of `w_k`.  No root-existence,
tail, summability, or infinite-dimensional hypothesis remains outside `ClockEnvelope`, Bessel
control, and the named finite prolate-to-Hermite coordinate limits.  Discharging those last true
operator inputs remains the separate gate below.

The **adjacent-level law `(9)` and its first excited constant `(13)` are now formalized** for the
two-mode Fuchs model in `GaloisForLFunctions/RHTower/LadderAdjacentScaleSeparation.lean`.  Writing
`ladderTwoModeRoot A k lam` for the depth-`k` rung, `RHTower.ladder_adjacent_ratio_tendsto` proves
that the adjacent rung ratio, corrected by the ratio of the two dominant leakages, converges to
`theta_(k+1)/theta_k`, and `RHTower.constrainedProlateHermiteTheta_adjacent_ratio` evaluates that
quotient as the pure partial-sum constant `Q_(k+1)^2/(Q_k Q_(k+2))`.

Because one radial rung advances the Fuchs index by exactly `4`, the common exponential clock
cancels and the corrected ratio is an exact power of the aperture.
`RHTower.ladder_adjacent_ratio_scaled_tendsto` therefore proves the card's `lambda^8` law in the
sharp rescaled form

```text
(mu_(k+1)/mu_k)/lambda^8
  -> [Q_(k+1)^2/(Q_k Q_(k+2))] * (A_(k+2)/A_(k+1)),
```

which is `(9)` with its constant `C_k` made explicit.  Its `k = 0` specialization
`RHTower.ladder_firstExcited_ratio_scaled_tendsto` gives the exact rational coefficient
`242/211`, i.e. `(13)`.  With `c = lambda^2` this is the card's `c^4` adjacent-gap fingerprint.
These theorems are unconditional statements about the Fuchs-rate model and are axiom-clean.

**The exact all-depth ladder law `(8)` is now formalized** in
`formal/GaloisForLFunctions/RHTower/ConstrainedProlateDepthSecular.lean`, for the true
infinite-dimensional constrained secular problem at every fixed depth `k`, by a flattening
sandwich.  On the `k`-th gap `(d_k, d_(k+1))` the full secular function (Finset head of `k+1`
poles + shoulder + `tsum` tail) is squeezed pointwise between two aggregated two-pole models —
head poles flattened down to `0` and up to `d_k`, head mass `Σ_(j≤k) ℓ_j²` — because
`1/(d_k−μ) ≤ 1/(d_j−μ) ≤ 1/(0−μ)` for `0 ≤ d_j ≤ d_k < μ`.  Both flattened models are literal
first-gap instances of the infinite secular theory, so their roots obey the two-mode limit; the
exact depth-`k` root exists (IVT between the flattened roots once the lower one clears `d_k`,
which happens eventually), is unique (strict monotonicity on the gap:
`depthSecular_strictMonoOn`), is trapped between them (`depthSecularRoot_bracket`), and inherits
the limit by squeeze.  The family theorem `depthSecularRoot_ratio_tendsto` proves

```text
mu_k(lambda)/d_(k+1)(lambda) -> S_k/(S_k + a_(k+1)^2)
```

under the depth-`k` transfer hypotheses (ordered head, Bessel bound `Σℓ² ≤ 2λ`,
`d_k/d_(k+1) → 0`, `λ·d_(k+1)/(d_(k+2)−d_(k+1)) → 0`, coordinate limits `ℓ_j → a_j` for
`j ≤ k+1`), and `ccm_depthSecularRoot_ratio_tendsto` evaluates the limit at the Hermite
coordinates as exactly `theta_k = Q_k/Q_(k+1)` — equation `(8)` for the exact constrained
spectrum, with no truncation.  All axiom-clean.

`formal/GaloisForLFunctions/RHTower/ConstrainedProlateLadderPrimeScale.lean` now proves the
finite-prime reparametrization for these same infinite-dimensional roots, rather than only citing
it after the two-mode calculation.  The generic theorem
`tendsto_div_pow_four_comp_sqrt_of_div_pow_eight` transports any `lambda^8`-normalized limit along
`X = lambda^2`; `ccm_fuchsModel_ladder_adjacent_primeScale_tendsto` applies it to the exact depth
roots and proves literally

```text
(mu_(k+1)(sqrt X)/mu_k(sqrt X))/X^4
  -> (theta_(k+1)/theta_k) * (A_(k+2)/A_(k+1)).
```

Thus the `c^4` statement is an unconditional Lean theorem about the exact Fuchs secular ladder,
not a prose corollary or a two-mode replacement.  Its remaining hypotheses are precisely the
named constraint-coordinate inputs of the exact-root theorem.

The concrete source regularity needed to state those inputs on actual modes is now axiom-clean in
`formal/GaloisForLFunctions/RHTower/ConstrainedProlatePointwiseRepresentative.lean`: every fixed
signed value is eventually nonzero; the resulting actual mode is unit-normalized and has a
canonical even compact source whose Fourier representative is globally `C^∞` and whose literal
interior source is `C^∞`.  All iterated derivatives are identified with exact compact Fourier
moments, and the exterior mass is exactly `1 - σ_n(a)²`.  This closes source choice, pointwise
representative, smoothness, normalization, and leakage bookkeeping.  It does not replace the
remaining prolate ODE numbering or Fuchs asymptotic proof.

The remaining gate for the true prolate operator is the concrete analytic inputs — Fuchs
fixed-index asymptotics for the true leakages and normalized prolate-to-Hermite convergence
`ell_j -> a_j` — plus the Fuchs-model depth-`k` discharge and the exact-root `lambda^8`
adjacent law `(9)` (its two-mode and leakage-side forms are already formalized in
`LadderAdjacentScaleSeparation.lean`).  None of this is replaced by an asymptotic hypothesis.

## Gates

- [x] exact all-fixed-mode theorem stated
- [x] complete paper proof including the infinite tail
- [x] exact first two constants and adjacent-gap law
- [x] parent-theory and rediscovery attack
- [x] preliminary literature audit through July 2026
- [x] provisional significance gate
- [x] all-depth aggregated two-mode Fuchs limits `theta_k` and `1-theta_k` formalized in Lean
- [x] quantified eventual lower bound for every constant below the all-depth Fuchs gap limit
- [x] adjacent-level law `(9)` formalized in Lean with explicit constant
  `[Q_(k+1)^2/(Q_k Q_(k+2))]·(A_(k+2)/A_(k+1))`
- [x] `lambda^8` and the literal `X=lambda^2`, `X^4` adjacent scale separation for the exact
  infinite-dimensional roots formalized in Lean (`ConstrainedProlateLadderPrimeScale`)
- [x] first excited coefficient `242/211` of `(13)` formalized in Lean
- [x] exact infinite-dimensional constrained root in EVERY spectral gap: existence, uniqueness,
  bracket, and the all-depth law `mu_k/d_(k+1) -> theta_k` `(8)` formalized in Lean via the
  flattening sandwich (`ConstrainedProlateDepthSecular`)
- [x] Fuchs-model depth-`k` discharge (`fuchsRate_radial_depth_struct`,
  `ccm_fuchsModel_depthSecularRoot_ratio_tendsto`) and the exact-root `lambda^8` adjacent law
  `(9)` (`ccm_fuchsModel_ladder_adjacent_scaled_ratio_tendsto`, coefficient
  `(theta_(k+1)/theta_k)·A_(k+2)/A_(k+1)`) formalized in Lean
- [x] exact-root eigenvector ladder assembly `(10)`--`(11)` in Lean from `ClockEnvelope`, Bessel
  control, and the named finite coordinate limits, including strong normalized `ell^2` convergence
- [ ] true-operator ℓ-side inputs (Bessel bound, prolate-to-Hermite limits) and Fuchs
  identification in Lean
- [ ] independent proof review
- [ ] independent literature review
- [ ] true finite-prime Weil spectral-ladder transfer
- [ ] Lean analytic-operator/asymptotic infrastructure

## Lean progress — the oscillator-ladder pin, and what the prolate-to-Hermite gate now needs

The open gate on this card is the pair of true-operator ℓ-side inputs: the prolate-to-Hermite
coordinate limits and the Fuchs identification.  Their common foundation is now formal, and the
last step turned out to be an identity rather than an asymptotic argument.

What the corpus already owned (no new work): the whole commuting-operator layer —
`HTGeometry/SturmSelfAdjoint.lean`, `HTGeometry/ProlateKernelSymmetry.lean`,
`RHTower/ProlateCommutationKernel.lean` (`prolateAction_bandEigen_eq_smul`: an eigenfunction of the
finite Fourier transform solves the prolate ODE), `RHTower/SlepianBandCommutation.lean`,
`RHTower/FuchsProlateScale.lean` (the exact scaling identity `prolateSLAction_sqrtScale`),
`RHTower/HermiteOscillatorEigen.lean` (`hermiteSLAction_hermiteFun`: eigenvalue `−(2n+1)`), and
`RHTower/ProlateHermiteRescale.lean`, whose
`exists_even_prolateHermiteRescale_of_signedMode` gives every live signed mode a smooth even global
profile whose Hermite rescaling satisfies, **with no convergence premise**,

```text
hermiteSLAction u + (c·s)·u = (ξ² u″ + 2ξ u′)/c ,      c = 2πλ² .
```

New (wired, axiom-clean):

```text
HTGeometry/WholeLineWronskianSymmetry.lean
    integral_deriv_eq_zero_of_tendsto_zero   a derivative whose primitive tends to 0 at ±∞
                                             integrates to 0 over the line
    hasDerivAt_wronskian                     (u′v − uv′)′ = u″v − uv″
    integral_secondDeriv_pairing_eq_zero
    integral_secondDeriv_mul_comm            ∫ u″v = ∫ u v″ for a vanishing Wronskian

RHTower/ProlateOscillatorLadderPin.lean
    hasDerivAt_hermiteFun, hasDerivAt_deriv_hermiteFun
    hermitePairing_pin (n) :
        hermiteSLAction u + μ·u = D  ⟹  (μ − (2n+1))·⟨u, φₙ⟩ = ⟨D, φₙ⟩
    abs_sub_oscillatorLadder_eq (n) :
        |μ − (2n+1)| = |⟨D, φₙ⟩| / |⟨u, φₙ⟩|
```

The `ξ²` potential cancels identically — it appears with the same sign on both sides of the
integration by parts — so no spectral theorem, no operator domain and no quasimode inequality is
used.  Applied to the prolate identity above,

```text
|c·s(c) − (2n+1)| = |⟨ξ²u″ + 2ξu′, φₙ⟩| / (c · |⟨u, φₙ⟩|) .
```

**Consequently the whole remaining analytic content of this card's prolate-to-Hermite gate is one a
priori bound**: that the defect pairing `⟨ξ²u″ + 2ξu′, φₙ⟩` stays bounded relative to `⟨u, φₙ⟩` as
the bandwidth grows.  That is a statement about a single rescaled profile against a single Gaussian
weight; it needs no expansion and no uniformity in the index.  With it, the eigenvalue is pinned to
the oscillator ladder at rate `1/c`, the same pairing pins the eigenvector, and
`ℓ_j = χ_{4j}·e_j(0)` with `χ → 1` delivers the coordinate limits `ℓ_j → |ĥ_{4j}(0)|` whose targets
`2^{1/4}` and `√3·2^{−5/4}` are already formal in `HermiteOriginConstraintTargets.lean`.

## Lean progress — the defect pairing needs no derivative bound at all

The note above reduced this card's prolate-to-Hermite gate to a single a priori bound on the defect
pairing `⟨ξ²u″ + 2ξu′, φₙ⟩`.  That bound is no longer needed in that form: the pairing transfers
entirely onto the Hermite side.

`GaloisForLFunctions/HTGeometry/WholeLineWronskianSymmetry.lean` (extended, wired):

```text
integral_deriv_mul_eq_neg     ∫ u′v = −∫ u v′ when u v → 0 at both ends
```

`GaloisForLFunctions/RHTower/ProlateDefectTransfer.lean` (wired):

```text
hermiteSqWeight n x           = x² φₙ(x)          (with its two derivatives)
hermiteLinWeight n x          = 2x φₙ(x)          (with its derivative)
integral_prolateDefect_transfer :
    ⟨ξ²u″ + 2ξu′, φₙ⟩ = ⟨u, ξ²φₙ″ + 2ξφₙ′⟩
integral_prolateDefect_transfer_explicit :
    ⟨ξ²u″ + 2ξu′, φₙ⟩ = ⟨u, ξ²(ξ² − 2n − 1)φₙ + 2ξφₙ′⟩
prolateLadder_pin_hermiteSide :
    (μ − (2n+1))·⟨u, φₙ⟩ = ⟨u, ξ²(ξ² − 2n − 1)φₙ + 2ξφₙ′⟩ / c
```

Two integrations by parts — one of second order against the weight `ξ²φₙ`, one of first order
against `2ξφₙ` — move both derivatives of the profile onto the Hermite factor, and
`φₙ″ = (ξ² − 2n − 1)φₙ` makes the surviving weight completely explicit.  The `4ξφₙ′` produced by the
second-order transfer and the `−2ξφₙ′` produced by the first-order one combine to `2ξφₙ′`, and the
two `±2φₙ` cancel.

**Consequence for this card.**  The distance from the rescaled eigenvalue `c·s(c)` to the `n`-th rung
of the oscillator ladder is now, exactly,

```text
|c·s(c) − (2n+1)| = |⟨u, ξ²(ξ² − 2n − 1)φₙ + 2ξφₙ′⟩| / (c · |⟨u, φₙ⟩|) ,
```

in which **no derivative of the prolate profile appears**.  What remains is a comparison of two
pairings of the profile against fixed Gaussian-decaying weights — the numerator against
`ξ²(ξ²−2n−1)φₙ + 2ξφₙ′` and the denominator against `φₙ` — plus the decay hypotheses that make the
two integrations by parts legitimate.  That is a non-degeneracy statement about one function against
one fixed weight, not an asymptotic expansion.

## Lean progress — the eigenvalue half of the prolate-to-Hermite gate closes

The residue recorded in the previous section was a lower bound on `|⟨u, φₙ⟩|`, uniform in the
bandwidth.  It is not an obstruction: the Hermite rescaling *flattens* the profile, so the pairing
has an explicit limit.

`GaloisForLFunctions/RHTower/ProlateCentreValuePairing.lean` (wired):

```text
tendsto_div_sqrt_atTop            ξ/√c → 0
tendsto_integral_rescaled_mul     ∫ Φ(ξ/√c) W(ξ) dξ ⟶ Φ(0) · ∫ W        (W integrable)
tendsto_zero_of_ladderPin
    d(c)·⟨u_c, V⟩ = ⟨u_c, W⟩/c ,  Φ(0)·∫V ≠ 0   ⟹   d(c) → 0
```

The pairing limit is dominated convergence with the two cheapest possible hypotheses on `Φ`:
continuity at the origin and boundedness.  Both are free — the profile is continuous by
construction, and `abs_le_of_bandTransform_eigen` makes it decay, hence bounded.

Applied to the ladder pin with `V = φₙ` and `W = ξ²(ξ²−2n−1)φₙ + 2ξφₙ′`, the denominator pairing
tends to `Φ(0)·∫φₙ` and the numerator pairing stays bounded, so

```text
c·s(c) − (2n+1) ⟶ 0 .
```

The nonvanishing hypothesis `Φ(0)·∫φₙ ≠ 0` is not an extra asymptotic input.  `∫φₙ ≠ 0` holds for
the even Hermite indices this card uses.  And `Φ(0) ≠ 0` follows from the data already in hand,
by ODE uniqueness rather than by assumption: the profile is **even**, so `Φ′(0) = 0`; the prolate
equation `(1 − x²)Φ″ − 2xΦ′ − c²x²Φ = χΦ` has leading coefficient `1` at `x = 0`, so the origin is
an ordinary point; hence `Φ(0) = 0` together with `Φ′(0) = 0` would force `Φ ≡ 0`, contradicting
`Φ ≠ 0`.

(An earlier draft of this note claimed `Φ(0) ≠ 0` was supplied by
`exists_even_prolateHermiteRescale_of_signedMode`'s hypothesis `evenProlateSignedValue a n ≠ 0`.
That is not so: `evenProlateSignedValue` is the signed *eigenvalue* `sgVal (evenTimeBandFourier a) n`,
not the centre value.  The uniqueness argument above is what supplies it.)

**Status of this card's gate.**  The *eigenvalue* half of the prolate-to-Hermite limit —
`c·s(c) → 2n+1`, equivalently the fixed-index prolate eigenvalue asymptotic at leading order — is
now a Lean theorem given the instantiation.  What the card still needs beyond it is the
*eigenvector* half, `ℓ_j(λ) → |ĥ_{4j}(0)|`, and the Fuchs identification of the leakage rates.

## The eigenvector half: why the Hermite-coefficient route is blocked, and what replaces it

The natural way to get `ℓ_j(λ) → |ĥ_{4j}(0)|` from the ladder pin is to expand the rescaled profile
in the Hermite basis.  The pin already forces every coordinate off the `n`-th rung to vanish:

```text
(μ − (2m+1)) · ⟨u, φ_m⟩ = ⟨u, ξ²(ξ²−2m−1)φ_m + 2ξφ_m′⟩ / c ,
```

so `|⟨u,φ_m⟩| ≤ ‖W_m‖ / (c |μ − (2m+1)|) → 0` for each fixed `m ≠ n`.  Coordinatewise vanishing plus
unit mass does **not** give `⟨u,φ_n⟩² → 1`: mass can drift to high rungs.  What closes that gap is a
uniform bound on the harmonic-oscillator energy `∑ (2m+1)⟨u,φ_m⟩² = ‖u′‖² + ‖ξu‖²` — boundedness
suffices, no rate (see `HTGeometry/OscillatorMassNoEscape.lean`).

**That energy is infinite for both natural normalizations of a prolate mode**, and this is not an
artefact:

- the compactly supported representative `e = ψ·1_{[−λ,λ]}` has finite `∫ t²e²` but a jump at `±λ`,
  hence `‖e′‖ = ∞`;
- the entire bandlimited profile `ψ` has finite `‖ψ′‖ ≤ 2πλ‖ψ‖` (it is bandlimited) but decays only
  like `1/t` — its Fourier transform is the truncated mode, which jumps — so `∫ t²ψ² = ∞`.

Neither object lies in the oscillator form domain.  The obstruction is exactly the time–frequency
duality that makes the prolate problem interesting, so the coefficient route cannot be repaired by
choosing the normalization better; it would need a fractional energy `⟨u, H^s u⟩` with `s < 1/2`.

### The route that does close it: linear ODE comparison on a fixed window

The rescaled profile satisfies, with **no convergence premise**,

```text
u″ − ξ²u + μu = (ξ²u″ + 2ξu′)/c ,     i.e.    u″ = [(ξ² − μ)u + (2ξ/c)u′] / (1 − ξ²/c) ,
```

which on a fixed window `|ξ| ≤ K` is a *regular* linear ODE as soon as `c > K²`, with coefficients
converging uniformly to those of the Hermite equation `v″ = (ξ² − (2n+1))v`.  Writing
`u = α_c · Ψ_c` with `Ψ_c(0) = 1`, `Ψ_c′(0) = 0` (the profile is even, so `u′(0) = 0`), linearity
removes the unknown amplitude from the comparison, and Grönwall gives

```text
Ψ_c → φ_n / φ_n(0)   uniformly on [−K, K] .
```

Uniqueness of the even solution of the Hermite equation at eigenvalue `2n+1` identifies the limit;
no decay condition at infinity is needed, because the initial-value problem already determines it.

The amplitude is then pinned by the normalization *together with the time second moment*, which is
finite and uniformly bounded — this is the one moment that survives:

```text
∫ t² e_λ(t)² dt / ∫ e_λ² = λ² ∫ x²Φ² / ∫ Φ² ≤ λ² μ / c = μ / (2π) ,
```

using only the prolate quadratic form `∫(1−x²)Φ′² + c²∫x²Φ² = μc` and `c = 2πλ²`.  Chebyshev then
gives `∫_{|t|>K} e_λ² ≤ M/K²` uniformly, so passing `1 = ∫e_λ²` to the limit yields
`α_c² → φ_n(0)²/‖φ_n‖²`, and the same second moment controls the far part of the integral
(`RHTower/SecondMomentIntegralTail.lean`:
`|∫_K^R f| ≤ (1+M)/(2√K)` from `∫x²f² ≤ M`).  Hence

```text
(∫ e_λ)² → (∫ φ_n)² / ‖φ_n‖² ,
```

which is the eigenvector half in squared form — the form the downstream cards consume
(`tendsto_ellSqRatio_of_hermiteLimits` takes `ell_j²` limits).

No `L²` compactness, no Parseval, no Riesz–Kolmogorov and no energy bound is used anywhere in this
route; the only analytic engine is Grönwall on a compact window.

## Lean progress — the window-comparison engine, and the scale-free form of the coordinate limit

New (wired, axiom-clean):

```text
HTGeometry/LinearSecondOrderComparison.lean
    phasePair, norm_phasePair, hasDerivAt_phasePair
    phasePair_norm_le      a priori exponential phase bound for u'' = P u + Q u'
    phasePair_dist_le      Grönwall separation of u'' = P_c u + Q_c u' from v'' = P v
                           with the same initial phase vector

HTGeometry/LinearSecondOrderLimit.lean
    phasePair_dist_le_uniform            the envelope taken at the right endpoint
    tendsto_sup_dist_of_coeff_tendsto    vanishing coefficient perturbation ⇒ vanishing envelope
    abs_intervalIntegral_sub_le_of_uniform

HTGeometry/OscillatorMassNoEscape.lean
    tsum_nat_add_le_of_moment_le          tail ≤ C/(2M+3) from ∑(2m+1)f m ≤ C
    tendsto_coeff_of_vanishing_of_moment_le

RHTower/HermiteCoefficientPin.lean
    tendsto_coeff_zero_of_pin, tendsto_coeffSq_of_ladderPin

RHTower/SecondMomentIntegralTail.lean
    abs_le_weighted_split                 |f| ≤ (s/x² + x²f²/s)/2
    abs_integral_le_of_secondMoment_sqrt  |∫_K^R f| ≤ (1+M)/(2√K) from ∫x²f² ≤ M
    abs_integral_le_of_sq_and_secondMoment
    tendsto_integral_of_tendsto_sq_of_secondMoment

RHTower/ProlateRescaledCoefficients.lean
    rescaledProlateP, rescaledProlateQ, hermiteRungP
    deriv2_eq_of_hermiteDefect            normal form of the exact Hermite-scale defect identity
    abs_rescaledProlateP_sub_le           ≤ 2|μ−(2n+1)| + 2K²(K²+2n+1)/c
    abs_rescaledProlateQ_le               ≤ 4K/c

RHTower/ProlateProfileWindowLimit.lean
    prolateProfile_window_dist_le         the explicit Grönwall envelope on [0,K]
    prolateProfile_window_phase_le        a priori phase bound on [0,K]
    tendsto_prolateWindow_envelope
    tendsto_prolateProfile_window         u_c → v pointwise on [0,K] once μ_c → 2n+1, c → ∞
```

Two corpus assets close what looked like separate obligations:

- `SlepianKernelScaledFubini.value_zero_ne_of_even_joint_prolate_band_eigen` already proves
  `Φ(0) ≠ 0` for a nonzero smooth even joint band/prolate eigenfunction, by exactly the
  ODE-uniqueness argument recorded above — so the centre-value nonvanishing input is not open.
- `ProlateSeparationEnergy.neg_separation_div_sq_mul_integral_sq_eq` is the exact Rayleigh identity

  ```text
  s · ∫_{-1}^{1} Φ² = (∫_{-1}^{1}(1−x²)Φ′²)/c² + ∫_{-1}^{1} x²Φ² ,      s = −χ/c² ,
  ```

  whose first term is nonnegative, so `∫x²Φ² ≤ s ∫Φ²` — the second-moment bound, with no new
  integration by parts.

### The coordinate limit is scale-free

Writing the unit-norm mode as `e(t) = κ Φ(t/λ)` with `∫_{-λ}^{λ} e² = 1` gives
`ℓ² = λ(∫_{-1}^{1}Φ)²/∫_{-1}^{1}Φ²`, and in the Hermite variable `ξ = √c x`, `c = 2πλ²`,

```text
ℓ² = (∫ u)² / (√(2π) · ∫ u²) .
```

The amplitude cancels, so **no normalization of the profile has to be pinned**: the limit follows
from local uniform convergence of `u` up to scale together with the normalized second-moment bound
`∫ξ²u² / ∫u² = c ∫x²Φ² / ∫Φ² ≤ c·s = μ`, which controls both tails.  The target value checks out on
the ground mode: with `φ₀ = e^{−ξ²/2}`, `(∫φ₀)²/(√(2π)∫φ₀²) = 2π/(√(2π)√π) = √2 = (2^{1/4})²`.

## Correction — the eigenvalue half is not closed by the centre-value pairing

An earlier note on this card recorded that the *eigenvalue* half `c·s(c) → 2n+1` "is now a Lean
theorem given the instantiation", via `RHTower/ProlateCentreValuePairing.lean`
(`tendsto_zero_of_ladderPin`).  That is wrong, and the reason is structural rather than technical.

`tendsto_integral_rescaled_mul` and `tendsto_zero_of_ladderPin` take **one fixed** profile `Φ` and
let the bandwidth act only through the rescaling `Φ(ξ/√c)`; the flattening that produces
`Φ(0)·∫V` in the limit is dominated convergence for that single function.  The prolate family does
not have that shape: its profile `Φ_c` is itself the `c`-dependent eigenfunction, so there is no
fixed `Φ` to rescale.  The two theorems remain correct and reusable, but they do not instantiate
here.

### What the eigenvalue half actually needs

With the window machinery now in place the missing input is one classical rigidity statement:

```text
if v ∈ L²(ℝ) is even and solves  v″ = (ξ² − μ) v  on all of ℝ,  then μ = 2n+1 for some even n,
and v is a multiple of the corresponding Hermite function.
```

Given it, both halves follow from the same argument.  Normalize `Ψ_c = u_c/u_c(0)` (legitimate:
`Φ(0) ≠ 0` is `SlepianKernelScaledFubini.value_zero_ne_of_even_joint_prolate_band_eigen`).  The
separation constants `μ_c` are bounded, so along any subsequence `μ_c → μ*`, and
`tendsto_prolateProfile_window` gives `Ψ_c → Ψ*` locally uniformly with `Ψ*″ = (ξ² − μ*)Ψ*`,
`Ψ*(0) = 1`, `Ψ*′(0) = 0`.  The normalized second-moment bound
`∫ξ²Ψ_c² ≤ μ_c ∫Ψ_c²` (now formal as `integral_rescaled_secondMoment_le`) makes the family tight, so
`∫_{-K}^{K}Ψ_c²` is bounded below a constant multiple of `∫Ψ_c²` uniformly, `Ψ* ∈ L²`, and the
rigidity statement forces `μ* = 2n+1` and `Ψ* = φ_n/φ_n(0)`.  Every subsequential limit is the same,
so the full limits hold — the eigenvalue half — and the coordinate limit then follows in the
scale-free form recorded above.

The corpus owns the oscillator ladder on Schwartz space
(`HTGeometry/SchwartzOscillatorAlgebra.lean`, `HTGeometry/HermiteOrthogonality.lean` with
`creationCLM`, `annihilationCLM` and the commutator `BA − AB = 4π`,
`HTGeometry/HermiteNumberOperator.lean`), but not the passage from *an `L²` solution of the ODE* to
that ladder, which is where the rigidity statement has to be built: `A = d/dξ + ξ` satisfies
`A†A = −d²/dξ² + ξ² − 1`, so `‖Av‖² = (μ−1)‖v‖²` forces `μ ≥ 1`, `Av` solves the same equation at
`μ−2`, and iterating must terminate, with `Av = 0` solved only by `Ce^{−ξ²/2}`.

## Lean progress — spectral rigidity of the harmonic oscillator is now formal

The classical statement named above as the single missing input is now an unconditional Lean
theorem, built from scratch (mathlib has no oscillator spectral theory in ODE form).  All
declarations audit to `[propext, Classical.choice, Quot.sound]`.

```text
HTGeometry/OscillatorEnergyMonotone.lean
    oscEnergy mu v v' ξ = v′² − (ξ²−μ)v²        E′ = −2ξv²,  antitone on the positive axis
    oscRatio  mu v v' ξ = −E/(ξ²−μ)             G′ = 2ξv′²/(ξ²−μ)² ≥ 0,  G ≤ v²

HTGeometry/OscillatorProductMonotone.lean
    oscProduct v v' ξ = v v′                    (v v′)′ = v′² + (ξ²−μ)v² ≥ 0 past the turning point
    not_integrableOn_Ici_of_le                  a positive floor on a half line kills integrability
    hasDerivAt_reflect                          the potential is even, so ξ ↦ v(−ξ) solves the same
    oscProduct_neg_of_integrableOn              L² ⇒ v v′ < 0 past the turning point
    oscEnergy_nonneg_of_integrableOn            L² ⇒ E ≥ 0

HTGeometry/OscillatorRecessiveLimits.lean
    not_deriv_le_neg_of_nonneg                  the one mechanism used throughout
    sign_const_of_ne_zero                       a nowhere-zero continuous function has one sign
    tendsto_oscProduct_zero, tendsto_deriv_zero_of_pos
    tendsto_weighted_sq_zero, tendsto_mul_sq_zero

HTGeometry/OscillatorLadderIdentity.lean
    oscLower v v' = v′ + ξv,  oscBoundary v v' = v v′ + ξv²
    hasDerivAt_oscBoundary                      B′ = (Av)² + (1−μ)v²
    hasDerivAt_oscLower, hasDerivAt_oscLowerDeriv   Av solves the same equation at μ−2
    integral_oscLower_sq_interval               ∫_{−R}^{R}(Av)² = B(R) − B(−R) + (μ−1)∫v²
    integrable_oscLower_sq, integral_oscLower_sq_eq   ‖Av‖² = (μ−1)‖v‖²
    one_le_of_integrable_of_pos                 μ ≥ 1

HTGeometry/OscillatorBoundaryVanishing.lean
    tendsto_oscBoundary_atTop_zero, tendsto_oscBoundary_atBot_zero

HTGeometry/OscillatorSpectralRigidity.lean
    eq_zero_of_phase_zero                       ODE uniqueness in both directions, from Grönwall
    integral_sq_pos_of_nontrivial
    exists_rung_of_integrable :
        v″ = (ξ²−μ)v ,  v nontrivial ,  v ∈ L²   ⟹   ∃ n : ℕ, μ = 2n+1
```

The proof uses no decay rate, no spectral theorem, no compactness and no Fourier analysis.  Every
step is one monotone quantity plus the observation that a nonnegative function cannot have a
derivative bounded above by a negative constant.  The energy `E` separates recessive from dominant
behaviour; the product `v v′` supplies the sign, the boundary limits and the integrability of `Av`;
the ladder identity is a single application of the fundamental theorem of calculus to
`B = v v′ + ξ v²`; and the induction on `μ ≤ 2n+1` terminates because `Av` either vanishes
identically — pinning `μ = 1` — or is again a nontrivial `L²` solution at `μ − 2`.

With this in hand the remaining prolate obligations are: a two-sided bound on the separation
constants `μ_c = c·s_c` (the lower bound `s ≥ 0` is already in
`exists_even_prolateHermiteRescale_of_signedMode`), a subsequence argument on the resulting compact
range, and the identification of the limiting index with the mode index.

## The remaining prolate chain, in order

With oscillator spectral rigidity formal, the eigenvalue half reduces to four steps, each with a
definite route and no literature import.

1. **A uniform upper bound `μ_c ≤ M_n`.**  This is the only genuinely variational step, and it is
   where the mode *index* enters: `μ_c = c·s_c` is the oscillator energy of the rescaled mode, and
   bounding it for a fixed index is the min–max principle against an `(n+1)`-dimensional trial
   space.  The corpus already owns the `n = 0` machinery in the crude form — `ProlateGaussianTrial`
   (the exact action `L_c v = (−c + 3cx² − c²x⁴)v` for `v = e^{−cx²/2}`),
   `ProlateGaussianTrialPositive` (`Rayleigh(v) > −c²/2·‖v‖²`), and
   `ProlateLowSeparationMode.exists_even_joint_prolate_eigen_separation_lt_half` (the eigenspace
   decomposition turning a trial estimate into an actual mode).  The sharp threshold is the same
   computation at the right scale: `Rayleigh(v) ≥ −c‖v‖²` is exactly

   ```text
   ∫_{-1}^{1} (3c x² − c² x⁴) e^{−c x²} dx ≥ 0 ,
   ```

   which after `t = √c x` is `∫_{−√c}^{√c} t²(3 − t²)e^{−t²}dt ≥ 0`, positive in the limit because
   `∫_ℝ t²(3−t²)e^{−t²} = (3/4)√π > 0`, with an exponentially small truncation defect.  That gives
   `μ_0 ≤ 1`.  For index `n` the same argument runs with the `(n+1)`-dimensional span of
   `H_k(√c x)e^{−c x²/2}`, `k ≤ n`.

2. **The limit profile.**  `Ψ_c = u_c/u_c(0)` is uniformly Cauchy in `C¹` on every window: the
   Grönwall comparison of `LinearSecondOrderComparison` applies to *two* perturbed members as well
   as to a member against the limit equation (a one-line generalization of `phasePair_dist_le` to
   `v″ = P₂v + Q₂v′`).  Completeness of `ℝ` then defines `Ψ*(x) = lim_c Ψ_c(x)`, `Ψ*′` likewise, and
   passing the integral form `Ψ_c′(x) = ∫_0^x (P_cΨ_c + Q_cΨ_c′)` to the limit — legitimate by
   uniform convergence on the compact window — shows `Ψ*″ = (ξ² − μ*)Ψ*`.  No ODE existence theory
   is needed, only the family itself.

3. **`Ψ* ∈ L²`.**  `integral_rescaled_secondMoment_le` gives `∫ξ²u_c² ≤ μ_c ∫u_c²`, so Chebyshev
   bounds the mass outside a window by `μ_c/K²` times the total; the window integrals converge, and
   the total is therefore bounded.  Fatou on windows gives `∫Ψ*² < ∞`.

4. **`exists_rung_of_integrable`** then forces `μ* = 2m+1`, and every subsequential limit of the
   bounded family `μ_c` is such an `m`; identifying `m` with the mode index `n` is the last step,
   and follows from the ordering of the greedy signed values
   (`ProlateSignedLeakageOrdering.abs_sgVal_antitone`) together with the strict separation of the
   rungs.
