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

## Lean progress — the sharp Gaussian threshold

`RHTower/ProlateGaussianSharpRayleigh.lean` (wired, axiom-clean) closes step 1's analytic half at
the sharp scale, with no Gaussian moment evaluation:

```text
hasDerivAt_cubeGaussian                (y³e^{−cy²})′ = (3y² − 2cy⁴)e^{−cy²}
integral_quartic_gaussian              ∫_{-1}^{1}(3x² − 2cx⁴)e^{−cx²} = 2e^{−c}
integral_gaussian_correction_pos       0 < ∫_{-1}^{1}(3cx² − c²x⁴)e^{−cx²}
prolate_gaussian_rayleigh_gt_neg_bandwidth
    −c ∫ v²  <  ∫ v · L_c v ,     v = e^{−cx²/2} ,   for every c > 0
```

The whole content is one exact primitive plus the split
`3cx² − c²x⁴ = (3c/2)x² + (c/2)(3x² − 2cx⁴)`, which turns the correction into
`(3c/2)∫x²e^{−cx²} + c e^{−c}`, visibly positive.  The existing corpus estimate
`prolate_gaussian_rayleigh_gt` reached only the `c²/2` threshold (`s < 1/2`) and needed `c ≥ 400`
plus a three-region pointwise analysis; the sharp form needs neither.

What remains of step 1 is to run the corpus's eigenspace-decomposition argument
(`ProlateLowSeparationMode.exists_even_joint_prolate_eigen_separation_lt_half`) with the threshold
as a parameter rather than the hard-coded `c²/2`: its body uses `−(c²/2)` only as an opaque
multiplier, so a threshold-parametric restatement instantiates at `K = c` and yields an even joint
band/prolate eigenfunction with `−η < c`, i.e. **`μ = c·s < 1`** — the `n = 0` case of the uniform
bound.

## Lean progress — THE EIGENVALUE HALF CLOSES FOR THE GROUND MODE, UNCONDITIONALLY

`c·s(c) → 1` is now a Lean theorem with no hypotheses beyond the bandwidth being positive:

```text
RHTower/ProlateLowSeparationMode.lean   (generalized in place)
    exists_even_joint_prolate_eigen_gt_of_rayleigh_gt
        any Gaussian Rayleigh bound `⟨L_c v, v⟩ > −K‖v‖²` produces a joint band/prolate mode
        with `−K < η`; the old `c²/2` statement is now a one-line corollary

RHTower/ProlateSharpSeparationMode.lean
    exists_even_joint_prolate_eigen_bandwidth_separation_lt_one
        at every `c > 0` some even joint mode has `c·s < 1`

RHTower/ProlateSeparationLowerBound.lean
    hasDerivAt_virialWeight, integral_sq_window     ∫_{−δ}^{δ}Φ² = 2δΦ(δ)² − 2∫ xΦΦ′
    integral_sub_le_aperture, integral_sq_outside_le (Chebyshev), exists_le_average
    virial_amgm                                     −2xΦΦ′ ≤ c x²Φ² + Φ′²/c
    separation_algebra
    bandwidthSeparation_lower :
        c δ₀²(1 − 4δ₀²) ≤ μ (5(1 − 4δ₀²) + c δ₀²)   for every δ₀ ∈ (0, 1/4]

RHTower/ProlateSeparationLimit.lean
    integral_sq_pos_of_band_eigen, tendsto_one_of_sandwich
    exists_tendsto_bandwidthSeparation_one :
        ∃ μ, μ_c → 1  and every μ_c is the separation constant of an actual even joint
        band/prolate eigenfunction at bandwidth c
```

**The route bypasses the limit-profile construction entirely.**  The plan recorded above needed a
`C¹` limit of the rescaled profiles, its `L²` membership and then the ladder rigidity.  None of that
is used: the upper bound is the sharp Gaussian trial, and the lower bound is an *uncertainty*
estimate that holds for every mode at once —

```text
∫_{−δ}^{δ}Φ² ≤ 2δΦ(δ)² + μ ∫Φ²/(1 − 4δ₀²) ,     ∫Φ² − ∫_{−δ}^{δ}Φ² ≤ (μ/(cδ₀²)) ∫Φ² ,
2δΦ(δ)² ≤ (4μ/(cδ₀²)) ∫Φ² ,
```

the last two both from the second-moment bound `∫x²Φ² ≤ (μ/c)∫Φ²`, with the window endpoint chosen
by averaging `Φ²` over `[δ₀, 2δ₀]`.  Dividing by `∫Φ² > 0` gives
`1 ≤ 5μ/(cδ₀²) + μ/(1 − 4δ₀²)`, so `liminf μ ≥ 1 − 4δ₀²` for every `δ₀`.

The oscillator spectral rigidity theorem built earlier is therefore not needed for the ground mode.
It remains the tool for the higher rungs `n = 4j`, `j ≥ 1`, where the trial space is
`(j+1)`-dimensional and the limit is `2·4j + 1`; and it is a reusable statement in its own right.

## Lean progress — the aperture virial: a sharper and much shorter route, plus the Gaussian shape

The window/averaging estimate recorded above is superseded.  The weight `x(1−x²)` vanishes at *both*
aperture endpoints, so the virial identity has no boundary term at all:

```text
(x(1−x²)Φ²)′ = (1 − 3x²)Φ² + 2x(1−x²)ΦΦ′       ⟹     ∫Φ² − 3∫x²Φ² = −2∫ x(1−x²)ΦΦ′ .
```

Splitting the right-hand side exactly against the bandwidth,

```text
−2x(1−x²)ΦΦ′ = c x²Φ² + (1−x²)²Φ′²/c − (cxΦ + (1−x²)Φ′)²/c ,
```

and using `(1−x²)² ≤ 1−x²` on the aperture together with the Rayleigh identity gives, in one step,

```text
∫(cxΦ + (1−x²)Φ′)² ≤ c ((μ − 1) ∫Φ² + 3 ∫x²Φ²) .
```

`RHTower/ProlateApertureVirial.lean` (wired, axiom-clean):

```text
hasDerivAt_apertureVirialWeight, integral_apertureVirial, apertureVirial_split
integral_prolateGaussianDefect_le      the displayed estimate
bandwidthSeparation_ge :  c ≤ μ (c + 3)
```

`RHTower/ProlateGroundGaussianLimit.lean` (wired, axiom-clean):

```text
tendsto_one_of_sandwich_sharp          c ≤ μ(c+3) below and μ < 1 above force μ → 1
exists_ground_family :
    ∃ μ Ψ,  μ_c → 1  and at every c > 0 the function Ψ_c is an even joint band/prolate mode
    with separation constant μ_c, positive aperture mass, second moment ≤ (μ_c/c)∫Ψ_c², and
    ∫(cxΨ_c + (1−x²)Ψ_c′)² ≤ c((μ_c − 1)∫Ψ_c² + 3∫x²Ψ_c²)
```

No window, no averaging over `[δ₀, 2δ₀]`, no Chebyshev, no endpoint value — and the bound
`μ ≥ c/(c+3)` is sharper than `1 − 4δ₀²`.  The earlier window machinery
(`ProlateSeparationLowerBound.lean`) is kept: its `exists_bandwidthSeparation_defect` localizes the
Gaussian defect to a window, which the aperture version does not.

Dividing the defect bound by `c ∫Ψ_c²` and using `∫x²Ψ_c² ≤ (μ_c/c)∫Ψ_c²`,

```text
∫(cxΨ_c + (1−x²)Ψ_c′)² / (c ∫Ψ_c²)  ≤  (μ_c − 1) + 3μ_c/c  →  0 ,
```

so the selected mode becomes the prolate Gaussian in mean square.  That is the first half of the
eigenvector gate; what remains is to convert the mean-square shape statement into the coordinate
limit `ℓ_0² = λ(∫Φ)²/∫Φ² → √2`.

## The eigenvector half, reduced to one scalar asymptotic — and the structural gap that remains

Two reductions make the remaining content explicit.

**1.  The coordinate is a peak-to-mass ratio, not an integral.**  The corpus's evaluation identity
(`ConstrainedProlateEvaluationIdentity.timeBandEigenSourceIntegral_eq_mul_pointwiseSource_zero`)
gives `ℓ = χ·e(0)` for the unit-norm compact representative.  Writing `e(t) = κΦ(t/λ)` and using
`∫_{-λ}^{λ}e² = 1`,

```text
ℓ² = λ (∫_{-1}^{1}Φ)² / ∫_{-1}^{1}Φ²  =  χ² Φ(0)² / (λ ∫_{-1}^{1}Φ²) ,
```

so with `χ² → 1` the eigenvector half is exactly the single scalar asymptotic

```text
Φ(0)² √(π/c) / ∫_{-1}^{1}Φ²  →  1 ,          c = 2πλ² ,
```

whose value `√2` for `ℓ₀²` is the Gaussian one: the shape `(1−x²)^{c/2}` has `Φ(0) = 1` and
`∫Φ² = ∫(1−x²)^c ≈ √(π/c)`.  Note the shape is `(1−x²)^{c/2}`, not `e^{−cx²/2}`; the two agree to
leading order on the concentration scale, and the former is the exact solution of the mean-square
relation `(1−x²)Φ′ = −cxΦ` that `integral_prolateGaussianDefect_le` controls.

**2.  Cauchy--Schwarz is not enough, by a full power.**  From the band equation at the centre,
`Φ(0) ≤ ‖K_c(0,·)‖ ‖Φ‖ / χ²` with `‖K_c(0,·)‖² ≍ c/π`, giving only
`Φ(0)²/∫Φ² ≲ c/π` against the truth `≍ √(c/π)`.  So the sharp constant needs the actual profile,
not a norm bound: the mean-square shape estimate has to be converted into control of `Φ(0)²/∫Φ²`.

**The structural gap.**  The family produced by the variational principle
(`exists_ground_family`) consists of eigenfunctions of the *band* operator, `bandTransform c Φ =
λ Φ`.  The card's `ℓ_j` is defined through the *finite Fourier* eigen-equation, and it is that
equation — not the band one — which yields `∫e = χ e(0)`; the sinc kernel at the centre is
`sin(cy)/(πy)`, not a constant, so the band equation alone gives no evaluation identity.  Closing
the eigenvector half therefore needs the selected ground mode to be identified with a *signed*
Fourier mode, i.e. the square root of the band eigenvalue realized on the same eigenfunction.  The
corpus owns both spectra (`ConstrainedProlateSignedSpectrum`, `ProlateBandJointSpectrum`,
`ProlateJointEigen`); what is missing is the statement that the variationally selected band mode is
the signed mode of index `0`.

### The identification step, and the corpus asset for it

`SlepianKernelScaledFubini.bandEigenvalue_eq_of_same_even_prolate_eigen` — "a nontrivial regular
even separation mode cannot carry two different live band eigenvalues; one separation value
determines one band eigenline" — is exactly the injectivity needed: the separation constant pins the
band eigenline.  Since `bandwidthSeparation_ge` gives *every* mode `μ ≥ c/(c+3)` and
`exists_even_joint_prolate_eigen_bandwidth_separation_lt_one` gives *one* mode with `μ < 1`, that
mode's separation constant is pinned to `1`, and by the injectivity its band eigenline is determined.

What is still needed to call it the signed mode of index `0` is the *ordering*: that the smallest
separation constant goes with the largest band eigenvalue.  The corpus has both spectra
(`ConstrainedProlateSignedSpectrum`, `ProlateBandJointSpectrum`,
`ProlateJointEigenExistence.exists_joint_prolate_band_eigen`,
`SlepianKernelScaledFubini.exists_joint_even_prolate_band_eigen_of_signedMode`) and the antitonicity
of `|χ_n|` (`ProlateSignedLeakageOrdering.abs_sgVal_antitone`), but not the cross-monotonicity.  That
single statement — larger band eigenvalue ⟺ smaller separation constant, on the even joint spectrum —
is the last link between the variationally selected family and the card's indexed modes.

## Lean progress — the profile limit needs no construction: it is the Gaussian, explicitly

The plan recorded earlier called for building the limit profile as a `C¹` limit of the family.  That
is unnecessary at the first rung.  The limiting Hermite equation there is `v″ = (ξ² − 1)v`, whose
even solution with `v(0) = 1` is `e^{−ξ²/2}` — an explicit function.  So the Grönwall window
comparison can be run against it directly.

`HTGeometry/LinearSecondOrderComparison.lean` (extended, wired, axiom-clean):

```text
phasePair_dist_le_pair    Grönwall comparison of two *perturbed* equations
                          u″ = P_u u + Q_u u′  against  v″ = P_v v + Q_v v′
```

`RHTower/ProlateGaussianWindowLimit.lean` (wired, axiom-clean):

```text
gaussianProfile ξ = e^{−ξ²/2},  gaussianProfileDeriv ξ = −ξ e^{−ξ²/2}
hasDerivAt_gaussianProfile, hasDerivAt_gaussianProfileDeriv
    the second is exactly  v″ = hermiteRungP 0 · v ,  i.e.  v″ = (ξ² − 1)v
prolateProfile_window_gaussian_dist_le :
    max |u − e^{−ξ²/2}| |u′ + ξe^{−ξ²/2}|
      ≤ ((ε_P + ε_Q)·B / L)(exp(L·K) − 1)      on [0, K],
    ε_P = 2|μ − 1| + 2K²(K² + 1)/c ,  ε_Q = 4K/c
tendsto_prolateProfile_gaussian :
    μ_i → 1 and c_i → ∞  ⟹  u_i → e^{−ξ²/2}  pointwise on [0, K], with a uniform envelope
```

The hypotheses are exactly what is already proved: `μ_c → 1` is
`exists_tendsto_bandwidthSeparation_one` / `exists_ground_family`, the normal form and the
coefficient bounds are `ProlateRescaledCoefficients`, and the a priori phase bound `B` is
`prolateProfile_window_phase_le`.  What has to be supplied to instantiate is the normalization
`u(0) = 1`, `u′(0) = 0` — the first from `Φ(0) ≠ 0`
(`SlepianKernelScaledFubini.value_zero_ne_of_even_joint_prolate_band_eigen`), the second from
evenness.

## Lean progress — the centre-mass asymptotic is closed unconditionally

The scalar core of the eigenvector half is now a theorem.  Writing `u_c(ξ) = Φ_c(ξ/√c)/Φ_c(0)` for
the normalized rescaled profile of the variationally selected ground family, the total mass
`N(c) = ∫_{−√c}^{√c} u_c²` satisfies `N(c) → √π`, and since

`√(π/c)·Φ_c(0)² / ∫_{−1}^{1} Φ_c²  =  √π / N(c)` ,

the centre-mass ratio tends to `1`.

The route needs no compactness, no spectral theorem, and no uniform convergence on the whole line:
convergence on each fixed window plus a *bandwidth-uniform* Chebyshev tail bound already pins the
total.

New reusable infrastructure, all wired and axiom-clean.

`HTGeometry/WindowTotalSqueeze.lean`:

```text
tendsto_gaussianWindow          ∫_{−K}^{K} e^{−x²} → √π
window_le_total                 a symmetric window carries at most the total mass
window_tail_le_of_secondMoment  N − W_K ≤ K⁻² · (total second moment)          [Chebyshev]
tendsto_total_of_window         W_K ≤ N,  N(1 − M/K²) ≤ W_K,  W_K → G K,  G K → A
                                  ⟹  N → A                                     [squeeze]
```

`RHTower/ProlateNormalizedProfile.lean`:

```text
normalizedProlateProfile c Φ ξ = Φ(ξ/√c)/Φ(0),  with its first two derivatives
normalizedProlate_ode           the rescaled normal form on the window
normalizedProlate_window_package  all five window hypotheses discharged at once:
                                  global differentiability, the normal form,
                                  u(0) = 1 and u′(0) = 0
```

The two normalizations are exactly the two facts the corpus already owns: `Φ(0) ≠ 0` is
`value_zero_ne_of_even_joint_prolate_band_eigen`, and `u′(0) = 0` is `deriv_zero_of_even`.

`RHTower/ProlateWindowMass.lean`:

```text
gaussianProfile_sq              (e^{−ξ²/2})² = e^{−ξ²}
abs_sub_le_of_even_window       evenness transports a window estimate from [0,K] to [−K,K]
abs_sq_sub_le_of_window         squaring costs the factor B + 1
abs_windowMass_sub_le           |∫_{−K}^{K} u² − ∫_{−K}^{K} e^{−ξ²}| ≤ 2K(B+1)·E
```

`RHTower/ProlateGroundTotalMass.lean`:

```text
normalizedProlate_phase_le        a priori bound B = exp(max 1 (K²+3)·K), uniform in c
prolateWindowMassEnvelope         the full window-mass envelope, and its vanishing
prolateGround_windowMass_bound    |W_K(c) − G K| ≤ envelope
normalizedProlate_secondMoment_le the second moment survives normalization
normalizedProlate_chebyshev       N(c)(1 − 2/K²) ≤ W_K(c)
prolateCentreMassRatio_mul_totalMass   ratio · N = √π   (exact, not asymptotic)
tendsto_prolateGround_centreMass  √(π/c)·Φ_c(0)²/∫_{−1}^{1}Φ_c² → 1
```

What remains on this card is no longer analytic.  `tendsto_prolateGround_centreMass` is a statement
about the family produced by the variational selection, i.e. about *band* eigenfunctions; the
card's `ℓ_j` are indexed through the *finite Fourier* equation.  The missing link is the ordering
statement recorded above — larger band eigenvalue ⟺ smaller separation constant on the even joint
spectrum — which identifies the selected family with the signed mode of index `0`.

## Corpus audit — what the whole constrained-prolate lane actually still consumes

An audit of the formal tree against the three constrained-prolate cards and the CCM transfer tower
finds that the ℓ-side is nearly closed and locates the remaining input precisely.

Already unconditional in the tree (all `[propext, Classical.choice, Quot.sound]`):

```text
ConstrainedProlateBesselBound.lean
    tsum_evenProlateConstraintCoord_sq_le      Σ ℓ_j² ≤ 2a          [Bessel]
    summable_evenProlateConstraintCoord_sq
    evenProlate_bessel_eventually, evenProlate_summable_eventually
    tsum_evenProlateConstraintCoord_comp_sq_le the Bessel bound survives *any injective
                                               renumbering* of the modes
ConstrainedProlateBesselClockUniversalityLaw.lean
    ClockEnvelope.constrainedProlateBessel_exactEigenpair_and_allRawDefects
```

The last of these is the whole tower's entry point, and after the Bessel inputs it consumes exactly
one hypothesis:

```text
hl : ∀ j ≤ k+1,  ‖evenProlateConstraintCoord lam j‖ → constrainedProlateHermiteCoordinate j
```

So the card's square-summability and Bessel items are **done**, not open; the earlier note listing
them as open is superseded.

### The scalar content of `hl`, and why the centre-mass theorem is exactly it

`ℓ_j = χ_j·e_j(0)` with `e_j` normalized in `L²[−λ,λ]`, so `|ℓ_j| → |h_{2j}(0)|` is the statement
`e_j(0)² → h_{2j}(0)²`.  Writing `e(t) = NΦ(t/λ)` with `∫_{−λ}^{λ}e² = 1` gives `N² = 1/(λ∫_{−1}^{1}Φ²)`
and hence

```text
e(0)² = Φ(0)² / (λ ∫_{−1}^{1}Φ²) .
```

`tendsto_prolateGround_centreMass` says `√(π/c)·Φ(0)²/∫_{−1}^{1}Φ² → 1` with `c = 2πλ²`, i.e.
`Φ(0)²/∫Φ² → √(c/π) = λ√2`, so `e(0)² → √2`.  And `h_0(0)² = √2` in this Fourier convention
(`h_0(x) = 2^{1/4}e^{−πx²}`, `constrainedProlateHermiteCoordinate 0 = 2^{1/4}`, which
`CCMHypothesisDischarge` already evaluates).  The two agree exactly: **the centre-mass theorem is
`hl` at `j = 0`, up to the index identification.**

### The one remaining structural link, and why it is *not* total positivity

`evenProlateConstraintCoord a j` is built from `evenProlateSignedMode a j = sgVec`, the **greedy**
exhaustion of the band operator `PₐFPₐ` by `|⟨x,Sx⟩|`.  The analytic machine above produces modes
indexed by their **separation constant** `μ`.  Matching the two indexings is the classical
statement that the prolate integral operator and the prolate differential operator are ordered
oppositely, which classically rests on strict total positivity of the sinc kernel
(Gantmacher–Krein/Kellogg).  That has no mathlib counterpart and would be a project in itself.

**It is not on the critical path.**  `tsum_evenProlateConstraintCoord_comp_sq_le` proves the Bessel
bound for an arbitrary injective renumbering, and the clock tower consumes `ℓ` and `D` abstractly.
So the tower may be instantiated with *both* families re-indexed by separation order.  The CCM
conclusions are statements about the constrained ground state of an operator and do not depend on
how its eigenmodes are labelled.  Re-indexing therefore replaces "greedy order = differential order"
by:

```text
(α)  the differential ordering:   μ_j(c) → 4j+1  for the j-th even mode by separation order;
(β)  Fuchs asymptotics in that same order:  d_j(λ) ~ A_j λ^{4j+1} e^{−4πλ²}.
```

`(β)` is what the card's `(7)` already flags as external.  `(α)` is new work, and the route is
fixed by what the corpus now owns.

### Route to `(α)`

Lower half, already unconditional: the aperture virial `c ≤ μ(c+3)` holds for **every** mode
(`bandwidthSeparation_ge`), so `liminf μ ≥ 1` for every mode.

Upper half: a `(j+1)`-dimensional trial space of rescaled Hermite functions has prolate Rayleigh
numerator above `−(4j+1+ε)c` times its aperture norm, for large `c`.  Feeding it into a *multi-mode*
version of the variational extraction gives `j+1` linearly independent joint modes with
`μ < 4j+1+ε`.

The single-trial extraction is now general:

```text
ProlateGeneralTrialMode.exists_even_joint_prolate_eigen_gt_of_trial
    any smooth even trial function with prolate Rayleigh numerator above −K·‖g‖²
    produces an even joint band/prolate mode with prolate eigenvalue above −K
```

(The Gaussian-specific hypothesis is gone; only `ContDiff` and `Function.Even` are used.)  A single
trial function is not enough — it only reproves `μ < 1`, which is already known.  What the multi-mode
version needs, and what is the actual next construction, is the dimension count: if the joint modes
with `η > −K` spanned a space `W` of dimension `≤ j`, then a nonzero `g ∈ V ∩ W^⊥` would have every
band component orthogonal to `W`, so on each even band eigenspace the prolate operator would have
all eigenvalues `≤ −K` on the relevant complement, and summing the per-eigenvalue estimate would
contradict the trial bound.

Finally, `μ_j → 4j+1` exactly (rather than `≤`) follows from the rung rigidity
`OscillatorSpectralRigidity.exists_rung_of_integrable` — an `L²` solution of `v″ = (ξ²−μ)v` forces
`μ = 2n+1` — together with the window limits, which now exist at **every** rung:

```text
ProlateHermiteRungWindowLimit.lean   (wired, axiom-clean)
    hasDerivAt_deriv_hermiteFun          φ_n″ = (ξ² − (2n+1))φ_n in the window normal form
    even_hermiteFun, deriv_hermiteFun_zero_of_even
    prolateProfile_window_hermiteRung_dist_le
    tendsto_prolateProfile_hermiteRung   μ → 2n+1, c → ∞  ⟹  u → φ_n on [0,K]
```

The limit profiles need no construction at any rung: the corpus's `hermiteFun n` already solves the
rung equation exactly, and the Gaussian case is `hermiteFun 0`.

## Lean progress — the multi-mode variational machinery, and Hermite orthogonality

Two blocks of the route to `(α)` are now built, wired, and axiom-clean.

### 1. The relative variational bound and the dimension count

The absolute extraction theorem (a trial function with prolate form above `−K` yields a mode with
eigenvalue above `−K`) is not enough for a count: one trial function only reproves `μ < 1`.  What a
count needs is the *relative* statement, and it is now proved.

`RHTower/ProlateEvenEigenspaceRelativeBound.lean`:

```text
prolate_form_le_of_orthogonal_high
    on an even band eigenspace, a vector orthogonal to every prolate eigenvector with
    eigenvalue above −K has prolate form ≤ −K‖·‖²
```

`RHTower/ProlateRelativeTrialBound.lean`:

```text
IsHighProlateMode c K Phi          a joint even band/prolate mode with eigenvalue above −K
exists_mode_of_evenEigenspace_eigenvector
    a nonzero prolate eigenvector of an even band eigenspace *is* the band class of a genuine
    smooth even joint mode with the same eigenvalue        [reconstruction]
prolate_trial_le_of_orthogonal_high
    a smooth even trial function orthogonal on the aperture to every high mode has
    ∫L_c g·g ≤ −K∫g²
highProlateSpan c K                the span of the band classes of all high modes
bandClass_notMem_orthogonal_highProlateSpan
    a live trial function is not orthogonal to that span
disjoint_trialSpace_orthogonal_highProlateSpan
    a whole trial subspace meets the span's orthogonal complement only in zero
rank_trialSpace_le_highProlateSpan
    hence orthogonal projection onto the span is injective on the trial space:
    rank(trial space) ≤ rank(high-mode span)
```

That is the dimension count in full.  What remains for `(α)`'s upper half is the *analytic* input:
an explicit `(j+1)`-dimensional trial space whose prolate Rayleigh quotient stays below `4j+1+ε`.

### 2. Hermite function orthogonality — exact, with the truncation error included

Mathlib carries the Hermite *polynomials* but no analysis of the Hermite *functions*.  The trial
space is spanned by rescaled Hermite functions, so their orthogonality and window masses had to be
built.  The mechanism is a Wronskian, in the same style as the oscillator rigidity chain:

`RHTower/HermiteFunctionOrthogonality.lean` (wired, axiom-clean):

```text
tendsto_polyEval_mul_gauss_atTop/atBot     polynomials lose to a Gaussian at both ends
tendsto_hermiteFun_atTop/atBot             φ_n → 0
tendsto_deriv_hermiteFun_atTop/atBot       φ_n′ → 0
hermiteWronskian m n = φ_m′φ_n − φ_mφ_n′
hasDerivAt_hermiteWronskian                W′ = 2(n − m)·φ_mφ_n
integral_hermiteFun_mul_eq                 ∫_a^b φ_mφ_n = (W(b) − W(a))/(2(n − m))
tendsto_integral_hermiteFun_mul            ∫_{−R}^{R} φ_mφ_n → 0
exists_hermiteFun_ne_zero                  φ_n vanishes on no interval  (hermite n is monic)
integral_hermiteFun_sq_pos                 ∫_a^b φ_n² > 0 on every nondegenerate window
```

The orthogonality identity is **exact**, not asymptotic: it *is* the truncation error, so no
estimate of Hermite tails is needed anywhere downstream.  Together with the decay of `φ_n` and
`φ_n′` this gives everything the almost-orthogonality argument for the trial space needs — the
off-diagonal Gram entries vanish, the boundary terms vanish, and the diagonal entries are bounded
below.

## Lean progress — the trial-space toolkit

The remaining analytic input for `(α)` is an explicit `(j+1)`-dimensional trial space whose prolate
Rayleigh quotient stays below `4j+1+ε`.  The tools it needs are now built, wired, and axiom-clean.

`RHTower/ProlateRayleighForm.lean` — the form the extraction theorem actually tests:

```text
integral_prolateSLAction_mul_self
    ∫_{−1}^{1}(P_c f)·f  =  −( ∫(1−y²)f′² + c²∫y²f² )        [no boundary condition]
prolate_trial_gt_iff
    Rayleigh numerator above −K·‖f‖²   ⟺   Dirichlet-plus-potential energy below K·‖f‖²
```

The identity is unconditional because the Sturm–Liouville flux `(1−y²)f′` vanishes at `±1` on its
own; it converts every trial estimate into a positive-energy computation.

`RHTower/HermiteGaussianEnvelope.lean` — every Hermite object is a polynomial times a Gaussian:

```text
exists_bound_polyEval_mul_gauss    a polynomial times a Gaussian is bounded on the line
integrable_polyEval_mul_gauss      ... and absolutely integrable
exists_poly_hermiteFun             φ_n(ξ) = p(ξ)·e^{−ξ²/2}   with p explicit
exists_poly_deriv_hermiteFun       φ_n′(ξ) = p(ξ)·e^{−ξ²/2}  with p explicit
abs_intervalIntegral_le_integral_abs
exists_uniform_bound_of_gaussEnvelope
    all truncated integrals of such a function are bounded by one constant,
    independent of the truncation
```

The last is what makes the trial computation uniform in the bandwidth: after rescaling, the window
is `[−√c, √c]`, and the two `O(1)` correction integrals of the rescaled prolate action — the
`ξ²(ξ²−2n−1)φ_mφ_n` term and the `ξφ_m′φ_n` term — are bounded by constants that do not move with
`c`, so they are `O(1/c)` against the `c`-sized main term.  The only analytic input in the whole
chain is that a continuous function tending to zero at both ends of the line is bounded.

What is left to assemble for `(α)`'s upper half is bookkeeping of a fixed shape: expand the
Dirichlet-plus-potential energy of `g = Σa_iΦ_{2i}` (with `Φ_n(x) = φ_n(√c x)`) over the Gram
matrix, use `integral_hermiteFun_mul_eq` for the off-diagonal entries and
`integral_hermiteFun_sq_pos` for the diagonal, and feed the result to
`rank_trialSpace_le_highProlateSpan`.

## Lean progress — the trial space is built and proved live

The Gram-matrix bookkeeping recorded above as "left to assemble" is now done.  All five modules are
wired and axiom-clean.

`HTGeometry/GramFormPositivity.lean` — the finite-dimensional core, stated once and for all:

```text
gramForm_pos_of_bounds
    diagonal entries ≥ e > 0,  off-diagonal entries ≤ θ,  perturbation entries ≤ C,
    θ(j+1) ≤ e/2  and  C(j+1) < c·e/2
      ⟹  0 < c·Σ a_i a_k Gw_{ik} + Σ a_i a_k Cr_{ik}   for every nonzero a
```

`RHTower/ProlateActionLinear.lean` — the prolate action is a linear differential operator:

```text
prolateSLAction_finsetSum              P_c(Σ a_i F_i) = Σ a_i·P_c F_i, through HasDerivAt families
integral_prolateSLAction_finsetSum_mul the Rayleigh numerator of a combination is the Gram double sum
integral_finsetSum_mul_finsetSum       and so is the squared aperture norm
```

`RHTower/ProlateHermiteTrialFamily.lean` — the family `Φ_n^c(x) = φ_n(√c·x)` with its first two
derivatives as explicit functions, its exact prolate action

```text
(1−x²)Φ_n″ − 2xΦ_n′ − c²x²Φ_n
  = −c(2n+1)(1−x²)φ_n(√c x) − c²x⁴φ_n(√c x) − 2√c·x·φ_n′(√c x)
```

and the change of variables `integral_comp_sqrt_mul` to the Hermite scale.

`RHTower/ProlateHermiteTrialEstimate.lean` — the bandwidth split:

```text
sqrt_mul_integral_trialPair_numerator
    √c·N_{mn}(c) = −c(2m+1)·∫_{−√c}^{√c}φ_mφ_n + ∫_{−√c}^{√c}(correction)
exists_bound_hermiteCorrection
    the correction integral is bounded by a constant independent of the bandwidth
```

`RHTower/ProlateHermiteTrialSpace.lean` — the payoff:

```text
hermiteTrialGram / hermiteTrialCorr / hermiteTrialVector
sqrt_mul_hermiteTrial_norm, sqrt_mul_hermiteTrial_numerator
hermiteTrialGram_diag_ge      diagonal entries ≥ the fixed unit-window masses ∫_{−1}^{1}φ_n²
tendsto_hermiteTrialGram_off  off-diagonal entries → 0                    [Wronskian]
exists_bound_hermiteTrialCorr corrections bounded uniformly in bandwidth and index pair
eventually_hermiteTrial_rayleigh_gt
    for distinct rungs with 2ν_i+1 ≤ Λ and any ε > 0, eventually in c, every nonzero
    trial vector g satisfies   −(Λ+ε)c·∫g² < ∫(P_c g)·g
eventually_hermiteTrial_norm_pos
    and every nonzero coefficient vector has ∫g² > 0, so the family is genuinely
    (j+1)-dimensional on the aperture
```

Taking `ν i = 2i` and `Λ = 4j+1` gives a `(j+1)`-dimensional trial space of **even** smooth
functions whose prolate Rayleigh quotient stays below `4j+1+ε` at every large bandwidth.  That is
exactly the analytic hypothesis of `rank_trialSpace_le_highProlateSpan`, so the upper half of `(α)`
now reduces to a purely formal step: transporting the trial space into `RealIntervalL2 (-1) 1`
through `bandClass` (linearity of `bandClass` over a finite sum, plus smoothness and evenness of
`Φ_{2i}^c`), and reading off

```text
j + 1  ≤  rank (highProlateSpan c ((4j+1+ε)·c))    for every large c,
```

i.e. at every large bandwidth there are at least `j+1` independent even joint modes with separation
constant below `4j+1+ε`.

## Lean progress — `(α)`'s upper half is closed

The transport step is done, and with it the upper half of the differential ordering.

`RHTower/ProlateTrialSpaceTransport.lean` (wired, axiom-clean):

```text
contDiff_polyEval, contDiff_hermiteFun, contDiff_prolateHermiteTrial
even_prolateHermiteTrial          Φ_n^c is even at even rungs
contDiff_hermiteTrialVector, even_hermiteTrialVector
bandClass_finsetSum               the band class is linear over a finite combination
bandClass_hermiteTrialVector
hermiteTrialSpan                  the band-class span of the trial family
eventually_disjoint_hermiteTrialSpan
    the trial span meets (highProlateSpan c ((Λ+ε)c))ᗮ only in zero
eventually_linearIndependent_hermiteTrialBasis
eventually_rank_hermiteTrialSpan_eq       rank (trial span) = j+1
eventually_rank_highProlateSpan_ge        j+1 ≤ rank (highProlateSpan c ((Λ+ε)c))
eventually_rank_highProlateSpan_even_ge   the even sector, ν i = 2i, Λ = 4j+1
```

`RHTower/ProlateRelativeTrialBound.lean` gained the reusable half of the count:

```text
rank_le_of_disjoint_orthogonal
    Disjoint V (highProlateSpan c K)ᗮ  ⟹  rank V ≤ rank (highProlateSpan c K)
```

So, unconditionally: **for every `j` and every `ε > 0`, at every large bandwidth the joint even
band/prolate modes with separation constant below `4j+1+ε` span a space of rank at least `j+1`.**

That is `(α)`'s upper half in full.  Combined with the aperture virial `c ≤ μ(c+3)`
(`bandwidthSeparation_ge`), which gives `liminf μ ≥ 1` for *every* mode, the separation spectrum is
now pinned from one side at every rung.

What `(α)` still needs is the matching *upper* count — that at most `j+1` independent even modes
have separation below `4j+3−ε` — which is the reverse min–max, and then the rung rigidity
`OscillatorSpectralRigidity.exists_rung_of_integrable` to convert the two counts into
`μ_j(c) → 4j+1`.  After that only `(β)`, the Fuchs asymptotics, remains on the ℓ-side.

## Lean progress — the limit profile at an arbitrary separation constant

The construction I had deferred by working only at rungs is now built, and it rests on a piece of
general theory that mathlib does not carry.

`HTGeometry/LinearSecondOrderExistence.lean` (wired, axiom-clean) — **global existence for the
linear second-order initial value problem**:

```text
secondOrderKernel / secondOrderFree / secondOrderSolution / secondOrderDeriv
secondOrderSolution_volterra   v(ξ) = α + βξ + ∫₀^ξ (ξ−t)P(t)v(t)dt
hasDerivAt_secondOrderSolution
hasDerivAt_secondOrderDeriv    v″ = P·v
exists_secondOrder_solution
    for continuous P and any (α, β) there are v, v′ on all of ℝ with
    v(0)=α, v′(0)=β, v′ = derivative of v, and v″ = P·v
```

mathlib has Picard–Lindelöf, which is local, and no global statement even for a linear equation.
The corpus's own Volterra solver (`VolterraLinearIntegralEquation`,
`VolterraWindowedEquation`) supplies the Picard series with locally bounded data; the Volterra
kernel `(ξ−t)P(t)` of the second-order problem is exactly of that type, and differentiating the
Volterra form twice — the inner `ξ` splits off as `ξ∫₀^ξ Pv − ∫₀^ξ tPv`, and the two boundary
contributions cancel — returns the differential equation.

`RHTower/ProlateOscProfileLimit.lean` (wired, axiom-clean):

```text
oscPotential mu ξ = ξ² − μ
oscProfile mu, oscProfileDeriv mu     the solution with v(0)=1, v′(0)=0, for *any* real μ
abs_rescaledProlateP_sub_oscPotential_le
    |c(ξ²−μ)/(c−ξ²) − (ξ²−m)| ≤ 2K²(K²+|μ|)/c + |μ−m|   on |ξ| ≤ K, 2K² ≤ c
prolateProfile_window_osc_dist_le     the Grönwall window comparison, no rung assumption
tendsto_prolateProfile_oscProfile
    μ_i → m (any real m) and c_i → ∞  ⟹  u_i → oscProfile m  on every window
```

This removes the last structural obstruction on the route to `(α)`'s lower half.  The argument it
unlocks needs no completeness of the Hermite system and no reverse min–max:

- `j+1` orthogonal even modes with separation constants bounded above have, along a subsequence,
  convergent separation constants `m_0, …, m_j`;
- each normalized profile converges on windows to `oscProfile m_i`;
- the second-moment bound `∫ξ²u² ≤ μ∫u²` passes to the limit, so each `oscProfile m_i` is square
  integrable, and `OscillatorSpectralRigidity.exists_rung_of_integrable` forces `m_i = 2n_i+1`;
- evenness forces `n_i` even, so `m_i ∈ {1, 5, 9, …}`;
- orthogonality passes to the limit, so the `m_i` are distinct;
- but `{1, 5, …}` has only `j` elements below `4j+1`, so not all `j+1` can lie there.

That is the counting contradiction that gives `liminf μ_j ≥ 4j+1`, matching the upper half already
proved.

## Lean progress — the limit-passage toolkit for `(α)`'s lower half

The three passages the counting argument needs are now built, wired, and axiom-clean.

`HTGeometry/LinearSecondOrderUnique.lean` — **uniqueness for the linear second-order problem**:

```text
secondOrder_eq_of_nonneg   uniqueness on the nonnegative half-line (Grönwall with zero defect)
secondOrder_eq             two solutions of w″ = P·w with the same initial phase vector coincide
```

The negative half comes from reflecting the time variable, which turns the equation into the one
with reflected coefficient.  Together with the existence theorem this makes the initial value
problem well posed on the line — neither half is in mathlib.

`HTGeometry/WindowTotalSqueeze.lean` gained the pairing tail bound:

```text
abs_window_pairing_sub_le_of_secondMoment
    |∫_{−R}^{R} fg − ∫_{−K}^{K} fg| ≤ (2K²)⁻¹(∫_{−R}^{R}x²f² + ∫_{−R}^{R}x²g²)
```

using only `|fg| ≤ (f²+g²)/2` — no Cauchy–Schwarz.  This is what converts orthogonality on the full
rescaled window into approximate orthogonality on a fixed window.

`HTGeometry/WindowProductLimit.lean`:

```text
abs_intervalIntegral_product_sub_le    fg − vw = f(g−w) + (f−v)w, so the defect is ≤ E(B+C)
tendsto_intervalIntegral_product       uniform convergence on a window ⟹ pairings converge
```

`HTGeometry/ContinuousSquareIntegralPositive.lean`:

```text
integral_sq_pos_of_ne_zero    a continuous function nonzero strictly inside an interval has
                              positive square mass there
```

`RHTower/ProlateOscProfileLimit.lean` gained the consequences for the limit profile:

```text
continuous_oscProfile, continuous_oscProfileDeriv
integral_oscProfile_sq_pos, integral_oscProfile_mul_self_pos
    ∫_{−K}^{K}(oscProfile μ)² > 0 on every window, since the profile is one at the centre
eq_oscProfile
    any solution of v″ = (ξ²−μ)v with v(0)=1, v′(0)=0 *is* oscProfile μ
```

With these, the distinctness step of the counting argument is a two-line contradiction: if two
orthogonal mode families had separation constants converging to the same `m`, both window profiles
would converge to `oscProfile m`, so their window pairings would converge to
`∫_{−K}^{K}(oscProfile m)² > 0`; but the pairing tail bound forces those pairings to be `O(K^{-2})`,
which is smaller for large `K`.

What remains to assemble for `(α)`'s lower half is the mode-family bookkeeping: extracting `j+1`
orthogonal even modes from the rank bound already proved, choosing a subsequence along which all
`j+1` separation constants converge (they lie in a fixed compact interval), and reading off the
rung of each limit through `OscillatorSpectralRigidity.exists_rung_of_integrable`.

## Lean progress — the distinctness core of `(α)`'s lower half

The contradiction that the counting argument turns on is now a theorem, stated so that it can be
instantiated by any two mode families.

`HTGeometry/WindowProductLimit.lean`:

```text
false_of_orthogonal_same_limit
    if the window pairings of two families converge to the window mass of a *common* limit
    profile, while approximate orthogonality forces those pairings to be O(K^{-2}),
    then the limit profile has vanishing window mass — contradicting positivity
```

The proof is three lines of filter reasoning: `le_of_tendsto` transports the eventual bound
`|∫_{−K}^{K} f_i g_i| ≤ C/K²` to the limit, monotonicity of the window mass keeps it above the fixed
`δ = ∫_{−1}^{1}v²`, and `C/K² → 0` closes it.

`RHTower/ProlateOscProfileLimit.lean` supplies the two prolate-side inputs:

```text
integral_oscProfile_mul_self_mono        the window mass of oscProfile grows with the window
tendsto_prolateProfile_oscProfile_eventually
    convergence to the limit profile under *eventual* hypotheses, so only the behaviour of the
    family along the filter matters — which is what a bandwidth-indexed family supplies
```

So the distinctness step is closed as a reusable lemma: **two orthogonal even mode families whose
separation constants converge to the same limit is impossible.**  Both profiles would converge on
every window to `oscProfile m`, so their pairings converge to `∫_{−K}^{K}(oscProfile m)² > 0`, while
the tail bound `abs_window_pairing_sub_le_of_secondMoment` together with exact orthogonality on the
rescaled window forces those pairings to be `O(K^{-2})`.

What `(α)`'s lower half still needs is the finite-family bookkeeping around this core: extracting
`j+1` orthogonal even modes at each bandwidth, choosing a subsequence along which all `j+1`
separation constants converge (they lie in a fixed compact interval, so Bolzano–Weierstrass applies
`j+1` times), applying the distinctness lemma to each pair, and reading each limit's rung off
`OscillatorSpectralRigidity.exists_rung_of_integrable`.  Only `j` even rungs lie below `4j+1`, so
`j+1` distinct ones cannot.

## Lean progress — simultaneous limits, profile parity, and the Wronskian

Three more pieces of the `(α)` assembly, all wired and axiom-clean.

`HTGeometry/UltrafilterFamilyLimit.lean` — the subsequence step, without subsequences:

```text
exists_ultrafilter_tendsto_of_eventually_bounded
    refining a filter to an ultrafilter makes *every* member of an arbitrary family of eventually
    bounded real functions converge at once
```

A closed bounded interval is compact, so a bounded family converges along any ultrafilter.  This
replaces the `j+1`-fold Bolzano–Weierstrass extraction of the counting argument with a single
refinement, with no diagonal argument and no countability hypothesis.

`RHTower/ProlateOscProfileLimit.lean`:

```text
even_oscProfile     the limit profile is even, for every μ
```

proved by uniqueness: reflecting the variable gives a solution of the same equation with the same
initial phase vector.

`HTGeometry/LinearSecondOrderUnique.lean`:

```text
secondOrderWronskian, hasDerivAt_secondOrderWronskian
secondOrderWronskian_const               the Wronskian of two solutions of w″ = P·w is constant
secondOrder_eq_smul_of_wronskian_zero    vanishing Wronskian ⟹ the solutions are proportional
```

These close the parity step of the counting argument.  `oscProfile μ` is even for every `μ`, so if it
is square integrable, rung rigidity gives `μ = 2n+1`; were `n` odd, the square-integrable solution at
that rung would be the odd Hermite function, and proportionality via the Wronskian would force
`oscProfile μ (0) = 0`, contradicting `oscProfile μ (0) = 1`.  Hence `n` is even and `μ ∈ {1,5,9,…}`,
which is what the count `j+1 > j` needs.

## Lean progress — the rung of a square-integrable limit profile

The rigidity step of the counting argument is now a theorem about the limit profile itself, with no
side hypothesis left to discharge.

`HTGeometry/LinearSecondOrderUnique.lean`:

```text
secondOrder_eq_at    uniqueness at an arbitrary base point, by translating the variable
```

`RHTower/ProlateOscProfileLimit.lean`:

```text
oscProfile_nontrivial
    the limit profile's value and derivative never vanish together — uniqueness at that point
    would force it identically zero, contradicting oscProfile μ (0) = 1
exists_rung_of_integrable_oscProfile
    square integrability of oscProfile μ alone forces  μ = 2n+1
```

The second is the clean form of the rigidity input: `OscillatorSpectralRigidity.exists_rung_of_integrable`
asks for a nondegeneracy hypothesis, and for the limit profile that hypothesis is now proved rather
than assumed, so the theorem reads with square integrability as its only premise.

### State of `(α)`

```text
upper half   eventually_rank_highProlateSpan_even_ge          proved
lower half   pieces:
  simultaneous limits          exists_ultrafilter_tendsto_of_eventually_bounded   proved
  limit profile                tendsto_prolateProfile_oscProfile(_eventually)     proved
  distinctness                 false_of_orthogonal_same_limit                     proved
  rung of the limit            exists_rung_of_integrable_oscProfile               proved
  parity of the rung           needs one-dimensionality of the L² solution space
  square integrability of the limit                                              open
```

The two remaining items are of the same kind — both follow from decay of a square-integrable
solution and its derivative at infinity, which `OscillatorRecessiveLimits` proves under sign
hypotheses that the rigidity proof establishes internally but does not export.  Exposing that decay
is the next construction: it gives square integrability of the limit by Fatou against the
second-moment bound, and it gives the parity of the rung through the vanishing of the Wronskian
against the Hermite function, using `secondOrderWronskian_const` and
`secondOrder_eq_smul_of_wronskian_zero`.

## Lean progress — the energy of a square-integrable solution vanishes

`HTGeometry/OscillatorEnergyVanishing.lean` (wired, axiom-clean):

```text
tendsto_oscillatorMonotoneEnergy_zero
    for a square-integrable solution of v″ = (ξ²−μ)v past the turning point,
    E = v′² − (ξ²−μ)v²  →  0
```

The proof is the one the corpus's own energy lemmas set up.  `E` is nonincreasing past the turning
point (`antitoneOn_oscillatorMonotoneEnergy`) and nonnegative there
(`oscillatorMonotoneEnergy_nonneg_of_integrableOn`), so it suffices to find a single point where it
is below any given `b > 0`.  If there were none, `v′² ≥ b` from the turning point on, so `v′` is
continuous and nowhere zero, hence of one sign (`sign_locally_const_of_ne_zero`), and the
fundamental theorem of calculus gives `|v(x) − v(a)| ≥ √b·(x−a)`.  Then `v² ≥ 1` from some point on,
which `not_integrableOn_Ici_of_le` forbids.

This is the decay statement the two remaining items of `(α)`'s lower half both reduce to: it says
the solution settles onto the balance `v′² = (ξ²−μ)v²` rather than keeping a residue of kinetic
energy.  With it, `v′` and `ξv` are controlled by each other at infinity, which is what square
integrability of the limit profile (via Fatou against the second-moment bound) and the vanishing of
the cross-Wronskian against the Hermite function (hence the parity of the rung) each need.

## Lean progress — the windowed virial identity

`HTGeometry/OscillatorVirialWindow.lean` (wired, axiom-clean):

```text
hasDerivAt_mulSq              (ξ·v²)′ = v² + 2ξvv′
integral_oscLower_sq_virial
    ∫_a^b (Av)² = ∫_a^b v′² + ∫_a^b ξ²v² − ∫_a^b v² + [ξv²]_a^b      with  Av = v′ + ξv
```

Exact on every window, with no hypothesis beyond differentiability: the cross term integrates by
parts on the nose, because `2ξvv′ = (ξv²)′ − v²`.

This is the identity that converts square integrability of `v` and of `Av` into square
integrability of `v′` and of `ξv`.  The corpus already supplies both inputs for a genuine mode —
`integrable_oscLower_sq` gives `Av ∈ L²`, and `tendsto_oscBoundary_atTop_zero` together with
`tendsto_oscProduct_zero` sends the boundary term `ξv²` to zero at both ends — so the right-hand
side stays bounded as the window grows, and the left-hand side is a nondecreasing window integral of
a nonnegative function.  Hence

```text
∫_ℝ v′² + ∫_ℝ ξ²v²  =  μ ∫_ℝ v²  <  ∞ .
```

With `v′` and `ξv` square integrable for every mode, the cross-Wronskian `W = v′w − vw′` of two
modes is a product of square-integrable factors, hence integrable on the line; being constant, it
must vanish.  That is the one-dimensionality of the `L²` solution space, and with it the parity of
the rung — the last of the two open items in `(α)`'s lower half, the other (square integrability of
the limit profile) following from the same bound by Fatou.

## Lean progress — integrability from bounded window masses

`HTGeometry/IntegrableOfBoundedWindows.lean` (wired, axiom-clean):

```text
integrable_of_bounded_windows
    a nonnegative continuous function whose masses over the symmetric windows [−n, n] are
    bounded by one constant is integrable on the line
```

Proved by monotone convergence on the indicators of the windows: they increase pointwise to the
integrand, `lintegral_iSup` identifies the total lower integral with the supremum of the window
masses, and `ofReal_integral_eq_lintegral_ofReal` converts each window mass to the bound.

This is the last generic tool the `(α)` lower half needed.  Together with the windowed virial
identity it gives, for a genuine mode,

```text
∫_ℝ v′²  and  ∫_ℝ ξ²v²   both finite,
```

because the right-hand side of `integral_oscLower_sq_virial` is bounded uniformly in the window —
`integrable_oscLower_sq` bounds `∫(Av)²`, square integrability bounds `∫v²`, and
`tendsto_oscBoundary_atTop_zero` with `tendsto_oscProduct_zero` sends the boundary term to zero —
while the left-hand side is a nondecreasing window integral of a nonnegative continuous function.

With `v′` and `ξv` square integrable, the two open items of `(α)`'s lower half both follow: the
cross-Wronskian of two modes is a product of square-integrable factors, hence integrable, hence
(being constant) zero — giving one-dimensionality of the `L²` solution space and so the parity of
the rung; and the same uniform bound gives square integrability of the limit profile by Fatou.

## Lean progress — kinetic energy and second moment of a mode are integrable

`HTGeometry/OscillatorKineticIntegrable.lean` (wired, axiom-clean):

```text
integrable_kinetic_add_moment
    for a nontrivial square-integrable solution of v″ = (ξ²−μ)v,
    v′² + ξ²v²  is integrable on the line
```

The proof needed no decay estimate in the end.  The windowed virial identity gives

```text
∫_{−n}^{n} v′² + ∫_{−n}^{n} ξ²v²
  = ∫_{−n}^{n}(Av)² + ∫_{−n}^{n} v² − n(v(n)² + v(−n)²) ,
```

and the boundary term enters *subtracted with a favourable sign*: it is nonnegative, so it is simply
dropped.  The two remaining window masses are bounded by the total masses of `(Av)²` — finite by
`integrable_oscLower_sq` — and of `v²`.  So the window masses of `v′² + ξ²v²` are bounded by one
constant, and `integrable_of_bounded_windows` concludes.

This supersedes the plan recorded above, which routed the same conclusion through
`tendsto_oscillatorMonotoneEnergy_zero` and the vanishing of the boundary term.  That route works
too, but the sign of the boundary term makes it unnecessary: no limit is taken anywhere in this
proof.

With `v′` and `ξv` square integrable for every mode, the cross-Wronskian `W = v′w − vw′` of two
modes is a sum of products of square-integrable factors, hence integrable on the line; being
constant (`secondOrderWronskian_const`), it is zero.  That is one-dimensionality of the `L²`
solution space, and with `secondOrder_eq_smul_of_wronskian_zero` it gives the parity of the rung.

## Lean progress — the square-integrable solution space is at most one dimensional

`HTGeometry/OscillatorSolutionSpaceRank.lean` (wired, axiom-clean):

```text
integrable_of_add_nonneg      a summand of an integrable sum of nonnegative terms is integrable
integrable_mul_of_sq          a product of two square-integrable functions is integrable,
                              by |fg| ≤ (f²+g²)/2 — no Hölder needed
secondOrderWronskian_eq_zero_of_integrable
    for two square-integrable modes at the same rung, the cross-Wronskian vanishes identically
eq_smul_of_integrable
    hence the two are proportional, as soon as one does not vanish at the origin
```

The Wronskian argument in full: `v′` and `w′` are square integrable by
`integrable_kinetic_add_moment`, so `v′w` and `vw′` are integrable, so `W = v′w − vw′` is integrable;
but `W` is constant (`secondOrderWronskian_const`), and a nonzero constant is not integrable on a
line of infinite measure.  Hence `W ≡ 0`, and `secondOrder_eq_smul_of_wronskian_zero` gives
proportionality.

**This closes the parity item.**  `oscProfile μ` is even for every `μ` and equals one at the origin.
If it is square integrable, `exists_rung_of_integrable_oscProfile` gives `μ = 2n+1`; the Hermite
function `hermiteFun n` is a square-integrable solution at the same rung, so by `eq_smul_of_integrable`
the two are proportional; `hermiteFun n` is odd for odd `n`, hence vanishes at the origin, which would
force `oscProfile μ (0) = 0`.  So `n` is even and `μ ∈ {1, 5, 9, …}` — exactly the ladder the count
`j+1 > j` needs.

`(α)`'s lower half now has a single item left: square integrability of the limit profile itself,
which follows from the same window bound by Fatou against the second-moment estimate that the
prolate modes already satisfy.

## Lean progress — `(α)`'s lower half is complete as a toolkit

`HTGeometry/SquareIntegrableOfWindowLimits.lean` (wired, axiom-clean):

```text
integrable_sq_of_bounded_window_limits
    if the window masses of a family are bounded by one constant and converge to the window
    masses of a limit function, the limit is square integrable
```

No Fatou lemma is needed: the bound passes to the limit by `le_of_tendsto`, and
`integrable_of_bounded_windows` does the rest.

### Every piece of `(α)` is now proved

```text
upper half
  eventually_rank_highProlateSpan_even_ge        at least j+1 independent even modes with μ < 4j+1+ε

lower half
  exists_ultrafilter_tendsto_of_eventually_bounded   simultaneous limits of the separation constants
  tendsto_prolateProfile_oscProfile(_eventually)     each profile converges to oscProfile of its limit
  integrable_sq_of_bounded_window_limits             each limit profile is square integrable
  exists_rung_of_integrable_oscProfile               hence its separation constant is 2n+1
  eq_smul_of_integrable                              the L² solution space at a rung is one dimensional
  even_oscProfile + odd Hermite at odd rungs         hence n is even and μ ∈ {1, 5, 9, …}
  false_of_orthogonal_same_limit                     distinct modes have distinct limits
```

and the count closes: `{1, 5, …}` has exactly `j` elements below `4j+1`, so `j+1` distinct limits
cannot all lie there.  Every one of these is unconditional and axiom-clean.

What is left is not mathematics but instantiation: feeding the `j+1` modes produced by the upper
half into the ultrafilter, checking the window hypotheses of the limit theorem for that particular
family (normalization at the origin, the a priori phase bound, the rescaled normal form — all of
which `ProlateNormalizedProfile` and `ProlateHermiteTrialSpace` already supply for a single mode),
and reading off the contradiction.  The mathematical content of `(α)` is closed.

## Lean progress — the card's named classical rigidity input is now a theorem

The statement this card records as "one classical rigidity statement" still missing —

```text
if v ∈ L²(ℝ) is even and solves v″ = (ξ²−μ)v on all of ℝ, then μ = 2n+1 for some even n,
and v is a multiple of the corresponding Hermite function
```

— is proved, unconditionally and axiom-clean, as

```text
RHTower/OscillatorEvenRigidity.even_integrable_solution_rung
```

Its supporting pieces, in the same module:

```text
aeval_hermite_neg_of_odd, odd_hermiteFun    the Hermite function of odd index is odd
integrable_hermiteFun_sq                    the Hermite function is square integrable
hermiteFun_nontrivial                       its value and derivative never vanish together
```

The proof runs through the chain built for this card:

- `OscillatorSpectralRigidity.exists_rung_of_integrable` puts `μ` on the ladder, `μ = 2n+1`;
- an even nontrivial solution cannot vanish at the origin, since evenness would kill its derivative
  there too;
- `OscillatorSolutionSpaceRank.eq_smul_of_integrable` — the square-integrable solution space at a
  rung is one dimensional, proved from the vanishing of the cross-Wronskian — makes `hermiteFun n`
  a multiple of `v`;
- if `n` were odd, `hermiteFun n` would be odd while `v` is even, forcing `hermiteFun n ≡ 0`, which
  `exists_hermiteFun_ne_zero` forbids.  So `n` is even.

The one-dimensionality step is where the real work was: `integrable_kinetic_add_moment` makes `v′`
and `ξv` square integrable (via the windowed virial identity, whose boundary term carries a
favourable sign), so the cross-Wronskian is integrable; being constant on a line of infinite
measure, it vanishes.

With this in hand the card's own recipe applies verbatim: normalize `Ψ_c = u_c/u_c(0)`, use
boundedness of the separation constants to take a limit, `tendsto_prolateProfile_oscProfile` for the
locally uniform convergence, `integral_rescaled_secondMoment_le` with
`integrable_sq_of_bounded_window_limits` for square integrability of the limit, and the rigidity
above to force `μ* = 2n+1` with `n` even and `Ψ* = φ_n/φ_n(0)`.  Every subsequential limit is the
same, so the full limit holds.

## Lean progress — the rigidity step, in the exact form the recipe uses

`RHTower/ProlateOscProfileLimit.lean` (wired, axiom-clean):

```text
odd_oscProfileDeriv                     the derivative of the limit profile is odd
even_rung_of_integrable_oscProfile
    if oscProfile m is square integrable then  m = 2n+1  with  n  even
```

This is `even_integrable_solution_rung` specialized to the limit profile, with both parity
hypotheses discharged: `even_oscProfile` was proved by uniqueness of the initial value problem, and
`odd_oscProfileDeriv` follows from it by uniqueness of the derivative.

So the rigidity step of the eigenvalue half now reads with **square integrability of the limit
profile as its only premise** — and that premise is itself supplied by
`integrable_sq_of_bounded_window_limits` from the uniform second-moment bound
`integral_rescaled_secondMoment_le` the prolate modes satisfy.

The chain from a bandwidth-indexed family to its rung is therefore complete end to end:

```text
bounded separation constants
  → exists_ultrafilter_tendsto_of_eventually_bounded      a common limit m
  → tendsto_prolateProfile_oscProfile_eventually          profiles converge to oscProfile m
  → integrable_sq_of_bounded_window_limits                oscProfile m is square integrable
  → even_rung_of_integrable_oscProfile                    m = 2n+1 with n even
```

with `false_of_orthogonal_same_limit` separating the limits of distinct modes, and the count
`|{1,5,…} ∩ [0,4j+1)| = j < j+1` closing `(α)`.

## Lean progress — the counting step

`HTGeometry/EvenRungCounting.lean` (wired, axiom-clean):

```text
not_injective_evenRung_below
    there is no injective family of j+1 even rungs below 4j+1
```

Only `j` even rungs lie below `4j+1` — namely `1, 5, …, 4j−3` — so the half-index map sends `j+1`
distinct rungs injectively into a `j`-element type, which pigeonhole forbids.

**Every mathematical step of `(α)` is now a theorem in the tree.**  Listed in the order the argument
uses them:

```text
eventually_rank_highProlateSpan_even_ge        j+1 independent even modes with μ < 4j+1+ε
exists_ultrafilter_tendsto_of_eventually_bounded   all j+1 separation constants converge at once
tendsto_prolateProfile_oscProfile_eventually  each profile converges to oscProfile of its limit
integrable_sq_of_bounded_window_limits        each limit profile is square integrable
even_rung_of_integrable_oscProfile            each limit is an even rung
false_of_orthogonal_same_limit                distinct modes have distinct limits
not_injective_evenRung_below                  j+1 distinct even rungs below 4j+1 is impossible
```

together with the supporting theory built for them, none of which mathlib has: global existence and
uniqueness for the linear second-order initial value problem, Hermite function orthogonality and
decay, the windowed virial identity, one-dimensionality of the square-integrable solution space, and
the bounded-window integrability criterion.

What separates this list from a closed `(α)` is only the bookkeeping of feeding the modes from the
first line into the second: selecting `j+1` pairwise orthogonal joint modes from the rank bound
(an orthonormal basis of the high-mode span adapted to the joint eigenspaces), and checking the
window hypotheses for that particular family — normalization at the origin, the a priori phase
bound, and the rescaled normal form, all of which `ProlateNormalizedProfile` already supplies for a
single mode.

## Lean progress — orthogonality of modes at distinct eigenvalues

`RHTower/ProlateModeOrthogonality.lean` (wired, axiom-clean):

```text
integral_mul_eq_zero_of_distinct_prolate_eigen
    two smooth prolate eigenfunctions with distinct eigenvalues pair to zero on the aperture
```

Immediate from the boundary-condition-free symmetry `prolateSLAction_band_symmetric`:
`η₁∫ΦΨ = ∫Ψ·(P_cΦ) = ∫Φ·(P_cΨ) = η₂∫ΦΨ`, so `(η₁−η₂)∫ΦΨ = 0`.

This is the first half of the mode-extraction bookkeeping: modes at distinct prolate eigenvalues are
automatically orthogonal, so a family of `j+1` modes needs Gram–Schmidt only *within* a single joint
eigenspace, where `prolateOnEvenEigenspace` is a symmetric operator on a finite-dimensional space
and `IsSymmetric.eigenvectorBasis` already supplies an orthonormal eigenbasis of joint modes.

## Lean progress — the mode-extraction bookkeeping is closed

The remaining `(α)` bookkeeping was to turn a *linearly independent* family of joint modes into an
*orthogonal* one.  A corpus audit found that the hard half was already proved:

```text
ProlateSeparationSimplicity.eq_const_mul_of_same_even_joint_prolate_eigen
    a separation value determines the band eigenvalue and the eigenline: two even joint modes with
    the same χ are multiples of one another
ProlateSeparationSimplicity.finrank_prolateOnEvenEigenspace_eigenspace_le_one
```

so no Gram–Schmidt is needed at all.  Combined with the symmetry argument, this gives

```text
ProlateModeOrthogonality.integral_mul_eq_zero_of_not_proportional
    two even joint modes that are not multiples of one another are orthogonal on the aperture
```

(wired, axiom-clean).  Non-proportional forces distinct separation values by simplicity, and
distinct separation values force orthogonality by the boundary-condition-free symmetry of the
prolate action.

**So `(α)`'s extraction step is closed**: `j+1` linearly independent joint modes — which
`eventually_rank_highProlateSpan_even_ge` supplies — are automatically pairwise orthogonal, which is
exactly the input `false_of_orthogonal_same_limit` consumes.  Every step of `(α)` is now proved in
the tree, and the only assembly left is threading the window hypotheses of
`ProlateNormalizedProfile` through the family.

`(β)`, the Fuchs asymptotics identifying the true leakages with the Fuchs family, is untouched and
remains this card's external input.

## Lean progress — orthogonality reaches the rescaled window

`RHTower/ProlateNormalizedProfile.lean` (extended, wired, axiom-clean):

```text
integral_normalizedProlate_mul_eq_zero
    if two profiles are orthogonal on the aperture, their normalized rescalings are orthogonal
    on the window [−√c, √c]
```

The change of variables `integral_comp_div_sqrt` carries `∫_{−1}^{1}ΦΨ = 0` to
`∫_{−√c}^{√c}` of the rescaled product, and the normalization constants factor out.

This is the bridge from the mode-level orthogonality of the previous step to the exact form
`abs_window_pairing_sub_le_of_secondMoment` and `false_of_orthogonal_same_limit` consume.  The
aperture-to-window chain for a family of `j+1` modes now reads:

```text
eventually_rank_highProlateSpan_even_ge      j+1 linearly independent even joint modes
integral_mul_eq_zero_of_not_proportional     pairwise orthogonal on the aperture
integral_normalizedProlate_mul_eq_zero       pairwise orthogonal on the rescaled window
abs_window_pairing_sub_le_of_secondMoment    hence O(K⁻²) on every fixed window
false_of_orthogonal_same_limit               so their limit profiles differ
```

with `even_rung_of_integrable_oscProfile` placing each limit on the even ladder and
`not_injective_evenRung_below` closing the count.  Every link is unconditional and axiom-clean.

## Lean progress — the uniform mass bound

`HTGeometry/WindowTotalSqueeze.lean` (extended, wired, axiom-clean):

```text
total_mass_le_of_window_bound
    N·(1 − μ/K²) ≤ 2K·B²    where N is the total mass, B a pointwise bound on the window [−K,K]
                            and μ the second-moment ratio
```

This is the step that makes the mass bound *uniform in the outer radius*, which is what the limit
machinery needs and what a naive `∫_{−K}^{K} u² ≤ 2KB²` does not give.  Chebyshev bounds the tail by
`(μ/K²)N`, so the window mass already accounts for a fixed fraction of the total; a pointwise bound
on that one window therefore caps the whole mass.

It also turned out to need neither `μ < K²` nor nonnegativity of the mass — both were in the first
statement and neither is used, so the lemma is stated without them and the caller supplies
positivity of `1 − μ/K²` only when it wants to divide.

Applied to the normalized prolate profiles, with `B` the a priori phase bound
`normalizedProlate_phase_le` and `μ` the separation constant bounded by `Λ`, this gives a single
constant `N` with `∫_{−K}^{K} u_i² ≤ N` for every window and every member of the family — the
hypothesis `integrable_sq_of_bounded_window_limits` and `false_of_orthogonal_same_limit` both
consume.

## Lean progress — the uniform mass bound, instantiated for prolate modes

`RHTower/ProlateGroundTotalMass.lean` (extended, wired, axiom-clean):

```text
normalizedProlate_total_mass_le
    (∫_{−√c}^{√c} u²)·(1 − μ/K²) ≤ 2K·(prolateWindowPhaseBound K)²
    for the normalized rescaled profile of any even joint mode
```

Every input is already in the tree: `normalizedProlate_window_package` for the normal form and the
initial phase vector, `normalizedProlate_phase_le` for the a priori bound on `[0,K]`,
`even_normalizedProlateProfile` with `abs_le_of_even_window` to carry it to `[−K,K]`,
`normalizedProlate_secondMoment_le` for the second-moment estimate, and
`total_mass_le_of_window_bound` to combine them.

So for a family with separation constants bounded by `Λ`, fixing any `K` with `K² > Λ` gives a
single constant `N`, depending only on `K` and `Λ`, with

```text
∫_{−K′}^{K′} u_i²  ≤  ∫_{−√c}^{√c} u_i²  ≤  N     for every window K′ and every member i .
```

That is the last quantitative hypothesis the `(α)` chain needed: it feeds
`integrable_sq_of_bounded_window_limits` (square integrability of each limit profile) and
`false_of_orthogonal_same_limit` (the `O(K⁻²)` pairing bound) at once.

## Lean progress — the two shape adapters for the assembly

Two small generalizations, both wired and axiom-clean, that remove the shape mismatches between the
`(α)` pieces and the family they have to be applied to.

`RHTower/ProlateWindowMass.lean`:

```text
abs_sub_le_of_even_window'
    evenness transports a difference bound against an *arbitrary* even comparison function
    from [0,K] to [−K,K]
```

The existing version was tied to the Gaussian; the limit profile `oscProfile m` is even for every
`m` (`even_oscProfile`), so the general version applies to it directly.

`HTGeometry/WindowProductLimit.lean`:

```text
tendsto_intervalIntegral_product_eventually
    pairings converge to the pairing of the limits under *eventual* hypotheses
```

The original required its continuity, closeness and boundedness hypotheses for every index; a
bandwidth-indexed family supplies them only eventually — the window inclusion `2K² ≤ c` alone is an
eventual condition — so the eventual form is what the assembly can actually feed it.

With these, the window-mass convergence needed twice in the `(α)` chain
(`integrable_sq_of_bounded_window_limits` and `false_of_orthogonal_same_limit`) is reachable from
`prolateProfile_window_osc_dist_le` plus `even_normalizedProlateProfile` and `even_oscProfile`,
with the envelope of `tendsto_oscWindowEps` as the rate.

## Lean progress — the window envelope as a named quantity

`RHTower/ProlateOscProfileLimit.lean` (extended, wired, axiom-clean):

```text
oscWindowEnvelope c μ m K B      the Grönwall envelope of the comparison against oscProfile m
oscWindowEnvelope_nonneg         it is nonnegative
tendsto_oscWindowEnvelope        and vanishes as μ → m, c → ∞
```

Naming the envelope is what lets the window comparison be fed to
`tendsto_intervalIntegral_product_eventually`, whose rate parameter `E : ι → ℝ` must be an explicit
function of the index with `E → 0` and `0 ≤ E i`.  Previously the envelope existed only inline
inside `prolateProfile_window_osc_dist_le`'s statement, where it could not be named as such a rate.

Nonnegativity needed the three factors separately — both coefficient defects are nonnegative for
positive bandwidth, and `exp(t) − 1 ≥ 0` for `t ≥ 0` via `Real.add_one_le_exp` — none of which is
automatic from the expression.

With the envelope named, the window-mass convergence

```text
∫_{−K}^{K} u_i·u_i  →  ∫_{−K}^{K} oscProfile m · oscProfile m
```

is an instantiation of `tendsto_intervalIntegral_product_eventually` with
`E i = oscWindowEnvelope (c i) (μ i) m K B`, the closeness bound from
`prolateProfile_window_osc_dist_le` carried to `[−K,K]` by `abs_sub_le_of_even_window'`, and the
uniform bound from `normalizedProlate_phase_le` carried across by `abs_le_of_even_window`.

## Lean progress — window masses converge

`RHTower/ProlateWindowMassLimit.lean` (wired, axiom-clean):

```text
tendsto_prolateWindowMass
    ∫_{−K}^{K} u_i·u_i  →  ∫_{−K}^{K} oscProfile m · oscProfile m
    for a family of normalized rescaled profiles with separation constants tending to m
    and bandwidth escaping
```

Every hypothesis it needs is discharged from pieces already in the tree: the Grönwall comparison
`prolateProfile_window_osc_dist_le` on `[0,K]`, carried to `[−K,K]` by `abs_sub_le_of_even_window'`
against the even limit profile; the uniform phase bound carried across by `abs_le_of_even_window`;
the envelope's nonnegativity and vanishing; and a bound on `oscProfile m` over the compact window.

This is the convergence hypothesis the `(α)` argument consumes **twice** — once as the input to
`integrable_sq_of_bounded_window_limits`, which then makes the limit profile square integrable and
so puts its separation constant on the even ladder, and once as the input to
`false_of_orthogonal_same_limit`, which separates the limits of two orthogonal modes.

With it, every hypothesis of every step in the `(α)` chain is now available in the form the step
asks for.  What remains is to write the chain down for a family of `j+1` modes.

## Lean progress — the eigenvalue half, assembled for one family

`RHTower/ProlateWindowMassLimit.lean` (wired, axiom-clean):

```text
exists_evenRung_of_prolate_family
    for a family of normalized rescaled prolate profiles with
      • the rescaled normal form and the initial phase vector u(0)=1, u′(0)=0 on every window,
      • a uniform a priori phase bound B,
      • a uniform window-mass bound N,
      • separation constants tending to m and bandwidth tending to infinity,
    the limit satisfies  m = 2n+1  with  n  even.
```

This is the card's **eigenvalue half**, `c·s(c) → 2n+1`, assembled end to end for a single family.
Its proof is three lines because every step was built separately: `tendsto_prolateWindowMass` gives
the window-mass convergence, `integrable_sq_of_bounded_window_limits` turns the uniform bound into
square integrability of the limit profile, and `even_rung_of_integrable_oscProfile` — the rigidity
statement this card named as its missing classical input — puts the limit on the even ladder.

Every hypothesis is one the prolate family satisfies, and each has its own theorem in the tree:
`normalizedProlate_window_package` for the normal form and normalization,
`normalizedProlate_phase_le` for `B`, `normalizedProlate_total_mass_le` for `N`, and
`even_normalizedProlateProfile` for evenness.

The remaining `(α)` statement — that the `j`-th separation constant tends to `4j+1` — now follows by
applying this theorem to each of the `j+1` modes supplied by
`eventually_rank_highProlateSpan_even_ge`, separating their limits with
`false_of_orthogonal_same_limit` (whose orthogonality hypothesis is
`integral_normalizedProlate_mul_eq_zero` applied to
`integral_mul_eq_zero_of_not_proportional`), and closing with `not_injective_evenRung_below`.

## Lean progress — the `(α)` counting capstone

`RHTower/ProlateWindowMassLimit.lean` (extended, wired, axiom-clean):

```text
false_of_prolateFamily_below
    there is no family of j+1 prolate mode families whose limiting separation constants are
    distinct and all below 4j+1
```

Each limit is an even rung by `exists_evenRung_of_prolate_family`; only `j` even rungs lie below
`4j+1`; `not_injective_evenRung_below` closes it.

This is `(α)`'s lower half as a theorem, with two of its inputs left as hypotheses on the family —
the window data (normal form, normalization, uniform phase and mass bounds) and the distinctness of
the limits.  Both are supplied by theorems already in the tree:

```text
window data     normalizedProlate_window_package, normalizedProlate_phase_le,
                normalizedProlate_total_mass_le, even_normalizedProlateProfile
distinctness    false_of_orthogonal_same_limit, whose orthogonality hypothesis is
                integral_normalizedProlate_mul_eq_zero applied to
                integral_mul_eq_zero_of_not_proportional
```

so what is left is threading them through — no further mathematics.  `(β)`, the Fuchs asymptotics,
is untouched and remains the card's external input.

## Lean progress — cross pairings converge

`RHTower/ProlateWindowMassLimit.lean` (extended, wired, axiom-clean):

```text
tendsto_prolateWindowPairing
    for two prolate families,
    ∫_{−K}^{K} u_i·v_i  →  ∫_{−K}^{K} oscProfile m · oscProfile m′
```

The rate is the *sum* of the two envelopes, which dominates each separately and still vanishes; the
uniform bounds and the evenness transports are the same as in the diagonal case.

This is the last hypothesis of `false_of_orthogonal_same_limit` that was not yet available for the
prolate family.  With it, the distinctness of the limits — the one input
`false_of_prolateFamily_below` still takes as a hypothesis — is derivable: if two modes had the same
limit `m`, their pairings would converge to `∫_{−K}^{K}(oscProfile m)² > 0`, while
`integral_normalizedProlate_mul_eq_zero` (from `integral_mul_eq_zero_of_not_proportional`) together
with `abs_window_pairing_sub_le_of_secondMoment` forces them to be `O(K⁻²)`.

## Lean progress — distinctness of the limits, derived

`RHTower/ProlateWindowMassLimit.lean` (extended, wired, axiom-clean):

```text
prolateFamily_limit_ne
    two prolate families whose window pairings are O(K⁻²) have distinct limiting
    separation constants
```

A common limit would make the pairings converge to `∫_{−K}^{K}(oscProfile m)²`, which is positive
and nondecreasing in `K`, while the `O(K⁻²)` bound sends them to zero.

This discharges the last hypothesis that `false_of_prolateFamily_below` was still carrying.  The
`O(K⁻²)` bound itself is the composite

```text
integral_mul_eq_zero_of_not_proportional      modes not multiples of one another are
                                              orthogonal on the aperture
integral_normalizedProlate_mul_eq_zero        hence their normalized rescalings are orthogonal
                                              on [−√c, √c]
abs_window_pairing_sub_le_of_secondMoment     so the pairing on a fixed window [−K,K] differs
                                              from zero by at most (2K²)⁻¹ times the second
                                              moments, which the mode bound caps
```

So both hypotheses of the counting capstone are now theorems.  `(α)` is closed as a chain of
unconditional axiom-clean results; the card's remaining input is `(β)`, the Fuchs asymptotics.

## Lean progress — `(α)`'s lower half, fully assembled

`RHTower/ProlateWindowMassLimit.lean` (wired, axiom-clean):

```text
false_of_orthogonal_prolateFamily_below
    there is no family of j+1 pairwise orthogonal prolate mode families whose limiting
    separation constants all lie below 4j+1
```

Distinctness of the limits is now *derived* from the orthogonality rather than assumed, so the only
hypotheses left are ones the prolate modes satisfy:

```text
the rescaled normal form and normalization u(0)=1, u′(0)=0 on every window
                                  normalizedProlate_window_package
a uniform a priori phase bound B   normalizedProlate_phase_le
a uniform window-mass bound N      normalizedProlate_total_mass_le
evenness                           even_normalizedProlateProfile
pairwise O(K⁻²) window pairings    integral_mul_eq_zero_of_not_proportional
                                     → integral_normalizedProlate_mul_eq_zero
                                     → abs_window_pairing_sub_le_of_secondMoment
separation constants converging    exists_ultrafilter_tendsto_of_eventually_bounded
bandwidth escaping                 the family is indexed by bandwidth
```

Together with the upper half `eventually_rank_highProlateSpan_even_ge`, which supplies `j+1`
linearly independent — hence, by simplicity, pairwise orthogonal — even joint modes with separation
below `4j+1+ε`, this is `(α)`: the `j`-th even separation constant tends to `4j+1`.

Every theorem in the chain is unconditional and axiom-clean.  What the card still needs is `(β)`,
the Fuchs asymptotics identifying the true leakages `d_n(λ)` with the Fuchs family
`A_n λ^{2n+1}e^{−4πλ²}`; that is external and untouched.

## The polynomial factor of `(β)` is the logarithmic correction to the WKB action

A corpus audit locates `(β)`'s obstruction precisely, and removes the first half of it.

### Where the corpus already stands

The reduction of the leakage to an exterior/interior mass ratio is **already formal**, and was not
recorded on this card: `ConstrainedProlatePointwiseRepresentative`'s
`evenTimeLimitedFourierRepresentative_exterior_energy` gives, for every time-limited `f`,

```text
∫_{y ≤ −a} |q|² + ∫_{y > a} |q|²  =  ‖f‖² − ‖T_a f‖² ,       q = the Fourier representative,
```

and `evenProlateSignedFourierRepresentative_exterior_energy_eq_leakage` specializes it to a live
signed mode: the leakage `1 − σ_n(a)²` **is** the exterior energy of the mode's Fourier
representative.  So `(β)` was already an ODE statement, not an operator statement.  Downstream,
`ProlateTurningLayer` turns exact mass balance into a leakage bound:

```text
leakage_lower_of_radial_mass_bounds :
  outside = inside · leakage / value²,  outside ≥ 1/(32c²),  inside ≤ 4e(c/√s)e^{2c(1−s)}
    ⟹  leakage ≥ (√s/(256 e c³))·e^{−2c(1−s)} .
```

### Why that bound cannot reach Fuchs, and what the missing factor is

Both the interior bound and the endpoint bound above use the crude WKB estimate
`∫_{√s}^{b} √((y²−s)/(1−y²)) dy ≤ 1 − s` (`integral_prolateWKB_le_aperture`,
`exp_neg_aperture_le_endpoint`).  At a fixed mode `s ≍ (2n+1)/c`, so `e^{−2c(1−s)}` is a *constant*
times `e^{−2c}`, whereas the Fuchs leakage is `c^{n+1/2} e^{−2c}`.  The whole polynomial factor is
missing, and it is missing for a definite reason: the WKB action

```text
A(s) = ∫_{√s}^{1} √((y²−s)/(1−y²)) dy = ∫_{arcsin √s}^{π/2} √(sin²θ − s) dθ
```

is not `1 − O(s)` but `1 + (s/4)·log s + O(s)`, and it is the *logarithmic* term that produces the
power of `c`:

```text
c·A(s) = c + (cs/4)·log s + O(cs) = c − ((cs)/4)·log c + O(1)      when c·s is bounded,
```

so `e^{−2cA(s)} = c^{(cs)/2} e^{−2c}·Θ(1)`, and with `c s = 2n+1` that is exactly `c^{n+1/2}e^{−2c}`.

### The sharp action, proved

`formal/GaloisForLFunctions/RHTower/ProlateWKBSharpAction.lean`, wired into the `RHTower` umbrella,
axioms `[propext, Classical.choice, Quot.sound]`:

```text
prolateAngleAction s = ∫_{arcsin √s}^{π/2} √(sin²θ − s) dθ

prolateAngleAction_sub_bounds :
   0 ≤ 1 + (s/4)·log s − A(s) ≤ 3 s               for 0 < s ≤ 1
```

Both bounds are explicit and one-signed.  The proof:

* the substitution `y = sin θ` removes the endpoint singularity, so every integral in sight is of a
  continuous function on a compact interval;
* `sin θ − √(sin²θ − s) = s/(2 sin θ) + ρ`, `0 ≤ ρ ≤ s²/(2 sin³θ)` — proved as
  `sub_sqrt_sq_sub_bounds`, the two inequalities being `(u−w)² ≥ 0` and
  `s u² + s² − 2u³(u−w) = w(2u+w)(u−w)²`;
* the main term integrates **exactly**: `log tan(θ/2)` differentiates to `1/sin θ`
  (`hasDerivAt_log_tan_half`) and `tan(t/2) = √s/(1+√(1−s))` at the turning angle
  (`tan_half_arcsin_sqrt`), so
  `∫_t^{π/2} dθ/sin θ = −(log s)/2 + log(1+√(1−s))` (`integral_one_div_sin_eq`);
* the correction is `O(s)` by Jordan's inequality `sin θ ≥ 2θ/π` together with
  `arcsin √s ≥ √s`, giving `∫_t^{π/2} dθ/sin³θ ≤ π³/(16 s)` (`integral_one_div_sin_cube_le`);
* the three leftover terms `1−√(1−s)`, `(s/2)log(1+√(1−s))` and the correction are each nonnegative
  and each at most `s`, whence the one-sided form.

Getting the *sharp* constant of the `s·log s` term is the whole point: replacing the exact cosecant
antiderivative by the comparison `1/sin θ ≍ 1/θ` would leave a factor-`π/2` uncertainty in that
coefficient, which is a factor `c^{±(2n+1)/4}` in the leakage — enough to destroy the ladder.

### Transport to the band variable, and the improved endpoint bound

Same module:

```text
prolateWKBProfile s y = √((y²−s)/(1−y²))
prolateWKB_eq_mul_profile :   prolateWKB c (−s c²) y = c · prolateWKBProfile s y     (c ≥ 0)
integral_prolateWKBProfile_eq :
   ∫_{√s}^{b} prolateWKBProfile s = ∫_{arcsin √s}^{arcsin b} √(sin²θ − s)            (b < 1)
integral_prolateWKB_le_angleAction :
   ∫_{√s}^{b} prolateWKB c (−s c²) ≤ c · A(s)
exp_neg_angleAction_le_endpoint :
   Φ(√s)·exp(−c·A(s)) ≤ Φ(b)
exp_neg_sharp_le_endpoint :
   Φ(√s)·exp(−(c + (cs/4)·log s)) ≤ Φ(b)
```

The last two are the sharp replacements for the corpus's `exp_neg_aperture_le_endpoint`, whose
conclusion is only `Φ(√s)·e^{−c} ≤ Φ(b)`.  The gain is the factor `s^{−cs/4}`; squared, and with
`c s = 2n+1`, that is exactly the Fuchs power `c^{n+1/2}`.  The change of variables is done on
`[√s, b]` with `b < 1`, i.e. strictly inside the band where the integrand is continuous, which is
also the form in which the corpus's Riccati comparison consumes it; the endpoint limit `b → 1` is
`ProlateForbiddenEndpoint`'s business and is untouched.

### What `(β)` still needs

With the sharp action in hand, three items remain, and all three are ODE estimates on the same
solution:

1. **The endpoint upper bound.**  The corpus owns the Riccati *sub*solution direction
   (`prolateWKB_subsolution`, `prolateLogDeriv_le_prolateWKB`), which gives `Φ(1) ≥ …`.  The reverse
   needs a Riccati *super*solution — the Liouville–Green profile `√q + q′/(4q) − b/2` — so that
   `Φ(1) ≤ Φ(√s)·poly·e^{−c A(s)}`.
2. **The interior normalization from below.**  `integral_sq_le_turning_amplitude_envelope` bounds
   `∫_{−1}^1 Φ²` above by `4e(c/√s)Φ(√s)²`; the matching lower bound `∫_{−1}^1 Φ² ≥ κ (c/√s)^{-1}…`
   — really `∫_{−1}^1 Φ² ≍ Φ_max² c^{−1/2}` — is what fixes the remaining half-power.
3. **The exterior mass upper bound.**  Only `outside ≥ 1/(32c²)` is proved; the companion
   `outside ≤ C Φ(1)²/c` comes from the Bessel-type behaviour at the regular singular point, for
   which `ProlateTwoBranch` and the Dunster layer already supply the amplitude.

Items 1–3 together with `prolateAngleAction_sub_bounds` give the two-sided envelope, and the
`FuchsEnvelope` consumer tolerates a slack of `±3/2` in the exponent, so none of the three has to be
sharp in its constants — only in its power of `c`.

## `(β)` item 1 closed: the endpoint bound in the *decaying* direction

The previous entry listed three ODE estimates still needed for `(β)`.  The first — an upper bound
for the endpoint value with the sharp WKB rate — is now proved, and by an argument that needs no
approximation theory at all.

### Why the obvious route fails, and what replaces it

The corpus's endpoint bound `le_endpoint_prolateWKB` comes from the Riccati *sub*solution property
of the WKB profile: `v = −Φ′/Φ ≤ √q`, hence `Φ(1) ≥ Φ(y₀)·exp(−∫√q)`.  The reverse inequality
`v ≥ √q − …` cannot come from a supersolution — the profile `√q + q′/(4q) − b/2` is *not* one; its
Riccati defect changes sign at `2y² = 1 + s`, exactly where the corpus's outer band begins.

It follows instead from **positivity alone**.  Beyond the turning point the Sturm flux has one sign
(`deriv_nonpos_of_turning`), so `v ≥ 0` on the *whole* remaining band; and the profile `√Q` is a
repeller from below for `v′ = v² + Bv − Q`: once `v` is below `√Q` it decreases, and once it
decreases it falls faster, so it reaches `0` and then crosses it in bounded time.  A `v` that stays
nonnegative on a window therefore cannot have started far below `√Q`.

`formal/GaloisForLFunctions/HTGeometry/RiccatiNoDip.lean`, wired into the `HTGeometry` umbrella,
axioms `[propext, Classical.choice, Quot.sound]`:

```text
sub_sub_div_le_of_riccati_nonneg :
  v′ = v² + B v − Q  on [y₀,y₁],  v ≥ 0 there,  Q ≥ S² ,  0 ≤ B ≤ M
    ⟹  v(y₀) ≥ S − M − 2/(y₁ − y₀)
```

The proof is two applications of the corpus's `riccati_le_of_le_of_supersolution` against explicit
**affine** supersolutions: first the drop `m − κ(y − y₀)` with `κ = S² − Mm − m²`, which forces
`v` to reach `0` strictly inside the window, and then the descent `−λ(y − z)` from that zero, which
forces `v` below `0` — contradicting nonnegativity.  Both affine functions are supersolutions only
because of the algebra `m + M < S − 2/L ⟹ κ > 2S/L`, which is where the constant `2` in the
statement comes from.

### The prolate instance and the endpoint bound

`formal/GaloisForLFunctions/RHTower/ProlateEndpointUpperBound.lean`, wired into the `RHTower`
umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

```text
prolatePotential_mono, prolateDrift_mono, prolateDrift_nonneg
    both Riccati coefficients are monotone on the nonnegative part of the band
prolateLogDeriv_nonneg
    beyond the turning point a positive mode has nonnegative Riccati derivative
prolateWKB_sub_le_prolateLogDeriv :
    prolateWKB c χ y₀ − 2y₁/(1−y₁²) − 2/(y₁−y₀)  ≤  prolateLogDeriv Φ y₀
prolate_endpoint_le :
    Φ b ≤ Φ a · exp(−∫_a^b (prolateWKB c χ t − 2(b+l)/(1−(b+l)²) − 2/l))
```

The last is the mirror of `exp_neg_aperture_le_endpoint`, in the direction the leakage upper bound
needs.  Its loss against the pure WKB rate is `(b−a)·(drift at `b+l` + 2/l)`, and both terms are
polynomial in the bandwidth once `l` is taken comparable to `1 − b`: the drift is `O(1/(1−b))` and
`2/l` likewise, so with `1 − b ≍ c^(−2)` the whole loss is `O(1)` in the exponent — no power of the
Gaussian clock is lost.  The integration step is
`GaloisForLFunctions.HTGeometry.le_mul_exp_integral_of_logDeriv_le'`, the windowed form added to
`EnvelopeFromLogDerivative.lean` alongside `mul_exp_integral_le_of_logDeriv_ge'` and
`exists_continuous_eqOn_Icc`.

### The action from below, with the endpoint tail

`ProlateWKBSharpAction.lean` gained the matching lower bound for the WKB integral, so the exponent
above is controlled by the sharp angular action rather than by the crude `c`:

```text
arcsin_le_pi_div_two_mul :   arcsin x ≤ (π/2)·x                        (Jordan, inverted)
angleAction_tail_le :        ∫_{arcsin b}^{π/2} √(sin²θ − s) ≤ (π/2)·√(1−b²)
sub_le_integral_prolateWKB :
    c·A(s) − c·(π/2)·√(1−b²)  ≤  ∫_{√s}^{b} prolateWKB c (−s c²)
```

With `1 − b ≍ c^(−2)` the tail `c√(1−b²)` is `O(1)`, so `∫_{√s}^{b} prolateWKB = c·A(s) + O(1)`
on both sides — `integral_prolateWKB_le_angleAction` above, and this below.

### Status of the three items

1. **Endpoint upper bound** — done, as above.
2. **Interior normalization from below** — open.  The corpus's
   `integral_sq_le_turning_amplitude_envelope` bounds `∫_{−1}^1 Φ²` above by `4e(c/√s)Φ(√s)²`,
   which is `c^(3/2)` where the truth is `c^(−1/2)`; the two-power gap is the largest single loss
   in the current chain and closing it needs the concentration of the mode in the allowed window
   `|y| ≤ √s` of width `≍ c^(−1/2)` together with the exponential decay just proved.
3. **Exterior mass upper bound** — open.  Only `outside ≥ 1/(32c²)` exists; the companion
   `outside ≤ C·Φ(1)²/c` comes from the Bessel behaviour at the regular singular point.

With the endpoint bound now two-sided at the sharp rate, items 2 and 3 are both statements about
*masses*, not about decay rates, and neither needs any further WKB input.

## `(β)` item 2: the band Sturm energy and the interior mass from below

The second of the three remaining estimates asked for a lower bound on the aperture mass in terms of
the mode's value at the turning point.  The obstruction was the *rate* at which the mode may fall
just past the turning point: the flux representation
`(1−y²)Φ′(y) = −∫_y^1 (χ + c²t²)Φ` gives only `|Φ′/Φ| = O(c²)` there, and a decay window of width
`c^(−2)` costs two powers of the bandwidth against the true width `c^(−1/2)`.

`formal/GaloisForLFunctions/RHTower/ProlateBandFluxEnergy.lean`, wired into the `RHTower` umbrella,
axioms `[propext, Classical.choice, Quot.sound]`, replaces `O(c²)` by `O(c)`:

```text
prolateWeightedPotential c χ y = (1 − y²)(χ + c²y²)
prolateBandEnergy c χ Φ y      = ((1−y²)Φ′)² − (1−y²)(χ + c²y²)Φ²

hasDerivAt_prolateBandEnergy :   E′ = −P′·Φ²        (the two cross terms cancel identically)
prolateBandEnergy_one :          E(1) = 0           (the weight vanishes at the endpoint)
prolateBandEnergy_nonpos :       E ≤ 0 past the maximum of P
prolateBandEnergy_le_of_inner :  E(y) ≤ (P(ystar) − P(y))·Φ(y)²  below it
prolateFlux_sq_le :              ((1−y²)Φ′(y))² ≤ K·Φ(y)²        whenever P ≤ K on the band
```

The two branches are the same identity read in the two directions in which `P` is monotone.  Past
the maximum of `P` the energy increases and vanishes at the endpoint, so it is nonpositive there;
below the maximum the energy at the top is nonpositive and the increase of `P` bounds the rest, the
monotonicity of `Φ` turning the integrand `P′Φ²` into `P′Φ(y)²`.  Since
`max P = c²(1−s)²/4`, the resulting flux bound is `|(1−y²)Φ′| ≤ (c(1−s)/2)·Φ` — one full power of
`c` better than the flux representation, uniformly on the band and with no initial data.

Its two consequences, in the same module:

```text
neg_mul_le_deriv_of_fluxBound :  −(√K/(1−t²))·Φ(t) ≤ Φ′(t)
exp_mul_le_prolate :             Φ(a)·exp(−∫_a^b √K/(1−t²)) ≤ Φ(b)
mass_lower_of_fluxBound :
   (b−a)·(Φ(a)·exp(−∫_a^b √K/(1−t²)))² ≤ ∫_a^b Φ²
```

With `K = c²(1−s)²/4` and a window of length `b − a ≍ 1/c` the exponent is `O(1)`, so

```text
∫_a^b Φ² ≥ κ·c^(−1)·Φ(a)² ,
```

against the true `c^(−1/2)`: the loss is now `c^(1/2)`, down from `c^(3/2)` for the flux-representation
route and from `c^(2)` for the corpus's `integral_sq_le_turning_amplitude_envelope` used in reverse.
That is inside the `±3/2` slack the `FuchsEnvelope` consumer allows.

### Remaining

Only item 3 of the three: the exterior mass from above, `outside ≤ C·Φ(1)²/c`, which is the Bessel
behaviour at the regular singular point `y = 1` and for which `ProlateTwoBranch` and the Dunster
layer already supply the amplitude.  Items 1 and 2 — the endpoint bound in both directions at the
sharp WKB rate, and the interior mass from below — are proved.

## Precision accounting for `(β)`, and the correction it forces

The previous two entries recorded items 1 and 2 as "closed".  They are proved, but a precision
audit shows only item 2 is sharp enough for the `FuchsEnvelope` consumer.  Recording the arithmetic
so no later session re-derives it.

### The slack the consumer actually allows

`FuchsEnvelope`'s three conclusions use only `fuchsRate C (e j) λ < fuchsRate c (e j + 4) λ`, i.e.
that the *upper* power at one ladder index is below the *lower* power at the next.  In the aperture
variable the ladder step is `8`, and the aperture-weighted tail rate costs one more, so a two-sided
estimate with multiplicative slacks `c^{σ₊}`, `c^{σ₋}` around the true value is admissible exactly
when

```text
σ₊ + σ₋ < 7/2          (c = 2πλ², so a factor c^σ is λ^{2σ}).
```

### Item 2 is inside the budget

`mass_lower_of_fluxBound` with `K = c²(1−s)²/4` and window `[√s, √s + 1/c]` has
`∫ √K/(1−t²) = O(1)`, so `inside ≥ κ·c^(−1)·Φ(√s)²` against the true `c^(−1/2)`: `σ = 1/2`.

### Item 1 is not, and why

`prolate_endpoint_le_log` — the improved form, with the comparison window taken proportional to the
distance to the endpoint rather than fixed — has loss exactly

```text
∫_a^b 6/(1−t) dt = 6·(log(1−a) − log(1−b))            (integral_six_div_one_sub)
```

which is the best this method gives: optimizing the window fraction `θ` in
`2/θ + 1/(1−θ)` bottoms out near `5.83`, and pushing the no-dip constant `2` down to its floor `1`
only reaches `4`.  The endpoint bound must be carried to `1 − b ≍ c^(−2)` — any farther out and the
uncovered WKB tail `∫_b^1 √q ≍ c√(1−b)` itself blows up — so the loss is `(1−b)^(−6) ≍ c^(12)`.
That is `σ₊ ≈ 12`, far outside `7/2`.

The reason is structural: the no-dip bound `v ≥ √Q − M − 2/L` compares a profile `√Q ≍ c(1−t)^(−1/2)`
against a loss `≍ (1−t)^(−1)`, and the two cross exactly at `1 − t ≍ c^(−2)` — precisely the scale
the argument has to reach.  No choice of window repairs that; the method is sharp in the exponential
rate and inherently `c^(O(1))` in the prefactor.

So `RiccatiNoDip` and `prolate_endpoint_le_log` stand as unconditional theorems — uniform, with no
initial data and no approximation theory — but they are not the tool that closes `(β)`.

### What is the tool

The corpus already owns the sharp endpoint analysis, on the *radial* side, with explicit constants
and `O(1/c)` relative error — which is `σ = 0`:

```text
ProlateDunsterEndpointCoefficientBounds
    abs_radialProlate_regularCoefficient_crossing_le            |F_regular| ≤ 18/c
    abs_radialProlate_logCoefficient_sub_pi_div_four_crossing_le |F_log − π/4| ≤ 141/c
ProlateDunsterUniformTransfer
    abs_radialProlate_sub_regularModel_le
        the endpoint-normalized radial profile differs from the regular Bessel model by
        O(1/c) times the common Bessel amplitude, uniformly beyond the matching point
ProlateDunsterEndpointVolterra, ProlateDunsterEndpointWronskian, ProlateDunsterBesselOffDiagonal,
ProlateTwoBranch  (the Liouville–Green amplitude and its two-branch form)
```

These are unconditional and already carry the `1/c` relative precision that `(β)` needs.  So the
route for **item 3** — and for the sharp replacement of item 1 — is not new WKB theory but the
computation of the exterior mass of the *Bessel model*:

```text
∫_1^∞ (model)² ≍ R(1)²/c ,
```

after which `abs_radialProlate_sub_regularModel_le` transfers it to the actual profile with `O(1/c)`
relative error.  The model integral is elementary in the Liouville–Green variable: with
`z = κ√(2u)`, `u = t − 1`, `κ² = c²(1−s)`,

```text
∫_0^1 J₀(κ√(2u))² du = (1/κ²)∫_0^{κ√2} J₀(z)² z dz ≍ 1/κ ≍ 1/c ,
```

and the far field contributes `O(1/c)` through the `1/t` decay of the amplitude.  What that needs
from mathlib or from the corpus is `∫ J₀² z dz` — the Bessel Parseval/`J₀² + J₁²` identity — plus
the corpus's own amplitude bounds.

### Revised status of the three items

1. **Endpoint upper bound** — proved unconditionally at the sharp exponential rate with a
   `c^(O(1))` prefactor (`prolate_endpoint_le_log`); *not* sharp enough on its own, superseded for
   `(β)` by the Dunster transfer.
2. **Interior mass from below** — proved, `σ = 1/2`, inside the budget.
3. **Exterior mass** — open; reduces to the Bessel-model mass integral above, with the transfer
   already unconditional in the corpus.

## `(β)` item 3 closed: the exterior mass is `O(1/c)`

`formal/GaloisForLFunctions/RHTower/ProlateExteriorMassBound.lean`, wired into the `RHTower`
umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

```text
radialProlateExteriorMassConstant = 9/10 + 2π·K² + 2T/5
integral_Ioi_profileDensity_le_half
integral_Ioi_crossing_radialProlate_sq_le :
    ∫_{x > 1 + 9/(8c²)} R² ≤ (2πK² + 2T/5)/c
integral_Ioc_one_crossing_radialProlate_sq_le :
    ∫_{1}^{1 + 9/(8c²)} R² ≤ 9/(2c²)
integral_Ioi_one_radialProlate_sq_le :
    ∫_{x > 1} R(x)² dx ≤ radialProlateExteriorMassConstant / c
```

for every endpoint-normalized (`R 1 = 1`) exact radial solution, `0 ≤ s ≤ 1/2`, `c ≥ 5`.  `K` is
`lgBesselCommonEnvelopeConstant` and `T` is `radialProlateDensityTransferConstant`.

No new analysis was needed: the corpus already owned both halves and they had not been combined.
`integral_Ioi_abs_radialProlateDensity_sub_besselDensity_le` transfers the exact density
`c·R²` to the regular Bessel density in `L¹` with error `2T/c`, and
`integral_Ioi_radialProlateBesselDensity_le` dominates the Bessel density by a *bandwidth-free*
multiple of the arcsine profile density, whose total tail mass `integral_Ioi_profileDensity` is
`1/2`.  So the exact exterior density has total mass `O(1)`, and since the density carries the
factor `c`, the mass of `R²` itself is `O(1/c)`.  The collar `[1, 1 + 9/(8c²)]` between the singular
endpoint and the Dunster matching point is covered by `abs_radialProlate_le_two_endpoint` (`|R| ≤ 2`)
times its length, contributing `9/(2c²)`.

That is the sharp order: `σ = 0`.

## The single remaining bottleneck, stated exactly

With items 2 and 3 sharp, the leakage ratio `d/(1−d) = outside/inside` is controlled except for one
factor.  Normalizing `Φ(1) = 1`:

```text
outside ≤ C/c                                     (item 3, σ = 0)
inside  ≥ κ·c^(−1)·Φ(√s)²                          (item 2, σ = 1/2)
Φ(√s)  ≥ Φ(b)·exp(∫_{√s}^b prolateWKB − 6·log((1−√s)/(1−b)))   (item 1)
```

and `Φ(b) ≥ Φ(1) = 1` for free, because `Φ` is antitone past the turning point.  Every factor is
sharp except the last: item 1's loss `6·log((1−√s)/(1−b))` with `1 − b ≍ c^(−2)` is `c^(−12)`, and it
enters `inside` **squared**, so `σ₊ ≈ 24` against a budget of `7/2`.

So the whole of `(β)` now rests on one quantity:

> the barrier ratio `Φ(√s)/Φ(1)`, to relative precision `c^(±3/2)`.

Both directions of it are proved at the sharp exponential rate — `exp_neg_sharp_le_endpoint` below
and `prolate_endpoint_le_log` above — and both carry a `c^(O(1))` prefactor.  Closing the gap is the
band-side analogue of what the corpus's Dunster layer already does on the radial side: Liouville–Green
error control with an `O(1/c)` error-control function, rather than the crude Riccati comparison.  The
tools on the radial side that would be mirrored are

```text
CCMFirstRowDunsterModel      the Bessel model, its derivatives, and the common envelope constant
ProlateDunsterEndpointVolterra    endpoint-anchored Volterra transport
ProlateDunsterEndpointCoefficientBounds   |F_regular| ≤ 18/c,  |F_log − π/4| ≤ 141/c
ProlateDunsterUniformTransfer     the uniform O(1/c) transfer beyond the matching point
```

and the band-side model is not Bessel but parabolic-cylinder (Hermite) at the turning point
`y = √s`, with a Liouville–Green region between the two.  `HTGeometry.LiouvilleTransformation` and
`HTGeometry.LiouvilleGreenErrorBound` supply the transformation and the *oscillatory* Volterra error
bound already; what is missing is the **exponential** (barrier) analogue of
`abs_le_exp_of_oscillatoryLG`, with kernel `sinh` in place of `sin`.  That is one module of the same
shape as the oscillatory one, and it is the last unconditional input `(β)` needs.

## The barrier error bound — the last named input for `(β)`

The previous entry identified the remaining bottleneck as the barrier ratio `Φ(√s)/Φ(1)` to
relative precision `c^(±3/2)`, and named the missing tool: the **exponential** analogue of the
corpus's oscillatory Liouville–Green error bound, with kernel `sinh` in place of `sin`.  It is now
proved.

`formal/GaloisForLFunctions/HTGeometry/GronwallBackward.lean` and
`formal/GaloisForLFunctions/HTGeometry/LiouvilleGreenExponentialErrorBound.lean`, both wired into
the `HTGeometry` umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

```text
integral_comp_reflect
abs_le_exp_integral_of_volterra_bound_backward
continuous_integral_tail
abs_sub_one_le_exp_sub_one_of_volterra_bound_backward

expLGKernel u ξ t = (1 − exp(−2u(t−ξ)))/2
expLGKernel_nonneg, expLGKernel_le_half, abs_expLGKernel_le_half
IsExponentialLGSolution b u ψ V a :
    ∀ ξ ∈ [a,b],  V ξ = 1 + (1/u) ∫_ξ^b κ(ξ,t) ψ(t) V(t) dt
volterra_defect_of_exponentialLG
volterra_bound_of_exponentialLG
abs_le_exp_of_exponentialLG :
    |V ξ| ≤ exp((1/2u) ∫_ξ^b |ψ|)
abs_sub_one_le_exp_sub_one_of_exponentialLG :
    |V ξ − 1| ≤ exp((1/2u) ∫_ξ^b |ψ|) − 1
```

Two things make this the right statement rather than the naive one.  First, the anchor: on a
barrier the recessive branch accumulates from the *right*, so the Volterra equation integrates from
the far endpoint back, and the Grönwall inequality has to be reflected — that is
`GronwallBackward`, obtained from the corpus's forward inequality by the substitution
`u ↦ a + b − u` (`integral_comp_reflect`).  Second, the normalization: the raw kernel
`sinh(u(ξ−t))` is unbounded, and the entire content of writing `V(ξ) = e^{u(ξ−a)}W(ξ)` is that the
normalized kernel `e^{u(ξ−t)} sinh(u(t−ξ)) = (1 − e^{−2u(t−ξ)})/2` lies in `[0, 1/2]`.  The error
control is then the *mass* `∫_ξ^b |ψ|` of the perturbation, not a pointwise bound times the length —
which is what makes the estimate survive a barrier of length `≍ c`.

Applied to the prolate barrier after the Liouville transformation
(`HTGeometry.LiouvilleTransformation`), `ψ` is the LG defect `A''/A − g/f`, whose mass over the
barrier is `O(1/c)` away from the turning point, so the bound reads `|V − 1| ≤ e^{O(1/c)} − 1 =
O(1/c)` — precision `σ = 0`, against the `σ ≈ 12` of the Riccati route.

### What `(β)` still needs, after this

The pieces are now: sharp action (`prolateAngleAction_sub_bounds`), interior mass from below
(`mass_lower_of_fluxBound`, `σ = 1/2`), exterior mass from above
(`integral_Ioi_one_radialProlate_sq_le`, `σ = 0`), and the barrier error bound above (`σ = 0`).
What remains is *assembly*, in three steps, none of which needs a new estimate:

1. Perform the Liouville transformation on the prolate barrier explicitly — produce the `ξ`, `A`,
   `ψ` of `hasDerivAt_liouvilleTransform` for `q = (χ + c²y²)/(1 − y²)` — and check that the
   prolate mode's normalized transform satisfies `IsExponentialLGSolution`.
2. Bound the mass `∫ |ψ|` of the LG defect over `[y₀, 1 − δ]` by `O(1/c)`; this is the same
   computation the corpus already performs on the radial side in
   `CCMRadialProlateDefect.integral_volterra_exponent_le`.
3. Cross the turning layer at `y = √s`, where LG fails: the corpus's `ProlateTurningLayer` already
   propagates the amplitude across it at a fixed cost `exp(1)`, so this contributes `σ = 0`.

Step 2 is the only one with content, and its radial twin is already proved.

## The barrier Liouville–Green package is complete

The previous entry named "one module of the same shape as the oscillatory one" as the last
unconditional input.  It is built, and with it the barrier analogue of the corpus's oscillatory
Liouville–Green layer is complete end to end.

`formal/GaloisForLFunctions/HTGeometry/PerturbedBarrierVolterra.lean`, wired into the `HTGeometry`
umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

```text
barrierCoshTail, barrierSinhTail, barrierKernelTail, barrierKernelTailDeriv
barrierKernelTail_eq          the separated form IS ∫_ξ^b sinh(u(ξ−t)) ψ W
hasDerivAt_barrierKernelTail       K′ = u(cosh·C − sinh·S)     (the lower-limit terms cancel)
hasDerivAt_barrierKernelTailDeriv  K″ = u²K − u ψ W            (via cosh² − sinh² = 1)
barrier_volterra_eq :
    W″ = (u² + ψ)W ,  W(b) = e^{−u(b−a)} ,  W′(b) = −u e^{−u(b−a)}
      ⟹  W ξ = e^{−u(ξ−a)} − (1/u)·∫_ξ^b sinh(u(ξ−t)) ψ W
isExponentialLGSolution_of_ode :
    hence  ξ ↦ e^{u(ξ−a)} W ξ  satisfies  IsExponentialLGSolution
abs_barrier_normalized_sub_one_le :
    |e^{u(ξ−a)} W ξ − 1| ≤ exp((1/2u)·∫_ξ^b |ψ|) − 1
barrier_two_sided :
    (2 − E)·e^{−u(ξ−a)} ≤ W ξ ≤ E·e^{−u(ξ−a)} ,   E = exp((1/2u)·∫_ξ^b |ψ|)
```

Three things had to be right.  The **anchor**: recessive data is imposed at `b`, and the Volterra
kernel integrates back from there, because forward integration of a recessive branch is unstable —
that is why `GronwallBackward` was needed.  The **separation**: `sinh(u(ξ−t)) = sinh(uξ)cosh(ut) −
cosh(uξ)sinh(ut)` splits the kernel integral into two ordinary tail primitives, so its first
derivative loses the lower-limit terms exactly (they cancel) and its second derivative is
`u²K − uψW`; the equation then follows from the corpus's uniqueness for `v″ = P v`
(`LinearSecondOrderUnique.secondOrder_eq_at`) applied to the difference against the zero solution.
The **normalization**: `e^{u(ξ−t)}sinh(u(ξ−t)) = −(1 − e^{−2u(t−ξ)})/2 ∈ [−1/2, 0]`, which is what
turns an unbounded kernel into a contraction and makes the error control the *mass* `∫_ξ^b |ψ|`
rather than a pointwise bound times the length — the difference between an estimate that survives a
barrier of length `≍ c` and one that does not.

`barrier_two_sided` is precisely the `σ = 0` replacement for `prolate_endpoint_le_log`: the relative
error is `E − 1`, and for the prolate barrier `∫|ψ| = O(1/c)` gives `E − 1 = O(1/c²)`.

### `(β)`: what is left

```text
sharp action                      prolateAngleAction_sub_bounds          ✔
interior mass from below          mass_lower_of_fluxBound        σ = 1/2 ✔
exterior mass from above          integral_Ioi_one_radialProlate_sq_le  σ = 0 ✔
barrier estimate, both sides      barrier_two_sided              σ = 0   ✔
```

Only the instantiation remains, and it is two steps:

1. **Liouville transformation of the prolate barrier.**  Produce `ξ = ∫√Q`, `A = Q^{1/4}`, and the
   defect `ψ = Q^{−1/4}(Q^{−1/4})″` for `Q = (χ + c²y²)/(1 − y²)`, and check the two identities of
   `HTGeometry.hasDerivAt_liouvilleTransform` (`X′² = 1/f(X)` and `A²X′` constant).
2. **The defect mass.**  `∫ |ψ| dξ = ∫ |Q^{−1/4}(Q^{−1/4})″| dy = O(1/c)` away from the turning
   point, because `Q ≍ c²` there so `Q^{−1/4} ≍ c^{−1/2}` and its second derivative is again
   `≍ c^{−1/2}`.  The radial twin of this computation is already proved as
   `CCMRadialProlateDefect.integral_volterra_exponent_le`.

The turning layer at `y = √s`, where Liouville–Green fails, is crossed by the corpus's
`ProlateTurningLayer` at the fixed cost `exp(1)`, i.e. `σ = 0`.

## The turning layer drops out of the leakage upper bound

A re-derivation of the assembly removes the hardest remaining region.  The previous plan anchored
the interior mass at the turning point `y = √s` and therefore had to cross the Airy layer, where
neither Liouville–Green nor the flux bound is sharp: the uniform flux bound `|(1−y²)Φ′| ≤ (c/2)Φ`
integrates to `c√s ≍ √c` over `[√s, 2√s]`, and the LG defect mass diverges like `τ^(−3/2)` as the
turning point is approached.

Anchor the interior mass at `2√s` instead.  Then:

```text
inside  ≥ κ·c^(−1)·Φ(2√s)²        mass_lower_of_fluxBound on [2√s, 2√s + 1/c],
                                   where ∫ √K/(1−t²) = O(1)
outside ≤ (C/c)·Φ(1)²             integral_Ioi_one_radialProlate_sq_le, homogeneous
Φ(1) ≤ Φ(1−ε)                     free: Φ is antitone past the turning point
leakage = outside·value²/inside   the exact mass balance
```

so

```text
leakage ≤ (C/κ)·(Φ(1−ε)/Φ(2√s))² ,
```

and the only analytic input left is the barrier ratio on `[2√s, 1−ε]` — **strictly inside the
region where Liouville–Green is valid**.  The Airy layer `[√s, 2√s]` never appears, and neither
does the endpoint collar `[1−ε, 1]`, because monotonicity of `Φ` supplies the inequality in the
direction the upper bound needs.

The two truncations cost nothing:

```text
∫_{√s}^{2√s} √q  ≈ (2√2/3)·c·s = (2√2/3)(2n+1) = O(1)
∫_{1−ε}^{1} √q   ≈ c√ε = O(1)     for ε ≍ c^(−2)
```

so `∫_{2√s}^{1−ε} √q = c·A(s) + O(1)` — the sharp action up to a bounded factor, `σ = 0`.  And the
LG defect mass on `[2√s, 1−ε]` is `O(1)`: near the turning point the integrand
`Q^{−1/4}(Q^{−1/4})″` scales as `c^{−1}s^{−1}τ^{−5/2}` against `dy = √s dτ`, and `c·s = 2n+1` is
bounded, so the mass is `C_n·τ₀^{−3/2}` with `τ₀ = 1`; near `y = 1` it is `c^{−1}(1−y²)^{−3/2}`,
integrating to `c^{−1}ε^{−1/2} = O(1)`.

### The scalar step, proved

`formal/GaloisForLFunctions/RHTower/ProlateLeakageUpperScalar.lean`, wired into the `RHTower`
umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

```text
leakage_upper_of_mass_bounds :
    outside = inside·leakage/value² ,  L ≤ inside ,  outside ≤ U ,  value² ≤ 1
      ⟹  leakage ≤ U/L
leakage_upper_of_prolate_masses :
    with the exterior mass supplied by integral_Ioi_one_radialProlate_sq_le,
      leakage ≤ (radialProlateExteriorMassConstant / c) / L
```

This is the companion the corpus lacked: `ProlateTurningLayer.leakage_lower_of_radial_mass_bounds`
reads the same balance in the other direction.  Note that the concentration value only helps —
`value² ≤ 1` — so no lower bound on it is needed.

### `(β)`'s upper half, remaining

One item: instantiate `HTGeometry.barrier_two_sided` on `[2√s, 1−ε]`, which needs the Liouville
transformation of the prolate normal form
`Q̂ = (χ + c²y²)/(1−y²) + (1−y²)^(−2)` and the `O(1)` bound on `∫|Q̂^{−1/4}(Q̂^{−1/4})″|`.  Then
`Φ(1−ε)/Φ(2√s) ≤ E·exp(−∫_{2√s}^{1−ε}√Q̂)` with `E = O(1)`, and
`leakage ≤ C·e^{−2cA(s)} = C·c^(n+1/2)e^{−2c}` — the Fuchs upper bound.

The lower half needs the two reversed inputs: `outside` from below at the sharp order (the corpus
has only `≥ 1/(32c²)`, lossy by `c`) and `inside` from above (`integral_sq_le_turning_amplitude_envelope`,
lossy by `c²`).  Both are mass estimates, not decay estimates, and both are now the only places
where the turning layer still enters.

## Liouville–Green in the original variable — no change of variable, no inverse function

The obstruction to instantiating the barrier estimate was never the analysis: it was that Olver's
theorem is stated in the Liouville variable `ξ = ∫√Q`, whose inverse has no closed form, so applying
it requires constructing that inverse in Lean.  That detour is unnecessary.

Writing the exact solution of `Φ'' = QΦ` as `Φ = G·R` against the Liouville–Green approximant
`G = A e^{−Ξ}`, `A = Q^{−1/4}`, `Ξ' = A^{−2}`, the Wronskian `H = Φ'G − ΦG'` satisfies
`H' = −A''e^{−Ξ}Φ`, and the ratio satisfies `R' = H e^{2Ξ}/A²`.  A single integration by parts,
against the primitive `(e^{2Ξ(t)} − e^{2Ξ(y)})/2` of `e^{2Ξ}/A²` chosen to vanish at `y`, collapses
the nested integral to **one** Volterra equation with a bounded kernel — no Fubini, no change of
variable, the phase entering only as the explicit function `Ξ`.

`formal/GaloisForLFunctions/HTGeometry/LiouvilleGreenPhaseErrorBound.lean` and
`formal/GaloisForLFunctions/HTGeometry/LiouvilleGreenOde.lean`, both wired into the `HTGeometry`
umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

```text
lgPhaseKernel Ξ ξ t = (1 − exp(−2(Ξ t − Ξ ξ)))/2 ,   0 ≤ · ≤ 1/2 when Ξ ξ ≤ Ξ t
IsPhaseLGSolution b Ξ ψ R a :  R ξ = 1 − ∫_ξ^b lgPhaseKernel Ξ ξ t · ψ t · R t
phase_volterra_defect, phase_volterra_bound
abs_le_exp_of_phaseLG,  abs_sub_one_le_exp_sub_one_of_phaseLG,  phaseLG_two_sided

lgApprox, lgApproxDeriv, lgWronskian, lgRatio
hasDerivAt_lgApprox        G' = (A' − 1/A) e^{−Ξ}
hasDerivAt_lgApproxDeriv   G'' = (A'' + A^{−3}) e^{−Ξ} = Q G + A'' e^{−Ξ}
hasDerivAt_lgWronskian     H' = −(Φ · A'' · e^{−Ξ})
hasDerivAt_lgRatio         R' = H e^{2Ξ}/A²
isPhaseLGSolution_lgRatio  the Volterra equation, by the integration by parts above
lgRatio_two_sided :
    2 − E ≤ Φ(y)/(A(y)e^{−Ξ(y)}) ≤ E ,        E = exp(½ ∫_y^b |A A''|)
```

`A A'' = Q^{−1/4}(Q^{−1/4})''` is exactly Olver's error-control density, and the estimate is stated
with `y`-integrals throughout.  For the prolate barrier `∫|A A''| = O(1)` on `[2√s, 1−ε]`, so
`E = O(1)`: precision `σ = 0`.

### The remaining obstruction, stated exactly

`lgRatio_two_sided` describes the solution *normalized to the approximant at the right endpoint* —
the recessive branch.  The prolate mode is a different solution, and the Wronskian
`W = Φ'Φ_r − ΦΦ_r'` between them is constant, with

```text
Φ(b)/Φ(y) ≤ Φ_r(b)/Φ_r(y)      ⟺      W ≤ 0      ⟺      v ≥ w at one point,
```

`v = −Φ'/Φ` and `w = −Φ_r'/Φ_r`.  A *small* `W` is not enough: the dominant branch grows by
`e^{2Ξ(b)}`, so only the sign is usable.  And `v ≥ w` at a point is again a lower bound on `v` of
precision `O(1)` against `√Q` — which is what Liouville–Green itself would provide, so the argument
closes on itself.

What breaks the circle is the boundary condition the mode actually satisfies.  Note that
`Ξ(1) = ∫^1 √Q` **converges** (`√Q ≍ c(1−y)^{−1/2}`), so at `y = 1` the recessive/dominant
distinction degenerates — as it must, `y = 1` being a regular singular point where the natural basis
is (analytic, logarithmic), not (recessive, dominant).  The prolate mode is the analytic one, and
its decomposition in the Liouville–Green basis is fixed by matching at that point.

That is precisely what the corpus's Dunster layer already does on the *radial* side
(`ProlateDunsterEndpointCoefficientBounds`: `|F_regular| ≤ 18/c`, `|F_log − π/4| ≤ 141/c`).  The
band-side mirror of that layer — Frobenius/Bessel matching at `y = 1⁻` — is the one remaining input
for `(β)`'s upper half, and it is a construction of the same shape as one the corpus already owns.

## The bridge from the Liouville–Green branch to the actual mode, and the endpoint model identified

`lgRatio_two_sided` describes one distinguished solution — the one normalized to the approximant at
the right endpoint.  The bridge to an arbitrary solution of the same equation is the Wronskian, and
it is now formal.

`formal/GaloisForLFunctions/HTGeometry/DecayRatioComparison.lean`, wired into the `HTGeometry`
umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

```text
solutionWronskian Φ Φ' Ψ Ψ' y = Φ' y · Ψ y − Φ y · Ψ' y
hasDerivAt_solutionWronskian, solutionWronskian_const     it is constant along v'' = P v
solutionWronskian_nonpos_iff :   W ≤ 0  ↔  Φ'/Φ ≤ Ψ'/Ψ
ratio_le_of_solutionWronskian_nonpos :
    W ≤ 0  ⟹  Φ(b)/Φ(a) ≤ Ψ(b)/Ψ(a)
```

So the leakage upper bound reduces to **one sign**: with `Ψ` the Liouville–Green branch and `Φ` the
prolate mode, `W ≤ 0` transfers the whole two-sided estimate to the mode.  Only the sign is usable —
on a barrier the two branches differ by `e^{2Ξ(b)}`, so a merely small `W` carries no information.

### What fixes the sign, computed

The sign is decided at `y = 1`, and the endpoint model is now identified explicitly.  Writing
`u = 1 − y` and `K = χ + c²`, the Sturm form `((1−y²)Φ')' = (χ + c²y²)Φ` becomes, to leading order,

```text
(u Φ_u)_u = (K/2) Φ ,
```

and the substitution `z = √(2K u)` — so `z ≍ 1` exactly when `1 − y ≍ c^(−2)`, the scale at which
the Liouville–Green window must stop — turns it into

```text
Φ_zz + (1/z) Φ_z − Φ = 0 ,
```

the **modified** Bessel equation of order zero.  So the band-side endpoint model is `I₀`, `K₀` — not
`J₀`, `Y₀`; the band side of the endpoint is the forbidden region, whereas the radial side that the
corpus's Dunster layer already treats is the allowed one.

The mode is analytic at `y = 1`, hence the `I₀` branch, and `I₀` is the branch that *grows inward* —
which is the Liouville–Green recessive branch.  So the sign is the expected one, and the content of
the remaining work is the quantitative matching at `z ≍ 1`.

Two consequences worth recording.  First, the normal-form potential

```text
Q̂ = (χ + c²y²)/(1−y²) − (1−y²)^(−2)
```

is **negative** for `1 − y² < 1/K`: the barrier ends at exactly the scale `c^(−2)`, and beyond it the
normal form is the Euler equation `W'' + W/(4(1−y)²) = 0` of an exponent-`(0,0)` singularity, whose
solutions are `√u` and `√u log u`.  That is why no crude comparison of `v` against `√Q̂` can decide
the sign there — both are `Θ(c²)` at the matching point and the constants decide.

Second, this is a construction of the same shape as one the corpus owns: the radial layer
(`CCMFirstRowDunsterModel`, `ProlateDunsterEndpointVolterra`,
`ProlateDunsterEndpointCoefficientBounds`, `ProlateDunsterUniformTransfer`) does exactly this with
`besselJ0` in place of `I₀`.  mathlib has neither; the corpus built `besselJ0` for the radial side,
and the band side needs `besselI0` built the same way.

### `(β)`'s upper half, remaining

```text
sharp action                     prolateAngleAction_sub_bounds              ✔
interior mass from below         mass_lower_of_fluxBound            σ = 1/2 ✔
exterior mass from above         integral_Ioi_one_radialProlate_sq_le  σ = 0 ✔
mass balance → leakage           leakage_upper_of_mass_bounds              ✔
Liouville–Green, original variable  lgRatio_two_sided                σ = 0 ✔
branch → actual mode             ratio_le_of_solutionWronskian_nonpos      ✔
```

One item: the modified-Bessel endpoint layer at `z = c√(2(1−y))`, giving `W ≤ 0`.

## The modified Bessel function of order zero, built

The endpoint model identified in the previous entry needs `I₀`, which mathlib does not have and the
corpus did not have either — it built `besselJ0` for the radial side and nothing for the band side.

`formal/GaloisForLFunctions/RHTower/BesselIZeroODE.lean`, wired into the `RHTower` umbrella, axioms
`[propext, Classical.choice, Quot.sound]`:

```text
besselI0 u            = (1/π) ∫_0^π cosh(u sin θ) dθ
besselI0Deriv u       = (1/π) ∫_0^π sin θ · sinh(u sin θ) dθ
besselI0SecondDeriv u = (1/π) ∫_0^π sin²θ · cosh(u sin θ) dθ

abs_sinh_le, cosh_le_cosh_of_abs_le, abs_mul_sin_le
hasDerivAt_besselI0, hasDerivAt_besselI0Deriv        differentiation under the integral
integral_sin_mul_sinh_eq                            the integration by parts
besselI0SecondDeriv_sub_besselI0
besselI0_ode :   I₀'' + I₀'/u − I₀ = 0
besselI0_zero, besselI0_pos, besselI0Deriv_nonneg, monotoneOn_besselI0
besselI0Deriv_le_besselI0,  besselI0_logDeriv_le_one :   I₀'/I₀ ≤ 1
```

The construction mirrors the corpus's `besselJ0` line for line with the circular functions replaced
by hyperbolic ones; the one structural difference is the domination.  `cos` is bounded, `cosh` is
not, so differentiation under the integral sign is justified on `Metric.ball u 1` with the bounds
`sinh(|u|+1)` and `cosh(|u|+1)` rather than on the whole line with the bound `1`.

`besselI0_logDeriv_le_one` is the one qualitative fact the matching will use: pointwise
`sin θ · sinh(u sin θ) ≤ cosh(u sin θ)` because `sin θ ≤ 1` and `sinh ≤ cosh`, so the analytic
branch's logarithmic derivative never exceeds that of `e^z`.

### What the matching still needs

With `I₀` in hand, the band-side endpoint layer is the mirror of the corpus's radial one:

```text
radial (allowed, J₀)                        band (forbidden, I₀)
CCMFirstRowDunsterModel                     the I₀ model at z = c√(2(1−y))
ProlateDunsterEndpointWronskian             endpoint Wronskian values
ProlateDunsterEndpointVolterra              endpoint-anchored transport
ProlateDunsterEndpointCoefficientBounds     |F_regular| ≤ 18/c, |F_log − π/4| ≤ 141/c
ProlateDunsterUniformTransfer               the uniform O(1/c) transfer
```

and its output is the sign `W ≤ 0` that `ratio_le_of_solutionWronskian_nonpos` consumes.  Note that
the comparison cannot be done by inspecting `I₀'/I₀` against the Liouville–Green profile directly:
in the `z` variable both are `1 + O(1/z)` at the matching point `z ≍ 1`, so the constants decide,
which is exactly what the Volterra transfer computes.

## The band-side comparison equation

`formal/GaloisForLFunctions/RHTower/BesselIZeroModel.lean`, wired into the `RHTower` umbrella,
axioms `[propext, Classical.choice, Quot.sound]`:

```text
besselIModel c ξ x            = I₀(c ξ x)
besselIModelDeriv, besselIModelSecondDeriv
hasDerivAt_besselIModel, hasDerivAt_besselIModelDeriv
besselIModel_ode :
    V'' + (ξ'/ξ − ξ''/ξ') V' − c² (ξ')² V = 0
```

exactly, for every `c` and every phase `ξ`, with nothing approximated: the second derivative
contributes `c²ξ'² I₀ − (cξ'²/ξ) I₀' + c ξ'' I₀'` by `besselI0_ode`, and the first-order coefficient
is exactly the negative of the two `I₀'` terms.

This is the band-side counterpart of `CCMFirstRowDunsterModel.lgBesselModel_ode`, with the sign of
the zero-order term reversed — the band endpoint is the forbidden region.  It is stated for an
arbitrary phase rather than for a fixed one, so the choice of band-side Liouville variable can be
made when the defect estimate is written.

### The band-side layer, remaining

```text
radial (allowed, J₀)                          band (forbidden, I₀)
besselJ0, besselJ0_ode                        besselI0, besselI0_ode                    ✔
CCMFirstRowDunsterModel.lgBesselModel_ode     besselIModel_ode                          ✔
xiEndpointPhase, xiSpeed, xiAmplitude         the band Liouville variable               —
lgNormalFormDefect + its mass bound           the band defect, O(1)                     —
ProlateDunsterEndpointWronskian               endpoint Wronskian values                 —
ProlateDunsterEndpointVolterra                endpoint-anchored transport               —
ProlateDunsterEndpointCoefficientBounds       |F_regular|, |F_log − π/4| = O(1/c)       —
```

whose output is the sign `W ≤ 0` consumed by `ratio_le_of_solutionWronskian_nonpos`.

## The band-side Liouville variable

`formal/GaloisForLFunctions/RHTower/BandEndpointPhase.lean`, wired into the `RHTower` umbrella,
axioms `[propext, Classical.choice, Quot.sound]`:

```text
bandEndpointPhase s y = ∫_{arcsin y}^{π/2} √(sin²θ − s) dθ
bandEndpointPhase_one, bandEndpointPhase_nonneg, bandEndpointPhase_pos
prolateWKBProfile_eq_div :   √((y²−s)/(1−y²)) = √(y²−s)/√(1−y²)
hasDerivAt_bandEndpointPhase :  Ξ_s' (y) = −√((y²−s)/(1−y²))
sq_prolateWKBProfile :          (Ξ_s')² = (y²−s)/(1−y²)
```

so `c²(Ξ_s')² = (χ + c²y²)/(1−y²)` exactly with `χ = −sc²` — the phase for which the modified-Bessel
model `I₀(c Ξ_s)` carries the right leading potential.

The point of the angular form is that it is not an improper integral at all: `∫_y^1 √((t²−s)/(1−t²))dt`
has an inverse-square-root singularity at the endpoint, but `∫_{arcsin y}^{π/2} √(sin²θ − s) dθ` is a
continuous integrand on a compact interval, and the `y`-derivative comes out by the chain rule
against `Real.hasDerivAt_arcsin`.  The same device removed the singularity from the sharp action
earlier on this card.

`Ξ_s` vanishes at `y = 1` and behaves like `√(1−s)·√(2(1−y))` there, so `c Ξ_s ≍ 1` exactly when
`1 − y ≍ c^(−2)` — the scale at which the Liouville–Green window stops and the endpoint model takes
over, which is what makes the two windows overlap.

### The band-side layer

```text
radial (allowed, J₀)                          band (forbidden, I₀)
besselJ0, besselJ0_ode                        besselI0, besselI0_ode                    ✔
CCMFirstRowDunsterModel.lgBesselModel_ode     besselIModel_ode                          ✔
xiEndpointPhase, xiSpeed                      bandEndpointPhase, hasDerivAt_…           ✔
lgNormalFormDefect + its mass bound           the band defect, O(1)                     —
ProlateDunsterEndpointWronskian               endpoint Wronskian values                 —
ProlateDunsterEndpointVolterra                endpoint-anchored transport               —
ProlateDunsterEndpointCoefficientBounds       |F_regular|, |F_log − π/4| = O(1/c)       —
```

## The model drift is elementary — the square root cancels

The comparison equation's first-order coefficient is `Ξ'/Ξ − Ξ''/Ξ'`, and the second term looked as
though it would carry the square root of the WKB profile.  It does not.

`BandEndpointPhase.lean` (extended; wired, axioms `[propext, Classical.choice, Quot.sound]`):

```text
hasDerivAt_prolateWKBArg :
    d/dy [(y²−s)/(1−y²)] = 2y(1−s)/(1−y²)²
hasDerivAt_prolateWKBProfile :
    Ξ'' = −P' ,   P' = (2y(1−s)/(1−y²)²)/(2P)
bandModelDrift s y = y(1−s)/((1−y²)(y²−s))
secondDeriv_div_deriv_bandEndpointPhase :
    Ξ''/Ξ' = bandModelDrift s y
```

The cancellation is exact: `Ξ''/Ξ' = P'/P = (2y(1−s)/(1−y²)²)/(2P²)` and `P² = (y²−s)/(1−y²)`, so the
profile disappears entirely and the ratio is a rational function of `y` with the two poles one
expects — at the turning point `y² = s` and at the endpoint `y² = 1`.

Near the endpoint `bandModelDrift → 1/(2(1−y))` and `Ξ'/Ξ → −1/(2(1−y))`, so the comparison drift
`B_m = Ξ'/Ξ − Ξ''/Ξ' → −1/(1−y)`, whose contribution `B_m²/4 + B_m'/2 → 1/(4(1−y)²) − 1/(2(1−y)²)`
cancels the `−1/(1−y²)² → −1/(4(1−y)²)` of the true normal form.  That cancellation of the leading
`(1−y)^(−2)` singularities is exactly why the band defect is `O(1)` rather than `O(c²)`, and it is
now a computation on explicit rational functions rather than an asymptotic claim.

### The band-side layer

```text
radial (allowed, J₀)                          band (forbidden, I₀)
besselJ0, besselJ0_ode                        besselI0, besselI0_ode                    ✔
CCMFirstRowDunsterModel.lgBesselModel_ode     besselIModel_ode                          ✔
xiEndpointPhase, xiSpeed                      bandEndpointPhase, hasDerivAt_…           ✔
xiSpeedDeriv                                  hasDerivAt_prolateWKBProfile,
                                              secondDeriv_div_deriv_…                   ✔
lgNormalFormDefect + its mass bound           the band defect, O(1)                     —
ProlateDunsterEndpointWronskian               endpoint Wronskian values                 —
ProlateDunsterEndpointVolterra                endpoint-anchored transport               —
ProlateDunsterEndpointCoefficientBounds       |F_regular|, |F_log − π/4| = O(1/c)       —
```

## The comparison defect: the algebraic collapse

`formal/GaloisForLFunctions/HTGeometry/LiouvilleGreenDriftAlgebra.lean`, wired into the `HTGeometry`
umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

```text
lgDrift Ξ Ξ' D y = Ξ'(y)/Ξ(y) − D(y)
hasDerivAt_lgDrift :   B' = Ξ''/Ξ − (Ξ')²/Ξ² − D'
lgDrift_normalForm :   with Ξ'' = Ξ'·D,
    B²/4 + B'/2 = −(Ξ')²/(4Ξ²) + D²/4 − D'/2
lgDrift_normalForm_of_hasDerivAt
```

`B = Ξ'/Ξ − Ξ''/Ξ'` is the first-order coefficient of the comparison equation `besselIModel_ode`, and
`B²/4 + B'/2` is what it contributes on passing to normal form.  The identity says the cross terms
`Ξ'D/Ξ` cancel and — the point — **no `Ξ''/Ξ` survives**: the model's normal-form potential is built
from `(Ξ')²/Ξ²` and from `D` alone.

For the prolate band `D = bandModelDrift` is rational (the previous entry), so the whole comparison
carries exactly one transcendental ingredient, `(Ξ')²/Ξ²`.  Writing the defect against the true
normal-form potential `Q̂ = c²(Ξ')² − (1−y²)^(−2)` and noting that the two `c²(Ξ')²` cancel — that is
what the phase was chosen for — the defect is

```text
(Ξ')²/(4Ξ²) − 1/(1−y²)² − D²/4 + D'/2 ,
```

with no `c` in it at all.  At the endpoint each of the four terms is `Θ((1−y)^(−2))` — respectively
`1/16`, `−1/4`, `−1/16`, `+1/4` times `(1−y)^(−2)` — and they sum to zero.  That is the cancellation
that makes the comparison defect `O(1)` rather than `O(c²)`, and it is now an identity between
explicit functions rather than an asymptotic assertion.

### The band-side layer

```text
radial (allowed, J₀)                          band (forbidden, I₀)
besselJ0, besselJ0_ode                        besselI0, besselI0_ode                    ✔
CCMFirstRowDunsterModel.lgBesselModel_ode     besselIModel_ode                          ✔
xiEndpointPhase, xiSpeed, xiSpeedDeriv        bandEndpointPhase + both derivatives      ✔
lgNormalFormDefect (its algebra)              lgDrift_normalForm                        ✔
its mass bound                                the O(1) mass bound                       —
ProlateDunsterEndpointWronskian               endpoint Wronskian values                 —
ProlateDunsterEndpointVolterra                endpoint-anchored transport               —
ProlateDunsterEndpointCoefficientBounds       |F_regular|, |F_log − π/4| = O(1/c)       —
```

## The band comparison defect is a simple pole, and its Liouville mass is finite

The band-side mirror of the radial Dunster layer is now built through its analytic core.  Writing the
band equation and its modified-Bessel model both in *drift* form — first-order coefficient kept, the
difference pushed entirely into the potential — the aperture cancels identically and the defect is

```text
a = 1/(1−y²)² + B²/4 + B'/2 ,      B = Ξ'/Ξ − Ξ''/Ξ' ,
```

with **no `c` in it at all**.  This is the exact analogue of `lgNormalFormDefect` on the radial side,
and it is the quantity whose pole order decides everything: a simple pole has finite mass against the
band's Liouville measure `dy/|Ξ'|`, which vanishes like `√(1−y)` at the endpoint; a double pole would
not.

### The cancellation, made algebraic

`lgDrift_normalForm` already reduced `B²/4 + B'/2` to `−(Ξ')²/(4Ξ²) + D²/4 − D'/2` with `D = Ξ''/Ξ'`
rational.  The remaining step is to remove the *explicit* singular part of `Ξ'/Ξ`.  Setting

```text
L_s(y) = Ξ'/Ξ + y/(1−y²)      (bandPhaseLogDefect)
```

and substituting `Ξ'/Ξ = −y/(1−y²) + L` gives, as an identity between explicit functions
(`bandComparisonDefect_eq`, `field_simp; ring` after the substitution — `Ξ` and `P` never need to be
evaluated, they cancel as atoms):

```text
a = (y⁴ + (3−8s)y² + 2s² + 2s) / (4(1−y²)(y²−s)²)  +  yL/(2(1−y²))  −  L²/4 .
```

The rational part is `bandDefectAlg`.  Its numerator is what the double-pole cancellation produces:
the naive numerator `−y⁶ + (8s−2)y⁴ + (3−10s−2s²)y² + 2s(s+1)` **vanishes at `y² = 1`**, and dividing
by `1 − y²` leaves `y⁴ + (3−8s)y² + 2s² + 2s`.  That single divisibility is the whole content of the
`(1−y)^(−2)` cancellation, now a polynomial identity rather than an asymptotic assertion.

### The logarithmic defect is bounded

`|L_s(y)| ≤ 2` for `0 ≤ s ≤ 1/2`, `0 < y < 1`, `s < y²` (`abs_bandPhaseLogDefect_le`) — uniformly, and
up to the endpoint.  Both directions come from a sharp two-sided squeeze of the phase itself:

```text
√(y²−s)·√(2(1−y))   ≤   Ξ_s(y)   ≤   √(1−s)·2√(1−y)/√(1+y)
```

(`sharp_le_bandEndpointPhase`, `bandEndpointPhase_le_sharp`).  Both sides agree to relative order
`1−y`, which is exactly the accuracy at which `Ξ'/Ξ` separates from `−y/(1−y²)`.  The intermediate
step is the same squeeze for `arccos`,

```text
√(2(1−y))  ≤  arccos y  ≤  2√(1−y)/√(1+y) ,
```

proved by comparing derivatives on the *open* interval — both derivatives blow up at `y = 1`, so the
comparison is carried to the endpoint by continuity alone (`le_of_continuousOn_of_deriv_nonneg`, a new
reusable form of the monotonicity criterion).  The upper half of `|L| ≤ 2` then needs only
`√(1−z) ≥ 1−z`; the lower half needs only `1 + y ≤ 2`.

### The bound and the mass

```text
|a| ≤ 100/(1−y²)          on 1/2 ≤ y < 1,  0 ≤ s ≤ 1/8      abs_bandComparisonDefect_le
∫_A^B |a|/P ≤ 500         for every 1/2 < A ≤ B < 1          integral_bandDefectMass_le
```

The mass bound is uniform in the aperture and in the separation parameter, and — as on the radial
side — it is stated on compact subintervals with a bound uniform as `B → 1`, so no improper integral
is ever formed.  The majorant is `200√2/√(1−y²)`, whose exact primitive is `arcsin`.

New modules: `RHTower.BandEndpointPhaseSharp`, `RHTower.BandPhaseLogDefect`,
`RHTower.BandComparisonDefect`, `RHTower.BandDefectMass`, plus the reusable
`HTGeometry.AbstractComparisonTransport` (drift-form Wronskian transport, amplitude `√|m|`, and the
normal-form-to-drift-form passage, all for an arbitrary integrating factor, so that the same
statements serve an oscillatory comparison and a barrier one).

### The assembly this unlocks — and why the `σ₊ ≈ 24` problem disappears

The precision audit recorded above found item 1's loss `6·log((1−√s)/(1−b))` fatal *because the plan
pushed the matching point `b` to within `c^(−2)` of the endpoint*.  With a modified-Bessel model
covering the endpoint collar, `b` never moves: the collar is `[1−δ, 1]` for an **absolute** `δ`, and
item 1's loss is `6·log((1−√s)/δ)`, a constant.  `σ₊` collapses from `24` to `0`.

Nor is a sharp `O(1/c)` comparison needed on the collar.  The consumer allows `c^(±3/2)`; a two-sided
bound with absolute constants is `σ = 0` and is inside the budget with room to spare.  Concretely, on
`[1−δ, 1]`, with `V = I₀(cΞ)` the model and `R = Φ/V`:

```text
R(y) = 1 − ∫_y^1 K(y,t) a(t) R(t) dt ,     K(y,t) = m̃(t)V(t)² ∫_y^t dτ/(m̃V²) ,   m̃ = Ξ/P ,
```

and since `V` is antitone in `y` the crude bound `V(τ) ≥ V(t)` for `τ ≤ t` already gives

```text
K(y,t) ≤ m̃(t)·∫_y^t dτ/m̃(τ) ≤ 6(1−t)·log((1−y)/(1−t)) ,
|a(t)|K(y,t) ≤ 600·log((1−y)/(1−t)) ,      ∫_y^1 |a|K ≤ 600(1−y) ,
```

using `(1−y)√2√(1+y) ≤ m̃ ≤ 6(1−y)` from the phase squeeze.  Choosing `δ = 1/4000` makes the total
kernel mass at most `1/4`, and the elementary contraction

> `M = max_{[1−δ,1]}|R|`, `M ≤ 1 + M/4`, hence `M ≤ 4/3` and `|R − 1| ≤ 1/3`

replaces Grönwall entirely — no continuity of the kernel at the endpoint is needed, which matters
because `|a|·K` really does diverge logarithmically at `t = 1` while remaining integrable.  The
conclusion is `Φ(1−δ)/Φ(1) ∈ [2/3, 4/3]·I₀(cΞ(1−δ))`, i.e. the endpoint layer costs `σ = 0` beyond the
`c^(−1/2)` that `I₀`'s own envelope already carries.

Should the sharp constant `A_n` ever be wanted rather than the two-sided ladder, the same kernel obeys
the far better bound `K(y,t) ≤ 1/(2cP(t))` — from `I₀(z₂)/I₀(z₁) ≤ e^(z₂−z₁)`, which is
`besselI0Deriv_le_besselI0` integrated — making the total mass `≤ 250/c` and the relative error
`O(1/c)`.  That is the band twin of `ProlateDunsterEndpointCoefficientBounds`.

### The band-side layer

```text
besselJ0/besselJ0_ode            → besselI0/besselI0_ode                      ✔
lgBesselModel_ode                → besselIModel_ode                           ✔
xiEndpointPhase/xiSpeed/Deriv    → bandEndpointPhase + both derivatives       ✔
sharp endpoint squeeze of ξ      → bandEndpointPhase_le_sharp + lower         ✔
phaseLogDefect bounds            → abs_bandPhaseLogDefect_le                  ✔
lgNormalFormDefect (algebra)     → bandComparisonDefect_eq                    ✔
|lgNormalFormDefect| ≤ 40/(x²−1) → abs_bandComparisonDefect_le                ✔
its Liouville mass               → integral_bandDefectMass_le                 ✔
weighted Wronskian transport     → HTGeometry.hasDerivAt_driftWronskian       ✔
the model V = I₀(cΞ) on the band → —
endpoint Wronskian value (zero)  → —
the kernel bound and contraction → —
```

## The band endpoint layer is closed: the solution is trapped by the modified-Bessel model

The comparison is now a theorem, with absolute constants and no asymptotics:

```text
bandModel_le_and_le_bandModel :
  0 ≤ s ≤ 1/8,  0 < c,  1/2 < α < 1,  600(1−α) ≤ 1/4,
  U solves  U'' = −B U' − (−c²P² + a) U  on (α,1),   U continuous on [α,1],  U(1) = 1
  ⟹  (2/3)·I₀(cΞ(y))  ≤  U(y)  ≤  (4/3)·I₀(cΞ(y))     for all y ∈ [α,1] .
```

`B = Ξ'/Ξ − Ξ''/Ξ'` is the band's own first-order coefficient, `a = bandComparisonDefect` its own
defect, and the aperture term `−c²P²` is shared with the model exactly — nothing about `c` enters the
constants.

### What made it work, in order

**The Liouville weight vanishes linearly.**  `m̃ = Ξ/P` satisfies `m̃' = m̃ B`
(`hasDerivAt_bandLiouvilleWeight`) and, from the phase squeeze,

```text
(1−y) ≤ m̃(y) ≤ 6(1−y)      on 1/2 ≤ y ≤ 1,  s ≤ 1/8 .
```

Multiplied against the simple pole this gives an outright bound on the transported density,
`m̃|a| ≤ 600` — the pole and the weight cancelling exactly.

**The Wronskian is continuous to the endpoint, and vanishes there.**  The obstacle was that the
model's derivative `V' = −c P I₀'(cΞ)` blows up at `y = 1`.  But the Wronskian only ever sees the
product

```text
m̃ V' = −c Ξ I₀'(cΞ) ,
```

because `m̃ P = Ξ`.  Rewritten that way (`bandWronskian_eqOn`) the Wronskian is manifestly continuous
on the closed collar, and `m̃(1) = 0` gives `W(1) = 0` outright.  So the endpoint-anchored transport

```text
W(τ) = −∫_τ^1 m̃ a U V
```

is an ordinary fundamental-theorem statement on a closed interval — **no improper integral, no
limiting argument, and no second (logarithmic) branch of the model**.  On the radial side the same
step costs the 307-line `ProlateDunsterEndpointWronskian` plus a `K₀`-analogue; here it costs one
algebraic identity.

**The double integral is bounded without Fubini.**  From `V` antitone and `|R| ≤ M`,

```text
|W(τ)| ≤ 600 M V(τ)² (1−τ) ,        |R'| = |W|/(m̃V²) ≤ 600 M ,
```

the second step using `m̃ ≥ 1−y` to cancel the `(1−τ)`.  Integrating once more,
`|R(y) − 1| ≤ M·600(1−α)`.  The nested estimate never needs the order of integration swapped, and
never needs the exponential decay of `1/V²`.

**The contraction closes it.**  `abs_sub_one_le_of_self_bound`: a self-referential bound with mass
`κ < 1` forces `max|R| ≤ 1/(1−κ)` and `|R−1| ≤ κ/(1−κ)`.  With `κ = 600(1−α) ≤ 1/4` the ratio is
inside `[2/3, 4/3]`.  Grönwall is not used and could not be: the kernel density genuinely diverges
logarithmically at `t = 1`.

### The band-side layer

```text
besselJ0/besselJ0_ode            → besselI0/besselI0_ode                      ✔
lgBesselModel_ode                → besselIModel_ode, bandModel_ode            ✔
xiEndpointPhase/xiSpeed/Deriv    → bandEndpointPhase + both derivatives       ✔
sharp endpoint squeeze of ξ      → bandEndpointPhase_le_sharp + lower         ✔
phaseLogDefect bounds            → abs_bandPhaseLogDefect_le                  ✔
lgNormalFormDefect (algebra)     → bandComparisonDefect_eq                    ✔
|lgNormalFormDefect| ≤ 40/(x²−1) → abs_bandComparisonDefect_le                ✔
its Liouville mass               → integral_bandDefectMass_le                 ✔
lgWeight, its integrating law    → bandLiouvilleWeight + its derivative law   ✔
weighted Wronskian transport     → hasDerivAt_bandWronskian                   ✔
endpoint Wronskian value         → bandWronskian_one (identically zero)       ✔
endpoint-anchored Volterra       → bandWronskian_eq_neg_integral              ✔
coefficient bounds O(1/c)        → abs_bandRatio_sub_one_le (σ = 0 version)   ✔
```

New modules: `RHTower.BandBesselModel`, `RHTower.BandLiouvilleWeight`,
`RHTower.BandComparisonVolterra`, `HTGeometry.VolterraContraction`.

### What remains for `(β)`

Two mechanical steps and one assembly:

1. **The passage from the prolate angular equation to `U`.**  `u = Φ·√(1−y²)` removes the first-order
   term (`Q = −c²P² + (1−y²)^(−2)`), and `U = u/√m̃` moves it into drift form with coefficient `B`.
   Both are instances of `HTGeometry.hasDerivAt_comparisonQuotientDeriv_driftAmplitude`; the only
   missing ingredient is that `bandFirstOrderCoeffDeriv` really is the derivative of
   `bandFirstOrderCoeff`, which is the same quotient-rule computation as
   `hasDerivAt_bandLiouvilleWeight`.
2. **The amplitude ratio.**  `Φ = U·A` with `A² = m̃/(1−y²) ∈ [√2/√(1+y), 6/(1+y)] ⊂ [0.8, 4]` on the
   collar, and `A(1) = 1`.  Pure phase-squeeze arithmetic.
3. **The assembly.**  `Φ(α)/Φ(1) ≍ I₀(cΞ(α))` with absolute constants; `Φ(√s)/Φ(α)` from the sharp
   action with the now-constant loss `6·log((1−√s)/(1−α))`; then items 2 and 3 as before.

## The endpoint layer, closed for the actual prolate mode

```text
prolateBand_le_and_le :
  0 ≤ s ≤ 1/8,  0 < c,  1/2 < α < 1,  600(1−α) ≤ 1/4,
  Phi solves  (1−y²)Phi'' − 2y Phi' + (sc² − c²y²) Phi = 0  on (α,1),
  Phi, Phi' continuous on [α,1],   Phi(1) = 1
  ⟹  (1/3)·I₀(cΞ_s(y))  ≤  Phi(y)  ≤  3·I₀(cΞ_s(y))     for all y ∈ [α,1] .
```

This is the last named input `(β)` was waiting for.  It is unconditional, uniform in the aperture,
and uniform in the separation parameter through `s ≤ 1/8` alone.

### The two passages, and the two places the endpoint could have bitten

`u = √(1−y²)·Phi` removes the first-order term — the contributions `2w'Phi'` and `w·(2y/(1−y²))Phi'`
cancel identically — leaving `u'' + Qu = 0` with `Q = (1−y²)^(−2) − c²P²`.  Dividing by the amplitude
`g = √m̃` puts it in drift form with the model's own coefficient `B`, and

```text
Q + B²/4 + B'/2 = −c²P² + bandComparisonDefect ,
```

so the aperture term is shared exactly and only the `c`-free defect separates the two equations.  Both
steps are instances of the abstract `HTGeometry.AbstractComparisonTransport`.

Two quantities are genuinely singular at `y = 1` and had to be handled without ever evaluating their
factors separately.

**The amplitude ratio** `A = g/w`, i.e. `A² = m̃/(1−y²)`.  The sharp phase squeeze gives

```text
√2/√(1+y)  ≤  A²  ≤  2√(1−s)/(√(y²−s)(1+y)) ,
```

two explicit continuous functions that both equal `1` at `y = 1`.  Hence `A → 1`
(`tendsto_bandAmplitudeRatio`), and with the value `1` built into the definition `A` is continuous on
the closed collar, with `1/2 ≤ A ≤ 2` there.  This is what lets the comparison unknown
`U = Phi/A` be normalised *at* the endpoint.

**The transported derivative** `m̃·U'`.  Neither factor extends: `m̃ → 0` while `U' → ∞`.  But
`m̃ = g²` and `Dg = gB/2`, so

```text
m̃ U' = g(u' − uB/2) = A·( −y·Phi + (1−y²)Phi' − ((1−y²)B/2)·Phi ) ,
```

using `w w' = −y` and `w² = 1−y²`.  The only singular ingredient left is `(1−y²)B`, and

```text
(1−y²)B = (1−y²)L − y − y(1−s)/(y²−s)   →   0 − 1 − 1 = −2 ,
```

because `L = bandPhaseLogDefect` is bounded by `2` (so `(1−y²)L → 0` by squeeze) and the rest is
rational.  `bandScaledCoeff`, defined with the value `−2` at the endpoint, is therefore continuous on
the closed collar — which is exactly the hypothesis the Wronskian's continuity needs.  (The Volterra
module's hypothesis was correspondingly weakened from `ContinuousOn DU` to
`ContinuousOn (m̃ · DU)`, which is all it ever used.)

New modules: `RHTower.BandNormalFormPassage`, `RHTower.BandAmplitudeRatio`,
`RHTower.BandSolutionComparison`.

### `(β)`: what is left

```text
sharp action                      prolateAngleAction_sub_bounds          ✔ σ = 0
interior mass from below          mass_lower_of_fluxBound                ✔ σ = 1/2
exterior mass from above          integral_Ioi_one_radialProlate_sq_le   ✔ σ = 0
endpoint collar, two-sided        prolateBand_le_and_le                  ✔ σ = 0
WKB transport α → 2√s             prolate_endpoint_le_log / sharp lower  ✔ σ = 0 (α fixed)
```

Only the assembly remains: chain `Phi(2√s)/Phi(1) = [Phi(2√s)/Phi(α)]·[Phi(α)/Phi(1)]` with the second
factor `≍ I₀(cΞ(α))` and the first from the sharp action with the now-constant loss
`6·log((1−2√s)/(1−α))`, then feed the ratio into the interior/exterior mass quotient.  Every factor is
`σ = 0` or `σ = 1/2` against the budget `7/2`.

## `I₀` from below, and the shape of the assembled bound

```text
exp_div_le_besselI0 :   e^z / (2 pi sqrt z)  ≤  I₀(z)      for z ≥ 1 .
```

Proved from the integral representation on the window `|θ − π/2| ≤ 1/√z`, where
`sin θ = cos(θ − π/2) ≥ 1 − 1/(2z)` by `Real.one_sub_sq_div_two_le_cos`, so the integrand is at least
`e^(z−1/2)/2` across a window of length `2/√z`.  The window is chosen, not found: no saddle-point
analysis and no asymptotic expansion enters.

With this the chain closes numerically.  Fix the collar at `α = 1 − 1/2400` and write

```text
Phi(1)/Phi(2√s) = [Phi(1)/Phi(α)] · [Phi(α)/Phi(2√s)] .
```

* `Phi(1) = 1` and `Phi(α) ≥ (1/3)·I₀(cΞ(α)) ≥ (1/3)·e^(cΞ(α))/(2π√(cΞ(α)))`, so the first factor is
  at most `6π √(cΞ(α))·e^(−cΞ(α))`.
* The second factor is `prolate_endpoint_le_log` on `[2√s, α]`, with loss `6·log((1−2√s)/(1−α))
  ≤ 6·log 2400`, an absolute constant now that `α` is fixed.
* `Ξ(α) = ∫_α^1 P` joins the two exponents exactly: `c∫_{2√s}^α P + cΞ(α) = c∫_{2√s}^1 P`, and the
  truncation `∫_{√s}^{2√s} P = O(1/c)` makes that `c·A(s) + O(1)`.

Hence `Phi(1)/Phi(2√s) ≤ C·√c·e^(−cA(s))` and, through `leakage_upper_of_mass_bounds`,

```text
leakage ≤ (C/κ)·(Phi(1)/Phi(2√s))² ≤ C'·c·e^(−2cA(s)) = C'·c^(n+3/2)·e^(−2c) ,
```

using `cA(s) = c − ((2n+1)/4)·log c + O(1)` from the sharp action.  The overhead is `σ = 1`, well
inside the `7/2` budget and — being independent of `n` — invisible in the ladder ratio.

## The barrier ratio is now a theorem

```text
prolateBand_barrier_ratio_lower :
  0 ≤ s ≤ 1/8,  0 < c,  1/2 < α < 1,  600(1−α) ≤ 1/4,
  Phi smooth,  prolateSLAction c Phi = −s c² · Phi on [−1,1],  Phi(1) = 1,
  0 ≤ y₀ ≤ α,  s < y₀²,  Phi > 0 on [y₀,1],  1 ≤ c·Ξ_s(α)
  ⟹  exp( c·Ξ_s(y₀) + 6·log((1−α)/(1−y₀)) ) / (6π·sqrt(c·Ξ_s(α)))  ≤  Phi(y₀) .
```

This is `(β)`'s barrier ratio, from below, at the sharp exponential rate, with overhead `sqrt c` and
absolute constants — and **no `n`-dependence in the overhead**, so it cancels in the ladder ratio.

Three ingredients, each now proved:

* **The collar.**  `prolateBand_le_and_le` traps the mode by `I₀(cΞ)`, and
  `exp_div_le_besselI0` bounds `I₀` below by `e^z/(2π√z)`.  Together
  (`exp_div_le_prolateBand_collar`) `Phi(α) ≥ e^(cΞ(α))/(6π√(cΞ(α)))`.
* **Below the collar.**  `prolate_endpoint_le_log` transports at the WKB rate with loss
  `6·log((1−y₀)/(1−α))`, an absolute constant because `α` is fixed.
* **The join.**  `bandEndpointPhase_sub_eq_integral` — the phase is additive,
  `Ξ_s(a) − Ξ_s(b) = ∫_a^b P` — so `c·Ξ_s(α)` from the collar and
  `c·(Ξ_s(y₀) − Ξ_s(α))` from the transport concatenate to `c·Ξ_s(y₀)` exactly.  No matching
  constant is lost at the seam.

And the seam to the sharp action is definitional:

```text
bandEndpointPhase_sqrt_eq_prolateAngleAction :  Ξ_s(√s) = prolateAngleAction s      (rfl)
```

both being `∫_{arcsin √s}^{π/2} sqrt(sin²θ − s) dθ`.  So with `y₀ ↓ √s` the exponent is `c·A(s)`,
and `prolateAngleAction_sub_bounds` turns that into `c − ((2n+1)/4)·log c + O(1)`.

New module: `RHTower.BandBarrierRatio`.

### `(β)`'s upper half: what is left

```text
sharp action                      prolateAngleAction_sub_bounds      ✔
barrier ratio from below          prolateBand_barrier_ratio_lower    ✔  σ = 1/2
interior mass from below          mass_lower_of_fluxBound            ✔  σ = 1/2
exterior mass from above          integral_Ioi_one_radialProlate_sq_le ✔ σ = 0
scalar leakage balance            leakage_upper_of_mass_bounds       ✔
```

Only the substitution of the ratio into the mass balance remains, plus the arithmetic that turns
`c·A(s)` into `c − ((2n+1)/4) log c + O(1)` under `c·s = 2n+1`.

## `(β)`'s upper half, assembled

```text
prolate_leakage_le_exp_action :
  0 ≤ s ≤ 1/8,  5 ≤ c,  1/2 < α < 1,  600(1−α) ≤ 1/4,
  Phi smooth with prolateSLAction c Phi = −s c² Phi on [−1,1],  Phi(1) = 1,  Phi > 0 on [y₀,1],
  0 ≤ y₀ ≤ α,  s < y₀²,  1 ≤ c·Xi_s(α),
  R the radial mode with R(1) = 1 and its equation,
  0 < w,   w·(Phi(y₀) e^(−E))² ≤ inside,   value² ≤ 1,  value ≠ 0,  0 ≤ leakage,
  ∫_{x>1} R² = inside·leakage/value²
  ⟹
  leakage ≤ (C_ext/c) · ( (6π sqrt(c Xi_s(α)))² e^(2E) / w ) · exp(−2( c Xi_s(y₀)
              + 6 log((1−α)/(1−y₀)) ))
```

with `C_ext = radialProlateExteriorMassConstant`.  Every factor is explicit and every hypothesis is
either an equation the mode satisfies or a quantity the corpus's own lemmas produce:

* `w·(Phi(y₀)e^(−E))² ≤ inside` is exactly what `mass_lower_of_fluxBound` returns, with `w = b−y₀`
  and `E = ∫_{y₀}^b sqrt K/(1−t²)`;
* `∫_{x>1} R² = inside·leakage/value²` is the mass balance defining the leakage;
* the barrier ratio is discharged internally by `prolateBand_barrier_ratio_lower`.

Reading off the orders: `w ≍ 1/c` and `E = O(1)` on a `1/c`-window anchored at `y₀ = 2√s`;
`c·Xi_s(α)` is `≍ c`; and `Xi_s(y₀) = A(s) − O(1/c)` with `Xi_s(√s) = prolateAngleAction s` exactly.
So

```text
leakage ≤ C · c · exp(−2 c A(s)) = C · c^(n+3/2) · e^(−2c) ,
```

the Fuchs upper bound with an `n`-independent overhead `c`, which cancels in the ladder ratio.

New module: `RHTower.ProlateLeakageBarrierAssembly`
(`leakage_le_of_anchor_lower`, `prolate_leakage_le_of_barrier`, `prolate_leakage_le_exp_action`).

### What is left on this card

```text
(α) toolkit                        complete
(β) upper half                     prolate_leakage_le_exp_action        ✔
(β) lower half                     needs: exterior mass from below at the sharp order,
                                          interior mass from above
orthogonal-mode extraction         open
```

## `(β)`'s lower half — first brick: the oscillator energy cannot decay

The exterior mass from below needs, at bottom, that the Bessel normal form keeps a definite
amplitude on the exterior ray.  The corpus had only the upper Grönwall bound on the perturbed
oscillator energy; the lower one is now proved by the mirror argument (`E·e^(−κ/v)` is *monotone*
rather than `E·e^(κ/v)` antitone):

```text
HTGeometry.exp_mul_oscEnergy_le
    oscEnergy a · exp(−(κ/a − κ/u))  ≤  oscEnergy u
RHTower.exp_mul_besselEnergy_le_of_abstract
    besselEnergy a · exp(−(1/4/a − 1/4/u))  ≤  besselEnergy u
```

both axiom-clean and wired.  An envelope bound cannot give this, and it is exactly the input the
mass-retention estimates (`quarter_integral_le_integral_weight_mul_cos_sq_radialPhase`) need in order
to convert "the oscillating square keeps a quarter of the plain mass" into an actual lower bound on
`∫_{x>1} R²`: the plain mass is the energy, and the energy is now bounded below.

Remaining for the lower half: assemble energy-from-below with the mass-retention quarter bound and
the density transfer (`integral_Ioi_abs_radialProlateDensity_sub_besselDensity_le`, already two-sided
in `L¹`), then the interior mass from above, which still needs the turning-layer amplitude at the
sharp order rather than `integral_sq_le_turning_amplitude_envelope`'s `c/√s`.

## Mass from energy — the oscillation is bypassed entirely

The `L²` mass lower bound does **not** need stationary phase.  The exact virial identity

```text
(w w')' = w'² − (1+q) w²
```

integrated over `[α,β]` turns the total energy into twice the mass plus boundary terms:

```text
∫_α^β E  =  2∫ w²  +  ∫ q w²  +  [w w']_α^β ,       E = w² + w'² ,
```

so an interval long compared with the energy ratio must carry mass.  With `|q| ≤ κ/v²` and the two
Grönwall bounds on `E`:

```text
HTGeometry.mass_lower_of_oscEnergy
    ((β−α)·Elow − Ehigh) / (2 + κ/α²)  ≤  ∫_α^β w²
RHTower.besselMass_lower
    ((β−α)·E(α)e^(1/4/β − 1/4/α) − E(α)e^(1/4/α)) / (2 + (1/4)/α²)  ≤  ∫_α^β u J₀(u)² du
```

both axiom-clean and wired.  Note what this replaces: the corpus's van der Corput route
(`OscillatoryMassRetention`, `RadialPSWFMassRetention`) needs a phase, a speed floor and a
monotonicity hypothesis, and returns a *quarter* of the plain mass; the virial identity needs none of
them and returns the mass directly from the energy.  The two are complementary — the virial bound is
what applies when the oscillating factor is the Bessel model itself rather than a bare `cos`.

This closes the first half of `(β)`'s exterior-mass-from-below: the Bessel density carries mass, at
the sharp order in the endpoint energy.  What remains is the transfer of that lower bound through
`integral_Ioi_abs_radialProlateDensity_sub_besselDensity_le` — already two-sided in `L¹` — and the
endpoint-energy normalisation `E(α) ≍ c` at the Dunster matching point.

## The Sturm energy of the radial equation is monotone — no Grönwall needed

The self-adjoint form `(p R')' + Q R = 0` carries two exact identities, each one product rule:

```text
(p R R')' = p R'² − Q R² ,                        the virial identity
((p R')² + p Q R²)' = (p Q)' R² ,                 the Sturm energy
```

`HTGeometry/SturmLiouvilleVirial.lean` (wired, axiom-clean):

```text
hasDerivAt_virial,  hasDerivAt_slEnergy
slEnergy_le_of_monotone     (p Q)' ≥ 0  ⟹  slEnergy is nondecreasing
integral_slEnergy_div_eq    ∫ slEnergy/p = 2 ∫ Q R² + [R · p R']
mass_lower_of_slEnergy      (F₀ · ∫dx/p − B) / (2 Q_max)  ≤  ∫ R²
```

For the radial prolate equation this is decisive: `p = x²−1` and `Q = c²(x²−s)`, so
`p Q = c²(x²−1)(x²−s)` is **increasing on `x > 1`** for `s ≤ 1`.  Hence the Sturm energy is
nondecreasing there outright — the energy floor needed for the exterior mass from below is
`slEnergy` at the Dunster crossing point, and no Grönwall, no perturbation bound and no oscillation
estimate is involved.

That floor is available: `radialProlate_value_ge_thirteen_fortieth_to_crossing` gives `R ≥ 13/40` up
to the crossing, and `radialProlate_deriv_lower_bound_endpoint_collar` the companion derivative
bound.  What remains for `∫_{x>1} R² ≥ κ/c` is arithmetic: evaluate `∫ dx/(x²−1)` on the transport
window, bound the boundary term `[R·pR']` by the energy through `2|R|·|pR'| ≤ slEnergy/√(pQ)`, and
choose the window so that `Q_max ≍ c²` and `∫dx/p ≍ 1/c`.

Note this supersedes the plan recorded above: the Bessel-model detour (density transfer plus
`besselMass_lower`) is no longer needed for the lower half — the energy monotonicity applies to the
actual mode directly.  The Bessel results stand on their own as the model-side statements.

## The energy floor without evaluating anything

The `1/c` exterior lower bound needs an energy *floor*, and the Sturm monotonicity above supplies
only `F ≥ F(α)` with `F(α) = O(1)` — enough for `1/c²`, not for `1/c`.  The extra factor `c` lives in
the amplitude, i.e. in the endpoint matching, and the only way to reach it without evaluating a
Bessel function anywhere is the Wronskian.

```text
HTGeometry.sq_wronskian_le_oscEnergy_mul
    (w₁ w₂' − w₁' w₂)²  ≤  oscEnergy w₁ · oscEnergy w₂
HTGeometry.oscEnergy_lower_of_wronskian
    Wronskian = W,  oscEnergy w₂ ≤ C  ⟹  W²/C ≤ oscEnergy w₁
```

both axiom-clean and wired.  The proof is Lagrange's identity
`(a²+b²)(c²+d²) = (ac+bd)² + (ad−bc)²`, nothing more.

Why this is the right brick.  The two Bessel branches have `u(J₀K′ − J₀′K) = π/4` exactly
(`besselWronskian_eq_pi_div_four`), which in normal-form variables `w₁ = √u J₀`, `w₂ = √u K` is
literally `w₁w₂′ − w₁′w₂ = π/4` — a *constant*, available with no evaluation.  The companion energy
is bounded above by the corpus's own common envelope (`exists_lgBesselModel_common_envelope`) together
with `oscEnergy_le_exp`.  So

```text
oscEnergy(√u J₀)  ≥  (π/4)² / C
```

with `C` absolute — no numeric bound on `J₀` or `Y₀` at any point, which matters because the Lean
rules forbid computation.

Chain for the exterior mass from below, now complete in structure:

```text
π/4 Wronskian          →  energy floor for the model            oscEnergy_lower_of_wronskian   ✔
energy floor           →  L² mass of the model                  besselMass_lower               ✔
model mass             →  exact mass                            density transfer (two-sided)   ✔ (corpus)
                                                                 ProlateDunsterEndpointCoefficientBounds ✔ (corpus)
```

What remains is the arithmetic of the substitution `u = c·ξ_s(x)`, under which
`c·A²·J₀(cξ)² dx = (1/c)·(besselNormalForm u)²/ξ′² du`, plus the elementary bound `1 ≤ ξ′ ≤ 2` on a
window bounded away from the endpoint.

## Where the factor `c` in the energy floor comes from

The Wronskian floor, done in the self-adjoint variables rather than the normal-form ones, explains
the missing power of the aperture outright.  For two solutions of `(p R')' + Q R = 0` the weighted
Lagrange identity

```text
(A² + μB²)(C² + μD²) − μ(BC − AD)²  =  (AC + μBD)² ,      μ = p Q ,
```

gives, with no positivity hypothesis at all,

```text
HTGeometry.sq_wronskian_mul_le_slEnergy_mul
    p Q · (R₁·(p R₂′) − (p R₁′)·R₂)²  ≤  slEnergy₁ · slEnergy₂
HTGeometry.slEnergy_lower_of_wronskian
    Wronskian = W,  slEnergy₂ ≤ C  ⟹  p Q W² / C ≤ slEnergy₁
```

both axiom-clean and wired.  The weight `p Q` appears because the Sturm energy weights `(p R′)²` and
`p Q R²` differently, and for the radial prolate equation

```text
p Q = c²(x²−1)(x²−s) ≍ c²   on a window bounded away from the endpoint,
```

so a companion solution with energy `O(c)` forces `slEnergy₁ = Ω(c)` — exactly the factor the
`1/c²` bound was missing.  Combined with `mass_lower_of_slEnergy`, whose denominator is `2 Q_max ≍ c²`,
this returns `∫ R² ≳ c/c² = 1/c`, the sharp order.

So the lower half's structure is settled, and the two candidate routes are now both available in
final form: through the model (Wronskian on `√u J₀`, `oscEnergy_lower_of_wronskian`, then
`besselMass_lower` and the density transfer), or directly on the exact solution (Wronskian on the
radial pair, `slEnergy_lower_of_wronskian`, then `mass_lower_of_slEnergy`).  The second is shorter
and needs no substitution; what it consumes is a second radial solution with a controlled Sturm
energy, which is what `ProlateDunsterEndpointVolterra`'s reconstruction supplies.

## The last structural gap in the energy floor: an envelope now controls the energy

`oscEnergy_lower_of_wronskian` needs an *upper* bound on the companion solution's energy
`E₂ = w₂² + w₂′²`.  The corpus supplies the envelope `|besselK u| ≤ C/√u`
(`exists_besselK_envelope`, hence `exists_lgBesselModel2_envelope`), which bounds `w₂ = √u·besselK u`
but says nothing about `w₂′`.  The gap is closed by a Landau inequality, not by an asymptotic:

```text
HTGeometry.abs_deriv_le_of_bounded
    |w| ≤ C  and  |w''| ≤ M  on [u, u+1]   ⟹   |w'(u)| ≤ 2C + M/2
```

(wired, axiom-clean).  The proof is one integration by parts in disguise: `g(t) = w(t) + (u+1−t)w′(t)`
has derivative `(u+1−t)w″(t)`, so `w(u+1) − w(u) − w′(u) = ∫_u^{u+1}(u+1−t)w″(t)dt` and the kernel
integrates to `1/2`.

For the oscillator this is self-improving: `w″ = −(1+q)w`, so the envelope bound on `w` *is* a bound
on `w″`, and therefore on `w′`.  Concretely, with `|w₂| ≤ C` and `|q| ≤ 1/(4u²) ≤ 1/4` for `u ≥ 1`,

```text
|w₂″| ≤ (5/4)C ,     |w₂′| ≤ 2C + 5C/8 ,     E₂ ≤ C² + (2C + 5C/8)² ,
```

all absolute.  Feeding that into `oscEnergy_lower_of_wronskian` with the exact constant
`w₁w₂′ − w₁′w₂ = π/4` gives an absolute energy floor for `√u J₀(u)` — with **no evaluation of any
Bessel function at any point**, which is what the no-computation rule requires.

The exterior-mass-from-below chain is therefore complete except for arithmetic:

```text
besselK envelope        →  |w₂| ≤ C                          corpus            ✔
Landau                  →  |w₂′| ≤ 2C + M/2  ⟹  E₂ ≤ C'      abs_deriv_le_of_bounded  ✔
π/4 Wronskian + E₂ ≤ C' →  E₁ ≥ (π/4)²/C'                    oscEnergy_lower_of_wronskian ✔
E₁ floor                →  ∫ u J₀² ≥ κ                       besselMass_lower  ✔
model mass              →  ∫_{x>1} R² ≥ κ/c                  density transfer (corpus) ✔
```

## The exterior mass from below, at the sharp order

```text
integral_Ioi_radialProlate_sq_ge :
  0 ≤ s ≤ 1/2,  8 ≤ c,  R(1) = 1 with the exterior radial equation
  ⟹  besselEnergyFloor/432/c  −  2·radialProlateDensityTransferConstant/c²   ≤  ∫_{x>2} R² .
```

`≍ 1/c`, matching `integral_Ioi_one_radialProlate_sq_le`'s `C/c` from above.  The card recorded the
available lower bound as `≥ 1/(32c²)`, "lossy by `c`"; that loss is gone.

The route is exact wherever it can be, and the pieces are all new:

```text
besselEnergy_lower              (π/4)²/((K_V(1)²+K_V'(1)²)e^{1/2}) ≤ besselEnergy u   (u ≥ 1)
besselMass_lower                virial identity + two-sided energy Grönwall
besselMass_lower_window         ∫_α^{α+4} (√u J₀)² ≥ (4/9)·besselEnergyFloor
besselMass_lower_tiled          n windows ⟹ linear growth in the ray length
xiAmplitude_sq_eq_mul_xiSpeed   A_s² = Ξ_s/(x²−s) · Ξ_s'          — an identity
besselDensity_ge_speed          B ≥ (1/8)·(cΞ')·J₀(cΞ)²  on [2,3]
integral_speed_besselJ0_sq      change of variables u = cΞ(x)
integral_besselJ0_sq_ge         ∫ J₀² = ∫ (√u J₀)²/u ≥ (tiled mass)/u₂
integral_window_besselDensity_ge   ∫_2^3 B ≥ besselEnergyFloor/432
```

Two things are worth recording because they were not obvious.

**The amplitude identity is what makes the change of variables possible.**  `A_s²/Ξ_s' = Ξ_s/(x²−s)`
exactly — no estimate — so on a window bounded away from the endpoint the density dominates a constant
multiple of `Ξ'(x)·J₀(cΞ(x))²`, which is precisely the shape `f'(x)·g(f(x))` that substitution
consumes.  Without it the integrand is not a pullback of anything.

**Tiling is where the factor `c` comes from.**  A single window gives a constant; the ray
`u ∈ [cΞ(2), cΞ(3)]` has length `≍ c`, so `⌊c/4⌋` disjoint windows give mass `≍ c`, and dividing by
`u₂ ≍ 3c` returns a constant for `∫ J₀²`.  The earlier attempt lost exactly this factor by bounding
`∫ w²/u` with a single window.

### `(β)`'s lower half: what is left

```text
exterior mass from below     integral_Ioi_radialProlate_sq_ge     ✔ sharp order
interior mass from above     still `integral_sq_le_turning_amplitude_envelope`, lossy by c^{3/2}
```

One input remains, and it is the turning-layer amplitude — the same Airy-scale question the upper
half sidestepped by anchoring at `2√s`.

## The barrier ratio from above: a vacuity repair and the sharp transport

`ProlateWKBSharpAction.lean` carried two theorems intended to supply the sharp *upper* bound on the
mode at the turning point,

```
exp_neg_angleAction_le_endpoint :  Phi(sqrt s) · exp(-c·A(s))  <=  Phi b
exp_neg_sharp_le_endpoint      :  Phi(sqrt s) · exp(-(c + (cs/4)·log s))  <=  Phi b
```

Both are **vacuous**.  Their hypothesis

```
hQ : forall y in Icc (sqrt s) b,  0 < -(s c^2) + c^2 y^2
```

is unsatisfiable for `c != 0`: at `y = sqrt s` the quantity is exactly `0`.  The Riccati potential
`prolateWKB c (-s c^2) y = sqrt((c^2 y^2 - c^2 s)/(1 - y^2))` vanishes at the turning point, so a
window whose *left endpoint is the turning point* can never satisfy the positivity the subsolution
comparison needs.  (Verified in a scratch file: `hQ` yields `False` from `Real.sq_sqrt`.)

`RHTower/ProlateAnchorActionUpperBound.lean` repairs this and, in the same stroke, removes a second
loss.  The anchor is separated from the turning point:

```
intervalIntegrable_prolateWKB
integral_prolateWKB_le_angleAction_anchor :  int_a^b W  <=  c·A(s)        (sqrt s <= a <= b < 1)
exp_neg_angleAction_le_endpoint_anchor    :  Phi a · exp(-c·A(s))  <=  Phi b
```

and the target is pushed to the band endpoint rather than left at an interior `b`.  The Riccati
potential *blows up* at `y = 1` while the logarithmic derivative of a smooth solution positive at
`1` stays bounded, so the initial inequality holds automatically near the endpoint:

```
tendsto_prolateWKB_atTop                  :  W -> infinity   along  nhdsWithin 1 (Iio 1)
eventually_prolateLogDeriv_le_prolateWKB  :  -Phi'/Phi <= W   eventually along the same filter
```

Taking `b -> 1^-` in the transported inequality gives the barrier ratio from above with **no loss at
all**:

```
prolate_anchor_le_exp_angleAction  :  Phi a <= Phi 1 · exp(c·A(s))
prolate_anchor_le_exp_sharp        :  Phi a <= Phi 1 · exp(c + (cs/4)·log s)
prolate_anchor_le_exp_sharp_of_one :  Phi a <= exp(c + (cs/4)·log s)          (Phi 1 = 1)
```

This is the exact companion of `prolateBand_barrier_ratio_lower`, and it is what the interior mass
estimate consumes.

### Why the anchor cannot be moved to the turning point

`exp_neg_angleAction_le_endpoint_anchor` needs `houter : c^2(1 - 2y^2) <= -s c^2`, that is
`y^2 >= (1+s)/2`.  The WKB profile is a Riccati subsolution only where the potential varies slowly;
near the turning point it does not.  The corpus's substitute valid on the whole band,

```
prolateRadialBarrier c s y = c·sqrt(1-s)·y / sqrt(1-y^2) ,
```

overshoots the exact profile `c·P(y) = c·sqrt((y^2-s)/(1-y^2))` by

```
barrier - cP  =  c s sqrt(1-y^2) / (sqrt(1-s) y + sqrt(y^2-s)) ,
```

whose integral from `sqrt s` to `1` is about `(cs/2)·log(1/s)`.  With `cs = 2n+1` and `s ~ 1/c` that
is about `((2n+1)/2)·log c`, i.e. **exactly the factor `c^{n+1/2}` the whole problem is about**.  The
crude barrier is therefore usable only across windows of length `O(s)`, never across the band.

## The interior mass from above: the variable-scale amplitude envelope

`HTGeometry/SturmAmplitudeEnvelope.lean` (new) is the tool.  For `(p R')' + Q R = 0` and a scale `K`,

```
G = R^2 + (p R')^2/K ,    G' = 2 R (p R')(1/p - Q/K) - (p R')^2 K'/K^2 ,
2|R||p R'| <= sqrt K · G ,   (p R')^2/K <= G ,
```

so `|G'/G| <= sqrt K·|1/p - Q/K| + |K'|/K`, and the logarithmic-derivative envelope traps `G` in both
directions.  Constant scale (`sturmAmplitude_le_mul_exp`, `sturmAmplitude_le_mul_exp'`) is a local
tool.  The variable scale is the global one: choosing

```
K = -Q p        (positive throughout the forbidden band)
```

makes `1/p - Q/K = 2/p`, hence `sqrt K·|1/p - Q/K| = 2 sqrt(-Q/p) = 2 c P(y)` -- *exactly twice the
WKB rate* -- and the whole extra cost is the logarithmic variation of the scale:

```
G(y)  <=  G(alpha) · exp(2c(Xi_s(y) - Xi_s(alpha))) · (K(alpha)/K(y)) .
```

For the angular equation `p = 1 - y^2`, `Q = c^2(s - y^2)`, so `K = c^2(y^2 - s)(1 - y^2)` and

```
K(alpha)/K(2 sqrt s)  is about  alpha^2(1 - alpha^2)/(3s)  =  O(1/s)  =  O(c) ,
```

a loss of `sqrt c` in `Phi` -- `sigma = 1/2`, not the `c^{n+1/2}` the crude barrier costs.

### The assembled chain for `(beta)`'s lower half

```
1.  Phi(alpha)          <= 3·I0(c Xi(alpha)) <= 3 e^{c Xi(alpha)}   prolateBand_le_and_le            [done]
2.  |Phi'(alpha)/Phi(alpha)| = O(c) , hence G(alpha) = O(1)·Phi(alpha)^2
                                                        radial barrier + prolate_endpoint_le_log
3.  Phi(2 sqrt s)^2     <= G(2 sqrt s) <= G(alpha)·e^{2c Xi(2 sqrt s)}·O(c)
                                                        sturmAmplitudeVar_envelope       [tool done]
4.  Phi(sqrt s)         <= Phi(2 sqrt s)·e^{O(cs)}      prolateRadialBarrier on [sqrt s, 2 sqrt s]
5.  int_{-1}^1 Phi^2    <= 4e(c/sqrt s)·Phi(sqrt s)^2   integral_sq_le_turning_amplitude_envelope [done]
6.  int_{Ioi 2} R^2     >= kappa/c - 2T/c^2             integral_Ioi_radialProlate_sq_ge  [done]
7.  leakage = outside·value^2/inside
```

Budget: step 3 costs `sigma = 1/2`, step 5 costs `c/sqrt s ~ c^{3/2}`, step 6 is sharp
(`sigma = 0`), and the upper half is `sigma_+ = 1`.  Total `sigma_+ + sigma_- = 1 + 1/2 + 3/2 = 3`,
inside the budget `7/2`.

Only steps 2-4 remain to be instantiated; steps 1, 5, 6 and the tool of step 3 are Lean-proved.

## `(beta)`'s lower half: the chain is closed, at a boundary budget

All of steps 1-7 are now Lean-proved and axiom-clean.  New modules:

```
HTGeometry/SturmAmplitudeEnvelope.lean
    sturmAmplitude, hasDerivAt_sturmAmplitude,
    abs_two_mul_le_sqrt_mul_sturmAmplitude,
    sturmAmplitude_le_mul_exp, sturmAmplitude_le_mul_exp'      (constant scale)
    sturmAmplitudeVar, hasDerivAt_sturmAmplitudeVar,
    abs_deriv_sturmAmplitudeVar_le, sturmAmplitudeVar_envelope (variable scale)

RHTower/ProlateAnchorActionUpperBound.lean
    intervalIntegrable_prolateWKB, integral_prolateWKB_le_angleAction_anchor,
    exp_neg_angleAction_le_endpoint_anchor,
    tendsto_prolateWKB_atTop, eventually_prolateLogDeriv_le_prolateWKB,
    prolate_anchor_le_exp_angleAction, prolate_anchor_le_exp_sharp,
    prolate_anchor_le_exp_sharp_of_one

RHTower/ProlateBandAmplitudeTransport.lean
    prolateBandScale, prolateBandScaleDeriv, prolateBandAmplitude, prolateBandMajorant,
    prolateBand_drift_eq, sqrt_prolateBandScale_mul, abs_prolateBandScaleDeriv_div_le,
    prolateBand_majorant_bound, integral_prolateBandMajorant, prolateBand_amplitude_le

RHTower/ProlateBandAmplitudeAnchor.lean
    abs_prolateLogDeriv_le_band, prolateBandAmplitude_anchor_le,
    prolate_le_mul_exp_radialBarrier, prolate_anchor_le_exp_bandPhase,
    prolate_turningPoint_sq_le_exp, integral_sq_le_exp_sharp_action,
    leakage_lower_of_mass_bounds

RHTower/ProlateLeakageLowerSharp.lean
    integral_Ioi_radialProlate_sq_ge_half, prolate_leakage_ge_exp_sharp_action
```

The headline is

```
prolate_leakage_ge_exp_sharp_action :

  besselEnergyFloor/(864 c)
    / (2 · 4e (c/sqrt s) · C · exp(2 c Xi_s(y0) + log-scale-ratio + 2 D))
      <=  leakage
```

with `C = 1 + (1-alpha^2)(barrier(alpha) + 6/(1-alpha))^2 / (c^2(alpha^2-s))`, the scale ratio
`(alpha^2-s)(1-y0^2) / ((y0^2-s)(1-alpha^2))`, and `D = c sqrt(1-s)(sqrt(1-s) - sqrt(1-y0^2))` the
`O(cs)` cost of the last window.  `prolate_anchor_le_exp_bandPhase` is the loss-free endpoint
transport `Phi(alpha) <= Phi(1) exp(c Xi_s(alpha))`, obtained as the `b -> 1` limit of the Riccati
subsolution comparison.

### The accounting, with `y0 = 2 sqrt s`, `alpha` a fixed collar edge, `cs = 2n+1`, `s ~ 1/c`

```
exterior mass             besselEnergyFloor/(864 c)     sharp                    sigma 0
scale ratio               O(1/s) = O(c)                 amplitude transport      sigma 1
aperture envelope         c/sqrt s ~ c^{3/2}            corpus turning envelope  sigma 3/2
last window               exp(O(cs))                    constant                 sigma 0
                                                                          sigma_- = 5/2
upper half                                                                sigma_+ = 1
                                                                          total   = 7/2
```

That is exactly the budget, not inside it.  The slack is in the aperture envelope: the truth is
`int Phi^2 ~ (sqrt s + 1/c) Phi(sqrt s)^2 ~ c^{-1/2} Phi(sqrt s)^2`, so
`integral_sq_le_turning_amplitude_envelope`'s prefactor `c/sqrt s` is lossy by `c^2`, not by
`c^{3/2}`.  Bounding the aperture mass *directly* by the band amplitude — constant scale `K = c^2 s`
on `[0, 2 sqrt s]` (cost `exp(O(cs))`, a constant) and band scale on `[2 sqrt s, alpha]` (cost the
same scale ratio already paid) — removes the `c/sqrt s` factor entirely and replaces it by the
scale ratio already counted.  That brings `sigma_-` to `3/2` and the total to `5/2`, inside the
budget.  This is the next step; the envelope tool it needs is already proved
(`sturmAmplitude_le_mul_exp` for the allowed region, `prolateBand_amplitude_le` for the band).

## The turning-layer prefactor is gone: `(beta)`'s lower half is inside budget

`RHTower/ProlateApertureMassSharp.lean` replaces the corpus's aperture envelope.  The point is that
the amplitude envelope crosses the turning layer *for free* once the scale is matched to the
potential.  On the allowed interval `[0, y0]` with `y0^2 <= 4s` take the **constant** scale
`K = c^2 s`:

```
1/p - Q/K = 1/(1-y^2) - 1 + y^2/s  in  [0, 5] ,     sqrt K = c sqrt s ,
```

so the envelope costs `exp(5 c sqrt s · y0) = exp(O(cs))`, a constant for a fixed mode.  At `y0` the
constant and band scales differ by `(y0^2-s)(1-y0^2)/s <= 3`, so the allowed amplitude passes into
the band amplitude; past `y0` the band transport applies; past `alpha` the loss-free endpoint bound
`prolate_anchor_le_exp_bandPhase` applies.  Three regions, one pointwise envelope:

```
prolate_allowed_sq_le
sturmAmplitude_const_le_three_mul_band
prolateBandAmplitude_le_uniform
prolate_sq_le_aperture_envelope
integral_sq_le_aperture_envelope
integral_sq_le_exp_sharp_action_amplitude
```

the last being

```
int_{-1}^1 Phi^2  <=  2(3C+1) · exp(2 c Xi_s(y0) + Lambda + 5 c sqrt s · y0)
```

with `C = 1 + (1-alpha^2)(barrier(alpha)+6/(1-alpha))^2/(c^2(alpha^2-s))` and
`Lambda = prolateScaleLog s y0 alpha` the log of the scale ratio.  **No `c / sqrt s`.**

`prolate_leakage_ge_exp_sharp_amplitude` (in `ProlateLeakageLowerSharp.lean`) is the corresponding
leakage bound.

### Budget, final

```
exterior mass        besselEnergyFloor/(864c)      sharp                        sigma 0
aperture bound       O(c) · Phi(sqrt s)^2          truth is c^{-1/2}·Phi^2      sigma 3/2
allowed interval     exp(O(cs))                    constant                     sigma 0
anchor constant C    O(1)                          constant                     sigma 0
                                                                        sigma_- = 3/2
upper half                                                              sigma_+ = 1
                                                                        total   = 5/2  <  7/2
```

Both halves of `(beta)` are now Lean-proved, axiom-clean, and inside the precision budget.  What
remains is bookkeeping: instantiate `y0 = 2 sqrt s` and a fixed collar `alpha`, evaluate
`Lambda = log((alpha^2-s)(1-y0^2)/((y0^2-s)(1-alpha^2)))` as `log(O(1/s))`, and convert
`Xi_s(y0)` to `A(s) = 1 + (s/4)log s + O(s)` with `cs = 2n+1`.

## The card's stated bottleneck is closed: the barrier ratio, two-sided

The bottleneck recorded above was

> the barrier ratio `Phi(y0)/Phi(1)`, to relative precision `c^(±3/2)`.

`RHTower/ProlateBarrierRatioTwoSided.lean` (wired, axiom-clean) delivers both directions with the
*same* sharp exponential:

```
prolateBand_sq_le_exp_bandPhase
    Phi(y0)^2  <=  C · exp(2 c Xi_s(y0) + Lambda)

prolateBand_barrier_ratio_two_sided
    exp(c Xi_s(y0) + 6 log((1-alpha)/(1-y0))) / (6 pi sqrt(c Xi_s(alpha)))  <=  Phi(y0)
      and the square bound above
```

with `C = 1 + (1-alpha^2)(barrier(alpha) + 6/(1-alpha))^2 / (c^2(alpha^2-s))` and
`Lambda = prolateScaleLog s y0 alpha = log((alpha^2-s)(1-y0^2)/((y0^2-s)(1-alpha^2)))`.

Since both bounds carry `exp(c Xi_s(y0))`, the relative precision is the product of the two
prefactors: `sqrt(C exp Lambda)` and `6 pi sqrt(c Xi_s(alpha))`.  With `y0 = 2 sqrt s`, `alpha` a
fixed collar edge, `cs = 2n+1` and `s ~ 1/c`,

```
exp Lambda = O(1/s) = O(c) ,     C = O(1) ,     c Xi_s(alpha) = O(c) ,
```

so the relative precision is `O(sqrt c) · O(sqrt c) = O(c)` — inside the required `c^(3/2)`.

The route that achieves this is *not* the parabolic-cylinder / Liouville-Green package the earlier
entry proposed.  It is the **Sturm amplitude envelope at a matched scale**
(`HTGeometry/SturmAmplitudeEnvelope.lean`): for `(pR')' + QR = 0` and any scale `K`,

```
G = R^2 + (pR')^2/K ,     |G'/G|  <=  sqrt K · |1/p - Q/K|  +  |K'|/K .
```

Taking `K = -Qp` in the band makes `1/p - Q/K = 2/p`, hence `sqrt K (2/p) = 2 c P(y)` — *exactly
twice the WKB rate* — and the entire extra cost is the logarithmic variation of the scale, two
elementary logarithms.  Taking `K = c^2 s` on the allowed interval `[0, 2 sqrt s]` gives
`|1/p - Q/K| = 1/(1-y^2) - 1 + y^2/s in [0,5]` and `sqrt K = c sqrt s`, so the turning layer is
crossed at cost `exp(10 c s)`, a constant for a fixed mode.  No turning-point model function is
needed at all: neither Airy, nor parabolic cylinder, nor a Liouville-Green error-control function.

Consequences already landed:

```
RHTower/ProlateApertureMassSharp.lean
    prolate_allowed_sq_le, sturmAmplitude_const_le_three_mul_band,
    prolateBandAmplitude_le_uniform, prolate_sq_le_aperture_envelope,
    integral_sq_le_aperture_envelope, integral_sq_le_exp_sharp_action_amplitude
RHTower/ProlateLeakageLowerSharp.lean
    integral_Ioi_radialProlate_sq_ge_half,
    prolate_leakage_ge_exp_sharp_amplitude, prolate_leakage_ge_explicit
```

`prolate_leakage_ge_explicit` is the leakage lower bound at the standard matching point
`y0 = 2 sqrt s`, entirely elementary in its constants:

```
besselEnergyFloor/(864 c)
  / (2 (2 (3C+1) exp(2c(1 + (s/4) log s) + log((alpha^2-s)/(3s)) + log((1-4s)/(1-alpha^2))
                      + 10 c s)))
    <=  leakage .
```

Both halves of `(beta)` are now Lean-proved, axiom-clean, and inside the precision budget
(`sigma_+ + sigma_- = 5/2 < 7/2`).

## `(beta)` delivered: the leakage, two-sided, at the sharp action

`RHTower/ProlateLeakageTwoSided.lean` (wired, axiom-clean):

```
prolate_leakage_two_sided

  besselEnergyFloor/(864 c)
    / (2 (2 (3C+1) exp(2c(1 + (s/4) log s)
                        + log((alpha^2-s)/(3s)) + log((1-4s)/(1-alpha^2)) + 10 c s)))
      <=  leakage  <=
  radialProlateExteriorMassConstant/c
    · ((6 pi sqrt(c Xi_s(alpha)))^2 exp(2 E) / (b - 2 sqrt s))
    · exp(-2(c Xi_s(2 sqrt s) + 6 log((1-alpha)/(1-2 sqrt s))))
```

with `E = (c b + 12)(b - 2 sqrt s)/(1 - b^2)` and `C` the anchor constant.  Both directions carry the
same exponential `exp(-2 c Xi_s(2 sqrt s))`, and `Xi_s(2 sqrt s) <= A(s) = 1 + (s/4) log s + O(s)`,
so with `cs = 2n+1` and `s ~ 1/c` the shared exponential is `exp(-2c) c^{n+1/2}` up to a bounded
factor.  The gap between the two prefactors is `c^{5/2}`, inside the card's budget of `7/2`.

The last new input was the interior mass from below, `RHTower/ProlateInteriorMassLower.lean`:

```
prolateFlux_sq_le_band            |(1-t^2) Phi'| <= (1-t^2)(barrier(t) + 6/(1-t)) |Phi|
one_sub_sq_mul_band_barrier_le    (1-t^2)(barrier(t) + 6/(1-t))  <=  c b + 12      (t <= b)
prolate_window_mass_lower         (b-y0)(Phi(y0) exp(-(cb+12)(b-y0)/(1-b^2)))^2 <= int_{y0}^b Phi^2
prolate_aperture_mass_lower       the same against the full aperture
```

At `y0 = 2 sqrt s` the barrier constant `c b + 12` is `O(sqrt c)` for a fixed mode, so a window of
width `1/(c b + 12)` costs a bounded exponential and contributes `Phi(y0)^2/(c b + 12)` — the true
order.  No turning-point model function (Airy, parabolic cylinder, Liouville-Green error control)
is used anywhere in either direction.

## Lean progress — `(11)` and the Gram-Schmidt property `(10a)` are theorems

`RHTower/HermiteContrastLadder.lean` (wired, axiom-clean).  Both are pure algebra in the centre
values, with no hypothesis beyond `a (k+1) != 0`, so they are unconditional:

```
contrastPartialSum a k = sum_{j<=k} (a j)^2                       S_k
contrastLadder a k     = (-a_0, ..., -a_k, S_k/a_(k+1), 0, ...)   w_k
rawContrast a m        = a_0 e_m - a_m e_0                        r_m

contrastLadder_inner_centre        <w_k, a> = 0
contrastLadder_inner_of_lt         <w_k, w_m> = 0   (k < m)
contrastLadder_inner_eq_zero       <w_k, w_m> = 0   (k != m)
contrastLadder_succ_ne_zero        w_k is not the zero vector
contrastLadder_inner_rawContrast        <w_k, r_m> = 0     for 1 <= m <= k
contrastLadder_inner_rawContrast_succ   <w_k, r_(k+1)> = a_0 S_(k+1) / a_(k+1)
```

Each identity is the same two-term cancellation: the head of `w_k` contributes `-S_k` and its single
tail entry contributes `+S_k`.  The last two are the Gram-Schmidt property in the sharp form: `w_k`
annihilates every earlier raw contrast and pairs nontrivially with the next one, which is exactly
what characterizes the `(k+1)`-st Gram-Schmidt vector of the ordered family `r_1, r_2, ...`.

The explicit combination realizing `w_k` inside `span{r_1, ..., r_(k+1)}` is

```
w_k = sum_{m=1}^{k} (-a_m/a_0) r_m  +  (S_k/(a_0 a_(k+1))) r_(k+1) ,
```

whose zero-coordinate is `-[-(S_k - a_0^2)/a_0 + S_k/a_0] = -a_0` as required.

Both pairings are stated as finite sums over any `range N` containing the supports, so no `l^2`
machinery is needed; the vectors have finite support by construction.

## Lean progress — `(4)` is a theorem for every `j`

`RHTower/HermiteCentreValueClosedForm.lean` (wired, axiom-clean) closes the card's `(4)`:

```
hermiteOriginValue_sq_two_mul
    hermiteOriginValue (2m)^2  =  sqrt 2 * centralBinom m / 4^m

hermiteOriginValue_sq_four_mul
    hermiteOriginValue (4j)^2  =  hermiteOriginValue 0 ^ 2 * binom(4j, 2j) / 16^j
```

i.e. `a_j^2 = a_0^2 q_j` with `q_j = binom(4j,2j)/16^j`, and `a_0^2 = sqrt 2` is the corpus's
`hermiteOriginValue_sq_zero`.  Only the corpus's own two-step origin recursion
`eval_zero_hermitePoly_add_two` and mathlib's central binomial recursion
`Nat.succ_mul_centralBinom_succ` are used; the induction works because the two ratios agree exactly:

```
a_{2m+2}^2 / a_{2m}^2                              = (2m+1)/(2m+2)
[centralBinom (m+1)/4^(m+1)] / [centralBinom m/4^m] = 2(2m+1)/(4(m+1)) = (2m+1)/(2m+2)
```

Every power of `pi` cancels between the squared origin value and the `L^2` normalisation, which is
why the closed form is rational times `sqrt 2`.

With this and `HermiteContrastLadder.lean`, the whole algebraic layer of the ladder card —
`(4)`, `(5)`, `(10)`, `(10a)`, `(11)` — is unconditional Lean.  What is left is analytic: the
prolate-to-Hermite convergence `(3)` and the compression spectrum statement `(8)`.

## Lean progress — the interlacing mechanism of `(8)`

`RHTower/SecularEquationInterlacing.lean` (wired, axiom-clean) proves the mechanism the card's `(8)`
runs on.  Compressing `diag(d_0, d_1, ...)` to the hyperplane orthogonal to `ell` gives the secular
equation `F(mu) = sum_j (ell_j)^2/(d_j - mu) = 0`, and:

```
secular d ell N mu            the secular function
secular_denom_ne              inside a gap every denominator is nonzero
secular_strictMonoOn          F is strictly increasing on (d_k, d_(k+1))
continuousOn_secular          and continuous there
tendsto_secular_atBot         F -> -infinity  at the left end of the gap
tendsto_secular_atTop         F -> +infinity  at the right end
exists_unique_secular_root    hence EXACTLY ONE root in each gap
```

This is the card's "there is exactly one constrained eigenvalue `mu_k(lambda)` in
`(d_k(lambda), d_(k+1)(lambda))`" — the interlacing half of `(8)` — for the scalar model, with no
hypothesis beyond `d` strictly increasing and the two adjacent `ell` entries nonzero.  The monotone
step is the identity

```
(ell_j)^2/(d_j - y) - (ell_j)^2/(d_j - x) = (ell_j)^2 (y - x) / ((d_j - x)(d_j - y)) ,
```

whose denominator is positive because inside a gap the two factors have the same sign, whichever
side of the gap the index falls on.

For the location of the root:

```
secular_smul            the equation is scale covariant, so the root may be studied in the
                        normalized variable theta = mu / d_(k+1)
limit_secular_root_iff  in the limit the equation degenerates to  -S/theta + T/(1-theta) = 0,
                        whose root is exactly  theta = S/(S+T)
```

With `S = S_k = sum_{j<=k} ell_j^2` and `T = ell_(k+1)^2`, the root is `S_k/S_(k+1)`, and the
coordinate limits `ell_j^2 -> A q_j` turn that into `Q_k/Q_(k+1) = theta_k` — the card's `(8)`.  What
remains between these and `(8)` is the uniformity: the passage from the exact equation at finite
`lambda` to the degenerate one, which is where the Fuchs separation `d_j/d_(j+1) -> 0` enters.

## Lean progress — `(8)`'s location statement, quantitatively

The item recorded above as remaining — "the passage from the exact secular equation at finite
`lambda` to the degenerate one" — is now a theorem.  Same module,
`RHTower/SecularEquationInterlacing.lean`:

```
secular_split               the three-block decomposition around the gap
secular_lower_block_le      lower block  <=  -S_k/mu
secular_lower_block_ge      lower block  >=  -S_k/(mu - eps d_(k+1))
secular_upper_block_bounds  upper block in  [0, T/((M-1) d_(k+1))]

secular_root_le             mu/d_(k+1)  <=  S_k/S_(k+1) + eps
le_secular_root             mu/d_(k+1)  >=  S_k/(S_(k+1) + T/(M-1))
```

where `S_k = sum_{j<=k} ell_j^2`, `T = sum_{j>k+1} ell_j^2`, and the two slack parameters are the
Fuchs separation itself:

```
d_j <= eps · d_(k+1)     for j <= k          (the lower modes are much smaller)
d_j >= M · d_(k+1)       for k+1 < j <= N    (the higher modes are much bigger)
```

As `eps -> 0` and `M -> infinity` both bounds converge to `S_k/S_(k+1)`, and the coordinate limits
`ell_j^2 -> A q_j` turn that into `Q_k/Q_(k+1) = theta_k`.  So the card's `(8)` is now:

- **interlacing** — `exists_unique_secular_root`, exactly one root per gap;
- **location** — `secular_root_le` and `le_secular_root`, the root pinned between two explicit
  expressions that squeeze to `theta_k` as the separation widens.

Both are unconditional and quantitative, with no limit hypothesis: they hold at every finite
`lambda` for which the two separation inequalities hold, which is what `(7)` supplies.

The proof of the lower bound splits on whether the root is already below `S_k/S_(k+1)`: if it is,
the singular term is bounded by `S_(k+1)/d_(k+1)` and the equation gives the bound directly; if it
is not, the bound is immediate because `S_k/(S_(k+1) + T/(M-1)) <= S_k/S_(k+1)`.

## Lean progress — the coordinate half of `(3)`: the tail machinery

The remaining item on this card was the coordinate limit `ell_j(lambda) -> a_j`.  Its two analytic
ingredients are now theorems, in `RHTower/SecondMomentTailBound.lean` (wired, axiom-clean).

The obstruction is that an `L^2` bound alone does **not** control the tail of `int Psi_c`: the tail
of a unit-`L^2` function can carry all its `L^1` mass.  What controls it is the *second moment*,
which the corpus already bounds (`integral_rescaled_secondMoment_le`).  The bound is Cauchy-Schwarz,
but it is obtained here with no Hoelder machinery at all:

```
abs_le_secondMoment_split      |f(xi)| <= (t/2)(1/xi^2) + (1/(2t)) xi^2 f(xi)^2     (t, xi > 0)
integral_Ioi_one_div_sq        int_{xi > K} xi^(-2)  =  1/K
integrableOn_Ioi_one_div_sq
integral_Ioi_abs_le_param      int_{xi > K} |f|  <=  t/(2K) + (1/(2t)) int_{xi > K} xi^2 f^2
integral_Ioi_abs_le_sqrt       int_{xi > K} |f|  <=  sqrt(N/K)      when the moment is <= N
```

The pointwise split is the identity

```
(t/2)(1/xi^2) + (1/(2t)) xi^2 f^2 - |f|  =  (t - xi^2 |f|)^2 / (2 t xi^2) ,
```

and setting `t = sqrt(N K)` balances the two halves, recovering the sharp constant.  So a family
with a uniform second-moment bound `N` has integral tails `<= sqrt(N/K)`, uniformly — as small as
one likes.

The second ingredient is the passage from that to the limit of the integrals:

```
tendsto_integral_of_compact_of_tail
    convergence of  int_{[-K,K]} F_i  for every K,  plus uniformly small tails,
    gives  int F_i -> int f
```

the three-epsilon argument, stated for an arbitrary filter so it applies to the bandwidth family
directly.

With `tendsto_prolateProfile_oscProfile` for the compact half and
`integral_rescaled_secondMoment_le` for the tails, these give `int Psi_c -> int Psi^*` — and with
`Psi^* = phi_n/phi_n(0)` from the rigidity theorem, that is the coordinate limit `(3)`.

## Lean progress — the tail hypothesis, instantiated for the prolate family

`RHTower/ProlateTailIntegralBound.lean` (wired, axiom-clean) discharges, for the actual normalized
prolate profiles, the tail hypothesis that `tendsto_integral_of_compact_of_tail` consumes:

```
intervalIntegral_secondMoment_mono   the window second moment dominates any sub-interval's
normalizedProlate_tail_le           |int_K^{sqrt c} Psi_c|  <=  sqrt(N/K)
normalizedProlate_tail_lt           and it is below any target delta once  K > N/delta^2
```

The input is the corpus's own `normalizedProlate_secondMoment_le`; the mechanism is the
second-moment tail bound.  The bound is uniform in the bandwidth: `N` is any bound for the window
second moment, which `normalizedProlate_total_mass_le` supplies with a constant depending only on
the window and the separation bound.

So all three ingredients of the coordinate half of `(3)` are now theorems:

```
compact half   tendsto_prolateProfile_oscProfile        (corpus)
tail half      normalizedProlate_tail_lt                (new)
transfer       tendsto_integral_of_compact_of_tail      (new)
```

and by evenness of the profile (`even_normalizedProlateProfile`) the negative tail is the same.

## Lean progress — the growing-window transfer, and `(3)`'s coordinate half assembled

`RHTower/SecondMomentTailBound.lean` now carries both halves of the transfer the prolate family
needs, plus the growing-window form its integrals actually have:

```
tendsto_setIntegral_Icc_of_tendsto_of_bounded
    pointwise convergence + a uniform bound  ==>  convergence of the window integrals
    (dominated convergence on a finite-measure window)

tendsto_intervalIntegral_growing_window
    integrals over every fixed window converge to g K,  g K -> A,
    and the tails past any large enough cut are uniformly small
      ==>  int_{-R_i}^{R_i} F_i -> A
```

The second is the shape the prolate integrals have: the window is `[-sqrt c, sqrt c]` and grows with
the bandwidth, so neither a fixed-domain dominated-convergence argument nor a fixed-tail argument
applies directly.  The proof is the four-epsilon split

```
int_{-R}^{R} F_i - A
  = (int_{-K}^{K} F_i - g K) + (g K - A) + int_{-R}^{-K} F_i + int_{K}^{R} F_i ,
```

with `K` chosen past both the tail threshold and the window-value threshold.

The three inputs for the prolate family are now all theorems:

```
pointwise convergence   tendsto_prolateProfile_oscProfile   (corpus)
uniform bound           normalizedProlate_phase_le          (corpus)
uniform tails           normalizedProlate_tail_lt           (this session)
```

so the coordinate half of `(3)`, `ell_j(lambda) -> a_j`, has every ingredient in Lean.  What is left
is to instantiate the transfer at the prolate family with those three, which is substitution rather
than mathematics.

## The growing-window transfer is now instantiated at the prolate family, PROVED

The transfer machinery built earlier was general; it is now applied to the ground family itself.

```
RHTower/ProlateProfileIntegralLimit.lean
  gaussianProfile_eq, integrable_gaussianProfile, continuous_gaussianProfile
  integral_gaussianProfile                    ∫_R e^{-x²/2} = √(2π)
  tendsto_intervalIntegral_gaussianProfile    the symmetric windows exhaust that mass
  abs_intervalIntegral_sub_le_of_window_dist  window closeness => integral closeness
  tendsto_intervalIntegral_of_window_dist     the same, along a filter, eventually
  intervalIntegral_neg_of_even                even integrand: left tail = right tail
  tendsto_intervalIntegral_growing_window'    the transfer with EVENTUAL integrability

RHTower/ProlateWindowProfileDistance.lean
  prolateWindowDistEnvelope, tendsto_prolateWindowDistEnvelope
  prolateGround_windowDist_bound   |Ψ_c(x) − e^{−x²/2}| ≤ envelope on the whole window

RHTower/ProlateGroundProfileIntegral.lean
  tendsto_prolateGround_profileIntegral
      ∫_{−√c}^{√c} Ψ_c(ξ) dξ  →  √(2π)
```

Three points that were not mere substitution:

1. The corpus window comparison is stated for the *square* of the profile, because that is what the
   mass computation needs.  The first-moment transfer needs the unsquared statement, which is the
   first half of the same Grönwall argument; `prolateGround_windowDist_bound` extracts it.
2. The growing-window transfer as originally stated demands interval integrability for *every*
   index.  A family indexed by the bandwidth and defined only for `c > 0` does not satisfy that, and
   no reformulation of the family fixes it.  `tendsto_intervalIntegral_growing_window'` weakens the
   hypothesis to `∀ᶠ`, which is what the family does satisfy.
3. The uniform second moment comes from the aperture virial `∫ξ²Ψ² ≤ μ_c ∫Ψ²` combined with the
   already-proved convergence of `∫Ψ²` to `√π`: eventually `μ_c ≤ 2` and `∫Ψ² ≤ √π + 1`, so
   `N₀ = 2(√π+1)` bounds the second moment for all large `c`, and the second-moment tail bound turns
   that into `|∫_K^{√c} Ψ_c| ≤ √(N₀/K)` — below any target once `K > N₀/δ²`.

The left tail needs no separate estimate: the ground profile is even, so the reflection
`intervalIntegral_neg_of_even` copies the right bound across.

This is the first-moment counterpart of `tendsto_prolateGround_centreMass`, which runs the same
squeeze on the square.  Both limits are now unconditional and axiom-clean.

## The normalization-free form of `(3)` at `j = 0`

`tendsto_prolateGround_profileIntegral` now returns BOTH limits for the same family:

```
int_{-sqrt c}^{sqrt c} Psi_c        -> sqrt(2 pi)
int_{-sqrt c}^{sqrt c} Psi_c^2      -> sqrt(pi)
```

and their combination is `tendsto_prolateGround_shapeRatio`:

```
( int Psi_c )^2 / int Psi_c^2  ->  2 sqrt(pi) .
```

This ratio is the right object to carry to `(3)`, because it is **invariant under rescaling the
eigenfunction** — the one ambiguity that separates the corpus's normalization from the card's
Fourier normalization.  Concretely, writing `Psi(xi) = Phi(xi/sqrt c)/Phi(0)` and substituting,

```
int_R Phi   = (Phi(0)/sqrt c) I_1 ,     int_R Phi^2 = (Phi(0)^2/sqrt c) I_2 ,
```

so for `e_0 = Phi / ||Phi||_2`,

```
ell_0^2 = (int Phi)^2 / int Phi^2 = I_1^2 / (sqrt c * I_2) ,
```

that is

```
sqrt c * ell_0(c)^2  ->  2 sqrt(pi) .
```

The `sqrt c` is exactly the Fourier-normalization factor the card absorbs into its convention.  So
what is proved is `(3)` at `j = 0` up to the card's normalization constant, and the remaining step
is bookkeeping in that convention, not analysis: identify the card's `a_0^2 = sqrt 2` against
`2 sqrt(pi)` under the CCM Fourier normalization, which fixes the constant once for all `j`.

Recorded so the next pass does not re-derive it: the naive attempt to read `ell_0` off the corpus
normalization directly gives `ell_0 = c^{-1/4} I_1 / sqrt(I_2) -> 0`, which is NOT a contradiction
with `(3)` — it is the same statement in a different normalization.  Only the rescaling-invariant
ratio should be compared across the two conventions.

## Lean progress — `(3)` threaded into `(8)`: the secular root converges to the coordinate ratio

`RHTower/SecularRootLimit.lean` (wired, axiom-clean).

The two location bounds already formal — `le_secular_root` and `secular_root_le` — sandwich the
normalized root:

```
S / (S + L + T/(M-1))   <=   mu / d_{k+1}   <=   S / (S + L) + eps
```

with `S = sum_{j<=k} ell_j^2`, `L = ell_{k+1}^2`, `T = sum_{j>k+1} ell_j^2`, and `eps`, `1/(M-1)`
the two gap slacks.  The new theorem closes the sandwich along a family:

```
tendsto_secular_ratio_of_limits
    S -> A,  L -> B,  T/(M-1) -> 0,  eps -> 0,  A + B != 0
      ==>  mu / d_{k+1}  ->  A / (A + B)

secular_limit_ratio_eq
    A/(A+B) is the root of the degenerate secular equation  -S/theta + T/(1-theta) = 0
```

This is exactly the threading of `(3)` into `(8)`.  The coordinate limits `ell_j -> a_j` supply
`S -> A` and `L -> B`; the leakage separation `d_k/d_{k+1} -> 0` supplies `eps -> 0`; and the
uniform infinite-tail estimate supplies `T/(M-1) -> 0`.  Nothing about the prolate family enters —
once those four limits are known, the root of the secular equation is pinned to the explicit ratio
of limiting coordinate masses.

The second theorem checks the consistency the card asserts: the limit `A/(A+B)` is precisely the
root of the degenerate equation, so the sandwich lands where the formal limiting problem says it
should rather than merely somewhere in the gap.

## Lean progress — `(β)` into `(8)`: the gap slack vanishes

`RHTower/PowerLawRatioVanishing.lean` (wired, axiom-clean).

```
tendsto_div_of_rpow_asymptotic
    f(c) / (A c^a E(c)) -> 1,   g(c) / (B c^b E(c)) -> 1,   a < b,   A,B != 0
      ==>   f(c) / g(c) -> 0
```

The shared factor `E` cancels identically and never has to be examined; only the difference of the
polynomial exponents survives.  In the application `E(c) = e^{-2c}` is the exponentially small factor
common to all leakage rates, so the theorem says exactly:

```
1 - lambda_n(c) ~ A_n c^{n+1/2} e^{-2c}    ==>    d_k / d_{k+1} = O(1/c) -> 0 ,
```

consecutive rates differing by one power of `c`.  That is the `eps -> 0` hypothesis of
`tendsto_secular_ratio_of_limits`, i.e. the `(β)` input to `(8)`.

Together with the previous section this completes the analytic glue for the threading:

```
(3)  coordinate limits  ell_j -> a_j        =>  S -> A,  L -> B
(β)  Fuchs rate ratio                       =>  eps -> 0        [this section]
     uniform infinite-tail estimate         =>  T/(M-1) -> 0
     ------------------------------------------------------------
(8)  tendsto_secular_ratio_of_limits        =>  mu_k / d_{k+1} -> A/(A+B)
```

Every implication in that table is now a Lean theorem; what the card still owes is the *inputs* on
the left in the corpus's own prolate objects — the coordinate limits at the card's normalization
(see the `sqrt c * ell_0^2 -> 2 sqrt(pi)` section) and the Fuchs asymptotic with its constant `A_n`.

## The normalization step of `(3)` is now a theorem, not bookkeeping

Two modules, both wired and axiom-clean.

```
HTGeometry/ShapeRatioDilation.lean
  intervalIntegral_dilate      int_{-aR}^{aR} b f(x/a)      = a b   int_{-R}^{R} f
  intervalIntegral_dilate_sq   int_{-aR}^{aR} (b f(x/a))^2  = a b^2 int_{-R}^{R} f^2
  shapeRatio_dilate            ( int_{-aR}^{aR} b f(x/a) )^2 / int_{-aR}^{aR} (b f(x/a))^2
                                   =  a . ( int_{-R}^{R} f )^2 / int_{-R}^{R} f^2
  shapeRatio_amplitude_invariant

RHTower/ProlateCoordinateNormalization.lean
  tendsto_sqrt_mul_prolateGround_coordSq
      sqrt c . ( int_{-1}^{1} Phi_c )^2 / int_{-1}^{1} Phi_c^2   ->   2 sqrt(pi)
```

The shape ratio is quadratic over quadratic, so the amplitude cancels exactly, and the dilation
survives once because the numerator is squared *after* integrating.  That is the whole content of
the "rescaling ambiguity" the card flagged: the normalised profile is
`Psi_c(xi) = Phi_c(xi/sqrt c) / Phi_c(0)`, which is `beta f(x/alpha)` with `alpha = sqrt c` and
`beta = 1/Phi_c(0)`, and the matching window `[-sqrt c, sqrt c]` corresponds to `R = 1` — the
eigenfunction's own interval.  So the corpus limit `2 sqrt(pi)` for the normalised profile transfers
verbatim, with the single factor `sqrt c`.

One point that was not bookkeeping: the transfer needs `Phi_c(0) != 0`, and no positivity of the
ground state is available in the corpus family data.  It is not needed.  If `Phi_c(0)` vanished the
normalised profile would be identically zero (Lean's `div_zero`), so its shape ratio would be `0`;
since the ratio tends to `2 sqrt(pi) != 0`, it is eventually nonzero, hence `Phi_c(0) != 0` for all
large `c` — which is all a limit statement needs.  The proof extracts the amplitude bound from the
limit itself.

So `(3)` at `j = 0` is now unconditional *in the card's own normalization*, with the constant
`2 sqrt(pi)` explicit.  What remains on this card is the Fuchs asymptotic with its constant `A_n`.

## The sharp constant `A_n` is NOT needed for `(β)`: a two-sided ladder suffices

`RHTower/TwoSidedRatioVanishing.lean` (wired, axiom-clean).

```
tendsto_div_of_rpow_twoSided
    0 <= f(c) <= A c^a E(c) ,   B c^b E(c) <= g(c) ,   a < b ,   A, B > 0
      ==>   f(c) / g(c) -> 0

tendsto_consecutive_leakage_ratio
    the same with E(c) = e^{-2c} and exponents k+1/2 , k+3/2
```

`tendsto_div_of_rpow_asymptotic` asked for asymptotic *equality* with constants, i.e. exactly the
Fuchs asymptotic `d_n(c) ~ A_n c^{n+1/2} e^{-2c}` including its constant.  That is more than the
threading uses.  Only the ratio `d_k / d_{k+1}` enters `(8)`, and a ratio needs no constants: an
upper bound on the numerator and a lower bound on the denominator suffice, and the shared
exponential cancels identically without ever being examined.

So the `(β)` input to `(8)` is discharged by the *two-sided ladder* — which is the form this tree's
prolate leakage estimates already take (`prolate_leakage_two_sided`,
`prolateBand_barrier_ratio_two_sided`) — rather than by the sharp Fuchs constant.  What the card
owes for `(β)` is therefore the instantiation of the existing two-sided leakage estimates at
consecutive modes, not a new asymptotic analysis.

## The third input of the `(8)` threading is now a theorem too

`RHTower/SecularTailVanishing.lean` (wired, axiom-clean).

```
sum_subset_le_of_sum_le    a bound on a nonnegative sum bounds every subsum
tendsto_tail_div_slack     0 <= T(c) <= C ,  M(c) -> infinity   ==>   T(c)/(M(c)-1) -> 0
```

Only two facts about the family are used: the infinite tail of the coordinate masses is bounded, and
the gap slack grows.  The first is a Bessel inequality — the masses of a normalised vector against an
orthonormal family sum to at most one, so *every* subfamily sum obeys the same bound uniformly in
`c`, which is what `sum_subset_le_of_sum_le` records.

With this the threading table is complete as Lean theorems:

```
(3)  coordinate limits  ell_j -> a_j    =>  S -> A,  L -> B     tendsto_prolateGround_shapeRatio
                                                                 + ProlateCoordinateNormalization
(beta) two-sided leakage ladder         =>  eps -> 0            tendsto_consecutive_leakage_ratio
     bounded tail + growing slack       =>  T/(M-1) -> 0        tendsto_tail_div_slack
     -----------------------------------------------------------------------------
(8)  tendsto_secular_ratio_of_limits    =>  mu_k / d_{k+1} -> A/(A+B)
```

Every implication *and* every input shape is now formal.  What the card still owes is the
instantiation of the two-sided leakage estimates at consecutive modes, and the coordinate limits at
indices `j > 0`; the ground index `j = 0` is closed.
