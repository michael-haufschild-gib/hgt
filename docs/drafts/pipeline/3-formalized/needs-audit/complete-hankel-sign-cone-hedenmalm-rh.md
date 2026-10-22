# Complete Hankel sign-cone and one-temperature Hedenmalm criterion

- **ID:** `complete-hankel-sign-cone-hedenmalm-rh`
- **Stage:** 3-formalized / needs-audit
- **Type:** UNIVERSAL CONE THEOREM / EXACT RH-EQUIVALENT SOURCE LAW
- **Date:** 2026-07-20
- **Scientific status:** `[PROVED HERE] [FORMALIZED] [UNCONDITIONAL] [NO COMPUTATION]
  [CANDIDATE NEW SYNTHESIS] [NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Parent card:** `gaussian-window-moment-defect-recession-law`

## Universal law

Let `mu` be a finite Borel measure on `R` which charges every nonempty open set and has all
bilateral exponential moments:

```text
integral exp(t*x) dmu(x) < infinity  for every real t.
```

For a continuous `L-infinity(mu)` multiplier `J`, define

```text
s_J(n) = integral x^n J(x) dmu(x).
```

Then the following are equivalent:

```text
J(x) >= 0 for every real x;

for every real polynomial p,
  integral p(x)^2 J(x) dmu(x) >= 0;

for every n and every c : Fin n -> R,
  sum_i sum_j c_i c_j s_J(i+j) >= 0.
```

Thus the complete tower of finite Hankel sections is exactly the pointwise sign cone.  No fixed
finite section is asserted to be complete; completeness resides in the cofinal family over all
degrees.

The proof has four dependency-closed steps:

1. Full bilateral exponential moments imply density of real polynomials in `L2(mu)`.
2. A bounded multiplier defines a continuous quadratic form on `L2(mu)`.
3. Positivity on the dense polynomial span extends to all of `L2(mu)`; indicator vectors then
   force almost-everywhere nonnegativity.
4. Continuity of `J` and positivity of `mu` on open sets upgrade the conclusion to pointwise
   nonnegativity.  The coefficient identity identifies polynomial squares with every finite
   Hankel quadratic form.

This is stronger than the Gaussian parent statement: Gaussian measure is only one instance of the
entire-exponential-moment/open-positive class.

## Hedenmalm--theta specialization

For `0<a<1/2`, set

```text
J_a(b) = Re Fourier(thetaCuspHorizontalAutocorrelationTangent a)(b/(2*pi)).
```

For any one `tau>0`, define the signed Gaussian moments

```text
s_(a,tau)(n) = integral b^n J_a(b) d(gamma_tau)(b),
d(gamma_tau)(b) = exp(-tau*b^2) db.
```

Let `HedenmalmGaussianHankelCone(tau)` mean that every finite Hankel quadratic form of every
`s_(a,tau)`, throughout `0<a<1/2`, is nonnegative.  Then

```text
HedenmalmGaussianHankelCone(tau) <-> RH       for every tau>0.
```

Consequently:

```text
exists tau>0, HedenmalmGaussianHankelCone(tau) <-> RH,
forall tau>0, HedenmalmGaussianHankelCone(tau) <-> RH,

tau,sigma>0 ->
  HedenmalmGaussianHankelCone(tau)
    <-> HedenmalmGaussianHankelCone(sigma).
```

The temperature invariance is exact: positive Gaussian damping changes the coordinates of the
complete moment carrier but cannot change its orientation.

## Exact remaining RH-bearing theorem

The present result is an equivalent reformulation, not a proof of the missing sign.  An RH proof in
this lane must prove any one of the following equivalent positive statements without assuming RH:

```text
J_a(b) >= 0 for every 0<a<1/2 and every b;

HedenmalmGaussianHankelCone(tau) for one positive tau;

reflection positivity / a Hilbert Gram realization of the full weighted moment sequence.
```

The source-specific uniform coalesced three-point theorem proves a genuine open order-three patch
for the positive theta density.  It does not imply the global Fourier orientation or the complete
Hankel tower and is not used as if it did.

## Formal realization

- `RHTower/EntireExponentialMomentPolynomialDensity.lean` proves polynomial density for every
  finite measure with a full bilateral exponential-moment window.
- `RHTower/GaussianWindowPolynomialDensity.lean` proves the Gaussian instance without using a
  numerical Gaussian integral value.
- `RHTower/ExponentialMomentPolynomialSignCone.lean` proves the polynomial-square sign-cone law.
- `RHTower/CompleteHankelSignCone.lean` proves the finite-Hankel tower equivalence.
- `RHTower/Hedenmalm/HedenmalmGaussianHankelRH.lean` proves the fixed-temperature RH equivalence,
  temperature invariance, and the existential/universal temperature endpoints.

The target module passes the narrow project build.  An explicit `#print axioms` audit of the
polynomial-density theorem, the universal sign-cone theorem, the complete-Hankel theorem, and all
four RH/temperature endpoints reports only Lean's standard logical foundations:
`propext`, `Classical.choice`, and `Quot.sound`.

## Hostile audit

1. **No sign is smuggled in.**  The general theorem recovers the sign of an arbitrary bounded
   continuous multiplier from the entire Hankel tower.  The Hedenmalm sign remains the RH-bearing
   input.
2. **No finite extrapolation.**  The quantifier over every finite degree is essential.
3. **No likelihood/current confusion.**  The multiplier is the actual center-mixed Fourier
   current, not the positive theta-tail likelihood measure.
4. **No numerical evidence.**  The proof uses density, bounded multiplication, indicator
   separation, and exact coefficient identities only.
5. **Novelty boundary.**  Exponential-moment polynomial density, Hamburger Hankel positivity,
   and Fourier-current criteria are classical parent components.  The universal sign-cone theorem
   and one-temperature Hedenmalm synthesis require an independent priority audit before a novelty
   claim.

## Gates

- [x] exact dependency-closed paper proof
- [x] unconditional formal proof of exponential-moment polynomial density
- [x] unconditional formal proof of the universal polynomial and complete-Hankel sign cones
- [x] unconditional formal proof of the one-temperature Hedenmalm/RH equivalence
- [x] narrow module build and explicit axiom audit
- [x] exact statement of the remaining RH-bearing sign theorem
- [ ] independent literature and priority audit of the synthesis
- [ ] formalization of the separate finite-section cooling/recession theorem from the parent card
