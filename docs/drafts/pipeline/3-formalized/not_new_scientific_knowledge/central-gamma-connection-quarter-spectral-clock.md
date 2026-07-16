# Central real-Gamma connection as a quarter-shift positive spectral clock

- **ID:** `central-gamma-connection-quarter-spectral-clock`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), `[BRIDGE]`, archimedean source value relation
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean module:** `GaloisForLFunctions.RHTower.GammaRealConnectionSpectralHankel`
- **Parent HTGeometry card:** `shifted-polygamma-positive-spectral-clock.md`
- **Statement:** Every positive-order derivative of the Deligne real-Gamma logarithmic connection
  at the functional-equation center is an explicit scalar multiple of the positive quarter-shift
  spectral moment; after exact normalization, its entire jet has strictly positive Hankel blocks.

## RHTower value relation

The existing archimedean connection is

```text
Omega_infinity(s) = -log(pi)/2 + psi(s/2)/2.                (1)
```

Lean first proves the all-order chain rule

```text
Omega_infinity^(m+1)(s)
  = (1/2)^(m+2) psi^(m+1)(s/2).                            (2)
```

At the functional-equation center `s=1/2`, the digamma argument is `1/4`.  Combining `(2)` with
the new shifted-polygamma spectral theorem gives

```text
Omega_infinity^(m+1)(1/2)
  = (1/2)^(m+2) (-1)^(m+2) (m+1)!
      sum_(j>=0) (j+1/4)^(-m-2).                           (3)
```

Define the normalized central connection jet

```text
A_m = Re(2^(m+2) (-1)^(m+2)
         Omega_infinity^(m+1)(1/2)/(m+1)!).                (4)
```

Lean proves the exact identity

```text
A_m = sum_(j>=0) (j+1/4)^(-m-2).                           (5)
```

This is an identity for the actual `gammaRealLogConnection` used by RHTower, not an analogy or a
separately postulated oscillator model.

## Positive statement and direct corpus discharge

Equation `(5)` supplies a positive infinite-support spectral measure for the normalized
archimedean source jet.  Reusing the HTGeometry strict moment theorem, Lean proves

```text
[A_(i+j)]_(0<=i,j<N) is positive definite,
det [A_(i+j)]_(0<=i,j<N) > 0                              (6)
```

for every finite `N`.  The determinant in `(6)` directly discharges the hypotheses of the existing
finite spectral-width, finite state-space, and linear-recurrence boundaries.  Thus the normalized
central Gamma connection cannot be reproduced by any uniformly bounded version of those models.

The positive statement is stronger than the no-go: the archimedean connection has an explicit
infinite oscillator ladder with positive weights and distinct reported reciprocal energies.

## Lean surface

- `iteratedDeriv_gammaRealLogConnection_succ`
- `iteratedDeriv_gammaRealLogConnection_half_eq_quarterMoment`
- `normalizedGammaRealConnectionJet`
- `normalizedGammaRealConnectionJet_eq_quarterMoment`
- `normalizedGammaRealConnectionJet_hankel_posDef`
- `det_normalizedGammaRealConnectionJet_hankel_pos`
- `normalizedGammaRealConnectionJet_not_fixedSpectralWidthLocalClosure`
- `normalizedGammaRealConnectionJet_not_fixedStateSpaceDimensionLocalClosure`
- `normalizedGammaRealConnectionJet_not_linearRecurrence`

## RH impact and remaining producer

This theorem upgrades the previous boundary precisely where the RH route needs source truth: the
Gamma part of the completed prime--Gamma connection now has a proved positive infinite-support
spectral representation at the center.  Therefore future decompositions do not need to assume or
reprove archimedean positivity, summability, support separation, or strict Hankel rank.

It still does not prove positivity of the full normalized prime--archimedean moment tower.  The
continued prime source is coupled additively to `(1)`, and subtracting a positive Gamma component
from the total does not preserve positivity in either direction.  To discharge
`PrimeArchMomentRepresentation`, one still needs either:

1. a positive representing measure for the prime residual in the same normalization and clock
   coordinate; or
2. a direct positive measure for the coupled total, with equation `(3)` used as its fixed
   archimedean summand.

The theorem therefore removes the Gamma-side producer obligation but leaves the prime-side sign
problem exposed.  It advances the RH search by narrowing, not by restating, the remaining gate.

## Physics provenance

M. Tierz and E. Elizalde, *Heat kernel-zeta function relationship coming from the classical moment
problem*, arXiv:math-ph/0112050, provides the quantum-mechanical spectral-zeta/moment framework.
The quarter-shift in `(3)` is forced internally by the real-Gamma half argument at `s=1/2`; it is
not chosen to imitate a physical spectrum.

## Anti-theatre verdict

The calculus and spectral-moment ingredients are known.  The corpus value is the exact wiring of
those ingredients into the actual RHTower archimedean source and the resulting discharge of several
existing finite-model hypotheses.  It is not advertised as new scientific knowledge.

## Verification

- [x] exact module target built and cached in one foreground process
- [x] direct touched-file Lean check passed
- [x] no numerical computation used
- [x] selected capstones depend only on `propext`, `Classical.choice`, and `Quot.sound`
- [x] module imported by the RHTower umbrella
- [x] no full or self-concurrent Lean build used
