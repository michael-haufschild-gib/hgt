# Route U dyadic Cayley source multiresolution

- **ID:** `route-u-dyadic-cayley-source-multiresolution`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE + EXACT BRIDGE CANDIDATE
- **Scientific status:** `[FROZEN CONJECTURE] [HOSTILE TESTING] [NOVELTY UNVERIFIED]`
- **Source:** Route U hard-edge cofinal source inversion and degree-free Cauchy density
- **Statement:** Dyadic hard-edge refinement is an exact even/odd Chebyshev multiresolution for
  the flat Cauchy energy; RH would follow if the completed prime--Gamma functional retained the
  corresponding half-submartingale inequality on the fixed false-RH carrier.

## Goal

Exclude `XiShiftedHardEdgeCofinalPrimeGammaInversionPhase` without treating linear packet growth as
a finite-resource contradiction. The decisive object is the arithmetic cross-covariance between
old even Chebyshev modes and newly admitted odd modes under dyadic hard-edge refinement.

## Gates

- [x] 0 -> 1 in-progress: source-pure statement, exact scaling, falsifiers, corpus shadow map
- [ ] 1 -> 2 fully-proven: dependency-closed flat refinement theorem plus proved source sign law or
  rigorously falsified scalar law and strongest surviving replacement
- [ ] 2 -> 3 formalized: closed Lean theorem(s), serial scratch verification, axiom audit, umbrella
  import, exact missing `.olean` build
- [ ] 3 -> 4 publication-ready: standalone theorem, proof, novelty audit, Lean certificate

## Exact Route-U normalization

Fix one polynomial--Gaussian carrier `P,t` and cutoff index `n`. At integral hard-edge mass

```text
a_k = k+1,
H_k = routeUExplicitPolynomialGaussianFiniteHankelQuadratic P t n k,
W_k = a_k^2 H_k.
```

Existing Lean identifies `W_k` exactly with the real part of the hard-edge sample divisor sum. The
false-RH construction chooses `P,t,n` so that `W_k` converges to one fixed negative cutoff divisor
trace. In particular, comparing raw `H_k`, or the factorial-weighted literal source capital, has
the wrong scale. Every conjecture below concerns `W_k`.

## Frozen bold conjecture U-DYADIC-SOURCE

For every Route-U polynomial--Gaussian carrier and cutoff index, the normalized completed-source
packet eventually obeys the dyadic half-submartingale inequality

```text
W_(2k+1) >= (1/2) W_k.                                  (U-DYS)
```

Here `a_(2k+1)=2a_k`, so this is exactly the mass refinement `a -> 2a`.

### Why it would close RH

If RH is false, existing Lean gives fixed `P,t,n` and `L<0` with `W_k -> L`. Passing to the dyadic
subsequence in `(U-DYS)` gives `L >= L/2`, impossible because `L<0`. Thus a source-pure proof of
`(U-DYS)` on every sufficiently large fixed-carrier packet excludes the existing closed false-RH
phase.

### Falsifiers

The conjecture is killed by any one of:

1. an exact admissible carrier and index with infinitely many `k` satisfying
   `W_(2k+1) < W_k/2`;
2. a corpus theorem showing completed prime--Gamma even/odd cross-covariance has unrestricted sign;
3. a source decomposition in which the odd detail square is accompanied by an uncontrolled linear
   cross term that cannot be absorbed by any cofinal tail estimate;
4. a theorem that `(U-DYS)` is stronger than RH and fails for an RH-compatible completed source.

No numerical experiment counts as proof or refutation.

## Exact flat model exposed by the source density

Let `A : R -> R` be the fixed compact even physical amplitude and `h_a=2/a`. Define the finite
Chebyshev packet

```text
B_a(cos theta)
  = h_a A(0) + 2h_a sum_(m>=1) A(h_a m) cos(m theta).
```

At doubled mass, fine frequencies split into even and odd indices:

```text
B_(2a)(x) = (1/2) B_a(T_2(x)) + D_a(x),
D_a(x)    = h_a sum_(m>=0) A(h_a(m+1/2)) T_(2m+1)(x).
```

For Chebyshev probability measure `mu_T`, even and odd modes are orthogonal and `T_2` preserves
`mu_T`. Therefore the candidate exact Pythagorean law is

```text
||B_(2a)||_(mu_T)^2
  = (1/4)||B_a||_(mu_T)^2 + ||D_a||_(mu_T)^2.           (FLAT-MRA)
```

The hard-edge Cayley substitution

```text
x = a tan(theta/2),
(a^2-x^2)/(a^2+x^2) = cos(theta),
a^2/(a^2+x^2) dx = (a/2) dtheta
```

turns the formalized degree-free density into

```text
integral_R routeUHardEdgeCauchyDensity a B_a x dx
  = pi*a*||B_a||_(mu_T)^2.
```

Consequently its flat real-line energy has the exact refinement

```text
E_(2a) = (1/2) E_a + 2*pi*a*||D_a||_(mu_T)^2.          (CAUCHY-MRA)
```

Constants will be fixed against mathlib's exact normalization before promotion to paper theorem.

## Anti-theatre interpretation

Fixed physical carrier does **not** mean fixed angular resource. Every dyadic refinement admits a
fresh orthogonal odd Chebyshev sector. Linear packet growth is orthogonal renewal, not repeated use
of a finite-dimensional budget. Hence no contradiction may be inferred from fixed carrier plus
cofinal dimension alone.

The flat law proves positivity only for the Cauchy reference measure. The completed prime--Gamma
functional is signed and is not known to diagonalize Chebyshev parity. Claiming that `(FLAT-MRA)`
implies `(U-DYS)` without controlling the arithmetic even/odd covariance is invalid.

## Corpus shadow map

- `XiShiftedHardEdgeCofinalLinearFiniteHankelDimension.lean`: supplies exact dyadic-compatible
  packet and the normalized sample divisor sum `W_k`.
- `XiShiftedHardEdgePrimeGammaSourceDisintegration.lean`: identifies literal completed source
  capital and degree-free Cauchy hard-edge density.
- cofinal positive-schedule no-go: fixed degree, recession, and arbitrary cofinal reindexing cannot
  distinguish RH; a genuine cross-scale source law is required.
- prime-log finite-jet controllability: no finite local prime--Gamma jet sign can supply the needed
  inequality.
- infinite renormalization-rank theorem: a successful prime--Gamma seam must retain infinitely many
  source directions; dyadic odd-sector renewal is compatible with this constraint.
- Gamma hypertranscendence Hankel no-go: archimedean transcendence alone gives no sign; arithmetic
  coupling must orient the cross-covariance.

## Risky prediction

After Chebyshev parity decomposition, the completed source need not have a nonnegative scalar odd
increment. The sharper surviving structure is predicted to be a positive `2 x 2` Schur complement
or a Carleson square-function bound in which the even--odd arithmetic covariance is controlled by
the odd diagonal energy. If true, its cofinal consequence should still forbid convergence to a
negative fixed point.

## Attack loop

1. Prove `(FLAT-MRA)` exactly on paper and in Lean.
2. Expand `W_(2k+1)-W_k/2` through the existing sample-divisor identity, not through a generic
   positive measure surrogate.
3. Separate diagonal odd energy, even transport, and completed arithmetic cross-covariance.
4. Search corpus no-gos for a sign-indefinite witness. If found, falsify `(U-DYS)` immediately and
   retain exact covariance decomposition as survivor.
5. Otherwise attack the cross term using the literal Gamma--polar--von-Mangoldt balance and an
   infinite-tail inequality. Finite jets and scalar Gamma subtraction are forbidden dead ends.
6. If scalar sign fails, promote the minimal matrix/Carleson statement that still contradicts a
   negative cofinal fixed point.

## Open core

`[OPEN CORE]` Determine the exact sign or sharp norm bound for completed prime--Gamma even/odd
Chebyshev covariance under `a -> 2a`. This is the first unproved step. Everything after it is a
short cofinal-limit contradiction already supported by the Route-U corpus.

## Literature audit

Classical Cayley quadrature, Malmquist--Takenaka rational bases, and Laguerre/Fourier transforms
contain related orthogonality infrastructure. No audited source states the completed zeta
prime--Gamma dyadic refinement or its Route-U cofinal consequence. Novelty remains unverified until
the arithmetic covariance theorem exists and broader literature comparison is complete.

## Log

- 2026-08-14 -- Card opened. Corrected normalization from raw Hankel/source capital to
  `W_k=(k+1)^2 H_k`. Froze `(U-DYS)` with explicit falsifiers. Identified fresh odd Chebyshev
  detail as reason fixed-carrier finite-budget arguments fail.
