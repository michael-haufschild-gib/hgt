# Route U dyadic Cayley source multiresolution

- **ID:** `route-u-dyadic-cayley-source-multiresolution`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE + EXACT BRIDGE CANDIDATE
- **Scientific status:** `[FROZEN CONJECTURE] [TRANSFER MECHANISM FALSIFIED]`
  `[LEAN-FORMALIZED POSITIVE SURVIVOR] [NOVELTY UNVERIFIED]`
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

Mathlib's Chebyshev measure has mass `pi`; division by `pi` gives the probability normalization
used above. The finite even/odd Pythagorean law, its half-refinement form, and the sharp lower bound
are now closed in Lean as

```text
RouteUDyadicCayley.flatPythagorean
RouteUDyadicCayley.flatHalfPythagorean
RouteUDyadicCayley.flatHalfSubmartingale.
```

The exact real-line change-of-variables theorem remains separate; the polynomial/arcsine theorem
already contains the complete parity mechanism needed for the hostile test.

## Hostile-test result: flat transfer to the divisor is invalid

The flat argument compares even and odd sectors at one abstract Cayley coordinate `x`. Route-U
does not evaluate both masses at that coordinate. For spectral node `z`, the mass-`a` node is

```text
x_a(z)=(a^2-z^2)/(a^2+z^2).
```

Lean proves the exact doubled-mass transport

```text
T_2(x_(2a)(z))
  = (16a^4-24a^2z^2+z^4)/(4a^2+z^2)^2.
```

It also proves the exact drift from the original mass-`a` node:

```text
T_2(x_(2a)(z)) - x_a(z)
  = 2 z^4 (z^2-8a^2) / ((4a^2+z^2)^2 (a^2+z^2)).
```

Hence tangent doubling cancels the entire quadratic spectral drift; for fixed `z` the node defect
starts at order `a^-4`. Packet degree grows linearly in `a`, so derivative amplification can raise
its effective size, but any argument treating node motion as a generic order-`a^-2` defect loses a
real cancellation. Lean theorem: `RouteUDyadicCayley.dyadicTransportedNode_sub_cayleyNode`.

Away from tangent-doubling poles, the right side is
`x_a(z/(1-z^2/(4a^2)))`, not `x_a(z)`. This is formalized by
`RouteUDyadicCayley.cayleyNode_doubling_eq_dyadicTransportedNode`.

Therefore arcsine invariance under `T_2` cannot compare `W_(2k+1)` with `W_k`: the Xi divisor is
sampled at a nonlinear drifted spectral node and carries a mass-dependent resolvent weight. The
proposed direct implication `(FLAT-MRA) -> (U-DYS)` is falsified. The scalar conjecture itself is
not disproved, but it now requires a genuinely arithmetic transport theorem rather than parity
orthogonality.

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

## Frozen hostile conjecture U-DYADIC-COHERENCE

The matrix/Carleson replacement above is now subjected to a sharper hostile test. Let `S_k(q)` be
the Route-U lattice sample at mass `a_k=k+1`, and split the fine sample at mass `2a_k` into its even
and odd lattice indices:

```text
S_(2k+1)(q) = E_k(q) + O_k(q).
```

The exact even-index reindexing gives one half of a coarse-mesh periodization evaluated at the
fine Cayley phase. Since both coarse and fine Cayley phases tend to the same spectral point and
alias tails vanish, freeze the prediction

```text
E_k(q) -> F(q)/2,
O_k(q) -> F(q)/2,                                      (U-DYC-point)
```

where `F(q)` is the compact Fourier extension at the Xi spectral point. After the existing
weighted divisor exchange, the three quadratic channels should satisfy

```text
sum_q w_(2k+1)(q) E_k(q)^2       -> L/4,
sum_q w_(2k+1)(q) O_k(q)^2       -> L/4,
sum_q 2 w_(2k+1)(q) E_k(q)O_k(q) -> L/2,              (U-DYC-global)
```

with `L=sum_q F(q)^2`.

If true, the dyadic covariance is asymptotically the rank-one matrix
`(L/4) [[1,1],[1,1]]`. For a false-RH carrier with `Re L<0`, both diagonal channels and the cross
channel are eventually negative in real part. Thus neither scalar odd-detail positivity nor a
positive `2 x 2` Schur complement can be an independent producer. Dyadic refinement would be a
coherent duplication of the signed central trace, not fresh positive capital.

**Falsifier:** one fixed node or one divisor-dominated carrier for which either half does not tend
to `F/2`, or for which weighted square/cross exchange fails despite the existing full-sample
domination. Pointwise proof is attacked first; global exchange is promoted only after its exact
majorant is checked.

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

`[OPEN CORE]` Control the sum of two defects under `a -> 2a`: nonlinear Cayley node transport of
the existing even sector, and completed prime--Gamma even/odd covariance of the fresh detail. A
sharp bound must be global/infinite-tail; finite prime-log jets and scalar Gamma subtraction are
already excluded. Everything after such a bound is a short cofinal-limit contradiction supported
by the Route-U corpus.

## Literature audit

Classical Cayley quadrature, Malmquist--Takenaka rational bases, and Laguerre/Fourier transforms
contain related orthogonality infrastructure. No audited source states the completed zeta
prime--Gamma dyadic refinement or its Route-U cofinal consequence. Novelty remains unverified until
the arithmetic covariance theorem exists and broader literature comparison is complete.

## Log

- 2026-08-14 -- Card opened. Corrected normalization from raw Hankel/source capital to
  `W_k=(k+1)^2 H_k`. Froze `(U-DYS)` with explicit falsifiers. Identified fresh odd Chebyshev
  detail as reason fixed-carrier finite-budget arguments fail.
- 2026-08-14 -- Hostile test falsified the flat-to-source transfer mechanism: dyadic parity is at a
  fixed abstract Cayley node, while the divisor sees exact nonlinear tangent-doubling node drift.
  Proved and Lean-formalized the strongest positive survivor: finite even/odd arcsine Pythagoras,
  exact half-refinement, sharp half-submartingale, and explicit doubled-node transport. Module:
  `formal/GaloisForLFunctions/RHTower/XiShiftedHardEdgeCayleyMultiresolution.lean`; scratch and tree
  `lake env lean` pass; axiom audit is `[propext, Classical.choice, Quot.sound]`; exact `.olean`
  built serially and umbrella import wired without an umbrella build.
- 2026-08-14 -- Strengthened node-transport survivor with exact drift formula. Discovered and
  formalized full quadratic cancellation: doubled-node transport differs from original node only
  through `2 z^4(z^2-8a^2)` over the explicit denominator. Rebuilt exact module `.olean` serially;
  axiom audit unchanged.
