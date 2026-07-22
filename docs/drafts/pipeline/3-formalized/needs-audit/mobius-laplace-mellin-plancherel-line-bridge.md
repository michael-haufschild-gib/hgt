# Exact Mellin--Plancherel line bridge for the Möbius--Laplace source

- **ID:** `mobius-laplace-mellin-plancherel-line-bridge`
- **Stage:** 3-formalized
- **Type:** THEOREM / ANALYTIC CONNECTOR
- **Scientific status:** `[PROVED] [NEW TO CORPUS] [STANDARD INFRASTRUCTURE] [NOT AN RH PROOF]`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/MobiusLaplaceMellinPlancherelBridge.lean`
- **Parent:** Gamma--Hankel localization; boundary-zero energy divergence

## Statement

For `f : R -> C`, define its logarithmic Mellin-line source

```text
g_sigma(u) = exp(-sigma u) f(exp(-u)).                         (MP1)
```

Mathlib's Mellin and Fourier normalizations satisfy the pointwise identity

```text
M f(sigma+i y) = Fourier(g_sigma)(y/(2 pi)).                  (MP2)
```

If `g_sigma` belongs to `L1(R) ∩ L2(R)`, then

```text
integral_R |M f(sigma+i y)|^2 dy
  = 2 pi integral_R |g_sigma(u)|^2 du.                        (MP3)
```

Specializing `f=Phi`, the discrete Möbius Laplace transform, gives the exact infinite-aperture
Mellin--Plancherel connector required by the Gamma--Hankel frontier.

## Proof

Equation `(MP2)` is Mellin's logarithmic change of variables with the explicit `2*pi` Fourier
frequency normalization. For `(MP3)`, turn the `L2` source into an `Lp` element. Its unitary
Fourier transform agrees almost everywhere with the classical `L1` Fourier integral by the
existing tempered-distribution bridge. Plancherel preserves the squared norm. Finally,
`y=2*pi*xi` contributes the factor `2*pi`.

No continuity, pointwise decay, zeta zero, or RH premise is used.

## Lean certificate

Verified declarations:

```text
logMellinLineSource
mellin_line_eq_fourier_logMellinLineSource
integrable_norm_sq_mellin_line_of_logMellinLineSource
integral_norm_sq_mellin_line_eq_logMellinLineSource
integral_norm_sq_ge_two_mul_sq_div_of_window_floor
mobiusLaplaceLogMellinLineSource
continuous_mobiusLaplaceLogMellinLineSource
mobiusLaplaceLogMellinLineSource_add
norm_mobiusLaplaceLogMellinLineSource_le_exp
norm_mobiusLaplaceLogMellinLineSource_le_exp_of_nonpos
mobiusLaplaceLogMellinLineSource_memLp_two_of_one_lt
mobiusLaplaceLogMellinLineSource_memLp_two_of_base
integrable_mobiusLaplaceLogMellinLineSource_of_base
exists_uniform_integral_norm_sq_mobiusLaplaceLogMellinLineSource_of_base
mellin_mobiusDiscreteLaplaceTransform_line_eq_fourier
integral_norm_sq_mellin_mobiusDiscreteLaplaceTransform_line_eq
exists_uniform_integral_norm_sq_mellin_mobiusDiscreteLaplaceTransform_line_of_base
analyticOnNhd_mellin_mobiusDiscreteLaplaceTransform_of_base
mellin_mobiusDiscreteLaplaceTransform_mul_zetaResidueUnit_eq_of_base
exists_boundary_zero_vertical_window_floor_of_canonical_identity
riemannZeta_ne_zero_of_memLp_mobiusLaplaceLogMellinLineSource_closed
MobiusLaplaceStrictRightEnergyFinite
MobiusLaplaceCofinalStrictRightEnergyFinite
mobiusLaplaceCofinalStrictRightEnergyFinite_iff_strictRightEnergyFinite
mobiusDiscreteLaplaceFiniteSection
mobiusDiscreteLaplaceFiniteSection_eq_finiteMobiusLaplacePencil
mobiusLaplaceFiniteSectionLogMellinLineSource
integral_norm_sq_mobiusLaplaceFiniteSectionLogMellinLineSource
mobiusLaplaceFiniteSectionLogMellinLineSource_memLp_two
MobiusLaplaceCofinalFiniteSectionEnergyBounded
MobiusLaplaceCofinalGammaHankelOffDiagonalUpperBounded
MobiusLaplaceCofinalGammaHankelOffDiagonalFrequentlyUpperBounded
mobiusLaplaceCofinalFiniteSectionEnergyBounded_of_gammaHankelOffDiagonal
mobiusLaplaceCofinalStrictRightEnergyFinite_of_gammaHankelOffDiagonalFrequently
mobiusLaplaceCofinalStrictRightEnergyFinite_of_finiteSectionEnergyBounded
mobiusLaplaceStrictRightEnergyFinite_of_allStrictHalfPowerDecay
mobiusLaplaceStrictRightEnergyFinite_implies_riemannHypothesis
mobiusLaplaceCofinalStrictRightEnergyFinite_implies_riemannHypothesis
mobiusLaplaceCofinalFiniteSectionEnergyBounded_implies_riemannHypothesis
mobiusLaplaceCofinalGammaHankelOffDiagonalUpperBounded_implies_riemannHypothesis
mobiusLaplaceCofinalGammaHankelOffDiagonalFrequentlyUpperBounded_implies_riemannHypothesis
mobiusLaplaceStrictRightEnergyFinite_iff_riemannHypothesis_of_decay
mobiusLaplaceCofinalStrictRightEnergyFinite_iff_riemannHypothesis_of_decay
```

Verification:

```text
lake env lean GaloisForLFunctions/RHTower/MobiusLaplaceMellinPlancherelBridge.lean  PASS
```

Principal theorem endpoints use only `propext`, `Classical.choice`, and `Quot.sound`.

## Frontier reduction

Suppose the base Gamma--Hankel energy `E_sigma` is finite. Lean now proves, uniformly for
`0<r<=r0`:

```text
g_(sigma+r) in L1 ∩ L2,
integral |g_(sigma+r)|^2 <= C(E_sigma,r0).                    (MP4)
```

Near `u=+infinity`, `(MP4)` is Cauchy--Schwarz against `exp(-r u)`. Near `u=-infinity`, Lean uses
the elementary bound `|Phi(x)| <= 1/x`. A single indicator majorant gives the uniform `L2`
ceiling; exact Mellin--Plancherel then gives a uniform full vertical-line Mellin ceiling.

The arithmetic/meromorphic boundary connector is now closed. Lean propagates the denominator-free
identity

```text
M Phi(s) * ((s-1) zeta(s)) = Gamma(s) * (s-1)
```

through the energy half-plane. At a boundary zero, finite analytic order gives
`zeta(z)=(z-rho)^m p(z)`, with `m>=1` and `p(rho)!=0`. Continuity of `Gamma/p` gives a uniform
nonzero local floor. On the vertical window `|t-Im(rho)|<=r`, Lean obtains

```text
|M Phi(sigma+r+i t)| >= c/r,
integral_R |M Phi(sigma+r+i t)|^2 dt >= 2*c^2/r.
```

This contradicts `(MP4)`. Consequently one finite base energy excludes every genuine zeta zero
in the **closed** half-plane `Re(s)>=sigma`.

Lean also packages the exact remaining source frontier:

```text
forall sigma>1/2, g_sigma in L2  ->  RiemannHypothesis.
```

The classical pointwise hierarchy maps into this mean-square source:

```text
forall b>1/2, Phi(x)=O(x^(-b))
  -> forall sigma>1/2, g_sigma in L2.
```

Thus the energy route is a genuine weakening of the existing pointwise criterion. Given the
classical Littlewood converse source, Lean exposes the exact energy/RH equivalence.

The source family compresses further. It is enough that for every `epsilon>0` there exists just
one finite-energy abscissa

```text
1/2 < sigma < 1/2 + epsilon.
```

Finite energy propagates to every line on its right by the contractive logarithmic tilt, so this
cofinal sparse predicate is exactly equivalent to the all-lines predicate and implies RH. No
uniform constant across the chosen lines is required. Conversely, all `sigma>1` energies are
unconditional from the global elementary bound `|Phi(x)|<=1/x`; only the interval immediately
right of `1/2` contains the source difficulty.

This bridge does not prove `E_sigma<infinity`. That source estimate remains RH-equivalent when
required for every `sigma>1/2`.

The finite source has now been reduced to its exact signed arithmetic component.  For every finite
aperture `N` and `sigma>0`, Lean proves

```text
integral_R |g_(N,sigma)(u)|^2 du
  = Gamma(2 sigma) sum_(m,n<=N) mu(m)mu(n)/(m+n)^(2 sigma).   (MP5)
```

Split the right side into diagonal mass `D_N` and signed off-diagonal covariance `O_N`.  When
`2 sigma>1`, `D_N` has an aperture-independent convergent p-series majorant.  Positivity of the
whole Gamma--Hankel form also gives `O_N >= -D_N`.  Therefore

```text
sup_N (D_N + O_N) < infinity
  iff
sup_N O_N < infinity.                                        (MP6)
```

Only the **upper sign** of off-diagonal Möbius covariance remains.  No absolute correlation bound,
lower bound, or diagonal estimate is open.  If `(MP6)` holds at exponents `2 sigma` cofinal from
the right at `1`, finite-section Fatou convergence gives the full cofinal source energy and RH.

Uniformity in aperture is also unnecessary.  Lean now proves a bounded-return compression:

```text
for every epsilon>0 choose 1 < r < 1+2 epsilon and C such that
  O_N(r) <= C for infinitely many arbitrarily large N
  -> RH.                                                       (MP7)
```

Indeed, the diagonal ceiling turns each bounded off-diagonal return into a bounded full-energy
return.  Extract an increasing aperture subsequence and apply Fatou to its pointwise limit.  Thus a
hypothetical zero with `Re rho >= r/2` forces `O_N(r) -> +infinity`: it cannot merely create sparse
energy spikes.  The exact remaining source problem is to prove arbitrarily large bounded returns,
not a bound for every aperture.

Adjacent literature does not close `(MP6)`.  Mangerel's 2024 Liouville theorem proves only strict
saving from the trivial bound for each antidiagonal, without a growing quantitative gap.  The
Misra--Saha--Sharma additive-convolution theorem assumes absolutely convergent Ramanujan
expansions and does not apply to Möbius.  Log-averaged/averaged-shift Chowla results concern fixed
or averaged translation shifts, not the growing reflection `m -> k-m` with the cofinal Hankel
weight.  No matching one-sided aperture-uniform covariance theorem was found; novelty status
remains unverified.

## Gates

- [x] exact Mellin--Fourier normalization proved
- [x] classical/unitary Fourier equality connected
- [x] exact `L2` line identity proved
- [x] concrete Möbius specialization compiled
- [x] formalize base-energy-to-uniform-interior-source transport
- [x] derive uniform infinite-aperture Mellin-line norm
- [x] connect actual `Gamma/zeta` boundary-zero factorization to pole lower bound
- [x] prove closed-half-plane zero exclusion from one finite base energy
- [x] connect strict-right energy family directly to `RiemannHypothesis`
- [x] connect all-strict-half-power pointwise decay to strict-right energy
- [x] compress all strict-right energies to a cofinal sparse family at `1/2`
- [x] prove unconditional finite energy on every line `sigma>1`
- [x] identify finite log energy exactly with finite Möbius Gamma--Hankel energy
- [x] prove diagonal energy uniformly summable for every Gamma exponent `r>1`
- [x] prove positivity supplies a uniform lower floor for off-diagonal covariance
- [x] compress finite energy to a one-sided off-diagonal upper ceiling
- [x] pass cofinal finite-section ceilings to the infinite source by Fatou
- [x] connect cofinal one-sided covariance ceilings directly to RH
- [x] remove aperture-uniformity: arbitrarily large bounded covariance returns suffice
- [x] prove an off-critical zero forces one-sided covariance escape with no bounded subsequence
- [x] expose conditional exact energy/RH equivalence interface
- [ ] prove `MobiusLaplaceCofinalGammaHankelOffDiagonalFrequentlyUpperBounded` unconditionally
