# Square-aperture positive-excess spectrum is the Xi zero-width spectrum

- **ID:** `square-aperture-positive-excess-zero-width-collision`
- **Stage:** `3-formalized`
- **Type:** `THEOREM (paper) / EXACT ROUTE COLLISION / NOT NEW SCIENTIFIC KNOWLEDGE`
- **Statement:** the square-aperture positive-excess-square Dirichlet abscissa is exactly
  `1+4` times intrinsic right-Xi transverse width whenever that width is positive; its critical
  endpoint is RH.

## Definitions

Put

```text
psi(x) = sum_(n<=x) Lambda(n),
E(x)   = psi(x)-x,
W(n)   = sum_(n/2<k<=n) Lambda(k)/sqrt(k),
c      = 2(1-1/sqrt(2)),
d_m    = W(m^2)-c m,
a_m    = (d_m)_+^2,
sigma_2 = abscissa of absolute convergence of sum_(m>=1) a_m m^(-s).
```

Let

```text
Theta = sup{Re rho : xi(rho)=0},
alpha_* = Theta-1/2.
```

Equivalently, `alpha_*` is `xiRightTransverseSup` in the formal development. If RH is false,
the positive-right Xi divisor is nonempty and `alpha_*>0`.

## Theorem

1. For every `alpha>=0`, if for every `epsilon>0`

   ```text
   E(x) = O_epsilon(x^(1/2+alpha+epsilon)),
   ```

   then

   ```text
   sigma_2 <= 1+4alpha.
   ```

2. The same Chebyshev error spectrum forces every Xi zero into

   ```text
   Re rho <= 1/2+alpha.
   ```

3. If the positive-right Xi divisor is nonempty, the classical generalized von Koch theorem gives

   ```text
   sigma_2 = 1+4alpha_*.
   ```

4. At zero width,

   ```text
   RH
   <-> sigma_2 <= 1
   <-> for every delta>0,
       sum_(m<=M) (d_m)_+^2 = O_delta(M^(1+delta)).
   ```

Consequently Route I's square-aperture positive-excess survivor is not an independent signed
dispersion mechanism. It is the zero-width invariant already exhausted by retired Route C2,
expressed through the affine spectral coordinate `alpha ↦ 1+4alpha`.

## Proof

### 1. Exact Abel identity

Partial summation gives, for every integer `n>=2`,

```text
W(n)
 = c sqrt(n)
   + E(n)/sqrt(n)-E(n/2)/sqrt(n/2)
   + (1/2) [
       integral_1^n E(t)t^(-3/2)dt
       - integral_1^(n/2) E(t)t^(-3/2)dt
     ].
```

The bracket is simply the integral over `(n/2,n]`; the displayed primitive-difference form is the
one already formalized by `dyadicCriticalMellinErrorIncrement`.

Fix `epsilon>0` and write `beta=alpha+epsilon>0`. If

```text
|E(t)| <= C t^(1/2+beta),  t>=1,
```

then both endpoint terms are at most `C n^beta` in absolute value. Moreover,

```text
|integral_1^X E(t)t^(-3/2)dt|
 <= C integral_1^X t^(beta-1)dt
 = (C/beta)(X^beta-1)
 <= (C/beta)X^beta.
```

Since `(n/2)^beta<=n^beta`,

```text
|d(n)| <= (2C+C/beta)n^beta,
```

where `d(n)=W(n)-c sqrt(n)`.

### 2. Square sampling and abscissa upper bound

For `m>=2`, exact square-root normalization gives

```text
d_m = d(m^2).
```

Hence

```text
0 <= a_m
     <= |d(m^2)|^2
     <= (2C+C/beta)^2 m^(4beta).
```

Given any real `y>1+4alpha`, choose

```text
epsilon = (y-(1+4alpha))/8.
```

Then `1+4(alpha+epsilon)<y`, so comparison with the convergent power Dirichlet series gives
absolute convergence at `y`. Since this holds for every `y>1+4alpha`,

```text
sigma_2 <= 1+4alpha.                                      (1)
```

The finitely many coefficients `m=0,1` are absorbed into the comparison constant and do not
affect the abscissa.

### 3. Reverse zero-width implication

The previously proved square-energy sampling theorem is zero-by-zero: if `xi(rho)=0` and
`Re rho>1/2`, then

```text
4 Re rho-1 <= sigma_2.                                    (2)
```

Combining `(1)` and `(2)` yields

```text
4 Re rho-1 <= 1+4alpha,
```

therefore `Re rho<=1/2+alpha`. Zeros on or left of the critical line already satisfy this bound.
Thus the Chebyshev error spectrum cannot be a weak wrapper: it forces the same Xi half-plane
width.

### 4. Intrinsic equality

When `Theta<1`, the classical generalized von Koch theorem says that, for every `epsilon>0`,

```text
psi(x)-x = O_epsilon(x^(Theta+epsilon)).
```

The commonly quoted stronger fixed-exponent form is
`O(x^Theta log(x)^2)` when stated with the usual endpoint convention. Since
`Theta=1/2+alpha_*`, it supplies the hypothesis of `(1)` at `alpha_*`, hence

```text
sigma_2 <= 1+4alpha_*.
```

The passage from the fixed logarithmic form to the all-epsilon form loses no dependency: for
`x>=1`, setting `u=log x` and maximizing `u^2 exp(-epsilon u)` gives

```text
log(x)^2 <= 4/(e^2 epsilon^2) x^epsilon.
```

If the supremum is the limiting value `Theta=1`, Chebyshev's unconditional `psi(x)=O(x)` estimate
instead gives `O_epsilon(x^(1+epsilon))`, which is the same required spectrum at
`alpha_*=1/2`. Thus no unproved assertion that the zero-free strip has fixed positive width is
being used.

Taking the supremum of `(2)` over right Xi zeros gives the reverse inequality, so

```text
sigma_2 = 1+4alpha_*.
```

No claim that the endpoint abscissa equals `1` under RH is needed. Von Koch--Schoenfeld gives only
the required `sigma_2<=1`; the already formalized reverse implication `sigma_2<=1 -> RH` supplies
the exact endpoint equivalence.

Finally, nonnegative-coefficient Dirichlet-abscissa theory identifies `sigma_2<=1` with the
all-supercritical summatory bounds

```text
sum_(m<=M) a_m = O_delta(M^(1+delta)).
```

This is exactly the live convex-dual conjecture, since finite convex duality already proves

```text
sum_(m<=M) a_m
 = sup_(u_m>=0) sum_(m<=M)(2u_m d_m-u_m^2).
```

## Anti-theatre and novelty audit

- `[NEW INTERNAL INFRASTRUCTURE]` Exact Chebyshev-error-to-square-energy abscissa transfer, including
  Abel endpoint, primitive, square-sampling, and coefficient-growth bookkeeping.
- `[NOT NEW SCIENTIFIC KNOWLEDGE]` Generalized von Koch already identifies prime-number-theorem
  error exponent with rightmost zeta-zero exponent. Schoenfeld owns the explicit RH endpoint used
  in the earlier full-correlation card.
- `[EXACT COLLISION]` Route C2 already recovers `XiZeroHalfPlaneBound alpha` exactly. The theorem
  above shows the square-aperture survivor recovers and is recovered by the same width after the
  classical source theorem. Calling this a new unconditional signed-dispersion estimate would be
  analytic-lift theatre.
- `[NO RH PROOF]` The source estimate at `alpha=0` is RH-strength. Nothing here proves it
  unconditionally.

Primary/authoritative sources:

- J. Pintz, *On the remainder term of the prime number formula and the zeros of Riemann's
  zeta-function*, Lecture Notes in Mathematics 1068 (1984),
  <https://doi.org/10.1007/BFb0099452>.
- L. Schoenfeld, *Sharper Bounds for the Chebyshev Functions theta(x) and psi(x). II*,
  Mathematics of Computation 30 (1976),
  <https://doi.org/10.1090/S0025-5718-1976-0457374-X>.
- *Encyclopedia of Mathematics*, “Distribution of prime numbers,” which records
  `psi(x)=x+O(x^Theta log^2 x)` for the supremal zero ordinate,
  <https://encyclopediaofmath.org/wiki/Distribution_of_prime_numbers>.

## Formal certificate

Module:

```text
formal/GaloisForLFunctions/RHTower/
  CCMSharpPrimeWindowSquareEnergyWidthCollision.lean
```

Unconditional theorems:

- `dyadicCriticalMellinErrorIncrement_abs_le_of_chebyshevErrorPower`
- `squarePrimeWindowCenteredDeviation_eq_errorIncrement`
- `squarePrimeWindowPositiveExcess_le_errorIncrement_abs`
- `squarePrimeWindowPositiveExcessSquare_coefficient_norm_le`
- `squarePrimeWindowPositiveExcessSquare_abscissa_le_of_chebyshevErrorPowerSpectrum`
- `xiZeroHalfPlaneBound_of_chebyshevErrorPowerSpectrum`

Endpoint module:

```text
formal/GaloisForLFunctions/RHTower/
  CCMSharpPrimeWindowSquareEnergyZeroWidthEquivalence.lean
```

Closed endpoint theorems:

- `squarePrimeWindowPositiveExcessSquare_abscissa_le_one_of_riemannHypothesis`
- `riemannHypothesis_iff_squarePrimeWindowPositiveExcessSquare_abscissa_le_one`
- `riemannHypothesis_iff_squarePrimeWindowPositiveExcessSquare_summatory_subpower`
- `squarePrimeWindowPositiveExcessSquare_abscissa_le_one_iff_summatory_subpower`
- `squarePrimeWindowPositiveExcessSquare_zeroWidthCollision`

These declarations close the exact RH endpoint and literal all-supercritical summatory-growth
equivalence. The generalized-von-Koch leaf
`CCMGeneralizedVonKoch.lean` discharges the former source premise and proves the closed intrinsic
identity
`squarePrimeWindowPositiveExcessSquare_abscissa_eq_intrinsicXiWidth_unconditional`.
All three leaves are imported by `GaloisForLFunctions.RHTower`.

Verification:

- exact source check:
  `lake env lean GaloisForLFunctions/RHTower/CCMSharpPrimeWindowSquareEnergyZeroWidthEquivalence.lean`
- exact leaf build:
  `lake build GaloisForLFunctions.RHTower.CCMSharpPrimeWindowSquareEnergyZeroWidthEquivalence`
- axiom audit of all five new endpoint declarations: only `propext`, `Classical.choice`, and
  `Quot.sound`; no project axiom and no `sorryAx`.
- `squarePrimeWindowPositiveExcessSquare_abscissa_eq_intrinsicXiWidth`
- `riemannHypothesis_of_chebyshevErrorPowerSpectrum_zero`

Lean now proves generalized von Koch in the exact transparent source proposition:

- `chebyshevErrorPowerSpectrum_of_xiZeroHalfPlaneBound`
- `xiZeroHalfPlaneBound_xiRightTransverseSup`
- `squarePrimeWindowPositiveExcessSquare_abscissa_eq_intrinsicXiWidth_unconditional`

The proof handles `alpha<1/2` by a parameterized zero-free Perron contour and handles
`alpha>=1/2` by the unconditional linear Chebyshev bound. Exact source check and exact leaf build
both pass for `GaloisForLFunctions.RHTower.CCMGeneralizedVonKoch`; axiom audit of all 22 new
declarations reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Gates

- [x] exact Abel identity
- [x] power-integral estimate
- [x] square-sampled coefficient upper bound
- [x] Dirichlet-abscissa upper bound
- [x] zero-by-zero reverse lower bound
- [x] intrinsic-width equality on paper
- [x] exact collision with C2 width invariant
- [x] all downstream implications after `ChebyshevErrorPowerSpectrum` formalized in Lean
- [x] generalized von Koch formalized in Lean
- [x] closed intrinsic-width equality theorem with no source-estimate premise

## Log

- 2026-08-01 — exact quantitative collision paper-proved and downstream transfer formalized.
- 2026-08-23 — generalized von Koch and closed intrinsic-width equality formalized; card promoted.
