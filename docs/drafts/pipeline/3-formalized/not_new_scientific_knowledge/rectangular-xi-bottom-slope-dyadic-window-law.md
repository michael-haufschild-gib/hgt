# The sharp dyadic prime window is a corrected Xi bottom-edge slope

- **ID:** `rectangular-xi-bottom-slope-dyadic-window-law`
- **Stage:** 3-formalized
- **Type:** VALUE RELATION / RH PROOF-BURDEN REDUCTION (Lean)
- **Scientific status:** `[FORMALIZATION] [POSITIVE STATEMENT] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`

## Exact bottom-edge value

Let `B_Xi(L,a)` be the normalized absolutely convergent bottom-edge integral of the squared
rectangular transform against `XiC'/XiC`, and let `B_infinity(L,a)` be the corresponding
archimedean logarithmic-derivative integral.  Define

```text
V(L,a)=Re(B_Xi(L,a)-B_infinity(L,a))+2*P(L,a)^2,
```

where `P` is the elementary even polar feature.  Lean proves unconditionally

```text
V(L,a)=rectangularPrimePolarSourceCoefficient(L,a)       (0<=L<=a).
```

The proof uses the honest Euler-line Dirichlet series for `-zeta'/zeta`, sharp Fourier inversion
at piecewise-linear autocorrelation regularity, and an integrable Gamma majorant.  There is no
test-regularity interface, continuation hypothesis, zero-location hypothesis, or project axiom.

## Exact slope readout

Put `L_0=log(2)/2`, `a_n=log(n)/2`, and deform

```text
(L,a)=(L_0+t,(log(n)+t)/2).
```

This keeps the two-edge centre `a-L/2` fixed while opening the width.  If `D_+V(n)` denotes the
right derivative at `t=0`, Lean proves

```text
D_+V(n)
 = b_0
   +4*(1-1/sqrt(2))*sqrt(n)
   +4*(sqrt(2)-1)/sqrt(n)
   -2*W_closed(n),

b_0=8*(exp(log(2)/4)-exp(-log(2)/4)),
W_closed(n)=sum_(n/2<=k<=n) Lambda(k)/sqrt(k).
```

Since the requested half-open value `W(n)` satisfies `W(n)<=W_closed(n)`, the single value-slope
lower bound

```text
b_0+4*(sqrt(2)-1)/sqrt(n)-2*C_epsilon*n^epsilon <= D_+V(n)
```

implies exactly

```text
W(n)<=2*(1-1/sqrt(2))*sqrt(n)+C_epsilon*n^epsilon.
```

Thus the remaining arithmetic inequality is now a lower bound for a literal corrected Xi
bottom-edge derivative.  No constant is lost; the closed-shell discrepancy is a nonnegative
endpoint atom.

## Lean implementation

```text
GaloisForLFunctions.RHTower.XiGuinandWeilRectangularArchimedean
  integrable_rectangularBottomArchIntegrand

GaloisForLFunctions.RHTower.XiGuinandWeilRectangularBottomEdge
  integrable_rectangularBottomXiLogDerivIntegrand
  normalizedRectangularBottomXiContribution_eq_prime_add_arch

GaloisForLFunctions.RHTower.XiGuinandWeilRectangularBottomSlope
  rectangularCorrectedBottomXiValue_eq_primePolarSource
  dyadicPrimePolarSourceDiagonalRightSlope_eq_closedShell
  hasDerivWithinAt_dyadicCorrectedBottomXiValue_diagonal_logSample
  dyadicWeightedPrimeWindow_upper_of_correctedBottomXiSlope_lower
```

The focused build is green.  `#print axioms` for all capstone declarations reports only
`propext`, `Classical.choice`, and `Quot.sound`.  The formal lint gate passes.

## Remaining RH burden

The relation closes the prime/Gamma/bottom-edge identification and the transfer to the target
dyadic window.  It does not supply the lower bound for `D_+V(n)`.  The next analytic step is to
pass the symmetric rectangular contour to its spectral residue value by proving vertical-edge
vanishing, and then establish a one-sided subpower lower bound for the resulting spectral
diagonal derivative.  That last sign/size statement is RH-bearing.

## Gates

- [x] sharp Fourier inversion at rectangular autocorrelation regularity
- [x] absolute integrability of the Gamma bottom edge
- [x] exact normalized Xi bottom-edge prime/Gamma splitting
- [x] corrected bottom edge equals the finite prime--polar source
- [x] corrected-bottom diagonal derivative reads the closed dyadic shell
- [x] direct corrected-slope-to-requested-window theorem
- [x] focused build, axiom audit, and formal lint
- [ ] vertical-edge vanishing and infinite symmetric-contour passage
- [ ] unconditional one-sided subpower lower bound for the spectral slope
- [ ] RH
