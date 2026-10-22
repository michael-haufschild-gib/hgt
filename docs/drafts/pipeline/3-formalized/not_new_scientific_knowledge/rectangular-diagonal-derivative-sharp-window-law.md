# The sharp dyadic prime window is a diagonal derivative of the rectangular source

- **ID:** `rectangular-diagonal-derivative-sharp-window-law`
- **Stage:** 3-formalized
- **Type:** VALUE RELATION / RH REDUCTION (Lean)
- **Scientific status:** `[FORMALIZATION] [POSITIVE STATEMENT] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`

## Statement

Let

```text
T(L,x)=sum_{k<=exp(x)} Lambda(k)/sqrt(k)
       * max(0,L-|log(k)-x+L|)
```

be the moving triangular prime value in the rectangular autocorrelation source.  Along the
diagonal deformation `(L,x) -> (L+t,x+t)`, the tent centre `x-L` is fixed and its radius grows.
Consequently its right derivative is the closed multiplicative shell

```text
D_+ T(L,x)
 =sum_{exp(x-2L)<=k<=exp(x)} Lambda(k)/sqrt(k).           (1)
```

The polar value paired with this tent is

```text
P(L,x)=4(1-exp(-L/2))^2 exp(x/2)
      +4(exp(L/2)-1)^2 exp(-x/2),
```

and Lean proves the exact diagonal derivative

```text
D P(L,x)
 =2(1-exp(-L))exp(x/2)+2(exp(L)-1)exp(-x/2).             (2)
```

Since the completed adjacent-block source is `A(L,x)=-T(L,x)+P(L,x)`, at
`L=log(2)/2` and `x=log(n)` one obtains

```text
D_+ A
 =2(1-2^(-1/2))*sqrt(n)
  +2(sqrt(2)-1)/sqrt(n)
  -W_closed(n),                                         (3)
```

where `W_closed(n)` contains the requested half-open value

```text
W(n)=sum_{n/2<k<=n} Lambda(k)/sqrt(k).
```

Therefore the single slope lower bound

```text
2(sqrt(2)-1)/sqrt(n)-C*n^epsilon <= D_+ A               (4)
```

implies exactly

```text
W(n)<=2(1-2^(-1/2))*sqrt(n)+C*n^epsilon.                 (5)
```

The only difference between `W_closed` and `W` is the possible lower endpoint `k=n/2`; its
coefficient is nonnegative, so the implication `(4) -> (5)` loses no constant.

This derivative also lifts exactly to the complete rectangular prime--polar coefficient `S`.
Before the first prime logarithm, the fixed prime tent is empty and the width-only sewing term has
derivative

```text
b=8(exp(log(2)/4)-exp(-log(2)/4)).
```

Lean therefore proves

```text
D_+ S(log(2)/2,log(n)/2)=b+2*D_+ A(log(2)/2,log(n)).     (6)
```

Thus a lower bound for the full prime--polar source slope, after subtracting `b`, directly implies
`(5)`; no adjacent-block proposition is exposed at the RH theorem boundary.

## Proof

For one logarithmic prime location `h=log(k)`, write

```text
tau(L,x;h)=max(0,L-|h-(x-L)|).
```

Under `(L,x)->(L+t,x+t)`, the centre `x-L` is unchanged, hence

```text
tau(L+t,x+t;h)=max(0,L+t-|h-(x-L)|).
```

Its right derivative at `t=0` is one when `|h-(x-L)|<=L` and zero otherwise.  This condition is
equivalent to `x-2L<=h<=x`.  Summation over the finite von Mangoldt pairing proves `(1)`, including
both boundary atoms.

Ordinary differentiation of `P` gives `(2)`.  At an integer logarithmic sample, the floor of
`exp(log(n)+t)` remains equal to `n` for all sufficiently small positive `t`; thus the finite-shell
derivative is also the right derivative of the literal adjacent-block source.  Substitution of
`L=log(2)/2` in `(2)` gives the two elementary terms in `(3)`.  Finally `W(n)<=W_closed(n)`, and
combining this inequality with `(3)` and `(4)` proves `(5)`.

## RH leverage

This is the reverse local bridge missing from the earlier sharp-to-rectangular sewing theorem.
The sharp window is no longer an external arithmetic hypothesis: it is read directly from a
one-sided derivative of the same two-parameter rectangular source family used by the Xi
Guinand--Weil value.  Lean now contains direct theorems from either the adjacent-block slope or the
complete prime--polar source slope to `RiemannHypothesis`.  After the remaining Gamma and contour
passages are completed, the proof burden can be attacked on the spectral side as a diagonal
variation estimate rather than by estimating the discontinuous prime window from scratch.

The slope estimate `(4)` is still RH-strength.  Neither the derivative identity nor the present
literature audit supplies its unconditional lower bound.

The critical quadratic-sampling law now composes with this derivative bridge.  It is enough to
prove `(4)` only at the square apertures `n=m^2`.  Equivalently, for every positive `epsilon`, it
is enough to find `C_epsilon >= 0` such that eventually

```text
2(sqrt(2)-1)/m-C_epsilon*(m^2)^epsilon
  <= D_+ A(log(2)/2,log(m^2)).                         (7)
```

The same square-only reduction is formalized for the complete rectangular prime--polar slope in
`(6)`.  Thus the remaining source estimate is required only on the logarithmic lattice
`x=2*log(m)`, rather than at every integer logarithmic sample.  The transfer from this lattice to
all `n` costs only `O(log n)`, which is absorbed by every positive power.

## Lean implementation

```text
GaloisForLFunctions.RHTower.CCM.CCMRectangularDirectionalDerivative
  hasDerivWithinAt_rectangularMovingPrimeTent_diagonal
  hasDerivWithinAt_rectangularMovingPrimeTentSum_diagonal
  hasDerivAt_rectangularAdjacentPolarValue_diagonal
  hasDerivWithinAt_criticalMellinAdjacentBlock_diagonal_logSample
  dyadicWeightedPrimeWindow_le_rectangularClosedPrimeShellValue
  hasDerivWithinAt_dyadicAdjacentBlock_diagonal_logSample
  hasDerivAt_rectangularFixedPrimePolarConstant_add
  hasDerivWithinAt_dyadicPrimePolarSource_diagonal_logSample
  dyadicWeightedPrimeWindow_upper_of_adjacentBlockDiagonalRightSlope_lower
  dyadicWeightedPrimeWindow_upper_of_primePolarSourceDiagonalRightSlope_lower
  riemannHypothesis_of_eventually_dyadicAdjacentBlockDiagonalRightSlope_lower
  riemannHypothesis_of_eventually_dyadicPrimePolarSourceDiagonalRightSlope_lower

GaloisForLFunctions.RHTower.CCM.CCMSharpPrimeWindowSquareSampling
  riemannHypothesis_of_eventually_squareAdjacentBlockDiagonalRightSlope_lower
  riemannHypothesis_of_eventually_squarePrimePolarSourceDiagonalRightSlope_lower
```

The focused module build is green.  `#print axioms` for the two capstone derivative theorems and
the direct dyadic implication reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Gates

- [x] exact fixed-centre tent expansion proved
- [x] right derivative reads the closed multiplicative shell
- [x] polar derivative has the target square-root coefficient
- [x] integer exponential floor shown locally right-constant
- [x] adjacent-block diagonal derivative formalized
- [x] complete prime--polar source diagonal derivative formalized
- [x] direct slope-to-dyadic-window implication formalized
- [x] direct all-epsilon slope-to-RH implications formalized
- [x] critical square-only slope-to-RH implications formalized
- [x] focused build and axiom audit pass
- [ ] prove an unconditional all-epsilon lower bound for the diagonal slope
- [ ] transfer the slope through the completed rectangular Guinand--Weil identity
- [ ] RH
