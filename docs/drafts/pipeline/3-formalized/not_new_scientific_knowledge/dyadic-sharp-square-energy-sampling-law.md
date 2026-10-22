# Critical square-sample energy controls the full dyadic sharp excess

- **ID:** `dyadic-sharp-square-energy-sampling-law`
- **Stage:** 3-formalized
- **Type:** VALUE RELATION / PROOF-BURDEN REDUCTION
- **Scientific status:** `[FORMALIZATION] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`

## Main law

Put

```text
W(n) = sum_(n/2 < k <= n) Lambda(k)/sqrt(k),
c = 2*(1-1/sqrt(2)),
E(n) = max(W(n)-c*sqrt(n), 0).
```

Lean proves the following unconditional implication:

```text
(forall epsilon>0,
  Summable (m |-> E(m^2)/m^(1+epsilon)))
  -> RiemannHypothesis.
```

This replaces the previously formalized all-aperture energy obligation

```text
forall epsilon>0,
  Summable (n |-> E(n)/n^(1+epsilon))
```

by a critically weighted series supported only on perfect-square apertures.

## Exact block relation

For every positive `n`, let

```text
r = floor(sqrt(n)),
N = (r+1)^2.
```

The square-sampling stability theorem gives

```text
W(n) <= W(N) + 3*sqrt(2)*log(N).
```

Since `sqrt(N)-sqrt(n)<=1`, Lean derives the positive-excess relation

```text
E(n) <= E(N) + c + 3*sqrt(2)*log(N).
```

The exact block

```text
r^2 <= n < (r+1)^2
```

contains `2r+1` integers. Therefore, for `sigma>0`, its lifted contribution satisfies

```text
sum_(r^2 <= n < (r+1)^2)
  E((r+1)^2)/n^sigma
<= 3*E((r+1)^2)/r^(2*sigma-1).
```

At `sigma=1+epsilon`, the exponent on the right is `1+2epsilon`. The assumed square energy is
available at every positive exponent, so this term is summable. The logarithmic interpolation
cost is bounded by an arbitrarily small positive power and is summable at `1+epsilon` as well.

## Natural versus successor-square weights

The block calculation naturally produces

```text
E((r+1)^2)/r^(1+epsilon).
```

Lean also proves that the natural square series implies this shifted series. For `r>=1`,
`r+1<=2r`, hence

```text
E((r+1)^2)/r^(1+epsilon)
<= 2^(1+epsilon)*E((r+1)^2)/(r+1)^(1+epsilon).
```

Thus the public capstone has the cleaner unshifted premise
`sum_m E(m^2)/m^(1+epsilon)<infinity`.

## Cesaro strengthening

The series condition has a positive cumulative form. Lean proves directly that RH follows from

```text
forall delta>0,
  sum_(1<=m<=M) E(m^2) = O_delta(M^(1+delta)).
```

This formulation contains no cancellation: it asks only for a nearly linear upper bound on the
total positive overshoot carried by the first `M` square apertures. It is often a better target for
mean-value, sieve, or large-sieve estimates than pointwise control of every `E(m^2)`.

Lean also exposes the direct Hilbert-space predecessor

```text
forall epsilon>0,
  sum_(m>=1) E(m^2)^2/m^(1+epsilon) < infinity.
```

This weighted square-energy condition implies the critical square energy and hence RH. It is the
form most directly comparable with discrete Selberg-integral or mean-square estimates.

## Quantitative zero-by-zero spectrum

The square reduction is now fixed-abscissa, not only an all-epsilon RH capstone.  For every
`alpha>0`, Lean proves

```text
sum_m E(m^2)/m^(1+2*alpha) < infinity
  -> every Xi zero rho satisfies Re(rho) <= 1/2+alpha.
```

The same conclusion follows from the Hilbert-facing premise

```text
sum_m E(m^2)^2/m^(1+4*alpha) < infinity.
```

Equivalently, one specified Xi zero at transverse displacement
`delta=Re(rho)-1/2>0` forces the linear series to diverge whenever `0<tau<2*delta`, and forces the
squared series to diverge whenever `0<tau<4*delta`.  This is a direct zero-by-zero source witness
and does not first pass through the proposition `not RiemannHypothesis`.

At the abscissa level the result is

```text
2*Re(rho)   <= abscissa(m |-> E(m^2)),
4*Re(rho)-1 <= abscissa(m |-> E(m^2)^2)
```

for every right-half Xi zero.  Both constants are intrinsic: square sampling sends a mode
`n^delta` to `m^(2*delta)`, and squaring that value sends it to `m^(4*delta)`.

Taking the supremum over the actual positive-transverse divisor gives the global laws

```text
1 + 2*xiRightTransverseSup <= abscissa(m |-> E(m^2)),
1 + 4*xiRightTransverseSup <= abscissa(m |-> E(m^2)^2).
```

These statements take `Nonempty XiRightZeroCopy` as an explicit divisor input.  Their proofs do
not first infer a witness from `not RiemannHypothesis`.

## Completed-error connection

The existing exact identity identifies `E(n)` with the positive backward `log 2` variation of the
completed critical-Mellin error. Composing it with the square-energy law gives a direct Lean
capstone requiring that variation only at `n=m^2`. This closes the former mismatch between the
completed-error energy theorem, which consumed every aperture, and the square-sampling theorem,
which had only a pointwise interface.

## Lean implementation

The implementation is

```text
GaloisForLFunctions.RHTower.CCM.CCMSharpPrimeWindowSquareEnergySampling
```

with public declarations

```text
dyadicWeightedPrimeWindowPositiveExcess_le_upperSquare_add_log
dyadicWeightedPrimeWindowPositiveExcess_LSeriesSummable_of_squareEnergy
dyadicWeightedPrimeWindowPositiveExcess_LSeriesSummable_of_squareLSeriesEnergy
dyadicWeightedPrimeWindowPositiveExcess_LSeriesSummable_of_squareSquareEnergy
riemannHypothesis_of_squarePrimeWindowPositiveExcessEnergy
riemannHypothesis_of_squarePrimeWindowPositiveExcessSquareEnergy
riemannHypothesis_of_squarePrimeWindowCumulativePositiveExcessGrowth
riemannHypothesis_of_squareCompletedErrorBackwardPositiveVariationEnergy
```

The quantitative divisor consumers are in
`GaloisForLFunctions.RHTower.CCM.CCMSharpPrimeWindowSquareEnergySpectrum`:

```text
xi_zero_re_le_half_add_of_squarePrimeWindowPositiveExcessEnergy
xi_zero_re_le_half_add_of_squarePrimeWindowPositiveExcessSquareEnergy
not_squarePrimeWindowPositiveExcessEnergy_of_xi_zero_transverse
not_squarePrimeWindowPositiveExcessSquareEnergy_of_xi_zero_transverse
two_mul_xi_zero_re_le_squarePrimeWindowPositiveExcess_abscissa
four_mul_xi_zero_re_sub_one_le_squarePrimeWindowPositiveExcessSquare_abscissa
one_add_two_mul_xiRightTransverseSup_le_squarePrimeWindowPositiveExcess_abscissa
one_add_four_mul_xiRightTransverseSup_le_squarePrimeWindowPositiveExcessSquare_abscissa
riemannHypothesis_of_squarePrimeWindowPositiveExcess_abscissa_le_one
riemannHypothesis_of_squarePrimeWindowPositiveExcessSquare_abscissa_le_one
```

The focused module build succeeds. `#print axioms` for both public declarations reports only
Lean/mathlib's foundational `propext`, `Classical.choice`, and `Quot.sound`; there are no project
axioms, `sorry`, `admit`, `opaque`, or hypothesis-bearing structure interfaces in the proof.

## RH leverage

The remaining analytic obligation is now the single value relation

```text
forall epsilon>0,
  sum_(m>=1)
    max(
      sum_(m^2/2 < k <= m^2) Lambda(k)/sqrt(k)
        - 2*(1-1/sqrt(2))*m,
      0)
    /m^(1+epsilon)
  < infinity.
```

This is strictly weaker than the pointwise square-sample subpower bound already known to imply
RH: sparse or moderately large positive overshoots are allowed whenever their critical weighted
mass is finite. It is also more concentrated than the all-aperture energy criterion because no
nonsquare excess values need to be estimated.

## Significance boundary

This theorem does not prove the displayed square-energy premise. It is an axiom-clean reduction
of the remaining RH burden, not an unconditional proof of RH. No claim of scientific novelty is
made until the square-energy premise is either proved from an independent source estimate or
shown by a literature audit to constitute a new theorem of independent interest.

## Gates

- [x] exact square-block partition formalized
- [x] exact block cardinality `2r+1` formalized
- [x] excess interpolation relation formalized
- [x] logarithmic loss absorbed by a summable subpower correction
- [x] successor-square critical energy implies full excess energy
- [x] natural square energy implies successor-square critical energy
- [x] direct square-energy-to-RH capstone formalized
- [x] square-sampled weighted `L2` energy-to-RH capstone formalized
- [x] nearly linear cumulative square-excess growth implies RH
- [x] completed critical-Mellin positive variation reduced to square samples
- [x] fixed-abscissa exponent-doubling transfer formalized
- [x] sharp weighted Cauchy--Schwarz exponent transfer formalized for every source consumer
- [x] zero-by-zero forced divergence at the linear and squared transverse exponents formalized
- [x] global exponent-doubled and exponent-quadrupled divisor-supremum laws formalized
- [x] focused module build
- [x] axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`
- [ ] unconditional proof of the square-sampled positive-excess energy
