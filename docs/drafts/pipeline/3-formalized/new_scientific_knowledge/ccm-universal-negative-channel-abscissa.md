# Universal fixed-window negative-channel Dirichlet abscissa

- **ID:** `ccm-universal-negative-channel-abscissa`
- **Stage:** 3-formalized
- **Type:** THEOREM / exact carrier invariant
- **Scientific status:** `[FORMALIZED] [STRONGER MAIN THEOREM SURFACE] [NOT AN RH PROOF]`
- **Parent:** `ccm-fixed-window-negative-channel-spectrum.md`

## Main theorem

For every positive rectangular window width `L` and every admissible tail `N`, let

```text
q^-_(L,N)(n)=max(-q_(L,N)(n),0)
```

be the actual negative fixed-window Weil mass, and let `sigma_abs(c)` be the extended-real
absolute-convergence abscissa of the Dirichlet series with nonnegative coefficients `c(n)`.
Then

```text
RH      => sigma_abs(q^-_(L,N)) = -infinity,
not RH  => sigma_abs(q^-_(L,N)) = 1 + delta_*,
```

where `delta_*` is the supremal right transverse displacement of the Xi divisor.  In the RH
branch the coefficient sequence itself is zero.  The abscissa is independent of `L` and `N`.

For every nonnegative exact split

```text
q^-_(L,N)=a+b,
```

one has the conservation law

```text
sigma_abs(q^-_(L,N)) = max(sigma_abs(a), sigma_abs(b)).
```

Hence every positive exact principal/residual allocation, for every fixed window and cutoff,
pays the same universal transverse abscissa in at least one channel.

## Stronger source-facing form

For every `alpha >= 0`, the following are equivalent:

1. `delta_* <= alpha`;
2. every Xi zero satisfies `Re rho <= 1/2 + alpha`;
3. `q^-_(L,N)` has finite Dirichlet energy at every abscissa `1 + alpha + epsilon`;
4. there exists any nonnegative majorant `m >= q^-_(L,N)` with that energy;
5. there exist nonnegative channels `a,b` with `q^-_(L,N) <= a+b` and both channel energies
   finite at every such abscissa.

The source construction therefore need not produce an exact split.  Positive domination is
enough.  This strictly weakens the operator-side obligation while retaining the complete
horizontal zero-free spectrum.  At `alpha=0` each energy-majorant or energy-cover statement is
exactly RH-equivalent.

## Proof architecture

The sharp transverse estimate gives

```text
q^-_(L,N)(n) <= C_L n^(delta_*),
```

so the abscissa is at most `1 + delta_*`.  If RH is false and the abscissa were smaller, choose a
real `sigma` strictly between its maximum with `1` and `1 + delta_*`.  Summability at `sigma`
and the one-abscissa negative-energy Landau theorem would force

```text
delta_* <= sigma - 1 < delta_*,
```

a contradiction.  Under RH the negative coefficients vanish.  For an exact nonnegative split,
the total series converges at a real abscissa exactly when both component series converge; taking
their convergence thresholds proves the maximum law.  The majorant and cover formulations follow
from comparison of nonnegative series.

## Formal artifacts

- `formal/GaloisForLFunctions/RHTower/CCMRectangularNegativeDirichletAbscissa.lean`
  - `xiRightTransverseSup_le_iff_negativePartEnergyAbove`
  - `xiRightTransverseSup_le_sub_one_of_negativePart_summable`
  - `xiRectangularNegativePart_summable_above_transverseSup`
  - `not_xiRectangularNegativePart_summable_below_transverseSup`
  - `xiRectangularNegativePart_abscissa_eq_transverseSup_of_not_rh`
  - `xiRectangularNegativePart_abscissa_eq_bot_of_rh`
  - `xiRectangularNegativePart_abscissa_dichotomy`
  - `xiRectangularNegativePart_abscissa_independent_of_window_tail`
  - `negativeChannelSplit_summable_iff`
  - `negativeChannelSplit_abscissa_eq_max`
  - `negativeChannelSplit_max_abscissa_independent`
  - `xiRightTransverseSup_le_iff_exists_negativeEnergyMajorantAbove`
  - `xiRightTransverseSup_le_iff_exists_twoChannelEnergyCoverAbove`

## Verification

- [x] exact module elaboration
- [x] dedicated Lake target build
- [x] aggregate `GaloisForLFunctions.RHTower` build
- [x] main theorem axiom audit: only `propext`, `Classical.choice`, `Quot.sound`
- [x] project formal lint after generated-index refresh

## Literature boundary

Absolute-convergence abscissae and Landau's theorem for nonnegative Dirichlet series are classical.
The claimed theorem surface is the exact identification of the negative logarithmically sampled
fixed-window Xi--Weil abscissa with the shifted transverse Xi-divisor exponent, its universality
over all positive windows and admissible tails, and its conservation under every positive split.
The order-ideal and positive-cover formulations are consequences of this conjunction, not claims
of a new general theorem about arbitrary Dirichlet series.

## RH boundary

The theorem does not construct a prime--Gamma or Sonin majorant with critical energy.  The
remaining RH-bearing theorem is now weaker and source-consumable:

```text
construct the actual completed rectangular source section q_(L,N)
and prove q^-_(L,N) <= m with m >= 0 and
sum m(n) / n^(1+epsilon) < infinity for every epsilon > 0.
```

Equivalently, construct a positive principal/residual cover with both critical shifted energies.
