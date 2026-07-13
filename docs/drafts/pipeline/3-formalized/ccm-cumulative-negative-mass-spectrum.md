# Cumulative negative-mass spectrum of the sharp prime--polar carrier

- **ID:** `ccm-cumulative-negative-mass-spectrum`
- **Stage:** 3-formalized
- **Type:** `[PROVED]` / exact source-growth reformulation
- **Route:** fixed-window Connes--Weil prime--polar tomography

## Main theorem

For a nonnegative real Dirichlet coefficient `a`, put

```text
A(X)=sum_(1<=n<=X) a(n).
```

At every nonnegative threshold `sigma`,

```text
abscissa_abs(a) <= sigma
iff
for every epsilon>0, A(X)=O_epsilon(X^(sigma+epsilon)).
```

For the negative part `S_(L,N)^-` of the literal finite rectangular prime--polar source, every
fixed positive width `L`, admissible tail `N`, and `alpha>=0` therefore satisfy

```text
every Xi zero has Re rho <= 1/2+alpha
iff
for every epsilon>0,
  sum_(n<=X) S_(L,N)^-(n)=O_epsilon(X^(1+alpha+epsilon)).
```

At `alpha=0`, this gives the source-only cumulative criterion

```text
RH
iff
for every epsilon>0,
  sum_(n<=X) S_(L,N)^-(n)=O_epsilon(X^(1+epsilon)).
```

The cumulative source has exact transverse power order.  For every `epsilon>0`,

```text
sum_(n<=X) S_(L,N)^-(n)
  =O_epsilon(X^(1+xiRightTransverseSup+epsilon)),
```

whereas for every `0<eta<xiRightTransverseSup` it is not
`O(X^(1+xiRightTransverseSup-eta))`.  Thus every horizontal zero-free region is the exact
supercritical cumulative-growth threshold of one explicit finite prime--polar sequence.

The same theorem holds for the exact prime--Gamma Weil source.  Under false RH its cumulative
negative mass has exact power order `1+xiRightTransverseSup`; under RH that negative mass
vanishes identically.

## Proof

The forward summatory bound is obtained by inserting a convergent positive Dirichlet weight:

```text
A(X)
<= X^t sum_n a(n)/n^t
= O(X^(sigma+epsilon))
```

with `t=sigma+epsilon/2`.  Conversely, Abel summation sends an
`O(X^(sigma+epsilon/2))` cumulative bound to convergence at every real exponent greater than
`sigma`.  The source specializations compose this equivalence with the exact prime--Gamma and
prime--polar negative-abscissa spectra.

## Formal theorem surface

- `NonnegativeDirichletSummatoryGrowthAt`
- `abscissaOfAbsConv_le_iff_nonnegativeDirichletSummatoryGrowthAt`
- `xiZeroHalfPlaneBound_iff_primeGammaCumulativeNegativeMassGrowth`
- `riemannHypothesis_iff_primeGammaCumulativeNegativeMassCriticalGrowth`
- `primeGammaCumulativeNegativeMass_exactPowerOrder_of_not_rh`
- `all_xiZeros_re_le_iff_rectangularPrimePolarSource_cumulativeNegativeMassGrowth`
- `riemannHypothesis_iff_rectangularPrimePolarSource_cumulativeNegativeMassCriticalGrowth`
- `rectangularPrimePolarSource_cumulativeNegativeMass_exactTransversePowerOrder`

The implementation is in
`formal/GaloisForLFunctions/RHTower/CCMCumulativeNegativeMassSpectrum.lean`.

## Status

- [x] general nonnegative Dirichlet summatory-growth theorem
- [x] exact prime--Gamma specialization
- [x] Gamma-free finite prime--polar specialization
- [x] critical RH endpoint
- [x] exact transverse power-order law
- [x] unconditional formal verification
