# Quantitative prime-source--divisor--energy spectrum and summable-family conservation

- **ID:** `ccm-quantitative-source-divisor-energy-spectrum`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / Connes--CCM source--divisor--energy synthesis
- **Scientific status:** `[PROVED] [FORMALIZED] [NOVELTY NEEDS AUDIT] [NOT AN RH PROOF]`
- **Formal module:**
  `GaloisForLFunctions.RHTower.CCMSourceDivisorEnergySpectrum`

## Principal theorem

Fix a rectangular width `L>0`, an admissible tail `N`, and `alpha>=0`.  The following data are
equivalent:

```text
every Xi zero satisfies Re(rho)<=1/2+alpha;

the inverse-tilted dyadic prime continuation is analytic on Re(s)>1+alpha;

the regularized critical-Mellin defect is analytic on Re(u)>alpha-1/2;

the negative fixed-window Weil carrier has Dirichlet energy at every
abscissa 1+alpha+epsilon, epsilon>0.
```

At `alpha=0`, the conjunction is equivalent to RH.  The bundled declarations are

```text
ccmQuantitativeSourceDivisorEnergySpectrum_capstone
riemannHypothesis_iff_ccmSourceDivisorEnergyEndpoint
```

This strengthens the isolated endpoint equivalences into one quantitative spectrum of exact
zero-free half-planes.

## Summable-family positive conservation

Let `a_i(n)>=0` be a family whose sum converges for each `n`, with aggregate

```text
total(n)=sum_i a_i(n),
```

and assume the aggregate covers the actual negative carrier.  Then

```text
sigma_abs(q^-_(L,N)) <= sigma_abs(total).
```

Consequently, under false RH the aggregate has abscissa at least
`1+xiRightTransverseSup`.  An aggregate abscissa at most `1+alpha` forces the full Xi zero-free
half-plane, while an aggregate abscissa at most one proves RH.  The formal declarations are

```text
summableNegativeChannelCover_aggregate_forces_full_abscissa
summableNegativeChannelCover_aggregate_forces_transverseSup_of_not_rh
xiZeroHalfPlaneBound_of_summableNegativeChannelCover_aggregate_abscissa
riemannHypothesis_of_summableNegativeChannelCover_aggregate_abscissa_le_one
```

This is the valid infinite-channel strengthening of finite non-dilution.  A finite exact split
conserves the carrier abscissa in a maximum channel.  An unrestricted pointwise-summable family
conserves it in its aggregate coefficient.

## Optimal source-side correction

The companion module

```text
GaloisForLFunctions.RHTower.CCMSharpPrimeWindowMinimalPositiveCorrection
```

proves that the negative part of the signed dyadic sharp-prime source is the pointwise least
nonnegative correction making that source nonnegative.  It equals twice the explicit
prime-window positive excess.  Every admissible correction dominates it pointwise and in
absolute-convergence abscissa, and the attainable correction-abscissa sublevel sets are exactly
those of the canonical correction.  Hence an admissible correction of abscissa at most
`1+alpha` forces the quantitative Xi half-plane bound; at abscissa one it proves RH.

This converts the correction no-go into a positive carrier theorem: every coefficientwise-
positive source realization must carry the canonical negative channel, and the remaining
arithmetic target is its critical abscissa bound.

## Formal boundary

The module proves equivalences and carrier obligations.  It does not prove the endpoint analytic
or aggregate estimate.  The remaining RH-bearing research theorem is to construct, directly from
the completed prime--Gamma/semilocal source, either

```text
an aggregate positive cover with sigma_abs(total)<=1,
```

or one of the equivalent endpoint holomorphy/negative-energy statements.

## Gates

- [x] quantitative source holomorphy equivalence
- [x] quantitative critical-Mellin holomorphy equivalence
- [x] quantitative negative-energy equivalence
- [x] finite maximum-channel conservation
- [x] arbitrary pointwise-summable aggregate conservation
- [x] aggregate zero-free-region theorem
- [x] aggregate RH endpoint
- [x] least positive sharp-source correction
- [x] exact feasible correction-abscissa law
- [x] correction-abscissa zero-free transfer
- [x] unconditional Lean proof
- [ ] primary-literature novelty audit of the combined theorem surface
- [ ] source construction proving the critical endpoint
- [ ] RH
