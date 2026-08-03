# Exact fixed-window positive-channel transverse spectrum

- **ID:** `ccm-fixed-window-negative-channel-spectrum`
- **Stage:** 3-formalized
- **Type:** THEOREM / quantitative carrier-spectrum law
- **Scientific status:** `[FORMALIZED] [NEW EXACT THEOREM SURFACE] [NOT AN RH PROOF]`
- **Parent:** `../ccm-fixed-window-sparse-exception-completeness.md`
- **Strengthened by:** `ccm-universal-negative-channel-abscissa.md`

The exact-split energy/subpower spectrum remains valid, but it is no longer the strongest main
carrier theorem.  The strengthened theorem identifies the exact universal Dirichlet abscissa,
proves maximum-abscissa conservation for every positive split, and replaces exact source splitting
by an arbitrary positive energy majorant or two-channel cover.

## Main theorem

Fix an admissible rectangular Weil tail and write its actual negative mass as an arbitrary
pointwise nonnegative split
\[
 q_{L,N}(n)^-=a(n)+b(n),\qquad a(n),b(n)\ge0.
\]
For every `alpha >= 0`, the following are equivalent:

1. the supremal transverse Xi displacement is at most `alpha`;
2. every Xi zero satisfies `Re rho <= 1/2 + alpha`;
3. the two positive channels satisfy

\[
 \sum_{n\ge1}\frac{a(n)}{n^{1+\alpha+\varepsilon}}<\infty
 \quad(\varepsilon>0)
\]
together with
\[
 b(n)\le C_\delta n^{\alpha+\delta}
 \quad(n\ge1,\ \delta>0).
\]
Consequently, whenever the true transverse exponent is larger than `alpha`, every positive
allocation exposes either divergent shifted Dirichlet energy in the first channel or residual
growth above order `alpha` in the second.  At `alpha = 0` this is exactly the RH carrier theorem.

The exceptional-set theorem is the indicator split
\[
 a=1_Eq^-,\qquad b=1_{E^c}q^-.
\]
A fractional selector `omega : N -> [0,1]` gives the continuous split
`a=omega*q^-`, `b=(1-omega)*q^-`.

## Significance

Semilocal principal/residual and trace/transition decompositions are positive operator splits,
not binary partitions of aperture indices.  The spectrum theorem is therefore the intrinsic
carrier statement; exceptional sets are only one coordinate realization.  Unlike an endpoint
criterion, it quantifies partial progress: a source estimate at exponent `alpha` produces the
corresponding horizontal zero-free region.

## Formal artifacts

- `formal/GaloisForLFunctions/RHTower/CCMRectangularNegativePartEnergyGate.lean`
  - `xiRectangularRightNegativePart_LSeriesSummable_at_one_add_of_tailNegativePart_summable`
- `formal/GaloisForLFunctions/RHTower/CCMRectangularNegativeChannelSplitCompleteness.lean`
  - `riemannHypothesis_iff_negativeChannelEnergy_and_subpowerChannel`
  - `negativeChannelDichotomy_of_not_riemannHypothesis`
  - `riemannHypothesis_iff_fractionalNegativeEnergy_and_complementarySubpower`
- `formal/GaloisForLFunctions/RHTower/CCMRectangularNegativeChannelSpectrum.lean`
  - `xi_zero_re_le_half_add_of_xiRectangularWeilTailNegativePart_summable`
  - `xiRightTransverseSup_le_iff_negativeChannelSpectrum`
  - `all_xiZeros_re_le_iff_negativeChannelSpectrum`
  - `riemannHypothesis_iff_negativeChannelSpectrum_zero`

## Gates

- [x] exact negative-energy RH gate already formalized
- [x] arbitrary nonnegative split theorem
- [x] universal false-RH split dichotomy
- [x] fractional-selector corollary
- [x] one-abscissa observable negative-energy bridge
- [x] full transverse spectrum for every positive split
- [x] zero-free-half-plane equivalence
- [x] exact module builds and axiom audit
- [x] replace the exceptional-set statement as the paper headline theorem

## Literature boundary

Landau continuation and weighted Chebyshev sign criteria are classical parent mechanisms.  The
located literature does not state the exact fixed-window theorem simultaneously for every
nonnegative channel allocation and every transverse exponent.  Novelty is claimed for this exact
carrier-spectrum conjunction, not for Landau's theorem or for generic Mellin positivity.

## RH boundary

The theorem classifies the carrier a successful construction must provide.  It does not prove
that the source-defined Connes/CCM split has the required energy and subpower estimates.
