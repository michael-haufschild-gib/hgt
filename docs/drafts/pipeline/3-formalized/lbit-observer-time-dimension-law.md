# L-bit observer-time dimension law

- **ID:** `lbit-observer-time-dimension-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Date:** 2026-07-30
- **Formal source:**
  `formal/GaloisForLFunctions/HTGeometry/LBitObserverTimeDimensionLaw.lean`

## Exact law

Let \(w(S)\in\mathbb N\) assign every finite l-bit interaction support a
spectral-jet birth order. For the scaled diagonal spectrum whose
order-\(m\) jet contains exactly the Walsh coefficients with \(w(S)=m\),
the projective temporal dimension resolved through order \(r\) is

\[
  \boxed{
  \tau_r=
  \sum_{m<r}
  \dim_{\mathbb Q}\operatorname{span}_{\mathbb Q}
  \{J_S:S\ne\varnothing,\ w(S)=m\}.}
\]

This formula is unconditional. In particular, it requires no rational
independence between coefficients in different birth layers. If each
individual layer is rationally independent, then

\[
  \tau_r=\#\{S\ne\varnothing:w(S)<r\}.
\]

For birth order equal to support diameter on \(n\) ordered sites, every
coefficient family obeys the unconditional ceiling

\[
  \tau_r\le n\,2^{r+1}.
\]

## Formal declarations

- `scaledLBitEnergyPolynomial_coeff`;
- `projectiveJetMap_scaledLBitSpectralJet_walsh`;
- `temporalDirectionSpace_scaledLBitSpectralJet_eq_pi`;
- `temporalDimension_scaledLBitSpectralJet_eq_sum_layerRank`;
- `lbitBirthLayerRank_le_card`;
- `temporalDimension_scaledLBitSpectralJet_le_card_bornBefore`;
- `temporalDimension_scaledLBitSpectralJet_eq_card_bornBefore`;
- `lbitSupportsBornBefore_diameter_subset_geometric`;
- `card_lbitSupportsBornBefore_diameter_le_linear`;
- `temporalDimension_diameterScaledLBitSpectralJet_le_linear_unconditional`;
- `temporalDimension_diameterScaledLBitSpectralJet_le_linear`.

## Scope

The resolution variable is spectral-jet order in an exactly scaled finite
diagonal l-bit family. It is not physical elapsed time, detector
resolution, decoherence time, or a claim about a generic microscopic
Anderson/MBL Hamiltonian. A separate finite-parameter phase-law theorem is
required to connect coefficient birth orders to laboratory observation
horizons.

## Verification

Direct target compilation passed:

```text
lake env lean GaloisForLFunctions/HTGeometry/LBitObserverTimeDimensionLaw.lean \
  -o .lake/build/lib/lean/GaloisForLFunctions/HTGeometry/LBitObserverTimeDimensionLaw.olean
```

Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
Final `lake build` audit is reserved for publication audit.
