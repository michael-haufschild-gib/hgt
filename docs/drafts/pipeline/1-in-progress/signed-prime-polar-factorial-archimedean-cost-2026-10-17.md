# Archimedean cost of the balanced factorial sources

- **ID:** signed-prime-polar-factorial-archimedean-cost
- **Stage:** 1-in-progress
- **Type:** PAPER-PROVED / LEAN IN PROGRESS / UNCOUNTED
- **Scope:** Signed prime–polar transport; actual producer source budgets.
- **Statement:** Determine explicit finite Lévy–sinh energies of the balanced
  factorial sources, including their growth and signed difference.

## Goal

The source-factorization package supplies compact continuous sources P_N,M_N,
equal origin energies between 6sqrt(N) and 46sqrt(N), exact factorial prime-grid
values for their contrast, and its unconditional small prime–polar pairing.
It does not yet supply quantitative archimedean jump energies of those sources.
That missing budget matters for the derivative-free signed transport bounds.

The dependency-closed paper proof below gives explicit bounds of order
sqrt(N) log(N+1) for the actual source energies and a much smaller signed
difference. Lean verification remains pending; no new contribution is counted.

## Approach and existing inputs

Use the explicit ramp and tent formulas to bound translation increments, with
separate near-origin and tail integrals. Do not replace the nonlocal functional
by a spectral moment or insert a pre-floor arithmetic counterterm.
The narrow tent supplies a support-driven lower bound beyond its correlation
width. Reciprocal source scaling and the parallelogram law organize the sum;
the already constructed causal contrast organizes the signed difference.

Inspected corpus inputs:

- `LogarithmicCompressionEnergy.biScaleLevyEnergy_le_linear_log_tail` and its
  explicit logarithmic tail integral. This currently requires `ContDiff ℝ 2`.
- `FiniteSourceEnergyScalarization.biScaleLevyEnergy_source_parallelogram`,
  also requiring `ContDiff ℝ 2`; the factorial ramp and tent do not meet that
  smoothness interface. Establish actual integrability from their increments.
- `UnitEnergySmallSources.source_energy_normalization` is amplitude scaling,
  not a new construction or a substitute for the missing jump-energy estimates.
- `SignedGramTrialCertificate.gramGap_eq_zero_iff` concerns physical-price slack;
  `QuantitativeGramProducer.quantitativeGramCoefficient_source_energy` supplies
  a lower coefficient bound, not the requested actual-source upper estimate.

Search evidence: `/tmp/spp10-next-factorization-search.json` is partial with a
disconnected semantic worker, complete file inventory, and predominantly pending
compiler metadata. Candidate-lemma and source-argument lists were empty; available
prose did not settle this question. Lexical fallbacks
`/tmp/spp10-next-factorization-lexical.json` and
`/tmp/spp10-next-arch-energy-search.json` returned the inputs above. Their output
does not include freshness or completeness metadata. No absence or novelty claim
is inferred from these searches.

## Gates

- [x] Audit prior actual-source increment and finite-energy results more broadly.
- [x] Prove the concrete sources belong to the literal jump-energy domain.
- [x] Obtain quantitative growth and a useful signed-difference theorem on paper.
- [ ] Formalize the actual numeric-index-only endpoint and audit its dependencies.

If bounded-energy behavior fails, retain the strongest positive quantitative
law, exact decomposition, or replacement construction before closing a route.
An abstract receiver or a generic scalar rescaling is not a contribution.

## Paper endpoint

Dependency-closed proof: `docs/reports/BiScaleUncertainty/SignedPrimePolarFactorialArchimedeanCost.md`.
Q=10^6 N^5, L=log(4N+1), B=[6L+7+2log Q]/sqrt(N),
U=2sqrt(N)[6+32(log(6Q)+π)+60(log(24000N)+π)].
For the actual balanced sources, target literal domain admission, energies between
6exp(−1/2)sqrt(N)log N−B and U, exact difference −2∫H_Nw with magnitude ≤2B,
and normalized lower bound (3/23)exp(−1/2)log N−[41+2log(10^6)]/6.
No factor four enters the signed difference. The complete Lean endpoint remains
pending; contribution count remains 10/100.

`/tmp/spp11-source-increment-search.json` reports partial=false/errors=[], full
file inventory, primarily pending/source-only compiler metadata, and deferred
refresh. Available candidate lemmas, source arguments and ingredient sets were
inspected. Direct source reads confirm existing C² hypotheses; generic local
Lipschitz existence does not provide the required explicit source bounds.

## Lean checkpoint

`CompactProfileLipschitz.lean` passed a direct leaf compilation to its olean;
`/tmp/spp11-profile.log` was empty, exit 0. This verifies the exponential,
clamp, tent, product and zero-extension estimates only.

Implementation under verification:
`SignedPrimePolarSourceArchimedeanCertificate.lean`.
These files target the actual admissions, energy bounds, exact signed difference
and normalized lower bound. They are not yet verified or counted.

`SignedPrimePolarTentRegularity.lean` passed direct compilation, exit 0; its log
`/tmp/spp11-tent-regularity.log` contains an informational ring-tactic suggestion,
no errors. `CompactLipschitzLevyEnergy.lean` passed direct compilation, exit 0,
with empty `/tmp/spp11-lipschitz-levy.log`. Both oleans were written. The source
certificate is implemented but remains unverified. API probes
`/tmp/spp11_api.lean` and `/tmp/spp11_finite_api.lean` also terminated with exit 0.

`SignedPrimePolarRampRegularity.lean` passed direct leaf compilation, exit 0,
with empty `/tmp/spp11-ramp-regularity.log` and its olean written. This verifies
the actual ramp's global Lipschitz constant 10000 N^4, pointwise bound 5, and
L¹ bound 20 N.

`SignedPrimePolarSourceJumpDomain.lean` passed direct leaf compilation, exit 0,
with empty `/tmp/spp11-source-jump-domain.log` and its olean written. This verifies
the actual F_N, G_N, P_N and M_N jump-domain admissions, the exact sum law,
absolute integrability of H_N w, and the exact signed difference −2∫H_Nw.
The full numerical upper/lower and normalized endpoint remains unverified. These
domain and identity lemmas do not independently increment the contribution count.

The upper-energy leaf passed compilation with two unused-tactic warnings.
Those tactics were removed; the cleaned source passed its final direct check,
exit 0 with empty `/tmp/spp11-source-jump-upper.log` and olean written.
`SignedPrimePolarTentJumpLower.lean` passed its direct leaf check, exit 0,
empty `/tmp/spp11-tent-jump-lower.log`, and olean written. The actual tent has
energy at least 6 exp(−1/2) N log N.
Contribution count remains 10/100; no package-11 ledger entry has been added.
`SignedPrimePolarCausalJumpBounds.lean` passed direct compilation, exit 0, with
empty `/tmp/spp11-causal-jump-bounds.log` and olean written. The actual signed
energy difference is at most 2B, with B as stated in the paper. Only the final
assembly/normalization leaf and closing audits remain. Count stays 10/100.

Hashes for eight verified leaves are recorded in
`/tmp/spp11-verified-support-manifest.json`.
