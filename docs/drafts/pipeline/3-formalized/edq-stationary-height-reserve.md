# EDQ stationary height reserve and reduced frequency budget

- **ID:** EDQ-SHR
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [current EDQ frontier](../1-in-progress/rh-current-frontier-map.md), [endpoint orientation](edq-stationary-endpoint-orientation.md)
- **Statement:** The actual Fourier atoms have a uniform height Lipschitz bound. Their strictly negative stationary-endpoint values give positive source-defined height reserves; removing modes within these reserves reduces the unknown stationary head and retains explicit negative margins in the full signed source comparison.

## Goal and scope

Proof chain: Euler deletion → actual remainder → full stationary-head comparison → exclusion of off-line zeros → RH. This component sharpens the retained stationary sector using a quantitative comparison of actual source values. It does not establish the remaining whole-head sign or RH. The reserve is defined by an independently proved positive integral, without a zeta-zero premise; no uniform numerical lower bound is asserted.

## Dependency-closed paper proof

Write `J_beta(t,v)=integral_1^infinity x^(-beta) sin(v(x-1)+t log x) dx`, beta>1. Positive dilation in the already defined atom gives exactly

`Im A(s,N,k)=w_k J_(sigma+2)(t,2*pi*k*N)`.

The sine Lipschitz inequality and the corpus's exact logarithmic power integral imply

`|J_beta(t,v)-J_beta(u,v)| <= |t-u|/(beta-1)^2`.

At the stationary endpoint `v>0`, let `E_beta(v)=J_beta(-v,v)`. The endpoint positive-budget identity proves `E_beta(v)>0` for beta>2, and phase reversal gives `J_beta(v,-v)=-E_beta(v)`. Define

`r_beta(v)=(beta-1)^2 E_beta(v)/2 > 0`.

For `v<=t<=v+r_beta(v)`, the Lipschitz estimate yields `J_beta(t,-v)<=-E_beta(v)/2<0`. For `t<=v`, the prior nonstationary/endpoint sign already applies. Thus every actual negative-frequency atom is negative throughout `t<=v+r_beta(v)`, extending across the stationary boundary.

Retain only stationary negative modes satisfying `v+r_beta(v)<t`. Every discarded mode has proved negative imaginary part. The sum over the original stationary set equals the reduced sum plus those negative terms. Combining this with the existing full signed Fourier comparison preserves both infinite sectors and the mean. If `B_N` is the reduced budget and `M_N` sums half the positive endpoint masses of removed modes, the exact original budget satisfies `S_N<=B_N-M_N`. This is an upper envelope of the original sum; it improves the estimate obtained by merely dropping the known negative terms, and does not claim a numerical improvement over retaining their exact values. Any positive first-harmonic witness required by a closed-right strip zero must lie beyond its positive reserve.

The power-mass bound also proves `|J_beta(t,v)|<=1/(beta-1)`, hence `r_beta(v)<=(beta-1)/2`. Throughout `0<sigma<=1`, the reserve satisfies `0<r_(sigma+2)(v)<=1`. Since `2*pi*N>1`, the first reserve ends before the second frequency threshold. Every stationary mode is therefore controlled whenever

`t<=2*pi*N+r_(sigma+2)(2*pi*N)`.

The existing positive-frequency ceiling and negative mean imply strict negativity of the complete normalized remainder throughout this extended cutoff, for `t>=1`. At `N=1`, this excludes zeta zeros with `1/2<=sigma<1` in the extended chamber. No zero premise is used to construct the reserve or prove any atom/remainder sign.

## Formal scope

`formal/GaloisForLFunctions/RHTower/ArithmeticStationaryHeightReserve.lean`, namespace `RHTower.DeletionMixedRefinement`: 386 lines, 30 declarations (25 theorems, five definitions). Imports the existing stationary-endpoint module and `PrimeLogZetaAbelPole`; no prior module was rebuilt or re-audited.

- `anchoredSineProfile_height_lipschitz`: exact height bound using the logarithmic power moment.
- `scaledBernoulliFourierAtom_im_eq_profile`: the normalization removes all residual anchor amplitude.
- `stationaryHeightReserve_pos`, `stationaryHeightReserve_eq_positive_budget`, `stationaryHeightReserve_le`: a strictly positive source-defined reserve with its exact positive-density representation and finite upper bound.
- `scaledBernoulliFourierAtom_neg_im_le_reserve_margin`, `scaledBernoulliFourierAtom_neg_im_neg_of_height_reserve`: half-endpoint negative margin and full negative collar.
- `normalizedWeightedRemainder_scaled_im_le_beyondReserve`: full source bound with reduced head, retained margins, opposing sectors, and mean.
- `normalizedWeightedRemainder_im_neg_of_first_height_reserve`: strict complete-remainder sign beyond the original first threshold.
- `riemannZeta_ne_zero_of_first_height_reserve`: actual zero exclusion in the extended unit chamber, for `1/2<=sigma<1`, `t>=1`.
- `exists_positive_first_harmonic_beyond_height_reserve_at_closed_right_zero`: every qualifying closed-right zero forces a positive first harmonic beyond the reserve.

The reduced head remains to compare against the exact opposing contributions at arbitrary height. Every reserve is positive, but no positive lower bound uniform over varying height, exponent, and frequency is asserted. The positive-witness conclusion includes critical zeros. This is not an unconditional proof or falsification of RH, and does not settle the full R statement outside its proved strip/height domain. No novelty claim is made.

## Verification gates

- [x] Corpus search and source inspection before new Lean code.
- [x] Complete symbolic paper proof; no numerical certificate or unproved sign premise.
- [x] Foreground scratch check, without warnings.
- [x] Finished leaf wired in `RHTower.lean`; exactly one leaf compiled in 4.9 seconds. No umbrella build.
- [x] All 30 new declarations audited; only `propext`, `Classical.choice`, and `Quot.sound`. No old declaration audited.
- [x] Documentation and current frontier updated; corpus index refreshed once.
- [ ] Global formal lint: three unrelated concurrently added modules are unwired, listed below.
- [ ] Full stationary-head comparison and unconditional RH proof/falsification.

## Verification records and cleanup

`LEAN_NUM_THREADS=1 lake env lean /tmp/edq_height_reserve.lean` passed without warnings. The final command `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.ArithmeticStationaryHeightReserve` compiled exactly one leaf in 4.9 seconds; dependency output was cached replay. A separate new-only `/tmp` axiom audit passed for all 30 declarations.

Global `python3 scripts/formal_tools.py lint` reports only these wiring errors:

- `GaloisForLFunctions.RHTower.ThetaCuspCenterCompensationFlux`
- `GaloisForLFunctions.RHTower.ThetaCuspCenterMixedAllOrderIntegration`
- `GaloisForLFunctions.HTGeometry.AlternatingPairJetIntegral`

These concurrently added modules are outside this work and were not modified, built, or re-audited. The new leaf has no lint error. The index refresh reports 32739 files, 399729 declarations, 3909 gap markers. All owned Lean/Lake handles completed; process inspection found none remaining. Four owned scratch sources/manifests were removed. Logs remain at `/tmp/edq_height_reserve_{build,axioms,lint,index}.log`. No numerical experiment, computational certificate, or added axiom enters the proof.
