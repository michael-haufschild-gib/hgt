# HB: native radial smoothing and cusp-cutoff form admission

Stage: 3-formalized. Seven public theorems are installed and audited. The actual cusp-cutoff primitive belongs to the original joint form domain for every source parameter and time. Untruncated native admission is also [formalized and audited](hb-native-form-admission.md). Complete operator identification, physical-current cancellation and RH remain open.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

## Construction in the original spaces

Fix a cusp cutoff n. The already admitted angular energy family H_n is continuous, compactly supported radially, and zero at the Dirichlet endpoint. Its original angular value embedding JH_n is C¹ with the literal radial derivative.

Set epsilon_m=1/(m+1) and use the already audited endpoint cutoff beta_m, whose support lies below -2 epsilon_m. Convolve beta_m H_n in the original angular energy space with the existing normalized nonnegative smooth bump of width epsilon_m/(k+2). The support-sum inclusion puts every smoothing below -epsilon_m. Thus every smoothing is an actual smooth compact radial energy family accepted by `RadialEnergyFamily.graph_mem`.

The continuous linear map J commutes with the Bochner integral. Classical convolution differentiation after J identifies the actual projected radial derivative with the convolution of `(J(beta_m H_n))'`. This uses the proved C¹ regularity after J; no angular derivative of the radial derivative is assumed.

For each fixed n,m, the compact continuous input and its projected derivative have finite norm bounds. All kernel widths are at most one, so both convolution errors have a common compact support enlarged by one. Their squared norms are bounded by four times the square of the respective input bound on that interval. The normalized-bump pointwise limit and dominated convergence give convergence in the angular-energy L² norm for values and the original angular L² norm for projected radial derivatives.

The original four joint components are value, radial derivative and both sech-weighted angular derivatives. Since sech has norm at most one, angular-energy convergence also controls the weighted components. Continuous component assembly therefore gives convergence in the original joint energy space. Its closed domain first admits the interior cutoff graph. The previously audited complete endpoint limit then admits the cusp-cutoff graph.

## Exact formal results

[ThetaCuspHawkingBMNativeRadialMollification.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMNativeRadialMollification.lean) contains:

- `nativeRadialMollification_graph_mem`: admission of each actual smoothing.
- `nativeRadialMollification_value` and `nativeRadialMollification_value_hasDerivAt`: exact original value and derivative identities.
- `nativeRadialMollification_energy_convergence` and `nativeRadialMollification_radial_convergence`: integrability at every scale and convergence of both squared-error integrals.
- `nativeInteriorJointGraph_mem` and `nativeCuspJointGraph_mem`: membership in the original closed joint form domain after the two successive limits.

All statements quantify over the original source parameters. They add no frequency chamber, domain-admission premise, mixed derivative assumption, numerical result or new axiom.

## Untruncated limit

The [full native admission proof](hb-native-form-admission.md) is now installed and audited. The original Bochner/product isometry and actual frame graph give a uniform bound on the admitted cutoff graphs, using native mass and the already proved cutoff gradient energy. Equality of pure-tensor pairings identifies the original value with eta_n W; dominated convergence gives strong convergence to W. The existing bounded weak-limit theorem, applied to the dense adjoint range of the injective original embedding, produces a domain vector whose original image is W.

The immediate remaining target is its actual operator equation `W=J(J.adjoint(W+G))`. Native admission alone does not establish the complete physical causal inverse identity or physical-current cancellation.

## Search evidence and distant-field comparison

Own corpus queries covered Friedrichs methods, closed graph approximation, Douglas factorization, weak-limit admission and uncurry, with deep mechanism searches. Candidate lemmas, source arguments and method descriptions were inspected separately from generated ingredient groups. Results included partial or deadline-limited searches and source-only compiler metadata. The weak-limit method was taken from its actual source; proposed search groups were not accepted as theorems.

A newest-first arXiv search for intertwining led to [Caputo, Quattropani and Sau, 9 September 2026](https://arxiv.org/html/2609.10450v1). Their Proposition 2.3 gives a generator intertwining on polynomial spaces; Section 6 studies a boundary-generator relation modulo lower degree. The useful comparison is proving an exact operator relation on its actual domain. Their exchange-model result is not a premise of this Lean construction.

## Validation

The complete smoothing and L² convergence fragment passed scratch Lean checks. The graph assembly was checked in scratch; the final real-restriction chain-rule correction passed a focused scratch check against the actual toolchain. The complete 449-line module then passed `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNativeRadialMollification`: two jobs, 187 seconds reported build time, reusing the isolated cache of 4146 local modules and 11 dependency packages. No dependency or umbrella build ran.

A separate scratch audit checked only the seven new public theorems. All use only `propext`, `Classical.choice`, and `Quot.sound`. The source and five emitted artifacts were installed byte for byte, and the leaf was imported in `RHTower.lean`. The frontier map and universal-law ledger were not modified. No numerical experiment ran. Final lint and cleanup are recorded in the full native-admission report.
