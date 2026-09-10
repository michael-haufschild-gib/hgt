# HB: native angular energy family and Dirichlet endpoint convergence

Stage: 3-formalized. Five family theorems and six endpoint theorems are proved and audited.

The construction attacks native admission to the original joint form domain, needed for the complete physical inverse identification. The proof chain is literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH. Full native form admission, complete physical-current cancellation and RH remain open.

## Actual family

Fix the original source parameters and time, and a cusp cutoff n. Let H(x) be the angular energy-domain element represented by the actual `nativeTimePrimitiveCutoff`, and let J be the original angular value embedding. Its three components are eta_n W and both actual angular frame derivatives of eta_n W.

Joint continuity of the literal pure jets, compact angular support, and finite radial propagation give common square-integrable bounds on each component. Dominated L² continuity therefore makes H continuous in the angular energy norm. The actual Dirichlet identity and injectivity of J give H(0)=0. Finite propagation gives compact radial support. The admitted literal radial derivative eta_n W_x has a common compact angular majorant; dominated L² differentiation gives `(JH)'=eta_n W_x` and C¹ regularity of JH. No mixed spatial derivative is assumed.

## Endpoint removal

Set epsilon_m=1/(m+1) and beta_m(x)=1-scaledCuspCutoff(epsilon_m,-x). It is smooth, lies in [0,1], is zero for x >= -2 epsilon_m, and is one for x <= -3 epsilon_m. For every fixed negative x, the whole beta_m germ is eventually one, so the actual derivative eventually vanishes there.

The existing weighted profile bound gives a fixed C>=0 with `abs(x beta_m'(x)) <= C` for every m and x. Since JH is C¹ and compactly supported, its derivative has a global bound D>=0. Its zero trace and the vector-valued mean-value inequality give `norm(JH(x)) <= D abs(x)`. Consequently

```
norm(beta_m'(x) JH(x)) <= D C.
```

On the original radial half-line this term vanishes below -3 for every m. Thus its squared norm is dominated by `(D C)^2` times the indicator of [-3,0]. Dominated convergence proves integrability at every m and convergence of its squared integral to zero.

The family difference beta_m H-H is dominated in squared angular energy norm by norm(H)^2 and is eventually zero at each negative radius. It therefore converges in the required angular-energy L² sense. Apply the same argument to the compact continuous derivative `(JH)'`. The exact product-rule decomposition

```
(beta_m JH)'-(JH)' = beta_m' JH + (beta_m-1)(JH)'
```

and `norm(a+b)^2 <= 2 norm(a)^2+2 norm(b)^2` then prove integrability and convergence of the complete radial derivative error in the original angular L² space. The theorem's target derivative is the literal native radial derivative, not a separately chosen representative.

## Remaining construction

For fixed n and m, convolve beta_m H in the angular energy space with a normalized bump of width epsilon_m/(k+2). Compact-support addition keeps the convolution strictly inside the original negative half-line. The original value embedding must commute with the Bochner integral, and classical convolution differentiation after that embedding must give convolution of `(beta_m JH)'`.

The shrinking-bump limit in H's energy space and in the projected derivative's original L² space should give convergence of the four original joint graph components: value, radial derivative, and both sech-weighted angular derivatives. `RadialEnergyFamily.graph_mem` and closedness must admit the fixed endpoint-cutoff graph. The endpoint limit above should then admit the fixed cusp-cutoff graph. The already proved global native energy and cusp-error limit should finally admit the complete native graph. These are three successive closed-domain limits; no common rate across their indices is needed. Convolution, graph-component assembly and native domain admission remain unproved in Lean.

## Search and outside-field comparison

Own corpus searches included mollifier, convolution, Hilbert translation, endpoint cutoff, and mechanism descriptions for compact-support L² continuity, vanishing-trace derivative convergence, and smoothing in the derivative graph. Candidate lemmas, source arguments, proposed ingredient groups and freshness metadata were inspected. Deep searches returned partial results, some runtime deadlines and predominantly source-only compiler metadata. Source arguments from compact convolution and averaging led to actual library convolution derivative and approximation statements; every library name used by the installed proofs was checked against this toolchain in scratch.

A newest-first arXiv search for Mosco led to [Stange, 25 August 2026](https://arxiv.org/html/2608.24647v1). Its bulk-surface evolution analysis discusses recovery sequences and subdifferential graph convergence in Sections 4.1–4.2. The useful comparison is the need to construct approximations retaining the actual boundary relation. Its results are not premises of the native proof.

## Formal statements

The family extension is in [ThetaCuspHawkingBMNativeJointEnergy.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMNativeJointEnergy.lean):

- `nativeTimePrimitiveAngularEnergy_continuous`, `nativeTimePrimitiveAngularEnergy_boundary`, and `nativeTimePrimitiveAngularEnergy_compact` establish the actual family and trace.
- `nativeTimePrimitiveAngularEnergy_value_hasDerivAt` identifies its literal radial derivative in the original angular L² space.
- `nativeTimePrimitiveAngularEnergy_value_contDiff` establishes C¹ regularity after that value embedding.

The endpoint results are in [ThetaCuspHawkingBMNativeRadialEndpoint.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMNativeRadialEndpoint.lean):

- `nativeDirichletCutoff_profile`, `nativeDirichletCutoff_weighted_derivative_bound`, and `nativeDirichletCutoff_eventually_one` establish the actual smooth cutoff, uniform bound and stabilization of its full germ.
- `nativeTimePrimitiveAngularEnergy_endpoint_error_tendsto_zero` controls the complete radial cutoff correction.
- `nativeTimePrimitiveAngularEnergy_endpoint_value_convergence` gives convergence in the angular energy norm.
- `nativeTimePrimitiveAngularEnergy_endpoint_radial_convergence` gives convergence of the actual radial derivative after the original value embedding.

All three native convergence statements also establish integrability at every cutoff scale. They require no frequency chamber, native global-domain premise, mixed derivative hypothesis, added axiom or numerical result.

## Validation

The family extension passed its complete scratch check with `lake env lean`. The endpoint development was checked in scratch, with the last chain-rule correction passing a focused scratch check against the actual cutoff profile. Both complete final sources then passed their exact-module audits:

- `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeJointEnergy`: two jobs, 18 seconds reported build time; 1223 source lines.
- `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeRadialEndpoint`: two jobs, 127 seconds reported build time; 261 source lines.

The isolated audit reused 4135 cached local modules and 11 cached dependency packages. No dependency or umbrella build ran. Separate temporary axiom-check files covered only the five new family theorems and six new endpoint theorems; every result uses only `propext`, `Classical.choice`, and `Quot.sound`. The audited sources and their five emitted artifacts were installed byte for byte, with source guards before installation. The new endpoint leaf is wired into `RHTower.lean`; the family leaf was already imported there.

`scripts/formal_tools.py lint` passed with existing large-file warnings. All owned scratch/audit files and eight search-output files were removed after their processes reached terminal status. No owned Lean or Lake process remained. The frontier map and universal-law ledger were not modified; no new route-independent RH constraint was established by this construction. No numerical experiment was run.
