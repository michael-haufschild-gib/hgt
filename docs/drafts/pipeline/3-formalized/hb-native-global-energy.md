# HB: global native gradient energy

Stage: 3-formalized. Four audited public theorems establish finite global gradient energy and the exact source-response identity for the literal native time primitive in the original radial/modular measure. Native form-domain admission is now [formalized and audited](hb-native-form-admission.md). Complete operator and physical inverse identification, full physical-current extinction and RH remain open.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

The hardest target remains cancellation of the complete physical current with independent SS/SV/VV amplitudes. This construction removes the global energy obstacle in the native form-domain admission needed for the complete inverse identification.

## Actual objects

Let W be `nativeJointTimePrimitiveField`, G be `nativeJointEllipticForcing`, and μ be the original `radialMeasure.prod D4BMModularCore.measure`. The complete G retains the three principal cutoff commutators. For eta_n = `modularCuspCutoff (n+1)`, define

```
E   = |W_x|² + sech(x)² sum_i |D_i W|²,
F_n = |eta_n W_x|² + sech(x)² sum_i |D_i(eta_n W)|²,
e_n = sech(x)² sum_i |(D_i eta_n) W|²,
L   = Re integral conj(G) W dμ.
```

`nativeJointGradientEnergy` uses the actual global native field and its original frame derivatives, rather than an independently chosen representative. The existing chart identities supply a continuous representative almost everywhere in μ, including the original closed modular cell.

## Dependency-closed analytical proof

1. The audited L² admissions of W and G imply integrability of M = |G|²+|W|². The elementary square inequality bounds |G||W| by M. Since |eta_n| <= 1, M also dominates every localized complex forcing pairing.
2. The complete cutoff germ is eventually one at each point of the original cell. Dominated convergence therefore gives integral conj(G) eta_n² W -> integral conj(G) W. Its real part remains the complete source-response pairing.
3. The audited exact cutoff identity is integral F_n = Re integral conj(G) eta_n² W + integral e_n. The independently audited error limit is integral e_n -> 0. Hence integral F_n -> L without assuming any global gradient integrability.
4. Full germ stabilization implies F_n = E eventually at each fixed cell point, because it preserves derivatives as well as cutoff values. Fatou gives integral E <= L and finite integrability of E. The proof passes through the nonnegative extended integral, avoiding use of a totalized Bochner integral as a finiteness argument.
5. The product rule and |a+b|² <= 2|a|²+2|b|² give F_n <= 2E+2e_n. Thus H_n = 2E+2e_n-F_n is nonnegative almost everywhere. Its pointwise limit is E and its integral tends to 2 integral E-L. Applying Fatou again yields integral E <= 2 integral E-L. Combined with step 4, this proves integral E = L.

The second Fatou pass excludes a defect from energy escaping into the cusp. It requires no new uniform cutoff-derivative majorant and no premise about global native gradient energy.

## Public theorems

- `nativeTimePrimitive_forcing_pairing_limit`: integrability of the complete pairing and convergence of actual cusp localizations.
- `nativeTimePrimitive_cutoff_energy_limit`: convergence of the exact total cutoff energy to L.
- `nativeTimePrimitive_gradient_energy_integrable`: actual global gradient integrability and its Fatou upper bound.
- `nativeTimePrimitive_global_energy`: exact global energy identity.

## Remaining domain construction

The [native form-admission construction](hb-native-form-admission.md) is now audited. The actual angular energy family, endpoint limit and normalized-bump smoothing admit every finite cusp-cutoff graph in the original closed joint domain. The original value and gradient norms give a uniform form bound using the cutoff-energy limit above. Strong convergence of the literal value projections, together with the dense adjoint range of the original injective embedding and the corpus's bounded weak-limit theorem, admits the untruncated native primitive. The remaining immediate target is its actual operator equation and subsequent complete physical inverse identification.

## Search and outside-field comparison

Own corpus queries included `Scheffe`, `cutoff gradient`, `Fatou complement convergence integral`, `zero extension`, and mechanism searches for nonnegative-limit integrability and derivative-graph approximation. Candidate lemmas, source methods, proposed ingredient sets and freshness metadata were inspected. Deep results were partial, with some deadline failures and predominantly source-only compiler metadata. The actual Fatou methods in `DiskSmirnovRadialL1` and `HeatEnergyBridge` informed the extended-integral argument; their mathematical hypotheses were not transferred to native data.

Own newest-first arXiv queries were `tightness` and `recovery`. [Ding–Liu–Lo, 9 September 2026](https://arxiv.org/html/2609.10222v1), Sections 3.3–3.4, derives derivative jumps by subtracting adjacent evolution equations while retaining initial compatibility defects. This suggests comparing the full onset equations term by term when the physical-current stage is reached. Its delayed parabolic hypotheses and nonzero mismatch assumptions do not establish native admission or HB current cancellation. No paper statement enters the Lean proof as a premise.

## Validation

All four public theorems are in [ThetaCuspHawkingBMNativeJointEnergy.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMNativeJointEnergy.lean).

- The complete scratch file passed `lake env lean` without warnings.
- Final `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeJointEnergy` passed: two jobs, 12 seconds reported build time. The isolated audit reused 4134 cached local modules and 11 cached dependency packages; no dependency or umbrella build ran.
- `#print axioms` checked only the four new public theorems. Each uses only `propext`, `Classical.choice`, and `Quot.sound`.
- Original-source equality was checked before installation. Audited source and five emitted artifacts were installed byte for byte.
- `scripts/formal_tools.py lint` passed with existing large-file warnings; that audit covered the 935-line global-energy version; the subsequent angular-family extension is documented in the [radial approximation report](hb-native-radial-form-approximation.md).
- The existing `RHTower.lean` import already wires this extended module. No umbrella change or umbrella build was needed.
- No mathematical computations, added axioms, or unfinished proof declarations enter this construction. Frontier map and universal-law ledger were not modified.
- Owned scratch/audit files and all eight search-output files were removed after their process handles reached terminal status. No owned Lean or Lake process remained.
