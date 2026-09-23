# PTR separable multimode Floquet rigidity

- **Stage:** 5-failed: fixed-profile geometric matrix-modal realization only.
- **Chain:** rotating-PTC Maxwell overlaps → infinite `(n,σ)` boundary operator → source-selected prime conormal → independent defect confinement → RH.
- **Corpus/source basis:** `PhotonicTimeCrystalDynamicChirality` proves `ω+nΔ`; `PhotonicFiniteDressedLaurentNoGo` gives the balanced helical material symbol; `PhotonicFixedKGeometricFloquetNoGo` excludes scalar fixed-`k` geometric solutions. The [source paper](https://arxiv.org/html/2609.08748v1) uses mode-indexed overlaps (Eq. 4) and amplitudes `c_{nσ}` (Eq. 5), so the actual next test is matrix-valued.

## Result and route meaning

Consider the formal all-grade matrix Floquet equation `(ω+nΔ)²(M₀c_n+M₊c_{n−1}+M₋c_{n+1})=Hc_n` on a complex spatial-mode space, with fixed operators `M₀,M₊,M₋,H` and `Δ≠0`. If `c_n=λ^n v`, `λ≠0`, then the three-grade second difference forces `P(λ)v=0`, where `P(λ)=M₀+λ⁻¹M₊+λ M₋`; the equation then forces `Hv=0`. A counterexample with either nonzero residual falsifies it. If `H` is injective, no nonzero separable geometric eigenfamily exists.

`PhotonicMultimodeGeometricFloquetRigidity.lean` proves the sharp classification: for `Δ≠0`, `λ≠0`, an all-grade separable solution exists exactly when `v ∈ ker P(λ) ∩ ker H`. This kills **fixed-spatial-profile geometric** realization under injective `H`, including arbitrary matrix-valued material mixing. The closed `ptr_no_injective_multimode_geometric_solution` has no assumptions/added axioms; targeted module build and axiom audit passed.

Positive survivor: the exact common-nullspace equivalence, formally proved in the same module. If `H` has a physical kernel, the theorem does not exclude states in that intersection. Grade-dependent profiles `v_n` and singular readout of non-geometric fields also survive. The recurrence is a formal modal model, **not yet derived** from the full rotating-cylinder Maxwell boundary problem. The source paper's finite `N_F=4` calculation is not that derivation.

Route-priority audit: `PhotonicHelicalInfiniteLadderCore` already gives distinct absolute OAM labels across grades, so a single fixed spatial profile was already incompatible with the literal helical selection. This result classifies and closes that auxiliary modal ansatz but does **not** remove the leading grade-dependent-profile obstruction. Do not treat it as PTR route closure.
