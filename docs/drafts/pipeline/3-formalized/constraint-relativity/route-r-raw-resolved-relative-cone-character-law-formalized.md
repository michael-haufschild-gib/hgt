# Route-R raw-resolved-relative cone character law — formalized

- **ID:** `route-r-raw-resolved-relative-cone-character-law-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `route-r-raw-resolved-relative-cone-character-law.md` (same directory)
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module | Path |
|---|---|
| `GaloisForLFunctions.HTGeometry.ConstraintRelativity.RelativeConeExactness` | `formal/GaloisForLFunctions/HTGeometry/ConstraintRelativity/RelativeConeExactness.lean` |
| `GaloisForLFunctions.HTGeometry.ConstraintRelativity.RouteRConeCharacter` | `formal/GaloisForLFunctions/HTGeometry/ConstraintRelativity/RouteRConeCharacter.lean` |
| `GaloisForLFunctions.HTGeometry.ConstraintRelativity.RouteRRawCurvature` | `formal/GaloisForLFunctions/HTGeometry/ConstraintRelativity/RouteRRawCurvature.lean` |

All three are wired into `GaloisForLFunctions.HTGeometry`.

## Corpus reuse

The raw prime-depth reporter was **not** rebuilt.  `RouteRRawCurvature` imports
`GaloisForLFunctions.RHTower.PrimeDepthBVWoldCurvedSourceDifferential` and reuses
`primeDepthBVWoldConnection`, `primeDepthBVWoldConnection_swap`,
`primeDepthBVWoldAdditiveCurvature_witness`, `primeDepthBVWoldTransport`,
`primeDepthBVWoldTransport_pos`, `primeDepthBVWoldCovariantD0`, `primeDepthBVWoldCovariantD1` and
`primeDepthBVWoldCovariantD1_comp_D0_apply`.  The mapping-cone layer (`ZCochain`, `ZCochainMap`,
`coneComplex`, `conePr`, `sourceCharacter`, `coneCharacter`, `coneRelativeLawEquiv`) comes from
`RelativeConeExactness`.

## Formal theorem chain

All declarations live in namespace `HTGeometry.ConstraintRelativity`.

Literal objects, §1:

1. `RouteRSource`, `D₀`, `D₁`, `D₁_comp_D₀`, `complex` — cards `(RRC.5)`, `(RRC.6)`.
2. `eta`, `eta_mem_cocycles`, `eta_class_ne_zero` — card `(RRC.7)`; `[η] ≠ 0` is forced by the
   regulator, not assumed.
3. `regulator`, `regulator_comp_D₀`, `regulator_eta`, `regulatorBar`, `regulatorBar_eta` — cards
   `(RRC.8)`, `(RRC.9)`.
4. `exactifyComplex`, `exactifyMap`, `exactifyPrimitive`, `exactify_comm_eta` — cards `(RRC.10)`,
   `(RRC.11)`: the resolved complex and the strict comparison are **constructed** as the universal
   exactification `δ₀(x, λ) = D₀x + λη`, so `Φ¹η = δ₀L` holds with `L = (0,1)`.
5. `ellOnePrimes`, `physicalQuotient` — card `(RRC.12)`.
6. `physChar`, `forwardPhysChar`, `reflectedPhysChar` — card `(RRC.13)`.
7. `eulerProfile`, `eulerClass`, `eulerProfile_mem_of_neg`, `eulerProfile_not_mem_of_nonneg`,
   `eulerClass_ne_zero_iff` — card `(RRC.14)`: `[F_t] ≠ 0 ↔ 0 ≤ t`, by summability below the
   centre and divergence of the prime harmonic series at and above it.
8. `shearRouteRSource`, `shearRouteRSource_eps_ne_zero`, `shearRouteRSource_alpha_ne_id` — the
   source datum is inhabited by a nondegenerate one, so nothing below is vacuous.

Theorem A, §2 — the raw pair is not a complex off centre:

9. `connection_witness_defect` — card `(RRC.4)`: `θ₀₁ + θ₁₂ − θ₀₂ = −log 2 / 8` on the witness
   triangle.
10. `transport_witness_ratio` — card `(RRC.16)`: `U₀₁U₁₂ = 2^{−a/8} · U₀₂`.
11. `rpow_neg_div_eq_one_iff` — `2^{−a/8} = 1 ↔ a = 0`.
12. `rawCurvature_witness_apply` — cards `(RRC.15)`, `(RRC.17)`:
    `(D¹D⁰f)(i₀,i₁,i₂) = U₀₂(2^{−a/8} − 1) f(i₂)`.
13. `rawCurvature_witness_ne_zero`, `raw_pair_not_complex` — **Theorem A**: for `a ≠ 0` the raw
    pair has nonzero composite, so it is not an ordinary cochain complex.

Theorem B, §3 — exactification creates a nonzero relative class:

14. `cone_cocycle_of_primitive`, `exactify_cone_cocycle` — cards `(RRC.19)`, `(RRC.20)`: `κ = (L, η)`
    is a cone cocycle.
15. `exactifyConeClass`, `exactify_conePr_coneClass` — the class and its projection to the shifted
    source cohomology, which is `[η]`.
16. `cone_cls_ne_zero_of_conePr_ne_zero`, `exactifyConeClass_ne_zero` — **card `(RRC.21)`**:
    `[κ] ≠ 0`, because a degree-zero cone boundary has source coordinate a source coboundary and
    `[η] ≠ 0`.
17. `exactify_cohomologyMap_eta` — the same class dies in resolved *absolute* cohomology.  Items
    16 and 17 are the card's contrast: relative cone cohomology retains what absolute cohomology
    kills.

Theorem C, §4 — no nonzero orientation factors through the resolved absolute complex:

18. `orientation_vanishes_of_primitive` — card `(RRC.23)`: a cochain map into a complex
    concentrated in degree one annihilates `Φ¹η`, since that is a coboundary.
19. `no_orientation_factors` — **Theorem C** in general form: no such map can agree with a nonzero
    physical orientation on the retained class.
20. `exactify_no_forward_orientation`, `exactify_no_reflected_orientation` — the two literal
    instantiations, valid exactly on the card's ranges `t ≤ 0` and `0 ≤ t`.

Theorem D, §5 — the two displayed degree-zero sequences have zero connecting maps:

21. `degreeZeroComplex`, `degreeZeroComplex_cohomology_one_eq_zero`,
    `degreeZero_connecting_eq_zero` — **Theorem D**: every linear map from the degree-zero
    cohomology of a degree-zero complex into the degree-one cohomology of another vanishes.
22. `regulator_section`, `isCompl_ker_span` — card `(RRC.24)`: the variable-ideal extension splits
    by `c ↦ c·e`, kernel and section line being complementary.
23. `ellOnePrimes_range_eq_ker` — card `(RRC.25)`: the fixed physical sequence
    `0 → ℓ¹(𝒫) → ℂ^𝒫 → V → 0` is exact.
24. `physChar_ne_zero` — the physical map is a nonzero direct coefficient multiplication, hence not
    a Bockstein of either displayed sequence, all of which vanish by item 21.

Theorem E, §6 — physical values are ordinary relative cone characters:

25. `sourceCharacter`, `coneCharacter`, `coneCharacter_coneInc`, `coneCharacterRel`,
    `coneCharacterRel_eq`, `coneCharacterRel_retained` — cards `(RRC.26)`–`(RRC.30)`: each `χ^ε`
    is an ordinary cochain map reading the shifted source coordinate only, never the chosen
    primitive.
26. `coneCharacter_retained`, `forward_retained_value`, `reflected_retained_value`,
    `exactify_forward_value`, `exactify_reflected_value` — **card `(RRC.31)`, boxed**:
    `χ^fwd_*([κ]) = c_ρ[F_{−t}]`, `χ^ref_*([κ]) = c_ρ[F_t]`.
27. `exactify_forward_ne_zero_iff`, `exactify_reflected_ne_zero_iff`, `exactify_both_ne_zero_iff`,
    `exactify_both_ne_zero_iff_critical` — card `(RRC.36)` and §9: nonzero exactly for `t ≤ 0`,
    for `0 ≤ t`, both exactly at `t = 0`, and at `t_ρ = 2 Re ρ − 1` exactly when `Re ρ = 1/2`.

Countertheorem, §7 — raw curvature also admits an ordinary stabilization:

28. `stabilizedD₀`, `stabilizedD₁` — card `(RRC.33)`: `d̃₀f = (D₀f, f)`, `d̃₁(ω,g) = D₁ω − D₁D₀g`.
29. `stabilized_d_squared` — **card `(RRC.34)`**: `d̃₁d̃₀ = 0`, for *every* composable pair of
    linear maps.
30. `stabilizedD₀_injective`, `stabilizedD₁_inl`, `stabilizedD₁_inr` — the stabilization loses
    nothing: the enlarged degree-zero map is injective and the enlarged degree-one map restricts
    to the raw map and to the exact curvature on the two summands.
31. `stabilizedComplex`, `rawStabilizedComplex` — card `(RRC.32)`: the enlarged ordinary complex,
    and its instantiation at the raw Route-R reporter.
32. `prodComplex`, `prodInr`, `prodSnd`, `prodSnd_prodInr_cohomologyMap`,
    `prodInr_cohomologyMap_ne_zero`, `rawStabilized_prod_retains_coneClass` — the card's
    "direct sum with `Cone(Φ_p)`": an ordinary complex containing the raw reporter, its exact
    curvature, and the nonzero relative cone class.  Excluding it needs an explicit naturality,
    minimality or source-admission axiom, not a homological obstruction.

Positive survivor, §8:

33. `routeR_positive_survivor` — **card `(RRC.35)`, boxed**: the package
    `(Cone(Φ), [κ], χ^fwd, χ^ref)` with its evaluations and the `t = 0` criterion, as one theorem.

## Scope

§9 states that global simultaneous nonerasure on every actual Ξ divisor is equivalent to RH; item
27 formalizes exactly the per-divisor reading (`exactify_both_ne_zero_iff_critical`) and proves
nothing about which `ρ` occur.  §10–§12 are audit and novelty commentary, not theorems.  The card's
open problem — a source-derived law forcing simultaneous nonerasure — is untouched, as the card
itself states.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstraintRelativity/RouteRRawCurvature.lean  # clean
lake build GaloisForLFunctions.HTGeometry                                                  # green
```

`#print axioms` on `raw_pair_not_complex`, `rawCurvature_witness_apply`, `transport_witness_ratio`,
`stabilized_d_squared`, `stabilizedD₀_injective`, `prodInr_cohomologyMap_ne_zero`,
`rawStabilized_prod_retains_coneClass`, `RouteRSource.exactifyConeClass_ne_zero`,
`no_orientation_factors`, `RouteRSource.exactify_no_forward_orientation`,
`RouteRSource.exactify_no_reflected_orientation`, `degreeZero_connecting_eq_zero`,
`isCompl_ker_span`, `ellOnePrimes_range_eq_ker`, `RouteRSource.physChar_ne_zero` and
`RouteRSource.routeR_positive_survivor` returns only `[propext, Classical.choice, Quot.sound]`.
