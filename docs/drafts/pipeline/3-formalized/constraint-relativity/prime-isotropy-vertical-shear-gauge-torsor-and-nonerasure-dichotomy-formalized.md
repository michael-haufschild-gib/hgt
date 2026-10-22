# Prime-isotropy vertical-shear gauge torsor and nonerasure dichotomy — formalized

- **ID:** `prime-isotropy-vertical-shear-gauge-torsor-and-nonerasure-dichotomy-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `prime-isotropy-vertical-shear-gauge-torsor-and-nonerasure-dichotomy.md`
  (same directory)
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module | Path |
|---|---|
| `GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicPrimeIsotropyVerticalGauge` | `formal/GaloisForLFunctions/RHTower/CCM/CCMRationalAdelicPrimeIsotropyVerticalGauge.lean` |

Wired into `GaloisForLFunctions.RHTower`.  All declarations live in the root namespace `RHTower`.

## Corpus reuse

Nothing below was rebuilt.

- `RHTower/CCM/CCMRationalAdelicPrimeIsotropyObserverFreedom.lean` (the sibling card
  `rational-adelic-h1-observer-coefficient-freedom-and-discriminant-law-formalized.md`) supplies
  `ccmRationalAdelicPrimeOrbitDifference` (`T`), `ccmRationalAdelicPrimeOrbitDifference_mem_ker`,
  `CCMRationalAdelicPrimeResidualQuotient` (`Q_p`), `ccmRationalAdelicPrimeResidualRelations`,
  `ccmRationalAdelicBruhatIntegral_orbitDifference` (card `(VSG.4)`, `hT = 0`),
  `ccmRationalIntegralFiniteAdelesBruhat`, `ccmRationalAdelicHaarWitness` and its two endpoint
  values, `ccmRationalAdelicHaarWitnessCocycle`, and
  `ccmRationalAdelicPrimeStokesObserver` with `..._class`.
- `RHTower/CCM/CCMRationalAdelicPrimeIsotropyRelativeXiChainMap.lean` — the source complex
  `ccmRationalAdelicPrimeRelativeD0/D1`, `ccmRationalAdelicPrimeRelativeComplex`,
  `ccmRationalAdelicPrimeRelativeClass`, and the strict comparison
  `ccmRationalAdelicPrimeRelativeXiComparison1`,
  `primeDepthBVWoldXiPrimeLocalizedLeadingConormal`,
  `primeDepthBVWoldXiResolvedCovariantD0`.
- `RHTower/CCM/CCMRationalAdelicPrimeIsotropyStokesRegulator.lean` —
  `ccmRationalAdelicPrimeOrbitStokesLM`, `ccmRationalAdelicPrimeOrbitStokes_scaling_sub` (card
  `(VSG.7)`: the primitive set is nonempty),
  `ccmRationalAdelicPrimeRelativeH1StokesRegulator`.
- `RHTower/CCM/CCMRationalAdelicEpsilonZero.lean`, `CCMRationalAdelicEpsilonOne.lean` — `ε₀`, `ε₁`
  and their scaling invariance.
- `RHTower/CCM/CCMRationalAdelicScalingAction.lean` — `ccmRationalAdelicBruhatScaling` and
  `ccmRationalAdelicBruhatScaling_sigma` (scaling commutes with the Real structure).
- `RHTower/CCM/CCMRationalAdelicBruhatSimpleTensorReal.lean`, `CCMRationalAdelicEndpointReal.lean` —
  the Real structure `ccmRationalAdelicBruhatSimpleTensorKRealEven.sigma`, its involutivity
  `ccmRationalAdelicBruhatSimpleTensor_sigma_sq`, and the endpoint laws
  `ccmRationalAdelicBruhatZeroEval_real`, `ccmRationalAdelicBruhatIntegral_real`.
- `RHTower/Deninger/DeningerThreeTermOperations.lean` — `DeningerThreeTermHom`, `H1map`, `H1map_mk`.
- `HTGeometry/GaussianSchwartz.lean` — `gaussianSchwartz`.
- From mathlib: `Submodule.dualAnnihilator`, `Submodule.dualQuotEquivDualAnnihilator`,
  `LinearMap.exists_extend`, `LinearMap.quotKerEquivOfSurjective`, `Submodule.quotEquivOfEq`.

## Formal theorem chain

### Theorem A — the full vertical gauge group, cards `(VSG.5)`, `(VSG.6)`

1. `ccmRationalAdelicPrimeShearAnnihilator`,
   `mem_ccmRationalAdelicPrimeShearAnnihilator_iff` — `Ann(im T)`.
2. `ccmRationalAdelicPrimeVerticalShear`,
   `ccmRationalAdelicPrimeVerticalShear_zero`, `ccmRationalAdelicPrimeVerticalShear_comp`,
   `ccmRationalAdelicPrimeVerticalShear_fst`,
   `ccmRationalAdelicPrimeVerticalShear_cocycle`,
   `ccmRationalAdelicPrimeVerticalShear_comp_D1`,
   `ccmRationalAdelicPrimeVerticalShear_comp_D0` — **`(VSG.6)`**: `G_ℓ(y,z) = (y, z + ℓy)` is a
   cochain automorphism fixing the coordinates and the retained cocycle, and `G_ℓG_m = G_{ℓ+m}`.
3. `ccmRationalAdelicPrimeVerticalGauge_classification` — **`(VSG.5)` boxed**: conversely, every
   linear map fixing the isotropy coordinate, fixing `η`, and commuting with `D₀` is `G_ℓ` for a
   unique `ℓ ∈ Ann(im T)`.
4. `ccmRationalAdelicPrimeShearAnnihilatorEquivDualCoinvariants` — **`(VSG.5)` boxed**:
   `Ann(im T) ≅ (A / im T)^*`.

### Theorem B — Stokes primitives are a gauge torsor, cards `(VSG.7)`–`(VSG.11a)`

5. `ccmRationalAdelicPrimeStokesPrimitives`,
   `ccmRationalAdelicPrimeOrbitStokesLM_mem_primitives` — **`(VSG.7)`**: nonempty, by the
   bilateral orbit regulator.
6. `mem_ccmRationalAdelicPrimeStokesPrimitives_iff` — **`(VSG.8)` boxed**:
   `𝒫_p = R_p + Ann(im T)`.
7. `ccmRationalAdelicPrimeStokesReader`, `ccmRationalAdelicPrimeStokesReader_cocycle`,
   `ccmRationalAdelicPrimeStokesReader_comp_shear` — **`(VSG.9)`, `(VSG.10)` boxed**:
   `I_R(η) = 1` and `I_R ∘ G_ℓ = I_{R−ℓ}`.
8. `ccmRationalAdelicPrimeStokes_simplyTransitive` — the shear action on primitives is simply
   transitive.
9. `ccmRationalAdelicBruhatZeroEval_mem_shearAnnihilator`,
   `ccmRationalAdelicBruhatIntegral_mem_shearAnnihilator`,
   `ccmRationalAdelicUnitWitness`, `ccmRationalAdelicUnitWitness_zeroEval`,
   `ccmRationalAdelicPrimeResidualRestrictLM`,
   `ccmRationalAdelicPrimeResidualRestrictLM_surjective`,
   `ker_ccmRationalAdelicPrimeResidualRestrictLM`,
   `ccmRationalAdelicPrimeAmbiguityEquiv` — **`(VSG.11)` boxed**:
   `𝒜_p = Ann(im T) / ℂε₀ ≅ Q_p^*`.  Surjectivity is the algebraic extension of functionals
   (`LinearMap.exists_extend`), and the kernel is `ℂε₀` because `ε₀` is normalised by the Gaussian
   tensored with `1_Ẑ`.
10. `ccmRationalAdelicPrimeResidualHaar`, `ccmRationalAdelicPrimeResidualHaar_ne_zero` —
    **`(VSG.11a)`**: the descended Haar covector is nonzero, so the Haar shear line is a
    nontrivial subtorsor.

### Theorem C — known symmetries do not remove the Haar shear, cards `(VSG.11b)`–`(VSG.15)`

11. `ccmRationalAdelicPrimeScalingCochain`,
    `ccmRationalAdelicPrimeScalingCochain_comm_D0`,
    `ccmRationalAdelicPrimeScalingCochain_comm_D1` — **`(VSG.11b)`**.
12. `ccmRationalAdelicPrimeScalingCochain_comm_haarShear` — **`(VSG.11c)` boxed**: item 1.
13. `ccmRationalAdelicPrimeRelativeReal`,
    `ccmRationalAdelicPrimeRelativeReal_involutive`,
    `ccmRationalAdelicPrimeRelativeReal_D0`,
    `ccmRationalAdelicPrimeRelativeReal_haarShear`,
    `ccmRationalAdelicPrimeRelativeReal_commutes_haarShear_iff` — **`(VSG.11d)`, `(VSG.11e)`**:
    item 2, the commuting Haar-shear subgroup is exactly `λ` real.
14. `ccmRationalAdelicPrimeXiComparison_shear_homotopy`,
    `ccmRationalAdelicPrimeXiComparison_shear_homotopy_D0` — **`(VSG.13)`–`(VSG.15)`**: item 3,
    the shear changes the strict resolved comparison by the resolved boundary of `ℓ(y)L_p`, and
    that homotopy annihilates every relative boundary.

### Theorem D and the dichotomy, cards `(VSG.16)` and §6

15. `ccmRationalAdelicPrimeVerticalShearHom`, `ccmRationalAdelicPrimeHaarShear_mem`,
    `ccmRationalAdelicPrimeHaarShear_H1map_witness` — the shear as an endomorphism of the complex,
    and its effect on the Haar-witness class: a multiple of the retained class.
16. `ccmRationalAdelicPrimeGaugeInvariantReader_erases` — **`(VSG.16)` boxed**: a reader invariant
    under the whole Haar shear line annihilates the retained class.  The card argues through the
    Stokes splitting; the Lean proof evaluates directly on the Haar-witness class, which is
    shorter and needs no splitting.
17. `ccmRationalAdelicPrimeStokesObserver_smul` — **§6**: the physical observer family is
    homogeneous in its target vector, so homogeneous linear naturality never selects one nonzero
    coefficient.
18. `ccmRationalAdelicPrimeGaugeInvariantObserver_target_eq_zero`,
    `ccmRationalAdelicPrimeMarkedObserver_target_free` — the **constitutive-rigidity dichotomy**:
    treating vertical shear as gauge forces `v = 0`; marking a Stokes splitting leaves every
    `v ∈ V` available.

## Scope

Sections 7 (Fourier/Poisson boundary), 8 (`[OPEN CORE]`, the fixed-space claim `𝒜_p^𝖲 = 0`) and 9
(novelty boundary) are explicitly *not* proved by the card, and are not formalized.  The card says
plainly that no full adelic Fourier cochain automorphism is constructed and that claiming Fourier
kills the ambiguity would be theatre; the Lean file makes no such claim.  The three open gates
remain open.

## Verification

```text
lake env lean GaloisForLFunctions/RHTower/CCM/CCMRationalAdelicPrimeIsotropyVerticalGauge.lean  # clean
lake build GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicPrimeIsotropyVerticalGauge          # green
```

`#print axioms` on `ccmRationalAdelicPrimeVerticalGauge_classification`,
`ccmRationalAdelicPrimeShearAnnihilatorEquivDualCoinvariants`,
`ccmRationalAdelicPrimeVerticalShear_comp_D0`, `ccmRationalAdelicPrimeVerticalShear_comp`,
`mem_ccmRationalAdelicPrimeStokesPrimitives_iff`, `ccmRationalAdelicPrimeStokesReader_comp_shear`,
`ccmRationalAdelicPrimeStokes_simplyTransitive`, `ccmRationalAdelicPrimeAmbiguityEquiv`,
`ccmRationalAdelicPrimeResidualHaar_ne_zero`, `ccmRationalAdelicPrimeScalingCochain_comm_D0`,
`ccmRationalAdelicPrimeScalingCochain_comm_haarShear`, `ccmRationalAdelicPrimeRelativeReal_D0`,
`ccmRationalAdelicPrimeRelativeReal_haarShear`,
`ccmRationalAdelicPrimeRelativeReal_commutes_haarShear_iff`,
`ccmRationalAdelicPrimeXiComparison_shear_homotopy`,
`ccmRationalAdelicPrimeXiComparison_shear_homotopy_D0`,
`ccmRationalAdelicPrimeGaugeInvariantReader_erases`, `ccmRationalAdelicPrimeStokesObserver_smul`,
`ccmRationalAdelicPrimeGaugeInvariantObserver_target_eq_zero` and
`ccmRationalAdelicPrimeMarkedObserver_target_free` returns only
`[propext, Classical.choice, Quot.sound]`.
