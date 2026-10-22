# Two-endpoint prime-orbit Stokes moduli and infinite coinvariant law — formalized

- **ID:** `two-endpoint-prime-orbit-stokes-moduli-and-infinite-coinvariant-law-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `two-endpoint-prime-orbit-stokes-moduli-and-infinite-coinvariant-law.md`
  (same directory)
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module | Path |
|---|---|
| `GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicTwoEndpointStokesModuli` | `formal/GaloisForLFunctions/RHTower/CCM/CCMRationalAdelicTwoEndpointStokesModuli.lean` |

Wired into `GaloisForLFunctions.RHTower`.  All declarations live in the root namespace `RHTower`.
One public accessor, `ccmRationalArchimedeanPrimeOrbitStokes_eq`, was added to
`RHTower/CCM/CCMRationalAdelicPrimeIsotropyStokesRegulator.lean`; it is a `rfl` lemma exposing the two
tails of the corpus's bilateral orbit functional.

## Corpus reuse

Nothing below was rebuilt.

- `RHTower/CCM/CCMRationalAdelicPrimeIsotropyStokesRegulator.lean` — the bilateral orbit functional
  `ccmRationalArchimedeanPrimeOrbitStokes` together with **Lemma C**: the summability of both tails
  (`primeOrbitPositiveTerm_summable` via the Schwartz lattice bound, and
  `primeOrbitNegativeTerm_summable` via the mean-value estimate and a geometric majorant) is
  already discharged there, so the sampling functionals of this card are honest linear forms with
  no new analysis.  Also `ccmRationalAdelicPrimeOrbitStokesLM` and the exact Stokes law
  `ccmRationalAdelicPrimeOrbitStokes_scaling_sub`.
- `RHTower/CCM/CCMRationalAdelicPrimeIsotropyObserverFreedom.lean` —
  `ccmRationalAdelicPrimeOrbitDifference`, `ccmRationalAdelicPrimeOrbitDifference_mem_ker`,
  `ccmRationalAdelicBruhatIntegral_orbitDifference` (card `(TPS.2)` for `ε₁`),
  `ccmRationalIntegralFiniteAdelesBruhat` and its value/integral lemmas.
- `RHTower/CCM/CCMRationalAdelicScalingAction.lean` — `ccmRationalAdelicBruhatScaling`,
  `ccmRationalArchimedeanScaling_apply`, `ccmRationalFiniteBruhatScaling_apply`,
  `ccmRationalAdelicBruhatScaling_tmul`, `ccmRationalFiniteBruhatScalingLinear`.
- `RHTower/CCM/CCMRationalFiniteAdeleHaarCharacter.lean` — `ccmRationalFiniteBruhatIntegral_scaling`,
  the finite Haar Jacobian.
- `RHTower/CCM/CCMRationalAdelicEpsilonZero.lean`, `CCMRationalAdelicEpsilonOne.lean` — `ε₀`, `ε₁`
  and their tensor evaluation.
- `RHTower/CCM/CCMRationalAdelicPrimeIsotropyRelativeXiChainMap.lean` —
  `ccmRationalAdelicFiniteZeroPartialEval` and `..._tmul` (card `(TPS.12)`).
- From mathlib: `ContDiffBump`, `HasCompactSupport.toSchwartzMap`, `LinearMap.exists_extend`,
  `LinearIndependent.finite_of_isNoetherian`, `Finset.sum_ite_eq'`.

## Formal theorem chain

### The abstract two-endpoint source, cards `(TPS.1)`–`(TPS.6)`

1. `twoEndpointOrbitDifference`, `twoEndpointKernel`,
   `twoEndpointOrbitDifferenceToKernel`, `twoEndpointD0`, `TwoEndpointH1`,
   `twoEndpointRetainedClass`, `TwoEndpointCoinvariants`.

### Theorem A — exact normalized-observer classification, cards `(TPS.7)`–`(TPS.10)`

2. `twoEndpointSplitRaw`, `twoEndpointSplitRaw_boundaries`, `twoEndpointSplit`,
   `twoEndpointUnsplitCoinvariants`, `twoEndpointUnsplitLine`, `twoEndpointUnsplit`,
   `twoEndpointH1Equiv` — **`(TPS.7)`, `(TPS.10)`**: `H¹₀₁ ≅ (K / im T) ⊕ k`.
3. `twoEndpointH1Equiv_retainedClass` — the splitting sends `η` to `(0,1)`.
4. `twoEndpointStokesCovector`, `twoEndpointStokesCovector_retainedClass` — **`(TPS.9)`**.
5. `twoEndpointStokesCovector_add_normalized`, `twoEndpointNormalizedCovector_sub` —
   **`(TPS.8)` boxed**: normalized covectors are exactly `I_R + Hom(K/im T, k)`.
6. `twoEndpointNormalizedCovector_from_primitive` — **`(TPS.8)`, last clause**: every such
   covector comes from a Stokes primitive, by extending the coinvariant functional from `K` to `A`
   (`LinearMap.exists_extend`) and subtracting.

### Theorem B — the Haar ambiguity collapses, card `(TPS.11)`

7. `twoEndpointStokes_shift_eps1_isPrimitive`, `twoEndpointStokesCovector_shift_eps1` —
   **`(TPS.11)` boxed**: `R` and `R + λε₁` are both primitives and induce the *same* covector,
   because the isotropy coordinate is constrained to `ker ε₁`.

### Literal rational-adelic instantiation, cards `(TPS.12)`, `(TPS.13)`

8. `ccmRationalAdelicPrimeAlpha`, `ccmRationalAdelicTwoEndpoint_eps0`,
   `ccmRationalAdelicTwoEndpoint_eps1`, `ccmRationalAdelicTwoEndpoint_primitive` — the three data
   conditions, each discharged by a corpus theorem, so Theorems A and B apply with no hypotheses
   left over.
9. `CCMRationalAdelicTwoEndpointKernel`, `CCMRationalAdelicTwoEndpointCoinvariants`,
   `ccmRationalAdelicTwoEndpointH1Equiv`, `ccmRationalAdelicTwoEndpointStokes_haar_collapse`.

### Bilateral orbit sampling, cards `(TPS.14)`–`(TPS.16)`

10. `ccmRationalScalingOfBase`, `ccmRationalAdelicOrbitSample` — **`(TPS.14)`**: sampling at a
    rational base `a` is the corpus's bilateral orbit functional precomposed with the rational
    scaling whose inverse label is `a`.  This is the one place where the Lean proof takes a
    different route from the card: the card samples at an arbitrary real base and re-proves
    absolute convergence and telescoping, whereas rational bases suffice for the separation
    argument and reduce **Lemma C** and **Lemma D** to corpus theorems.
11. `ccmRationalAdelicOrbitSample_orbitDifference` — **Lemma D, `(TPS.15)`**: every base reads an
    orbit difference as `ε₀`, because scalings commute and `ε₀` is scaling invariant.
12. `ccmRationalAdelicOrbitPhase`, `ccmRationalAdelicOrbitPhase_orbitDifference`,
    `ccmRationalAdelicOrbitPhaseCovector` — **`(TPS.16)`**: the orbit-phase difference descends to
    the two-endpoint coinvariants.

### Theorem E — infinite residual moduli, cards `(TPS.17)`–`(TPS.21)`

13. `ccmRationalArchimedeanPrimeOrbitStokes_of_support` — a witness supported inside `(1,2)` is
    read at exactly the one point of its orbit lying there: the positive tail collapses to `n = 0`
    and the negative tail is identically zero.
14. `ccmRationalAdelicOrbitSample_tmul` — sampling a simple tensor factors through the finite
    value at the zero adele.
15. `ccmRationalScalingTwo`, `ccmRationalFiniteHaarNull`,
    `ccmRationalFiniteHaarNull_integral`, `ccmRationalFiniteHaarNull_zero` — the finite factor
    `1_Ẑ − 2·(1_Ẑ ∘ 2)` has zero Haar integral and value `−1` at zero.  This replaces the card's
    zero-integral archimedean bump: the `ε₁` condition is carried by the finite factor, so each
    archimedean witness is a *single* bump.
16. `orbitCentre`, `orbitBump`, `orbitWitnessArch`, `orbitWitnessArch_centre`,
    `orbitWitnessArch_eq_zero_of_out`, `orbitWitnessArch_centre_ne`, `orbitWitnessArch_base` —
    **`(TPS.18)`**: bumps at the centres `1 + 2^{−(j+1)}`, of radius `2^{−(j+4)}`, are supported
    in `(1,2)`, pairwise separated, and miss the base point `7/4`.
17. `orbitWitness`, `orbitWitness_mem` — **`(TPS.19)`**: the witnesses lie in the two-endpoint
    kernel.
18. `ccmRationalAdelicOrbitSample_witness`, `ccmRationalAdelicOrbitSample_witness_base`,
    `ccmRationalAdelicOrbitPhaseCovector_witness` — **`(TPS.20)`, `(TPS.21)`**: the orbit-phase
    covectors are a dual family to the witness classes.
19. `orbitWitnessClass_linearIndependent`,
    `not_finiteDimensional_ccmRationalAdelicTwoEndpointCoinvariants`,
    `exists_independent_orbitWitnesses` — **`(TPS.17)` boxed**: the two-endpoint coinvariants are
    infinite-dimensional, so normalized two-endpoint Stokes covectors form an infinite-dimensional
    affine space.

## Scope

Sections 7 (consequences), 8 (hostile conjecture loop) and 9 (novelty boundary) are commentary.
The three open gates — the induced Fourier action on the coinvariant quotient, all-prime
compatibility, and target fixed-ideal coefficient rigidity — are **not** formalized and are not
claimed; the card is explicit that no Fourier/Poisson action on this cohomology has been
constructed and that claiming one would be theatre.

## Verification

```text
lake env lean GaloisForLFunctions/RHTower/CCM/CCMRationalAdelicTwoEndpointStokesModuli.lean  # clean
lake build GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicTwoEndpointStokesModuli          # green
```

`#print axioms` on `twoEndpointH1Equiv`, `twoEndpointH1Equiv_retainedClass`,
`twoEndpointStokesCovector_shift_eps1`, `twoEndpointStokesCovector_add_normalized`,
`twoEndpointNormalizedCovector_sub`, `twoEndpointNormalizedCovector_from_primitive`,
`ccmRationalAdelicTwoEndpointH1Equiv`, `ccmRationalAdelicTwoEndpointStokes_haar_collapse`,
`ccmRationalAdelicOrbitSample_orbitDifference`, `ccmRationalAdelicOrbitPhaseCovector`,
`ccmRationalArchimedeanPrimeOrbitStokes_of_support`, `ccmRationalFiniteHaarNull_integral`,
`ccmRationalFiniteHaarNull_zero`, `orbitWitness_mem`,
`ccmRationalAdelicOrbitPhaseCovector_witness`, `orbitWitnessClass_linearIndependent`,
`not_finiteDimensional_ccmRationalAdelicTwoEndpointCoinvariants` and
`exists_independent_orbitWitnesses` returns only `[propext, Classical.choice, Quot.sound]`.
