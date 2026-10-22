# Rational-adelic H1 observer-coefficient freedom and discriminant law — formalized

- **ID:** `rational-adelic-h1-observer-coefficient-freedom-and-discriminant-law-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `rational-adelic-h1-observer-coefficient-freedom-and-discriminant-law.md`
  (same directory)
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module | Path |
|---|---|
| `GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicPrimeIsotropyObserverFreedom` | `formal/GaloisForLFunctions/RHTower/CCM/CCMRationalAdelicPrimeIsotropyObserverFreedom.lean` |

Wired into `GaloisForLFunctions.RHTower`.  All declarations live in the root namespace `RHTower`,
matching the CCM prime-isotropy modules they extend.

## Corpus reuse

Nothing below was rebuilt.

- `RHTower/CCM/CCMRationalAdelicPrimeIsotropyRelativeXiChainMap.lean` — the whole source complex:
  `CCMRationalAdelicPrimeRelativeOne`, `ccmRationalAdelicPrimeRelativeD0` (`D₀x = (Tx, ε₀x)`),
  `ccmRationalAdelicPrimeRelativeD1`, `ccmRationalAdelicPrimeRelativeComplex`,
  `ccmRationalAdelicPrimeRelativeCocycle` (`η_p = (0,1)`), `ccmRationalAdelicPrimeRelativeClass`,
  `ccmRationalAdelicPrimeRelativeClass_ne_zero`, and the strict Route-R comparison
  `ccmRationalAdelicPrimeRelativeXiComparison0/1/2`, `ccmRationalAdelicPrimeRelativeXiChainMap`.
- `RHTower/CCM/CCMRationalAdelicPrimeIsotropyStokesRegulator.lean` — the bilateral orbit Stokes
  primitive `ccmRationalAdelicPrimeOrbitStokesLM` (`R_p`), its exact law
  `ccmRationalAdelicPrimeOrbitStokes_scaling_sub` (`R_p T = ε₀`, card `(OCF.5)`), the descended
  period `ccmRationalAdelicPrimeRelativeH1StokesRegulator` and its normalisation
  `ccmRationalAdelicPrimeRelativeH1StokesRegulator_class`.
- `RHTower/CCM/CCMRationalAdelicEpsilonZero.lean` — `ccmRationalAdelicBruhatZeroEval` (`ε₀`) and its
  scaling invariance `ccmRationalAdelicBruhatZeroEval_smul`.
- `RHTower/CCM/CCMRationalAdelicEpsilonOne.lean` — `ccmRationalAdelicBruhatIntegral` (`ε₁`) and its
  rational-scaling invariance `ccmRationalAdelicBruhatIntegral_smul`, which is card `(OCF.21)`.
- `RHTower/CCM/CCMRationalFiniteAdeleHaar.lean` — `ccmRationalIntegralFiniteAdeles`, its openness and
  compactness, and the normalisation `ccmRationalFiniteAdeleHaar_integral_subring` (`μ_f(Ẑ) = 1`).
- `RHTower/CCM/CCMRationalArchimedeanHaar.lean` — `ccmRationalArchimedeanSchwartzIntegral` and the
  Jacobian law `ccmRationalArchimedeanSchwartzIntegral_scaling`.
- `RHTower/PrimeFirstTraceGradedVariableIdealFixedXiComparison.lean` — `PrimeTraceSequence`,
  `primeFirstTraceSummableIdeal`, `primeFixedPhysicalFisherClass` and the sharp summability wall
  `primeFixedPhysicalFisherClass_ne_zero_iff`, which is the card's `[F_u] = 0 ⟺ u < 0`.
- `RHTower/Deninger/DeningerArithmeticThreeTermCohomology.lean` / `DeningerThreeTermOperations.lean` —
  `cycles1`, `boundaries1`, `H1`, `H1_mk_eq_zero_iff`, `DeningerThreeTermHom.H1map`.
- `HTGeometry/GaussianSchwartz.lean` — `gaussianSchwartz`, the Gaussian as a `SchwartzMap ℝ ℂ`.
- From mathlib: `LocallyConstant.indicator`, `MeasureTheory.integral_indicator_const`,
  `integral_gaussian`, `integral_complex_ofReal`, `LinearMap.coprodEquiv`,
  `LinearMap.ringLmapEquivSelf`, `LinearEquiv.arrowCongr`.

## Formal theorem chain

### Theorem A — full source `H¹` decomposition, cards `(OCF.6)`–`(OCF.10)`

1. `ccmRationalAdelicPrimeOrbitDifference` (`T = α_p − 1`),
   `ccmRationalAdelicPrimeOrbitDifference_mem_ker` (`im T ⊆ ker ε₀`),
   `ccmRationalAdelicPrimeResidualRelations`, `CCMRationalAdelicPrimeResidualQuotient` —
   **`(OCF.6)`**: the intrinsic residual quotient `Q_p = ker ε₀ / im T`.
2. `ccmRationalAdelicPrimeRelativeCyclesSplit`,
   `ccmRationalAdelicPrimeRelativeCyclesSplit_boundaries`,
   `ccmRationalAdelicPrimeRelativeH1Split` — **`(OCF.8)`**: the coordinate change
   `(y,z) ↦ ([y], z − R_p y)` is well defined on cohomology, because `R_p T = ε₀` sends the
   boundary subspace onto `im T ⊕ 0`.
3. `ccmRationalAdelicPrimeResidualToH1`, `ccmRationalAdelicPrimeStokesLineToH1`,
   `ccmRationalAdelicPrimeRelativeH1Unsplit` — **`(OCF.9)`**, **`(OCF.9a)`**: the inverse, whose
   independence of the representative is exactly
   `ccmRationalAdelicPrimeResidualToH1Raw_relations`.
4. `ccmRationalAdelicPrimeRelativeH1Equiv` — **`(OCF.7)` boxed**: `H¹(C_p) ≅ Q_p ⊕ ℂ`.
5. `ccmRationalAdelicPrimeRelativeH1Equiv_class` — **`(OCF.10)`**: the retained class is the Stokes
   generator `(0,1)`.

### Theorem B — the resolved comparison kills all of `H¹`, cards `(OCF.13)`–`(OCF.16)`

6. `ccmRationalAdelicPrimeRelativeXiChainMap_H1map_eq_zero` — **`(OCF.14)` boxed**: because the
   degree-one comparison is `Φ¹(y,z) = z·δL_p`, *every* cocycle image is the resolved boundary of
   `z·L_p`, so the induced map on `H¹` is identically zero.  The corpus only had this for the
   retained class.
7. `ker_ccmRationalAdelicPrimeRelativeXiChainMap_H1map` — **`(OCF.15)`**: `ker H¹(Φ_p) = H¹(C_p)`.
8. `ccmRationalAdelicPrimeObserverDescentEquiv` — **`(OCF.16)` boxed**: the observer-descent space
   is the entire dual-valued space `Hom(H¹(C_p), V) ≅ Hom(Q_p, V) ⊕ V`, the last isomorphism using
   the chosen Stokes splitting.

### Theorem C — the target coefficient is completely free, cards `(OCF.17)`–`(OCF.20)`

9. `ccmRationalAdelicPrimeStokesObserver` — **`(OCF.18)`**: `P_v = Ī_p(·)·v`.
10. `ccmRationalAdelicPrimeStokesObserver_class` — **`(OCF.19)`**: `P_v([η_p]) = v`.
11. `ccmRationalAdelicPrimeStokesObserver_injective` — **`(OCF.20)`**: `v ↦ P_v` is injective, so
    abstract duality makes every coefficient available and selects none.

### Theorem D — the Haar trace produces Stokes ambiguity, cards `(OCF.21)`–`(OCF.28a)`

12. `ccmRationalAdelicBruhatIntegral_orbitDifference` — **`(OCF.21)`**: `ε₁T = 0`, from the
    corpus's rational-scaling invariance of the adelic Haar integral.
13. `ccmRationalIntegralFiniteAdeles_isClopen`, `ccmRationalIntegralFiniteAdelesBruhat`,
    `ccmRationalIntegralFiniteAdelesBruhat_apply`,
    `ccmRationalFiniteBruhatIntegral_integralFiniteAdelesBruhat` — **`(OCF.22a)`–`(OCF.22c)`**:
    `1_Ẑ` is a genuine finite Bruhat function with Haar integral one.
14. `ccmRationalArchimedeanSchwartzIntegral_gaussianSchwartz`,
    `ccmRationalArchimedeanHaarWitness`, `ccmRationalArchimedeanHaarWitness_zero`,
    `ccmRationalArchimedeanSchwartzIntegral_haarWitness` — **`(OCF.22)`, `(OCF.24)`**: the
    archimedean witness.  The card uses `x²e^{−πx²}`; the Lean file uses the orbit difference of
    Gaussians `g(p⁻¹x) − g(x)`, which likewise vanishes at the origin (`g(p⁻¹·0) = g(0)`) but has
    mass `p − 1 ≠ 0`, because the archimedean Haar integral carries a Jacobian and the value at
    the origin does not.  This avoids computing a Gaussian second moment.
15. `ccmRationalAdelicHaarWitness`, `ccmRationalAdelicHaarWitness_zeroEval`,
    `ccmRationalAdelicHaarWitness_integral`, `ccmRationalAdelicHaarWitness_integral_ne_zero` —
    **`(OCF.23)`, `(OCF.24a)`**: `ε₀(y) = 0` and `ε₁(y) = p − 1 ≠ 0`.
16. `ccmRationalAdelicHaarWitness_notMem_residualRelations`,
    `ccmRationalAdelicPrimeResidualQuotient_nontrivial` — **`(OCF.25)` boxed**: `Q_p ≠ 0`.
17. `ccmRationalAdelicPrimeShiftedStokesLM`,
    `ccmRationalAdelicPrimeShiftedStokes_scaling_sub` — **`(OCF.26)`, `(OCF.27)`**:
    `R_{p,λ} = R_p + λε₁` satisfies the same exact Stokes law.
18. `ccmRationalAdelicPrimeShiftedStokesRegulatorLM`,
    `ccmRationalAdelicPrimeShiftedStokesRegulator_comp_D0`,
    `ccmRationalAdelicPrimeShiftedStokes_boundaries_le_ker`,
    `ccmRationalAdelicPrimeRelativeH1ShiftedStokes`,
    `ccmRationalAdelicPrimeRelativeH1ShiftedStokes_class` — **`(OCF.28)`**: every shift kills all
    boundaries and is still normalised to one on the retained class.
19. `ccmRationalAdelicHaarWitnessCocycle`,
    `ccmRationalAdelicPrimeRelativeH1ShiftedStokes_injective` — **`(OCF.28a)`**: distinct shifts
    give distinct cohomology covectors, evaluated on the class of `(y, 0)`.  Scaling invariance,
    source trace, boundary annihilation and period-one normalisation therefore do not select the
    Stokes covector.

### Theorem E — reflection-doubled observer discriminant, cards `(OCF.29)`–`(OCF.36)`

20. `CCMRationalPrimeFixedPhysicalSpace`, `primeReflectionDoubledObserver`,
    `primeObserverAxisDiscriminant` — **`(OCF.29)`, `(OCF.30)`, `(OCF.35)`**.
21. `primeReflectionDoubledObserver_fst_ne_zero_iff`,
    `primeReflectionDoubledObserver_snd_ne_zero_iff` — the card's summability classification
    `[F_u] = 0 ⟺ u < 0` (`(OCF.31)`), transported through a nonzero divisor scalar.
22. `primeReflectionDoubledObserver_ne_zero` — **`(OCF.32)`**: origin avoidance throughout
    `|t| < 1`.
23. `primeReflectionDoubledObserver_pos`, `primeReflectionDoubledObserver_neg_grade` —
    **`(OCF.33)`, `(OCF.34)`**.
24. `primeReflectionDoubledObserver_notMem_axisDiscriminant_iff` — **`(OCF.36)` boxed**: the
    doubled coefficient avoids the coordinate-axis discriminant exactly at neutral grade.
25. `primeReflectionDoubledObserver_neg`, `primeObserverAxisDiscriminant_swap` — reflection swaps
    the two components and preserves the discriminant.

## Scope

Sections 7 (hostile conjecture loops), 8 (RH leverage) and 9 (novelty boundary) are commentary on
the formalized statements.  The card's `[OPEN CORE] [SOURCE_OBSERVER_DISCRIMINANT_TRANSVERSALITY]`
and the RH gate are **not** formalized and are not claimed: the card states plainly that at the
physical specialisation `t_ρ = 2 Re ρ − 1`, global discriminant avoidance *is* RH and cannot be
inserted as a premise.  The Lean file therefore proves the discriminant law as a statement about
an arbitrary grade `t` in the moderate strip, with no divisor input.

## Verification

```text
lake env lean GaloisForLFunctions/RHTower/CCM/CCMRationalAdelicPrimeIsotropyObserverFreedom.lean  # clean
lake build GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicPrimeIsotropyObserverFreedom          # green
```

`#print axioms` on `ccmRationalAdelicPrimeRelativeH1Equiv`,
`ccmRationalAdelicPrimeRelativeH1Equiv_class`,
`ccmRationalAdelicPrimeRelativeXiChainMap_H1map_eq_zero`,
`ker_ccmRationalAdelicPrimeRelativeXiChainMap_H1map`,
`ccmRationalAdelicPrimeObserverDescentEquiv`, `ccmRationalAdelicPrimeStokesObserver_class`,
`ccmRationalAdelicPrimeStokesObserver_injective`, `ccmRationalAdelicBruhatIntegral_orbitDifference`,
`ccmRationalFiniteBruhatIntegral_integralFiniteAdelesBruhat`,
`ccmRationalAdelicHaarWitness_zeroEval`, `ccmRationalAdelicHaarWitness_integral`,
`ccmRationalAdelicPrimeResidualQuotient_nontrivial`,
`ccmRationalAdelicPrimeShiftedStokes_scaling_sub`,
`ccmRationalAdelicPrimeRelativeH1ShiftedStokes_class`,
`ccmRationalAdelicPrimeRelativeH1ShiftedStokes_injective`,
`primeReflectionDoubledObserver_ne_zero`, `primeReflectionDoubledObserver_pos`,
`primeReflectionDoubledObserver_neg_grade`,
`primeReflectionDoubledObserver_notMem_axisDiscriminant_iff`,
`primeObserverAxisDiscriminant_swap` and `primeReflectionDoubledObserver_neg` returns only
`[propext, Classical.choice, Quot.sound]`.
