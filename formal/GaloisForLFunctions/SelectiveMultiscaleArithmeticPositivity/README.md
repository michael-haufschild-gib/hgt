# Selective Multiscale Arithmetic Positivity (SMAP)

Namespace `GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity`; umbrella `SelectiveMultiscaleArithmeticPositivity.lean`;
18 modules. All results are unconditional; theorems of the form `RH ↔ …` are equivalences, not proofs of RH. No module carries
`#print axioms` lines.

## 1. Motivation

Every positivity the corpus proves on the complete arithmetic source (Gamma payment of cell differences, the high Haar-detail
floor, narrow atomic positivity) also holds for every bounded twist `ωΛ`, `|ω| ≤ 1`. The Liouville twin is not Weil positive.
So a proof of RH must use an inequality that is true for `Λ` and false for its twins: a **selective** inequality. SMAP locates
where `Λ` differs from its twins (the pole hyperplane), measures the size of the difference (`2 log 2`), and sets up the
multiscale structure (dyadic levels of the complete source) on which a selective inequality would have to survive infinite
refinement.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Atomic positivity at a root | `AtomicPositiveAt` | eventually `Q_λ ≥ 0` on atomic tests of width `1/κ_N` at `log n`, `n ≤ N` |
| Pole moments | `poleMomentA`, `poleMomentB`, `polePairing` | `A(f) = ∫f e^{−u/2}`, `B(f) = ∫f e^{u/2}`; `A(f)B(g) + A(g)B(f)` |
| Harmonic coordinate | `harmonicSum`, `harmonicMass`, `poleProj` | `ℓ(x) = Σx_n/√n`; `H_N = Σ1/n`; projection along `u_n = n^{−1/2}` |
| Finite part, retained fraction | `markovFinitePart`, `defectFractionRetained` | `φ₀` of the Markov form; `c₀ = 1 − ε − 32e²wN` |
| Hyperplane gap | `HasHyperplaneGap` | on `ℓ(x) = 0`: `P_N(ωx) ≤ (log N − γ − g + ε)|x|²` eventually |
| Gauge correlation | `gaugeHarmonicSum`, `gaugeWitness` | `S_N(ω) = Σω(n)/n`; `(ω_n − S_N/H_N)n^{−1/2}` |
| Pole split | `poleCoord`, `poleResidual` | `y = αb + z`, `z ⟂ b` |
| Twisted rough form | `roughWeilTw` | full signed form of `ωΛ` on compact BV sources |
| RG margin | `rgMargin` | `μ_{L+1} = min(μ_L − c_L, d_L)` |
| Complete cells | `logCell`, `translate`, `coarseCoeff`, `detailCoeff`, `logDetail`, `levelPart`, `orbitPairing` | `1_{[log a, log(a+1))}`; pair averages/half-differences; level-`j` part |
| Dyadic shift | `dyadicShift` | `(Sx)_{2m} = x_m`, odd entries `0` |
| Level orbit | `levelOrbit` | `Σ_j c_j f(· − s_j)` |
| Tower positivity | `TowerPositive`, `DyadicPositive`, `lagW`, `primeMass` | every window of `T_{kℓ}g` has no negative square; lag correlation; prime mass of a weight difference |
| Shifted test | `shiftTest` | `φ(· − t)` as a real test |

External: `weilQuadTw`, `atomicTest`, `atomicWeilForm`, `twistedAtomicWeilForm`, `atomSpacing`, `atomDilate`
(SpacingScaleHarmonicAnalysis / ArithmeticElectrostatics); `poleDefect`, `fullPrimeMatrix`, `ramanujanAdjunctionEnergy`,
`truncPole`, `liouvilleSign` (RenormalizedArithmeticPotentialTheory); `tameDifferent` (ArithmeticIntersectionTheory); `haarSectionProfile`, `haarMass`,
`haarPrimeEntry`, `weilGram` (ArithmeticCastelnuovoSeveri); `orderedGammaTail`, `sectionMass` (ArithmeticIndexDescent);
`liouvilleTwin` (ArithmeticCorrespondencePositivity / ArithmeticLorentzianGeometry).

## 3. Language

- **Twin**: weight `ωΛ` with `|ω| ≤ 1`; **sign gauge**: `ω² = 1`; Liouville twin `λ(n)Λ(n)`.
- **Twin-blind**: holds for every twin of a family. **Selective**: true for `Λ`, false for a named twin.
- **Pole hyperplane**: `A(f) = 0`; on atomic tests it is the harmonic hyperplane `Σx_n/√n = 0`.
- **Ceiling**: `log N − γ`, the top of the prime form (pole direction). **Gap**: distance below the ceiling on the hyperplane.
- **Level**: dyadic translate `T_{j log 2}`; **coupling cost**: coarse margin spent to pay a cross-level pairing.
- **Tower**: `g, T_ℓ g, T_{2ℓ} g, …`; Hecke tower at `ℓ = log p`.

## 4. Mechanisms

**A. Selection and the pole hyperplane**

1. **Selection at a root.** Atomic families of finite overlap order are RH-complete and the Weil cone is `{Λ}` under RH, empty
   otherwise; so atomic positivity of a bounded weight at one root forces RH and the weight `Λ`.
2. **Pole split.** `W(f) = M(f) + 2A(f)B(f)`; on atomic tests `A(f_x) = A(g)ℓ(x)`, `B(f_x) = B(g)Σx_n√n`. Below the spacing,
   `W_ω(f_x) − W(f_x) = (∫g²)(P_N(x) − P_N(ωx))`: archimedean and pole terms cancel, twins differ only in the prime form.
3. **Gap transfer.** On the hyperplane `W = M ≥ (φ₀ + c₀G)‖f‖²`. The defect `D_N` ignores the pole direction, so off the
   hyperplane: `W ≥ (φ₀ + c₀G)‖f‖² − c₀G‖g‖²ℓ²/H_N + 2AB` (selective Gårding).

**B. Size of selectivity**

4. **Bottleneck.** Ramanujan profile of conductor `m` sits at `log N − E_m`, `E_m = γ + log m + τ(m)`; `log m + τ(m) ≥ 2 log 2`
   with equality only at `m = 2`. The eigenvectors at `E_1`, `E_2` span a plane meeting every hyperplane, so no sign gauge has
   gap above `2 log 2`; `ζ` attains it.
5. **Correlation.** Witness `x = (ω − S/H)b` costs `O(S²)` below the ceiling: `S_N² = o(log N)` ⇒ gap `0`. Misalignment
   `⟨y,b⟩² ≤ |y|²·2(H − S)` for `y ⟂ ωb`: `S/H → 1` ⇒ gap `2 log 2`.

**C. Multiscale structure**

6. **Self-similarity.** `C_{2a} + C_{2a+1} = T_{log 2}C_a`; the complete source on `1..2^L − 1` is `Σ_j T_{j log 2}(generator + details)`;
   translation-invariant forms are level-Toeplitz.
7. **RG calculus.** `2b + e ≥ (1−θ)δt² − (β²/(θδ))s²`; summable coupling costs below `min(μ₀, D)` keep a uniform margin; a
   positive definite detail block leaves exactly the Schur-corrected coarse block, which is lower.
8. **Pole across levels.** Pole pairing of two copies `= 2A(f)B(f)cosh((t−s)/2)`, growing like `2^{|k−j|/2}`; rank two, one
   negative direction, removed by `Σc_j 2^{−j/2} = 0`. The hyperplane is invariant under `dyadicShift` (`ℓ` scales by `1/√2`).
9. **Three-part coupling.** Adjacent levels: one constant. Separated levels: Gamma `≤ π4^{−(k−j−1)}`, pole hyperbolic (zero on
   the hyperplane), remainder `= −∫(ψ_err − c)q'` (centred Chebyshev error at the lags between levels).

**D. Tower sign**

10. **Toeplitz rigidity.** Tower Grams are Toeplitz in the lag; a `2 × 2` window bounds the symmetrized lag correlation by the
    diagonal; two weights differ only by the prime pairing of their difference, so unbounded one-signed prime mass along lags
    excludes joint tower positivity.
11. **Pole-free generators.** Annihilating tests of ACS plus the point `τ = 1` give pole-free generators on `[−ε, ε]` seeing any
    finite set of outer eigenvalues `p^{ρ−1/2}`.

## 5. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| Atomic positivity at one root ⇔ RH ∧ weight = `Λ` | `atomicPositiveAt_iff`, `not_forall_atomicPositiveAt` | proved |
| Twins differ only in the prime form | `weilQuadTw_atomicTest_sub_weilQuad` | proved |
| Pole hyperplane separates `ζ` from Liouville in full forms | `exists_pole_hyperplane_separates_full_weil_forms`, `exists_liouville_weilQuad_lt_of_harmonic` | proved |
| Selective Gårding (sharp reserve `2 log 2 − η`) | `exists_weilQuad_atomicTest_ge_selective`, `eventually_weilQuad_atomicTest_ge_sharp` | proved |
| Margin of `ζ` = `2 log 2`, of Liouville = `0`, maximal among sign gauges | `isGreatest_zeta_hyperplaneGap`, `isGreatest_liouville_hyperplaneGap`, `isGreatest_signGauge_hyperplaneGap` | proved |
| Conductor two is the unique first excitation | `ramanujanAdjunctionEnergy_sub_one_ge` | proved |
| Correlation decides the margin | `not_hasHyperplaneGap_of_harmonicSum_small`, `hasHyperplaneGap_two_mul_log_two_of_correlation`, `frequently_harmonicSum_sq_ge_of_hasHyperplaneGap` | proved |
| High-detail floor is twin-blind | `exists_haarTail_roughWeilTw_floor` | proved |
| Dyadic multiresolution, level-Toeplitz law | `sum_logCell_multiresolution`, `weilOrbitPairing_level` | proved |
| RG margin and Schur transparency | `rgMargin_pos`, `fromBlocks_posSemidef_iff_effective` | proved |
| Cosh law of pole couplings | `polePairing_shift`, `poleTerm_twoLevels_opposite` | proved |
| Separated levels couple through the Chebyshev error | `abs_weilPair_shift_add_chebyshev_le`, `abs_weilPair_add_primePart_le` | proved |
| Touching levels couple uniformly | `exists_abs_weilPair_adjacent_dyadic_le` | proved |
| Tower sign rigidity; interval statements do not decide it | `primeMass_add_le_of_towerPositive`, `not_towerPositive_and_perturbed` | proved |
| `Λ` and Liouville never both tower positive | `not_towerPositive_liouvilleTwin_and_vonMangoldt` | proved |
| Pole-free one-prime tower sign is RH at every overlap | `riemannHypothesis_iff_towerPositive_poleFree_small`, `zeta_poleFree_small_tower_law` | proved (equivalence) |

## 6. Tools

**Developed**
- Pole-hyperplane calculus on atomic tests: moments, projection, Gårding with the pole term kept.
- Hyperplane-gap extremal theory for sign gauges (witnesses, eigenvector planes, misalignment).
- RG margin recursion, Schur transparency, block dominance (Gershgorin for forms).
- Dyadic multiresolution of complete cells; level-Toeplitz law; dyadic shift on atoms.
- Three-part inter-level coupling bounds (touching, Gamma tail, Chebyshev).
- Tower Toeplitz rigidity via `2 × 2` windows; prime-mass lower bounds on log windows.

**To build**
- Signed (cancelling) estimates of the inter-level Chebyshev couplings, summable in level distance.
- A selective lower bound on generator orbits beyond the spacing scale.
- Toeplitz symbol calculus for windowed generator orbits.

## 7. Open questions

1. Is there a selective full-form inequality on a cofinal source family that the Liouville twin violates?
2. Can the Chebyshev couplings between dyadic levels be made summable by cancellation, so that `rgMargin` stays positive?
3. For `S_N/H_N → ρ ∈ (0,1)`, is the margin a function of `ρ` alone?
4. What selective input pays the low-index and generator-cell residual left by the twin-blind floor?
5. Does the sharp gap `2 log 2` transfer from atomic tests to complete-cell sources with Gamma and both poles?

## 8. Traps

| Trap | Fact |
|---|---|
| A strong twin-blind floor completes the proof | Twin-blind positivity at any finite-order root is impossible |
| The high-detail Haar floor is evidence for `ζ` | It holds for every twist, Liouville included, with the same index |
| `ζ` is the minimum of its gauge orbit | Only on nonnegative atomic tests; on the hyperplane Liouville lies strictly below |
| The hyperplane gap can be large | It is at most `2 log 2`; no sign gauge does better |
| A larger gap means more selective | The zero weight has every gap; selectivity is posed among sign gauges |
| Agreeing with `Λ` at most primes keeps a margin | The margin reads `Σω(n)/n` over integers |
| Pole couplings are summable level costs | They grow like `2^{|k−j|/2}`; they vanish only on the hyperplane |
| Separated levels can be paid in absolute value | Gamma part yes; the Chebyshev part does not decay |
| Adding a positively paid level cannot hurt | It leaves the Schur-corrected, lower coarse block |
| Interval prime statements decide the tower sign | `Λ` and `Λ + εn^{−η}` share them; at most one is tower positive |
| Small generator support gives intermediate content | Pole-free tower positivity is RH for every `ε > 0` |

## 9. Context

**Uses**

| Programme | Imports | For |
|---|---|---|
| RenormalizedArithmeticPotentialTheory | 5 | prime ceiling, pole-hyperplane gap, Liouville separation, Ramanujan spectral points, sharp `2 log 2` |
| ArithmeticCastelnuovoSeveri | 5 | Haar cell effectivity, Frobenius towers, signature law, one-prime defect, lambda ring |
| SpacingScaleHarmonicAnalysis | 3 | gauge at every root, universal threshold, critical exponent |
| RHTower | 3 | Weil cone uniqueness, ξ mass shell, theta prime schedule |
| ArithmeticLorentzianGeometry | 3 | pole defect, hyperbolicity is blind |
| ArithmeticIndexDescent | 2 | ordered Chebyshev identity, touching-cell window bound |
| ArithmeticElectrostatics | 2 | gauge at atomic resolution |
| ArithmeticCorrespondencePositivity | 1 | `ζ` is the worst twin on nonnegative tests |

**Used by**

| Programme | Modules | For |
|---|---|---|
| ArithmeticCountingPositivity | 6 | prime flips, harmonic correlation, parity tower, secular signs |
| RenormalizedArithmeticPotentialTheory | 4 | trial energies, pole projection, Ramanujan pole coordinates, mode energies |
| HeckeKreinToeplitz | 2 | selectivity battery on prime towers, index-one window |
| TransMetzlerWeilPositivity | 2 | Liouville selectivity, prime-flip complete form |
| ArithmeticIndexDescent | 1 | full prime window and growing head pole |
| `MainTheorems.lean` | 1 | aggregation |

| Neighbour | Relation |
|---|---|
| RenormalizedArithmeticPotentialTheory | owns the prime form and its gap; SMAP transfers the gap to full Weil forms |
| ArithmeticCountingPositivity | continues the margin theory for prime flips |
| HeckeKreinToeplitz | continues the tower Toeplitz sign theory |
| SignedArithmeticHodgeTheory | builds the dyadic clock on the cell space; SMAP uses the same self-similarity |

## 10. Big picture

SMAP sharpens the target. Anything the twins of `Λ` also satisfy cannot prove RH, and most positivity built so far is of that
kind. The place where `Λ` is special is the pole hyperplane, and the size of its advantage is a definite constant, `2 log 2`,
carried by the prime two and by the correlation of `Λ` with the pole. That advantage is real but small and lives at spacing
scale.

The multiscale analysis shows where it must be spent. Across dyadic levels everything is paid or removable (Gamma decays, the
pole vanishes on one hyperplane) except one quantity: the signed Chebyshev error along the dyadic orbit. Tower positivity on
pole-free generators is exactly RH at any overlap, and interval-type prime information cannot decide it. RH research must
therefore find cancellation in the prime error between scales, and use the hyperplane margin as the selective reserve that
pays it.
