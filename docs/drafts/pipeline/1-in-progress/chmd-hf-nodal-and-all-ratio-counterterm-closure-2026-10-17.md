# CHMD Nodal-Cross vs. Prime-Shift Closure & HF All-Ratio Secular/Window Counterterm Closure

- **ID:** chmd-hf-nodal-and-all-ratio-counterterm-closure-2026-10-17
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/rh-current-frontier-map.md · Routes `CHMD` + `HF` + `OWU`
- **Statement:** (1) On `SourceGraph`, `-4 sourcePair(posGraph p, negGraph p)` decomposes into the sum of two non-negative terms — `-4 ⟪(fullGroundEquiv p⁺).snd, (fullGroundEquiv p⁻).snd⟫` (strictly positive on sign-changing vectors) and `4 ⟪primeShiftOperator p⁺.fst, p⁻.fst⟫` — which reinforce each other in the primitive-contraction nodal bound, satisfy three-term individual nodal-lobe energy identities and exact odd half-mass lobe laws, and force `ν ≤ μ_max` (or `ν < μ_max` when the primitive `oneL`-defect is dominated by the prime-shift cross term alone). (2) On `HF`, the `M`-stage secular counterterm potential `secantStagePotential M n` telescopes `secantCombinedSecularWeight n * (2 / √n)` exactly for `2 ≤ n < M` with zero square-root relaxation loss on `Finset.Icc 2 (M - 1)`, decreases monotonically in `M`, and combines with the `+ 2 * sinhHalfMoment f ^ 2` plastic bonus and `oddShift` window laws to establish all-ratio (`S / L` unrestricted) `markovEnergy ≥ 0`, prime-blind impossibility, and spectral-gap rigidity whenever `2 * sinhHalfMoment f ^ 2` covers the high-frequency secant excess.

## Goal
Close the two coupled analytic steps identified in the frontier review of `CHMD` + `HF` + `OWU`:
1. **Target 1 (`CHMD`):** Bridge the nodal-cross term `-4 sourcePair(p⁺, p⁻)` in `CHMDSpectralBesselAndPrimitiveContractionNodalBounds.lean`, the stationary-vs.-prime-shift decomposition in `CHMDStationaryResolventDictionaryAndNodalPolarization.lean`, and the nodal-lobe Rayleigh algebra in `CHMDEigenvectorNodalLobeEnergiesAndPrimitiveLobeBounds.lean` into bilateral nonnegative decompositions, odd half-mass lobe laws, universal primitive-contraction resolvent polarization identities, and explicit eigenvalue upper-bound (`ν ≤ μ_max` and `ν < μ_max`) criteria.
2. **Target 2 (`HF`):** Generalize the finite 4-stage secular counterterm telescoping in `MarkovDegreeSixteenFirstCellAndTwentySevenRatioPBAP.lean` to an arbitrary `M`-stage potential `secantStagePotential M n` (`M ≥ 2`, with adaptive zero-loss telescoping at `M = N + 1` and stage-monotonicity / closed rational bounds for `M = 6..9`) and unify it with the `+ 2 * sinhHalfMoment f ^ 2` bonus and `oddShift` window laws in `MarkovOddShiftWindowAndPlasticCrossoverPBAP.lean` and `MarkovOddSectorFarkasAndOneSidedPBAP.lean` to obtain all-ratio (`S / L` arbitrary) coercivity, `markovEnergy ≥ 0`, and prime-blind vanishing criteria.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean modules `CHMDNodalCrossPrimeShiftAndPrimitiveRayleighClosure` and `MarkovMultiStagePotentialAndAllRatioSinhCrossoverPBAP`, `lake env lean` green, `#print axioms` clean, `scripts/formal_tools.py lint` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach
1. **Target 1 (`formal/GaloisForLFunctions/RHTower/CHMDNodalCrossPrimeShiftAndPrimitiveRayleighClosure.lean`):**
   - Import `GaloisForLFunctions.RHTower.CHMDEigenvectorNodalLobeEnergiesAndPrimitiveLobeBounds`.
   - Prove the bilateral nonnegative decomposition of `-4 * sourcePair (posGraph p) (negGraph p)` into `-4 * ⟪(fullGroundEquiv (posGraph p)).snd, (fullGroundEquiv (negGraph p)).snd⟫ + 4 * ⟪primeShiftOperator (posGraph p).val.fst, (negGraph p).val.fst⟫`, showing both summands are `≥ 0` and `-4 * sourcePair p⁺ p⁻ > 0` whenever `posGraph p ≠ 0` and `negGraph p ≠ 0` (in particular for any nonzero primitive or odd vector).
   - Substitute this bilateral decomposition into `nodal_cross_le_of_primGraph_absGraph_rayleigh_le` and `eigenvector_nodal_cross_le_of_primGraph_absGraph_rayleigh_le`, proving that both the stationary cross-jump and prime-shift cross-jump reinforce the spectral-gap term `((ν - μ_max) / (ν * μ_max)) * ‖p.val.fst‖^2`.
   - Deduce unconditional eigenvalue upper bounds `ν ≤ μ_max` when `2 * ((1 - μ_max) / μ_max) * ⟪|w|, oneL⟫^2 ≤ -4 * sourcePair p⁺ p⁻` and strict `ν < μ_max` when `2 * ((1 - μ_max) / μ_max) * ⟪|w|, oneL⟫^2 ≤ 4 * ⟪primeShiftOperator p⁺.val.fst, p⁻.val.fst⟫` for any nonzero primitive eigenvector `w`.
   - Prove the three-term nonnegative decomposition of individual lobe energy `‖(posGraph q).val.snd‖^2 - ⟪(fullGroundEquiv q⁺).snd, (fullGroundEquiv q⁻).snd⟫ + ⟪primeShiftOperator q⁺.val.fst, q⁻.val.fst⟫ = ((1 - μ) / μ) * ‖(posGraph q).val.fst‖^2` (and for `negGraph q`), giving individual lobe upper bounds on both the stationary cross-jump and prime-shift cross-jump.
   - Prove the exact odd-sector (`reflectGraph p = -p`) half-mass lobe identities for `.fst`, `.snd`, and `sourceEnergy` on `posGraph p` and `negGraph p`.
   - Prove the universal primitive-contraction resolvent polarization identity relating `⟪resolvent (primGraph (absGraph p)).val.fst, (primGraph (absGraph p)).val.fst⟫` to `⟪resolvent p.val.fst, p.val.fst⟫`, `4 * ⟪resolvent p⁺.val.fst, p⁻.val.fst⟫`, and `2 * ⟪|p.val.fst|, oneL⟫^2`.
2. **Target 2 (`formal/GaloisForLFunctions/RHTower/MarkovMultiStagePotentialAndAllRatioSinhCrossoverPBAP.lean`):**
   - Import `GaloisForLFunctions.RHTower.MarkovDegreeSixteenFirstCellAndTwentySevenRatioPBAP` and `GaloisForLFunctions.RHTower.MarkovOddSectorFarkasAndOneSidedPBAP`.
   - Define `secantStagePotential (M n : ℕ) : ℝ` for arbitrary stage horizon `M` and prove exact telescoping `secantStagePotential M n - secantStagePotential M (n + 1) = secantCombinedSecularWeight n * (2 / √n)` for `2 ≤ n < M`, tail majorization for `n ≥ M ≥ 2`, nonnegativity `0 ≤ secantStagePotential M n` for `M ≥ 2, n ≥ 2`, stage monotonicity `secantStagePotential (M + 1) 2 ≤ secantStagePotential M 2`, exact agreement with `secantFourStagePotential` at `M = 6`, closed bounds for `M = 7, 8, 9`, and the adaptive `N`-stage prime-blind counterterm bound `|primeBlindCounterterm secantCombinedSecularWeight f| ≤ secantStagePotential M 2 * ∫ ‖f.1‖^2`.
   - Combine the degree-16 first-cell secular bound and `secantStagePotential` with the retained `+ 2 * sinhHalfMoment f ^ 2` plastic crossover bonus and `oddShift` window laws to establish all-ratio (`S / L` unrestricted) `0 ≤ markovEnergy f`, prime-blind vanishing `f = 0`, and spectral-gap laws whenever `2 * sinhHalfMoment f ^ 2` covers the high-frequency secant excess.

## Log
- 2026-10-17 — created in 1-in-progress
