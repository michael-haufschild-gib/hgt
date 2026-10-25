# Full-Cone Riemann–Roch & Bézout, Invariant Trace Majorant, or Zero-Rate H¹ Floor

- **ID:** acs-full-cone-majorant-floor-2026-10-25
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `docs/reports/rh-current-frontier-map.md` (`#acs`, line 521); `formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/README.md`
- **Statement:** Establish unconditionally in Lean 4 either: (A) `RiemannRochAxiom` and `BezoutAxiom`/`AmpleAxiom` on the same full arithmetic source cone of `scalingSurface` or `meyerScalingSurface`, or (B) a centered-flow-invariant quadratic majorant `Φ` for `meyerSourceTrace` on `DeningerMeyerStrongLogTarget`, or (C) a zero-rate (equivalently, aperture-uniform) `H¹` Sobolev defect floor across all apertures `r > 0` (including via signed coalescent surplus control).

## Goal
Deliver a complete, unconditional, axiom-clean (`propext`, `Classical.choice`, `Quot.sound`) solution of the ACS closing target—not a new reformulation, criterion, numerical improvement, or unrescued no-go. By established ACS theorems (`HodgeIndexFromEffectivity.exists_effectivity_iff_hodgeIndex`, `ExactArithmeticSourceEffectivity.globalExactArithmeticSourceCone_bezout_iff`, `MeyerSourceIntersectionSurface.meyerDegreeSourceCone_bezout_iff`, `FlowInvariantMeyerMajorantsForceCriticality.exists_invariant_meyer_trace_majorant_iff`, `AllParityCriticalDeficitAndEndpointSobolevLaws.riemannHypothesis_iff_uniform_gradedSobolevSourceCone_riemannRoch`), every branch (A), (B), (C) is unconditionally equivalent to `RiemannHypothesis`.

## Gates
- [x] Phase 1 (Contextualize): Read `ACS`, `SBWF`, `MPG`, `AKT`, `APD`, `AOG`, `BG`, `TTPC` READMEs, 2026-10-25 frontier reviews (`opus`, `astra`, `fable`, `walls-ledger`, `what-forces-blindness`), and active pipeline cards (`q-i`, `q-ii`, `q-iii`, `rh-closing-producer-conjecture-loop-2026-10-25`, `forcing-blindness-loop-2026-10-25`, `ccm-published-gap-closure-2026-10-21`).
- [x] Phase 2 (External SOTA Audit): Audited primary literature through October 2026: Connes–Consani–Moscovici (2020–2026, scaling site periodic-orbit RR, Sonin trace formula, prolate/Dirac determinants), Meyer (2005, idèle-class Fréchet representation and explicit trace formula), Suzuki (2023–Sept 2026, `arXiv:2606.09096`, screw-function `H¹` representation of Weil's quadratic form & de Branges spaces), van der Geer–Schoof (2000) / Vignéras (1977) / Zwegers (2002) (Arakelov theta `h⁰` and Lorentzian `(1, r-1)` indefinite theta completions), and Goldston–Suriajaya / Maynard–Pratt / Guth–Maynard (2024–2026, pair correlation beyond Montgomery & large-value zero density).
- [ ] Phase 3 (Conjecture beyond SOTA): Formulate competing, well-typed, non-circular candidate mechanisms across branches (A), (B), (C) that pass the full selectivity battery (`goldenDatum`, DMV Beurling, `S ⊂neq ℙ`, over-regular continuous counts, parity twins).
- [ ] Phase 4 (Try to end the route): Ruthlessly attack each candidate for falsity, circularity, hidden boundary/cutoff leaks, or battery failure; enter relentless interrogation after every refutation.
- [ ] Phase 5 (Complete paper proof): Dependency-closed paper proof with zero `[OPEN CORE]`.
- [ ] Phase 6 (Lean 4 formalization & Anti-theatre test): Foreground `lake --old env lean` verification, `#print axioms` audit, umbrella wiring.
- [ ] Phase 7 & 8 (Anti-laziness test & Iteration): Continue cycles until the target is achieved.

## Phase 1 & 2 Synthesis: Exact Obstacles & Surviving Openings

### Established Obstacles (Formalized in Corpus)
1. **Boundary Rigidity (`SourceConeBoundaryRigidity`, `BezoutCostsTwiceTheNegativeReserve`):** Any fibre-invariant reserve `Φ` whose `sourceCone Φ` satisfies both `RiemannRochAxiom` and `BezoutAxiom` must satisfy `Φ(x) = defect(x, x) ≥ 0`. Adding `2R` (`R ≥ 0`) buys Bézout when `defect + R ≥ 0` (`globalArithmeticMajorantCone`) at the price of breaking graded RR unless `R = 0`.
2. **Full Hasse Faithfulness Adds Simplicity (`FaithfulHilbertSchmidtSourceReserves`, `BoundedMeyerSourceSurface`):** `meyerHilbertSourceCone` has unconditional Bézout and ampleness, while its RR is equivalent to `RiemannHypothesis ∧ ∀ ρ, xiSupportMultiplicity ρ = 1` due to Jordan nilpotent growth under centered flow.
3. **Single-Channel Positivity Is Blind (`MaximalBlindIdealOfTheMeyerSource`):** `isGreatest_meyerSharpPositiveIdeal` proves that every `♯`-stable right convolution ideal on which `meyerSourceTrace` is nonnegative lies in `meyerTraceBoundedIdeal` (functions vanishing on off-line `Ξ` zeros).
4. **Origin-`L²` & Finite-Reading Blindness (`PoissonBoundariesAreDenseInOriginMass`, `OriginHilbertCohomologyObstruction`, `FiniteDegreeConesCannotSatisfyBezout`):** Poisson boundaries `∑_{n≥1} f(nx)` are dense in `L²(ℝ, du)` half-densities; every continuous cohomological functional factoring through origin `L²` is constant; every finite-dimensional linear reading has negative-square cycles in its kernel.
5. **Countermodel Elimination (`BeurlingRiemannFunctionalEquationRigidity`, `HamburgerIntegralMassRigidity`, `C-18`):** Positive integer masses `ℕ` + Poisson/theta functional equation uniquely force `∑_{n≥1} δ_n`; 2-periodicity + full additive sieve `∑_{m≥1} m^{-1-ε} G_ε(mx) = C_2(⌊x⌋)` uniquely force `μ(d)`. Thus any mechanism genuinely coupling `(ℤ, +)` Poisson/successor structure with `(ℕ_{≥1}, ×)` complete Euler/Möbius factorization has **no** countermodels.

### Active Conjecture Arena (Phase 3 Queue)
To be populated and attacked in Phase 3 & 4.
