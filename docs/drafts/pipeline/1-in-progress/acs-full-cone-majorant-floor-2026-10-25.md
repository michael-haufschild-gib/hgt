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

### Active Conjecture Arena (Phase 3 & Phase 4 Ledger)

#### Refuted / Circular Initial Candidates (Phase 4 Diagnostics)
- **M-01 (Zwegers / Vignéras Indefinite Theta `h⁰` on `orbitSurface`):** `CIRCULAR`. Zwegers's double-error-function completion `sgn(B(c₁, x)) - sgn(B(c₂, x))` is supported in `{Q ≥ 0}` iff `{Q < 0}` splits into two disconnected light-cone components, which requires Lorentzian `(1, r-1)` signature (`defect ≥ 0`) as an input; on an orbit seeing `D ≥ 1` off-line zeros (`zeta_orbit_signature_law`), `{pair > 0}` is connected and the sum diverges.
- **M-02 (Critical-Line Bochner Measure Majorants `Φ_μ(g) = ∫ |g~(1/2 + it)|² dμ(t)` on `DeningerMeyerStrongLogTarget`):** `INSUFFICIENT / BLIND`. Taking the quotient infimum `Φ_quot(g) = inf_{f ∈ Cap} Φ(g + Sum f)` preserves nonnegativity, centered-flow invariance, and `meyerSourceTrace` majorization, while multiplication by `ξ(1/2 + it)` on cap functions is dense away from critical-line zeros, annihilating `μ|_{\{ξ ≠ 0\}}` and leaving `Φ_quot` blind to off-line zeros.
- **M-03 (Suzuki Screw-Line Norm `‖𝔖_t‖_{L²(ℝ)}²` Identification):** `CIRCULAR`. Unconditional `memLp_suzukiFrakSFull t` gives `‖𝔖_t‖² ≥ 0`, whereas `‖𝔖_t‖² = 2π Ψ(t)` (`riemannHypothesis_iff_norm_sq_suzukiFrakSFull`) requires `E(z) = XiC(z) + i XiC'(z)` to have no upper-half-plane zeros (`StrictHermiteBiehlerGivesRH`).

#### Exact Pure Harmonic-Analysis Reduction of `EWU` / `ACS` (Derived & Verified Analytically)
By `EvenSectorBlindMinimumSmallAperturePositivity.primeBlindPositiveEvenPolar_iff_riemannHypothesis` and `EvenSectorExactMomentRealization.exists_single_smooth_exact_moments`, all three ACS targets (full-cone RR + Bézout/ampleness on `globalExactArithmeticSourceCone` / `meyerDegreeSourceCone`, centered-flow-invariant `meyerSourceTrace` majorant, and zero-rate `H¹` Sobolev defect floor) hold unconditionally iff for every single smooth even pole-free test `g : SmoothEvenPolarTestFn` with `logVector g.1.1 = 0`, `weilArchRe (EF.weilTest g g) ≥ 0`.

Setting `G(y) := |y|^{-1/2} g(log |y|)` (`G(0) := 0`) and `Ĝ = 𝓕 G`:
1. `G ∈ C^∞_c(ℝ \ {0}) ⊂ 𝓢_even(ℝ)` satisfies `G(1/y) = |y| G(y)` (`∀ y ≠ 0`) and `Ĝ(0) = ∫_ℝ G(y) dy = 0` (`Ĝ'(0) = 0`, so `|Ĝ(ξ)| = O(ξ²)` as `ξ → 0`).
2. **All-integer dilation orthogonality (both sides):** `∫_0^∞ G(n y) conj(G(y)) dy = ∫_0^∞ Ĝ(n ξ) conj(Ĝ(ξ)) dξ = 0` for every integer `n ≥ 2`.
3. **Beckner–Tate exact identity (verified on `G(y) = e^{-π y²}`):** Because `G(1/y) = |y| G(y)` kills `∫_0^∞ (log y) |G(y)|² dy = 0`,
   `weilArchRe (EF.weilTest g g) = ∫_0^∞ (log ξ) |Ĝ(ξ)|² dξ`.
4. **Co-Poisson identity:** `∑_{n=1}^∞ Ĝ(n ξ) = ∑_{m=1}^∞ (1/m) G(ξ / m)` for all `ξ > 0`; in particular `∑_{n=1}^∞ Ĝ(n ξ) = 0` identically on `ξ ∈ (0, e^{-A})` where `supp(G) ⊂ [e^{-A}, e^A]`.
5. **Phase-4 Necessity Checks Passed:**
   - Dropping `G(1/y) = |y| G(y)` fails under `Ĝ ↦ √λ Ĝ(λ ·)` (`λ → +∞` sends `∫ (log ξ) |Ĝ_λ(ξ)|² dξ → -∞`).
   - Dropping integer dilation orthogonality `(2)` fails because `λ ≡ 0 ∉ WeilPositiveEvenPolar` (`source_unique_of_weilPositiveEvenPolar`).
   - Pairing `conj(Ĝ(ξ))` with `∑_{n≥1} Ĝ(n ξ)` against flat weight `1` collapses to the tautology `∑_{m≥1} Φ(m) = φ(1) = ‖G‖²`.

#### Next Competing Non-Circular Mechanisms Under Attack (Phase 3 → Phase 4)
- **M-04 (Multiplicative-to-Additive Bi-Dilation / Hilbert-Space Projection on `(G, Ĝ)`):** Couple `(2)` (`⟨U_n G, G⟩ = ⟨U_n Ĝ, Ĝ⟩ = 0` for `n ≥ 2`), `(1)` (`G(1/y) = |y| G(y)`), and `(4)` (`∑_{n≥1} Ĝ(n ξ) = ∑_{m≥1} m^{-1} G(ξ/m)`) with logarithmic scale integration `∫_0^∞ (dc/c) ∫_0^c ...` or Mellin–Hardy Hankel/Toeplitz factorization.
- **M-05 (Two-Channel / Biarithmetic Meyer Correspondence Positivity on `DeningerMeyerStrongLogTarget`):** Test whether coupling centered scaling `D_a` with additive Fourier/sheaf translation escapes single-channel `isGreatest_meyerSharpPositiveIdeal`.
- **M-06 (Signed Coalescent Surplus Control in `TransThresholdPairCorrelation`):** Test whether signed Ramanujan–Dirichlet lobe cancellation + additive shift structure controls `oddEvenShiftPrimeCoalescentSurplus` across `η ∈ (0, 1/3)` without hitting the Bombieri–Friedlander–Iwaniec parity barrier.
