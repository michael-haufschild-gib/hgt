# Strategic review of the RH research programme

**Reviewer:** Opus · **Date:** 19 October 2026 · **Status of RH:** open

## Scope and sources

The following documents were read in full:

- [`rh-current-frontier-map.md`](../rh-current-frontier-map.md) (all 678 lines: 27 live routes, 18 candidates, shared constraints)
- [`hard-obstacles-summary-1810.md`](../hard-obstacles-summary-1810.md)
- [`arithmetic-positivity-theory/README.md`](../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/README.md)
- [`BiScaleUncertainty/README.md`](../../../formal/GaloisForLFunctions/BiScaleUncertainty/README.md)
- [`TransHorizonIncidenceMechanics/README.md`](../../../formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/README.md)
- [`BezoutValuationIncidence/README.md`](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/README.md)

No other markdown file was opened. Every other fact below comes from Lean source, the corpus search tool or import scans, or from published mathematics; Appendix A lists them. Statements about external literature are standard results quoted from memory. The appendix marks each as such. They were not re-verified in this review.

---

## 0. Conclusions in brief

1. **No open target has been reduced to anything weaker than RH.**
   - Every "Open" line in the ledger is equivalent to RH or implies it outright.
   - The relaxations the programmes treat as easier are just as hard, and are themselves famous open problems:
     - **PM/BVI.** A uniform bound at one fixed damping ε is already a zero-free half-plane (§2.1). This was verified in Lean.
   - Nothing proved so far comes with a progress measure.
2. **The work mostly concerns observation, not cancellation.**
   - The four programmes produce exact identities, sharp finite constants, recovery and conditioning laws, and positivity on restricted families.
   - Each of these restates the problem with the same difficulty. None produces a signed estimate at the critical scale.
   - The ledger records this itself:
     - 179 "Established [L], auxiliary" entries against 92 unqualified ones;
     - 67 explicit "no … follows" disclaimers;
     - 41 phrases stating equivalence with RH.
3. **The 27 live routes come down to about two problems.**
   - Every positivity route leaves the same unpaid term: the signed prime−polar pairing.
   - That pairing is the Chebyshev error ψ(x)−x at the critical scale, which is exactly the WL/MC target.
4. **RH sits on a "square-root threshold".**
   - A rigorous lattice theorem in the corpus, combined with the mean value theorem for Dirichlet polynomials, gives this picture (heuristic outside the lattice model). Dense off-line configurations near height T become visible to the explicit formula only when the prime sum is longer than about T.
   - That length is exactly where mean-value (diagonal) control of a prime sum ends. Below it, only averaged information is available.
   - None of the four programmes is organized around the height T. They are organized around the cutoff N, which is the Fourier-dual variable.
5. **BVI and THIM work entirely inside the parity limitation of sieve theory.**
   - Their objects are truncated divisor sums with divisors at most N. Beyond the horizon, the signed remainder is the Möbius sum itself.
   - Selberg's parity principle says divisor-sum (Type I) information cannot decide its sign. A bilinear (Type II) input is needed, and none is used.
6. **The four programmes are cut off from the only machinery in mathematics known to produce unconditional signed arithmetic estimates.**
   - The corpus holds about 800 modules of classical analytic number theory in `RHTower/Sieve/`. They include Vinogradov–Korobov, zero-density estimates, the large sieve, Halász, Type II estimates and large values.
   - Of the 808 programme files, exactly one imports a classical analytic estimate. APT imports none.
   - BVI's one cofinal cancellation theorem obtains its cancellation from the imported prime number theorem.
7. **What mathematics lacks** (§3.2):
   - a mechanism that excludes zeros from a fixed half-plane;
   - a parity-breaking estimate with a power saving;
   - control of the zero configuration at every height rather than on average;
   - a structural positivity for Spec ℤ (an analogue of the Hodge index theorem);
   - an amplification tower (an analogue of 𝔽_{q^n}).

   No known method over ℚ meets the first three requirements simultaneously, and RH needs all three.
8. **Recommendation.**
   - Do not start another umbrella of identities.
   - Introduce one narrowly defined new programme, the **Square-Root Threshold programme (SRT)**. It studies localized explicit formulas at the resolution of the zero spacing. Its first theorems are within reach: a visibility law, a no-go theorem for diagonal-only methods, and positivity at large aperture for almost every height window.
   - Impose a calibration rule on all four programmes (§4.5).

---

## 1. What has been built

| Quantity | Value | Source |
|---|---|---|
| Lean files in the four programmes | APT 50, BiScale 536, BVI 127, THIM 95 (808 total) | file count |
| Distinct modules of each programme cited in the ledger | B 319, V 121, T 56, A 34; RHTower 412 | ledger scan |
| Ledger entries marked "Established [L], auxiliary" | 179 | ledger scan |
| Ledger entries marked "Established [L]:" without the auxiliary tag | 92 | ledger scan |
| Phrases of the form "RH-equivalent", "iff RH", "RH ⇔" | 41 | ledger scan |
| Phrases "premise" / "implies RH" | 34 | ledger scan |
| Explicit "no … follows" / "does not …" disclaimers | 67 | ledger scan |
| Files in `RHTower/Sieve/` | 3001, about 792 of them in the families Vinogradov, large sieve, Halász, Type II, Maynard, Matomäki–Teräväinen, Vaughan, zero density, Bombieri, Barban, Levinson, Selberg | file scan |
| Programme files importing *any* `RHTower.Sieve` module | 20 of 808 | import scan |
| Programme files importing a classical analytic estimate (VK, large sieve, Halász, Type II, large values, mean value theorem, zero density, Kuznetsov) | **1** (`BiScaleUncertainty/HighFrequencyLaplaceEnergyMeanValue.lean`, mean value theorem) | import scan |

These numbers show that the formal output is real and large. They also show its character. Most of the output consists of reformulations, finite classifications, obstructions and identities. The analytic engines that produce unconditional cancellation exist in the same repository but are not connected to these four programmes.

---

## 2. Why no hard obstacle has moved

### 2.1 Every open target is already at full height

A reformulation is progress only if the new target is strictly easier and can be reached by some identifiable mechanism. Each route has a natural *graded* form: a parameter which, at one end, is a known theorem and, at the other end, is RH. The relevant fact is how far along that scale current mathematics reaches.

| Route (programme) | Graded form | RH at | What the intermediate values mean | Best unconditional value |
|---|---|---|---|---|
| PM / FZZ-P (BVI, THIM) | Uniform energy bound at fixed damping ε | ε ↓ 0 | **No zeros with Re ρ > ½+ε.** The Mellin transform of the source is `(1−2^(1−s))ζ(s)/(sζ(s+ε))` (`RHTower/PMPowerDampedMobiusMellin.lean`, docstring). Fixed-ε admission gives analyticity on Re s > ½ (`BiScaleUncertainty/RoutePMVarianceToWitnessSynthesisAndCriticalStripBridge.lean`), hence a zero-free half-plane. | ε ≥ ½ only (`pmPowerDampedFermiSource_half_le_memLp_and_analytic_mellin`), which is the trivial half-plane Re s > 1 |
| CTF / Nyman–Beurling | L^p ladder | p = 2 | No zero with 1−1/p < Re ρ < 1 (`RHTower/FermiNymanBeurlingWitnessSignature.lean`, `no_zeta_zero_of_fermiNymanWitnessLp_selfSimilar`) | only the limit p → ∞ |
| WL, MC | One-sided bound O(x^θ) for the Chebyshev deficit or the Mertens sum | θ = ½ | No zeros with Re ρ > θ (Landau) | θ = 1 with Vinogradov–Korobov saving (`RHTower/Sieve/VinogradovKorobovMoebius.lean`, `sum_moebius_isBigO_vinogradovKorobov`) |
| LA (heat flow) | de Bruijn–Newman constant Λ ≤ λ | λ = 0 | Off-line zeros give the lower bound Λ ≥ κ₀(δ)/log Im ρ (`RHTower/XiSliceKKLScaleOffLineDetection.lean`) | `newmanConstant_le : newmanConstant ≤ 1/8` (corpus normalization) |
| Weil-positivity cluster (RW, EWU, OWU, CHMD, PBAP; APT, BiScale) | Support aperture a of the test | a → ∞ | Frequency resolution about π/a (see §2.4). This is not a height cutoff. | small apertures only (EWU: blind minimum ≥ 1/20 for a ≤ (log 2+1/50)/2) |

**Consequence.** No zero-free half-plane Re s > σ is known for any σ < 1. Those half-plane statements are the "quasi-Riemann hypotheses", open since 1859. Hence the fixed-ε target of PM/BVI, any L^p rung with 2 < p < ∞, and any one-sided bound with θ < 1 are each beyond all known mathematics.

The obstacles summary says in §3.1 that the PM constant B_ε "may diverge as ε↓0", as if the fixed-ε target were easier. That is accurate as a statement about quantifiers. It is misleading as a statement about difficulty: **at every fixed ε ∈ (0,½) the target is a zero-free half-plane.** It should be recorded as a correction.

### 2.2 Exact identities preserve the difficulty; observation is not cancellation

Exact identities are isomorphisms of the problem. A sharp finite constant describes how much information a set of observations contains. It does not bound the arithmetic signal.

The work on this card's sibling, the dyadic-antichain prime-capacity theorem (finished today), is an archetype. It is a sharp, complete classification of when the selected Fermi trace controls the sieve energy on a support class. Mathematically it is a statement about observation geometry. It contains no information about the size of ∑μ.

The ledger's BVI, THIM and BiScale entries are dominated by the same type of result:

- phase-recovery orders (0/4/6);
- totient observability thresholds;
- five-mode polytopes;
- optimal conditioning (4/π²)(log₂N)²;
- closed-cycle observation orders ⌊T⌋+1;
- collar coefficient asymptotics.

The obstacles summary already states, in §1.6, that arithmetic recovery of finite data is not exclusion of zeros. The programmes have not yet acted on that.

### 2.3 Positivity of one component: the routes collapse to two problems

APT's README puts it precisely: one cannot apply Cauchy–Schwarz to the Weil form before knowing it is positive. In every positivity route the positive pieces are proved and the same term is left unpaid. The positive pieces are Markov energy, prime-chain variance, archimedean Lévy energy, collar coefficients, and factorial-span diagonals.

**The unpaid term is the signed prime−polar pairing** ∑Λ(n)n^(−½)h(log n) − ∫2cosh(x/2)h(x)dx. The ledger states, under WL, that this pairing equals a Chebyshev-error gauge (`B:HyperbolicGaugeChebyshevEnergyRepresentation`, `B:SignedPrimePolarHalfLineTransport`).

Hence RW, EWU, OWU, CHMD, PBAP, TT and the APT/BiScale producers all reduce to the WL/MC problem: one-sided control of ψ(x)−x at the scale √x. Classically that problem is equivalent to Weil positivity. The 27 live routes are therefore essentially **two equivalent problems in many coordinate systems**:

- (P1) a one-sided square-root bound for the prime or Möbius error;
- (P2) positivity of the Weil form at all apertures.

More coordinate systems do not move either problem.

### 2.4 The square-root threshold

The corpus contains a rigorous model computation that locates the difficulty.

- **Lattice visibility law.** `RHTower/ZeroLatticeDepthNyquistLaw.lean`, `offLineLattice_weil_positive_iff`: for an off-line lattice pair with ordinate spacing 2π/L and **any** depth 0 < δ ≤ ½, the Weil form is nonnegative on all C² tests supported in [−a,a] **if and only if a ≤ L/2**. The threshold does not depend on the depth.
- **Mean value theorem.** A Dirichlet polynomial of length N, averaged over t ∈ [T,2T], has mean square (T+O(N))∑|bₙ|². The diagonal term dominates exactly when N ≪ T. The corpus has this as `RHTower/Sieve/DirichletMVT.lean`, `dirichlet_meanValue_theorem`.

Zeros near height T have spacing about 2π/log(T/2π). A test of aperture a reads primes up to e^{2a}. For off-line configurations as dense as the true zeros, the lattice law requires a ≳ ½ log T, that is, **prime sums of length ≳ T**. **This is exactly where diagonal mean-value control ends.**

For sparse or isolated off-line zeros a shorter aperture can suffice. In that case, however, the information sits in short Dirichlet polynomials evaluated at one height. By the Kronecker–Bohr phase freedom, short prime polynomials take every phase pattern at suitable heights; this is the content of the BAG route and of Bagchi's recurrence criterion.

This gives the following dichotomy, rigorous in the lattice model and heuristic in general:

> Information about an individual off-line zero at height T is carried either by prime sums longer than about T, beyond the diagonal regime, or by values at a single height of short prime sums, where averaged estimates say nothing and phase freedom rules out uniform bounds.

Every unconditional estimate in the corpus's sieve library is diagonal or averaged. This is the precise reason why density theorems, proportion theorems and mean-square bounds never exclude a single zero.

### 2.5 The parity limitation of BVI and THIM

BVI and THIM study s_{N,c}(k) = ∑_{d|k, d≤N} c(d). The obstacles summary records that the trans-horizon source is the Möbius function itself: s_{N,μ}(k) = −μ(k) for N < k ≤ 2N. Bounding the complete trans-horizon energy is therefore a problem about sums of μ.

Selberg's parity principle states that sieve information of divisor-sum type cannot distinguish an integer with an even number of prime factors from one with an odd number. It is a standard principle with rigorous versions for specific sieve setups, for example Selberg's example built on Liouville's λ.

The ledger shows the symptoms:

- fixed-linear-horizon source laws are **symmetric** probability laws (`V:CofinalMobiusSourceValueLaw`);
- the variance–covariance cone is sharp, so no stronger universal two-moment inequality exists (`V:ExactSuccessorMomentRegionAndUniversalInequalities`);
- the first-octave target *is* the Mertens target (`V:PowerSavingIncrementCriterion`).

BVI's additive input is gcd(n, n+1) = 1. It is combinatorial and still of Type I. Every known parity-breaking estimate (Vinogradov, Bombieri, Friedlander–Iwaniec, Heath-Brown, Matomäki–Radziwiłł) uses **bilinear (Type II) structure**. BVI and THIM use none.

Further, BVI's one cofinal cancellation theorem obtains its cancellation from the prime number theorem. `BezoutValuationIncidence/UniformCofinalMobiusPrefixDiscrepancy.lean` imports `PNTPlus.Consequences`, and the classical o(N) theorem (`RHTower/Sieve/MoebiusSharpLittleO.lean`) is a contour argument through the zero-free region.

### 2.6 Countermodels are acknowledged, but not used as a test bench

Each of the following satisfies part of ζ's structure and has off-line zeros:

- **Beurling generalized integers.** By the Diamond–Montgomery–Vorhauer construction [lit], the de la Vallée Poussin zero-free region is optimal for Beurling systems. Any argument that uses only multiplicative structure, Λ ≥ 0 and regular integer counting cannot do better than de la Vallée Poussin.
- **Davenport–Heilbronn type series.** These have a functional equation but no Euler product.
- **ζ(s−a)ζ(s+a).** This has an Euler product and a functional equation but the wrong poles and Gamma factors; it appears in the ledger's shared constraints.
- **Zeta23 lattice configurations.**

The corpus has formal objects for all of them: `RHTower/BeurlingSystem*` with `beurlingCountermodel_zero_im_pos`, `davenportHeilbronnFakeCoeff` in `RHTower/EulerProduct.lean`, `NonTemperedShiftedZetaPairCountermodel`, and `Zeta23.ExplicitFormula`.

The READMEs list the Beurling pitfall (BVI pitfall 7, BiScale pitfall 6). Candidate inequalities are not, however, *evaluated* on these models before work is invested in them.

The first known mechanism that separates ζ from the Beurling models with off-line behaviour is the Vinogradov–Korobov exponential-sum input. It exploits the additive smoothness of log(n+h) (Taylor expansion and Weyl differencing). No programme has an ingredient of that type.

### 2.7 Documentation drift found during the review

1. **Invalid target still stated in the THIM README.** It still states the tail target "L²((0,1/N), dx/x²)" in three places: Obstacle 1 in §1.2, Pillar 5, and Frontier item 3. The obstacles summary (§1.1) showed that this target is invalid: the transformed integral diverges unless the periodic function vanishes. It should be replaced by the corrected weak-closure principle (uniform norm bound plus local L² convergence on compact intervals).
2. **Overclaims in the THIM README.** It speaks of "6 Irreducible Uncharted Obstacles" and of pillars that overcome named walls. The obstacles summary says the six families are not proved irreducible and that nothing has been closed.
3. **Overclaim in the BiScale README.** It speaks of "100% unconditional all-scale signed Weil lower bounds", whereas the ledger records that these retain an unpaid node sum.
4. **Missing correction in the obstacles summary.** It should record that the fixed-ε PM target is a quasi-RH half-plane (§2.1).

---

## 3. Question 1 — Which tools are missing?

### 3.1 Tools that exist in mathematics, mostly in our corpus, and are unused by the four programmes

| Tool | What it provides | In the corpus | Used by the four programmes |
|---|---|---|---|
| Zero-density estimates and large values of Dirichlet polynomials (Ingham, Huxley, Heath-Brown, Guth–Maynard [lit]) | Counts of zeros with Re ρ ≥ σ; *averaged* exclusion with explicit exponents | `ZetaZeroDensityInghamHuxley`, `ZetaZeroDensityTwelveFifths`, `ZetaZeroDensityEightThirds`, `ChenGuptaLiZeroDensityExponents`, `Sieve/Maynard*` | no |
| Exponential sums (Weyl, van der Corput, Vinogradov mean value theorem) | Additive-structure input that separates ℤ from Beurling systems | `Sieve/VinogradovMeanValueBound`, `Sieve/VinogradovKorobovZeroFree`, `Sieve/VinogradovKorobovMoebius` | no |
| Bilinear decompositions (Vaughan, Heath-Brown), Halász, Matomäki–Radziwiłł / Matomäki–Teräväinen | Parity-breaking Type II estimates | `Sieve/VaughanTypeIIEstimate`, `Sieve/Halasz*`, `Sieve/MatomakiTeravainen*` | no |
| Large sieve; spectral (Kuznetsov) large sieve | Bounds beyond the square-root threshold *for structured coefficients* | `Sieve/LargeSieveWeak`, `KuznetsovLargeSieve*` | no |
| Mollified moments (Levinson, Conrey) | Proportions of zeros on the line; the known crossing of the square-root threshold via Kloosterman sums | present in `RHTower` | no |
| Graded receivers (Landau, Beurling L^p, de Bruijn–Newman bounds) | Progress measures | present (§2.1) | not used as measures |
| Function-field proofs (Stepanov; Weil and Kloosterman sums) | The only complete templates of an RH proof | `StepanovCount.stepanov_count`, `WeilKloostermanHasseDavenport`, `ConnesFunctionFieldWindow` | no structural use |
| Countermodels | Necessary conditions on any proof | §2.6 | as named pitfalls only |

### 3.2 What mathematics as a whole lacks

These are precise gaps, not slogans. Each is a statement no one has proved.

- **B1. A zero-free half-plane.** Every known exclusion mechanism is either:
  - perturbative near Re s = 1 (de la Vallée Poussin, Vinogradov–Korobov), where the region shrinks with height because bounds for ζ(σ+it) grow with t; or
  - statistical (density, proportions).

  No mechanism gives Re ρ ≤ σ₀ < 1 for all zeros. The Lindelöf hypothesis and the density hypothesis would not give one either.
- **B2. Parity-breaking with a power saving.** Bilinear methods break parity, but for global Möbius sums they save only exp(−c(log x)^{3/5−o(1)}). Matomäki–Radziwiłł saves in almost all short intervals and only by o(1). A bound ∑_{n≤x}μ(n) = O(x^{1−η}) for some η > 0 would itself be a quasi-RH (B1).
- **B3. Control at every height.** Everything unconditional about zeros near the critical line holds on average over the height: density, proportions, pair correlation in the diagonal range. Excluding one zero requires a statement about every height. Over function fields this comes from finite-dimensional cohomology: finitely many zeros, Riemann–Roch, Frobenius.
- **B4. A structural positivity for Spec ℤ.** Weil's proof for curves rests on positivity of the intersection pairing on the surface C×C (Castelnuovo–Severi, the Hodge index theorem). The analogue over ℚ is the arithmetic site or adelic cohomology with a Hodge-type pairing (Connes–Consani, Deninger), and it is conjectural. The corpus's HF route builds realizations (Meyer quotient, Paugam pairing, Fredholm determinant equal to Ξ). A realization supplies no positivity.
- **B5. An amplification tower.** Deligne's proof deduces the sharp bound |α| ≤ q^{w/2} from weak bounds that are uniform under tensor powers and extensions 𝔽_{q^n}. There is no known family attached to ζ alone in which its zeros recur with amplified weight and weak bounds hold uniformly.

The following table is an organizing assessment, not a theorem: every result over ℚ falls short on at least one of A, B, C.

| Requirement | A: fixed half-plane or depth | B: every height | C: prime-weighted control beyond the square-root/parity threshold |
|---|---|---|---|
| de la Vallée Poussin / Vinogradov–Korobov zero-free region | no (shrinks) | yes | partial (exponential sums for ζ, not the sign of μ) |
| Zero-density estimates | yes | no (counts) | no (diagonal plus additive energy) |
| Proportions on the line (Selberg, Levinson, Conrey) | — | no | yes, for mollified ζ through Kloosterman sums, not for Λ |
| Matomäki–Radziwiłł | no | no (almost all intervals) | yes (Type II) |
| Function-field RH (Weil, Stepanov, Deligne) | yes | yes | yes, through Frobenius and cohomology |
| **What any route of ours requires after calibration** | **yes** | **yes** | **yes** |

The programmes' targets demand A ∧ B ∧ C. Only the function-field proofs achieve all three. They do so through structure (Frobenius, finite-dimensional cohomology, positivity of intersection) that has no counterpart in any of the four programmes.

---

## 4. Question 2 — What each programme should research next

Each subsection gives three things:

- **Keep:** assets worth retaining;
- **Stop:** lines whose output the ledger already shows to be nonselective or archimedean only;
- **Next:** ordered problems, each with a first milestone and a calibration requirement.

### 4.1 Arithmetic Positivity Theory (APT)

**Keep.**
- The relative perturbation calculus: the zero-side majorant 𝒵 and the sharp threshold ε < (√(1+δ)−1)².
- The exact Weil formulas for factorial tails.
- The Schur-complement bookkeeping.

These are correct tools for comparing *different* sources.

**Stop.** New restricted families whose positivity comes from archimedean growth: factorial spans, ramp–tent spans, Müntz repairs. The ledger records this family as positive without RH ("nonselective") at least ten times.

**Next.**
1. **A selectivity criterion as a theorem.**
   - Positivity of the Weil form on a family F carries information about zeros only if, near each height T, F contains tests that resolve the local zero spacing.
   - Prove that every family with a bounded resolution scale is compatible with off-line lattice configurations whose spacing is below π/a(F). Use `Zeta23` and `offLineLattice_weil_positive_iff`.
   - *Milestone:* a single theorem explaining all of the factorial-family nonselectivity results.
2. **Height-localized Weil forms.**
   - Define modulated tests f_T(u) = g(u)e^{iTu} with aperture a = α log T.
   - Prove the localized explicit formula, with the prime side written as a Dirichlet polynomial of length e^{2a} evaluated near height T.
   - This is the representation in which the square-root threshold (§2.4) becomes visible.
3. **Positivity for almost every window.**
   - From the corpus's Ingham–Huxley theorem (`exists_zeroHeightBox_ncard_le_ingham_huxley`), prove that the localized Weil form is nonnegative for every T ∈ [T₀, 2T₀] outside an exceptional set of measure ≪ T₀^{1−c(α)}, with an explicit exponent.
   - *Calibration:* this would be the first unconditional positivity statement at aperture comparable to log T. Every later improvement of a density exponent would transfer to it directly.
4. **The critical envelope β = ½.** README topic 4 should be revisited only after item 2, in the localized setting.

### 4.2 BiScale Uncertainty

**Keep.**
- Origin concentration and compactness of the infinite grid (`InfiniteGridOriginConcentration`, `InfiniteGridStrictEnergyLoss`, `SignedGridTraceCompactness`).
- The distant-copy polar construction (`DistantCopyPolarEnforcement`).
- The packet Plancherel identity (`PacketEnergyPlancherel`).
- Producer–consumer duality as a Hilbert-space tool.

**Stop.**
- Collar-coefficient asymptotics, cap and activation hierarchies, Schur-capped ladders.
- Finite-grid optimization.
- Variations on cycle and observation orders.

The ledger annotates these dozens of times as "archimedean, not signed prime−polar payment".

**Next.**
1. **A profile decomposition for the blind-minimum problems.**
   - Prove a concentration–compactness theorem: a minimizing sequence for the even or odd blind minimum at aperture a either converges, with the minimizer equal to the ground state that OWU/EWU already realize, or splits into profiles whose energies are explicitly archimedean. The profiles are origin concentration, distant polar copies and increasing oscillation.
   - The obstacles summary names this as a research target (§3.3), and the ingredients are in the corpus.
   - *Payoff:* the blind minimum is already antitone in a (EWU). The problem "first aperture at which the minimum reaches zero" then becomes a well-posed eigenvalue-crossing problem for an attained ground state.
2. **Bounds on the spectral density of the source.**
   - The identity ∫|𝓕f|²(¼+4π²ξ²)S_N(ξ)dξ reduces packet energy to S_N, the spectral density of the truncated prime sum.
   - Bound S_N on average with the corpus's mean value theorem and large-values estimates (`Sieve/DirichletMVT*`, `Sieve/Maynard*`).
   - *Milestone:* the first BiScale theorem that consumes a classical analytic estimate, giving packet-energy bounds whose exponents are tied to density exponents.
3. **Apply the bi-scale uncertainty principle to the source, not the tests.**
   - The README's central idea — the logarithmic grid versus additive structure — has so far constrained only test functions.
   - Formulate and prove a native version of the classical uncertainty statement for Λ, namely Littlewood's and Ingham's Ω±(√x) results for ψ(x)−x.
   - *Calibration:* reproducing an unconditional Ω± theorem shows that the machinery sees the critical scale √x at all.

### 4.3 Bézout–Valuation Incidence (BVI)

**Keep.**
- The finite sieve algebra in Selberg coordinates and the polytopes, as a library.
- The pronic Gram splitting 𝒢 = ΛΛᵀ + 𝒢^ec.
- The renormalized-defect identities.
- The exact first-octave formulas.

**Stop.**
- Further moment-recovery orders, observability thresholds, polytopes and magnitude laws.
- Limit laws at a fixed linear horizon; these are symmetric in sign by the parity principle.
- Compensated O_ε(1) remainders at fixed ε (§2.1: fixed ε is a quasi-RH).

**Next.**
1. **Calibration.**
   - Determine whether any BVI-native argument yields even ∑_{n≤x}μ(n) = o(x). At present this is imported from the prime number theorem.
   - If the answer is no, prove the negative statement: BVI's identities hold verbatim for a Beurling system whose prime number theorem fails. This is a countermodel test using the corpus `BeurlingSystem`.
   - *Milestone:* a native theorem, or a documented proof that BVI's mechanism carries no cancellation.
2. **A Type II decomposition of the complete trans-horizon remainder.**
   - Rewrite the log-renormalized complete PM/BVI remainder through Vaughan's or Heath-Brown's identity.
   - Handle the Type I part with BVI algebra and the Type II bilinear forms with the corpus's existing estimates (`Sieve/VaughanTypeIIEstimate`, `Sieve/MatomakiTeravainen*`, `Sieve/Halasz*`).
   - *Milestone:* the first cofinal *signed* bound with a nontrivial saving. Expect only a saving of de la Vallée Poussin / Vinogradov–Korobov shape, and calibrate against it.
3. **A parity diagnostic.**
   - Prove that the finite quadratic invariants BVI uses (all forms in Selberg coordinates built from data with level ≤ N) take identical or indistinguishable values on μ and on a parity-modified multiplicative model (Selberg's (1 ± λ) weights).
   - *Positive survivor:* the minimal bilinear input that separates the two models.

### 4.4 Trans-Horizon Incidence Mechanics (THIM)

**Keep.**
- The exact transfer between discrete sieve energies and continuous Weil/CHMD forms: prime chains ↔ sieve energies, Fermi cells ↔ pronic energies.
- Coordinates on the quotient by the signed radical.

This transfer layer is THIM's genuine asset.

**Stop or correct.**
- The README targets and overclaims listed in §2.7.
- Fermi observability and conditioning packages; the dyadic-antichain card is complete and should be treated as finished infrastructure.
- Proliferation of identities for odd eigenvectors without a sign input.

**Next.**
1. **Transport graded statements into CHMD.**
   - CHMD has a dimension formula: (q, q+1, 2q+1) bound states for q off-line zeros, when off-line zeros are finite.
   - Prove a bound of the shape: the number of odd bound states with spectral parameter ≥ ½+η, and readout localized at height ≤ T, is ≤ C·N(σ(η), T).
   - Combined with the corpus density theorems, this gives CHMD its first measurable unconditional quantity.
2. **Decide the absorption condition.**
   - Determine, by a concrete calculus computation, whether coshSinhPolarRatio(a, M, R) ≤ θ ≤ 1 is attainable for any nonzero admissible w at the actual parameters.
   - *Milestone:* either a witness or a no-go theorem. The answer settles whether the mechanism of `CollectiveLowPrimeChebyshevTransportAndSinhAbsorption` can apply at all.
3. **Serve as the discrete side of the new SRT programme (§5).** Fermi and pronic cells are Dirichlet-polynomial coefficients. THIM should provide the exact discrete counterpart of the localized explicit formula at height T.

### 4.5 Rules across programmes

1. **Calibration.** Every new card states:
   - its graded parameter;
   - the strongest unconditional value of that parameter in mathematics;
   - whether the programme's own machinery reproduces that value.

   A mechanism that cannot reproduce de la Vallée Poussin-strength information is not a candidate for RH.
2. **Countermodel evaluation.** Before formalizing a candidate inequality, evaluate it on the Beurling, Davenport–Heilbronn, shifted-product and Zeta23 models.
   - An inequality that holds on a model with off-line zeros cannot imply RH.
   - A proof that uses only axioms satisfied by such a model cannot prove RH.
3. **Classical tools first.** Before building an elementary substitute, search `RHTower/Sieve` (about 800 modules in the relevant families) for the analytic estimate.
4. **Accounting.** Observation, recovery and conditioning results count as infrastructure, not progress on the sign. This matches the stored user directive that every turn work directly on the hard inequality.

---

## 5. Question 3 — Is a new programme needed?

**Yes, one, defined narrowly.**

The diagnosis shows a representation gap. The four programmes are organized around the cutoff or horizon N and the scale log n. The difficulty sits at the height T and at the resolution of the zero spacing there, which is the Fourier-dual variable. No existing programme states its problems at a given height. Another umbrella of identities would repeat THIM's remit, as the obstacles summary already warns.

### The Square-Root Threshold programme (SRT): localized explicit formulas at the resolution of the zero spacing

**Central question.** At height T, which unconditional mechanisms control the explicit formula at the resolution of the local zero spacing? What additional arithmetic information would make the localized Weil form nonnegative at *every* height?

**Why it is new.** The classical literature has the ingredients: zero-indicating Dirichlet polynomials (Turán, Montgomery), mean value theorems, Montgomery's pair correlation, and Goldston–Montgomery. It does not organize them as a theory of where, in the explicit formula, the information about an individual off-line zero sits, with matching no-go and positive theorems. The corpus's lattice visibility law is an original first instance.

**Research questions, with first theorems.**

- **SRT-1 · Visibility law** (theorem target).
  - Extend `offLineLattice_weil_positive_iff` from lattices to configurations of local density (log T)/2π.
  - Determine the minimal aperture at which a localized test makes the Weil form negative, as a function of the depth and local spacing of the off-line configuration.
  - *Expected shape:* aperture about ½ log T, that is prime support about T, for configurations as dense as the true zeros; less for isolated zeros. The isolated case is to be proved or refuted.
- **SRT-2 · Insensitivity of diagonal methods** (no-go target).
  - Construct abstract zero configurations in the Zeta23 framework, with one off-line pair in every dyadic height block.
  - Show that they reproduce all diagonal mean-value data, and every presently known large-values and density bound, of the true explicit formula for prime sums up to length T^{1−η}.
  - This rigorously excludes every proof that uses only diagonal information.
  - *Positive survivor:* the exact off-diagonal quantity that distinguishes the configurations.
- **SRT-3 · Positivity for almost every window** (positive target, within reach).
  - From the corpus density theorems, prove nonnegativity of the localized Weil form at aperture α log T for all heights outside an exceptional set with an explicit exponent (shared with APT item 2).
  - This would be the first unconditional positivity theorem at large aperture.
- **SRT-4 · Structure of the off-diagonal terms** (research frontier).
  - The terms n ≠ m with |log(n/m)| ≲ 1/T are shifted sums.
  - With Λ as source they are prime-pair correlations, blocked by parity.
  - With mollified ζ as source (Levinson's representation) they are shifted divisor convolutions. Kloosterman and spectral methods handle these (Conrey's θ = 4/7 used Deshouillers–Iwaniec [lit]; the corpus has the Kuznetsov large sieve).
  - *Milestone:* reproduce a mollifier range θ > ½ in the language of localized Weil forms, as a calibration of the one known way across the threshold. Then determine how far that representation can be pushed toward pointwise control.
- **SRT-5 · The pointwise problem** (where new mathematics must be invented).
  - Prove the precise Kronecker–Bohr statement: for every finite set of primes and every phase pattern, there are heights at which the part of the localized form coming from those primes is as negative as the trivial bound.
  - Hence pointwise positivity must come from the coupling, through the functional equation, between finitely many primes and the infinite tail.
  - Formulate the minimal global inequality that expresses this coupling. Relate it to Bagchi's recurrence criterion (BAG).
  - This is the stated object of invention for the programme. B1–B3 of §3.2 meet here.

**What the programme yields even if RH is not reached.**
- SRT-1 and SRT-3 are new theorems.
- SRT-2 is a rigorous necessary condition on any proof.
- SRT-4 measures how far the only known threshold-crossing technology reaches.

If SRT-5 fails, the failure is recorded as a no-go together with its strongest positive survivor, as the project's closure discipline requires.

**Interfaces.**
- APT supplies relative-perturbation tools.
- BiScale supplies profile decomposition and spectral-density bounds.
- THIM supplies the discrete localized formula.
- BVI supplies the Type II reformulation of the Möbius side.
- `RHTower/Sieve` supplies the analytic estimates.

**What not to start now.** An "arithmetic amplification" programme, seeking a tower over ℚ analogous to 𝔽_{q^n} (gap B5), is the long-range alternative. It should begin only once it has a falsifiable first statement. A candidate is the aperture-amplification question:

> Is there a positivity-preserving operation on arithmetic tests that maps aperture-a positivity to aperture-ca positivity with c > 1?

Small-aperture positivity is already proved, so such an operation would make positivity propagate to every aperture. Deciding whether one can exist is a well-posed first problem.

---

## 6. Prioritized next steps

| # | Action | Programme | Type |
|---|---|---|---|
| 1 | Correct the THIM README tail target and overclaims, the BiScale "100%" wording, and the obstacles summary's fixed-ε statement (§2.7) | THIM, BiScale, docs | correction |
| 2 | Adopt the calibration and countermodel rules (§4.5) for every new card | all | process |
| 3 | SRT-1: visibility law beyond lattices | SRT (APT/THIM) | theorem |
| 4 | SRT-3 / APT-3: positivity for almost every window from Ingham–Huxley | SRT, APT | theorem |
| 5 | BVI-2: Type II decomposition of the complete trans-horizon remainder, calibrated against Vinogradov–Korobov | BVI | theorem |
| 6 | BVI-3: parity diagnostic theorem for BVI's finite invariants | BVI | no-go plus survivor |
| 7 | BiScale-1: profile decomposition for the blind-minimum problems | BiScale | theorem |
| 8 | THIM-2: decide attainability of the sinh-absorption condition | THIM | witness or no-go |
| 9 | SRT-2: insensitivity of diagonal methods (Zeta23 configurations) | SRT | no-go |
| 10 | SRT-4 and SRT-5: off-diagonal structure and the global coupling inequality | SRT | research frontier |

---

## Appendix A — Evidence log

**Searches with `scripts/formal_tools.py research`, lexical or hybrid, `--any`.** Queries:

- "sieveSeq congr coefficients agree Icc horizon"
- "two_pow_mul_odd equiv bijective"
- "ordCompl odd part …"
- "Beurling countermodel offline zero"
- "Davenport Heilbronn"
- "zero density estimate"
- "Vinogradov Korobov zero free region"
- "large sieve inequality"
- "Montgomery Vaughan mean value Dirichlet polynomial"
- "Matomaki Radziwill"
- "Halasz"
- "Vaughan identity type II bilinear"
- "Guth Maynard large values"
- "BeurlingSystem"
- "Stepanov finite field curve Riemann hypothesis"
- "parity problem sieve"
- "de Bruijn Newman constant"
- "Vinogradov mean value decoupling"
- "Selberg class"
- "Zeta23Countermodel" (0 hits)
- "tensor power trick amplification"
- "aperture positivity zero free region"
- "Connes function field window"
- "Yoshida Weil functional small support"
- "Diamond Montgomery Vorhauer" (no relevant hit)
- "newmanConstant le half"
- "Beurling Lp Nyman density zero free half plane"

A deep query "unconditional zero-free region implies Weil quadratic form positive for test functions of bounded support aperture" found no theorem converting a zero-free region into aperture positivity. It surfaced `offLineLattice_weil_positive_iff`.

**Lean source read.**
- `RHTower/ZeroLatticeDepthNyquistLaw.lean`: header and the statement of `offLineLattice_weil_positive_iff`.
- `RHTower/StepanovCount.lean`: header and `stepanov_count`.
- `RHTower/DeBruijnNewmanConstant.lean`: `newmanConstant_le`.
- `RHTower/PMPowerDampedMobiusMellin.lean`: header, the Mellin formula `(1−2^(1−s))ζ(s)/(sζ(s+ε))`.
- `BiScaleUncertainty/RoutePMVarianceToWitnessSynthesisAndCriticalStripBridge.lean`, lines 1–110: fixed-ε admission implies Mellin analyticity on Re s > ½.
- `BezoutValuationIncidence/UniformCofinalMobiusPrefixDiscrepancy.lean`: imports, including `PNTPlus.Consequences`.
- `RHTower/Sieve/MoebiusSharpLittleO.lean`: header, the contour argument through the zero-free region.

**Import scans.** These cover the four programme directories against `RHTower.Sieve`, and against the families VK, Vinogradov, large sieve, Halász, Type II, Maynard, Matomäki–Teräväinen, Vaughan, mean value theorem, zero density and Kuznetsov. Result: 20 files import some Sieve module; one file imports a classical analytic estimate. The counts in §1 come from directory listings and ledger scans.

**External literature cited, standard results quoted from memory [lit], not re-verified in this review.**
- Landau's theorem on Dirichlet integrals with one-signed coefficients.
- Beurling (1955), L^p density of the Nyman–Beurling span.
- Diamond–Montgomery–Vorhauer (2006), Beurling primes with large oscillation.
- Selberg's parity principle.
- Vinogradov–Korobov.
- Guth–Maynard (2024), large values of Dirichlet polynomials.
- Conrey (1989), more than two fifths of the zeros on the line, using Deshouillers–Iwaniec.
- Zhang (2013), level of distribution beyond ½ using Deligne's bounds.
- Rodgers–Tao (2018), Λ ≥ 0.
- Weil, Stepanov–Bombieri and Deligne, proofs of RH over finite fields.
