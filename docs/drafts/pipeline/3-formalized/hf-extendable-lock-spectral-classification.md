# Extendable producer locks: spectral identity and classification

- **ID:** hf-extendable-lock-spectral-classification
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Opus loop rows 2081–2088 (`1-in-progress/rh-goal-loop-opus-2026-09-29.md`); STATUS MUST-949–954; `bohr-route-detection.md` rows 91–95
- **Statement:** Let `G` be a Herglotz producer, and suppose its lower-line lock factor `G(1−s)/(κ₀G(s)) = e^{L(s)}` extends holomorphically to the lower region with `Re L` bounded above. Then `κ₀ Σ_{n≥1} a(n) n^{−3/2} A_L(n) = G(1)`, where `A_L(n)` is the edge Abel transform at frequency `log n`. Every lock whose edge Abel spectrum vanishes at the integer frequencies is impossible. This includes decaying twists, density margins and regularly varying phases.

## Goal
This is the uniqueness half (U) of the HF route (RH ⟸ PBAP + U). A second producer (a twin) carries a nonconstant lock phase `θ = 2π·μ([0,x])` (mod 2π) from its non-integer spectral mass. The card classifies the locks whose phase extends holomorphically, and shows which of them can occur: only those with Abel spectrum at the frequencies `log n`. Not an RH proof. It narrows U to non-extendable (atomic, rough) locks and to integer-resonant almost-periodic locks.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure (Herglotz producer + Hamburger reflected limit), attack via contour shift to `Re s = 3/2`
- [x] 1 → 2  fully-proven: paper proofs in loop rows 2083–2088
- [x] 2 → 3  formalized: Lean modules below, `lake build --old` green, `#print axioms` = `[propext, Classical.choice, Quot.sound]`, no heartbeat overrides
- [ ] 3 → 4  not pursued (user directive: no manuscripts)

## Theorem chain (Lean, `RHTower.AbelianTwist`)
| Result | Module | Statement |
|---|---|---|
| MUST-949 | `WeilWindowedLinearLockQuantization` | windowed linear locks force `e^{−η/2} ∈ ℕ` |
| MUST-950 | `WeilEvaporationLockRigidity` | `x log x` phases (constant-rate evaporation) are impossible, also on windows; generic `windowed_lock_impossible_of_tendsto` |
| MUST-951 | `WeilDecayingTwistLockRigidity` | `Re L(3/2+iy) → −∞` (density → ∞) is impossible; perturbed evaporation |
| MUST-952 | `WeilMarginTwistLockRigidity` | density margin `Re L' ≤ −c` and `L'' → 0` are impossible (oscillating densities); model `log_periodic_lock_impossible` |
| MUST-953 | `WeilRegularVariationLockRigidity` (+ `WeilLowerRegionContour`) | `y Re L' → ∞` and `L''/(Re L')² → 0` (densities ≫ 1/x, regularly varying) are impossible, with lower-region regularity only; model `log_density_lock_impossible` (`x/log(x+e)`) |
| MUST-954 | `WeilLockSpectralIdentity`, `WeilLockSpectralSystem` | `κ₀ √m Σ a(n)n^{−3/2}A_L^{(m)}(n) = G(1)` for all `m`; `abel_null_lock_impossible` |
| MUST-1234 | `WeilLockSpectralTwist`, `WeilDirichletLockSpectrum`, `WeilDirichletLockRigidity` | system for any bounded holomorphic twist `V`; for `V = Σ P(k)k^{−(s−½)}`: `A^{(m)}(n) = nP(m/n)`, `F·V = G(1)ζ`, constant lock ⇒ `λ = Λ` ∧ RH (`dirichlet_lock_rigidity`) |
| MUST-1244 | `WeilMixedResonanceLockSpectrum`, `WeilMixedResonanceLockRigidity` | integer-resonant + non-rational AP locks ⇒ `λ = Λ` ∧ RH (`integer_resonant_lock_rigidity`); Bohr means at `±log k` force `P(k) = 0`, `k ≥ 2` |
| MUST-1246 | `WeilRationalCuspLockSpectrum`, `WeilRationalCuspLockRigidity` | one-sided rational resonances (`u > 1`, non-integer) plus integral and irrational frequencies ⇒ `λ = Λ` ∧ RH (`one_sided_rational_lock_rigidity`); real-height limits, unit translation, triangular induction |
| MUST-1247 | `WeilBoundedSpectrumLockRigidity` | spectra with attained extremes (all finite exponential sums) ⇒ `λ = Λ` ∧ RH (`bounded_spectrum_lock_rigidity`); unimodularity plus the extreme Bohr coefficient |
| MUST-1310 | `WeilInnerLockRigidity`, `WeilLowerSpectrumLockRigidity` | locks holomorphic near the lower line and inner to its left ⇒ `λ = Λ` ∧ RH (`inner_lock_rigidity`); AP locks with spectrum in `(0,1]` (`lower_spectrum_lock_rigidity`). Positivity alone: the boundary phase of `G` is monotone, an inner factor's phase runs the other way |
| MUST-1315 | `WeilLockMeanMotionRigidity` | AP locks: Parseval mean motion `Σ\|q_j\|² log ρ_j ≥ 0` (`lock_meanMotion_nonneg`); `≤ 0` ⇒ `λ = Λ` ∧ RH (`lock_meanMotion_rigidity`); palindromic moduli ⇒ trivial (`palindromic_lock_rigidity`) |
| MUST-1322 | `WeilBoundedDenominatorLockConvolution`, `WeilBoundedDenominatorLockPeriodicity` | bounded-denominator AP locks `N^{s−½}Σ P(k)k^{−(s−½)}` (two-sided rational spectrum) force `N`-periodic Dirichlet coefficients (`bounded_denominator_lock_periodic`); Hamburger-type uniqueness from the boundary half-line (`eq_zero_of_vertical_halfLine`) |
| MUST-1327 | `WeilBoundedDenominatorLockRH`, `PeriodicExpProducerSingleCharacter`, `CharacterProductZeroPlanting` (+ HTGeometry `PrimeProgressionReciprocalDivergence`, `PeriodicCharacterDecomposition`, `DirichletExpMultiplicativeTwist`) | bounded-denominator AP locks ⇒ RH (`bounded_denominator_lock_riemannHypothesis`); single-character rigidity of periodic Dirichlet exponentials (`periodic_exp_single_character`); zero planting for two characters (`exists_charProduct_zero`) |

## Approach
Shift the reflected radial integral `ε∫ e^{L} φ k` to `Re s = 3/2` (lower contour; only lower-region regularity is needed). There the edge is a Dirichlet series in `a(n)n^{−s}`, and Hamburger's kernel is `c_τ e^{yκ_τ} + O(e^{πy})`. Each Dirichlet term is a one-dimensional Abel integral at frequency `log n`. Its decay (MUST-951) or its integration by parts under a margin (MUST-952/953) shows that its `ε`-limit vanishes. Tannery's theorem then sums the terms, and Hamburger's reflected limit `2β = G(1) ≠ 0` closes the argument.

## No-go closure (the U obstruction exposed)
- **Exact killing mechanism:** any extendable lock without integer-frequency Abel spectrum.
- **Strongest positive survivor:** the spectral identity (MUST-954). Extendable twins must resonate with the integers, weighted by their own Dirichlet coefficients.
- **New insight:** a density margin alone cannot exclude a lock. Self-resonant densities `ρ ∝ 1 + a cos θ` give periodic locks whose Abel spectrum sits on a lattice, and they escape every margin argument. So the remaining U room is arithmetic: (i) integer-resonant AP locks (the corpus AP and rational-phase theorems cover summable or one-sided cases); (ii) non-extendable locks from fractional atoms on the zeros of ζ (C13, C538), which need cancellation, not analysis of the phase.
- **Status:** all statements above are dependency-closed and formalized.

## Log
- 2026-10-11 — created at stage 3 from loop rows 2081–2088 (MUST-949–954, all Lean, wired into `GaloisForLFunctions.RHTower`).
- 2026-10-11 — MUST-1234: integer-resonant (Dirichlet) locks closed in Lean (`dirichlet_lock_rigidity`, modules `WeilLockSpectralTwist`, `WeilDirichletLockSpectrum`, `WeilDirichletLockRigidity`). The extendable class still open: rational non-integer and mixed AP resonances.
- 2026-10-11 — MUST-1244: mixed AP locks (integral rational resonances plus non-rational frequencies) closed in Lean (`integer_resonant_lock_rigidity`, modules `WeilMixedResonanceLockSpectrum`, `WeilMixedResonanceLockRigidity`). Contour and twist system now need only strip regularity. Open in the AP class: rational non-integer resonances (need positivity).
- 2026-10-11 — MUST-1246: one-sided multifrequency rational locks closed in Lean (`one_sided_rational_lock_rigidity`, modules `WeilRationalCuspLockSpectrum`, `WeilRationalCuspLockRigidity`), via real-height radial limits and unit translation. Only bilateral rational spectra remain in the AP class (they need Herglotz positivity).
- 2026-10-11 — MUST-1247: bounded-spectrum (in particular finite) exponential-sum locks closed (`bounded_spectrum_lock_rigidity`, module `WeilBoundedSpectrumLockRigidity`). Open in the AP class: unbounded two-sided rational spectra.
- 2026-10-12 — MUST-1310: inner locks and spectra below one closed (`inner_lock_rigidity`, `lower_spectrum_lock_rigidity`). This class needs positivity: the non-Herglotz `(1 + c·2^{½−s})ξ` (real `|c| > 1`) has a left-inner lock and satisfies every analytic identity. Open in the AP class: rational frequencies on both sides of `1`, unbounded on some side.
- 2026-10-12 — MUST-1315: mean-motion law. The AP class is now organized by `m = Σ|q_j|² log ρ_j`: positivity gives `m ≥ 0`, `m = 0` is trivial. Open: `m > 0` with two-sided rational spectra.
- 2026-10-12 — MUST-1322: bounded-denominator AP locks force periodic coefficients (`bounded_denominator_lock_periodic`). The open AP class splits: (i) bounded denominators, which reduce to single-character rigidity of periodic producers plus the mean-motion sign `m ≤ 0`; (ii) unbounded denominators.
- 2026-10-12 — MUST-1327: bounded-denominator AP locks force RH (`bounded_denominator_lock_riemannHypothesis`). The almost-periodic class is open only for unbounded denominators.
- 2026-10-13 — **The almost-periodic class is CLOSED.**
  - MUST-1388: rational locks with unbounded denominators force RH (`rationalLock_riemannHypothesis`), under the weight `√den·8^{ω(den)}`.
  - MUST-1391: AP locks with arbitrary real frequencies force RH (`almostPeriodicLock_riemannHypothesis`). Irrational lock points carry no weight (`lockPer_eq_zero_of_irrational`).
  - Supporting results:
    - `apLock_coefficients` (MUST-1387): AP lock ⇒ `a(n) = Σ_{0<m u_j≤1} a(m)c_j√u_j e(n m u_j)`;
    - `limitPeriodic_exp_single_character` (MUST-1383);
    - `limitPeriodic_producer_riemannHypothesis` (MUST-1385).
  - Remaining U room in the extendable/AP classification: none for absolutely convergent AP locks, up to the denominator weight.
  - Open: non-AP non-extendable locks, i.e. step phases from fractional atoms (twins: a real-rooted `F ∈ V_k` gives the producer `s(s−1)Γ_ℝF^{1/k}`, whose lock jumps by `e^{2πi m/k}` at zeros of multiplicity `m ≢ 0 (k)`).
  - The conclusion is RH, not `λ = Λ`. Upgrading to `λ = Λ` would need the mean-motion law (MUST-1315) for the trivial-class factor `A`.
