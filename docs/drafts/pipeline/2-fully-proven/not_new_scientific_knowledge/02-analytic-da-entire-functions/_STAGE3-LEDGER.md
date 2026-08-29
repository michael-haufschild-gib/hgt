# Stage-3 sweep ledger — 02-analytic-da-entire-functions

Goal: unconditional Lean formalization of every card in this folder, then promotion to
`3-formalized`. No hypotheses added beyond the card's own; no axioms; no `sorry`.

## Status table

| # | Card | Hard classical input | Status |
|---|---|---|---|
| 1 | supergaussian-wide-newton-plateau-monomialization | elementary (Newton envelope + Wiman face) | **DONE → 3-formalized** (2026-08-29) |
| 2 | finite-jet-nonidentifiability-ht | Hölder (owned) | **DONE → 3-formalized** (2026-08-29) |
| 3 | order-two-shadow-matching-normal-form | algebraic core DONE; needs Gol'dberg + zero-free Hadamard | PARTIAL |
| 4 | quasianalytic-one-phase-bezout-boundary-law | all steps closed | **DONE → 3-formalized** (2026-08-29) |
| 5 | quasianalytic-exponential-log-phase-jet-law | all steps closed | **DONE → 3-formalized** (2026-08-29) |
| 6 | exponential-tower-exact-differential-order | both halves closed | **DONE → 3-formalized** (2026-08-29) |
| 7 | first-order-meromorphic-compression-matching | Steinmetz + 3-field factorization | TODO |
| 8 | entire-heat-multiplicative-da-order-three-floor | Valiron–Zimogljad–Strelitz | TODO |
| 9 | drifting-periodic-primitive-ramification-exclusion | reduction DONE (`DriftPeriodicRamification`); needs I5 + I4 | PARTIAL |
| 10 | entire-composition-hypertranscendence-or-law | Steinmetz reduction / Huang–Ng Thm 3 | TODO |
| 11 | first-order-composition-two-defect-decomposition | Clunie + trdeg observability | TODO |
| 12 | autonomous-cap-derivative-shadow-law | Clunie + trdeg observability | TODO |
| 13 | newton-corner-nonautonomous-composition-unit-cost | Clunie + Puiseux Jacobian | TODO |
| 14 | asymptotically-exponential-algebraic-cascade-unit-cost | Clunie + Puiseux Jacobian + Briot–Bouquet | TODO |
| 15 | nonautonomous-cap-linear-order-two-shadow-rigidity | Briot–Bouquet | TODO |
| 16 | fixed-taylor-modulus-newton-geometry-ht-blindness | Ostrowski finite basis | TODO |
| 17 | arithmetic-entire-heat-da-finite-spectrum | Popken + Mahler normalization | TODO |
| 18 | finite-commuting-shift-peeling-hypertranscendence-law | Adamczewski–Dreyfus–Hardouin Thm 1.2 | TODO |
| 19 | autonomous-ade-almost-periodic-frequency-rank | Cartwright/O'Brien | TODO |
| 20 | first-order-autonomous-algebraic-ap-periodicity | Schwartz surface flows + normalization | TODO |
| 21 | paired-quasi-elliptic-constraint-rigidity | Hardouin–Singer PPV + Cassidy | TODO |
| 22 | smooth-stein-order-two-autonomous-ade-frequency-rank | Taubes (Weinstein conj. dim 3) | TODO |

## Corpus assets already owned (do not rebuild)

- `HTGeometry.Hypertranscendence` — `DifferentiallyAlgebraic`, `Hypertranscendental`
- `HTGeometry.GammaHypertranscendental.hypertranscendental_gamma` (Hölder)
- `HTGeometry.FiniteJetIndistinguishability` — jets at 0, `exists_finiteJet_da_and_ht`
- `HTGeometry.MaximumTermCentralIndex` — maximum term `mu(r)`, central index
- `HTGeometry.WimanValiron*` — explicit Wiman–Valiron estimate
- `HTGeometry.StretchedExponentialMagnitudeHypertranscendence`, `LogSuperlacunaryMagnitudeHypertranscendence`
- `HTGeometry.ExactDifferentialOrderAffine`, `CascadeExactOrder`, `AffineExponentialCascadeOrder`,
  `IteratedExponentialGrowthHeight`, `AffineExponentialCascadeGrowth`
- `HTGeometry.ClunieSeparationBridge`, `RHTower.PolyaCompositionGrowth`, `HTGeometry.PolyaConnectedTransfer`
- `HTGeometry.BohrHullGroup`, `AlmostPeriodicHull`, `AutonomousSeparant`
- `HTGeometry.NevanlinnaEntireCharacteristic`, `NevanlinnaCharacteristicLowerBound`, `LogDerivPoissonJensen`

## Shared classical infrastructure still missing (drives most remaining cards)

| # | Theorem | Cards that need it |
|---|---|---|
| I1 | Gol'dberg: an entire solution of a first-order ADE has finite order | 3, 14 |
| I2 | Hadamard: zero-free entire of finite order is `exp P` | 3 |
| I3 | Clunie composition growth `T(r, f∘g)/T(r,g) → ∞` | 11, 12, 13, 14 |
| I4 | Briot–Bouquet classification of autonomous first-order meromorphic solutions | 14, 15 |
| I5 | Nevanlinna second main theorem with ramification (≤ 2 totally ramified finite values) | 9 |
| I6 | Steinmetz reduction / Huang–Ng Thm 3 | 7, 10 |
| I7 | Valiron–Zimogljad–Strelitz order-two growth wall | 8 |
| I8 | Ostrowski finite-coefficient-basis theorem for DA Dirichlet series | 16 |
| I9 | Popken lower bound + Mahler normalization | 17 |
| I10 | Adamczewski–Dreyfus–Hardouin Thm 1.2 (`S_∞`) | 18 |
| I11 | Cartwright/O'Brien autonomous frequency theorem | 19 |
| I12 | Schwartz surface-flow trichotomy + curve normalization | 20 |
| I13 | Hardouin–Singer several-automorphism PPV + Cassidy | 21 |
| I14 | Taubes: the Weinstein conjecture in dimension three | 22 |
| I15 | Pólya composition growth (via **Bohr's circle-covering theorem**, not a minimum-modulus floor) | 6 |

## Corpus assets discovered (do not rebuild)

Nevanlinna / value distribution:
- **mathlib** now has `ValueDistribution`: `characteristic`, `proximity`, `logCounting`, the
  **first main theorem** (`abs_characteristic_sub_characteristic_shift_le`,
  `characteristic_sub_characteristic_inv_le`), Cartan's identity, `characteristic_monotoneOn`.
- `HTGeometry.PoissonJensenFormula.poissonJensen`
- `HTGeometry.LogDerivPoissonJensen` — `logDeriv_poissonJensen`, `norm_logDeriv_le`,
  `norm_logDeriv_le_characteristic`, `circleAverage_abs_log_norm_le_characteristic`
- `HTGeometry.LogDerivativeProximity` — `circleAverage_posLog_logDeriv_le`,
  `circleAverage_posLog_logDeriv_sub_const_le` (the proximity of `f'/(f−a)`)
- `HTGeometry.SecondMainTheoremChain.mul_characteristic_le_sum_logCounting_add_proximity`
  (SMT modulo the residual proximity term; the FMT is a hypothesis mathlib can now discharge)
- `HTGeometry.SmallGrowthDerivative.smallGrowth_proximity_logDeriv_isLittleO` (log-derivative
  lemma in the small-growth case)
- `Nevanlinna.borel_growth`, `exists_ge_lt_two_mul`, `exists_ge_lt_two_mul_scaled`
  (`HTGeometry/BorelGrowthLemma.lean`) — the exceptional-set lemma

Growth / factorization:
- `HTGeometry.FiniteOrderHadamard.exists_polynomial_exp_of_ne_zero_of_growth` (zero-free Hadamard)
- `HTGeometry.FiniteOrderZeroFreeDifferentialAlgebraic.differentiallyAlgebraic_of_zeroFree_of_finiteOrderEnvelope`
  — **this is the whole zero-free-primitive residue of card 3 except Gol'dberg**
- `RHTower.MinimumModulus.norm_lower_bound_of_anchor` — a fully *quantitative* minimum-modulus
  floor for zero-free functions; `RHTower.EntireMinimumModulus` wraps it but hides the constant
- `RHTower.PolyaCompositionGrowth`, `HTGeometry.PolyaConnectedTransfer`,
  `HTGeometry.IteratedExponentialGrowthHeight`, `HTGeometry.AffineExponentialCascadeGrowth`

Cascades / differential algebra:
- `HTGeometry.CascadeExactOrder`, `CascadeUpperBound`, `EntireCascadeStateFieldOrder`
  (the unit-cost law modulo jet independence — the exact residue of cards 13/14)
- `HTGeometry.AnalyticJetFieldBridge` — DA closed under `+ − × ^`
- `HTGeometry.FractionRingDerivation.fractionRingDerivation`
- `HTGeometry.DifferentiallyAlgebraicCancellation.differentiallyAlgebraic_right_of_mul_eq`

## The next infrastructure build: Nevanlinna's second main theorem

Chain to write, in order (unlocks cards 4, 7, 8, 9, 10, 11, 12, 13, 14):

1. `NevanlinnaTruncatedCounting` — the truncated counting function `N̄(r, a)`.
2. `NevanlinnaLogDerivBound` — the general logarithmic-derivative lemma
   `m(r, f'/f) = O(log⁺ T(ρ, f) + log⁺ 1/(ρ−r) + log ρ)` from
   `norm_logDeriv_le_characteristic` plus `borel_growth` for the exceptional set.
3. `NevanlinnaSecondMain` — discharge the residual proximity term of
   `mul_characteristic_le_sum_logCounting_add_proximity` through
   `Σ_j (f−a_j)⁻¹ = (1/f')·Σ_j f'/(f−a_j)`, and truncate.
4. `NevanlinnaRamification` — `Σ_a (1 − 1/m_a) ≤ 1` for entire `f`, hence at most two totally
   ramified finite values; feeds `exists_finset_totallyRamified_card_ge` and closes card 9.

## Pólya's composition theorem: the correct route (settled 2026-08-29)

The card `exponential-tower-exact-differential-order` records the gate as "a quantitative
minimum-modulus floor".  **That is the wrong tool** and it cannot work: for `g = exp` and `h = exp`
the minimum modulus of the outer function on the circle `|w| = t` is `e^{-t}`, so a circle *floor*
for the outer function gives nothing at the iterated-exponential scale.

Pólya's original paper (*On an integral function of an integral function*, J. London Math. Soc. 1
(1926), 12–15) proves

> **Theorem II.** `f = g ∘ h` entire, `h(0) = 0`, `F, G, H` the maximum moduli on `|z| ≤ r`.
> There is an absolute `c ∈ (0,1)`, independent of `g, h, r`, with `F(r) ≥ G(c·H(r/2))`.

and the proof is a **circle-covering** argument, not a floor: it uses

> **Bohr's theorem** (H. Bohr, *Scripta Univ. atque Bibl. Hierosolymitanarum* 1 (1923); generalising
> E. Landau, Rend. Palermo 46 (1922), 347–348).  Let `0 < ρ < 1` and let `φ` be regular on `|z| ≤ 1`
> with `φ(0) = 0` and `max_{|z|=ρ}|φ| = 1`.  Let `r_φ` be the radius of the largest circle `|w| = r_φ`
> **all** of whose points are values of `φ` on `|z| ≤ 1`.  Then `r_φ ≥ C(ρ) > 0`.

Applying Bohr to `φ(z) = h(rz)/H(r/2)` with `ρ = 1/2` makes `h(|z| ≤ r)` cover a whole circle of
radius `R ≥ c·H(r/2)`; picking `w₀` on that circle with `|g(w₀)| = G(R)` gives `F(r) ≥ G(R)`.

**Bohr's theorem follows from Schottky's theorem** by the following short argument (worked out here):
if every circle `|w| = t` with `t ≤ C` fails to be covered, choose omitted values `w₁, w₂` with
`|w₁| = C`, `|w₂| = C/2`; then `(φ − w₂)/(w₁ − w₂)` omits `0` and `1` and takes the value
`(0 − w₂)/(w₁ − w₂)` of modulus `≤ 1` at the origin, so Schottky bounds `|φ|` on `|z| = ρ` by
`t·(1/2 + (3/2)Ψ(1,ρ))`; with `max_{|z|=ρ}|φ| = 1` this forces `C ≥ (1/2 + (3/2)Ψ(1,ρ))⁻¹`.

**The corpus already owns the modular machinery Schottky needs**, in the Böttcher area:
`Bottcher.ModularLambda.modularLambda`, `Bottcher.ModularLambdaCovering.modularLambda_surjective`
(`λ` attains every value in `ℂ∖{0,1}`), `Bottcher.ModularLambdaOmittingLift.omitting_lift_member_based`,
`Bottcher.CrossRatioOmittingBridge.spherical_normal_of_omitting_lift`.  So the build order for
card 6 is: **Schottky → Bohr → Pólya II → growth-depth → `cd₊(F_n) = n`.**

## Build plan for Bohr → Pólya (card 6), resting entirely on corpus assets

The corpus's Böttcher lane already owns the modular machinery:

- `Bottcher.ModularLambda.modularLambda` and `Bottcher.ModularLambdaCovering` — including
  `modularLambda_surjective` and the covering map `isCoveringMap_lambdaPunct : ℍ → ℂ∖{0,1}`;
- `Bottcher.ModularLambdaOmittingLift.omitting_lift_member` / `omitting_lift_member_based` /
  `omitting_lift_member_strict` — every holomorphic `f : ball c R → ℂ∖{0,1}` lifts to a bounded
  holomorphic disc map;
- `Bottcher.MontelNormal.montel_subseq` (bounded Montel) and
  `Bottcher.OmittingNormal.normal_of_omitting_lift` (three-value Montel modulo the lift),
  `Bottcher.CrossRatioOmittingBridge.spherical_normal_of_omitting_lift`.

Chain to build (refined 2026-08-29 — **no hyperbolic geometry and no normal-families limit
argument are needed**).  **Steps 1–3 are now Lean-closed** in
`HTGeometry/ModularDiskChart.lean` and `HTGeometry/BohrCoveringCircle.lean`:

1. ✅ **A compact section of `λ` over a compact set** — `modularDisk`, `analyticOnNhd_modularDisk`,
   `exists_modularDisk_eq`, `isOpen_modularDisk_image`, `exists_radius_lt_one_modularDisk_covers`.  `λ` is a covering map onto `ℂ∖{0,1}`
   (`isCoveringMap_lambdaPunct`), hence a surjective local homeomorphism; so for every compact
   `K ⊆ ℂ∖{0,1}` there is a compact `L ⊆ ℍ` with `K ⊆ λ(L)`.  Consequently
   `s₀(K) := sup_{τ ∈ L} |cayley τ| < 1`.
2. ✅ **Uniform Schottky on a compact base set** — `cayley_cayleyInv`, `normSq_blaschke_identity`,
   `norm_le_of_blaschke_le`, `exists_bound_of_omitting_compact_base`.  Let `f : ball 0 1 → ℂ∖{0,1}` be holomorphic with
   `f 0 ∈ K`.  Lift with `omitting_lift_member_based` to `g : 𝔻 → 𝔻` with `g 0 = cayley τ₀`,
   `τ₀ ∈ L`, so `|g 0| ≤ s₀`.  Schwarz–Pick gives
   `|g z| ≤ (s₀ + ρ)/(1 + s₀ ρ) =: s < 1` for `|z| ≤ ρ`, whence
   `|f z| ≤ Ψ(K, ρ) := max_{|w| ≤ s} |λ(cayleyInv w)|`, a finite constant.
   (Only a *compact base set* is needed — the full Schottky theorem, with its cusp asymptotics for
   `λ`, is **not** required.)
3. ✅ **Bohr's circle-covering theorem** — `bohrBase`, `isCompact_bohrBase`,
   `exists_covered_circle`.  If the circles `|w| = t` and `|w| = t/2` both miss a value
   of `φ`, say `w₁, w₂`, then `ψ := (φ − w₂)/(w₁ − w₂)` omits `0` and `1` and its value at the
   origin satisfies `1/3 ≤ |ψ(0)| ≤ 1` **and** `|ψ(0) − 1| = |w₁|/|w₁ − w₂| ≥ 2/3`, so `ψ(0)` lies
   in the fixed compact `K = {|w| ∈ [1/3, 1], |w − 1| ≥ 2/3}` of `ℂ∖{0,1}`.  Step 2 then bounds
   `|ψ| ≤ Ψ(K, ρ)` on `|z| ≤ ρ`, hence `|φ| ≤ t(1/2 + (3/2)Ψ)` there; with
   `max_{|z|=ρ}|φ| = 1` this forces `t ≥ (1/2 + (3/2)Ψ)⁻¹ =: C(ρ)`.  So some circle of radius
   `≤ C(ρ)` is entirely covered.
4. **Pólya's Theorem II** `F(r) ≥ G(c·H(r/2))` by applying step 3 to `φ(z) = h(rz)/H(r/2)`.
5. `PositiveLowerOrder g`, `GrowthHeightAtLeast h k` ⟹ `GrowthHeightAtLeast (g∘h) (k+1)`, and the
   `List.Sublist` induction over factorizations ⟹ `cd₊(F_n) = n`, closing card 6 together with the
   already-proved `ord_DA(F_n) = n`.

Steps 1–3 give a compact-base Schottky bound and Bohr's covering theorem — both reusable far
beyond this card (they are the quantitative core of Picard/Montel).

## Log
- 2026-08-29 — ledger created; all 22 cards read; corpus reconnaissance done.
- 2026-08-29 — card 1 closed: `SuperGaussianNewtonPlateau`, `SuperGaussianMonomialization`,
  `SuperGaussianAutonomousFace`; axioms clean; promoted to `3-formalized`.
- 2026-08-29 — card 2 closed: `EntireTaylorUniformApproximation`, `FiniteJetNonidentifiability`.
- 2026-08-29 — card 3 algebraic core landed (`OrderTwoShadowMatching`); residue = Gol'dberg + Hadamard.
- 2026-08-29 — card 9 reduction landed (`DriftPeriodicRamification`); SMT programme planned.
- 2026-08-29 — Schottky (compact base) and **Bohr's circle-covering theorem** Lean-closed:
  `HTGeometry/ModularDiskChart.lean`, `HTGeometry/BohrCoveringCircle.lean`; axioms clean.
  Remaining for card 6: Pólya's Theorem II and the composition-depth induction.
- 2026-08-29 — **card 6 closed and promoted**: Bohr → Pólya II → growth-depth → `cd₊(F_n)=n`.
  New: `ModularDiskChart`, `BohrCoveringCircle`, `PolyaCompositionMaximum`,
  `IterExpExponentComparison`, `CompositionGrowthHeight`, `CompositionDepth`.
- 2026-08-29 — **card `quasianalytic-one-phase-bezout-boundary-law` closed and promoted**.
  New: `PolynomialProjectiveBoundary`, `UpperPoincareGrowth`, `OnePhaseBezoutBoundary`.
  Reusable: gcd/Bezout normalisation over `K[X]`, finite-dimensional coefficient-sphere compactness
  with locally uniform polynomial limits, terminal projective boundary of a polynomial.
- 2026-08-29 — **card `quasianalytic-exponential-log-phase-jet-law` closed and promoted**.
  New: `VandermondePhaseJet`, `JetProjectiveLimit` (abstract finite jet carrier), `ExponentialPolynomialCarrier`.
  Reusable: uniform lower bound for an invertible matrix, Vandermonde jet inversion over unit phases,
  the abstract `JetEval` functional-projective limit, exponential-polynomial recession.
