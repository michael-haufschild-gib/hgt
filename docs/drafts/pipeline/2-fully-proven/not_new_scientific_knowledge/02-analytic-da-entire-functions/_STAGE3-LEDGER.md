# Stage-3 sweep ledger — 02-analytic-da-entire-functions

Goal: unconditional Lean formalization of every card in this folder, then promotion to
`3-formalized`. No hypotheses added beyond the card's own; no axioms; no `sorry`.

## Status table

| # | Card | Hard classical input | Status |
|---|---|---|---|
| 1 | supergaussian-wide-newton-plateau-monomialization | elementary (Newton envelope + Wiman face) | **DONE → 3-formalized** (2026-08-29) |
| 2 | finite-jet-nonidentifiability-ht | Hölder (owned) | **DONE → 3-formalized** (2026-08-29) |
| 3 | order-two-shadow-matching-normal-form | Gol'dberg now Lean-proved | **DONE → 3-formalized** (2026-08-29) |
| 4 | quasianalytic-one-phase-bezout-boundary-law | all steps closed | **DONE → 3-formalized** (2026-08-29) |
| 5 | quasianalytic-exponential-log-phase-jet-law | all steps closed | **DONE → 3-formalized** (2026-08-29) |
| 6 | exponential-tower-exact-differential-order | both halves closed | **DONE → 3-formalized** (2026-08-29) |
| 7 | first-order-meromorphic-compression-matching | Steinmetz + 3-field factorization | TODO |
| 8 | entire-heat-multiplicative-da-order-three-floor | Valiron–Zimogljad–Strelitz | TODO |
| 9 | drifting-periodic-primitive-ramification-exclusion | closed with `card_totallyRamified_le_four` | **DONE → 3-formalized** (2026-08-29) |
| 10 | entire-composition-hypertranscendence-or-law | Steinmetz reduction / Huang–Ng Thm 3 | TODO |
| 11 | first-order-composition-two-defect-decomposition | Clunie + trdeg observability | **DONE → 3-formalized** (2026-08-30) |
| 12 | autonomous-cap-derivative-shadow-law | Clunie + trdeg observability | **DONE → 3-formalized** (2026-08-30) |
| 13 | newton-corner-nonautonomous-composition-unit-cost | Clunie + Puiseux Jacobian | TODO |
| 14 | asymptotically-exponential-algebraic-cascade-unit-cost | Clunie + Puiseux Jacobian + Briot–Bouquet | TODO |
| 15 | nonautonomous-cap-linear-order-two-shadow-rigidity | Briot–Bouquet | TODO |
| 16 | fixed-taylor-modulus-newton-geometry-ht-blindness | Ostrowski finite basis — replaced by corpus Mahler confinement | **DONE → 3-formalized** (2026-08-30) |
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
| ~~I1~~ | **CLOSED (2026-08-29)** — `HTGeometry.GoldbergFiniteOrder.finiteOrderEnvelope_of_algebraic_relation` | 3, 14 |
| ~~I2~~ | ~~Hadamard: zero-free entire of finite order is `exp P`~~ — **already owned**: `HTGeometry.FiniteOrderHadamard.exists_polynomial_exp_of_ne_zero_of_growth` | 3 |
| ~~I3~~ | **CLOSED (2026-08-29)** — `HTGeometry.ClunieCompositionGrowth.exists_clunie_composition_growth` and `not_eventually_characteristic_comp_le` | 11, 12, 13, 14 |
| I4 | Briot–Bouquet classification of autonomous first-order meromorphic solutions | 14, 15 |
| ~~I5~~ | **CLOSED (2026-08-29)** — Nevanlinna ramification: `HTGeometry.NevanlinnaRamification.card_totallyRamified_le_four` gives `q ≤ 4` for an entire function, which is all card 9 needs | 9 |
| ~~I11~~ | **CLOSED (2026-08-29)** — the general logarithmic-derivative lemma `m(r,f'/f) = O(log⁺T(R,f) + log(1/(R−r)) + log R)` — the single input the corpus's `SecondMainTheoremChain` still needs, and the common prerequisite of I1, I3, I5, I6, I7 | 3, 7, 8, 9, 10, 11, 12, 13, 14, 15 |
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

## The logarithmic-derivative lemma (I11): route and progress

The corpus already owns everything on either side of it:

- `HTGeometry.LogDerivPoissonJensen.logDeriv_poissonJensen` — Nevanlinna's starting identity,
  `f'/f` = divisor sum + differentiated Herglotz average;
- `HTGeometry.LogDerivPoissonJensen.norm_logDeriv_le_characteristic` — the pointwise bound
  `‖f'/f‖ ≤ ‖divisor sum‖ + (2R/(R−|w|)²)·(2T(R,f) + C₀)`;
- `HTGeometry.SecondMainTheoremSeparation.sum_proximity_le_of_meromorphic` and
  `HTGeometry.SecondMainTheoremChain.mul_characteristic_le_sum_logCounting_add_proximity` — the
  second main theorem *up to* the residual proximity term.

The corpus's existing integration of the pointwise bound (`LogDerivativeProximity`) costs `log 2`
per divisor point, i.e. `O(n(R,f)) = O(T(R,f))` — too large for a second main theorem.  The fix is
the classical `α`-power trick with a fixed `α ∈ (0,1)`:

```text
log⁺ x = (1/α)·log⁺(x^α) ≤ (1/α)·log(1 + x^α),   (x+y)^α ≤ x^α + y^α,
```

so the `n(R)` divisor terms enter the average only through `log n(R) = O(log T(R,f))`.  The step that
makes this work is a bound on the circle average of `‖w − u‖^{-α}` that is **uniform in `u`**.

**Built (2026-08-29)** — `HTGeometry/NegPowerCircleAverage.lean`, unconditional and axiom-clean:

| Step | Lean name |
|---|---|
| `|sin|^{-α}` is interval-integrable on `[0,π/2]`, `[π/2,π]`, `[0,π]`, `[0,2π]`, and (by periodicity) on every interval | `intervalIntegrable_abs_sin_rpow_neg_left/_right/_pi/_two_pi`, `intervalIntegrable_abs_sin_rpow_neg` |
| the constant `C_α = ∫_0^{2π}|sin|^{-α}` and its shift invariance | `sinNegPowerConst`, `sinNegPowerConst_nonneg`, `integral_abs_sin_rpow_neg_shift` |
| **`‖r e^{iθ} − u‖ ≥ r·|sin(θ − arg u)|`** — the distance to a circle point is at least the distance to the line through `0` and `u` | `norm_circle_sub_ge` |
| the zero set of a shifted sine is countable, hence null | `countable_sin_shift_eq_zero` |
| **the uniform circle bound `∫_0^{2π}‖r e^{iθ} − u‖^{-α}dθ ≤ C_α·r^{-α}`, with `C_α` independent of `u`** | `intervalIntegral_norm_circle_sub_rpow_neg_le` |

**Also built (2026-08-29)** — the remaining two self-contained pieces:

| Step | Lean name | Module |
|---|---|---|
| `y ↦ log(1+y)` is concave on `[0,∞)`; `log⁺ y ≤ log(1+y) ≤ y` | `concaveOn_log_one_add`, `posLog_le_log_one_add`, `log_one_add_le`, `posLog_le_self` | `HTGeometry/PosLogRpowAverage.lean` |
| `log⁺(y^α) = α·log⁺ y` | `posLog_rpow` | same |
| **Jensen for `log(1+·)`**: `⨍ log(1+G) ≤ log(1 + ⨍G)` | `average_log_one_add_le` | same |
| **the `α`-power `log⁺` estimate `⨍ log⁺F ≤ (1/α)·log(1 + ⨍F^α)`** | `average_posLog_le_log_one_add_average_rpow` | same |
| `(∑ f_i)^α ≤ ∑ f_i^α` for `0 < α ≤ 1` | `rpow_sum_le_sum_rpow` | `HTGeometry/NegPowerCircleAverage.lean` |
| interval integrability of the circle kernel | `intervalIntegrable_norm_circle_sub_rpow_neg` | same |
| **the divisor-kernel `α`-power average**: `∫_0^{2π}(∑_u m_u(‖w−u‖⁻¹ + (R−r)⁻¹))^α dθ ≤ (∑_u m_u^α)·(C_α r^{-α} + 2π(R−r)^{-α})` | `intervalIntegral_kernelSum_rpow_le` | same |

**Assembled (2026-08-29)** — `HTGeometry/AlphaProximityEstimate.lean` and
`HTGeometry/LogDerivProximityBound.lean`, unconditional and axiom-clean:

| Step | Lean name |
|---|---|
| the normalised arc measure and `⨍ h ∂arc = (2π)⁻¹∫_0^{2π} h` | `arcMeasure`, `arcMeasure_univ`, `arcMeasure_real_univ`, `average_arcMeasure` |
| interval-integral form of the `α`-power `log⁺` estimate | `intervalIntegral_posLog_le_log_one_add_rpow` |
| **the `α`-power proximity estimate**: a function bounded a.e. on the circle by a divisor-kernel sum plus `B` has `(2π)⁻¹∫log⁺ ≤ (1/α)log(1 + (2π)⁻¹(∑m_u^α)(C_α r^{-α} + 2π(R−r)^{-α}) + B^α)` | `circleAverage_posLog_le_of_kernel_bound` |
| **the Blaschke reflection factor is `≤ 1/(R−r)`** on the circle of radius `r` | `norm_blaschke_reflection_le` |
| **the estimate for the Poisson–Jensen kernel itself** (finsum divisor term, weights `|n_u|`) | `circleAverage_posLog_le_of_poissonJensen` |
| the angles of a circle hitting a point / a finite set are countable, hence null | `countable_circle_preimage_point`, `countable_circle_preimage_finset` |

**I11 CLOSED (2026-08-29)** — `HTGeometry/LogDerivProximityBound.lean`:

```text
circleAverage_posLog_logDeriv_le_of_entire :
  0 < α → α < 1 → 0 < r → r < R → 1 ≤ R →
  Differentiable ℂ f → (∀ z, meromorphicOrderAt f z ≠ ⊤) →
  (∀ u ∈ sphere 0 |R|, MeromorphicOn.divisor f (closedBall 0 |R|) u = 0) →
  (2π)⁻¹ ∫_0^{2π} log⁺‖(f'/f)(re^{iθ})‖ dθ
    ≤ (1/α)·log(1 + (2π)⁻¹·(∑ᶠ_u |n_u|^α)·(C_α r^{-α} + 2π(R−r)^{-α})
        + (2R/(R−r)²·(2T(R,f) + C₀))^α)
```

unconditional, `#print axioms` = `propext, Classical.choice, Quot.sound`.  Supporting lemma:
`ne_zero_of_divisor_eq_zero`.

**Trap recorded (it is why the specialization must assume `f` entire).**  `MeromorphicOn.divisor f U w = 0` together with
`meromorphicOrderAt f w ≠ ⊤` gives `meromorphicOrderAt f w = 0`, but that does **not** by itself give
`AnalyticAt ℂ f w` and `f w ≠ 0` — the value at the single point `w` is invisible to
`meromorphicOrderAt`.  Continuity at `w` is needed (`MeromorphicAt.analyticAt`).  So the
specialization is stated for an entire `f`, which is exactly the case every card in this folder
needs.

### The second main theorem: state of the chain

**The corpus already owns the SMT in exactly the shape I11 feeds** — this was missed by the earlier
survey and is the key structural fact:

```text
SecondMainTheoremChain.mul_characteristic_le_of_separated :
  q·T(r,f) ≤ ∑_j N(r,a_j) + ∑_j m(r, f'/(f − a_j)) + m(r, 1/f') + constants
```

so step 2 of the old plan is **not needed**: the separation estimate has already been converted into
the per-value logarithmic derivatives.

**Bridged (2026-08-29)** — `HTGeometry/LogDerivProximityBound.lean`:

```text
proximity_logDeriv_sub_const_le :
  proximity (fun z => deriv f z / (f z - a)) ⊤ r ≤ (the I11 bound for f - a)
```

i.e. I11 now bounds each summand of the middle group of the corpus SMT, for entire `f`.

**Counting bridge DONE (2026-08-29)** — `HTGeometry/DivisorMassCounting.lean` and
`HTGeometry/LogDerivCountingBound.lean`:

| Step | Lean name |
|---|---|
| `(|n|:ℝ)^α ≤ (|n|:ℝ)` for an integer `n` and `0 < α ≤ 1` | `rpow_abs_intCast_le` |
| **the divisor mass splits into the two pole masses**: `∑ᶠ|n_u| = poleMultiplicityMass f R + poleMultiplicityMass f⁻¹ R` (via `MeromorphicOn.divisor_inv` and `posPart_add_negPart`) | `divisorMass_eq_add` |
| **the counting bridge** `log 2 · ∑ᶠ|n_u| ≤ N(2R,f) + N(2R,1/f)` — the corpus's `log_two_mul_poleMultiplicityMass_le_logCounting` applied to `f` *and* to `f⁻¹` | `log_two_mul_divisorMass_le_logCounting` |
| `∑ᶠ|n_u|^α ≤ ∑ᶠ|n_u|` | `divisorMass_rpow_le` |
| **the logarithmic-derivative estimate against the counting functions** | `circleAverage_posLog_logDeriv_le_counting` |

The corpus already owned the mass bound in its *pole* form; applying it to `f⁻¹` supplies the zero
form, so no new potential theory was needed.

**What is left of the second main theorem:**
2. **SMT side conditions for an entire `f`: DONE (2026-08-29)** — `HTGeometry/SecondMainTheoremEntire.lean`.
   `mul_characteristic_le_of_separated_entire` discharges every meromorphy hypothesis of the corpus
   SMT (sums, differences, quotients and inverses of meromorphic germs are meromorphic, and `f'` is
   entire); `exists_mul_characteristic_le_of_separated_entire` additionally discharges the
   first-main-theorem defect `hfmt` through the corpus's `characteristic_top_le_characteristic_coe`,
   taking `K = ∑_j |K_j|`.  The only hypothesis left is `hcod`: `f'` does not vanish identically
   near the circle.
3. **the ramification term: DONE (2026-08-29)** — `HTGeometry/RamificationTermBound.lean`.

   | Step | Lean name |
   |---|---|
   | **inequality 2** `m(r,1/g) ≤ T(r,g) + C − N(r,1/g)` (first main theorem for `g`) | `proximity_inv_top_le` |
   | the first main theorem in the direction `T(r,a₀) ≤ T(r,f) + C` (the corpus owned only the opposite one) | `characteristic_coe_le_characteristic_top` |
   | **inequality 3** `T(r,f') ≤ 2T(r,f) + m(r,f'/f)` | **already corpus-owned**: `SmallGrowthDerivative.smallGrowth_characteristic_deriv_le` |
   | **the assembled bound** `(q/2 − 2)·T(r,f) ≤ ∑_j m(r,f'/(f−a_j)) + m(r,f'/f) + C` | `totallyRamified_characteristic_bound` |

   Inequality 3 needed no work at all: the corpus already had it for general meromorphic `f`.
   The old plan's `m(r, 1/f')` — absorb via `m(r,1/f') = T(r,f') − N(r,1/f') + O(1)` and
   `T(r,f') ≤ 2T(r,f) + m(r,f'/f) + O(1)`; for a totally ramified family this is what turns
   `N(r,a_j)` into the truncated `N̄(r,a_j) ≤ (1/2)N(r,a_j)`.

**Scope note for card 9 (found 2026-08-29).**  Card 9 does *not* need the sharp bound.
`DriftPeriodicRamification.exists_finset_totallyRamified_card_ge` produces *arbitrarily large finite
sets* of totally ramified values, so **any** finite bound closes it.  The lossy chain

```text
N(r,1/f') ≥ (1/2)∑_j N(r,a_j)   [each a_j-point has multiplicity m ≥ 2, so f' vanishes to order m−1 ≥ m/2]
m(r,1/f') = T(r,f') − N(r,1/f') + O(1)
T(r,f')   ≤ 2T(r,f) + m(r,f'/f) + O(1)
```

fed into the corpus SMT gives `(q/2 − 2)·T(r,f) ≤ S(r,f) + C`, hence `q ≤ 4` — enough.  This avoids
the truncated counting function `N̄` and the ramification-counting identity entirely.

**First displayed inequality, pointwise part: DONE (2026-08-29)** —
`HTGeometry/TotallyRamifiedOrder.lean`:

| Step | Lean name |
|---|---|
| at an `a`-point of a totally ramified value, `order(f − a) = m ≥ 2` and `order(f') = m − 1` | `order_deriv_of_totallyRamified` |
| **the pointwise divisor inequality `order(f − a) ≤ 2·order(f')`** | `order_le_two_mul_order_deriv` |

built on mathlib's `analyticOrderAt_deriv_of_pos` and `AnalyticAt.analyticOrderAt_eq_zero`.

**Divisor form: DONE (2026-08-29)** — same module:

| Step | Lean name |
|---|---|
| for an entire `g` of finite order everywhere, `divisor g U u = (analyticOrderAt g u).toNat` | `divisor_eq_analyticOrder_toNat` |
| away from an `a`-point the shifted divisor vanishes | `divisor_sub_eq_zero_of_ne` |
| the divisor of `f'` is nonnegative | `divisor_deriv_nonneg` |
| **pointwise**: `divisor(f − a) ≤ 2·divisor(f')` at a totally ramified `a` | `divisor_sub_le_two_mul_divisor_deriv` |
| **summed over distinct values** (at most one is attained at any point) | `sum_divisor_sub_le_two_mul_divisor_deriv` |

**Inequality 1 COMPLETE (2026-08-29)** — `sum_logCounting_le_two_mul_logCounting_deriv`:

```text
∑_j 𝑁(divisor(f − a_j)) (r) ≤ 2 · 𝑁(divisor f') (r)
```

for finitely many distinct totally ramified values of an entire `f`, obtained by integrating the
summed pointwise divisor inequality against the corpus's
`smallGrowth_locallyFinsupp_logCounting_mono` (`logCounting` is an additive hom, so `map_sum` and
`map_nsmul` do the rest).

**Value-distribution form DONE (2026-08-29)** — `divisor_posPart_eq_self` (an entire function's
divisor is its own positive part) plus mathlib's `ValueDistribution.logCounting_coe` /
`logCounting_zero` give

```text
sum_logCounting_value_le_two_mul_logCounting_deriv_zero :
  ∑_j N(r, a_j) ≤ 2 · N(r, 1/f')
```

for an entire `f` and finitely many distinct totally ramified values.  **Inequality 1 is closed.**

## I5 (Nevanlinna ramification) — the single remaining step

Everything is in place except the asymptotic conclusion.  The pieces:

```text
totallyRamified_characteristic_bound :
  (q/2 − 2)·T(r,f) ≤ ∑_j m(r, f'/(f − a_j)) + m(r, f'/f) + C
proximity_logDeriv_sub_const_le / circleAverage_posLog_logDeriv_le_counting :
  each m(·) ≤ (1/α)·log(1 + (2π)⁻¹(log 2)⁻¹(N(2R,f) + N(2R,1/f))(C_α r^{-α} + 2π(R−r)^{-α}) + B^α)
```

**Correction found while starting this step (2026-08-29) — the doubling was fatal.**  The counting
bridge as first built (`log_two_mul_divisorMass_le_logCounting`, inherited from the corpus's
`log_two_mul_poleMultiplicityMass_le_logCounting`) evaluates the counting function at **`2R`**.  The
Borel lemma controls `T` only across a step of size `1/T(r)`, never across a doubling — and
`T(2r,f)/T(r,f)` is genuinely unbounded for infinite order.  So no choice of `R` could have made the
argument close.

Fixed by generalising the corpus proof from the ratio `2` to an arbitrary ratio:
`HTGeometry/PoleMassRatioRadius.lean`

| Step | Lean name |
|---|---|
| pole mass in `|z| ≤ R` versus the counting function at any `R' > R`, with loss `log(R'/R)` | `log_ratio_mul_poleMultiplicityMass_le_logCounting` |
| **the counting bridge at an arbitrary larger radius** | `log_ratio_mul_divisorMass_le_logCounting` |

Since only the *logarithm* of the divisor mass enters the final estimate, a ratio as small as
`1 + 1/(r T(r))` costs only `O(log r + log T(r))` — harmless.

**The step.**  Put `R := r + 1/T(r,f)`, so `(R − r)^{-α} = T(r,f)^α`.  The corpus's Borel lemma —
`HTGeometry.BorelGrowthMonotone.borel_growth_monotone` (exceptional set of measure ≤ 2 where
`2T(r) ≤ T(r + 1/T(r))`), or `BorelGrowthExponent.borel_growth_monotone_rpow` at exponent `α` —
gives `T(R,f) < 2T(r,f)` off a set of finite measure.  Feed the counting bridge at ratio
`R'/R` with `R' ≤ r + 1/T(r)` rather than at `2R`.  Then every `N` and `B` in the I11 bound is
`O(T(r,f))`, so the whole right-hand side is `O(log T(r,f) + log r)`, i.e. `S(r,f) = o(T(r,f))`.
With `q ≥ 5` the left-hand side is `≥ (1/2)T(r,f)`, contradicting `T(r,f) → ∞` for a transcendental
`f`.  Hence **`q ≤ 4`**, which is I5 and closes card 9 (which needs only *some* finite bound —
see the scope note above).

Corpus assets for this step (do not rebuild):
`BorelGrowthLemma.borel_growth`, `BorelGrowthMonotone.borel_growth_monotone`,
`BorelGrowthExponent.borel_growth_monotone_rpow`, `borel_growth_monotone_rpow_ne_top`.

### Asymptotic packaging built (2026-08-29) — `HTGeometry/LogPolyNegligible.lean`

| Step | Lean name |
|---|---|
| `1 + x^k ≤ (1+x)^k`; `log(1 + C·X·Y) ≤ log(1+C) + log(1+X) + log(1+Y)` | `one_add_pow_le`, `log_one_add_mul_le` |
| `log(x+2)/x → 0` | `tendsto_log_add_div_atTop` |
| **`S(r) ≤ log(1 + C(r+1)^k(T r + 1)^k)` and `log r / T r → 0` ⟹ `∀ ε > 0, ∀ᶠ r, S r ≤ ε·T r`** | `eventually_le_of_log_poly_bound` |
| **`(q/2 − 2)·T(r) ≤ S(r) + C` eventually, `S` negligible, `T → ∞` ⟹ `q ≤ 4`** | `le_four_of_characteristic_bound` |

So both ends of the last step are now formal.  What remains is purely the substitution: choose
`R := r + 1/(2T(r))`, `R' := r + 1/T(r)`, apply `borel_growth_monotone` to get `T(R',f) < 2T(r,f)`
off a finite-measure set, and check that the resulting bound from
`circleAverage_posLog_logDeriv_le_counting` (with `log_ratio_mul_divisorMass_le_logCounting` at ratio
`R'/R`) has the shape `log(1 + C(r+1)^k(T(r)+1)^k)` required by `eventually_le_of_log_poly_bound`.
A convenient lower bound for the ratio loss is `log(R'/R) ≥ 1/(4·T(r)·(r+1))` for `r ≥ 1`.

### Ratio-radius estimate and sequence conclusion built (2026-08-29)

| Step | Lean name | Module |
|---|---|---|
| **the logarithmic-derivative estimate with the counting functions at any `R' > R`** (cost `log(R'/R)⁻¹`) | `circleAverage_posLog_logDeriv_le_counting_ratio` | `HTGeometry/LogDerivCountingRatio.lean` |
| the counting conclusion along a *sequence* of radii (the Borel good set is unbounded, not cofinite) | `le_four_of_characteristic_bound_seq` | `HTGeometry/LogPolyNegligible.lean` |

**The single remaining lemma for I5.**  With `T r := characteristic f ⊤ r`, for `r` outside the
Borel exceptional set put `R := r + 1/(2 T r)` and `R' := r + 1/(T r)`.  Then

* `T R' < 2 T r` (`BorelGrowthMonotone.borel_growth_monotone`);
* `N(R',f) = 0` for entire `f`, and `N(R',1/f) ≤ T R' + K ≤ 2 T r + K` (first main theorem);
* `log(R'/R) ≥ 1/(4 · T r · (r+1))` for `r ≥ 1`;
* `(R − r)^{-α} = (2 T r)^α` and `2R/(R−r)² ≤ 8 (r+1) (T r)²`.

Substituting into `circleAverage_posLog_logDeriv_le_counting_ratio` gives a bound of the shape
`log(1 + C (r+1)^k (T r + 1)^k)`, which is exactly the hypothesis of
`eventually_le_of_log_poly_bound`.  Feeding that and `totallyRamified_characteristic_bound` into
`le_four_of_characteristic_bound_seq` yields `q ≤ 4` — I5 — and promotes card 9.

### Borel good radii and zero-free radii built (2026-08-29)

| Step | Lean name | Module |
|---|---|---|
| the monotone `≥ 1` majorant the Borel lemma needs (the characteristic is monotone only on `(0,∞)` and can dip below 1) | `charMajorant`, `monotone_charMajorant`, `one_le_charMajorant`, `characteristic_le_charMajorant` | `HTGeometry/BorelGoodRadii.lean` |
| **good radii exist beyond every bound** (exceptional set has measure ≤ 2, half-lines have infinite measure) | `exists_good_radius` | same |
| **a sequence `rₙ → ∞` of good radii** | `exists_good_radius_seq` | same |
| the zero set of an entire function of finite order everywhere is countable | `countable_zeroSet` | `HTGeometry/ZeroFreeRadius.lean` |
| **every interval of radii contains one whose circle carries no zero** — required by the Poisson–Jensen hypothesis `hbd` | `exists_radius_no_zero_on_sphere` | same |

The second of these was an unnoticed obligation: `circleAverage_posLog_logDeriv_le_of_entire`
requires `f` to have no zero on `|z| = R`, so the radius `R` in the Borel substitution cannot be
taken to be exactly `r + 1/(2T r)` — it must be chosen inside a small interval around it, which
`exists_radius_no_zero_on_sphere` now supplies.

### The Borel substitution is CLOSED (2026-08-29) — `HTGeometry/RamificationSubstitution.lean`

| Step | Lean name |
|---|---|
| `u/(1+u) ≤ log(1+u)`; `y^{1/2} ≤ y+1`; `y^{1/2} ≤ y` for `y ≥ 1` | `log_one_add_ge`, `rpow_half_le_add_one`, `rpow_half_le_self` |
| the explicit Poisson–Jensen coefficient value at the substituted radii | `coefB_value` |
| **the ratio loss** `(log((r+t)/R))⁻¹ ≤ 4(r+1)/t` for `R ∈ (r+t/4, r+t/2)` | `inv_log_ratio_le` |
| the arithmetic core: three factor bounds combine into one polynomial | `substitution_poly_bound` |
| **the substitution**: at a Borel-good radius, `m(r,f'/f) ≤ 2·log(1 + C(r+1)^4(U r + 1)^4)` | `exists_logDeriv_poly_bound` |

Stated for an *arbitrary* monotone majorant `U ≥ 1` dominating the characteristic, not just
`charMajorant f`: the ramification argument applies it to `f` and to all the shifts `f − a_j` at the
*same* radii, so a single common majorant is needed.

**All of I5's ingredients are now formal.**  What remains is the bookkeeping assembly:
`totallyRamified_characteristic_bound` + (q+1 copies of) `exists_logDeriv_poly_bound` via
`proximity_logDeriv_sub_const_le` + `eventually_le_of_log_poly_bound_const` +
`exists_good_radius_seq` + `le_four_of_characteristic_bound_seq`.

## I5 CLOSED (2026-08-29)

```text
card_totallyRamified_le_four :
  Differentiable ℂ f → (q values, pairwise δ-separated, all totally ramified) →
  (order ≠ ⊤ for f, the shifts and f') → (f' not ≡ 0 near each circle) →
  (log r / charMajorant f r → 0) → (charMajorant f → ∞) →
  q ≤ 4
```

unconditional, `#print axioms` = `propext, Classical.choice, Quot.sound`.
`HTGeometry/NevanlinnaRamification.lean`.

The full chain, all built this session:

`NegPowerCircleAverage` → `PosLogRpowAverage` → `AlphaProximityEstimate` →
`LogDerivProximityBound` (I11) → `DivisorMassCounting` → `LogDerivCountingBound` →
`PoleMassRatioRadius` → `LogDerivCountingRatio` → `SecondMainTheoremEntire` →
`TotallyRamifiedOrder` → `RamificationTermBound` → `BorelGoodRadii` → `ZeroFreeRadius` →
`LogPolyNegligible` → `RamificationSubstitution` → `NevanlinnaRamification`.

### Remaining for card 9

`card_totallyRamified_le_four` needs the two growth hypotheses.  For the card's `W` they are not an
extra assumption but a consequence of the drift, by an argument that needs **no Picard theorem**:

* `W(z+T) = W(z) + C` makes `V := W − (C/T)·z` entire and `T`-periodic;
* if `V` is constant then `W` is affine, `W' = C/T ≠ 0`, and no value is totally ramified;
* if `V` is nonconstant then every point `nT` is a zero of `V − V(0)`, so
  `n(r, 1/(V − V(0))) ≥ 2r/|T| − 1`, whence `N(r, ·) ≥ (log 2)(r/|T| − 2)` and, by the first main
  theorem, `T(r,V) ≥ c·r − O(1)`;
* subadditivity (`NevanlinnaEntireCharacteristic.characteristic_add_le`) and
  `T(r, cz) = O(log r)` give `T(r,W) ≥ c·r − O(log r)`, hence both growth hypotheses.

That periodic-zero counting bound is the last piece before card 9 promotes.

## The Nevanlinna stack after card 9 (2026-08-29)

Card 9 is promoted.  The build left behind a general Nevanlinna layer that the remaining cards can
use directly; every item is unconditional and axiom-clean.

| Statement | Lean name | Module |
|---|---|---|
| `log⁺‖f w‖ ≤ (R+r)/(R−r)·(2T(R,f)+K)` for entire `f`, `‖w‖ ≤ r < R` | `posLog_norm_le_characteristic` | `MaxModulusCharacteristicBound` |
| Cauchy estimate along a *sequence* of radii | `iteratedDeriv_eq_zero_of_frequently_growth` | idem |
| `T(r,f) = O(log r)` along some sequence ⟹ `f` is a polynomial | `exists_polynomial_of_frequently_characteristic_le_log` | idem |
| **not a polynomial ⟹ `T(r,f)/log r → ∞`** | `tendsto_characteristic_div_log_atTop` | idem |
| the two Borel growth hypotheses from transcendence alone | `charMajorant_growth_of_not_polynomial` | idem |
| the SMT error term is `o(T)` along a sequence of good radii | `exists_good_radii_error_negligible` | `NevanlinnaErrorNegligible` |
| finitely many zeros ⟹ `N(r,0,f) ≤ M log r + C` | `exists_logCounting_le_of_finite_zeros` | `FiniteZeroCounting` |
| **classical SMT** `(q−2)T(r,f) ≤ ∑ N(r,a_j,f) + S(r,f) + C` | `exists_sub_two_characteristic_le_sum_logCounting` | `ValuePreimageInfinite` |
| **transcendental entire ⟹ some value has infinitely many preimages** | `exists_infinite_preimage_of_not_polynomial` | idem |
| lattice of zeros ⟹ linear characteristic growth | `logCounting_zero_ge_of_lattice_zeros`, `exists_characteristic_ge_of_lattice_zeros` | `LatticeZeroCounting` |

The reverse maximum-modulus bound was the missing keystone; the corpus already owned
`NevanlinnaTranslationBoundary.posLog_norm_le_poissonBoundary_add_poleGreen`, whose pole term
vanishes for entire functions, and `PoissonJensen.circleAverage_abs_log_norm_le_characteristic`.

### Next: I3 (Clunie composition growth)

The route is now fixed and needs no minimum-modulus argument:

1. `f` transcendental ⟹ some value `a` has `n` distinct preimages `b_1, …, b_n`
   (`exists_infinite_preimage_of_not_polynomial` + `Set.Infinite.exists_subset_card_eq`);
2. at a point where `g = b_j`, `analyticOrderAt (f∘g − a) ≥ analyticOrderAt (g − b_j)` — factor
   `f − a = (w − b_j)^m h` and compose;
3. hence `N(r, a, f∘g) ≥ ∑_j N(r, b_j, g)`, by `logCounting_le` on divisors;
4. the classical SMT for `g` at the `n` separated values `b_j` gives
   `(n−2)T(r,g) ≤ ∑_j N(r,b_j,g) + S(r,g) + C`;
5. the first main theorem gives `N(r,a,f∘g) ≤ T(r,f∘g) + C`;
6. `exists_good_radii_error_negligible` kills `S(r,g)` along a sequence of radii.

Result: for every `n`, `T(r,f∘g) ≥ (n−3)·T(r,g) − C` along a sequence of radii tending to infinity —
the limsup form, which is what the algebraicity contradiction in cards 11–14 consumes.

## I3 CLOSED (2026-08-29)

```text
exists_clunie_composition_growth :
  f, g entire and not polynomials → ∀ n,
  ∃ C, ∃ᶠ r in atTop, (n − 3)·T(r,g) ≤ T(r, f∘g) + C

not_eventually_characteristic_comp_le :
  f, g entire and not polynomials → ∀ c d,
  ¬ (∀ᶠ r, T(r, f∘g) ≤ c·T(r,g) + d·log r + d)
```

both unconditional and axiom-clean.  Supporting modules:

* `CompositionValueCounting.analyticOrderAt_le_comp` — a `b`-point of `g` is an `a`-point of `f∘g`
  of at least the same multiplicity, by factoring `f − a = (w − b)^k h` and composing;
* `CompositionValueCounting.sum_logCounting_le_logCounting_comp` — `∑_j N(r, b_j, g) ≤ N(r, a, f∘g)`
  for an injective family of `f`-preimages of `a`;
* `ClunieCompositionGrowth.meromorphicOrderAt_comp_sub_const_ne_top` — a composition of
  transcendental entire functions is nowhere locally constant, via mathlib's open-mapping
  dichotomy `AnalyticAt.eventually_constant_or_nhds_le_map_nhds`.

No minimum-modulus estimate and no Pólya inequality is used; the Nevanlinna route is strictly
shorter.  What cards 11–14 still need beyond this is the *algebraic* half: that an element algebraic
over a field generated by finitely many derivatives of `g` has characteristic `O(T(r,g) + log r)`,
and the differential-field transcendence-degree bookkeeping of the card statements.

## I1 CLOSED (2026-08-29) — Gol'dberg's theorem

```text
finiteOrderEnvelope_of_algebraic_relation :
  f entire, some Taylor coefficient nonzero,
  ∑_{p ∈ S} A_p(w)·f(w)^{p₁}·f'(w)^{p₂} = 0,  total degree ≤ d,
  the top symbol has T-degree m ≥ 1 with A_{(d−m,m)} ≠ 0
  → FiniteOrderEnvelope f
```

unconditional, axiom-clean.  The chain:

1. `GoldbergCentralIndex.norm_le_of_topSymbol_le_one` — a top symbol of modulus at most one bounds
   `T` by `(1 + ∑_p ‖A_p(z)‖)/‖A_q(z)‖ + 1`;
2. `GoldbergCentralIndex.exists_bound_coeff_quotient` — that quotient is `O((1+‖z‖)^D)` beyond the
   growth radius of the leading coefficient (`PolynomialGrowthBound`);
3. `GoldbergCentralIndex.exists_centralIndex_le_pow_of_relation` — combining with the Wiman place
   (`z·f'/f` within a factor two of `ν`) and with **density** of the places gives
   `ν(t) ≤ C·t^{D+1}` at *every* large `t`;
4. `GoldbergFiniteOrder.finiteOrderEnvelope_of_centralIndex_le_pow` — a polynomial central index
   gives `log μ(r) ≤ r^{K+2}` and hence the envelope, via
   `MaximumTermCentralIndex.log_maxTerm_le_rpow_of_centralIndex_le_rpow` and
   `MaximumModulusLocalGrowth.coeffSum_le_maxTerm_mul_two`;
5. `GoldbergFiniteOrder.entireCoeffs_taylorCoeff`, `coeffFun_taylorCoeff` — the Taylor bridge from a
   general entire function to the coefficient-sequence formalism;
6. the case of finitely many nonzero coefficients is handled directly
   (`finiteOrderEnvelope_of_eventually_taylorCoeff_eq_zero`), so the theorem needs no transcendence
   hypothesis.

### The density refactor

`Nevanlinna.borelWindow α := ((1 − (2^α)⁻¹)⁻¹).toReal + 1` and
`Nevanlinna.exists_mem_Icc_lt_two_mul_rpow_window` put a Borel-good radius inside *every* window of
that length.  The bound `x ≤ R + borelWindow α`, and the window bound `d + 2H ≤ x + 1`, are now
threaded through `exists_ge_centralIndex_no_double`, `exists_good_parameters`,
`exists_radius_point_wiman_valiron_selected`, `exists_radius_defect_le_eps`,
`exists_radius_defect_le_eps_of_transcendental`, `exists_radius_dominates_and_defect_le_eps`,
`exists_radius_norm_topSymbol_le` and `exists_radius_wiman_place`, whose statements changed shape
from `∀ R, ∃ y ≥ R` to `∃ M, ∀ R, ∃ y ∈ [R, max R M + borelWindow (1/4) + 1]`.

## The analytic half of cards 11–14 is closed (2026-08-29)

"Outer-state independence" — the step the cards phrase as *"the Nevanlinna root estimate and
Clunie's composition-growth theorem show that `h = f∘g` is transcendental over every field generated
by finitely many derivatives of `g`"* — is now a single unconditional Lean theorem:

```text
not_algebraic_comp_over_jet :
  f, g entire and not polynomials, N ≥ 1,
  A : ℕ → MvPolynomial (Fin (n+2)) ℂ,  A N not identically zero on the jet,
  ∀ z, ∑_{i ≤ N} A i (z, g z, …, g⁽ⁿ⁾ z) · (f (g z))^i = 0
  → False
```

The chain, all axiom-clean:

| Step | Lean name | Module |
|---|---|---|
| a Borel-good radius outside any null set | `exists_good_radius_seq_avoiding` | `BorelGoodRadiiAvoiding` |
| one sequence of radii making a whole finite family's logarithmic-derivative proximities negligible | `exists_good_radii_family` | `GoodRadiiFamily` |
| every derivative up to order `n` has `T(r,g⁽ʲ⁾) ≤ 2ⁿ⁺¹·T(r,g) + C` along that sequence, and the shift proximities are negligible | `exists_radii_jet_bound_and_error` | `IteratedDerivativeGrowth` |
| `¬ ∀ᶠ r, T(r,f∘g) ≤ c·∑ⱼ T(r,g⁽ʲ⁾) + d log r + d` | `not_eventually_characteristic_comp_le_jet` | `ClunieDerivativeField` |
| `T(r, A(z, G(z))) ≤ K(log r + ∑ T(r,Gⱼ)) + K` for a multivariate polynomial | `exists_characteristic_eval_le` | `MultivariateEvalCharacteristic` |
| the transcendence statement above | `not_algebraic_comp_over_jet` | `CompositionJetTranscendence` |

Two design points were forced by the mathematics:

* the multiplier in the jet bound must not depend on the number `N` of preimages used in the second
  main theorem, or the Clunie comparison `N − 3 > c` becomes circular; it is `2ⁿ⁺¹`, and all the
  `N`-dependence sits in the additive constant;
* the top coefficient of an algebraic relation is only assumed not identically zero, so the radii
  whose circle carries one of its zeros must be avoided; that set is countable, hence null, and the
  Borel exceptional set has measure two, so a window of length four always contains a usable radius.

What remains for cards 11–14 is the *algebraic* half: the transcendence-degree bookkeeping of the
jet fields (`H_h(n) = 1 + S_g(n)` and `trdeg_K N = 1 + (1−aut f)·π(g)`), for which the corpus already
owns `Algebra.trdeg`, `differentialAdjoin`, `DifferentialAlgebraicOver`, `DerivationClosed` and the
finite-transcendence descent `differentialAlgebraicOver_of_intermediate_trdeg_lt_aleph0`.

## The field-side transcendence bridge (2026-08-30)

`HTGeometry/CompositionJetField.lean`, unconditional and axiom-clean:

```text
not_isAlgebraic_comp_over_jetGen :
  f, g entire and not polynomials →
  ¬ IsAlgebraic ↥(IntermediateField.adjoin ℂ (Set.range (jetGen hg n)))
      (analyticMeroElement (f ∘ g) _)
```

where `jetGen hg n : Fin (n+2) → meroField univ` is the coordinate followed by
`g, g', …, g⁽ⁿ⁾`.  This is `not_algebraic_comp_over_jet` transported into the meromorphic function
field, and it is the exact hypothesis the transcendence-degree computation of cards 11–12 consumes.

The transport uses only corpus material — no new analysis:

* `AlgebraAdjoinAlgebraic.isAlgebraic_algebraAdjoin_of_isAlgebraic_intermediateField` turns
  algebraicity over the generated *field* into algebraicity over the generated *ring*, so no
  denominators have to be cleared;
* `Algebra.adjoin_range_eq_range_aeval` presents each coefficient as an `MvPolynomial (Fin (n+2)) ℂ`
  in the generators — which is exactly the shape of the analytic theorem, because the base is `ℂ`
  and the coordinate is one of the generators;
* `AnalyticMeroPolynomialEval` (`analyticMeroElement_eval_mvPolynomial`,
  `analyticMeroElement_finsetSum`, `analyticMeroElement_eq_zero_iff`) converts the field identity
  into the pointwise identity and back.

Working over `ℂ` rather than `RatFunc ℂ` is what makes the transport short; the two normalisations
differ by exactly one transcendence degree (`trdeg ℂ (RatFunc ℂ) = 1`), so a statement
`H = 1 + S` is the same in both.

### Remaining for card 12 (and the same shape for 11, 13, 14)

1. ~~**The degree increment.**~~ **CLOSED (2026-08-30)** —
   `HTGeometry.CompositionJetTrdeg.trdeg_adjoin_comp_eq_add_one`:

   ```text
   trdeg ℂ (adjoin ℂ (insert (f∘g) (range (jetGen hg n))))
     = trdeg ℂ (adjoin ℂ (range (jetGen hg n))) + 1
   ```

   unconditional and axiom-clean.  Three things made it go through: the general
   `AdjoinInsert.adjoin_insert_eq_restrictScalars` had to live in a module *without* the
   `relativeGauge*` local instances (inside the heavy module every attempt timed out at `isDefEq`);
   the singleton has to be presented as `Set.range (fun _ : PUnit => x)` so that
   `ProjectiveHorizonAllRankQSystem.adjoin_range_lift_eq_top` applies on the nose; and
   `synthInstance.maxHeartbeats` has to be raised, since the meromorphic-field instance stack is
   deep.
2. **The jet equivalence.**  `adjoin ℂ ({z} ∪ h-jets)` and `adjoin ℂ ({z, h} ∪ g-shadow)` are
   algebraic over one another:
   * forward: `h⁽ᵏ⁾` is a polynomial in `f⁽ⁱ⁾∘g` and `g⁽ʲ⁾` (chain rule, induction on `k`), and each
     `f⁽ⁱ⁾∘g` is algebraic over `ℂ(h, f'∘g)` — differentiate the autonomy relation `P(f,f') = 0`;
   * backward: `g' = h'/(f'∘g)`, then `g''` from `h'' = (f''∘g)(g')² + (f'∘g)g''`, and so on.
   Both directions need a *minimal-degree* choice of the autonomy polynomial so that `∂P/∂Y` does
   not vanish on the solution.

   The clean Lean route for the forward half avoids Faà di Bruno entirely: in the differential field
   `meroField univ` let `R_m` be the `ℂ`-subalgebra generated by `{f⁽ⁱ⁾∘g : i ≤ m} ∪ {g⁽ʲ⁾ : j ≤ m}`.
   Since `(f⁽ⁱ⁾∘g)′ = (f⁽ⁱ⁺¹⁾∘g)·g′` and `(g⁽ʲ⁾)′ = g⁽ʲ⁺¹⁾`, `Algebra.adjoin_induction` gives
   `x ∈ R_m → x′ ∈ R_{m+1}`, and `h⁽ᵏ⁾ ∈ R_k` follows by induction on `k`.  The field derivation
   agrees with the ordinary derivative on entire elements by
   `MeroExponentialGauge.deriv_analyticMeroElement`.
3. **Assembly**: `H_h(n) = 1 + S_g(n)`, then the DA order law, the compression ledger, and the
   `E, G, H = exp∘G` counterexample (the last needs: no rational solution of `r' − 2zr = 1`, which
   is an elementary pole/degree argument).

The corpus already owns the abstract staircase these feed
(`DerivativeShadowStaircase`, `trdeg_eq_add_one_of_transcendental`, `trdeg_eq_of_isAlgebraic`,
`StateFieldTrdeg`), so item 2 is the only genuinely new mathematics left in cards 11–12.

## Card 12: the forward half of the jet equivalence (2026-08-30)

`HTGeometry/CompositionJetRing.lean`, unconditional and axiom-clean:

| Statement | Lean name |
|---|---|
| `(f⁽ⁱ⁾∘g)′ = (f⁽ⁱ⁺¹⁾∘g)·g′` in the meromorphic field | `deriv_compJetElem` |
| `(g⁽ʲ⁾)′ = g⁽ʲ⁺¹⁾` | `deriv_jetElem` |
| the `ℂ`-subalgebra of index at most `m` | `compJetRing` |
| **one differentiation raises the index by one** | `deriv_mem_compJetRing_succ` |
| **`(f∘g)⁽ᵏ⁾` lies in the ring of index at most `k`** | `jetElem_comp_mem_compJetRing` |

`deriv_mem_compJetRing_succ` is proved by `Algebra.adjoin_induction`; the two generator cases are the
chain rule and the index shift, and the ring cases are `deriv_add'`/`deriv_mul'` from
`DeltaStructureLinearOde` — the corpus forms that avoid the `Algebra ℤ` diamond that
`Derivation.map_add` runs into on the Ore-localised meromorphic field.

This is the forward half of card 12's jet equivalence, and it needs no Faà di Bruno formula: only
that the ring is carried into the next one by the derivation.

### What card 12 still needs

* **(a)** `f⁽ⁱ⁾∘g` is algebraic over `ℂ(h, f′∘g)`: compose the autonomy relation `P(f,f′) = 0` with
  `g`, then differentiate it repeatedly.  Needs `P` of minimal `Y`-degree so that `∂P/∂Y` does not
  vanish on the solution.
* **(b)** the backward direction: `g′ = h′/(f′∘g)`, then `g″` from
  `h″ = (f″∘g)(g′)² + (f′∘g)g″`, and so on — each `g⁽ʲ⁾` algebraic over the `h`-jet field with `f′∘g`
  adjoined.
* **(c)** assembly: `trdeg` is unchanged by algebraic extensions (`trdeg_eq_of_isAlgebraic`), so
  (a)+(b)+`trdeg_adjoin_comp_eq_add_one` give `H_h(n) = 1 + S_g(n)`; then the DA order law, the
  compression ledger, and the `E, G, H = exp∘G` counterexample.

## Card 12: the autonomy relation composes (2026-08-30)

`HTGeometry/MeroTranscendentalConstants.lean` and `HTGeometry/AutonomousCompJet.lean`, both
unconditional and axiom-clean:

| Statement | Lean name |
|---|---|
| univariate polynomial evaluation transfers to the field | `aeval_analyticMeroElement_polynomial` |
| **a nonconstant entire function is transcendental over `ℂ`** | `transcendental_analyticMeroElement_of_nonconstant` |
| `f′` algebraic over `ℂ(f)`, as an explicit relation | `AutonomousFirstOrder` |
| **`f′∘g` is algebraic over `ℂ(f∘g)`** | `isAlgebraic_compJetElem_one` |

The transcendence lemma is the one place where the plane's uncountability is used: a polynomial
relation over `ℂ` forces every value of the function into the finite root set, each level set is
countable unless the function is constant there (`ZeroFreeRadius.countable_zeroSet`), and a finite
union of countable sets is not `ℂ`.

`isAlgebraic_compJetElem_one` is `AutonomousFirstOrder f` composed with `g`: the relation
`∑ c_k(f)·(f′)^k = 0` becomes `∑ c_k(f∘g)·(f′∘g)^k = 0`, whose coefficients `c_k(f∘g)` lie in
`Algebra.adjoin ℂ {f∘g}` and are nonzero for the index where `c_k ≠ 0`, by the transcendence lemma.

### Still open on card 12

* ~~the induction `f⁽ⁱ⁾∘g` algebraic over `ℂ(h, f′∘g)`~~ **CLOSED (2026-08-30)** —
  `AutonomousCompJetAll.isAlgebraic_compJetElem_of_autonomous` proves the stronger statement that
  *every* `f⁽ⁱ⁾∘g` is algebraic over `ℂ(f∘g)` alone.  The device is the **pullback derivation**
  `x ↦ x′/g′`, installed as a local `Differential` instance, for which `f⁽ⁱ⁾∘g ↦ f⁽ⁱ⁺¹⁾∘g`; the
  generator's image is `f′∘g`, algebraic by `isAlgebraic_compJetElem_one`, so
  `AlgebraicClosureDerivationClosed.deriv_mem_algebraicClosure` applies and the relative algebraic
  closure of `ℂ(f∘g)` contains the whole composed jet.  No minimal-degree bookkeeping is needed —
  the minimal polynomial argument is already inside the corpus lemma.

  Two instance traps: `c⁻¹ • Differential.deriv` must be written *without* ascribing the
  `Derivation ℤ` type (ascription picks `OreLocalization.instAlgebra` where the class provides
  `Ring.toIntAlgebra`), and the membership `y ∈ ⊥` must be cleared before
  `IntermediateField.adjoin_induction` or it lands in the motive.
* ~~the backward direction recovering `g⁽ʲ⁾` from the `h`-jets and `f′∘g`~~ **CLOSED (2026-08-30)** —
  `CompositionJetBackward.isAlgebraic_jetElem_over_compJets`: for `1 ≤ j ≤ n`, `g⁽ʲ⁾` is algebraic
  over the field generated by `f∘g, (f∘g)′, …, (f∘g)⁽ⁿ⁾`.  Supporting:
  `compJetElem_one_ne_zero` (`f′∘g ≠ 0`, by the open-mapping dichotomy),
  `gradedJetRing` with `deriv_mem_gradedJetRing_succ`, and
  `jetElem_comp_sub_mem_gradedJetRing`, the leading-term identity
  `(f∘g)⁽ʲ⁺¹⁾ − (f′∘g)·g⁽ʲ⁺¹⁾ ∈ R_j`.  The graded ring must exclude `g` itself from its generators —
  `g` is exactly the state the primitive defect measures, and it is not recoverable.  The original
  route sketched below is what was carried out:
  with `R_m` the ring generated by the composed jets and the `g`-jets of order at most `m`,
  `h⁽ʲ⁾ − (f′∘g)·g⁽ʲ⁾ ∈ R_{j−1}` by induction — differentiating `a·g⁽ʲ⁾ + r` gives
  `a·g⁽ʲ⁺¹⁾ + (a′g⁽ʲ⁾ + r′)` and `r′ ∈ R_j` by `deriv_mem_compJetRing_succ`.  Solving for `g⁽ʲ⁾`
  needs `f′∘g ≠ 0`, which follows from the open-mapping dichotomy exactly as in
  `meromorphicOrderAt_comp_sub_const_ne_top`;
* the assembly through `trdeg_eq_of_isAlgebraic` and `trdeg_adjoin_comp_eq_add_one`, then the DA
  order law, the compression ledger, and the `E, G, H = exp∘G` counterexample.

## Card 12: the finite-jet shadow law is proved (2026-08-30)

`HTGeometry/CompositionShadowLaw.lean`, unconditional and axiom-clean:

```text
trdeg_shadow_law :
  f, g entire, neither a polynomial, f∘g and g nonconstant, AutonomousFirstOrder f →
  trdeg ℂ ℂ(z, f∘g, (f∘g)′, …, (f∘g)⁽ⁿ⁾)
    = trdeg ℂ ℂ(z, g′, …, g⁽ⁿ⁾) + 1
```

This is the card's `H_h(n) = 1 + S_g(n)`.  The `ℂ`- and `ℂ(z)`-normalisations differ by exactly one
degree on both sides, so the identity is the same in either.

The assembly is the two halves plus two general field lemmas:

| Step | Lean name |
|---|---|
| `h` is transcendental over the shadow field | `not_isAlgebraic_comp_over_jetGen` |
| a transcendental generator costs one degree | `CompositionJetTrdeg.trdeg_adjoin_insert_eq_add_one` |
| mutually algebraic fields have equal degree | `TrdegMutuallyAlgebraic.trdeg_eq_of_mutually_algebraic` |
| outer jets ⊆ graded ring (no `g`) | `jetElem_comp_mem_gradedJetRing` |
| composed jets algebraic over `ℂ(h)` | `isAlgebraic_compJetElem_of_autonomous` |
| inner jets algebraic over the outer jet field | `isAlgebraic_jetElem_over_compJets` |

`trdeg_eq_of_mutually_algebraic` goes through the relative algebraic closures — two intermediate
fields each algebraic over the other have the same closure, and
`StateFieldTrdeg.trdeg_algebraicClosure_restrictScalars_eq` says the closure does not change the
degree.  Both closures must be compared after `restrictScalars`, since as intermediate fields they
live over different bases.

### Card 12 after the shadow law

Still to formalise for promotion:

* the **DA order law** `ord_DA(f∘g) = 1 + ord_DA(g′)` — the union of the finite-jet identities, via
  `DifferentialTranscendenceDegree.differentialTranscendenceDegree` and
  `DifferentialAdjoinFiniteTrdeg`;
* the **compression ledger** `ord_DA(h_N) = ord_DA(g) + N − ∑ π(h_k)`, a corollary of the order law;
* the **entire counterexample** `E = exp(−z²)`, `G = ∫E`, `H = exp∘G` with `ord_DA G = ord_DA H = 2`,
  whose only nonstandard ingredient is that `r′ − 2zr = 1` has no rational solution — an elementary
  pole/degree argument;
* the closing "same scalar order, opposite cap behaviour" comparison.

## Card 12: the order law, the defect dichotomy and the ledger (2026-08-30)

The finite-jet shadow law is now extended to the full jet field and to its two stated corollaries.

New modules:

- `HTGeometry/AdjoinDirectedUnion.lean` — general field theory, no analysis:
  `adjoin_iUnion_eq_iSup`, `directed_adjoin_of_monotone`, `exists_stage_mem`, and
  `exists_isAlgebraic_stage`: an element algebraic over the field generated by an increasing union
  of generating sets is already algebraic over the field generated by one stage.  The witnessing
  polynomial has finitely many coefficients, each lies at a finite stage, the stages are directed,
  and the polynomial is then lifted through `Polynomial.lifts` along `IntermediateField.inclusion`.
- `HTGeometry/CompositionShadowLawInfinite.lean` — `coordElem`, `jetGen_zero_eq_coordElem`, and
  `trdeg_shadow_law_infinite`: for `f` autonomous first-order and both factors transcendental
  entire non-polynomials with nonconstant composition,
  `trdeg_ℂ ℂ(z, all jets of f∘g) = trdeg_ℂ ℂ(z, all positive derivatives of g) + 1`.
  This is the card's DA order law `ord_DA(f∘g) = 1 + ord_DA(g')` in the ℂ-normalisation
  (`trdeg_ℂ = ord_DA + 1`, which avoids cardinal subtraction).
  Only the transcendence step needs the limit: mutual algebraicity holds stage by stage and
  therefore for the union directly.
- `HTGeometry/CompositionShadowLawConsequences.lean` —
  `trdeg_adjoin_insert_eq_of_isAlgebraic` (algebraic generator costs nothing; the companion of
  `trdeg_adjoin_insert_eq_add_one`), `daRank`, `shadowRank'`, `jetSet_eq_insert`,
  `daRank_eq_shadowRank_or_succ` (**the primitive defect is 0 or 1** — Attack item 2),
  `daRank_comp` (the order law in rank form), `compression_ledger`
  (`daRank(h_N) + ∑_{k<N} defect k = daRank(h_0) + N`, the card's compression ledger as a cardinal
  identity), and `trdeg_jetField_comp_of_algebraicIndependent` (**the HT consequence**: if the
  coordinate and `g',…,g^{(n)}` are algebraically independent then the jets of `f∘g` up to order `n`
  give transcendence degree `n+2`, i.e. `H_{f∘g}(n) = n+1` over `ℂ(z)`).

All axiom-clean (`propext, Classical.choice, Quot.sound`), all wired into `HTGeometry.lean`.

Trap recorded: `rw` with the corpus lemma
`trdeg_intermediateFieldAdjoin_range_eq_cardinalMk_of_algebraicIndependent` fails against a
syntactically identical goal in the `meroField` setting (the local `relativeGauge*` instances make
the `Algebra ℂ (meroField univ)` instance differ invisibly).  Deriving the equation from the
hypothesis and finishing with `Eq.trans` works.

Remaining on card 12 (all in the counterexample sections):

1. `ord_DA(exp(−z²)) = 1`, `ord_DA(G) = 2` for `G = ∫₀^z exp(−t²)dt`, `ord_DA(exp∘G) = 2`.
   The only hard step is `G` transcendental over `ℂ(z, E)`, `E = exp(−z²)`.  The route is the
   classical Liouville argument, which factors into:
   (α) `E` transcendental over `ℂ(z)`;
   (β) the derivation on `ℂ(z)[E]` with `E′ = −2zE` (degree preserving, leading coefficient
       `a_d′ − 2zd·a_d`);
   (γ) `b′ = λ z b` has no nonzero rational solution for `λ ≠ 0` (kills all denominators: a monic
       denominator `B` of `E`-degree `m` satisfies `B | B′` and `B′ + 2mzB` has smaller degree);
   (δ) `r′ − 2zr = 1` has no rational solution (pole/degree argument);
   (ε) the algebraic-to-rational descent: if `y` is algebraic over a differential field `K` and
       `y′ ∈ K`, then `(y + a_{n−1}/n)′ = 0` where `a_{n−1}` is the next-to-leading coefficient of
       the minimal polynomial — differentiate the minimal polynomial and use minimality.  Combined
       with "the constants of the meromorphic field of the plane are `ℂ`", this gives `y ∈ K`.
   None of (α)–(ε) is owned by the corpus (searched: Liouville criterion, hyperexponential integral,
   Laurent structure of exponential extensions, minimal-polynomial derivative descent).
   `AlgebraicPrimitiveDescent` has the *difference*-field analogue and the reusable
   `nextCoeff_taylor_of_monic`; `ScalarAdditiveDifferentialTorsor` handles only the HT case.
2. `A(z) = exp(z) + sin(z)`: `ord_DA(A) = ord_DA(A′) = 2`, defect `0`, so `ord_DA(exp∘A) = 3`.
   Needs: `exp(z)` and `exp(iz)` algebraically independent over `ℂ(z)` (the corpus owns
   exponential-independence machinery — check `ExponentialRationalShadow` / Ax–Schanuel lane).
3. The nonautonomous cap `B(w) = w exp(w)` giving `ord_DA(B∘G) = 3`.

## Card 12: the Liouville layer for the Gaussian counterexample (2026-08-30)

Four new modules, all axiom-clean, all wired into `HTGeometry.lean`:

- `HTGeometry/RationalLinearCoefficientNoSolution.lean` (namespace `GaloisForLFunctions.RationalShadow`)
  — `ratFuncCoordinateDerivation_affine_cross`, `degree_wronskian_lt`,
  `eq_zero_of_deriv_eq_linear_mul` (`z′ = c·t·z`, `c ≠ 0`, forces `z = 0`) and
  `not_deriv_eq_linear_mul_add_one` (`z′ = c·t·z + 1` has no rational solution).
  The homogeneous case is a degree count; the inhomogeneous case needs `denom ∣ denom′`, hence a
  constant denominator, and then a degree count.  Helpers `lt_one_add_self_of_ne_bot`,
  `zero_le_of_ne_bot`, `zero_lt_one_add_of_ne_bot` for `WithBot ℕ` — `le_add_self` is unavailable
  there (no `CanonicallyOrderedAdd` instance) and `norm_cast` does not see through `1 + ↑n`;
  `WithBot.add_lt_add_right` and `Nat.WithBot.lt_zero_iff` are the working tools.
- `HTGeometry/MeroFieldConstants.lean` — `exists_complex_of_deriv_eq_zero`: **the constants of the
  meromorphic field of the plane are `ℂ`**.  Write the element as `a/b` with entire germs,
  differentiate the cleared identity, and feed the resulting vanishing Wronskian to the corpus's
  `exists_constant_of_quotientWronskian_eq_zero` (`MeromorphicTranslationFixedField`).
- `HTGeometry/HyperexponentialTranscendence.lean` — `coeff_X_mul_derivative`,
  `eq_zero_of_coeffs_mem_of_natDegree_lt`, and `transcendental_of_hyperexponential`: if `D t = u·t`
  with `u ∈ K` and no nonzero `w ∈ K` solves `D w = k·u·w` for any `k ≥ 1`, then `t` is
  transcendental over `K`.  Differentiating the minimal polynomial gives a second annihilator of the
  same degree with leading coefficient `n·u`; minimality forces every lower coefficient to solve an
  excluded equation, so the minimal polynomial is `X^n`.
- `HTGeometry/HyperexponentialPrimitive.lean` — `exists_coprime_monic_repr` (coprime monic-denominator
  representation in a simple transcendental extension, via Bézout for `EuclideanDomain.gcd`),
  `restrictDerivation`, `twistPoly`, `coeff_twistPoly`, `deriv_aeval_eq_aeval_twistPoly`, and
  **`not_deriv_eq_of_hyperexponential`**: under the same homogeneous hypotheses plus "no `w ∈ K`
  with `D w + u·w = 1`", no element of `K(t)` has derivative `t`.

Key corpus assets found rather than rebuilt: `DerivationAlgebraicDescent.derivMapCoeffs`,
`derivation_aeval_eq`, `mem_of_isAlgebraic_of_derivation_mem` (algebraic + derivative in the base ⇒
in the base — exactly Liouville's descent step), and
`MeromorphicTranslationFixedField.exists_constant_of_quotientWronskian_eq_zero`.
Mathlib asset found: `Differentiable.isExactOn_univ` (`Mathlib/Analysis/Complex/HasPrimitives.lean`)
— **every entire function has an entire primitive**, which is how the Gaussian primitive `G` gets
constructed without any power-series or contour work.

Traps recorded:
- `GCDMonoid K[X]` is not an available instance, so `isCoprime_div_gcd_div_gcd` cannot be used;
  `EuclideanDomain.gcd` with `gcd_eq_gcd_ab` (Bézout) gives coprimality directly.
- `rw` with `r = gcd r s * A₀` rewrites the `r` inside `gcd r s` as well; obtain the gcd and its
  Bézout coefficients as opaque local variables before any rewriting.

Remaining for the counterexample: assemble the three abstract theorems in the meromorphic field —
a `Derivation ℂ` upgrade of the corpus `Differential`, the rational subfield as an
`IntermediateField ℂ`, derivation-closedness of `ℂ(z, E)`, and then the two rank computations.

## Card 12 — autonomous-cap-derivative-shadow-law — DONE (2026-08-30)

Everything the card proves is now Lean, unconditional and axiom-clean.  Nine new modules, all wired
into `GaloisForLFunctions.HTGeometry`:

- `GaussianExponentialField` — `ratField` (the rational subfield of `meroField univ`),
  `meroComplexDerivation`, the Gaussian exponential `E = exp(−z²)` and `E′ = −2z E`.
- `GaussianPrimitiveTranscendence` — `E` transcendental over `ℂ(z)`; a primitive `G` of `E`
  (from mathlib's `Differentiable.isExactOn_univ`) transcendental over `ℂ(z, E)`.
- `GaussianOrderLedger` — `daRank G = 3`, `shadowRank G = 2`, primitive defect one.
- `ExponentialCapNonAdditivity` — `exp` is autonomous first order, `daRank exp = 2` with defect
  zero, `daRank (exp ∘ G) = 3`, and `order_not_additive_expGauss`.
- `RotatedExponentialIndependence` — Artin shortening (corpus `eq_zero_of_sum_expLike_eq_zero`)
  plus the new rational obstruction `eq_zero_of_deriv_eq_const_mul` gives algebraic independence of
  `exp z` and `exp (i z)` over `ℂ(z)`, hence `trdeg_ℂ ℂ(z, exp z, exp iz) = 3`.
- `SumExponentialSineOrderLedger` — `A = exp + sin` has jet field = shadow field =
  `ℂ(z, exp z, exp iz)`, so `daRank A = shadowRank A = 3`, defect zero.
- `AutonomousCapCostComparison` — polynomials have rank one, hence `not_exists_poly_of_daRank_ne_one`;
  `daRank (exp ∘ A) = 4`; equal rank with different cap cost.
- `GaussianExponentialCompositionField` — Clunie (corpus `not_isAlgebraic_comp_over_jetGen`) gives
  `Y = exp G` transcendental over the jet field of `G`; `trdeg_ℂ ℂ(z, E, G, Y) = 4`.
- `NonautonomousCapGaussian` — the recovery chain `q G = E(1+G)`, `q′ + 2zq = −(q−E)²`,
  `(q′+2zq)(1+G)² = −q²` makes `G`, `E`, `Y` algebraic over `ℂ(z)⟨Q⟩` for `Q = G exp G`, so
  `daRank Q = 4`: breaking autonomy restores the compressed state.

Reusable assets produced on the way: `eq_zero_of_deriv_eq_polynomial_mul` /
`eq_zero_of_deriv_eq_const_mul` (rational logarithmic-derivative obstructions),
`derivationClosed_jetField`, `isAlgebraic_of_quadratic_mem`, `not_exists_poly_of_daRank_ne_one`,
`transcendental_coordElem`, `coordElem_mem_ratField`, `iteratedDeriv_polynomial`.

Two environment traps worth remembering:

- `rw` fails on goals that print identically to a lemma's LHS (invisible instance mismatch in the
  `meroField` tower).  Deriving the equation as a hypothesis and finishing with `exact`/`.trans`
  plus `congrArg (fun c : Cardinal => c + 1)` works.
- `ring`/`linear_combination` fail on a goal produced by `refine <lemma> (a := …) … ?_` for the same
  reason.  State the polynomial identity as its own theorem and pass it to the lemma by `exact`.

## Card 11 — first-order-composition-two-defect-decomposition — DONE (2026-08-30)

Eight new modules, all wired into `GaloisForLFunctions.HTGeometry`:

- `CompositionJetFieldTranscendence` — Clunie transcendence of `f ∘ g` over the *whole* jet field of
  `g` (directed union of the finite stages) and over the shadow field.
- `CompositionPairIndependence` — `(f ∘ g, g)` algebraically independent over `ℂ`; the coefficient
  principle `eq_zero_of_sum_aeval_mul_pow`; the reusable
  `isAlgebraic_of_finsetSum_relation`.
- `FirstOrderCompositionRelation` — `FirstOrderDA`, the row decomposition, and the substituted
  relation transported into the meromorphic field.
- `CompositionRelativeVisibility` — `deriv_isAlgebraic_of_generators`, `forall_isAlgebraic_jetElem`,
  and the collapse `trdeg N = trdeg K + 1` whenever `h′` is algebraic over `K(h)`; the autonomous
  case via the corpus `isAlgebraic_compJetElem_one`.
- `FirstOrderCompositionDefect` — the analytic input `exists_ne_zero_comp` (a nonzero entire
  function composed with a nonconstant entire function is nonzero, by countability of zero sets),
  the algebraicity of `f′ ∘ g` over any field seeing `g` and `h`, and the nonautonomous case
  `trdeg N = trdeg K + 2`.
- `TwoDefectDecomposition` — `relTrdeg`, the tower formula, the three two-defect identities, and
  `shadowLoss_eq_zero_of_autonomous` (hence the autonomous cap law again).
- `RelativeVisibilityDegree` — the card's own relative statements `trdeg_K N = 1` and `= 2`, proved
  by transporting the mutual-algebraicity data along `IntermediateField.extendScalars`.
- `NonautonomousCapShadowLoss` — `λ = 0` for `w exp w` on the Gaussian primitive.

Note on cardinals: `Cardinal` has no subtraction and no cancellation, so the card's
`ord_DA(h) = ord_DA(g′) + 1 + (1−aut)π − λ` is formalized additively as
`daRank h + λ = shadowRank g + 1` (resp. `+ 2`), together with the genuinely relative statements
`relTrdeg (K ≤ N) = 1` (resp. `2`), which do not follow from the additive form when `trdeg_ℂ K` is
infinite — the hypertranscendental stratum.

## Card 16 in progress (2026-08-30): Theorems 1 and 2 closed

**The Ostrowski gate (I8) is closed without importing Ostrowski.**  The corpus already owns Mahler
coefficient-field confinement:
`MahlerCoefficientFieldConfinement.exists_forall_coefficientsIn_of_integer_ordinaryADE` together with
`FormalMahlerIntegerNormalization.exists_integer_jet_relation_of_formalRelation` gives, for any
nonzero formal ADE relation, a cutoff `N` valid over *every* intermediate coefficient field.  Taking
`K = ℚ(a₀,…,a_N)` confines all coefficients to a finitely generated field, and a finitely generated
field has finite transcendence degree — which is exactly what the card needs.  The Dirichlet-series
form of Ostrowski is never required.

New modules (all wired into `GaloisForLFunctions.HTGeometry`, axioms = the standard three):

- `IndependentCoefficientHypertranscendence` — `coefficients_mem_adjoin_of_formalRelation` and
  `aeval_formalJets_ne_zero_of_infinite_independent`: a power series with infinitely many
  algebraically independent coefficients satisfies no nonzero algebraic differential equation.
- `PrescribedModulusPhases` — countability of `ℚ`-adjoins inside `ℂ`, uncountability of the circle,
  and `exists_transcendental_scaled`: any nonzero radius carries a unit vector whose scaling is
  transcendental over a prescribed countable field.
- `ModulusPhaseSequence` — the recursive construction `phaseSeq ρ` with `‖phaseSeq ρ n‖ = |ρ n|`,
  each support member transcendental over the field generated by the earlier ones, and
  `algebraicIndepOn_phaseSeq` (independence of every finite support subset, by
  `Finset.induction_on_max` + `AlgebraicIndepOn.insert`).
- `ModulusProfileHypertranscendence` — the entire realization `modulusProfileFunction ρ`
  (`FormalMultilinearSeries.ofScalarsSum`), `norm_taylorPS_modulusProfileFunction` (the prescribed
  magnitudes) and **Theorem 1**: `hypertranscendental_modulusProfileFunction`.
- `FactorialModulusProfile` — **Theorem 2** items 1–2: `factorial_profile_carries_DA_and_HT`
  (`exp` and the phase-randomized `1/n!` series have identical Taylor moduli, one DA and one HT).

Still open on card 16: Theorem 2 items 3–4 (identical maximum-term/Newton data and order/type one),
Theorem 3 (uncountably many divisors on one HT magnitude fiber, via order-zero Hadamard), and the
bridge from the card's root-test hypothesis `limsup ρₙ^{1/n} = 0` to the boundedness form used here.

### Card 16: what is left, and two new infrastructure items

Closed so far: Theorem 1 (with the card's own root-test hypothesis, via
`ModulusProfileHypertranscendence.bounded_of_root_tendsto`), Theorem 2 items 1–2
(`FactorialModulusProfile.factorial_profile_carries_DA_and_HT`) and item 3
(`ModulusDeterminesNewtonData.factorialProfile_newton_data_agree`: equal Taylor moduli give equal
maximum term, equal attaining set, equal central index and equal logarithmic Newton envelope, so all
Newton data — transition radii and plateau widths included — coincide).

Remaining:

| # | Theorem | Missing input |
|---|---|---|
| ~~I16~~ | **CLOSED (2026-08-30)** — `FactorialProfileGrowth.factorialProfile_order_one_type_one`: `‖f z‖ ≤ exp ‖z‖` for both realizations, and on every large circle each exceeds `exp((1−ε)r)` (Cauchy estimate + splitting the exponential series at `2er`, using only `m! ≥ (m/e)^m`) | card 16 Theorem 2 item 4 |
| ~~I17~~ | **CLOSED (2026-08-30)** — `EntireQuotientNormalForm.exists_entire_nonvanishing_quotient` (corpus) plus the new `SqrtStretchedZeroFree.const_of_ne_zero_of_subexponential` | card 16 Theorem 3 |

For Theorem 3 the corpus already owns the HT half:
`StretchedExponentialMagnitudeHypertranscendence.hypertranscendental_stretchedExponentialPhaseFunction`
holds for *every* phase sequence, so the family `θ ↦ (fun n => if n = 0 then t else 0)` is the card's
family; only the divisor-rigidity step is missing.  `FiniteOrderHadamard.exists_polynomial_exp_of_ne_zero_of_growth`
is the zero-free half of it.

### Card 16 Theorem 3: the exact plan (2026-08-30)

The family is corpus-owned: `StretchedExponentialMagnitudeHypertranscendence.sqrtStretchedPhaseFunction θ`
with `ρ n = exp (−exp √n)` and arbitrary phases, and
`hypertranscendental_sqrtStretchedPhaseFunction` gives HT for every `θ`.  Put
`F t := sqrtStretchedPhaseFunction (fun n => if n = 0 then t else 0)`.

Chain to prove:

1. **Order zero.**  `‖F t z‖ ≤ ∑ₙ ρₙ ‖z‖ⁿ` and, for every `ε > 0`, eventually `∑ₙ ρₙ rⁿ ≤ exp (ε r)`.
   Use `exp (√n) ≥ n²/24` (fourth term of the exponential series) so `ρₙ ≤ exp(−n²/24)`; complete the
   square `−n²/24 + n log r = −(n − 12 log r)²/24 + 6 (log r)²`; split at `n ≥ 24(log r + 1)` where the
   terms are `≤ e^{−n}`.  Then `(24 log r + 25)·exp(6 (log r)²) + 2 ≤ exp(ε r)` eventually because
   `(log r)² = o(r)`.
2. **Two phases with the same divisor.**  `F t − F s` is the constant `ρ₀(e^{it} − e^{is}) ≠ 0`;
   `EntireQuotient.exists_entire_nonvanishing_quotient` gives `F t = Q · F s` with `Q` entire and
   nonvanishing, so `(Q − 1)·F s = c` forces `F s` to be **zero-free**.
3. **Hadamard.**  `FiniteOrderHadamard.exists_polynomial_exp_of_ne_zero_of_growth` (growth exponent
   `d = 1` suffices) writes `F s = exp ∘ p`.  The statement carries no degree bound, so use
   Borel–Carathéodory (already inside that module's proof) plus a Cauchy coefficient estimate: from
   `Re p ≤ ε r` on `|z| = r` one gets `|p| ≤ C ε r` on `|z| = r/2`, hence every coefficient of
   positive degree vanishes and `p` is constant.
4. **Contradiction.**  A constant `F s` has vanishing first Taylor coefficient, but that coefficient
   is `ρ₁ ≠ 0`.  Hence distinct phases give distinct divisors, and the phase circle is uncountable.

## Card 16 — fixed-taylor-modulus-newton-geometry-ht-blindness — DONE (2026-08-30)

All three theorems and every listed item are Lean-proved and axiom-clean; the card is in
`3-formalized`.  Ten new modules: `IndependentCoefficientHypertranscendence`,
`PrescribedModulusPhases`, `ModulusPhaseSequence`, `ModulusProfileHypertranscendence`,
`FactorialModulusProfile`, `ModulusDeterminesNewtonData`, `FactorialProfileGrowth`,
`SqrtStretchedGrowth`, `SqrtStretchedZeroFree`, `SqrtStretchedDivisorFamily`.

Reusable assets produced: `aeval_formalJets_ne_zero_of_infinite_independent` (independent
coefficients ⇒ hypertranscendence), `exists_transcendental_scaled` (a transcendental point on any
prescribed circle), `phaseSeq` (prescribed moduli with independent values),
`const_of_ne_zero_of_subexponential` (**a zero-free entire function of order zero is constant** —
Hadamard + Borel–Carathéodory + Cauchy), `newton_data_congr` (equal moduli ⇒ equal Newton data),
`sq_div_le_exp_sqrt`, `term_le_geometric`, `isLittleO_log_sq_id`.

Status after this card: 10 of 22 cards are in `3-formalized` (1–6, 9, 11, 12, 16).

## Route analysis for the twelve remaining cards (2026-08-30)

Cards done: 1–6, 9, 11, 12, 16.  Remaining: 7, 8, 10, 13, 14, 15, 17, 18, 19, 20, 21, 22.

**Card 18 is the closest.**  Its §2 peeling theorem is *already* corpus-owned and abstract:
`HTGeometry.FiniteCommutingShiftPeeling.shiftWord_dichotomy` takes the one-shift dichotomy as a
hypothesis.  What is missing is exactly the ADH one-shift statement

> `f ∈ ℂ((s⁻¹))`, `f(s+h) − f(s) = r ∈ ℂ(s)` ⟹ `f ∈ ℂ(s)` or `f` is HT over `ℂ(s)`.

That is a *telescoping* dichotomy, the exact shape of the corpus's differential Ostrowski criteria
(`ElementaryOstrowski.differentialIndependent_of_no_constant_simultaneous_jet_telescoping`,
`AutomorphismFamilyOstrowski.automorphismFamily_differentialIndependent_of_no_constant_simultaneous_jet_telescoping`),
which is how the q-difference ADH gate was closed for the RG/QFT folder.  The build is:

1. the model: `LaurentSeries ℂ` in the variable `X = s⁻¹` with the automorphism
   `F ↦ F.subst (X / (1 + hX))` (substitution of a power series of order one), a commuting
   derivation, and invariants = constants (a translation-periodic formal Laurent series is constant);
2. feed the criterion; the telescoping branch must be shown to force `f ∈ ℂ(s)`;
3. instantiate `shiftWord_dichotomy` with `R = rational`, `H = HT`, plus the elementary descent
   "`g` DA ⟹ `Δ_h g` DA".

**Card 17** needs Popken's lower bound.  Two of its three inputs are corpus-owned:
`NonlinearMailletUnconditional.exists_isGevreySeries_of_annihilator` (Maillet, for the conjugate
series) and `MahlerCoefficientFieldConfinement.coefficientsConfinedToNumberField_of_formalRelation`
(all coefficients in one number field).  Missing: Pólya–Popken **denominator** control, then the
elementary norm argument `|N(D·a_n)| ≥ 1`.  The denominator bound should come from the same forward
recursion that proves the confinement theorem.

**Cards 7 and 10** need Steinmetz reduction; **13 and 14** need the Newton-corner Puiseux Jacobian
(nothing classical beyond Clunie, but a weighted-initial-form calculus — an iterated Laurent-series
model would carry it); **14 and 15** need Briot–Bouquet; **8** the Valiron–Zimogljad–Strelitz growth
wall; **19** Cartwright/O'Brien; **20** Schwartz surface flows; **21** Hardouin–Singer PPV; **22**
Taubes' Weinstein conjecture.

## Card 17 formalization plan (in progress, 2026-08-30)

`arithmetic-entire-heat-da-finite-spectrum` — the missing classical input is **Pólya–Popken
denominator control**, which the corpus did not own. Mechanism (Mahler's induction, as recalled by
Krattenthaler–Rivoal arXiv:2502.09259): the weight `Δ_q = C^q ∏_{j ≤ q} A_j^{⌊q/j⌋}` is a
denominator for the `q`-th coefficient, where `A_j` is the absolute norm of the `j`-th indicial
value. Floor exponents are superadditive, `⌊i/j⌋ + ⌊i'/j⌋ ≤ ⌊(i+i')/j⌋`, which is exactly what the
convolution in the nonlinear part of the coefficient recursion needs; and `∑_{j≤q} q/j ≤ q(1+log q)`
gives `log Δ_q = O(q log² q) = o(q²)`, which beats the super-Gaussian Cauchy bound `|a_n| ≤ M e^{-n²}`.

Built and wired (all axiom-clean, `lake build` green):
- `HTGeometry/MahlerDenominatorScale.lean` — `mahlerScale`, `mahlerScale_mul_dvd`,
  `mahlerScale_dvd_of_le`, `mahlerScale_succ_dvd`, `sum_div_le_harmonic`, `log_mahlerScale_le`.
- `HTGeometry/AlgebraicDenominator.lean` — `DenBy` API, `exists_denBy`, `rat_isAlgebraic_int`,
  `exists_norm_denominator` (the absolute norm is a denominator for the inverse, of size the
  product of the conjugate moduli).
- `HTGeometry/MahlerDenominatorSeries.lean` — `MahlerDen` (graded: vanishing order `t` plus weight
  `e·Δ_{n-t}`), shift additivity under multiplication, `MahlerDen.aeval`,
  `exists_taylorDefect_const` (the Taylor defect gains two shifts, constant independent of the
  weight data), `boundedDenSubsemiring`.
- `HTGeometry/PolyaPopkenDenominator.lean` — `exists_mahlerDen_of_nondegenerate_eulerADE`: the full
  denominator recursion in the corpus's Euler-jet framework.

Remaining for the card: conjugate Maillet (naturality of the Euler ADE under an embedding of the
coefficient field, then `NonlinearMailletUnconditional`), the Liouville assembly with
`AlgebraicIntegerSeparation.inv_pow_le_norm_embedding`, and the analytic side (super-Gaussian
Cauchy bound; `RGTowerCoherence.differentiallyAlgebraicOn_comp` with the logarithm chart to move
the DA hypothesis from the spatial fibre to the ordinary generating function, then Mahler integer
normalization and `ordinaryToEulerADE`).

### Card 17 CLOSED (2026-08-30)

`arithmetic-entire-heat-da-finite-spectrum` is fully formalized and moved to `3-formalized`.
`arithmetic_heat_finite_spectrum` in `HTGeometry/ArithmeticHeatFiniteSpectrum.lean`; axiom-clean.
The arithmetic parent, **Popken's lower bound** for nonzero algebraic Taylor coefficients of a
differentially algebraic series, is now corpus-owned as
`exists_popken_floor_of_formalRelation` (`HTGeometry/ArithmeticTaylorCoefficientFloor.lean`),
together with its two previously missing inputs: Pólya–Popken denominator control
(`exists_mahlerDen_of_nondegenerate_eulerADE`) and Maillet's bound for all Galois conjugates
(`exists_uniform_conjugate_gevrey`).  Infrastructure item **I17 (Pólya–Popken)** is CLOSED.

Reusable for the other cards of this folder: the graded denominator calculus `MahlerDen`, the
weight `mahlerScale` with its superadditivity and `O(q log² q)` size, the subring-coefficient
calculus `MvCoeffIn`, `exists_integer_euler_ade` (integral nondegenerate Euler normalization), and
the naturality lemma `map_aeval_eulerJetOver` for conjugating formal solutions.

## Card 18 in progress (2026-08-30): the formal Laurent shift model

`finite-commuting-shift-peeling-hypertranscendence-law` — the missing input is the ADH one-shift
dichotomy. Proof route settled (all elementary, no parametrized Picard–Vessiot needed):

1. **Ostrowski.** Instantiate `AutomorphismFamilyOstrowski.automorphismFamily_differentialIndependent_of_no_constant_simultaneous_jet_telescoping`
   with `K = ℂ(s)`, `L = ℂ((s⁻¹))`, `C = ℂ`, one automorphism `σ_h`, `x = f`, `b = r`.  If `f` is DA
   the criterion yields constants `c` and `g ∈ ℂ(s)` with `Δ_h g = ∑_k c_k r^{(k)}`, hence
   `∑_k c_k f^{(k)} - g` is `σ_h`-invariant, hence constant: **`f` satisfies a constant-coefficient
   inhomogeneous ODE `L(δ)f = g̃ ∈ ℂ(s)`.**
2. **Rationality.** Factor `L = (δ-λ)L₁`; it suffices to treat first order.  The cokernel of
   `δ - λ` on `ℂ(s)` splits over the poles (partial fractions), the translation permutes the poles
   freely, and a finitely supported shift-periodic family of pole classes vanishes; so `g̃` is in
   the image and `f` differs from a rational solution by an element of `ker L(δ) ∩ ℂ((s⁻¹))`, i.e.
   by a polynomial.
3. **Peeling.** `FiniteCommutingShiftPeeling.shiftWord_dichotomy` (corpus-owned).

Model built and wired so far (all axiom-clean, `lake build` green):
- `HTGeometry/LaurentShiftAutomorphism.lean` — `shiftSubst h = X/(1+hX)`, the power-series
  automorphism `shiftPS`, its Laurent extension `shiftLaurent`, `shiftLaurent_coordS : σ_h s = s+h`,
  and the chain-rule identity `X² a′ = a²`.
- `HTGeometry/LaurentShiftDerivation.lean` — `d/ds = -X² d/dX` on `ℂ((X))` (`laurentSDifferential`),
  `deriv_coordS : s′ = 1`, and `shiftLaurent_deriv : σ_h ∘ d/ds = d/ds ∘ σ_h`.
- `HTGeometry/LaurentShiftFixedField.lean` — `exists_laurentC_of_shiftLaurent_eq`: the fixed field
  of a nonzero translation is `ℂ` (inversion reduces to the power-series case, where the
  coefficient of `X^{m+1}` in `σ_h B - B` is `-m h b_m`).
- `HTGeometry/RatFuncLaurentShift.lean` — `ratToLaurent : ℂ(s) ↪ ℂ((X))` with `s ↦ X⁻¹`
  (transcendence of `X⁻¹` via `HahnSeries.single`), and `shiftLaurent_ratToLaurent`: the embedding
  intertwines `ratShiftBy h` with `shiftLaurent h`.

Next: the differential-algebra compatibility of the embedding, then steps 1–3.
