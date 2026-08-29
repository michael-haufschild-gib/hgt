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
| ~~I2~~ | ~~Hadamard: zero-free entire of finite order is `exp P`~~ — **already owned**: `HTGeometry.FiniteOrderHadamard.exists_polynomial_exp_of_ne_zero_of_growth` | 3 |
| I3 | Clunie composition growth `T(r, f∘g)/T(r,g) → ∞` | 11, 12, 13, 14 |
| I4 | Briot–Bouquet classification of autonomous first-order meromorphic solutions | 14, 15 |
| I5 | Nevanlinna second main theorem with ramification (≤ 2 totally ramified finite values) | 9 |
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

**What is left of the second main theorem:**

1. **the counting bridge** — `∑ᶠ_u |n_u|^α ≤ ∑ᶠ_u |n_u| = n(R,1/f)` (as `|n|^α ≤ |n|` for `|n| ≥ 1`,
   `α ≤ 1`), and `n(r,1/f)·log(R/r) ≤ N(R,1/f) ≤ T(R,f) + O(1)`, which converts the I11 bound into
   `S(r,f) = O(log⁺T(R,f) + log(1/(R−r)) + log R)`;
2. **the ramification term** `m(r, 1/f')` — absorb via `m(r,1/f') = T(r,f') − N(r,1/f') + O(1)` and
   `T(r,f') ≤ 2T(r,f) + m(r,f'/f) + O(1)`; for a totally ramified family this is what turns
   `N(r,a_j)` into the truncated `N̄(r,a_j) ≤ (1/2)N(r,a_j)` and yields **`q ≤ 2` totally ramified
   finite values for an entire function** (I5), closing card 9.
