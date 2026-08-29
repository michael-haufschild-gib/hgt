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
