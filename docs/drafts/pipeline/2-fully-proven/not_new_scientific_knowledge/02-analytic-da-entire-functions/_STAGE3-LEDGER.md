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
| 15 | nonautonomous-cap-linear-order-two-shadow-rigidity | Briot–Bouquet — bypassed | **DONE → 3-formalized** (2026-09-01) |
| 16 | fixed-taylor-modulus-newton-geometry-ht-blindness | Ostrowski finite basis — replaced by corpus Mahler confinement | **DONE → 3-formalized** (2026-08-30) |
| 17 | arithmetic-entire-heat-da-finite-spectrum | Popken + Mahler normalization | **DONE → 3-formalized** (2026-08-30) |
| 18 | finite-commuting-shift-peeling-hypertranscendence-law | Adamczewski–Dreyfus–Hardouin Thm 1.2 | **DONE → 3-formalized** (2026-08-30) |
| 19 | autonomous-ade-almost-periodic-frequency-rank | Cartwright/O'Brien | **DONE → 3-formalized** (2026-08-31) |
| 20 | first-order-autonomous-algebraic-ap-periodicity | Schwartz surface flows + normalization | TODO |
| 21 | paired-quasi-elliptic-constraint-rigidity | Hardouin–Singer PPV + Cassidy | **DONE → 3-formalized** (2026-08-31) |
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
| ~~I9~~ | **CLOSED (2026-08-30)** — `HTGeometry.ArithmeticTaylorCoefficientFloor.exists_popken_floor_of_formalRelation` | 17 |
| ~~I10~~ | **CLOSED (2026-08-30)** — `HTGeometry.LaurentShiftDichotomy.rational_or_hypertranscendental_of_shift`, proved from the internal Ostrowski criterion and the rational pole obstruction | 18 |
| ~~I11b~~ | **CLOSED (2026-08-31)** — the strict form needs no dimension theory: homogeneity of the hull plus invariance of domain, both corpus-owned | 19 |
| I12 | Schwartz surface-flow trichotomy + curve normalization | 20 |
| ~~I13~~ | **NOT NEEDED** — the card's own collapse theorem reduces the abstract class to the elliptic-gamma logarithmic derivative, whose matroid is already corpus-owned; the paired telescoping never has to be redone | 21 |
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

### Card 18 state (2026-08-30, later)

Steps 1 and the model are done and wired:
- `HTGeometry/RatFuncLaurentDifferential.lean` — `ratFuncSDifferential` (`d/ds` on `ℂ(s)`),
  `deriv_polyToLaurent`, and `deriv_ratToLaurent`: the embedding is a morphism of differential
  fields.
- `HTGeometry/ShiftLaurentOstrowski.lean` — all instances (`Algebra (RatFunc ℂ) (LaurentSeries ℂ)`,
  both scalar-tower forms, `DifferentialAlgebra`), the instantiated Ostrowski criterion
  `hypertranscendental_of_no_telescoper`, and `exists_ode_of_telescoper`: a constant telescoping
  relation for the increment turns the primitive into a solution of a constant-coefficient
  inhomogeneous equation `∑ c_p f^{(p)} = ι g` with rational right-hand side.
- `HTGeometry/ShiftPolePartCalculus.lean` — `polePart_ratFuncDerivative`
  (`polePart (f′) c (d+1) = -d · polePart f c d`) and `polePart_ratFuncShift`
  (`polePart (f(X+a)) c d = polePart f (c+a) d`).

Remaining for the one-shift dichotomy (step 2 of the route above), all elementary:
1. the obstruction functional `Θ^λ_β(u) = ∑_{d≥1} ((-λ)^{d-1}/(d-1)!) polePart u β d`, its
   vanishing on `(δ-λ)(ℂ(s))`, and its transformation `Θ_β(ρ_h u) = Θ_{β+h}(u)`;
2. finite pole support + shift-periodicity ⟹ `Θ ≡ 0`;
3. sufficiency: `Θ ≡ 0 ⟹ u ∈ (δ-λ)(ℂ(s))` by the triangular solve on principal parts (peel the
   top pole coefficient, induct on the pole order);
4. `ker(δ-λ)` inside `ℂ((s⁻¹))` is `0` for `λ ≠ 0` and `ℂ` for `λ = 0` (valuation count);
5. factor a general `L(δ)` into linear factors and induct on the degree; then peel with
   `FiniteCommutingShiftPeeling.shiftWord_dichotomy`.

## Card 18 CLOSED (2026-08-30)

`finite-commuting-shift-peeling-hypertranscendence-law` is fully formalized and moved to
`3-formalized`.  The ADH one-shift dichotomy is now proved inside the corpus rather than assumed:

- `HTGeometry/LaurentShiftKernel.lean` — the corpus Laurent derivation is the explicit coefficient
  operator (`formalLaurentDeriv_eq`), so `(d/ds w)_n = -(n-1) w_{n-1}`
  (`coeff_laurentSDeriv`).  Hence `ker(d/ds) = ℂ` (`exists_laurentC_of_deriv_eq_zero`) and
  `ker(d/ds - λ) = 0` for `λ ≠ 0` (`eq_zero_of_deriv_eq_const_mul`, by leading-order comparison).
- `HTGeometry/LaurentShiftFirstOrder.lean` — `firstOrderLaurentOp`, the translation intertwining
  lemmas, and `exists_ratToLaurent_of_firstOrder`: if `σ_h u = u + ι ρ` and `u′ - λu = ι g` with
  `ρ, g` rational, then `u` is rational.  The translated equation gives
  `ρ_h g - g = (δ-λ)ρ`, so `Θ^λ` is `h`-periodic and finitely supported, hence identically zero, so
  `g` is in the image of `δ-λ` over `ℂ(s)`; the two solutions differ by a kernel element.
  `exists_ratToLaurent_of_opWord` iterates this along a word of first-order factors.
- `HTGeometry/LaurentShiftDichotomy.lean` — `laurentDiffOp`, the evaluation of a complex polynomial
  at `d/ds` in `AddMonoid.End (ℂ((s⁻¹)))`, `exists_opWord_of_polynomial` (factor over `ℂ` and read
  the operator as a word of first-order factors), `exists_ratToLaurent_of_ode`,
  `rational_or_hypertranscendental_of_shift` (the one-shift dichotomy), `shiftSemilinear` (the
  translation as a `DifferentialSemilinearEquiv (RatFunc ℂ) (LaurentSeries ℂ)`, which gives HT
  descent through a shift difference), and the two peeling forms
  `rational_or_hypertranscendental_of_shiftWord` (via `FiniteCommutingShiftPeeling`) and
  `rational_or_hypertranscendental_of_shiftList`.

All axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).

Reusable elsewhere in the folder: the whole `ℂ((s⁻¹))`/`ℂ(s)` differential model (derivation,
translation automorphism, fixed field, embedding), the pole obstruction calculus `Θ^λ`, the
first-order preimage theory over `ℂ(s)`, and `laurentDiffOp` for any constant-coefficient
differential operator argument.

## Route analysis for cards 13 and 14 (2026-08-30, after card 18)

The **model half of the Newton-corner Jacobian is already corpus-owned.**  `ExpAffineCascade`
carries the exact product cascade of both cards:

- `scaledDerivation a` on `MvPolynomial ℕ ℂ` has `scaledDerivation a (X k) = C (scaleWeight a k) *
  ∏_{j ∈ Icc 1 k} X j`, i.e. `δ X_k = (∏_{j<k} a_j) · X_1 ⋯ X_k` — the affine-exponential product
  cascade that both cards use as the Newton-corner initial form;
- `scaled_jet_det_ne_zero` proves its observability Jacobian nonzero;
- `not_differentiallyAlgebraicOfOrder_of_model` transfers a formal model derivation plus the
  analytic law `deriv F_k = evalAt F (δ (X k))` into "no ADE of order below `n`";
- `CascadeExactOrder.exactDifferentialOrder_entireCascade_of_transcendental` then gives the exact
  order once the jet independence is in hand, and `CascadeUpperBound` supplies the upper bound.

So for cards 13 and 14 the **only** missing step is the passage from the true derivative law

`F_k' = ∏_{j≤k} A_j(F_j)`,  `A_j` algebraic over `ℂ(X_j)` with a branch `A_j = λ_j X_j (1+o(1))`
at `X_j = ∞`,

to the model law `δ X_k = (∏ λ_j) X_1 ⋯ X_k`.  Two pieces:

1. **Generalize the model machine.**  `not_differentiallyAlgebraicOfOrder_of_model` is written for
   `MvPolynomial ℕ ℂ`.  The cascade of algebraic exponential-cover maps needs the same statement
   over a ℂ-algebra `R` carrying a derivation and a ℂ-algebra evaluation into the germ field that
   intertwines the derivation with `d/dz` — the finite algebraic extension
   `Frac(ℂ[X_1,…,X_n])(A_1,…,A_n)`.
2. **The Newton-corner transfer.**  Show the Jacobian in that extension is nonzero by comparing with
   the model Jacobian.  The natural formal carrier is the *iterated Puiseux tower*
   `L_0 = ℂ`, `L_k = HahnSeries ℚ L_{k-1}`, with `X_k ↦ t_k⁻¹` and `A_k ↦` its given branch (the
   branch's coefficients are in `ℂ ⊆ L_{k-1}`, so no algebraic-closedness of `L_{k-1}` is needed).
   The corpus already carries derivations on iterated Hahn series (`hahnCoeffMapHom`,
   `hahnGradeHom`, `innerEuler` in `QDifferenceLaurentModel`), which is what `∂/∂X_k` becomes there.
   The leading-form comparison is then a valuation statement inside that tower.

Useful check computed by hand: for `n = 3` and `δ X_k = ∏_{j≤k} A_j(X_j)` the Jacobian is
`J = A_1² A_2 A_3² · (A_1' A_2 A_2'' − A_1' A_2'² − A_1'' A_2')`, which the model
`A_j = λ_j X_j` sends to `−λ_1 λ_2² · A_1²A_2A_3²`.  So the Newton-corner hypothesis enters only
through the leading form, exactly as the card claims.

## Card 21 is much closer than its own Lean note claims (2026-08-30)

`paired-quasi-elliptic-constraint-rigidity`'s "Lean route" paragraph is stale.  The elliptic layer
it calls missing is in fact built and its sibling card
`3-formalized/new_scientific_knowledge/gamma/irrational-elliptic-gamma-hypertranscendence-matroid.md`
is already at stage 3.  Owned and directly reusable:

- `EllipticGammaPairedIncrement` — the genuine elliptic-gamma logarithmic derivative `Ψ` as a
  meromorphic field element, its exact period one, and both mixed faces
  `Δ_σ Ψ = λ_τ`, `Δ_τ Ψ = λ_σ` (recentred);
- `TripticOrbitResidueReciprocity.triptic_orbit_residue_reciprocity` — the card's cited
  orbit-divisor identification, unconditional;
- `EllipticGammaPeriodCosetMatroid`, `EllipticGammaQuotientPeriodCosetMatroid`,
  `EllipticCompositumMatroidTransport`, `EllipticGammaTranslationCosetRankLaw` — the exact
  period-coset partition matroid over the paired compositum *and* over the rational base, i.e.
  the card's §5/§6 spectrum and matroid conclusions;
- `EllipticGammaExternalDefectOstrowski.ellipticGammaExternalDefectFamily_no_simultaneous_jet_telescoping`
  — the paired telescoping obstruction the card derives from Hardouin–Singer/Cassidy;
- `EllipticOrbitQuotient.elliptic_nonresonance_simplePolePair_ne_coboundary` — the orbital-residue
  separator of §5;
- `JacobiThetaDivisorSimple`, `EllipticThetaLogComparison`, `SimplePoleUnit` — the theta
  logarithmic derivative's single simple pole and residue one.

**What is genuinely missing is only the collapse theorem** of the card's §"Collapse theorem":
every simple paired quasi-elliptic primitive is `F = r Ψ(z+a) + C`.  Its three steps are

1. a one-pole rigidity lemma: a meromorphic `U` with `Δ_1 U = 0`, `Δ_τ U` constant and exactly one
   simple pole mod `Λ_τ` equals `r λ_τ(z − p) + const` — because the difference is entire,
   `1`-periodic with constant `τ`-increment, so its derivative is an entire `Λ_τ`-elliptic
   function, hence constant, hence zero;
2. the pole-class identification `p_τ − p_σ ∈ H`, which is `triptic_orbit_residue_reciprocity`;
3. `W = F − r Ψ(z+a)` has all of `1, τ, σ` as periods of `δW`; the group is nondiscrete, so
   `δW` is constant and `1`-periodicity forces `δW = 0`.

Then the card's spectrum theorem is the owned elliptic-gamma matroid transported along
`F = r Ψ(z+a) + C`.  Card 21 is therefore the next target.

### Two new modules towards cards 13/14 and 21 (2026-08-30)

- `HTGeometry/CascadeModelAlgebra.lean` — `DifferentialRealization R δ`, the algebra-valued form of
  `PolynomialCascadeModel`: a family of `ℂ`-algebra evaluations `ev z : R →ₐ[ℂ] ℂ` whose variation
  in the base point is the model derivation.  `ev_jet` identifies the analytic jets with the model
  jets and `not_differentiallyAlgebraicOfOrder_of_realization` forbids every lower-order ADE from
  independence of the model jets.  This is the piece cards 13 and 14 need in order to run the
  corpus's cascade machinery over the *algebraic* state ring `ℂ(X_1,…,X_n)(A_1,…,A_n)` rather than
  a polynomial ring.
- `HTGeometry/PairedQuasiEllipticRigidity.lean` — `const_of_periodic_of_constant_increment`: an
  entire function periodic for one lattice generator and with constant increment along the other is
  constant (its derivative is entire and lattice-invariant, hence constant by elliptic Liouville;
  an entire function with constant derivative is affine and periodicity kills the slope), plus
  `exists_const_sub_of_periodic_of_constant_increment`.  This is the analytic core of card 21's
  one-pole classification step.

Remaining for card 21: (i) formalize "exactly one simple pole with residue `r` mod `Λ_τ`" and show
the difference `U_τ − r λ_τ(· − p)` is entire (corpus assets: `EllipticMeromorphicOrderTools`,
`SimplePoleUnit`, `JacobiThetaDivisorSimple`, `EllipticThetaLogComparison`); (ii) the pole-class
identification via `triptic_orbit_residue_reciprocity`; (iii) assemble the collapse
`F = r Ψ(z+a) + C`; (iv) transport the owned elliptic-gamma matroid along that identification.

### Card 21: steps 1 and 3 of the collapse theorem are built (2026-08-30)

`HTGeometry/QuasiPeriodPoleRigidity.lean` (axiom-clean, wired):

- `HasConstIncrement` and its closure under the `ℤ`-span of a family of steps;
- `meromorphicOrderAt_add_constIncrement` — a step along which a function changes by a constant
  preserves every *negative* order, because adding an analytic function cannot lower a pole order;
- `analyticAt_of_small_constIncrements` — a meromorphic normal form with arbitrarily small
  constant-increment steps has no poles at all (the pole would be moved to itself by arbitrarily
  small steps, contradicting isolation);
- `meromorphicNF_constant_of_rankThree_constIncrements` and its unit-period form
  `const_of_unit_period_of_constIncrements` — **card 21's step 3**: a meromorphic normal form with
  period one and constant increments along `σ` and `τ`, the three steps rationally independent, is
  constant and both increments vanish;
- `const_of_nonneg_order_of_unit_period` — **card 21's step 1**: matching principal parts (all
  orders `≥ 0`) plus period one and a constant `τ`-increment force constancy.

Both rest on `PairedQuasiEllipticRigidity.const_of_periodic_of_constant_increment` and the corpus's
`exists_small_rankThree_periods`.  Step 2 (`triptic_orbit_residue_reciprocity`) is already owned.

What is left on card 21 is the concrete assembly: instantiate step 1 with the theta logarithmic
derivative's single simple pole (`JacobiThetaDivisorSimple.tendsto_thetaLogDeriv_normalized_lattice`
gives the residue in punctured-limit form; it must be converted to a statement about
`meromorphicOrderAt` of the difference), then step 3 with `Ψ = ellipticGammaLogDerivMero`, and
finally transport the owned elliptic-gamma period-coset matroid along `F = r Ψ(z+a) + C`.

### Card 21: the one-pole classification is complete (2026-08-31)

`HTGeometry/PrincipalPartMatching.lean` (axiom-clean, wired) closes card 21's step 1 end to end:

- `HasPrincipalPart f q r` — `f = r/(w−q) + analytic` on a punctured neighbourhood;
- `meromorphicOrderAt_sub_nonneg_of_principalPart` — matching principal parts cancel;
- `nonneg_order_sub_of_matching_principal_parts` — same pole set and same principal parts leave no
  poles anywhere;
- `meromorphicAt_of_hasPrincipalPart`, `meromorphicOn_of_principal_parts`;
- `constIncrement_toMeromorphicNFOn_of_eventually_punctured` — punctured-neighbourhood increment
  identities pass to the entire canonical normal form (the increment analogue of the corpus's
  `periodic_toMeromorphicNFOn_of_eventually_punctured`);
- `const_of_nonneg_order_of_punctured_unit_period` and the packaged
  **`const_sub_of_matching_principal_parts`**: two meromorphic functions with the same pole set, the
  same simple principal part at each pole, punctured period one and punctured constant
  `τ`-increments differ by a constant, and their increments coincide;
- `analyticOrderAt_eq_one_of_simple_zero` and **`hasPrincipalPart_logDeriv_of_simple_zero`** — at a
  simple zero of `θ` the logarithmic derivative `θ′/θ` has principal part exactly `1/(w−q)`.  This
  is the instantiation route for `λ_τ`: the corpus already proves
  `jacobiTheta₂_thetaHalfPeriod_add_lattice_eq_zero` and
  `jacobiTheta₂'_thetaHalfPeriod_add_lattice_ne_zero`, i.e. that every lattice translate of the odd
  half-period is a simple zero of theta.

So all three steps of the collapse theorem are now Lean-proved in reusable form (step 1 here,
step 2 = corpus `triptic_orbit_residue_reciprocity`, step 3 =
`QuasiPeriodPoleRigidity.const_of_unit_period_of_constIncrements`).  What remains is the concrete
wiring: identify `λ_τ`'s pole set as the theta divisor, apply `const_sub_of_matching_principal_parts`
to `U_τ` and `r λ_τ(· − p)`, then step 3 to `F − r Ψ(· + a)`, and transport the owned elliptic-gamma
period-coset matroid along the resulting identity.

### Card 21: the one-pole classification is instantiated at the Jacobi theta source (2026-08-31)

`HTGeometry/ThetaSourceOnePole.lean` (axiom-clean, wired):

- `HasPrincipalPart.const_mul` and `HasPrincipalPart.comp_sub` — scaling and translating a
  principal part, so a comparison object `r · λ_τ(· − p)` is covered;
- `thetaDivisor τ` — the odd half-period orbit;
- `hasPrincipalPart_thetaSource` — the theta source has principal part exactly `1/(w − q)` at every
  divisor point, from the corpus's simple-zero data;
- `analyticAt_thetaSource_of_notMem` — it is analytic off the divisor;
- `eventually_jacobiTheta₂_ne_zero` and `eventually_thetaSource_shift` — the quasiperiod drop
  `λ_τ(z+τ) = λ_τ(z) − 2πi` holds on a punctured neighbourhood of every point;
- **`const_sub_thetaSource_of_matching_principal_parts`** — the card's step 1 at the actual theta
  source: a meromorphic function with the theta divisor as pole set, principal part `1/(w−q)` at
  each pole, punctured period one and a punctured constant quasiperiod increment differs from the
  theta source by a constant, *and its increment is forced to be `−2πi`*.

Card 21's collapse theorem is now reduced to bookkeeping: apply this with `U_τ` (after scaling by
its residue and translating by its pole class), the same for `U_σ`, then
`QuasiPeriodPoleRigidity.const_of_unit_period_of_constIncrements` to `F − r Ψ(· + a)`, and finally
transport the owned elliptic-gamma period-coset matroid.

### Card 21: the germ-level form of step 3 (2026-08-31)

The increments of a meromorphic function are germ identities, so they hold on punctured
neighbourhoods, not pointwise — and a meromorphic *normal form* with a genuine pole cannot satisfy
a pointwise increment identity at all.  `HTGeometry/PuncturedQuasiPeriodRigidity.lean` therefore
redoes step 3 with the hypotheses the actual objects satisfy (axiom-clean, wired):

- `HasPuncturedConstIncrement` with closure under the `ℤ`-span (add / neg / zsmul), using the
  corpus's `TripticGermConstraint.tendsto_nhdsNE_add_const` to transport punctured neighbourhoods;
- `meromorphicOrderAt_add_puncturedConstIncrement` — pole orders are germ invariants, so a punctured
  constant increment still preserves every negative order;
- `analyticAt_of_small_puncturedConstIncrements` — arbitrarily small punctured quasi-periods still
  exclude poles;
- `constIncrement_of_punctured_of_analytic` — once pole-free, punctured identities upgrade to
  pointwise ones by continuity;
- `meromorphicNF_constant_of_rankThree_puncturedConstIncrements` and
  **`const_of_unit_period_of_puncturedConstIncrements`** — the usable form of card 21's step 3.

With `ThetaSourceOnePole.const_sub_thetaSource_of_matching_principal_parts` (step 1 at the actual
Jacobi theta source) and the corpus's `triptic_orbit_residue_reciprocity` (step 2), every
mathematical ingredient of card 21's collapse theorem is now Lean-proved in the germ-level form the
elliptic-gamma objects satisfy.

### Card 21: step 3 inside the meromorphic field, where `Ψ` lives (2026-08-31)

The elliptic-gamma objects are elements of `meroField (Set.univ : Set ℂ)`, so step 3 is now also
proved there, avoiding any germ/function translation.  `HTGeometry/MeroRankThreeIncrementCollapse.lean`
(axiom-clean, wired):

- `addTranslationMeroEquiv_coordElem` — the coordinate germ translates by the step;
- `algebraMap_complex_eq_constToAnalytic`, `addTranslationMeroEquiv_complexConst`;
- `exists_complex_of_rankThree_constIncrements` — an element whose translation increments along
  three rationally independent steps are constants, one of them zero, is a complex constant.  The
  proof: its derivative is fixed by the whole rank-three group, hence constant by the corpus's
  `exists_constant_of_rankThree_translation_fixed`; subtracting that multiple of `coordElem` leaves
  an element with vanishing derivative, hence constant by
  `MeroFieldConstants.exists_complex_of_deriv_eq_zero`; and the exact period kills the coordinate
  coefficient;
- **`exists_complex_of_unit_period_of_constIncrements`** — the packaged form: exact period one plus
  constant `σ`- and `τ`-increments, the three steps rationally independent, force the element to be
  a complex constant *and both increments to vanish*.

This is exactly the last paragraph of the card's collapse proof and its §7 uniqueness statement, in
the ambient field of the already-formalized elliptic-gamma matroid.

### Card 21: the germ/function bridge (2026-08-31)

`HTGeometry/MeroRealizationTransport.lean` (axiom-clean, wired) supplies the missing half of the
corpus's `RealizesMero` calculus — **faithfulness**:

- `eq_zero_of_realizesMero_eventually_zero` — a germ realizing a function that vanishes off its
  poles is zero (the numerator vanishes on a punctured neighbourhood of every point, hence
  everywhere by continuity);
- `realizesMero_algebraMap_complex`, `realizesMero_neg`;
- **`realizesMero_eq_of_eventuallyEq`** — two germs realizing functions that agree off their poles
  are equal.

The rest of the bridge is already owned and was found by search rather than rebuilt:
`AllDepthCarrierJets.realizesMero_thetaLogDerivMero` (`thetaLogDerivMero σ` is realized by
`thetaSource σ`), `EllipticGammaJetRealization` (the elliptic-gamma logarithmic derivative is
realized by an explicit function), `MeromorphicRealizationAlgebra.realizesMero_translate` and
`realizesMero_div`, and `MeromorphicFractionRealization.realizesMero_add/const_mul/sum`.

So card 21's chain is now complete in principle: the function-level one-pole classification
(`ThetaSourceOnePole.const_sub_thetaSource_of_matching_principal_parts`) transports along
`realizesMero_eq_of_eventuallyEq` into a `meroField` identity, which feeds
`MeroRankThreeIncrementCollapse.exists_complex_of_unit_period_of_constIncrements`, after which the
already-formalized elliptic-gamma period-coset matroid transports along the resulting identity.

### Card 21: the capstones (2026-08-31)

`HTGeometry/PairedQuasiEllipticCollapse.lean` (axiom-clean, wired) writes the chain out:

- `eventually_eq_const_of_constant_toMeromorphicNFOn` — a meromorphic function with constant
  canonical normal form agrees with that constant off its poles;
- **`eq_thetaLogDerivMero_add_const_of_matching_principal_parts`** — card step 1 in the meromorphic
  field: a germ realized by a function with the theta divisor as pole set, principal part `1/(w−q)`
  at each pole, punctured period one and a punctured constant quasiperiod increment equals
  `thetaLogDerivMero τ` up to a complex constant, and its increment is forced to be `−2πi`;
- **`exists_complex_sub_of_structural_increments`** — the collapse: a primitive with period one
  whose two structural increments are those of a reference primitive up to constants equals that
  reference up to one complex constant, and both constants vanish;
- **`exists_complex_sub_of_same_increments`** — the card's §7 constraint uniqueness;
- `defect_eq_of_sub_algebraMap` and **`defect_eq_of_structural_increments`** — translation defects
  do not see an additive constant, so such an `F` has *exactly* the same defect family as the
  reference at every shift.  This is the transport that carries the already-formalized
  elliptic-gamma period-coset matroid, shift spectrum and hypertranscendence verbatim to `F`.

The reference primitive is `ellipticGammaLogDerivMero σ τ`, whose hypotheses are supplied by the
owned `addTranslationMeroEquiv_ellipticGammaLogDerivMero_one`,
`ellipticGammaExternalLogDerivDefectMero_sigma` and `..._tau`.  What is left is the τ-face
bookkeeping: that face is the *recentred* σ-theta, so Theorem step 1 needs its translated form
(`HasPrincipalPart.comp_sub` plus `MeromorphicRealizationAlgebra.realizesMero_translate` give it).

## Card 21 CLOSED (2026-08-31)

`paired-quasi-elliptic-constraint-rigidity` is fully formalized and moved to `3-formalized`.

The card's own "Lean route" note was stale by more than a year of corpus work: the elliptic layer it
called missing had been built for the elliptic-gamma cards.  What had to be built was the analytic
rigidity around it — eight new modules:

`PairedQuasiEllipticRigidity`, `QuasiPeriodPoleRigidity`, `PuncturedQuasiPeriodRigidity`,
`PrincipalPartMatching`, `ThetaSourceOnePole`, `TranslatedThetaOnePole`,
`MeroRankThreeIncrementCollapse`, `MeroRealizationTransport`, and the two capstone modules
`PairedQuasiEllipticCollapse`, `SimplePairedQuasiEllipticCollapse`, `PairedQuasiEllipticSpectrum`.

Capstones: `exists_complex_sub_ellipticGammaLogDerivMero` (the collapse theorem),
`exists_complex_sub_of_same_increments` (constraint uniqueness),
`pairedQuasiEllipticPrimitive_differentialMatroid` and `pairedQuasiEllipticPrimitive_eRk` (the exact
spectrum, complete finite-shift matroid and subpacket rank law).  All axiom-clean.

**Infrastructure item I13 (Hardouin–Singer PPV + Cassidy) turned out not to be needed**: the card's
collapse theorem reduces the abstract class to the elliptic-gamma logarithmic derivative, whose
matroid the corpus already owns, so the paired telescoping descent never has to be redone for the
abstract class.

Reusable elsewhere: the whole principal-part calculus (`HasPrincipalPart` with `const_mul`,
`comp_sub`, order-cancellation, and the log-derivative-at-a-simple-zero lemma), the rank-three
quasi-period rigidity in pointwise, germ and `meroField` forms, and — most broadly —
`MeroRealizationTransport.realizesMero_eq_of_eventuallyEq`, which makes the corpus's `RealizesMero`
calculus *faithful* and so lets any identity proved about meromorphic functions be moved into the
global meromorphic differential field.

## Card 19: the non-strict half is already corpus-owned (2026-08-31)

`autonomous-ade-almost-periodic-frequency-rank` is much further along than the status table says.
The card's finite-frequency law is **already formalized**, in exactly the card's hypotheses:

- `AutonomousCarrierRegularity.rank_bohrSpectrum_le_of_strip_differential_equation` — a function
  holomorphic and uniformly almost periodic on a vertical strip satisfying there a nonzero
  autonomous algebraic differential equation of exact order `n` has
  `rank_ℤ ⟨bohrSpectrum⟩ ≤ 2n`;
- `..._of_strip_differential_equation` and `..._of_stripAnnihilator` give the same for the carrier
  character group;
- the machinery underneath is `HullChartFrequencyRank.rank_bohrHullFrequencies_le_of_charts`
  (a finite closed atlas of charts into `ℝ^k` bounds the rank by `k`), Ritt's separant step, and
  the carrier representatives.

**The one remaining gap is strictness**: the card asserts `rank < 2n`, the corpus proves `≤ 2n`.
The card's own consequence — no finite-order regular autonomous ADE generates an infinite
rationally independent spectrum — already follows from the non-strict bound.

Route for strictness (Cartwright/O'Brien).  The jet-at-zero map embeds the hull `X_f` in `ℝ^{2n}`
(injective by ODE uniqueness on the orbit hull, a homeomorphism onto its image by compactness).  If
the rank were exactly `2n` then `dim X_f = 2n`, a compact subset of `ℝ^{2n}` of covering dimension
`2n` has interior, and homogeneity of `X_f` plus invariance of domain make its image clopen in
`ℝ^{2n}`, contradicting compactness.  Both hard inputs exist in the corpus:
`HTGeometry.InvarianceOfDomain.invariance_of_domain_open_map` and the covering-dimension layer
`EuclideanSharpCoveringDimension.hasCoverDimLE_of_isCompact_euclidean`.  What is missing is the
Pontryagin step "covering dimension of a compact connected abelian group = rational rank of its
dual" and "a compact `K ⊆ ℝ^p` with `dim K = p` has nonempty interior".

Note the torus shortcut does **not** work: a rank-`2n` frequency group need not be finitely
generated, so `X_f` need not contain a `2n`-torus — it can be a solenoid.  The dimension-theoretic
argument is the honest one.

### Card 19: the strict rank law is proved, without dimension theory (2026-08-31)

Two new modules (axiom-clean, wired):

- `HTGeometry/HomogeneousEuclideanNoGo.lean` — **`false_of_compact_homogeneous_embedding`**: a
  compact *homogeneous* space cannot both embed in a finite-dimensional Euclidean space `E` and
  receive a continuous injection from a nonempty open subset of `E`.  Proof: invariance of domain
  makes the image of that open patch open; homogeneity carries the patch to every point, so the
  whole image is open; it is also compact hence closed; `E` is connected, so the image is all of
  `E`, contradicting `NormedSpace.noncompactSpace`.
- `HTGeometry/StrictHullFrequencyRank.lean` — `openUnitCube` with its openness and nonemptiness,
  `homogeneous_bohrHull` (the hull is a completion of a topological group, so translation is a
  homeomorphism), **`card_lt_of_hull_global_chart`** (an independent packet of frequencies is
  *strictly* smaller than the dimension of a globally injective chart) and
  **`rank_bohrHullFrequencies_le_pred_of_global_chart`**: a globally injective continuous chart of
  the phase carrier into `ℝ^k` bounds the rational rank of the frequency group by `k − 1`.

The Cartwright/O'Brien strictness therefore needs **no dimension theory at all** — no "covering
dimension of a compact connected abelian group equals the rank of its dual", no "a compact
`K ⊆ ℝ^p` of dimension `p` has interior".  The earlier route note in this ledger is superseded:
homogeneity plus invariance of domain does the whole job, and both were already in the corpus.

Remaining for card 19: build the global jet chart `J : BohrHull f → ℝ^{2n}` from the card's
uniqueness hypothesis (two hull members with the same jet at `0` solve the same autonomous system,
hence coincide), and feed it to `rank_bohrHullFrequencies_le_pred_of_global_chart`.  The non-strict
half is already `AutonomousCarrierRegularity.rank_bohrSpectrum_le_of_strip_differential_equation`.

## Card 19 CLOSED (2026-08-31)

`autonomous-ade-almost-periodic-frequency-rank` is fully formalized and moved to `3-formalized`.
Its own "Lean status" note was stale: the Bohr hull, its character theory, the carrier
representatives and the chart rank bound had all been built for the phase-rank programme, and the
non-strict half was already `AutonomousCarrierRegularity.rank_bohrSpectrum_le_of_strip_differential_equation`.

Three new modules closed the strictness:

- `HTGeometry/HomogeneousEuclideanNoGo.lean` — `false_of_compact_homogeneous_embedding`;
- `HTGeometry/StrictHullFrequencyRank.lean` — `openUnitCube`, `homogeneous_bohrHull`,
  `card_lt_of_hull_global_chart`, `rank_bohrHullFrequencies_le_pred_of_global_chart`;
- `HTGeometry/StrictJetChartFrequencyRank.lean` — `complexJetToReal` with its continuity and
  injectivity, and the capstones `rank_bohrHullFrequencies_le_pred_of_jet_injective`,
  `rank_bohrSpectrum_le_pred_of_jet_injective` (the card's `rank_ℚ Γ(f) < 2n`) and
  `rank_bohrSpectrum_observable_le_pred_of_jet_injective` (the divisor-frequency corollary).

**Neither Takahashi's `dim G = rank dual(G)` nor any covering-dimension theory is used.**  Earlier
in this ledger I recorded the opposite route; that note is superseded.  The whole strictness is:
an independent packet of `2n` frequencies gives a continuous injection of an *open* cube into the
carrier; composing with the global jet chart, invariance of domain makes the carrier's image contain
an open set; homogeneity of the hull moves that patch to every point, so the image is open as well
as compact, hence clopen in the connected `ℝ^{2n}`, hence everything — contradicting
`NormedSpace.noncompactSpace`.

Directly reusable for card 20 (whose statement is the `n = 1` case: rank `< 2` and nonconstant
forces rank exactly one, i.e. periodicity) and for card 22's dimension-four exclusion, which is the
same invariance-of-domain argument.

### Cards 20 and 22: Schwartz and the dimension-four step replaced (2026-08-31)

`HTGeometry/LocallyEuclideanHomogeneousNoGo.lean` (axiom-clean, wired) localizes the Euclidean
obstruction:

- `isOpen_range_of_compact_homogeneous_locally_euclidean` — if a compact homogeneous space embeds in
  a target that is locally Euclidean of dimension `p` along the image, and receives a continuous
  injection from a nonempty open subset of `ℝ^p`, then its image is **open**;
- `false_of_compact_homogeneous_locally_euclidean_proper` — on a connected Hausdorff such target the
  image is then clopen, hence everything, so a *proper* embedding is impossible.

Consequences for the two flow cards:

- **Card 20** cites Schwartz's surface-flow trichotomy to exclude cases (a) and (c).  With this
  lemma the trichotomy is not needed: the hull is compact and homogeneous, an independent pair of
  frequencies injects an open square into it, and the state map lands in a surface, so the image
  would be clopen — while the card's own case-(c) argument already observes that the image *avoids
  the divisor at infinity*, i.e. the embedding is proper.  That is exactly `hproper`.
- **Card 22**'s §4 (real dimension four is impossible) is the same statement: invariance of domain
  plus compactness against a non-compact Stein surface.

What card 20 still needs is the algebraic input feeding the lemma: the normalization of the plane
curve, the lift of the state map, and the regularity of the induced vector field along the hull —
i.e. its §§1–3.  Card 22 still needs its CR/contact layer and Taubes for the dimension-three case;
only the dimension-four branch is now covered.

### Card 10 audit: two of its three ingredients are already owned (2026-08-31)

`entire-composition-hypertranscendence-or-law` needs three things.  Two are corpus theorems:

- **DA is closed under composition** — `RGTowerCoherence.differentiallyAlgebraicOn_comp`
  ("across a faithful substitution the composite of two differentially algebraic germs is again
  differentially algebraic");
- **DA inverse-closure** — `LocalInverseHypertranscendence.differentiallyAlgebraicOn_of_localInverse`
  ("differential algebraicity is inherited by a local analytic inverse"), together with
  `differentiallyAlgebraic_of_differentiallyAlgebraicOn` (for an entire function a relation on one
  nonempty open set is global).

Those two give the card's easy direction *and* its whole **inner-HT half**: if `g` is HT, `f` is DA
and `f ∘ g` is DA, then `g = f⁻¹ ∘ (f ∘ g)` is DA on an open set, hence globally — contradiction.

The single missing ingredient is the **outer-HT half**, i.e. Steinmetz reduction / Huang–Ng
Theorem 3: `f` HT and `g` nonconstant entire imply `f ∘ g` HT.  That is also the missing ingredient
of card 7, so it is the highest-leverage remaining classical build in this folder (two cards).  The
corpus's Nevanlinna stack for it: `SecondMainTheoremChain`, `LogDerivativeProximity`,
`LogDerivPoissonJensen`, `ClunieSeparationBridge`, `ClunieCompositionGrowth`, plus mathlib's
`ValueDistribution` first main theorem.

### Cards 13/14: the weighted transfer, the exact shape the degeneration needs (2026-08-31)

Appended to `HTGeometry/ObservabilityJacobianTransfer.lean` (axiom-clean):

- `map_observabilityJacobian_weighted` — a specialization need not intertwine the derivations on the
  nose.  If `π ∘ δ_R = c · (δ_S ∘ π)` and `π ∘ ∂_R^j = d_j · (∂_S^j ∘ π)` with `c` a
  `δ_S`- and `∂_S`-constant, then the Jacobian transports with entry `(i,j)` scaled by `c^i d_j`;
- **`observabilityJacobian_det_ne_zero_of_weighted_map`** — over a domain, with `c ≠ 0` and every
  `d_j ≠ 0`, a nonzero specialized Jacobian still certifies a nonzero source Jacobian, because the
  row–column rescaling only multiplies the determinant by `(∏ c^i)(∏ d_j)`.

This is exactly the shape the Newton-corner degeneration produces: rescaling `X_j ↦ ε^{-w_j} X_j`
multiplies `∂/∂X_j` by `ε^{w_j}` and the time derivation by a power of `ε`, so the intertwining is
weighted rather than exact.  With this in place the only object still to construct for cards 13 and
14 is the specialization `π` itself into a ring where `A_j` reduces to `λ_j X_j`.

### Cards 7/10: the algebraic half of the Steinmetz application is owned (2026-08-31)

Two corpus theorems already carry the Faà di Bruno step, so the composite-jet expansion does not
have to be built:

- `CompositionJetBackward.jetElem_comp_mem_gradedJetRing` — the `k`-th jet of `f ∘ g` lies in the
  ring generated by the composed outer jets of index at most `k+1` and the inner jets of index
  `1..k`.  This is exactly the expansion `P(z, (f∘g)^{(k)}) = ∑_j (M_j(f)∘g)·H_j(g,z)` that the
  Steinmetz argument starts from;
- `CompositionJetClosure.compJet_mem_differentialAdjoin` — every jet of the outer function lies in
  the differential field generated by the inner function and the composite.

Consequently, when `g` is itself DA, "`f ∘ g` DA" already forces the family `{f^{(j)} ∘ g}` to have
finite transcendence degree over `ℂ(z)`.  **The entire remaining content of Steinmetz reduction is
the coefficient descent**: turning a relation with coefficients in `ℂ(z)` into one with coefficients
in `ℂ(w)`, i.e. small-function Nevanlinna theory.  That is the single unbuilt object for cards 7 and
10, and it is where any future work on them should start.

### Cards 13/14: the specialization, pinned down (2026-08-31)

Working the construction through, the **plain** transfer suffices — the weighted version is not
needed if the target derivation is defined to absorb the scaling.  Concretely:

- target ring `S := (ℂ[X_1^ℚ,…,X_n^ℚ])((ε^{1/N}))` — Laurent series in `ε^{1/N}` over the group
  algebra of `ℚ^n`;
- `π(X_j) := ε⁻¹ X_j`, and `π(A_j) := ε⁻¹ Ā_j` where `Ā_j := λ_j X_j + ∑_{q<1} c_q ε^{1-q} X_j^q`
  is the given Puiseux branch after the substitution `X ↦ X/ε` and multiplication by `ε`.  Each
  coefficient of a fixed power of `ε^{1/N}` is a single monomial `c_q X_j^q`, so `Ā_j` is genuinely
  `ε`-integral with `Ā_j |_{ε = 0} = λ_j X_j`;
- `π` is a `ℂ`-algebra map because the branch satisfies `A_j`'s minimal polynomial;
- define `∂_j^S := ε · (∂/∂X_j)` and `δ_S := ∑_k ε^{-k} (∏_{j≤k} Ā_j) ∂_k^S`.  With these the
  intertwining `π ∘ ∂_j = ∂_j^S ∘ π` and `π ∘ δ = δ_S ∘ π` is **exact**, so
  `observabilityJacobian_det_ne_zero_of_map` applies directly.

What is then left is a single concrete estimate: the determinant of the Jacobian in `S` is
`ε^κ · (model determinant + O(ε^{>0}))`, so it is nonzero because the model determinant is
(`ExpAffineCascade.scaled_jet_det_ne_zero`).  All entries are explicit `ε`-Laurent series, so this
is a bookkeeping computation rather than a new idea — but it is the last unbuilt step, together with
the construction of `S` and its two derivations.

### Cards 13/14: the graded calculus (2026-08-31)

`HTGeometry/LaurentHasLead.lean` (axiom-clean, wired) packages the boundary-coefficient bookkeeping
as a small algebra:

- `HasLead f d c` — `f` vanishes below degree `d` and has coefficient `c` there;
- `hasLead_zero`, `hasLead_one`, `HasLead.mono` (weaken the degree, boundary coefficient becomes
  zero), `HasLead.add`, `HasLead.neg`, `HasLead.sub`, `HasLead.mul` (degrees add, coefficients
  multiply), `HasLead.pow`;
- **`det_ne_zero_of_hasLead`** — if every entry of a matrix satisfies
  `HasLead (M i j) (a i + b j) (L i j)` and `L.det ≠ 0`, then `M.det ≠ 0`.

Because `HasLead` is closed under the ring operations with degrees adding, the boundary coefficient
behaves as a graded ring homomorphism, and cancellation inside an entry is harmless: an entry whose
model value is zero simply has boundary coefficient zero, which is what the model matrix records.
So the Newton-corner degeneration reduces to a finite, purely mechanical computation of
`HasLead` facts for `∂_j (δ^i X_n)`, given `HasLead (A_j) (-w_j) λ_j`-style hypotheses for the
branches.  Nothing analytic remains in that step.

### Cards 13/14: the graded calculus over an arbitrary value group (2026-08-31)

`HTGeometry/HahnLeadingCoefficient.lean` (axiom-clean, wired) generalizes the leading-coefficient
calculus from `LaurentSeries` to `HahnSeries Γ R` for any linearly ordered cancellative value
monoid: `HasLeadAt f d c`, with `hasLeadAt_zero`, `.mono`, `.add`, `.neg`, `.sub`, `.mul`, plus
`coeffAt_mul_eq_zero_of_lt` and `coeffAt_mul_of_vanishing_below`.

This generalization is necessary, not cosmetic.  A several-variable Newton-corner degeneration needs
the coordinate derivations `∂/∂X_j`, and each of those shifts *one component* of the degree while
multiplying the boundary coefficient by that component's exponent.  A single integer degree cannot
record that, so the `ℤ`-graded version of the calculus could never carry the induction; a
multi-graded value group can.  With `Γ = Fin n → ℤ` lex-ordered, the coordinate derivations become
graded operators of known shift, which is exactly the invariant the entry-lead induction needs.

### Cards 13/14: the multi-graded Newton model (2026-08-31)

`HTGeometry/MultiGradedNewtonModel.lean` (axiom-clean, wired) builds the ambient the degeneration
lives in:

- `mgDeg n := Lex (Fin n → ℤ)` — the multi-degree group, which mathlib already equips with
  `AddCommMonoid`, `LinearOrder` and `IsOrderedCancelAddMonoid`, so `HahnSeries (mgDeg n) ℂ` is a
  legitimate Hahn ring;
- `mgComp n j` — the `j`-th exponent as an additive character;
- `mgUnit`, `mgStep`, `mgX n j` — the coordinate `X_j` as a Hahn monomial of multi-degree `-e_j`;
- `mgEuler n j := hahnDerivation (mgComp n j)` — the corpus's general graded derivation, reused
  rather than rebuilt;
- `mgPartial n j := mgShift n j • mgEuler n j` — the `j`-th coordinate derivation (up to a global
  sign the Jacobian criterion does not see), with `coeff_mgPartial` computing its effect on
  coefficients;
- **`hasLeadAt_mgPartial`** — the coordinate derivation shifts the boundary degree by `mgStep n j`
  and multiplies the boundary coefficient by that exponent.

With this the graded invariant is complete: sums, products and coordinate derivatives all act
predictably on `HasLeadAt` data, which is everything the entry-lead induction for
`∂_j (δ^i X_n)` consumes.

### Cards 13/14: what the leading-determinant test actually demands (2026-08-31)

Working the induction through exposes a condition that the earlier route notes glossed over, and it
is worth recording precisely because it is the real remaining content.

`det_ne_zero_of_hasLead` consumes bounds `a i + b j` and the matrix `L` of boundary coefficients, and
needs `det L ≠ 0`.  `det L` is the coefficient of the Jacobian determinant at the single degree
`∑a + ∑b`.  So it is **not** enough that the model determinant be nonzero — what is needed is that
the model determinant have a nonzero coefficient at exactly that degree, i.e. that its Newton
polygon have a unique vertex at the sum of the row and column minima.

Concretely the model derivation `δ_0 X_k = (∏_{j<k} λ_j) X_1 ⋯ X_k` is *not* multi-homogeneous — it
shifts different coordinates by different degrees — so `δ_0^i X_n` is a sum of monomials of several
degrees, and the entries of the model Jacobian are not homogeneous either.  The classical
"choose rapidly increasing rational weights so that the finitely many monomials of `J_n` are
separated" step in the card's own proof is exactly the device that makes the minimum unique.

Evidence that the vertex is indeed unique: at `n = 2` the model determinant is `−λ_1λ_2 X_2` and at
`n = 3` it is `−λ_1³λ_2³λ_3² X_1² X_2 X_3²` — a single monomial in both cases (computed by hand
from the general formula `J = A_1²A_2A_3²(A_1'A_2A_2'' − A_1'A_2'² − A_1''A_2')`).

So the remaining work on cards 13 and 14 is a combinatorial analysis of the model cascade: show that
`δ_0^i X_n` has a unique minimal monomial under a suitable weight order, read off `a i`, `b j`, and
check that the resulting `L` is the boundary matrix of a single-monomial determinant.  Everything
else — the model determinant's nonvanishing, the transfer, the leading-determinant test, the graded
calculus and the multi-graded model with its derivations — is built and axiom-clean.

### Cards 13/14: the naive leading-determinant route provably fails (2026-08-31)

I computed the model cascade's monomial structure explicitly, and it rules the naive route out.  This
supersedes the previous entry's optimism and should stop a future session from re-attempting it.

For `δ_0 X_k = c_k X_1 ⋯ X_k`, applying `δ_0` to a monomial with exponent vector `a` gives
`∑_k a_k c_k · (mono / X_k) · X_1 ⋯ X_k`, whose `k`-th term has exponent
`a − e_k + (1,…,1,0,…,0)` (`k` ones).  The `k = n` term dominates every other **componentwise**, so
the maximal monomial is unique at each step and the leading exponent evolves by
`a ↦ a + (1,…,1) − e_n`.  Starting from `X_n` this gives

    lead(δ_0^i X_n) = c_n^i · X_1^i ⋯ X_{n-1}^i · X_n,   exponent  v_i = (i, i, …, i, 1)

for every `i ≥ 0`.  Applying `∂_j` lowers slot `j` by one and multiplies by that exponent, so the
Jacobian entry `(i, j)` has leading exponent `v_i − e_j` — which is exactly of the separable form
`a_i + b_j` with `a_i = −v_i`, `b_j = e_j`, as the leading-determinant test requires.

**But the boundary matrix is then singular.**  Its entries are `L i j = (v_i)_j · c_n^i`, i.e.
`i · c_n^i` for `j < n` and `c_n^i` for `j = n`.  For `n ≥ 3` the first `n − 1` columns are
proportional, so `det L = 0` and `det_ne_zero_of_hasLead` gives nothing.  The leading terms of the
determinant cancel; the true leading monomial of `J_0` comes from sub-leading data — consistent with
the hand computation at `n = 3`, where `J_0 = −λ_1³λ_2³λ_3² X_1²X_2X_3²` has multi-degree
`(2,1,2)`, not `∑v_i − ∑e_j`.

So the Newton polygon of `J_0` is **not** the sum of the row and column minima, and no choice of
weights fixes that: the obstruction is the cancellation, not the ordering.  The card's own phrase
"after passing to the logarithmic velocities, the triangular Jacobian induction has base determinant
`1`" is therefore load-bearing — the reduction must be run in the log-velocity frame, where the
corpus already computes the model determinant exactly
(`ExpAffineCascade.scaled_jet_det_ne_zero` via `ExponentialTowerUnitCost.towerJet_det_ne_zero` and
the terminal-scaled Bell reduction), and the general case must control the error terms *at each
stage of that reduction* rather than in one leading-term comparison.

Concretely the obstruction to running the corpus reduction verbatim is that in the `E`-frame
(`E_j := A_j ∂_j`, `δ = ∑_k u_{k-1} E_k`, `δ u_n = u_n T` with `T = ∑_k u_{k-1} A_k'`) one has
`E_n T = u_{n-1} A_n A_n''`, which vanishes identically in the model (`A_n'' = 0`) but not in
general.  The Newton-corner hypothesis makes it *small*, so the reduction should survive with
controlled errors — that is the shape a correct proof has to take.

### Two new reusable modules, and a replacement for Schwartz in card 20

**`HTGeometry/BriotBouquetLinear.lean`** — the degree-`≤ 1` case of the Briot–Bouquet
classification, proved by an integrating factor rather than by curve theory:

| Declaration | Statement |
|---|---|
| `eq_exp_of_deriv_eq_const_mul` | an entire solution of `f′ = a f` is `f 0 · exp (a z)` |
| `eq_affine_of_deriv_eq_const` | an entire solution of `f′ = b` is `f 0 + b z` |
| `eq_briotBouquetMap_of_deriv_eq_affine` | an entire solution of `f′ = a f + b` with `a ≠ 0` *is* `briotBouquetMap a 0 (f 0 + b/a) (−b/a)` |
| `briotBouquet_coeff_ne_zero_of_ne` | the exponential coefficient is nonzero exactly when the solution is nonconstant |

This is the first *classification* result for the Briot–Bouquet class in the corpus: until now
`briotBouquetMap` existed only as a definition that downstream theorems took as a hypothesis.
Card 15 needs the algebraic-`c` case, which still requires the curve argument; the linear case is
now unconditional.

**`HTGeometry/DisjointEuclideanSheets.lean`** — `isOpen_range_of_continuous_injective`,
`countable_of_pairwiseDisjoint_ranges`, `countable_of_injective_prod`,
`not_injective_prod_of_uncountable`: a continuous injection `E → E` of a finite-dimensional
Euclidean space has open range, so pairwise-disjoint such ranges are pairwise-disjoint nonempty
open sets and a separable space carries only countably many.  Hence `X × E` admits no continuous
injection into `E` unless `X` is countable.

**Why this matters for card 20.**  It replaces Schwartz's `C²` surface-flow trichotomy, the card's
heaviest cited input.  The argument: near the hull the normalized vector field `V` is holomorphic
and nonvanishing, so the real flow extends to a local *complex* flow, and a flow box gives a
continuous injection `T × D_ε → U` from (transversal) × (complex time) into the surface.  If the
hull were a non-circle solenoid its transversal `T` would be a Cantor set — uncountable — and
`countable_of_injective_prod` forbids that.  So the transversal is countable, hence (being compact
and totally disconnected or a point) the orbit is open in the hull, hence all of it, hence the hull
is a circle and `Γ(f)` is infinite cyclic.

Note this replaces case `(b)`-vs-solenoid *and* case `(c)`: a two-torus hull would have rank two and
is already excluded by the card-19 machinery (`rank_bohrHullFrequencies_le_pred_of_global_chart`).

What card 20 still needs is §§1–3 — normalization of the projective closure of the plane curve, the
lift of the state map through it, and regularity of `V` at every hull point.  Mathlib has no curve
normalization, and the singular points cannot simply be avoided: the state `J_g(0)` of a hull member
may land on `Sing(C)`, which is exactly what normalization repairs.  So §4 is now owned and §§1–3
are the whole remaining cost.

### Card 15 does not need Briot–Bouquet: an elementary route, and two more modules

Card 15 (`nonautonomous-cap-linear-order-two-shadow-rigidity`) reduces, as its own §"Entire rigidity
of the matching equation" shows, to excluding a transcendental entire `f` with

```text
z f'(z) = c(f(z)),   c algebraic over C(Y),
```

equivalently `P(f, z f') = 0` for a nonzero `P ∈ C[Y,W]`.  The card discharges this by citing the
Briot–Bouquet classification of entire autonomous first-order solutions.  That citation is
avoidable.  The following chain is elementary and uses only machinery the corpus owns or that is now
built:

1. **`ν(r) → ∞`** for a transcendental entire `f` — owned
   (`CentralIndexDivergence.tendsto_centralIndex_atTop`).
2. **Wiman–Valiron**: at suitable radii and at points of the maximum circle where `‖f‖ ≥ μ(r)`,
   `z f'(z)/f(z)` differs from `ν(r)` by a controlled amount — owned
   (`WimanValironPolynomialBound.exists_radius_point_wiman_valiron_scale` and siblings).
3. **The balancing principle**: in `∑_k a_k(y) w^k = 0` the largest term is within a factor of the
   number of terms of some *other* term — new, `PolynomialMagnitudeBalance`.
4. **Polynomial magnitudes**: `‖a_k(y)‖ ≍ ‖y‖^{deg a_k}` for large `‖y‖` — new, same module.
5. Steps 3 and 4 pin `‖W‖ = ‖z f'‖` between two constant multiples of `‖Y‖^e` for one `e` in the
   finite set `{(d_i − d_k)/(k − i)}` of Newton slopes: maximality of the index `k` gives
   `‖W‖^{k-i} ≥ ‖a_i‖/‖a_k‖` for every `i < k` and `‖W‖^{i-k} ≤ ‖a_k‖/‖a_i‖` for every `i > k`,
   and the balancing partner `j` supplies the matching inequality on the other side.
6. Since `ν = ‖W‖/‖Y‖ → ∞`, necessarily `e > 1`, so `ν(r) ≥ c·μ(r)^{e-1}` with `e − 1 > 0`.
7. **The growth wall** then gives a contradiction — new, `CentralIndexGrowthWall`.

**`HTGeometry/CentralIndexGrowthWall.lean`** — `logMaxTerm`, `logMaxTerm_mono`,
`centralIndex_mul_le_logMaxTerm_sub`, `false_of_centralIndex_ge_exp_mul_logMaxTerm`,
`false_of_centralIndex_ge_rpow`, `exists_forall_coeff_eq_zero_of_centralIndex_le`.  The wall itself:
if `ν(r) ≥ c·μ(r)^σ` with `σ > 0` beyond some radius, then on the logarithmic radius scale each unit
climb of `log μ` takes at most `e^{−σ}` times the time the previous one took, so `log μ` passes every
bound at the *finite* radius `t₀ + K/(1 − e^{−σ})` — impossible.  The proof is a geometric series,
not a differential inequality; the only input is the corpus's lower growth law
`ν(r)·log(s/r) ≤ log μ(s) − log μ(r)`.

**`HTGeometry/PolynomialMagnitudeBalance.lean`** — `norm_eval_le_mul_pow`, `exists_le_norm_eval`,
`exists_ne_norm_le_card_mul`.

What remains for card 15 is step 2's bookkeeping: the corpus's Wiman–Valiron statements carry
explicit error terms and select a radius from an interval, so assembling them into "`ν(r) ≍ ‖W‖/‖Y‖`
along a sequence of radii" is the work left.  Steps 1, 3, 4, 5, 7 are done or owned.

Cards 8 and 13/14 also run into a growth wall of this shape, so `CentralIndexGrowthWall` is expected
to serve all three.

### The Wiman–Valiron layer is weaker than "owned" suggests — a parameter audit

Step 2 of the card-15 chain needs the classical asymptotic

```text
z f'(z) / f(z) = ν(r)·(1 + o(1))     at a maximum-circle point with ‖f(z)‖ ≥ μ(r),
```

for a *general* transcendental entire `f`.  The corpus's Wiman–Valiron stack does not deliver it,
and the reason is structural rather than cosmetic.  Recording the audit so this is not rediscovered.

Track the parameters of `WimanValironRadius.exists_radius_point_wiman_valiron_bound`.  Write `H` for
the half-width of the logarithmic window, `s` for the permitted spread of `ν` across it, `L` for the
Lipschitz constant of `ν` on the window, `v₀` for the minimal scale, `N` for the half-width of the
index window.  The chain ties them by

```text
L = s / v₀,   h = H/2,   2 L v₀ ≤ N ≤ 2 L H,   selection needs  d − c > 2H·Δν / s,
```

and the resulting error is, after the tails are made negligible,

```text
E ≈ C·( s^{3/2} + √s · log(ν + 2s + 2/H) / H ).
```

Two observations settle it.

1. `L·v₀ = s` **identically**, because the Lipschitz constant is manufactured as spread over minimal
   scale (`CentralIndexSpreadSelection.centralIndex_le_add_of_spread_le`).  Hence `N ≥ 2Lv₀ = 2s`
   always — the index window can never be taken smaller than the spread, whatever `v₀` is chosen.
   That is what puts `s^{3/2}` in the error.
2. The selection lemma needs `T > 2H·Δν/s` on an interval of length `T`.  A Borel-type window has
   `T + 2H ≈ 1/ν` and `Δν ≲ ν`, which forces `s ≳ ν` — and then `s^{3/2} ≳ ν^{3/2} ≫ ν`.  Widening
   the window to escape that makes `Δν` grow at least as fast as `ν` for any function of positive
   order, with the same outcome.

So the estimate is usable only when `ν` is nearly constant across a logarithmic window — entire
functions of order zero with `ν(r) = O((log r)^k)`, `k < 3`.  The `8 ≤ H` in the `_polynomial` and
`_scale` wrappers is not the obstruction (`_bound` has `H` free); the obstruction is `L·v₀ = s`.

**What must be built.**  The classical argument does not bound the profile by a Lipschitz constant.
It uses the second moment: the normalised coefficient profile is Gaussian of width `√(ν a)` with
`a = d log ν / d log r`, and the index window is taken at `N ≈ √(ν a)·(log ν)^{1/2+ε}` — far below
the spread.  The corpus already has the moment machinery (`MaximumTermProfileMoments`,
`MaximumTermWindowMoments`, `meanIndex`) and the window estimate itself
(`WimanValironWindowEstimate.norm_mul_logDeriv_sub_centralIndex_le_window`, whose `L`, `v₀`, `N`, `H`
are all free).  What is missing is a **second-moment tail bound** replacing
`CentralIndexSpreadSelection`'s Lipschitz route, so that `N` can be taken of order `√(sL)` rather
than `≥ 2s`.

This is the single asset standing between the corpus and cards 8, 13, 14 and 15, all of which need a
growth wall fed by a Wiman–Valiron asymptotic.  The wall itself is now built
(`CentralIndexGrowthWall`); the feed is not.

### Correction: the Wiman–Valiron layer *is* strong enough — the wrappers were the problem

The previous entry concluded that `L·v₀ = s` blocks the classical asymptotic and that a new
second-moment tail bound is required.  That conclusion is wrong, and the parameter audit that
produced it was carried out at the wrong level.  `WimanValironRadius` exposes

```text
exists_radius_point_norm_mul_logDeriv_sub_centralIndex_le_closed
```

with **every** parameter free — `H, v₀, s, L, h, N` — subject only to `s ≤ L v₀`, `v₀ ≤ h`,
`2h ≤ H`, `2 L v₀ ≤ N ≤ 2 L H`, and the selection condition.  `N ≥ 2s` is indeed forced, but that is
harmless: the resulting error is `≈ C·s^{3/2}`, and `s` is a *free target spread*, not the actual
rise of `ν`.  What the earlier audit got wrong was tying `H` to a constant; `H` may be taken small.

**The working parameter choice.**  Put

```text
K := 3 log s,   v₀ = h = H/2 = K/s,   L = s/v₀ = s²/K,   N = ⌈2s⌉.
```

Every constraint holds, with `s ≤ L v₀`, `2h ≤ H` and `2Lv₀ ≤ N ≤ 2LH = 4s` all tight.  Then
`2Lh = 2s`, the tail rate is `N/(4L) = K/(2s)` so `(N/(4L))(N+1) ≈ K`, and `K = 3 log s` makes both
`G₀` and `G₂` negligible against `√(2N+1)` and `N²√(2N+1)`.  The bound collapses to `≈ 14 s^{3/2}`.
Note this is exactly the existing tie in `exists_radius_point_wiman_valiron_bound`
(`v₀ = h = H/2`, `L = 2s/H`) — only the `8 ≤ H` of the `_polynomial` and `_scale` wrappers has to be
bypassed, and `H := 2K/s` is small.

**Closing the loop with Borel.**  The selection needs `T > 2HΔ/s` on an interval of length `T`, where
`Δ = ν(e^{c+T+2H}) − ν(e^c)`.  Take `T := c₀/ν^{1/4}`.  The Borel growth lemma at exponent `1/4` —
the set where `ν(e^{x + c₀/ν(e^x)^{1/4}}) > 2 ν(e^x)` has finite measure, since each doubling
consumes measure `c₀/ν^{1/4}` and `∑ 2^{-k/4}` converges — gives `Δ ≤ ν` outside a finite-measure
exceptional set.  Then

```text
s ≈ √(12 Δ log s / T) = √(12/c₀) · ν^{5/8} · √(log s),
E ≈ 14 s^{3/2} = 14 (12/c₀)^{3/4} · ν^{15/16} · (log s)^{3/4}  ≪  ν,
```

because `(log s)^{3/4} ≪ ν^{1/16}`.  So the classical asymptotic

```text
‖ z f'(z)/f(z) − ν(r) ‖ ≤ ε · ν(r)     at arbitrarily large r, at a maximum-circle point
```

follows for **every** transcendental entire function, with no growth hypothesis.  The corpus owns
`BorelGrowthLemma`, `BorelGrowthMonotone` and `BorelGrowthExponent` already.

**What is left** is the inequality bookkeeping: instantiate `_bound` (or `_closed`) at
`H := 2K/s` and estimate the explicit right-hand side.  That is a single self-contained module,
`WimanValironAsymptotic`, and it is the feed the growth wall needs for cards 8, 13, 14 and 15.

### The Wiman–Valiron narrow-window estimate is built

`HTGeometry/WimanValironSmallWindow.lean` — the missing feed identified above, now proved and
axiom-clean.

| Declaration | Statement |
|---|---|
| `wv_tail_ratios_le_one` | with `K = 3 log s`, `L = s²/K`, `2s ≤ N ≤ 4s` and `s ≥ 100`, both geometric tails `q^{N+1}/(1−q)` and `q^{N+1}/(1−q)³` are at most one |
| `wv_rhs_le` | the whole explicit right-hand side collapses to `30 s^{3/2}(1 + log(ν + 4s)/log s)` |
| `exists_radius_point_wiman_valiron_small_window` | the estimate itself, at the logarithmic window of width `6 (log s)/s` |

The mechanism is the one predicted in the corrected audit: the tail rate satisfies
`(N/(4L))(N+1) ≥ K`, so `q^{N+1} ≤ e^{−K} = s^{−3}`, while `1 − q ≥ K/(3s)` by the corpus's
`one_sub_exp_neg_ge`; the ratios are then below `1/(s² log s)` and `1/log³ s` respectively.  The
mean-minus-mode factor `2Lh` is exactly `2s`, and `1/(e^h − 1) ≤ 1/h = s/K ≤ s`, so the logarithm's
argument is at most `ν + 4s`.  With `u = √s ≥ 10` the head factor is at most `3.2u`, the second
moment at most `55 s²u`, and the closing term at most `21 su`; the total is `29 u³(1 + Λ)` with
`Λ = log(ν + 4s)/log s`, and `30` is taken for room.

Note the key cancellation: `2 log(...)/h = (2s/K)·log(ν + 4s)` and `log(ν + 4s) = Λ · log s = Λ K/3`,
so `K` drops out and the logarithmic factor is scale-free.  That is why the bound is `s^{3/2}` times
a *ratio of logarithms* rather than `s^{3/2} log ν`.

**What remains** for the asymptotic `‖z f'/f − ν‖ ≤ ε ν` is the Borel selection: choose
`T = c₀/ν^{1/4}` and `s ≈ √(12 Δ log s / T)`, verify `hsmall` from the Borel growth lemma at
exponent `1/4`, and check `30 s^{3/2}(1 + Λ) ≤ ε ν`.  The corpus owns `BorelGrowthLemma`,
`BorelGrowthMonotone` and `BorelGrowthExponent`; nothing else is missing.

### The Wiman–Valiron asymptotic is proved, unconditionally

`HTGeometry/WimanValironAsymptotic.lean` —

```text
exists_radius_point_logDeriv_close_centralIndex :
  EntireCoeffs a → a n₀ ≠ 0 → (∀ M, ∃ n ≥ M, a n ≠ 0) → 0 < ε → ∀ R,
    ∃ x ≥ R, ∃ z, ‖z‖ = exp x ∧ μ(exp x) ≤ ‖f z‖ ∧
      ‖ z f'(z)/f(z) − ν(exp x) ‖ ≤ ε · ν(exp x)
```

axiom-clean, no growth hypothesis on `f` beyond transcendence.  This is the classical asymptotic the
corpus had not reached, and it is the feed the growth wall needs.

**The parameter scheme.**  A single scale `w` drives everything.  With `T₀ = ν(r) + 1`,

```text
w = T₀^{1/100},   δ = T₀^{-1/4} = w^{-25},   s = w^{64},   H = 6 (log s)/s,
```

so that every quantity is an integer power of `w` — that is the reason for the hundredth root.  The
supporting lemmas are `wv_scale_facts` (`log w ∈ [3, w]` for `w ≥ 40`), `wv_window_le`
(`H ≤ δ/4`, reducing to `1536 log w ≤ w^{39}`), `wv_selection_lt` (`2 H w^{100}/s < δ/2`, reducing to
`1536 log w < w³`, true from `w² ≥ 1600`) and `wv_error_le` (`30 s^{3/2}(1 + Λ) ≤ ε ν`, via
`Λ ≤ 1.58` and a central index at least `w^{100}/2`, giving relative error `155/w⁴`).

**The three inputs.**  `Nevanlinna.exists_ge_lt_two_mul_rpow` at exponent `1/4` gives a radius where
`ν` does not double across the step `δ`; `monotone_centralIndex_exp` transports that across the
sampling interval; `exists_radius_point_wiman_valiron_small_window` supplies the estimate itself.
`tendsto_centralIndex_atTop` pushes the scale above the thresholds `w ≥ 40` and `155/ε ≤ w⁴`.

**Consequence.**  The chain for card 15 is now complete except for its algebraic half: with this
asymptotic, `‖z f'‖ ≍ ν(r)‖f(z)‖` at maximum-circle points, and `PolynomialMagnitudeBalance` pins
`‖z f'‖` to a power `‖f‖^e` of the value; `ν → ∞` forces `e > 1`, and `CentralIndexGrowthWall`
contradicts `ν ≥ c μ^{e−1}`.  Cards 8, 13 and 14 consume the same asymptotic.

### The wall and the asymptotic do not yet meet: a radius-set mismatch

Trying to close card 15 with the two new assets exposes a mismatch that must be recorded.

`CentralIndexGrowthWall.false_of_centralIndex_ge_rpow` needs `c·μ(r)^σ ≤ ν(r)` for **every** `r ≥ r₀`:
its march picks the radii `t_{n+1} = t_n + K q^n` itself, and monotonicity of `ν` cannot repair a
missing value — `ν(e^t) ≥ ν(e^τ)` for `τ ≤ t` is the right direction, but `μ(e^τ) ≤ μ(e^t)` is the
wrong one, so a lower bound at `τ` does not transfer to `t`.

`WimanValironAsymptotic.exists_radius_point_logDeriv_close_centralIndex` supplies the estimate only
at *some* radius beyond each bound.  The underlying Borel selection is in fact much stronger — the
exceptional set has finite measure, so good radii have density one — but the theorem as stated
forgets that.

**The bridge, and why it is not free.**  Suppose the estimate holds at `τ ∈ [t − η, t]`.  Then
`ν(e^t) ≥ ν(e^τ) ≥ c e^{σφ(τ)}` and `φ(t) − φ(τ) ≤ ν(e^t)·η`, so choosing `η ≤ 1/(σ ν(e^t))` costs
only a factor `e^{-1}`.  The march therefore survives if every interval `[t_n − 1/(σν), t_n]`
contains a good radius.  The bad set has finite total measure, but the marching steps `K q^n` and the
tolerances `1/(σν)` both shrink, so no single starting radius makes all of those intervals good.
Closing this needs the Borel lemma re-stated as a *density* statement and the march re-run against
it, or a wall that consumes a full-measure hypothesis directly.

**A second observation, recorded so it is not re-attempted.**  Replacing the wall by a pointwise
growth comparison does not work.  The balancing principle gives `‖z f'(z)‖ ≍ ‖f(z)‖^e` at every point
where `‖f(z)‖` is large, and at a maximum-modulus point this yields `M(r, f') ≥ c M(r)^e / r`, hence
`M(2r) ≥ c M(r)^e` by Cauchy.  That is *not* a contradiction — `exp(exp z)` satisfies far more — so
the finite-radius blow-up really is the only available mechanism, and it is a statement about `μ` on
an interval, not along a sequence.

The local expansion is also insufficient by itself: at `z = 0` an entire solution of `z f' = c(f)`
has `c(f(0)) = 0` and `c'(f(0)) = m` where `m` is the order of vanishing of `f − f(0)`, which is
consistent (e.g. `c(Y) = m(Y − a)`, `f = a + Cz^m`) — it kills `c(Y) = Y²` but not the general case.

### Card 15: the growth route is a dead end; the mechanism is finite-time blow-up

The mismatch above is not a bookkeeping gap — it is fatal to the growth route, and the reason is
worth recording so the route is not re-attempted.

The march in the growth wall must reach infinity in *finite* logarithmic time, so its steps
necessarily shrink to zero.  A hypothesis available only outside a set of finite measure therefore
cannot feed it: a finite-measure set may still meet every one of the shrinking marching intervals
near the accumulation point.  No strengthening of the Borel selection repairs this, because the
selection is what produces the finite-measure exceptional set in the first place.

**The correct mechanism is separation of variables.**  For `F' = c(F)` with `F` entire and the branch
of `c` of degree `ρ > 1` at infinity,

```text
t − t₀ = ∫_{F(t₀)}^{F(t)} dY / c(Y),
```

and `∫^∞ dY/c(Y)` **converges** when `ρ > 1`.  So along a path on which `F → ∞` the parameter `t`
reaches a finite limit: the solution has a singularity at a finite point, contradicting entirety.
This is local and path-based; it never mentions growth of `M(r)` at all.  It is also exactly why the
`M(2r) ≥ c M(r)^e` comparison recorded above is not a contradiction — the obstruction lives at a
finite point of the plane, not at infinity.

**What that costs in Lean.**  It needs a complex-analytic flow: existence and uniqueness for
`F' = c(F)` along a path, and the statement that the maximal interval of existence is bounded when
the time integral converges.  Mathlib has `ODE_solution_unique` for real Banach-space ODEs but no
complex-analytic continuation of solutions, so this is a build of its own.

**The assets remain.**  `CentralIndexGrowthWall` and `WimanValironAsymptotic` are unaffected as
statements — they are correct and reusable — but card 15 is not their consumer.  Cards 8, 13 and 14
are about growth of cascades rather than blow-up of a first-order autonomous solution, and should be
re-examined against the asymptotic on their own terms rather than by analogy with card 15.

### A Nevanlinna route to card 15 that avoids complex-analytic flows

The blow-up mechanism recorded above is the right *idea*, but it is not the only way to reach the
conclusion, and there is a route through value distribution that needs no ODE theory at all.

For `F` entire with `F' = c(F)` and `c` a polynomial of degree `d`:

```text
d · m(r,F) + O(1) = m(r, c ∘ F) = m(r, F') = m(r, F·(F'/F)) ≤ m(r,F) + m(r, F'/F),
```

so `(d − 1) m(r,F) ≤ m(r, F'/F) + O(1)`.  The logarithmic-derivative estimate makes the right side
`O(log r + log T(2r))`, whence `T(r,F) = O(log r)` off an exceptional set and `F` is a polynomial —
and a polynomial cannot satisfy `F' = c(F)` with `d ≥ 2`, since `deg F − 1 = d · deg F` has no
solution.  Every step is proximity algebra plus the corpus's own log-derivative bound; no flow, no
maximal interval of existence.

`HTGeometry/ProximityPolynomialComposition.lean` supplies the first equality, which was the missing
piece:

| Declaration | Statement |
|---|---|
| `posLog_norm_polyEval_le` | `log⁺‖p(y)‖ ≤ deg p · log⁺‖y‖ + log⁺(∑‖coeff‖)` |
| `exists_le_posLog_norm_polyEval` | `deg p · log⁺‖y‖ − C ≤ log⁺‖p(y)‖` for a constant `C` |
| `circleIntegrable_posLog_norm_of_continuous` | the circle integrand of a continuous function is integrable |
| `proximity_comp_polynomial_le` | `m(r, p ∘ f) ≤ deg p · m(r,f) + log⁺(∑‖coeff‖)` |
| `exists_le_proximity_comp_polynomial` | `deg p · m(r,f) − C ≤ m(r, p ∘ f)` |

**Corpus already owns more than expected here.**  `HTGeometry/AlgebraicProximityBound.lean` carries
`proximity_le_of_root`, `proximity_le_of_root_characteristic_top`, `proximity_eval_mvPolynomial_le`,
`characteristic_eval_mvPolynomial_le` and — the one that matters for the algebraic `c` of card 15 —
`exists_bound_proximity_of_two_var_relation`, "an element algebraic over the field generated by an
entire function grows no faster".  That is exactly the estimate for `W = z f'` algebraic over `ℂ(f)`.
Its `posLog_norm_eval_le` forced a rename of the new lemmas to the `polyEval` forms.

So the remaining work for card 15's analytic core is: assemble
`m(r,F') ≤ m(r,F) + m(r,F'/F)` from `proximity_top_le_of_codiscrete_mul`, feed the corpus's
`proximity_logDeriv_sub_const_le`, and run one Borel step on `T`.

### The autonomous proximity inequality is built

`HTGeometry/ProximityFirstOrderAutonomous.lean`, axiom-clean:

| Declaration | Statement |
|---|---|
| `proximity_deriv_le_add_logDeriv` | `m(r, F') ≤ m(r, F) + m(r, F'/F)` for entire `F` with a nowhere-identically-zero germ on the circle |
| `exists_proximity_autonomous_bound` | if `F' = c(F)` with `c ≠ 0` of degree `d`, then `(d − 1)·m(r,F) ≤ m(r, F'/F) + C`, with `C` independent of `r` |
| `natDegree_eq_zero_of_derivative_eq_comp` | a polynomial solution of `q' = c ∘ q` with `deg c ≥ 2` is constant |

The first is `proximity_top_le_of_codiscrete_mul` applied to `F' = F·(F'/F)`, valid off the zero set
of `F`, which is codiscrete by `MeromorphicAt.MeromorphicOn.codiscreteWithin_setOf_ne_zero`.  The
second combines it with `exists_le_proximity_comp_polynomial` and the identity `c ∘ F = F'`.  The
third is the degree count `deg q − 1 = d · deg q`, impossible for `d ≥ 2` and `deg q ≥ 1`.

**What is left for the `d ≥ 2` no-go.**  Feed `proximity_logDeriv_sub_const_le` (with `a = 0`) into
the second, at `R = 2r`, to get

```text
m(r,F) ≤ (1/α)·log(1 + [divisor term] + [ (2R/(R−r)²)(2T(R,F) + C₀) ]^α) + C,
```

then a Borel step on `T` to replace `T(2r)` by `2T(r)` outside a set of finite measure, giving
`T(r,F) = O(log r)` there and hence `F` polynomial by
`IteratedDerivativeGrowth.tendsto_characteristic_atTop_of_not_polynomial`.  The degree count then
closes it.  The only genuinely new work is bounding the divisor term, which counts zeros of `F` in
`|z| ≤ 2r` with an `α`-power and is `O(T(2r))` — enough, since it enters under a logarithm.

### The pure-power Briot–Bouquet no-go is proved, with no value distribution at all

`HTGeometry/AutonomousPowerRigidity.lean`, axiom-clean:

| Declaration | Statement |
|---|---|
| `eq_zero_of_deriv_eq_const_mul_sq` | an entire solution of the Riccati equation `H' = c H²` with `c ≠ 0` is identically zero |
| `eq_const_of_deriv_eq_const_mul_pow` | an entire solution of `F' = γ (F − a)^d` with `γ ≠ 0` and `d ≥ 2` is the constant `a` |

This supersedes the Nevanlinna plan for the pure-power case: the argument uses neither the
logarithmic-derivative estimate nor a Borel step.  The substitution `H = (F − a)^{d-1}` gives
`H' = (d−1)γH²`; a zero of `H` forces `H = 0` on a disc, because on a disc of radius `ρ` with
`ρ‖c‖ ≤ 1/2` and `‖H‖ ≤ 1` the mean value inequality gives `M ≤ ‖c‖M²ρ ≤ M/2` for the maximum `M`;
the identity theorem propagates that to the plane.  A nowhere-vanishing `H` makes `1/H` entire with
constant derivative `−c`, hence affine with nonzero slope, hence with a zero — impossible for `1/H`.

**Why this matters for the local step of card 15.**  Combined with the order comparison at a root
`a` of `c` — if `F(z₀) = a` with `F − a` vanishing to order `k` and `c` vanishing to order `m` at
`a`, then `k − 1 = km`, which has no solution with `k ≥ 1, m ≥ 1` — a solution of `F' = c(F)` omits
every root of `c`.  For `c = γ(Y − a)^d` that is now a complete theorem.

**What the general polynomial case still needs.**  If `c` has two or more distinct roots, the
solution omits two values, and ruling that out is Picard's little theorem, which mathlib does not
have.  The corpus's second main theorem for entire functions
(`SecondMainTheoremEntire.mul_characteristic_le_of_separated_entire`) is the natural substitute — it
gives `2T(r) ≤ N(r,a₁) + N(r,a₂) + S(r)` and both counting terms vanish for omitted values — so the
route is: discharge its `hfmt` first-main-theorem defect and its `S(r)` term, exactly the assembly the
previous entry describes.

### Every quadratic autonomous equation is now closed, and the local half in full generality

Two more modules, both axiom-clean.

`HTGeometry/AnalyticEquilibriumUniqueness.lean`:

| Declaration | Statement |
|---|---|
| `eq_zero_of_zero_of_norm_deriv_le_on_ball` | Gronwall vanishing: `G z₀ = 0` and `‖G'‖ ≤ C‖G‖` on a ball of radius `ρ` with `ρC < 1` force `G = 0` |
| `eq_const_of_root_of_deriv_eq_comp` | a solution of `F' = c(F)` that meets a root of `c` is constant — equivalently, a nonconstant entire solution **omits every root of `c`** |

The second is the local half of the Briot–Bouquet no-go, in full generality and with no value
distribution: factoring `c = (X − a)·p` gives `G' = G·p(F)` for `G = F − a`, and Gronwall does the
rest.  This replaces the order comparison `k − 1 = km`, which would have needed an
`analyticOrderAt`-of-derivative lemma that mathlib does not have.

`HTGeometry/QuadraticAutonomousNoGo.lean`:

| Declaration | Statement |
|---|---|
| `exists_exp_eq` | every nonzero complex number is an exponential |
| `eq_const_of_deriv_eq_quadratic` | `F' = γ(F − a₁)(F − a₂)` with `a₁ ≠ a₂` has no nonconstant entire solution |

Inverting `F − a₁` linearises the equation to `V' = −γ − γ(a₁ − a₂)V`; `BriotBouquetLinear` gives
`V = −b/α + κ exp(α z)`, and a nonzero `κ` makes `V` vanish because `exp` attains every nonzero
value.  **With the pure-power case this closes every quadratic `c`** — its two roots are either
distinct or equal.

**Where the general degree stands.**  For `deg c = d ≥ 3` a nonconstant solution omits every root of
`c`.  One distinct root is `eq_const_of_deriv_eq_const_mul_pow`; two or more omitted values is
Picard, absent from mathlib and from the corpus (the search turns up `modularLambda_omits_zero_one'`
in `Bottcher/QuarticModularForm.lean`, the classical ingredient, but no covering argument on top of
it).  The corpus's second main theorem remains the practical substitute.

### The general-degree no-go: a second-main-theorem route that needs no Picard

For `deg c = d ≥ 2` with two or more distinct roots, Picard is *not* the only way.  The corpus's
second main theorem for entire functions applies directly, and the hypotheses are all now available.

Let `F` be a nonconstant entire solution of `F' = c(F)`.  Two facts, both proved above:

* `F` omits every root of `c` (`eq_const_of_root_of_deriv_eq_comp`);
* hence `c(F)` never vanishes, so **`F'` never vanishes** — which is exactly the `hcod` hypothesis of
  `SecondMainTheoremEntire.mul_characteristic_le_of_separated_entire`, and it holds everywhere, not
  merely codiscretely.

Apply the theorem at `q = 2` with the omitted values `a₁, a₂`.  Both counting terms
`N(r, a_j)` vanish, leaving

```text
2 T(r,F) ≤ m(r, F'/(F−a₁)) + m(r, F'/(F−a₂)) + m(r, 1/F') + O(1).
```

The two logarithmic-derivative terms are `S(r,F)` by `proximity_logDeriv_sub_const_le`.  The
ramification term is handled by Jensen rather than by a ramification count: `F'` is entire and
nowhere zero, so `log‖F'‖` is harmonic and

```text
m(r, 1/F') = m(r, F') − log‖F'(0)‖,
```

while `m(r,F') ≤ m(r,F) + m(r,F'/F) = T(r,F) + S(r,F)` — that is the already-built
`proximity_deriv_le_add_logDeriv`.  Substituting gives `2T ≤ T + S + O(1)`, i.e. `T(r,F) ≤ S(r,F)`,
which is the contradiction.

**Ingredient status.**

| Needed | Where |
|---|---|
| `hcod`: `F'` nonvanishing | proved, from `eq_const_of_root_of_deriv_eq_comp` |
| `hfmt`: first-main-theorem defect `T(r,F) ≤ T(r,F−a) + K` | `NevanlinnaEntireCharacteristic.characteristic_add_le` and `characteristic_const_eq` |
| `m(r,F'/(F−a)) = S(r,F)` | `LogDerivProximityBound.proximity_logDeriv_sub_const_le` |
| `m(r,F') ≤ m(r,F) + m(r,F'/F)` | `ProximityFirstOrderAutonomous.proximity_deriv_le_add_logDeriv` |
| `m(r,1/g) = m(r,g) − log‖g 0‖` for zero-free entire `g` | **to build** — from mathlib's `MeromorphicOn.circleAverage_log_norm` (zero divisor, `meromorphicTrailingCoeffAt g 0 = g 0`) and `Real.posLog_sub_posLog_inv` |
| a Borel step turning `T ≤ S` into a contradiction | `BorelGrowthExponent`, plus `IteratedDerivativeGrowth.tendsto_characteristic_atTop_of_not_polynomial` |

Only the Jensen row is genuinely missing, and mathlib supplies its two halves.

### The Jensen row is built — every ingredient of the general-degree no-go is now present

`HTGeometry/JensenProximityReciprocal.lean`, axiom-clean:

```text
proximity_inv_eq_sub : g entire and zero-free → m(r, 1/g) = m(r, g) − log‖g 0‖
```

The pointwise identity is mathlib's unconditional `Real.posLog_sub_posLog_inv`
(`log⁺x − log⁺x⁻¹ = log x`); integrating it against the circle turns the difference of proximities
into `⨍ log‖g‖`, and mathlib's `AnalyticOnNhd.circleAverage_log_norm_of_ne_zero` evaluates that at
the centre.

**A duplication caught late.**  The first draft of this module proved the mean value property from
`MeromorphicOn.circleAverage_log_norm` by showing the divisor vanishes — about thirty lines — before
a grep for the *use sites* (not the name) turned up
`AnalyticOnNhd.circleAverage_log_norm_of_ne_zero`, which is mathlib's own zero-free Jensen and is
consumed in six corpus modules already.  The module now calls it.  Searching for the statement's
*consumers* rather than its expected name is what surfaced it.

With this the ingredient table of the previous entry is complete: every row for
`2T(r,F) ≤ m(r,F'/(F−a₁)) + m(r,F'/(F−a₂)) + m(r,1/F') + O(1)` and its collapse to `T ≤ S` is
either in mathlib, in the corpus, or built above.  What remains is the assembly itself — instantiate
`mul_characteristic_le_of_separated_entire` at `q = 2`, discharge `hfmt` from
`characteristic_add_le`, substitute the four bounds, and run the Borel step.

### The second main theorem is assembled for an omitting function

`HTGeometry/SecondMainTheoremOmitted.lean`, axiom-clean:

| Declaration | Statement |
|---|---|
| `logCounting_eq_zero_of_omits` | an entire function omitting `a` has `N(r,a) = 0` |
| `meromorphicOrderAt_ne_top_of_deriv_ne_zero` | an entire function with nowhere-vanishing derivative has finite meromorphic order everywhere |
| `characteristic_le_of_omits_two` | `T(r,F) ≤ m(r,F'/(F−a₁)) + m(r,F'/(F−a₂)) + m(r,F'/F) + O(1)` for entire `F` omitting `a₁ ≠ a₂` with `F'` zero-free |

The assembly instantiates `mul_characteristic_le_of_separated_entire` at `q = 2`.  Both counting
terms vanish by the first lemma; `hcod` is satisfied *everywhere*, not merely codiscretely, since
`F'` is zero-free; the ramification term becomes `m(r,F') − log‖F'(0)‖` by `proximity_inv_eq_sub`,
and `m(r,F') ≤ m(r,F) + m(r,F'/F)` by `proximity_deriv_le_add_logDeriv`.  Because
`m(r,F) = T(r,F)` for entire `F`, one power of the characteristic cancels against the `2T` on the
left.

The first-main-theorem defect `hfmt` is left as a hypothesis; the corpus discharges it with
`SecondMainTheoremChain.characteristic_top_le_characteristic_coe`, whose constant does not depend on
`r`.

**What is left for card 15's general-degree case.**  Only the final step: each of the three terms on
the right is `S(r,F)` by `proximity_logDeriv_sub_const_le`, so `T ≤ S`, and a Borel step on `T`
turns that into `T(r,F) = O(log r)` — whence `F` is a polynomial and the degree count
`natDegree_eq_zero_of_derivative_eq_comp` closes it.

### Every denominator made zero-free

`characteristic_le_of_omits_two_shifted`, appended to `HTGeometry/SecondMainTheoremOmitted.lean`
and axiom-clean:

```text
T(r,F) ≤ 2·m(r, F'/(F−a₁)) + m(r, F'/(F−a₂)) + O(1)
```

for entire `F` omitting `a₁ ≠ a₂` with `F'` zero-free.

The improvement over the previous form is the factorisation used to split the ramification term.
Writing `F' = F·(F'/F)` leaves `m(r, F'/F)`, whose denominator `F` may vanish — and the
logarithmic-derivative estimate's divisor term then counts those zeros.  Writing instead

```text
F' = (F − a₁)·(F'/(F − a₁))
```

keeps the denominator at an *omitted* value, so it is zero-free and the divisor term of
`proximity_logDeriv_sub_const_le` vanishes identically.  The shift costs only
`m(r, F − a₁) ≤ m(r,F) + log⁺‖a₁‖ + log 2`, from `Nevanlinna.characteristic_add_le` and
`characteristic_const_eq`.

This matters because it removes the one genuinely awkward input of the final step: with both
denominators zero-free, `proximity_logDeriv_sub_const_le` reduces to

```text
m(r, F'/(F−a)) ≤ (1/α)·log(1 + (2R/(R−r)²·(2T(R,F−a) + C₀))^α),
```

no divisor sum at all.  Choosing `R = r(1 + 1/T(r))` makes `2R/(R−r)² ≈ 2T(r)²/r`, and a Borel step
gives `T(R) ≤ 2T(r)` outside a set of finite measure, so the right-hand side is
`3 log T(r) − log r + O(1)`.  Feeding that back gives `T(r) ≤ 9 log T(r) + O(1)`, so `T` is bounded
and `F` is constant.

### The logarithmic-derivative estimate at an omitted value

`HTGeometry/LogDerivOmittedValue.lean`, axiom-clean:

| Declaration | Statement |
|---|---|
| `divisor_eq_zero_of_forall_ne_zero` | the divisor of a zero-free entire function is identically zero |
| `proximity_logDeriv_le_of_omits` | `m(r, f'/(f−a)) ≤ (1/α)·log(1 + (2R/(R−r)²·(2T(R,f−a) + \|log‖f(0)−a‖\|))^α)` when `f` omits `a` |

Both the divisor finsum and the `max` in `proximity_logDeriv_sub_const_le` collapse: the finsum
because every term is `0^α = 0`, and the `max` because the trailing coefficient of a zero-free
analytic germ is its value, so its two arguments are equal.  The result is a bound in the
characteristic alone — no zero counting anywhere.

`ZeroFreeRadius` already had a *pointwise* `divisor_eq_zero_of_ne_zero`; the new lemma is the global
form and is named accordingly.

**The remaining step for card 15, in full.**  Combining with
`characteristic_le_of_omits_two_shifted`:

```text
T(r,F) ≤ (3/α)·log(1 + (2R/(R−r)²·(2T(R,F−a) + C₀))^α) + O(1).
```

Take `R := r + T(r)^{-α}`.  The corpus's Borel lemma at exponent `α`
(`Nevanlinna.exists_ge_lt_two_mul_rpow`) gives `T(R) ≤ 2T(r)` outside a set of finite measure, and
`2R/(R−r)² = 2R·T(r)^{2α} ≈ 2r·T(r)^{2α}`, so the right-hand side is
`3(log r + (2α+1) log T(r)) + O(1)`.  Since `log T = o(T)`, this forces `T(r) = O(log r)` on a
cofinal set, hence everywhere by monotonicity — so `F` is a polynomial, and
`natDegree_eq_zero_of_derivative_eq_comp` finishes.

### The quantitative no-go inequality, fully assembled

`HTGeometry/OmittedValueCharacteristicBound.lean`, axiom-clean:

| Declaration | Statement |
|---|---|
| `characteristic_nonneg_of_entire` | `0 ≤ T(r,F)` for entire `F` |
| `characteristic_sub_const_le` | `T(r, F − a) ≤ T(r,F) + log⁺‖a‖ + log 2` |
| `characteristic_le_log_of_omits_two` | `T(r,F) ≤ (3/α)·log(1 + (2R/(R−r)²·(2T(R,F) + C))^α) + C'` for entire `F` omitting `a₁ ≠ a₂` with `F'` zero-free, all `0 < r < R`, `1 ≤ R` |

This is the whole second-main-theorem chain in one inequality, with **no counting function anywhere**:
the two `N(r,a_j)` vanish because the values are omitted, the ramification term is Jensen's
`m(r,1/F') = m(r,F') − log‖F'(0)‖`, and the divisor term of the logarithmic-derivative estimate
vanishes because the shifted factorisation keeps every denominator at an omitted value.  The
constants depend only on `α`, on `a₁, a₂`, and on the germ of `F` at the origin.

**All that is left is the Borel closure.**  Put `R := r + T(r)^{-α}`.  Then
`2R/(R−r)² = 2R·T(r)^{2α}`, and `Nevanlinna.exists_ge_lt_two_mul_rpow` gives `T(R) ≤ 2T(r)` outside
a set of finite measure, so

```text
T(r) ≤ (3/α)·log(1 + (2r·T(r)^{2α}·(4T(r) + C))^α) + C' = 3 log r + 3(2α+1) log T(r) + O(1)
```

on the good set.  Since `log T = o(T)` that bounds `T(r)` by `O(log r)` cofinally, hence everywhere
by monotonicity, so `F` is a polynomial — and `natDegree_eq_zero_of_derivative_eq_comp` closes card
15's general-degree case.

### The Borel closure: every name located, nothing missing

The three inputs I expected to have to build for the final step all already exist.

**Monotonicity of the characteristic.**  Mathlib has it —
`ValueDistribution.characteristic_monotoneOn (h : Meromorphic f) : MonotoneOn (characteristic f ⊤) (Ioi 0)`
in `Mathlib/Analysis/Complex/ValueDistribution/Cartan.lean`, whose own docstring calls the result
"surprisingly non-trivial".  This is what `Nevanlinna.exists_mem_Icc_lt_two_mul_rpow_window` needs.

**A good radius in every window, not merely cofinally.**  The corpus's
`BorelGrowthExponent.exists_mem_Icc_lt_two_mul_rpow_window` produces a Borel-good point inside every
interval of length `borelWindow α`.  That is the form required: a merely cofinal good set would give
`T(s) ≤ A log r + B` for some unrelated `r ≥ s`, which bounds nothing; a good point inside
`[s, s + borelWindow α]` gives `T(s) ≤ A log(s + borelWindow α) + B`, i.e. `T(s) = O(log s)`.

**`T = O(log r)` implies polynomial.**  `MaxModulusCharacteristicBound.posLog_norm_le_characteristic`
bounds the interior maximum modulus by the characteristic at a larger radius — the direction opposite
to `characteristic_le_posLog_of_forall_sphere`, and the one needed here.  It turns `T = O(log r)`
into `M(r) = O(r^C)`, hence polynomial growth.

**The arithmetic of the collapse.**  With `R = r + T(r)^{-α}` and `T(r) = characteristic F ⊤ r + 1`:

```text
2R/(R−r)² = 2R·T(r)^{2α},   T(R) ≤ 2T(r)   (Borel),   R ≤ r + 1,
log(1 + x^α) ≤ log 2 + α·log⁺x,
```

so `characteristic_le_log_of_omits_two` gives

```text
T₀ ≤ 3 log(2(r+1)) + 6α log(T₀+1) + 3 log(4T₀+2+C) + C'.
```

Bounding `log y ≤ 2√y` (from `log √y ≤ √y − 1`) makes the two `log T₀` terms `O(√T₀)`, so for large
`T₀` they are below `T₀/2` and `T₀ ≤ 6 log(2(r+1)) + C''`.

So the remaining work on card 15's general-degree case is assembly against known names, with no
missing mathematical input.

### The collapse arithmetic

`HTGeometry/LogSelfBoundArithmetic.lean`, axiom-clean:

| Declaration | Statement |
|---|---|
| `le_of_le_add_six_log` | `0 ≤ A + B` and `T ≤ A + 6 log(T+1) + B` imply `T ≤ 2(A+B) + 1156` |
| `log_one_add_rpow_le` | `log(1 + x^α) ≤ log 2 + α·log⁺x` for `x ≥ 0`, `α > 0` |

The first is the self-bound collapse: `log(T+1) ≤ 2√(T+1)` makes the logarithmic term `O(√T)`,
which drops below `T/2` once `T > 1156` — the threshold is where `576(T+1) ≤ T²` bites.  The second
removes the `α`-power from the logarithmic-derivative estimate, leaving a plain logarithm; taking
`α = 1/2` throughout makes `2R/(R−r)² = 2R·T(r)` exactly, with no fractional powers left anywhere.

**A third duplication, and what finally catches them.**  `log_le_two_mul_sqrt` was already in the
corpus *twice*, in `LogBelowLinear` and `LogWeightedPoisson`, both in namespace
`GaloisForLFunctions.HTGeometry`.  Neither a name search of the index nor the single-module build
surfaces this — what surfaced it was the *grep output printed by `lake build`* while it recompiled
dependents.  The reliable check is an explicit scratch file importing the new module alongside its
likely neighbours; that is now the routine before installing anything.  Removing the duplicate then
exposed the narrow-import trap: dropping `import Mathlib` in favour of the corpus import lost
`Real.rpow` and `Real.posLog` entirely.  Both imports are needed.

### The Borel closure is executed

`HTGeometry/OmittedValueLogarithmicGrowth.lean`, axiom-clean:

| Declaration | Statement |
|---|---|
| `charPlusOne` | `x ↦ T(max x 1) + 1`, monotone on all of `ℝ` and at least `1` |
| `monotone_charPlusOne`, `one_le_charPlusOne`, `charPlusOne_eq` | its three properties |
| `exists_characteristic_le_log_of_omits_two` | for entire `F` omitting `a₁ ≠ a₂` with `F'` zero-free, `∃ A ≥ 1, B`, `∀ s ≥ 1`, `T(s,F) ≤ 6 log(s + A) + B` |

Taking `α = 1/2` throughout is what makes this tractable: `R = x + T(x)^{-1/2}` gives
`(R − x)² = T(x)^{-1}` exactly, so `2R/(R−x)² = 2R·T(x)` with no fractional powers surviving, and
`3/α = 6`.  The chain is `y ≤ 2D(x+1)(T₀+1)²` with `D = 4 + C`, then `log⁺y = log(2D) + log(x+1) +
2 log(T₀+1)`, then `log_one_add_rpow_le`, then `le_of_le_add_six_log`.

The Borel lemma is used in its **window** form.  That is not a convenience: a cofinal good set bounds
`T(s)` by `A log r + B` for some unrelated `r ≥ s`, which is no bound on `s` at all.  The window form
puts the good radius within `borelWindow (1/2)` of `s`, and monotonicity of the characteristic
transports the bound back.

**Card 15's general-degree case is now one step from closed.**  `T(r,F) = O(log r)` plus
`MaxModulusCharacteristicBound.posLog_norm_le_characteristic` gives `M(r) = O(r^C)`, so `F` is a
polynomial; `natDegree_eq_zero_of_derivative_eq_comp` then contradicts `deg c ≥ 2`.  The only
remaining input is "entire of polynomial growth is a polynomial".

### The two-root Briot–Bouquet no-go is PROVED

`HTGeometry/BriotBouquetTwoRootNoGo.lean`, axiom-clean:

| Declaration | Statement |
|---|---|
| `le_exp_posLog` | `x ≤ exp (log⁺ x)` for `x ≥ 0` |
| `exists_polyGrowth_of_characteristic_le_log` | `T(s) ≤ 6 log(s+A) + B` for `s ≥ 1` implies `‖F z‖ ≤ M (1 + ‖z‖)^{36}` |
| `not_nonconstant_of_two_roots` | **no nonconstant entire `F` satisfies `F' = c(F)` when `deg c ≥ 2` and `c` has two distinct roots** |

The full chain, all of it now formal: a nonconstant solution omits every root of `c`
(`eq_const_of_root_of_deriv_eq_comp`), hence `F' = c(F)` is zero-free; the second main theorem
applies with both counting terms zero and the ramification term from Jensen
(`characteristic_le_of_omits_two_shifted`); the logarithmic-derivative estimate has no divisor term
(`proximity_logDeriv_le_of_omits`); the Borel closure gives `T(r,F) = O(log r)`
(`exists_characteristic_le_log_of_omits_two`); comparing maximum modulus at `r` with the
characteristic at `2r` gives degree-`36` polynomial growth; `exists_polynomial_of_polynomial_growth`
makes `F` a polynomial `p`; `Polynomial.funext` turns `F' = c(F)` into `p' = c ∘ p`; and
`natDegree_eq_zero_of_derivative_eq_comp` kills it because `deg p − 1 = deg c · deg p` has no
solution.

The first-main-theorem defect is discharged inside the theorem from
`characteristic_top_le_characteristic_coe`, taking `K = max K₁ K₂` over the two values.

**With `eq_const_of_deriv_eq_const_mul_pow` this covers every `c` of degree ≥ 2**: over `ℂ` a
polynomial of degree ≥ 1 has at least one root, and either it has two distinct roots (this theorem)
or exactly one, in which case `c = γ(X − a)^d` and the pure-power rigidity applies.  Assembling that
case split into a single statement is the only remaining step.

### The Briot–Bouquet no-go is complete for every polynomial of degree at least two

`HTGeometry/BriotBouquetNoGo.lean`, axiom-clean:

| Declaration | Statement |
|---|---|
| `eq_const_mul_pow_of_unique_root` | a complex polynomial all of whose roots equal `a` is `C(leadingCoeff)·(X − a)^{deg}` |
| `eq_const_of_deriv_eq_comp` | **an entire solution of `F' = c(F)` with `deg c ≥ 2` is constant** |

The case split is over `ℂ`, where a polynomial of degree ≥ 2 has a root: two distinct roots go to
`not_nonconstant_of_two_roots`, a single root to `eq_const_of_deriv_eq_const_mul_pow` after the
factorisation.  The factorisation uses `Splits.eq_prod_roots`, `splits_iff_card_roots` and
`Multiset.eq_replicate_card`.

Together with `BriotBouquetLinear` — `deg c ≤ 1` gives `d + c·exp(a z)` — this is the **complete
Briot–Bouquet classification of entire solutions of `F' = c(F)` for polynomial `c`**, which is the
input card 15 cites and the corpus previously lacked.  It was reached without complex-analytic ODE
flows, without Picard, and without the Wiman–Valiron asymptotic: the local half is Gronwall, the
global half is the second main theorem with every counting term zero.

**Card 15's status.**  The card's chain is: the vanishing of the three-jet determinant forces
`A = c(y)/x`, hence `x f'(x) = c(f(x))`; passing to `F(t) = f(e^t)` gives `F' = c(F)`; Briot–Bouquet
then makes `f` a polynomial, contradicting transcendence.  The last step is now formal for polynomial
`c`.  What the card needs beyond it is the *algebraic* `c` case — `c` algebraic over `ℂ(Y)` rather
than polynomial — for which `AlgebraicProximityBound.exists_bound_proximity_of_two_var_relation` is
the corpus's entry point.

### What the algebraic-coefficient case actually needs, and why it is not the same problem

Card 15 needs Briot–Bouquet for `c` *algebraic* over `ℂ(Y)`, i.e. for the corpus's own predicate
`AutonomousCompJet.AutonomousFirstOrder f`: `∑_k c_k(f)·(f′)^k = 0` with polynomial `c_k`.  It is
worth recording why the polynomial theorem just proved does not extend by a small step.

**The algebraic case is a classification, not a no-go.**  For polynomial `c` of degree ≥ 2 there are
*no* nonconstant entire solutions, and that is what `eq_const_of_deriv_eq_comp` proves.  For
algebraic `c` there are: `exp` satisfies `f′ = f`, and `℘` satisfies `(℘′)² = 4℘³ − g₂℘ − g₃`.  So no
contradiction is available; the statement to prove is that the entire solutions are exactly
`d + c·exp(a z)` and the polynomials.

**Why the second-main-theorem route does not transfer.**  Its engine was that a solution omits *two*
values, giving `2T ≤ … `.  For `f′ = f` the solution omits exactly one value (zero), and the second
main theorem at `q = 1` says nothing.  The omitted-value count is what carried the polynomial case,
and it is not available here.

**What the classification reduces to.**  For card 15 the needed consequence is narrower than the
full classification: `f` entire with `z f′(z) = c(f(z))` implies `f` is a polynomial.  Passing to
`F(t) = f(eᵗ)` makes this a statement about the *order*: `log M(r,F) = log M(eʳ, f)`, so `f` is a
polynomial exactly when `F` has order at most one.  So the missing input is

> an entire solution of an autonomous first-order algebraic differential equation has order ≤ 1,

a Gol'dberg/Bank-type growth theorem.  That is the honest remaining gap; it is a growth statement, and
the corpus's Wiman–Valiron layer — including this session's `WimanValironAsymptotic` and
`CentralIndexGrowthWall` — is the natural place to attack it, since order is exactly what the central
index measures.

### The Wiman–Valiron asymptotic in window form

`exists_radius_point_logDeriv_close_centralIndex_window`, appended to
`HTGeometry/WimanValironAsymptotic.lean` and axiom-clean:

```text
∃ R₁, ∀ R ≥ R₁, ∃ x ∈ Icc R (R + borelWindow(1/4) + 1), ∃ z,
  ‖z‖ = exp x ∧ μ(exp x) ≤ ‖f z‖ ∧ ‖ z f'(z)/f(z) − ν(exp x) ‖ ≤ ε · ν(exp x)
```

The cofinal form proved earlier is not enough for a growth conclusion, for the same reason recorded
in the Borel-closure entry: a good radius somewhere beyond `R` bounds nothing at `R` itself, whereas
a good radius within a fixed distance does, once monotonicity is applied.  The change is to call
`exists_mem_Icc_lt_two_mul_rpow_window` instead of `exists_ge_lt_two_mul_rpow` and to hoist the
threshold `R₁` in front of the quantifier over `R`.

The window is `borelWindow(1/4) + 1` rather than `borelWindow(1/4)`: the selected radius `x` is
Borel-good, but the estimate is produced at a radius `y ∈ [x, x + δ]` with `δ = T₀^{-1/4} ≤ 1`, so
one extra unit is needed to contain it.

**Why this is the tool for the algebraic case.**  The order bound needed for card 15 is
`ν(r) = O(r)`.  At a Wiman–Valiron point the relation `∑ c_k(F)(F′)^k = 0` becomes
`∑ c_k(F)(ν/r)^k F^k ≈ 0`; the balancing principle `exists_ne_norm_le_card_mul` pins `ν/r ≍ M^σ` for
one of finitely many rational `σ`; `σ > 0` is excluded by `CentralIndexGrowthWall`, and `σ ≤ 0` gives
`ν(r) = O(r)` directly.  Monotonicity of `ν` then spreads the bound from the window radii to all
radii, and `log μ(r) = ∫ ν dr/r = O(r)` is order at most one.

### The growth half of the order-one theorem

`HTGeometry/CentralIndexLinearOrderOne.lean`, axiom-clean:

```text
log_maxTerm_le_linear_of_centralIndex_le_linear :
  (∀ r ≥ r₀, ν(r) ≤ C r) → ∀ r ≥ r₀, log μ(r) ≤ log μ(r₀) + 4 C (log 2) r
```

Each doubling of the radius costs `ν(2r) log 2 ≤ C r log 2` by the lower growth law, and the dyadic
induction telescopes.  The induction is on `k` with the invariant "for every `r ∈ [r₀, 2^k r₀]`",
splitting at `r ≤ 2r₀` (one step from the base) versus `r > 2r₀` (halve and apply the hypothesis);
that split is what keeps the constant at `4` rather than growing with `k`.

**Where card 15's algebraic case now stands.**  The chain is

```text
autonomous relation  →  ν(r) = O(r)  →  log μ(r) = O(r)  →  order ≤ 1  →  f polynomial,
```

and the last two arrows are now formal (this module, plus `MaxModulusCharacteristicBound` and
`exists_polynomial_of_polynomial_growth`).  The first arrow is the remaining work: at a
Wiman–Valiron point supplied by `exists_radius_point_logDeriv_close_centralIndex_window`, the
relation `∑ c_k(F)(F′)^k = 0` reads `∑ c_k(Y)·V^k ≈ 0` with `V = ν‖Y‖/r`; the balancing principle
pins `V ≍ ‖Y‖^σ` for one of finitely many rational `σ`; `σ > 1` is excluded by
`CentralIndexGrowthWall` and `σ ≤ 1` gives `ν = O(r)`.  A pigeonhole over the finitely many index
pairs is needed because the balancing pair may vary with the radius.

### The upper half of `ν(r) = O(r)`

`HTGeometry/TopCoefficientBound.lean`, axiom-clean:

```text
mul_le_sum_of_top_dominated :
  (∀ i, 0 ≤ A i) → 1 ≤ t → A n * t^n ≤ ∑_{j<n} A j * t^j → A n * t ≤ ∑_{j<n} A j
```

When `t ≥ 1` every lower power is at most `t^{n-1}`, so dividing the domination relation by `t^{n-1}`
bounds `t` itself.  Applied to `∑ c_k(F)(F′)^k = 0` with `F′ = W/z` and `|z| = r`, the terms have
magnitudes `|c_k(F)|(|W|/r)^k` and the conclusion is

```text
|W| ≤ r · (∑_{j<n} |c_j(F)|) / |c_n(F)|,
```

which is `ν(r) = O(r)` whenever the coefficient ratio is bounded — i.e. whenever
`max_{j<n} deg c_j ≤ deg c_n + 1`.

**What the remaining case needs.**  When that degree inequality fails the upper bound carries a
positive power of `‖F‖` and is not enough; the two-sided Newton-polygon balancing is then required,
with `‖W‖ ≍ r‖Y‖^e` for `e = (d_j − d_k)/(k − j)` and the wall excluding `e > 1`.  Because the
balancing pair can vary with the radius, a pigeonhole over the finitely many pairs is needed to fix
one pair on a cofinal set of window radii.  The worked example is `W² + Y⁵W + 1 = 0`, where the crude
bottom-index bound gives `σ < 0` and misses the blow-up branch `zF′ ≈ −F⁵` entirely — which is why
the pigeonhole cannot be avoided.

### The two-sided balancing

`HTGeometry/TwoSidedBalancing.lean`, axiom-clean:

```text
exists_pow_between_of_balanced :
  index k maximal, partner j ≠ k with A k t^k ≤ (n+1)(A j t^j)  →
    ∃ u < v ≤ n,  A u / ((n+1) A v) ≤ t^{v-u} ≤ (n+1) · A u / A v
```

Both inequalities come from the same two facts read in opposite directions: maximality of the
`k`-term gives one, the balancing partner the other.  The case split is only on whether `j < k` or
`k < j`, and the two cases produce the same conclusion with `{u,v} = {j,k}` ordered — which is why
the statement can be phrased without reference to which of the two indices was maximal.

With `t = ‖W‖/r` and `A k = |c_k(F)|` this says `‖W‖/r` is comparable to a fixed power of the
maximum modulus, and that is the step converting the algebraic relation `∑ c_k(F)(F′)^k = 0` into a
growth law.

**What is left is the glue**, not a new idea: at each window radius the balancing supplies a pair
`(u,v)`; pigeonholing over the finitely many pairs fixes one on a cofinal set; on that set
`ν ≍ r·μ^{e-1}` with `e = (d_u − d_v)/(v − u)`; `e > 1` contradicts `CentralIndexGrowthWall` and
`e ≤ 1` gives `ν(r) = O(r)`, which `CentralIndexLinearOrderOne` turns into order at most one, and
`MaxModulusCharacteristicBound` plus `exists_polynomial_of_polynomial_growth` into "polynomial".

### The pigeonhole, and a correction: the `e > 1` branch needs the *integral* wall

`HTGeometry/CofinalPigeonhole.lean`, axiom-clean:

```text
exists_cofinal_of_finite_pigeonhole :
  (∀ R, ∃ x ≥ R, ∃ p ∈ S, P x p) → ∃ p ∈ S, ∀ R, ∃ x ≥ R, P x p
```

for a nonempty finite `S`.  Each index failing beyond its own threshold would let the maximum of
those finitely many thresholds contradict the hypothesis.

**But the pigeonhole is not where the difficulty was, and one branch does not need it at all.**
Working the assembly through:

* For the `e ≤ 1` branch no pigeonhole is required.  Each window radius carries *some* pair `p`, and
  each pair yields `ν(r) ≤ C_p·r`; taking `C := max_p C_p` over the finite set gives `ν(r) ≤ C r` at
  **every** window radius, and monotonicity spreads it to all radii.
* For the `e > 1` branch the pigeonhole gives a *cofinal* set of radii where `ν(r) ≥ c μ(r)^{e-1}`.
  That is **not enough for `CentralIndexGrowthWall`**, whose march picks radii with geometrically
  shrinking gaps and therefore needs the hypothesis on an interval, not on a cofinal set — the same
  obstruction recorded earlier for the blow-up route.

**What the `e > 1` branch actually needs** is the *integral* form of the wall.  With
`log μ(r) = log μ(r₀) + ∫ ν(t) dt/t` and the estimate holding outside a set of finite measure `M`,

```text
(1/σ)(e^{−σφ(t₀)} − e^{−σφ(T)}) ≥ c·(T − t₀ − M),
```

whose left side is bounded by `e^{−σφ(t₀)}/σ`, so `T − t₀` is bounded — a contradiction for large
`T`.  This replaces the discrete march by a differential inequality valid almost everywhere, which is
exactly what a finite-measure exceptional set supports.  The corpus's `MonotoneIncrementMeasure`
(`integral_increment_eq`, `volume_increment_ge_le`) is the natural starting point.

### Good-radius selection at every scale

`HTGeometry/GoodRadiusSelection.lean`, axiom-clean:

| Declaration | Statement |
|---|---|
| `exists_notMem_of_volume_lt` | a set of measure below `b − a` misses a point of `Icc a b` |
| `exists_notMem_of_volume_ne_top_of_lt` | a set of measure at most `M` misses a point of every interval longer than `M` |

Trivial as measure theory, but it is the selection the `e > 1` branch needs and the reason that
branch is not hopeless: the exceptional set of the Wiman–Valiron estimate has *finite* measure, so
good radii occur in every window of a *fixed* length — the length required does not shrink.

**The state of the `e > 1` branch, precisely.**  The discrete march of `CentralIndexGrowthWall`
cannot be fed by a cofinal set because its steps shrink geometrically.  Two ways out, both viable:

1. *Integral form.*  `log μ(r) = log μ(r₀) + ∫ ν dt/t` gives `φ' = ν(eᵗ)` a.e.; with
   `ν ≥ c e^{σφ}` off a set of measure `M`, the substitution `ψ = e^{−σφ}` yields
   `(−ψ/σ)' ≥ c` on the good set, so `ψ(t₀)/σ ≥ c(T − t₀ − M)` and `T` is bounded.  Needs the exact
   integral identity and the fundamental theorem for monotone functions.
2. *Euler form.*  Partition `[t₀,T]` into `N` intervals of length `h`; each with bad measure `< h`
   holds a good point `s_i`, and `φ(a_{i+2}) − φ(a_i) ≥ ν(e^{s_i})·h ≥ c h e^{σφ(a_i)}`.  The
   resulting recursion `Φ_{i+1} ≥ Φ_i + βe^{σΦ_i}` with `β = ch/2` halves `ψ = e^{−σΦ}` within
   `2ψ₀/(σβ)` steps — a time `4ψ₀/(σc)` independent of `h` — and the halvings form a geometric
   series, so `φ` passes every bound in bounded time.  Needs only the discrete growth law and this
   module's selection, plus a bound on how many partition intervals can be wholly bad (`≤ M/h`).

Route 2 avoids measure-theoretic differentiation entirely and is the one to take.

### The Euler blow-up

`HTGeometry/EulerBlowup.lean`, axiom-clean:

| Declaration | Statement |
|---|---|
| `euler_step` | `Φ + β e^{σΦ} ≤ x` and `σβ ≤ e^{−σΦ}` imply `e^{−σx} ≤ e^{−σΦ} − σβ/2` |
| `exp_le_half_of_euler_recursion` | a recursion `Φ_{i+1} ≥ Φ_i + β e^{σΦ_i}` halves `e^{−σΦ}` within `ψ₀/(σβ)` steps |

One step is `ψ ↦ ψ²/(ψ + σβ)` after `e^{−u} ≤ 1/(1+u)`, and `ψ²/(ψ + σβ) ≤ ψ − σβ/2` holds **exactly**
when `σβ ≤ ψ` — the condition is not an artefact but the exact threshold, which is why the invariant
is phrased as a disjunction "either `ψ_i ≤ ψ₀ − i σβ/2` or `ψ_i ≤ ψ₀/2`", the second branch absorbing
the case where the step condition fails.

**The scaling is the point.**  In the intended application `β = c h/2` with `h` the partition step,
so the number of steps to halve is proportional to `1/h` and the *elapsed parameter* `N h` is
independent of `h`.  Halving repeatedly therefore drives `Φ` past every bound within a bounded
parameter range — the discrete replacement for `φ' ≥ c e^{σφ}` that the finite-measure exceptional
set of a Wiman–Valiron estimate can support, unlike the geometric march of `CentralIndexGrowthWall`.

With `GoodRadiusSelection` supplying a good point in every partition interval whose bad measure is
below its length, the `e > 1` branch now has all of its analytic content in place; what is left is
to instantiate `Φ i := log μ(e^{a_i})` against the corpus's discrete growth law.

### Counting the wholly bad intervals — and a correction to the blow-up scaling

`HTGeometry/BadIntervalCount.lean`, axiom-clean:

```text
card_mul_le_of_subset_of_volume_le :
  disjoint `Ico (t₀ + i h) (t₀ + (i+1) h)` for `i ∈ S`, all inside `B`, `volume B ≤ M`
    → (S.card) · h ≤ M
```

**This forced a correction to the plan recorded two entries ago.**  That entry proposed taking the
partition step `h` *fixed and larger than* the exceptional measure `M`, so that every interval holds
a good radius.  That does not work: once `ψ = e^{-σΦ}` falls below `σβ = σch`, each step merely
halves `ψ`, so `Φ` grows by `log 2/σ` per step — linear in the elapsed parameter, never blowing up.
The `σβ ≤ ψ` regime is the only one that blows up, and it needs `h` *small*, not large.

The correct accounting does not need every interval to be good.  With `h` small, at most `M/h` of
the `N = (T − t₀)/h` intervals are wholly bad; on the rest the Euler step applies, and the total
decrease of `ψ` is at least

```text
(N − M/h) · σ c h / 2  =  σ c (T − t₀ − M) / 2,
```

**independent of `h`**.  Since the total decrease cannot exceed `ψ(t₀)`, this bounds `T − t₀` by
`M + 2ψ(t₀)/(σc)` — the contradiction.  The other branch, where `ψ` drops below `σch` at some step,
makes `Φ` exceed `log(1/(σch))/σ`, which is unbounded as `h → 0` while `φ(T)` is fixed.

So both branches close, and the three modules `GoodRadiusSelection`, `EulerBlowup` and
`BadIntervalCount` are exactly what the accounting consumes.

### The telescoping accounting

`HTGeometry/StepwiseTelescope.lean`, axiom-clean:

```text
le_sub_card_mul_of_stepwise :
  (∀ i ∈ G, ψ(i+1) ≤ ψ i − d) → (∀ i ∉ G, ψ(i+1) ≤ ψ i) →
    ∀ N, ψ N ≤ ψ 0 − (G.filter (· < N)).card · d
```

The marked indices `G` are the partition intervals containing a radius outside the exceptional set;
the unmarked ones are wholly bad and need only monotonicity.  Combined with `BadIntervalCount`
(`card ≤ M/h`) the drop is at least `(N − M/h)·d`, and with `d = σch/2` that is `σc(Nh − M)/2` —
independent of `h`.

**The four pieces of the `e > 1` branch are now all in place:**

| Piece | Module |
|---|---|
| a good radius in every interval whose bad measure is below its length | `GoodRadiusSelection` |
| at most `M/h` intervals are wholly bad | `BadIntervalCount` |
| one good step drops `e^{−σΦ}` by `σβ/2` when `σβ ≤ e^{−σΦ}` | `EulerBlowup` |
| the drops telescope | `StepwiseTelescope` |

Running them against `φ(t) = log μ(eᵗ)` and the corpus's `centralIndex_mul_le_logMaxTerm_sub`: either
`e^{−σΦ}` stays above `σch` throughout, and the telescoped drop bounds `T − t₀` by
`2M + 4e^{−σφ(t₀)}/(σc)`; or it falls below `σch` at some step, forcing `φ(T) > log(1/(σch))/σ`,
unbounded as `h → 0` while `φ(T)` is fixed.  Choosing `T` past the first bound and `h` small enough
to violate the second closes both.

### The growth wall with a finite-measure exceptional set — PROVED

`HTGeometry/MeasureGrowthWall.lean`, axiom-clean:

```text
false_of_centralIndex_ge_exp_off_null :
  EntireCoeffs a → a n₀ ≠ 0 → 0 < c → 0 < σ → 0 ≤ M → volume B ≤ ofReal M →
  (∀ t ≥ t₀, t ∉ B → c · e^{σ φ(t)} ≤ ν(eᵗ)) → False
```

This is the theorem the `e > 1` branch was waiting on, and it repairs the defect recorded against
`CentralIndexGrowthWall`: that wall needs its hypothesis at *every* radius because its march takes
geometrically shrinking steps, whereas a Wiman–Valiron estimate only ever holds outside a set of
finite measure.

All four supporting modules are consumed:

* `GoodRadiusSelection` — every partition interval not wholly inside `B` holds a usable radius;
* `BadIntervalCount` — at most `M/h` intervals are wholly inside `B`;
* `EulerBlowup` — one usable step drops `e^{−σΦ}` by `σch/2`;
* `StepwiseTelescope` — the drops accumulate.

The total drop is `≥ σc(Nh − M)/2 = σc((T − t₀)/2 − M)/2`, independent of `h`, and cannot exceed
`e^{−σφ(t₀)}`; choosing `T = t₀ + 2M + 4e^{−σφ(t₀)}/(σc) + 1` contradicts that.

One design point made the proof short: `h` is chosen so that `σch < e^{−σφ(T)}`, and since `φ` is
monotone and every partition point lies below `T`, the Euler step's side condition `σch ≤ e^{−σΦ i}`
holds at *every* index with no case analysis.  The earlier plan, taking `h` fixed and larger than
`M`, had to case-split and did not blow up at all.

**Card 15's algebraic case now needs only the two-sided balancing run at Wiman–Valiron radii**:
`TwoSidedBalancing` pins `ν/r ≍ μ^{e−1}`; `e > 1` feeds this wall, `e ≤ 1` gives `ν = O(r)`, and
`CentralIndexLinearOrderOne` with `MaxModulusCharacteristicBound` and
`exists_polynomial_of_polynomial_growth` finish.

### The Newton-polygon bound for a vanishing power sum

`HTGeometry/VanishingPowerSum.lean`, axiom-clean:

```text
exists_pow_between_of_vanishing_sum :
  w ≠ 0 → ∑_{k ≤ m} α_k w^k = 0 → (∃ k ≤ m, α_k ≠ 0) →
    ∃ u < v ≤ m, α_u ≠ 0 ∧ α_v ≠ 0 ∧
      ‖α_u‖/((m+1)‖α_v‖) ≤ ‖w‖^{v−u} ≤ (m+1)·‖α_u‖/‖α_v‖
```

The maximal term is nonzero — otherwise every term, hence every coefficient, would vanish, since
`w ≠ 0` — so `exists_ne_norm_le_card_mul` supplies a partner and `exists_pow_between_of_balanced`
gives the two-sided estimate.

`TwoSidedBalancing` had to be strengthened to carry `0 < A u ∧ 0 < A v` in its conclusion: the
identity of `u` and `v` as `{j,k}` is discarded there, so the nonvanishing of the two coefficients
cannot be recovered downstream and must be exported.

Applied with `α_k = c_k(F(z))` and `w = F′(z)`, this converts an autonomous algebraic differential
relation into a comparison between `‖F′‖` and a power of `‖F‖` — the shape the Wiman–Valiron point
turns into a growth law for `ν`.

### The Newton-polygon bound for a vanishing power sum

`HTGeometry/VanishingPowerSum.lean`, axiom-clean:

```text
exists_pow_between_of_vanishing_sum :
  w ≠ 0 → ∑_{k ≤ m} α_k w^k = 0 → (∃ k ≤ m, α_k ≠ 0) →
    ∃ u < v ≤ m, α_u ≠ 0 ∧ α_v ≠ 0 ∧
      ‖α_u‖/((m+1)‖α_v‖) ≤ ‖w‖^{v−u} ≤ (m+1)·‖α_u‖/‖α_v‖
```

The maximal term is nonzero — otherwise every term, hence every coefficient, would vanish, since
`w ≠ 0` — so `exists_ne_norm_le_card_mul` supplies a partner and `exists_pow_between_of_balanced`
gives the two-sided estimate.

`TwoSidedBalancing` had to be strengthened to carry `0 < A u ∧ 0 < A v` in its conclusion: the
identity of `u` and `v` as `{j,k}` is discarded there, so the nonvanishing of the two coefficients
cannot be recovered downstream and must be exported.

Applied with `α_k = c_k(F(z))` and `w = F′(z)`, this converts an autonomous algebraic differential
relation into a comparison between `‖F′‖` and a power of `‖F‖` — the shape the Wiman–Valiron point
turns into a growth law for `ν`.

### Reading Wiman–Valiron on the derivative

`HTGeometry/WimanValironDerivative.lean`, axiom-clean:

```text
norm_deriv_between_of_wv :
  ‖z‖ = r → 0 < r → 0 ≤ ν → F z ≠ 0 → ‖z F′(z)/F(z) − ν‖ ≤ ε ν →
    (1 − ε) ν ‖F z‖ / r ≤ ‖F′(z)‖ ∧ ‖F′(z)‖ ≤ (1 + ε) ν ‖F z‖ / r
```

Since `‖z F′/F‖ = r‖F′‖/‖F‖`, the relative bound on the difference is exactly a two-sided bound on
`‖F′(z)‖`.  The hypothesis `0 ≤ ν` is needed and not cosmetic: without it `‖(ν : ℂ)‖` is `|ν|`, and
the upper bound would carry `|ν|` where `ν` is wanted.

**The order-one chain is now fully assembled from named results:**

| Step | Module |
|---|---|
| a Wiman–Valiron radius in every window | `WimanValironAsymptotic` (`…_window`) |
| the estimate read on `F′` | `WimanValironDerivative` |
| the relation `∑ c_k(F)(F′)^k = 0` pins `‖F′‖` to a power of `‖F‖` | `VanishingPowerSum` |
| the coefficient magnitudes `‖c_k(Y)‖ ≍ ‖Y‖^{deg}` | `PolynomialMagnitudeBalance` |
| `e > 1` is impossible | `MeasureGrowthWall` |
| `e ≤ 1` gives `ν(r) = O(r)` | `TopCoefficientBound` |
| `ν = O(r)` gives order ≤ 1 | `CentralIndexLinearOrderOne` |
| order ≤ 1 gives polynomial | `MaxModulusCharacteristicBound`, `exists_polynomial_of_polynomial_growth` |

### Attempting the order-one assembly exposes a branch-consistency gap

Running the chain end to end does not close, and the obstruction is mathematical rather than glue.
Recording it so the "only assembly remains" note above is not taken at face value.

At each Wiman–Valiron radius the Newton bound supplies *some* index pair `(u,v)` and hence an
exponent `e = (d_u − d_v)/(v − u)`, with

```text
ν/r ≤ C‖Y‖^{e−1}   (upper, from the pair's upper bound)
ν/r ≥ c‖Y‖^{e−1}   (lower, from its lower bound).
```

The trouble is that `e` may differ from radius to radius, and the two branches want incompatible
things:

* `e ≤ 1` gives `ν ≤ C r` at that radius, and to conclude `ν = O(r)` everywhere one needs such
  radii in *every* window — but the window theorem yields one radius per window and cannot control
  which pair it carries.
* `e > 1` gives `ν ≥ c μ^{e−1}`, and `MeasureGrowthWall` needs that off a set of *finite* measure.
  Pigeonholing the pairs over the co-null good set yields a pair holding on a set of *infinite*
  measure, which is strictly weaker and does not feed the wall.

Taking the maximum or minimum exponent over the finitely many pairs does not repair it: a uniform
upper bound with `E = max e` is vacuous once `E > 1`, and a uniform lower bound with `min e` is
vacuous once that is `≤ 1`.  The two are simultaneously useless exactly when the exponent set
straddles `1`.

**What is actually needed** is that the exponent is eventually *constant* — that `F′` follows a
single branch of the algebraic function at all large radii.  Classically this is where the Puiseux
expansion at infinity enters: the branch is determined by a Newton-polygon edge and cannot switch,
because the coefficient magnitudes `‖c_k(Y)‖ ≍ ‖Y‖^{d_k}` are eventually monotone comparisons.  That
is a genuine ingredient, not bookkeeping, and it is the honest remaining gap for card 15's algebraic
case — distinct from every gap recorded above, all of which are now closed.

### Correction: branch consistency is NOT needed — a density dichotomy closes it

The previous entry claimed the exponent must be shown eventually constant, via Puiseux.  That is
wrong: a dichotomy on the *density* of the two kinds of good radius closes the argument with no
branch analysis at all.

Split the co-null good set as `G = G_≤ ⊔ G_>` by whether the radius's exponent satisfies `e ≤ 1`.

* **If `G_>` has positive upper density `δ₀`.**  Then along a sequence of `T`,
  `volume (G_>ᶜ ∩ [t₀,T]) ≤ (1 − δ₀/2)(T − t₀)`.  The growth wall does not actually need a
  *finite*-measure exceptional set — its accounting only needs the wholly bad intervals to number at
  most a fraction of `N`.  With bad measure `≤ δ(T − t₀) + M` and `δ < 1/2`, the good intervals number
  at least `N(1 − 2δ) − M/h` and the total drop is `σc((1 − 2δ)(T − t₀)/2 − M)/2`, still independent
  of `h`, still bounding `T`.  So this case is impossible.
* **If `G_>` has upper density zero.**  Then `volume (G_> ∩ [t₀, 2r]) = o(r)`, so
  `volume (G_≤ᶜ ∩ [r, 2r]) ≤ o(r) + M < r` for large `r`, and `exists_notMem_of_volume_lt` produces a
  radius of `G_≤` inside `[r, 2r]`.  Monotonicity of `ν` then gives `ν(r) ≤ ν(r′) ≤ C r′ ≤ 2C r`.

Either way `ν(r) = O(r)`, which is the order-one input.  The needed generalisation of
`MeasureGrowthWall` is small — replace `volume B ≤ ofReal M` by
`∀ T, volume (B ∩ Icc t₀ T) ≤ ofReal (δ (T − t₀) + M)` with `δ < 1/2`, and carry the factor
`(1 − 2δ)` through the same count — and no new mathematical ingredient is required.

### The density growth wall is built

`HTGeometry/DensityGrowthWall.lean`, axiom-clean:

```text
false_of_centralIndex_ge_exp_off_density :
  0 ≤ δ → δ < 1/2 → (∀ S, volume (B ∩ Icc t₀ S) ≤ ofReal (δ (S − t₀) + M)) →
  (∀ t ≥ t₀, t ∉ B → c · e^{σ φ(t)} ≤ ν(eᵗ)) → False
```

The finite-measure hypothesis of `MeasureGrowthWall` is replaced by a density bound below one half.
Nothing in the accounting changes except the count: the good intervals number at least
`N(1 − 2δ) − M/h`, the telescoped drop is `σc((1 − 2δ)(T − t₀)/2 − M)/2`, still independent of `h`,
and `T − t₀` is bounded by `(2M + 4e^{−σφ(t₀)}/(σc))/(1 − 2δ)`.

The interval-containment side condition needed strengthening — the bad intervals must be shown to lie
inside `Icc t₀ T`, not merely inside `B` — which is where the partition bound `2Nh = T − t₀` enters a
second time.

**Both halves of the density dichotomy for card 15 now have their tool:** the `e > 1` branch is
excluded by this wall as soon as it has positive upper density, and the `e ≤ 1` branch is spread by
`GoodRadiusSelection` once the other branch has density zero.

### The thin branch of the density dichotomy

`HTGeometry/DensityDichotomy.lean`, axiom-clean:

```text
exists_mem_of_small_complement :
  (∀ x ∉ B, x ∈ G₁ ∨ x ∈ G₂) → volume B ≤ ofReal M →
  volume (G₂ ∩ Icc t₀ (2r)) ≤ ofReal (ε·2r) → ε·2r + M < r →
    ∃ x ∈ Icc r (2r), x ∈ G₁
```

`[r, 2r]` has measure `r` and would have to be covered by `B` together with the thin part of `G₂`;
the measure bound forbids it.

**Card 15's algebraic case is now reduced to a mechanical case split.**  Both branches have their
tool and neither needs a new idea:

| Branch | Tool | Conclusion |
|---|---|---|
| `G_>` (exponent `> 1`) has positive upper density | `DensityGrowthWall` | contradiction |
| `G_>` has upper density zero | `DensityDichotomy` + monotonicity of `ν` | `ν(r) = O(r)` |

and `ν = O(r)` runs into `CentralIndexLinearOrderOne` → order at most one →
`MaxModulusCharacteristicBound` → `exists_polynomial_of_polynomial_growth` → `F` is a polynomial,
contradicting transcendence.

The session's arc on this card, for the record: the blow-up route, Picard, the Wiman–Valiron growth
wall in its original discrete form, and branch consistency via Puiseux were each proposed and each
turned out to be avoidable or wrong.  What survived is the second main theorem for the polynomial
case — proved outright — and, for the algebraic case, the density dichotomy above.

### Closing the coverage gap between the two branches

`HTGeometry/DilatedDensityDichotomy.lean`, axiom-clean:

```text
exists_mem_of_small_complement_dilate :
  … → volume (G₂ ∩ Icc t₀ (K r)) ≤ ofReal (ε (K r)) → 1 < K →
  ε (K r) + M < (K − 1) r → ∃ x ∈ Icc r (K r), x ∈ G₁
```

**This was a real gap, not a cosmetic one.**  The wall branch tolerates an exceptional set of density
below `1/2`; the thin branch as first stated tolerated `G₂` of density below `1/2`.  The two
thresholds meet exactly at `1/2` and jointly cover *nothing with certainty* — a function whose `G₂`
has density exactly one half escapes both.

Widening the window from `[r, 2r]` to `[r, K r]` removes it: the thin branch then tolerates any
density below `1 − 1/K`, so as `K` grows it covers every density below one, while the wall covers
everything above one half.  The spread bound degrades only by the constant factor `K`, so
`ν(r) = O(r)` is unaffected.

Why `1/2` is intrinsic to the wall and cannot simply be raised: the Euler recursion needs a good
radius in `[a_i, a_{i+1}]` and then room to grow to `a_{i+2}`, so it consumes *two* partition
intervals per step, and the count `N(1 − 2δ)` carries the factor two.  Taking the good radius in the
first half of an interval does not help — it halves the interval length and the factor reappears.

### The growth wall at a single horizon

`HTGeometry/LocalisedGrowthWall.lean`, axiom-clean:

```text
false_of_centralIndex_ge_exp_off_density_at :
  0 ≤ δ → δ < 1/2 →
  t₀ + (2M + 4 e^{−σ φ(t₀)}/(σc))/(1 − 2δ) + 1 ≤ T →
  volume (B ∩ Icc t₀ T) ≤ ofReal (δ (T − t₀) + M) →
  (∀ t ≥ t₀, t ∉ B → c e^{σ φ(t)} ≤ ν(eᵗ)) → False
```

`DensityGrowthWall` asked for the density bound at every horizon, but its proof uses exactly one, so
the horizon becomes a parameter.

**This is the form the dichotomy actually needs, and the reason is a quantifier.**  "The exceptional
set has density below `1/2` at every horizon" is a supremum condition whose negation gives a single
horizon and is worthless downstream.  "There is a horizon where the density is below `1/2`" is a
liminf condition, and *its* negation — the density stays above `1/2` from some point on — is exactly
the hypothesis `DilatedDensityDichotomy` consumes.  The case split can therefore be made on a
statement whose two sides are both usable, which the earlier formulation could not support.

### Correction: the density dichotomy does not close the algebraic case either

Attempting the case split with `LocalisedGrowthWall` and `DilatedDensityDichotomy` fails, and the
reason invalidates the plan recorded three entries ago.  Recording it so the two modules are not
mistaken for a finished argument.

**Density does not localise, and the conclusion needed is local.**  The order-one input is
`ν(r) ≤ C r` for *all* large `r`, i.e. in the logarithmic variable `ν(eˣ) ≤ C eˣ` for all large `x`.
Monotonicity of `ν` spreads a bound from `x′` back to `x` only at the cost of `e^{x′−x}`, so the
spreading window must be **additive** in `x` and of *fixed* length — `x′ ∈ [x, x + W]` gives
`ν(eˣ) ≤ C e^W eˣ`, which is what is wanted.

`DilatedDensityDichotomy` supplies a point of `G₁` in `[r, K r]`, a **multiplicative** window.  In the
logarithmic variable that is `[x, K x]`, and the resulting bound `ν(eˣ) ≤ C e^{Kx}` is exponentially
weaker than needed — useless.

Repairing it would need `volume (G₂ ∩ [x, x + W]) < W` for a fixed `W` at all large `x`, and a bound
on the density of `G₂` over `[t₀, T]` gives no information about a short window: a set of density
zero can still contain intervals of any fixed length arbitrarily far out.

**So the "which branch" problem is genuinely back**, and the earlier note dismissing branch
consistency was premature.  The two modules remain correct and reusable — the localised wall is
strictly stronger than the density wall, and the dilated thin branch is a clean covering statement —
but neither is the tool that closes card 15's algebraic case.  The honest position is that of the
Puiseux entry: what is needed is that `F′` follows a *single* branch at all large radii, so the
exponent `e` is eventually constant and no case split over radii is required at all.

### The branch problem dissolves for the upper bound

`HTGeometry/PointwiseDerivativeBound.lean`, axiom-clean:

```text
exists_norm_deriv_le_of_relation :
  C m ≠ 0 → (∀ z, ∑_{k ≤ m} C_k(F z)·(F′ z)^k = 0) →
  ∃ K R₀, 0 < K ∧ 1 ≤ R₀ ∧ ∀ z, R₀ ≤ ‖F z‖ →
    ‖F′ z‖ ≤ max 1 (K ‖F z‖^{∑_j deg C_j})
```

**This is the way past the "which branch" obstruction, for the half of the argument that needs it.**
The two-sided Newton estimate selects an index pair that may vary with the radius, which is what
defeated the density dichotomy.  The *upper* bound needs no such selection: `mul_le_sum_of_top_dominated`
compares the top term against all the others at once, and the coefficient magnitudes are controlled
by `norm_eval_le_mul_pow` above and `exists_le_norm_eval` below.  Exponent and constant depend only
on the coefficient polynomials.

Consequently, at a Wiman–Valiron radius,

```text
ν(r) ‖F z‖ / (2r) ≤ ‖F′ z‖ ≤ K ‖F z‖^{d}   ⟹   ν(r) ≤ 2K r ‖F z‖^{d−1},
```

so when `d ≤ 1` — with `d` the fixed exponent above — this gives `ν(r) = O(r)` at every window
radius, hence everywhere by monotonicity, with no case split and no density argument.  The residual
difficulty is confined to `d > 1`, where a *lower* bound is needed and the branch genuinely matters.

### The dual pointwise bound, and the exact residual gap

`HTGeometry/BottomCoefficientBound.lean`, axiom-clean:

```text
norm_bottom_le_of_relation :
  (∀ z, ∑_{k ≤ m} C_k(F z)(F′ z)^k = 0) → 1 ≤ ‖F′ z‖ →
    ‖C_0(F z)‖ ≤ (∑_{k ≥ 1} ‖C_k(F z)‖) · ‖F′ z‖^m
```

Reading the relation from the bottom rather than the top.  Like the upper bound it involves no branch
choice — the bottom term is compared against all the others at once — so it too transfers freely
between radii.

**The residual gap can now be stated exactly.**  Write

```text
D_up  := max_{j < m, C_j ≠ 0} (deg C_j − deg C_m)/(m − j)      (sharp upper exponent)
D_low := min_{k ≥ 1, C_k ≠ 0} (deg C_0 − deg C_k)/k            (sharp lower exponent)
```

Then `D_up ≤ 1` gives `ν(r) = O(r)` and `D_low > 1` feeds the growth wall.  Both are uniform in the
radius.  The unresolved case is exactly

```text
D_low ≤ 1 < D_up,
```

whose smallest witness is `W² + Y⁵W + 1 = 0`: the two branches are `‖W‖ ≍ ‖Y‖⁵` and
`‖W‖ ≍ ‖Y‖^{−5}`, and *both* conclusions are acceptable — the large branch feeds the wall, the small
branch makes `ν` tiny — but the argument must know which one `F′` follows at each radius.  That, and
only that, is what branch consistency is needed for.

Checked against the two standard examples: `F′ = F` has `D_up = 1`, so the upper route closes it;
`(℘′)² = 4℘³ − g₂℘ − g₃` has `D_low = 3/2 > 1`, so the wall closes it.  Neither needs the branch.

### Cards 8, 13 and 14 share one obstruction, and it is a single combinatorial fact

Reading card 8 (`asymptotically-exponential-algebraic-cascade-unit-cost`) against the cards 13/14
analysis shows they are the *same* problem, which was not previously recorded.

Card 8's step 2 asks for the observability Jacobian of

```text
δ X_k = ∏_{j ≤ k} A_j(X_j),      A_j(X_j) = λ_j X_j (1 + o(1))
```

and argues that "the leading term is obtained by replacing every `A_j` by `λ_j X_j`, because every
correction has strictly lower exponent in at least one variable".  That is precisely the degeneration
to the model cascade `δ₀ X_k = ∏_{j≤k} λ_j X_j` used by cards 13 and 14, and the corpus already owns
the model determinant's nonvanishing (`ExpAffineCascade.scaled_jet_det_ne_zero`).

**The gap is the same in all three, and it is not the model determinant but its *valuation*.**
Writing `M = m + (corrections)`, the claim needs `v(det M − det m) > v(det m)`.  Each correction term
has valuation at least `min_π ∑ v(m_{iπ(i)})` plus a positive gap — but `v(det m)` can *exceed* that
minimum, because the leading terms of the model determinant cancel.  The entry recorded early in this
session computed the cancellation explicitly: the naive boundary matrix has proportional columns for
`n ≥ 3` and vanishing determinant.

**So all three cards reduce to one statement:** the model determinant `J_n` is a single monomial up to
a nonzero scalar.  Then `v(det m)` is known exactly, the correction terms are strictly above it, and
the degeneration argument goes through for every one of them.  Verified by hand at `n = 2`
(`−λ₁λ₂X₂`) and `n = 3` (`−λ₁³λ₂³λ₃²X₁²X₂X₃²`); the general case is a concrete induction on the
cascade, not an analytic problem.

This is the highest-leverage open item in the folder: one combinatorial lemma unblocks three cards.

### The vocabulary for the shared obstruction

`HTGeometry/ScalarMonomial.lean`, axiom-clean: `IsScalarMonomial p` — `p = monomial s c` with
`c ≠ 0` — with closure under products and powers, the generators `1`, `C c`, `X i`, `(−1)^n`, and
`IsScalarMonomial.ne_zero`.

**Why this is the right next step, from reading the corpus's own proofs.**  The determinant
nonvanishing that cards 8, 13 and 14 all rest on is proved in `ExponentialTowerUnitCost` by two
mutually recursive inductions, and each step of each induction produces a value of the shape

```text
det = (−1)^a · 1 · X^b · (smaller determinant)
```

via `derivationIterateOutputJacobian_det_terminalScaled`.  Every factor there is a scalar monomial.
So replacing the invariant `≠ 0` by `IsScalarMonomial` in `towerJet_det_ne_zero` and
`monomialJetJacobian_det_ne_zero` needs *no new mathematics* — the same reduction equations carry the
stronger conclusion — and `ScaledExponentialCascade` then transports it to `scaled_jet_det_ne_zero`,
because `scaleHom` sends monomials to scalar multiples of monomials.

That yields the single-monomial fact identified above as the shared obstruction, and with it the
valuation of the model determinant, which is exactly what the Newton degeneration from the perturbed
cascade needs.  Hand-verified at `n = 2` and `n = 3`.

### Tower monomial shape, and the one place the induction stalls

`HTGeometry/TowerMonomialShape.lean`, axiom-clean: `IsScalarMonomial.prod` and
`isScalarMonomial_towerMonomial` (`towerMonomial k = ∏_{1 ≤ i ≤ k} X i`).

With these, two of the three determinant results carry the strengthened invariant with no new
mathematics, because their proofs are *equational*:

* `monomialJetJacobian_det = (−1)^a · towerMonomial(s+1) · towerMonomial(s+2)^b · sumJacobian_det`
* `towerJet_det = (−1)^a · 1 · X_{s+2}^b · monomialJetJacobian_det`

Every explicit factor is a scalar monomial by the new lemmas.

**The induction stalls at `sumJacobian_det_ne_zero`, and the reason is its proof style.**  That one is
proved *by contradiction* — assume the determinant vanishes, push it through `topSub`, the column
pencil and the leading-coefficient extraction, and derive a contradiction from a minor.  It never
produces a value for the determinant, so there is nothing to strengthen: `≠ 0` is all the argument
yields.

So the shared obstruction of cards 8, 13 and 14 now has a single precise location: **make
`sumJacobian_det_ne_zero` constructive** — compute `det (sumJacobian (k+1))` rather than refute its
vanishing.  The pencil machinery already isolates the leading column data
(`det_columnLeading_smul_add`, `det_columnLeading_of_row_zero`), which express the determinant as
`towerMonomial(k+1)^{k+2} · (−1)^{k+1} · (minor)`; what is missing is the same treatment of the minor,
by induction, in place of the contradiction step.

### Why the constructive rewrite is not a reformatting job

Tracing `sumJacobian_det_ne_zero` further shows the contradiction is not incidental to the proof
style — it is what the *pencil* method yields, and that matters for estimating the work.

The chain is: `topSub_sumJacobian` maps `sumJacobian (k+2)` under a ring homomorphism to a
`columnPencil`; `coeff_det_columnPencil` extracts the pencil determinant's *leading coefficient* as
`det (columnLeading …)`; and `det_columnLeading_smul_add` and `det_columnLeading_of_row_zero`
evaluate that leading coefficient as `towerMonomial(k+1)^{k+2} · (−1)^{k+1} · (minor)`.

So the method computes the leading coefficient of the image of the determinant, never the determinant
itself.  Nonvanishing of a leading coefficient gives nonvanishing of the whole — which is why the
proof is a contradiction — but it gives no formula, and a formula is what the Newton degeneration
needs.

**The target is nevertheless sound.**  `ScaledExponentialCascade` shows the cascade determinant equals
a constant times `scaleHom` of the tower determinant, so the cascade computations
`J₂ = −λ₁λ₂X₂` and `J₃ = −λ₁³λ₂³λ₃²X₁²X₂X₃²` — both single monomials — say that the tower
determinant, and with it `det (sumJacobian)`, is a single monomial too.  What is missing is a proof
that computes it: an induction evaluating `det (sumJacobian (k+1))` outright, rather than the pencil
argument that only certifies it nonzero.

Estimated shape: the same column-pencil decomposition, but retaining every coefficient of the pencil
polynomial instead of the leading one, so that the recursion returns a value.  That is a rewrite of
`ExponentialTowerSumJacobian`, not a patch — the honest cost of unblocking cards 8, 13 and 14.

### REFUTED: the model determinant is not a single monomial

Computing `sumJacobian 2` explicitly refutes the "single monomial" target proposed above.  This
matters more than any of the modules built for it, so it is recorded in full.

`towerSum 2 = 1 + X₁ + X₁X₂` and `δ(towerSum 2) = X₁ + X₁X₂ + X₁²X₂`, so

```text
sumJacobian 2 = [ 1 + X₂            X₁        ]
                [ 1 + X₂ + 2X₁X₂    X₁ + X₁²  ]
```

whose determinant is `(1+X₂)(X₁+X₁²) − X₁(1+X₂+2X₁X₂) = X₁² − X₁²X₂ = X₁²(1 − X₂)` — **not** a
monomial.

Feeding that through the two equational reductions:

```text
det (monomialJetJacobian 3) = ± towerMonomial 2 · towerMonomial 3^b · det (sumJacobian 2)
det (towerJet Jacobian, height 4) = ± X₄^{b'} · det (monomialJetJacobian 3)
```

so the height-4 model determinant carries the factor `(1 − X₂)` and is not a single monomial either.

The `n = 2` and `n = 3` computations that suggested the conjecture are genuine — `−X₂` and
`−X₁²X₂X₃²` — but they are the smallest cases, and the offset in the reduction means the first
`sumJacobian` with any content is `sumJacobian 2`, which appears only at height four.  Checking one
case further would have refuted it immediately.

**Consequence for cards 8, 13 and 14.**  The Newton degeneration cannot be justified by "the model
determinant is a monomial, so its valuation is known".  What is true, and what the corpus proves, is
that the determinant's *leading coefficient under the column pencil* is a monomial multiple of a
smaller determinant.  So the degeneration must be run against that graded leading data, not against
the determinant as a whole — which is the same conclusion the early entry on cards 13/14 reached
from the other direction, when the naive product-form bounds gave `det L = 0`.

## Picard's little theorem is now proved, and it opens the autonomous order-one route

### Built: `HTGeometry/JensenProximityReciprocalBound.lean`, `HTGeometry/PicardLittleTheorem.lean`

`eq_const_of_omits_two` — **an entire function that omits two distinct values is constant** — is
proved unconditionally and is axiom-clean.  So is the sharp restatement
`subsingleton_compl_range_of_nonconstant`: the complement of the range of a nonconstant entire
function is a subsingleton.  Mathlib has no Picard theorem of any kind (only Picard--Lindelöf), and
the corpus had only the characteristic bound, not the conclusion.

The one missing analytic step was the ramification term.  The zero-free identity
`m(r,1/g) = m(r,g) − log‖g(0)‖` needs `g` zero-free, which is why every earlier statement in this
lane carried the hypothesis `∀ z, deriv F z ≠ 0`.  The repair is that Jensen's formula degrades to an
*inequality* in the direction one wants: for entire `g` the divisor is non-negative, so its
logarithmic counting function is non-negative and

```text
log‖c(g)‖ ≤ ⨍ log‖g‖,   hence   m(r, 1/g) ≤ m(r, g) − log‖c(g)‖,
```

with `c(g)` the trailing coefficient at the origin (`proximity_inv_le_sub`).  The zeros of `g` only
help.  With that substitution the whole chain — the omitting second main theorem, the quantitative
`T(r) ≤ log T(R)` bound, the Borel window collapse — runs with the derivative allowed to vanish; the
nonvanishing the second main theorem actually needs is codiscrete, and the derivative of a
nonconstant entire function is a nonzero entire function.

### The route this opens for card 15's algebraic case

The card's remaining input is: *an entire solution of an autonomous first-order algebraic
differential equation has order at most one*.  The following route uses only assets the corpus
already owns, and in particular needs **no Puiseux series** — mathlib has none.

Write the relation as `∑_{k ≤ m} C_k(F)·(F′)^k = 0` with `C_m ≠ 0`.

1. **Exponent quantization.**  At a root `w` of `∑_k c_k w^k` the maximal term is attained twice up
   to the factor `m`, so `∃ k < j` with `|w|^{j−k} ≍ |c_k|/|c_j|`.  With `c_i = C_i(y)` and
   `|C_i(y)| ≍ |y|^{deg C_i}` for `|y| ≥ R₀`, this gives `|w| ≍ |y|^{D}` for `D` one of the finitely
   many rationals `(deg C_k − deg C_j)/(j−k)`.  Hence the pointwise **dichotomy**: there are
   constants `C, c, ε > 0` depending only on the `C_k` with, for every `z` with `‖F z‖ ≥ R₀`,

   ```text
   ‖F′ z‖ ≤ C‖F z‖    or    ‖F′ z‖ ≥ c‖F z‖^{1+ε}.
   ```

   `ε` is the gap between `1` and the least element of the finite exponent set exceeding `1`.
   Assets: `PolynomialMagnitudeBalance`, `TopCoefficientBound`, `TwoSidedBalancing`,
   `VanishingPowerSum`.

2. **The Wiman--Valiron ratio, in window form.**  At the good radii,
   `F′(z_r)/F(z_r) ≈ ν(r)/z_r`, so `‖F′(z_r)‖ ≍ (ν(r)/r)·M(r)`.  Asset:
   `WimanValironAsymptotic.exists_radius_point_logDeriv_close_centralIndex_window` — the good radii
   are dense in every window, not merely cofinal.

3. **The two branches of the dichotomy.**
   * Second branch at some large radius: `ν(r) ≥ c·r·M(r)^ε`.  Since `ν` is **monotone** and
     `ν(r)·log s ≤ log μ(rs) − log μ(r)` (`CentralIndexGrowthWall.centralIndex_mul_le_logMaxTerm_sub`),
     one radius with huge `ν` forces `log μ(2r) ≳ r·μ(r)^ε`, which the growth walls forbid
     (`false_of_centralIndex_ge_exp_mul_logMaxTerm`, `false_of_centralIndex_ge_rpow`).
   * First branch at all large good radii: `ν(r) ≤ C·r` there.  **Monotonicity of `ν` plus the window
     form of Wiman--Valiron transports this to every radius**: given `t`, take a good radius
     `r ∈ [t, t+W]`, then `ν(t) ≤ ν(r) ≤ C(t+W)`.  Then
     `CentralIndexLinearOrderOne.log_maxTerm_le_linear_of_centralIndex_le_linear` gives order one.

Monotonicity of the central index is what repairs the localization failure recorded earlier in this
ledger: the density dichotomy failed because density does not localize, but a *monotone* quantity
needs only one good radius per window, which is exactly what the window form of Wiman--Valiron
supplies.  This is the first route in this lane that does not stall on branch consistency.

### Built: the dichotomy and the Grönwall half; and why the growth walls cannot finish the other half

Two more modules are in the tree, both axiom-clean.

* `HTGeometry/AutonomousExponentDichotomy.lean` — `exists_deriv_dichotomy_of_relation`.  There are
  constants `K ≥ 1`, `0 < c ≤ 1`, `R₀ ≥ 1`, depending only on the coefficient polynomials, with

  ```text
  ∀ z, R₀ ≤ ‖F z‖ →  ‖F′ z‖ ≤ K‖F z‖   ∨   c‖F z‖^{m+1} ≤ ‖F′ z‖^m.
  ```

  The gap is real, not an artefact: the Newton exponent is `(d_u − d_v)/(v − u)` with integer data
  and `v − u ≤ m`, so it cannot lie strictly between `1` and `1 + 1/m`.  Both alternatives are stated
  with natural-number powers, so no real exponentiation appears.

* `HTGeometry/EntireGronwallExponentialType.lean` — `norm_le_mul_exp_of_norm_deriv_le`.  If
  `‖F′ z‖ ≤ K(1 + ‖F z‖)` everywhere then `‖F z‖ ≤ (1 + ‖F 0‖)e^{K‖z‖}`: Grönwall's integral
  inequality along the ray `t ↦ t·z`, using mathlib's
  `norm_le_gronwallBound_of_norm_deriv_right_le`.  This is the tame alternative's conclusion — order
  one and finite exponential type — with no hypothesis beyond the pointwise bound.

**The wild alternative cannot be excluded by growth alone.**  This is worth recording, because the
attempt looks promising and fails for a structural reason.

Suppose the wild alternative holds at a Wiman--Valiron point of some window.  Then
`ν(r)^m ≥ c·μ(r)·r^m`, and monotonicity of `ν` transports it to every radius *with a lag*: for every
`t` there is a good radius `x ∈ [t − W − 1, t]`, so

```text
ν(e^t) ≥ c₁·e^{t−W−1}·μ(e^{t−W−1})^{1/m}.
```

The growth walls need the estimate *without* the lag.  With it the finite-time blow-up argument
breaks: writing `g(t) = log μ(e^t)`, the hypothesis is a **delay** differential inequality
`g′(t) ≥ c₁e^{t−W}·exp(σ·g(t−W))`, and such an inequality has finite solutions — define `g` on the
`n`-th interval of length `W` to be a tower `T_n` with `T_n ≈ T_{n−1} + W·exp(σT_{n−1})`.  The lag
lets the solution outrun its own driving term, so no contradiction is available.  The same objection
kills the variants through `ν(r) ≤ log μ(r²)/log r` and through the Cauchy estimate
`M(r,F′) ≤ M(2r,F)/r`: every one of them reduces to a doubling- or shift-lagged inequality, and every
such inequality is satisfiable by a fast enough entire function.  Entire functions may grow
arbitrarily fast, so *no* pure growth argument can exclude the wild branch.

What the wild branch actually contradicts is the local dynamics — `F′ ≈ F^{D}` with `D > 1` blows up
in finite time — and that is a statement about the flow, not about `μ` and `ν`.

Two structural facts that a future attempt should start from, both cheap:

1. **The branch is locally constant.**  For `‖F z‖ > R₁ := max(R₀, (K/c′)^m)` the two alternatives are
   mutually exclusive, and each is an open condition, so the branch is constant on every connected
   component of `Ω = {z : ‖F z‖ > R₁}`.
2. **Every component of `Ω` is unbounded**, by the maximum modulus principle: on a bounded component
   `‖F‖ = R₁` on the boundary, forcing `‖F‖ ≤ R₁` inside.

So the wild branch, if it occurs, occurs on an unbounded component throughout — which is exactly the
configuration the finite-time blow-up argument contradicts, and exactly the configuration that
`1/F` makes accessible: on such a component `F` is zero-free, `g = 1/F` is holomorphic with
`‖g‖ < 1/R₁` and `‖g′‖ ≥ c‖g‖^{1−1/m}`.  Bounding `g′` on discs inside the component by Cauchy gives
`‖F(z₀)‖ ≥ (c·R₁·ρ)^{m/(m−1)}` for every disc `D(z₀,ρ) ⊆ Ω`, i.e. the component must be *thin*.  A
quantitative form of that thinness, against the fact that the component is unbounded, is the missing
step.

#### The wild branch, reduced to one conformal statement

On a component `V` of `Ω` carrying the wild branch, put `ε = 1/m`, `g = 1/F` (holomorphic and
zero-free on `V`, with `‖g‖ < 1/R₁`) and, on a simply connected piece, `h = g^ε/ε`.  Then

```text
h′ = g^{ε−1}g′,    so   ‖h′‖ = ‖g‖^{ε−1}‖g′‖ = ‖F′‖ / ‖F‖^{1+ε} ,
```

and the wild branch says exactly `‖h′‖ ≥ c′`, while the sharp Newton upper bound says
`‖h′‖ ≤ C′`.  So the wild branch is the statement that `h` is a holomorphic map with derivative
bounded above and below, from `V` into the disc of radius `B = (1/R₁)^ε/ε`, and `‖h‖ → B` at the
finite boundary of `V` because `‖F‖ = R₁` there.

If `h` were proper onto that disc it would be an unbranched cover of a simply connected target, hence
a biholomorphism, and its inverse would be `1/c′`-Lipschitz — forcing `diam V ≤ 2B/c′` and
contradicting the unboundedness of every component.  **The single missing point is properness at the
end of `V` at infinity**, where `‖F‖ → ∞` and hence `‖h‖ → 0` rather than `B`.  That end is what an
argument must close; it is the same end that the finite-time blow-up argument would rule out.

This is a genuinely smaller target than "branch consistency at all radii", and it is conformal
geometry rather than Newton--Puiseux theory, so it does not need the Puiseux series mathlib lacks.

## The Euler relation closes card 15's input, except for one degenerate Newton case

Card 15's decisive input is **not** `F′ = c(F)` in the abstract: the card's own equation is
`x f′(x) = c(f(x))` with `f` entire, and it needs only the conclusion *`f` is a polynomial*, which
contradicts the assumed transcendence.  That is a much better target than the Briot--Bouquet
classification, and it is now proved except in one case.

### Built: `HTGeometry/EulerAutonomousPolynomial.lean`

`eventually_taylorCoeff_eq_zero_of_euler_relation` — an entire `f` with
`∑_{k ≤ m} C_k(f)·(z f′)^k = 0` has only finitely many nonzero Taylor coefficients, provided some
index `ms ≥ 1` carries the maximal total degree `deg C_k + k` and is the largest such index.
Axiom-clean.  The mechanism, which took the whole of this session's machinery:

1. The corpus already owns **Gol'dberg's theorem** (`GoldbergCentralIndex`,
   `exists_centralIndex_le_pow_of_relation`): a first-order algebraic relation with polynomial
   coefficients in `z` makes the central index polynomial in the radius.  Expanding
   `∑_k C_k(f)(z f′)^k` into monomials `(A p).eval z · f^{p.1} · (f′)^{p.2}` with
   `A (j,k) = C((C k).coeff j)·X^k` puts the relation in exactly that form; the total degree of the
   monomial `(j,k)` is `j + k`, so the index `ms` is what Gol'dberg calls the top symbol.
2. At a Wiman--Valiron radius, `z f′/f` is within `ν/2` of the central index `ν(r)`, so the exponent
   dichotomy of the relation becomes a dichotomy for `ν`:
   `ν(r) ≤ 2K` or `c·μ(r) ≤ (3ν(r)/2)^m`.
3. `ν(r) → ∞` for a transcendental function, so the tame alternative fails at every large radius.
   The wild one, with Gol'dberg's polynomial bound, gives `μ(r) ≤ B·r^{Kg·m}` at the good radii;
   monotonicity of `μ` and the window form of Wiman--Valiron spread it to *every* large radius.
4. A transcendental maximum term outgrows every power (`tendsto_maxTerm_div_pow_atTop`).

The intermediate `false_of_euler_relation_of_centralIndex_le_pow` states steps 2--4 on their own, with
the polynomial central-index bound as an explicit hypothesis.

### The one remaining case, and its route

The hypothesis on `ms` fails exactly when the maximal total degree is attained **only** at `k = 0`,
that is when `deg C_0 > deg C_k + k` for every `k ≥ 1`.  Gol'dberg's theorem as formalized needs
`1 ≤ ms`, and the smallest example is real: `z f′ + f^{10} = 0`.

In that case the tame alternative is impossible *at every point where `‖f‖` is large* — comparing
`|C_0(f)| ≥ L‖f‖^{deg C_0}` against `∑_{k ≥ 1}|C_k(f)|·(K‖f‖)^k ≤ mAK^m‖f‖^{d₁}` with
`d₁ = max_{k ≥ 1}(deg C_k + k) < deg C_0` bounds `‖f‖`.  So the wild bound
`c‖f‖^{m+1} ≤ ‖z f′‖^m` holds everywhere `‖f‖ ≥ R₂`, and hence, after taking `log⁺` and absorbing the
bounded region into a constant,

```text
m·log⁺‖z f′(z)‖ ≥ (m+1)·log⁺‖f z‖ − E    for every z.
```

Integrating over the circle and using `m(r, z f′) ≤ log⁺ r + m(r,f′)` and
`m(r,f′) ≤ m(r,f) + m(r,f′/f)` gives, for entire `f` where `m = T`,

```text
T(r,f) ≤ m·m(r, f′/f) + m·log r + E,
```

which is `T ≤ S(r,f) + O(log r)` — the same collapse that proved Picard, and it forces
`T(r,f) = O(log r)`, hence a polynomial.  The one piece not yet assembled is the logarithmic-derivative
estimate *with* its divisor term: `proximity_logDeriv_sub_const_le` carries
`∑ᶠ_u |divisor f (closedBall 0 |R|) u|^α`, which vanished in the omitted-value application but here
must be bounded by the zero-counting function and then by `T(2R,f)` (mathlib's
`AnalyticOnNhd.sum_divisor_le` is the Jensen inequality for that), and its hypothesis that the divisor
vanishes on the sphere `|z| = R` must be met by choosing `R` off the discrete zero set
(`GoodRadiusSelection`).  With those two, the collapse of `OmittedValueLogarithmicGrowth` applies
verbatim.

### The dominant-constant-term case: three of its four steps are built

The case Gol'dberg does not reach is now attacked directly, and the analytic content is in place.

* `HTGeometry/DominantConstantTermWild.lean` — `exists_not_tame_of_dominant_constant_term`.  If
  `deg C_k + k < deg C_0` for every `1 ≤ k ≤ m`, then `‖W‖ ≤ K‖Y‖` is impossible once `‖Y‖` is large:
  it would bound `L‖Y‖^{deg C_0}` by `B‖Y‖^{deg C_0 − 1}`.
* `HTGeometry/EulerWildProximity.lean` — `proximity_id_eq` (`m(r, z) = log⁺ r`) and
  `characteristic_le_logDeriv_of_wild`.  From the pointwise wild bound,
  `(m+1)log⁺‖f‖ ≤ m·log⁺‖z f′‖ + E` at every point — the region `‖f‖ < R₂` is absorbed into the
  constant — and integrating over the circle with
  `m(r, z f′) ≤ log⁺ r + m(r,f′) ≤ log⁺ r + m(r,f) + m(r,f′/f)` gives, for entire `f`,

  ```text
  T(r,f) ≤ m·m(r, f′/f) + m·log r + E .
  ```
* `HTGeometry/EulerDominantConstantTerm.lean` — combines the two with the exponent dichotomy:
  `exists_wild_of_dominant_constant_term` (the wild bound at every point where `‖f‖` is large) and
  `exists_characteristic_le_logDeriv_of_dominant_constant_term` (the displayed inequality, with the
  constant existentially quantified).
* `HTGeometry/LogSelfBoundArithmetic.lean` gains `le_of_le_add_mul_log`: `T ≤ A + c·log(T+1)` forces
  `T ≤ 2A + 2c|log 4c| + 1`, the self-bound collapse with an arbitrary logarithmic coefficient (the
  earlier lemma was fixed at coefficient six).

**The one step left** is the same collapse that finished Picard, applied to `m(r,f′/f)` for a function
whose zeros are not controlled.  The tool for it is already in the corpus:
`LogDerivCountingBound.circleAverage_posLog_logDeriv_le_counting` is Nevanlinna's estimate with the
divisor weight already replaced by counting functions,

```text
m(r, f′/f) ≤ (1/α)·log(1 + (2π)⁻¹·(log 2)⁻¹·(N(2R,f,∞) + N(2R,f,0))·(r^{-α}·k(α) + 2π(R−r)^{-α})
                        + (2R/(R−r)²·(2T(R,f) + c₀))^α) .
```

For entire `f` the first counting term vanishes and the second is at most `T(2R,f) + O(1)` by the
first main theorem, so with `α = 1/2`, `R = r + (T(r)+1)^{-1/2}` and the Borel window lemma the right
side is `O(log r + log(T(r)+1))`; `le_of_le_add_mul_log` then gives `T(r) = O(log r)`, hence a
polynomial by `tendsto_maxTerm_div_pow_atTop`.  The remaining work is bookkeeping of exactly the kind
`OmittedValueCharacteristicBound` and `OmittedValueLogarithmicGrowth` already carry out, with the
counting term carried along instead of vanishing.

## Card 15's analytic input is closed, unconditionally

`HTGeometry/WildCharacteristicCollapse.lean` proves
`eventually_taylorCoeff_eq_zero_of_euler_relation_general`:

> An entire `f` satisfying `∑_{k ≤ m} C_k(f)·(z f′)^k = 0` with `C_m ≠ 0` and `m ≥ 1` has only
> finitely many nonzero Taylor coefficients.

No hypothesis on the Newton configuration; axiom-clean.  This is exactly the input card 15 needs:
its equation is `x f′(x) = c(f(x))` with `c` algebraic, so `f` is a polynomial, contradicting the
assumed transcendence.

The proof splits on the largest index `ms` carrying the maximal total degree `deg C_k + k`.

* `ms ≥ 1`: Gol'dberg's theorem (already in the corpus) makes the central index polynomial in the
  radius, and the exponent dichotomy at the Wiman--Valiron radii then bounds the maximum term by a
  power of the radius — impossible for a transcendental function.
* `ms = 0`: the constant term dominates, so the *tame* alternative of the dichotomy is impossible
  wherever `‖f‖` is large, and the wild bound `c‖f‖^{m+1} ≤ ‖z f′‖^m` holds at every such point.
  Integrating its `log⁺` over the circle gives `T(r,f) ≤ m·m(r, f′/(f−a)) + m·log r + E`, and the
  logarithmic-derivative estimate collapses that to `T(r,f) = O(log r)`.

### How the second case avoids the doubling obstruction

The corpus's counting form of the logarithmic-derivative estimate bounds the divisor mass by counting
functions at **twice** the radius, and `T(2r)` is not controlled by the Borel window — the resulting
inequality `T(x) ≲ log T(2x)` is satisfiable by a tower, so that route cannot close.  The repair is to
bound the mass at radius `R` by Jensen's inequality against the maximum modulus on a circle of radius
`R′` only slightly larger, and then by the characteristic at `R″` slightly larger still, using the
Poisson--Jensen constant `(R″+R′)/(R″−R′)` of `MaxModulusCharacteristicBound.posLog_norm_le_characteristic`.
All three radii sit inside the Borel window `[x, x + (T(x)+1)^{-1/2}]`, so every characteristic that
appears is `≤ 2T(x) + 1`, and the widths only cost powers of `T(x)+1` inside a logarithm.

New modules for that argument:

| Module | Content |
|---|---|
| `ZeroFreeRadiusSelection` | a radius in any interval whose circle carries no zero — the hypothesis the estimate needs |
| `DivisorMassCharacteristic` | `divisorMass_le_characteristic`: Jensen plus Poisson--Jensen, with three nearby radii |
| `WildCharacteristicCollapse` | the per-radius bound, the Borel assembly, and the two-case theorem |

`EulerWildProximity` also gained `characteristic_le_logDeriv_shift_of_wild`, which takes the
logarithmic derivative at a shift `f − a` chosen so that the shifted function is `1` at the origin;
that makes both the Jensen bound and the germ constant of the estimate trivial.

## Card 15 CLOSED (2026-09-01)

`nonautonomous-cap-linear-order-two-shadow-rigidity` is fully formalized and moved to
`3-formalized`.  Five new modules, all axiom-clean and wired into `HTGeometry.lean`:

| Module | Content |
|---|---|
| `DerivationAlgebraicStability` | the corpus's derivation-stability lemmas, restated for an explicitly supplied `Derivation ℤ` or `Derivation ℂ` instead of the ambient `Differential` instance: kernel field, "kills everything algebraic over the kernel", "stabilises the relative algebraic closure of a stable base" |
| `AdjoinSingletonAlgebraicWitness` | `exists_polynomialCoeff_relation_of_isAlgebraic_adjoin_singleton` — the univariate form of `algebraicWitness_of_isAlgebraic_adjoin`: algebraicity over `K[t]` gives a relation with *polynomial* coefficients in `t` and nonzero leading one |
| `EulerCompositionPolynomialRigidity` | the substituted Euler relation: `analyticMeroElement_eulerComp`, `exists_polynomial_of_eventually_taylorCoeff_eq_zero`, and `exists_polynomial_of_euler_mero_relation` (a vanishing polynomial expression in `f∘g` and `g·(f′∘g)` makes `f` a polynomial) |
| `EulerMatchingCompositionState` | `exists_polynomial_of_euler_matching`: if a derivation with `∂_x g = 1`, `∂_x (f∘g) = 0` kills `g·(f′∘g)`, then `f` is a polynomial |
| `NonautonomousCapLinearOrderTwo` | the state family, the observability Jacobian, and `daRank_comp_linear_order_two` |

### The two things worth recording

**Briot–Bouquet is not needed, and neither is the Wiman–Valiron route.**  The card's decisive input
was already closed analytically by `eventually_taylorCoeff_eq_zero_of_euler_relation_general`; what
this session added is the *bridge* from the differential-algebra degeneration to that input.  The
bridge is not a classification of solutions — it is a transcendence count:

> `∂_x(x A) = 0` with `∂_x g = 1` and `∂_x (f∘g) = 0`, plus `trdeg ℂ(g, f∘g, A) = 2`, forces
> `g·(f′∘g)` to be algebraic over `ℂ[f∘g]`.

If it were transcendental, `{g·(f′∘g), f∘g}` would be independent, and `g` — which `∂_x` moves, so
`g` cannot be algebraic over the field `∂_x` kills — would add a third transcendence degree inside a
field of degree two.  The rest is `algebraicWitness`-style denominator clearing.

**The chain rule is a derivation-difference argument, not Faà di Bruno.**  `D` and
`∂_z + v ∂_x + (qv + px) ∂_v + (Av) ∂_y` are two derivations of the meromorphic field agreeing on
the four generators; their difference therefore kills everything algebraic over the state field, in
particular `A = f′∘g`.  That yields `A₂ = ∂_x A + A ∂_y A` — i.e. the card's `C = A_x + A_y A` — with
no jet combinatorics at all, and it is what makes `∂_v A₂ = 0` available for the determinant.

Naming trap recorded: `derivation_eq_zero_of_mem_adjoin` already exists in
`JetPrincipalSymbolExtraction` for base-field derivations, so the `Derivation ℤ` variants here are
named `derivationInt_*` to keep the umbrella importable.

## Card 8 started (2026-09-01): the growth half is built

`HTGeometry/SuperGaussianCentralIndex.lean` (axiom-clean, wired) proves the card's step 1 in
central-index form, which is the form the Wiman--Valiron layer consumes:

| Statement | Lean theorem |
|---|---|
| a Gaussian bound has a positive constant once a coefficient is nonzero | `pos_of_gaussian_decay` |
| `‖a n‖ ≤ M e^{−A n²}` forces `ν(r) ≤ 2 log r / A` past the threshold | `centralIndex_le_of_gaussian_decay_of_lt` |
| the threshold is met at every large radius | `eventually_gaussian_threshold`, `eventually_centralIndex_le_of_gaussian_decay` |
| **the estimate for every `A > 0` makes `ν(r) = o(log r)`** | `tendsto_centralIndex_div_log_zero` |

The proof is two lines of arithmetic: if `ν ≥ 2L/A` with `L = log r` then
`−Aν² + νL = ν(L − Aν) ≤ −νL ≤ −2L²/A`, so the central term `‖a_ν‖r^ν ≤ M e^{−2L²/A}` sinks below the
fixed term `‖a_{n₀}‖r^{n₀} ≥ ‖a_{n₀}‖`.  No integral, no theta bound, no Gaussian sum: the
completing-the-square estimate of the card's step 1 is only needed for the *maximum modulus*, and the
central index is what the differential-order argument actually uses.

### Route audit for card 8's remaining half, and the exact obstruction

The card's remaining input is Valiron--Zimogljad--Strelitz: a transcendental entire solution of an
ADE of order at most two has positive order.  With the growth half above, what is needed is the
weaker `ν(r) = o(log r)` is impossible.

**The corpus's first-order layer is exactly the right shape.**  `TopSymbolWimanPlace`
(`exists_radius_norm_topSymbol_le`) and `NewtonWeightPositiveOrder` (the face inequality
`exists_radius_wimanFace`, the weight collapse, the tie collapse, and the positive-order readings)
carry out precisely this analysis for relations `∑ A_p(z) f^{p₁} (f′)^{p₂}`, and their conclusions —
`ν^{q₂}·r ≤ C·ν^P`, `ν^{q₂} r^{deg+1} ≤ 2 r^{q₂+1}` — contradict `ν = o(log r)` immediately.  So the
work for card 8 is to redo that layer for triples `f^{p₁}(f′)^{p₂}(f″)^{p₃}`.

**The single missing analytic input is the second-derivative Wiman--Valiron estimate**
`z² f″(z)/f(z) ≈ ν(ν−1)` at a Wiman place; the corpus has only the first-derivative form
(`MaximumTermLogarithmicDerivative.norm_mul_logDeriv_sub_centralIndex_le_sharp`,
`WimanValironWindowEstimate`).

**Two naive routes are ruled out, and it is worth recording why.**

1. *Substituting `f″ ↦ (f′)²/f` and quoting the first-order layer.*  The substitution
   `Y₁ ↦ Y₀T, Y₂ ↦ Y₀T²` has kernel exactly `(Y₀Y₂ − Y₁²)`, so a relation in that ideal — e.g. the
   Wronskian relation satisfied by `A e^{cz}` — is invisible to it.  That case is separately fine
   (`f f″ = (f′)²` forces `f = A e^{cz}`, of order one), and since the annihilating ideal of `f` is
   prime one may assume `P ∉ (Y₀Y₂ − Y₁²)`.  But the substitution *merges* monomials of equal
   `(|α|, α₁ + 2α₂)`, and merging can cancel leading coefficients while the Wiman--Valiron error term
   still sees the individual, larger, monomials.
2. *Reducing `P` to normal form modulo `Y₀Y₂ − Y₁²` first.*  The normal form has at most one monomial
   per `(|α|, α₁+2α₂)` class, so it has no merging cancellation — but the discarded part
   `(Y₀Y₂ − Y₁²)·S` contributes `f²(v − u²)·S`, which is only smaller by the Wiman--Valiron error
   `δ ≍ ν^{−1/2}`, and `δ` dominates the `ν^{−1}` gap between adjacent Newton groups whenever
   `ν = o(log r)`.  So the reduction does not by itself remove the tie problem.

The corpus's own first-order treatment *does* solve the tie problem
(`exists_radius_tieCollapse`, `not_transcendental_of_tie_dominant`), so the honest route for card 8 is
to extend that treatment, not to look for a substitution trick.

### Card 8: the second-derivative Wiman--Valiron estimate is a two-moment consequence

Extending the corpus's Wiman--Valiron layer to `f″` does **not** require redoing the moment stack.
With `c_n` the normalised coefficients at the maximum point and `ν` the central index,

```text
z f′/f − ν            = S₁/S₀,          S_k := ∑ (n − ν)^k c_n,
z² f″/f − ν(ν−1)      = S₂/S₀ + (2ν − 1)·(z f′/f − ν),
```

because `n(n−1) − ν(ν−1) = (n − ν)(n + ν − 1)`.  So the second-derivative estimate needs exactly two
things the corpus already has:

* the first-derivative estimate in relative form,
  `WimanValironAsymptotic.exists_radius_point_logDeriv_close_centralIndex`:
  `‖z f′/f − ν‖ ≤ ε·ν` at radii beyond every bound;
* the **second moment** `∑ (n − ν)² ‖a_n‖ r^n ≤ (N²√(2N+1) + 2G₂)·μ(r)`
  (`MaximumTermProfileMoments.tsum_index_sq_le_gaussian`), divided by `‖f(z)‖ ≥ μ(r)`.

Since the first-derivative bound is itself the Cauchy--Schwarz geometric mean of the zeroth and
second moments, the second moment is `O((εν)²)` in the same selection, so

```text
‖z² f″/f − ν(ν−1)‖ ≤ (εν)² + (2ν + 1)·εν = O(ε ν²).
```

**The build for card 8 is therefore:**

1. extend the selection chain `WimanValironWindowEstimate → WimanValironRadius →
   WimanValironAsymptotic` so that the selected radius also reports the second-moment bound
   (the moment bound is already proved; only the plumbing through the three selection layers is
   missing);
2. package `‖z² f″/f − ν(ν−1)‖ ≤ ε ν²` as the order-two companion of
   `exists_radius_point_logDeriv_close_centralIndex`;
3. redo `TopSymbolWimanPlace` and the face inequality of `NewtonWeightPositiveOrder` for triples
   `f^{p₁}(f′)^{p₂}(f″)^{p₃}`, with Newton weight `deg A_p − p₂ − 2p₃` and `ν`-power `p₂ + 2p₃`;
4. read off the contradiction with `ν(r) = o(log r)`, which every conclusion of that layer already
   delivers (`ν^{q}·r ≤ C·ν^{P}` and its variants).

### Card 8: the order-two Wiman--Valiron window estimate is built (2026-09-01)

Two new modules, axiom-clean and wired:

* `HTGeometry/SecondDerivativeDeviationSeries.lean` — `derivCoeffs`, `entireCoeffs_derivCoeffs`,
  `deriv_coeffFun_eq` (the derivative is the series of the shifted coefficients),
  **`mul_sq_deriv2_coeffFun_eq`** (`z² f″(z) = ∑ n(n−1) a_n z^n`),
  **`mul_sq_deriv2_sub_eq_tsum`** and **`norm_mul_sq_deriv2_sub_le`**:

  ```text
  z² f″ − k(k−1) f = ∑ (n − k)² a_n z^n + (2k − 1)·(z f′ − k f),
  ```

  because `n(n−1) − k(k−1) = (n − k)(n + k − 1)`.
* `HTGeometry/SecondDerivativeWimanValironWindow.lean` — `window_mass_le_sqrt` (the window carries at
  most `√(2N+1)` times the value, from `sum_window_le_sqrt_card_mul_bound`) and
  **`norm_mul_sq_deriv2_div_sub_le`**: at a maximum-modulus point, for *any* bound `E` of the
  order-one defect,

  ```text
  ‖z² f″/f − ν(ν−1)‖ ≤ (N²√(2N+1) + 2G₂) + (2ν + 1)·E .
  ```

  No new moment analysis is needed: the second moment is `tsum_index_sq_le_gaussian` and the value
  bound is `‖f(z)‖ ≥ μ(r)`.

**What is left for the order-two asymptotic.**  The corpus's selection chain
(`WimanValironRadius → WimanValironPolynomialBound → WimanValironSmallWindow →
WimanValironAsymptotic`) consumes the window hypotheses and returns only the order-one bound, so the
order-two conclusion cannot be composed onto `exists_radius_point_logDeriv_close_centralIndex`.  The
right refactor is one new *data* selection theorem that exposes, at the selected radius, the point
`z` together with `hz`, `hfz`, `hmax`, `hcrit`, the Lipschitz pair and the tail bounds `G₀, G₂` —
everything both window estimates ask for — mirroring the parameter choices
(`w = T₀^{1/100}`, `s = w^64`, `H = 6 log s / s`, `δ = T₀^{−1/4}`) of
`exists_radius_point_logDeriv_close_centralIndex`.  Both estimates then follow, and `wv_error_le`
(already public and purely arithmetic) tunes the order-one bound; the order-two constant
`N²√(2N+1) + 2G₂` needs the analogous, and much easier, arithmetic bound against `ε ν²`.

### Card 8: the order-two Wiman--Valiron asymptotic is PROVED (2026-09-01)

`HTGeometry/SecondDerivativeWimanValironAsymptotic.lean`, axiom-clean and wired:

> **`exists_radius_point_secondDeriv_close_centralIndex`** — for a transcendental entire function and
> every `ε > 0`, at radii beyond every bound there is a point of the maximum circle with
> ```text
> ‖z f′/f − ν‖ ≤ ε·ν      and      ‖z² f″/f − ν(ν−1)‖ ≤ ε·ν² .
> ```

Five modules, in dependency order:

| Module | Content |
|---|---|
| `SecondDerivativeDeviationSeries` | `z² f″ = ∑ n(n−1)a_n z^n`; the splitting into the squared-deviation series plus `(2k−1)` times the order-one deviation |
| `SecondDerivativeWimanValironWindow` | the window estimate `‖z²f″/f − ν(ν−1)‖ ≤ (N²√(2N+1) + 2G₂) + (2ν+1)E` |
| `WimanValironWindowData` | the corpus selection returning the window *data* rather than the order-one conclusion (reusable; not needed by the chain below) |
| `SecondDerivativeWimanValironRadius` | `wvClosedBound`, `wvSecondMomentBound`, and both estimates at one selected radius |
| `SecondDerivativeWimanValironAsymptotic` | `wv_second_moment_le` (`≤ 148 s²√s`), the parameter tying, the small window, `wv_second_error_le`, and the asymptotic |

**No new moment analysis was needed.**  The whole order-two estimate rests on two facts the corpus
already had: `tsum_index_sq_le_gaussian` (the second moment under Gaussian concentration) and
`sum_window_le_sqrt_card_mul_bound` (the window's mass against the value).  Every arithmetic lemma of
the corpus's tuning — `wv_scale_facts`, `wv_window_le`, `wv_selection_lt`, `wv_rhs_le`,
`wv_tail_ratios_le_one`, `wv_error_le` — was reused verbatim; the only genuinely new arithmetic is
`wv_second_moment_le` and `wv_second_error_le`, and both are two-line power comparisons
(`N ≤ 4s`, `s = w^64`, `ν ≥ w^100/2`, so `148 s²√s = 148 w^160 ≤ (ε/2)ν²` once `1184/ε ≤ w^40`).

**Remaining for card 8.**  Redo `TopSymbolWimanPlace` and the face inequality of
`NewtonWeightPositiveOrder` for triples `f^{p₁}(f′)^{p₂}(f″)^{p₃}`: Newton weight
`deg A_p − p₂ − 2p₃`, `ν`-power `p₂ + 2p₃`.  Every conclusion of that layer
(`ν^{q}·r ≤ C·ν^{P}` and its variants) contradicts `ν(r) = o(log r)`, which
`SuperGaussianCentralIndex.tendsto_centralIndex_div_log_zero` supplies.

### Card 8: the plan for the order-two Newton face, and why cancellation is not an obstacle

Worth recording, because two earlier attempts in this ledger stalled on exactly this point.

The order-two top symbol, cleared of `z`-powers, is

```text
z^{2d}·∑_{|p|=d} A_p(z)·(f′/f)^{p₂}·(f″/f)^{p₃}
  ≈ ∑_{|p|=d} A_p(z)·z^{2d−p₂−2p₃}·ν^{p₂+p₃}(ν−1)^{p₃} .
```

The `ν`-polynomials `ν^{p₂+p₃}(ν−1)^{p₃}` are **linearly independent** for distinct `(p₂,p₃)` — the
multiplicity of the root `0` is `p₂+p₃` and of the root `1` is `p₃`, so both are recoverable — hence
the symbol is a nonzero polynomial in `(z, ν)` whenever some `A_p ≠ 0`.  That is reassuring but *not*
what the proof uses.

What the proof uses is the corpus's own device: `exists_radius_wimanFace` never needs a
non-cancellation hypothesis, because it states a **floor for one monomial and a ceiling for the
others**,

```text
‖lead A_q‖/2 · r^{deg A_q + (2d − q₂ − 2q₃)}·ν^{q₂+2q₃}
  ≤ η·2^{2d}·r^{2d} + K·∑_{p ≠ q} ν^{p₂+2p₃}·r^{deg A_p + (2d − p₂ − 2p₃)} ,
```

obtained from `‖A_q T₁^{q₂}T₂^{q₃}‖ ≤ ‖symbol‖ + ∑_{p≠q}‖A_p T₁^{p₂}T₂^{p₃}‖`.  Cancellation among
the `A_p` is therefore irrelevant: only one coefficient's leading term ever needs a lower bound.  The
Newton weight is `ω_p = deg A_p − p₂ − 2p₃` and the `ν`-power is `p₂ + 2p₃`; a strictly maximal `ω`
makes every competitor lose a full power of `r`, and `ν = o(log r)` then contradicts the resulting
`ν^{k_q}·r ≤ C·ν^{K}` in every branch.

The lower bound on `|f″/f|` that the floor needs is available: the order-two asymptotic gives
`|f″/f| ≥ (ν(ν−1) − εν²)/r²`, positive once `ν ≥ 2`.

### Card 8: the order-two Newton face has a genuine degenerate branch — Wiman--Valiron alone cannot close it

Working the face argument through with the new order-two asymptotic exposes an obstruction that is
*not* an artefact of the packaging, and it explains why Zimogljad's original proof runs to a hundred
pages.

For a top-degree monomial `p = (p₁,p₂,p₃)` the face inequality compares individual terms of size
`r^{ω_p}·ν^{k_p}` with `ω_p = deg A_p − p₂ − 2p₃` and `k_p = p₂ + 2p₃`.  In the **order-one** case
`p` is determined by `p₂` once `|p| = d`, so distinct monomials have distinct `k_p` and the
lexicographic maximum of `(ω_p, k_p)` is always unique — which is exactly why
`NewtonWeightPositiveOrder` can close every branch.  In the **order-two** case
`(p₂,p₃) = (2,0)` and `(0,1)` give the same `k`, so ties are possible, and the tied monomials are
precisely those whose combination is the Wronskian:

```text
A(z) f (f′)² + B(z) f² f″  =  f²·(A(f′)²/f + B f″) ,   A + B = 0  ⟹  −A f·(f f″ − (f′)²).
```

At a Wiman--Valiron point `f f″ − (f′)² = f²·(ν(ν−1) − ν² + O(εν²))/z² = f²(−ν + O(εν²))/z²`.  The
*main* term of the degenerate combination is therefore smaller by a factor `1/ν`, while the
Wiman--Valiron error is `εν²` with `ε` a fixed constant — the error is larger than the main term by
`εν`.  Sharpening `ε` does not help: the classical Wiman--Valiron error for `f^{(k)}/f` is
`(ν/z)^k(1 + O(ν^{−1/2+δ}))`, so the absolute error at `k = 2` is `ν^{3/2} ≫ ν`.

**Conclusion.**  The degenerate branch of the order-two Newton face cannot be closed by the
Wiman--Valiron method at any error quality that method supplies.  Zimogljad's theorem needs a
different tool, and Strelitz's "simpler" proof (Canad. J. Math. 35 (1983)) should be read before any
further Lean work on this branch.  Everything up to the degenerate branch — the order-two
asymptotic, the deviation series, the top-symbol reduction — is now built and is reusable
independently of how the branch is eventually closed.

### Cards 7 and 10: the missing input is pinned down exactly

Huang--Ng, *Hypertranscendency of Perturbations of Hypertranscendental Functions* (arXiv:2007.10037),
Theorem 3 and its Theorem C.  Verbatim:

> **Theorem C (Steinmetz's Reduction Theorem).**  Let `F_j`, `1 ≤ j ≤ N`, be meromorphic on `ℂ`; let
> `h_j` be meromorphic and `g` entire with `T(r,h_j) = O(T(r,g))` outside a set of finite measure.
> Given `F_1(g)h_1 + ⋯ + F_N(g)h_N = 0`, there are polynomials `p_j`, not all zero, with
> `p_1(g)h_1 + ⋯ + p_N(g)h_N = 0`.  Furthermore, if `h_j ≢ 0` for some `j`, there are polynomials
> `Q_j`, not all zero, with `F_1Q_1 + ⋯ + F_NQ_N = 0`.

> **Theorem 3.**  If `f` is hypertranscendental over `ℂ(z)` and `g` is a nonconstant entire function,
> then `f ∘ g` is hypertranscendental over `S_g`.

The deduction is three lines: Faà di Bruno writes
`P(z, f∘g, …, (f∘g)^{(n)}) = ∑_j (M_j(f)∘g)·H_j(g)` with `M_j(f)` a *constant-coefficient*
differential monomial of `f` and `H_j(g)` a differential polynomial in `g` with coefficients small
relative to `g`, so `T(r,H_j(g)) = O(T(r,g))`; Theorem C's second conclusion then gives polynomials
`Q_j`, not all zero, with `∑_j M_j(f)·Q_j = 0` — a nontrivial ADE for `f` over `ℂ(z)`.

**The corpus already owns the Faà di Bruno step** (`CompositionJetBackward.jetElem_comp_mem_gradedJetRing`,
`CompositionJetRing`).  So cards 7 and 10 reduce to Theorem C alone.  Note also the paper's own
Remark 2: the reduction theorem does *not* apply to `g ∘ f` — which is consistent with the corpus's
split, where the inner-HT half is handled by local-inverse closure instead.

Reference for the proof to formalize: F. Gross and C. F. Osgood, *A simpler proof of a theorem of
Steinmetz*, and N. Steinmetz, *Über die faktorisierbaren Lösungen gewöhnlicher
Differentialgleichungen* (Math. Z. 170 (1980) 169--180).

### Cards 7/10: the second half of Steinmetz's theorem is an elementary induction on the first

Worth recording, because it halves the formalization target.

Theorem C has two conclusions.  The second follows from the first by a three-line induction on `N`,
with no analysis at all:

* `N = 1`: `F₁(g)h₁ = 0` with `h₁ ≢ 0` forces `F₁∘g ≡ 0`, hence `F₁ ≡ 0` (the range of a nonconstant
  entire `g` is open), so `Q₁ = 1` works.
* `N → N−1`: the first conclusion gives polynomials `p_j`, not all zero; say `p_N ≠ 0`.  Solving
  `∑ p_j(g)h_j = 0` for `h_N` and substituting into `∑ F_j(g)h_j = 0` gives

  ```text
  ∑_{j<N} (F_j p_N − F_N p_j)(g)·h_j = 0 ,
  ```

  a relation with `N − 1` terms whose coefficients still satisfy `T(r,h_j) = O(T(r,g))`.  By
  induction there are polynomials `Q̃_j`, not all zero, with `∑_{j<N}(F_jp_N − F_Np_j)Q̃_j = 0`, i.e.
  `Q_j := p_N Q̃_j` (`j < N`) and `Q_N := −∑_{j<N} p_j Q̃_j` work; they are not all zero because
  `ℂ[z]` is a domain and `p_N ≠ 0`.

So the only genuinely analytic content of Theorem C is its **first** conclusion: a relation
`∑ F_j(g)h_j = 0` with coefficients of characteristic `O(T(r,g))` forces a *polynomial* relation
`∑ p_j(g)h_j = 0`.

### Cards 7/10: an equivalent reformulation, in the corpus's own vocabulary

The outer-HT half is exactly

> `f` hypertranscendental over `ℂ(w)` ⟹ the composed jets `{f^{(i)}∘g}` are algebraically
> independent over `ℂ(z)⟨g⟩`.

The corpus already proves the `i = 0` case (`CompositionJetTranscendence.not_algebraic_comp_over_jet`,
by Clunie growth plus the Nevanlinna root estimate), and the substituted relation of card 10 is
precisely a nontrivial polynomial relation among the composed jets over `ℂ(z)⟨g⟩`.  The corpus's
growth argument does not extend as it stands: a relation among *several* `f^{(i)}∘g` gives no
characteristic bound on any one of them, which is exactly the gap Steinmetz's first conclusion fills.

### Card 10: three of its four pieces are corpus-owned; the exact build for the fourth

Audit of what card 10 (`f ∘ g` DA ⟺ `f` DA and `g` DA, for nonconstant entire `f, g`) still needs:

| Direction | Status |
|---|---|
| both DA ⟹ composite DA | `RGTowerCoherence.differentiallyAlgebraicOn_comp` + `substitutionFaithful_of_rightInverse` |
| inner DA + composite DA ⟹ outer DA | **owned**: `CompositionDecompositionLaw.differentiallyAlgebraic_of_comp` (its `hφ'` is only `φ′ ≢ 0`, not nonvanishing) |
| outer DA + composite DA ⟹ inner DA | not yet assembled — the build is written out below |
| `f` HT **and** `g` HT and composite DA ⟹ False | the Steinmetz gap |

So after the third direction is built, card 10's only remaining gap is the *both-hypertranscendental*
case, i.e. exactly Steinmetz's first conclusion.

**The build for the third direction** (all ingredients are corpus theorems):

1. Choose `z₀` with `g′(z₀) ≠ 0` and `f′(g z₀) ≠ 0`.  Both zero sets are countable
   (`FirstOrderCompositionDefect.countable_zeroSet_of_exists_ne_zero`, with `f′∘g ≢ 0` from
   `exists_ne_zero_comp`), and `ℂ` is uncountable.
2. `ParabolicFatouJetRealization.exists_localInverse_analytic` gives a local analytic inverse `γ` of
   `f` at `w₀ = g z₀`; cut it down to balls `A ∋ w₀`, `B ∋ f w₀`.
3. `LocalInverseHypertranscendence.differentiallyAlgebraicOn_of_localInverse` makes `γ` DA on `B`
   (using `f` DA on `A`).
4. `exists_localInverse_analytic` again, for `f ∘ g` at `z₀` — legitimate because
   `(f∘g)′(z₀) = f′(g z₀)·g′(z₀) ≠ 0` — and
   `CrossDomainSubstitution.substitutionFaithful_of_rightInverse` turns that right inverse into
   `SubstitutionFaithful W B (f∘g)`.
5. `differentiallyAlgebraicOn_comp` gives `γ ∘ (f∘g)` DA on `W`, and `γ(f(g t)) = g t` there.
6. `LocalInverseHypertranscendence.differentiallyAlgebraic_of_differentiallyAlgebraicOn` globalises.

`EllipticMeroFieldDifferentialAlgebraicity.infinite_ball` supplies the `Set.Infinite` side conditions
the substitution lemmas ask of the ball domains.

### Card 10: three of the four directions are now Lean (2026-09-01)

`HTGeometry/CompositionInnerDecomposition.lean`, axiom-clean and wired:

| Statement | Lean theorem |
|---|---|
| a nonconstant entire function has a point of nonzero derivative | `exists_deriv_ne_zero` |
| a point where **both** `g′` and `f′∘g` are nonzero (both zero sets are countable) | `exists_regular_point` |
| a local analytic inverse with explicit ball/open domains and both `MapsTo` conditions | `exists_localInverse_domains` |
| **outer DA + composite DA ⟹ inner DA** | `differentiallyAlgebraic_inner_of_comp` |
| the substitution by a nonconstant entire function is faithful on the plane | `substitutionFaithful_univ` |
| **both DA ⟹ composite DA** | `differentiallyAlgebraic_comp_entire` |
| **inner DA + composite DA ⟹ outer DA** | `differentiallyAlgebraic_outer_of_comp` |
| **the Boolean law, modulo the both-HT case** | `differentiallyAlgebraic_comp_iff_of_gap` |

The domain bookkeeping that made the inner direction work: take `A = ball w₀ s` where `γ ∘ f = id`,
and `B = ball(f w₀, δ₀) ∩ γ⁻¹(A)`.  Then `MapsTo f A B` holds because `γ(f w) = w ∈ A`, and
`MapsTo γ B A` holds by construction — no circular shrinking, which is what the naive "shrink both
balls" attempt runs into.

So card 10 now needs exactly `hgap`: `f` HT and `g` HT and `f∘g` DA is impossible.

### Why `hgap` is not reachable by the corpus's growth arguments

Recorded so a future session does not re-derive it.

The substituted relation is `∑_ν c_ν·(F_ν ∘ g) = 0` with `F_ν = ∏_i (f^{(i)})^{ν_i}` the distinct
jet monomials and `c_ν` differential polynomials in `g` — so `T(r,c_ν) = O(T(r,g))`, and by Clunie
`T(r, F_ν∘g)/T(r,g) → ∞`: the coefficients are genuinely *small functions* relative to every term.
Since `f` is HT the `F_ν` are `ℂ(w)`-linearly independent, so what is needed is that the `F_ν∘g`
stay linearly independent over the small functions.

* **The two-term case is reachable**: `b·(G∘g) = −1` gives `T(r,G∘g) = O(T(r,g))`, so `G` is
  rational by Clunie, which is a `ℂ(w)`-relation among the jets of `f` — contradiction.
* **The induction does not close.**  Applying `D = (1/g′)·d/dz` (which satisfies
  `D(G∘g) = G′∘g` and preserves smallness, since `T(r,1/g′) = T(r,g′) + O(1)`) turns one relation
  into a relation among *more* monomials: differentiating a degree-`d` jet monomial produces
  degree-`d` monomials of one higher jet order.  Each differentiation therefore adds unknowns at
  least as fast as equations — even in the linear case `∑_i c_i (f^{(i)}∘g) = 0`, `k`
  differentiations give `k+1` equations in `n+1+k` unknowns.  So no Wronskian/Cramer elimination
  closes the system.

This is the same wall the literature hits: Steinmetz's reduction theorem rests on his generalisation
of the second main theorem to small functions, and there is no growth-only substitute.

## Cards 13/14: why the Newton degeneration is unrepairable, and the exact reduction that replaces it (2026-09-01)

### The top-weight coefficient matrix of the model cascade has rank one — for every weight

Work with the model `δ X_k = ∏_(j≤k) λ_j X_j` and any monomial valuation `deg_w X_j = w_j > 0`.
Write `W_k = w_1 + … + w_k`.

* `δ` raises the weighted degree of a monomial containing `X_n` by exactly `W_(n−1)`, and raises every
  other monomial by less, so `deg_w (δ^i X_n) = W_n + i·W_(n−1)` and the **top-weight part of
  `δ^i X_n` is exactly `P_(n−1)^i P_n`** (coefficient one), where `P_k = ∏_(j≤k) λ_j X_j`.
* Hence for `i ≥ 1` the Jacobian entry `∂_k (δ^i X_n)` has top-weight degree

  `a(i,k) = D_i − w_k`,  `D_i := W_n + i·W_(n−1)`,

  which is **separable**: the leading-coefficient matrix is `c_i · d_k`, of rank one.
* Row `i = 0` is `∂_k X_n = δ_(kn)`, so the optimal assignment must send row `0` to column `n`, and
  every remaining permutation of rows `1..n−1` onto columns `1..n−1` has the *same* total
  `∑_i D_i − ∑_(k<n) w_k`.

So **every** surviving permutation ties, for **every** choice of weights: the assignment problem
never has a unique optimum and the model determinant is always a strictly lower-order term than the
individual permutation products.  This is not a defect of the particular bounds used earlier
(`det_ne_zero_of_hasLead`, "the first `n − 1` columns are proportional"); it is intrinsic, and no
sharpening, reweighting, or blow-up of the one-parameter degeneration can repair it.  The
one-parameter Newton degeneration of these Jacobians is therefore closed as a route.

### The general degeneration criterion is now Lean, and says exactly this

`HTGeometry/LogScaleDeterminantNonCancellation.lean` proves, unconditionally:

| Statement | Theorem |
|---|---|
| products add log-scale exponents | `HasLogScaleExponent.prod` |
| a negligible correction does not move an exponent | `HasLogScaleExponent.add_isLittleO` |
| the determinant reads off the optimal assignment | `hasLogScaleExponent_det_of_unique_max` |
| the same with identically null entries allowed | `hasLogScaleExponent_det_of_unique_max_on` |
| **degeneration**: `M = m + r`, `r` entrywise `o` of `m`, unique optimum ⟹ `det M` carries the model exponent | `hasLogScaleExponent_det_of_perturbation`, `…_on` |
| eventual nonvanishing | `det_ne_zero_of_unique_max_logScale`, `det_ne_zero_of_perturbation_unique_max_on` |

The hypothesis it isolates is precisely uniqueness of the optimal assignment, which the paragraph
above shows *fails identically* for these cascades.  The theorem is therefore correct and reusable,
and it certifies that the card's step-2 proof as written cannot be completed.

### The replacement: an unconditional bordered reduction

`HTGeometry/DerivationBorderedJetReduction.lean` proves, for any commutative `ℂ`-algebra, any time
derivation `δ`, any coordinate derivations, and **no hypothesis beyond the law**:

```
δ H = U · H  ⟹  det (∂_j δ^i H)_(i,j≤n+1)
                 = H^(n+1) · det ( border row `∂_j H` ; rows `∂_j δ^s U` )
```

(`derivationIterateOutputJacobian_det_uniformBordered`, with
`derivationIterateOutputJacobian_det_ne_zero_of_uniformBordered`,
`uniformBordered_derivationBell_det_eq`, `derivationBellCoeff_det = 1`.)

This removes the hypothesis `hterminalU` of `derivationIterateOutputJacobian_det_terminalScaled`,
which is what blocked the exact algebraic route: for the general cascade the multiplier
`U = P_n / X_n = P_(n−1)·A_n(X_n)/X_n` **does** involve the top coordinate — `∂_n U = 0` forces
`A_n' X_n = A_n`, i.e. exact linearity — so no coordinate derivation kills its jets, and the
terminal-scaled reduction is unavailable.  The bordered reduction needs nothing of the kind.

### What the reduction turns the card into

Iterating the bordered reduction along `W_0 := X_n`, `W_(k+1) := δ W_k / W_k` (the iterated
logarithmic derivatives) peels one row at a time.  For the cascade the first two steps are exact:

* `δ X_n = U · X_n` with `U = P_(n−1) h_n(X_n)`, `h_n := A_n/X_n`, and the border row is `∂_j X_n = δ_(jn)`;
* `δ U = U · V` with `V = T_(n−1) + P_(n−1) κ_n(X_n)`, `T_(n−1) = ∑_(i≤n−1) A_i'(X_i) P_(i−1)`,
  `κ_n := X_n h_n'(X_n)`, and the border row is `∂_j U = U · m_j(X_j)`, `m_j := A_j'/A_j ≠ 0`.

In the model `h_n` is the constant `λ_n`, so `κ_n = 0` and `V = T_(n−1)` is free of `X_n`; in general
`κ_n → 0` along the branch, which is where the asymptotic hypothesis re-enters — but now against a
*single scalar* rather than against a determinant with rank-one leading behaviour.

The remaining Lean gap for both cards is therefore one named object: the **general peel step**, the
bordered reduction with an arbitrary number of border rows already accumulated,

```
det ( a_0 ; … ; a_(k−1) ; ∂_j δ^s W )  =  W^(N−k−1) · det ( a_0 ; … ; a_(k−1) ; ∂_j W ; ∂_j δ^s V )
```

for `δ W = V · W`.  The corpus owns this only for the polynomial-coefficient cascade
(`PeelInduction`, `PeelEntry`, `PairPeelInduction`, `BorderShapeColumn`, `JetGradientRecursion`);
the general derivation-level version is the missing infrastructure.

## The general peel is now Lean: `HTGeometry/DerivationJetPeel.lean` (2026-09-01)

The missing infrastructure named at the end of the previous section is built, unconditionally, at
the level of an arbitrary commutative `ℂ`-algebra with an arbitrary time derivation and arbitrary
coordinate derivations.

| Statement | Theorem |
|---|---|
| `δ^m x = x · B_m(A)` with a natural-number index | `bellJet`, `derivation_iterate_eq_bellJet` |
| the Bell coefficient matrix is unitriangular | `bellJetCoeff`, `bellJetCoeff_self`, `bellJetCoeff_of_lt` |
| gradients of Bell values through gradients of jets | `derivation_bellJet_succ` |
| the matrix with `k` border rows and jets of `W` below | `peelMatrix` |
| **the peel step** `det (…, δ^s W) = W^(N−k−1) · det (…, ∂W, δ^s V)` for `δW = V·W` | `peelMatrix_det_succ` |
| nonvanishing transfers along one step | `peelMatrix_det_ne_zero_of_succ` |
| iterating the step along the whole chain | `peelMatrix_det_chain` |
| **the closed form** | `outputJacobian_det_eq_gradientMatrix` |
| observability from the chain gradients | `outputJacobian_det_ne_zero_of_gradientMatrix` |

The closed form is: for a chain of iterated logarithmic derivatives `Y_0 = W`,
`Y_(m+1) = δY_m / Y_m` (i.e. `δ Y_m = Y_(m+1) · Y_m`),

```
det (∂_j δ^i Y_0)_(i,j < N)  =  (∏_(m<N) Y_m^(N−m−1)) · det (∂_j Y_m)_(m,j < N).
```

Every hypothesis-bearing part of the old route disappears: no coordinate has to kill anything, no
asymptotics are used, and the `n` explicit factors are visibly nonzero whenever the chain members
are.  What is left is a single named statement:

> **the gradients of the iterated logarithmic derivatives of the output are linearly independent.**

### What the chain is for the cascade

`Y_0 = X_n`, `Y_1 = P_(n−1) h_n(X_n)` with `h_n := A_n/X_n`, `Y_2 = T_(n−1) + P_(n−1) κ_n(X_n)` with
`T_(n−1) = ∑_(i≤n−1) A_i'(X_i) P_(i−1)` and `κ_n := X_n h_n'(X_n)`.  Its gradients are

* `∂_j Y_0 = δ_(jn)` — a coordinate vector, so the determinant drops to the `(n−1)×(n−1)` minor on
  the first `n−1` columns immediately;
* `∂_j Y_1 = Y_1 · m_j(X_j)` for `j < n`, `m_j := A_j'/A_j ≠ 0`;
* `∂_j Y_2 = ∂_j T_(n−1) + P_(n−1) m_j κ_n` for `j < n`.

In the exactly-linear model `κ_n = 0` and `Y_2 = T_(n−1)` is free of `X_n`; in general `κ_n → 0`
along the Puiseux branch.  The asymptotic hypothesis now has to beat a **single scalar** at each
level rather than a determinant whose leading behaviour is rank one, which is exactly the repair the
old route could not make.

### Status of the two cards

Neither is closed.  What has changed is that the open core is one statement about one matrix, with
every reduction to it unconditional and in Lean, instead of a Newton degeneration that the first
section of this entry shows can never work.

## The chain-gradient matrix does have a unique optimal assignment (2026-09-01)

The two new tools compose, and the composition is the route.

**The model's chain-gradient determinant is already owned.**  `outputJacobian_det_eq_gradientMatrix`
gives `det (∂_j δ^i X_n) = (∏_m Y_m^(N−m−1))·det (∂_j Y_m)` with every factor `Y_m ≠ 0`, and
`ExpAffineCascade.scaled_jet_det_ne_zero` gives the left side nonzero for the model.  Hence the
model's chain-gradient determinant is nonzero, with no new work.

**Unlike the jet Jacobian, the chain-gradient matrix is not rank-one degenerate.**  For the model
`δ X_k = X_1⋯X_k` the chain is `Y_0 = X_n`, `Y_1 = P_(n−1)`, `Y_2 = S_(n−1) := ∑_(i<n−1) P_i`,
`Y_(m+1) = δY_m/Y_m`, and each `Y_m` for `m ≥ 2` involves only `X_1,…,X_(n−2)`.  The zero pattern
alone already forces most of the assignment:

* `n = 3`: rows `(0,0,1)`, `(X_2,X_1,0)`, `(1,0,0)` — exactly one surviving permutation, determinant
  `−X_1`, and `X_3²·X_1X_2·(−X_1) = −X_1²X_2X_3²`, which is the hand value of `det (∂_j δ^i X_3)`.
  The closed form checks out.
* `n = 2`: `(0,1)`, `(1,0)`, determinant `−1`, and `X_2·(−1) = −X_2`.  Also correct.
* `n = 4`: rows `Y_0 = (0,0,0,1)`, `Y_1 = (X_2X_3, X_1X_3, X_1X_2, 0)`, `Y_2 = (1+X_2, X_1, 0, 0)`,
  `Y_3 = (∂_1Y_3, ∂_2Y_3, 0, 0)`.  Rows `0` and `1` are forced onto columns `4` and `3`; two
  permutations survive on the `2×2` block.  With
  `Y_3 = X_1(1+X_2+X_1X_2)/(1+X_1+X_1X_2)` one computes
  `∂_2 Y_3 = (X_1+X_1²+X_1³)/(1+X_1+X_1X_2)²`, of weighted degree `w_1 − 2w_2`, and
  `∂_1 Y_3` of weighted degree `0` (its numerator's top term is `X_1²X_2²`, with coefficient
  `2 − 1 = 1`, so there is no cancellation).  The two assignment totals are

  `w_1` (rows `2,3` to columns `2,1`) and `w_1 − w_2` (to columns `1,2`),

  so the optimum is **unique** for every positive weight.

That is exactly the hypothesis of `hasLogScaleExponent_det_of_unique_max_on` /
`det_ne_zero_of_perturbation_unique_max_on`.  So the degeneration that is impossible on the jet
Jacobian is available on the chain-gradient matrix.

### The remaining work, precisely

1. Compute, for general `n`, the weighted degrees `deg_w (∂_j Y_m)` of the model chain and prove the
   assignment optimum is unique.  (`Y_1` contributes the monomial row `P_(n−1)/X_j`; the rows
   `m ≥ 2` are gradients of the `S`-tower and are the part that needs a general formula.)
2. Show the perturbed chain's gradients differ from the model's by entrywise `o`, which is where
   `κ_n = X_n h_n'(X_n) → 0` and the Puiseux branches of the `A_j` enter — against one scalar per
   level, not against a determinant.
3. Feed both into `det_ne_zero_of_perturbation_unique_max_on` and then into
   `outputJacobian_det_ne_zero_of_gradientMatrix`.

Step 1 is a self-contained combinatorial computation about the model tower; step 2 is the card's own
asymptotic hypothesis used one factor at a time.  Neither needs any new analytic input.

### The uniqueness criterion, reduced to one statement about leading forms

Write `lf(f)` for the top-weight part of `f` and `K_m` for the largest coordinate index occurring in
`lf(Y_m)`.  For a rational `f` one always has `deg_w (∂_j f) ≤ deg_w f − w_j`, with **equality exactly
when `lf(f)` depends on `X_j`**.  Hence the chain-gradient matrix's exponent matrix is

`a(m, j) = deg_w Y_m − w_j`  for `j ≤ K_m`,  and strictly smaller for `j > K_m`.

Any permutation using only equality entries has the same total `∑_m deg_w Y_m − ∑_j w_j`; any
permutation using one non-equality entry has a strictly smaller total.  So:

> **The optimum is unique as soon as `K_m = n − m` for every `m`** — a strict staircase leaves exactly
> one permutation that uses equality entries throughout, namely `σ(m) = n − m`.

`K_0 = n` and `K_1 = n − 1` are immediate (`Y_0 = X_n`, `Y_1 = P_(n−1)` exactly), and `K_2 = n − 2`
follows from `Y_2 = S_(n−2)` having top term `P_(n−2)`.  The inductive step needs

`lf(δ Y_m) = lf(Y_m) · P_(K_m − 1)`,   i.e.  `K_(m+1) = K_m − 1`,

and this is where a genuine choice enters: `deg_w (δ f) = max_k (deg_w (∂_k f) + W_k)`, and a
coordinate `k > K_m` contributes `deg_w f + W_(k−1) − ε_k`, which beats the `k = K_m` term unless
`ε_k > W_(k−1) − W_(K_m −1)`.  Explicitly for `n = 4`, `∂_2 Y_3` has `ε_2 = w_2` against a threshold
`w_1`, so the step holds only when `w_2 > w_1`: **the weights must be chosen increasing**, and the
required inequalities for general `n` are the remaining computation.  (For `n ≤ 4` no such step is
needed, which is why those cases close by hand.)

In the analytic realisation `X_k = F_k = f_k ∘ ⋯ ∘ f_1` the separation `T(r,F_k)/T(r,F_(k−1)) → ∞` is
far stronger than any linear weight, so the same criterion should be run there — with
`HasLogScaleExponent` measured against a growing radius rather than against a monomial valuation —
rather than in the abstract weighted setting.  That is the concrete next step for both cards.

## Step 1 is proved on paper: the model chain has a strict staircase (2026-09-01)

Work in the model `δ X_k = P_k = X_1⋯X_k` with weights `w_1 < w_2 < ⋯` and `W_k = w_1+⋯+w_k`.
Write `S_m := ∑_(i≤m) P_i`, `σ_j := S_j / P_j = 1 + S_(j−1)/P_j`, so `deg(σ_j − 1) = −w_j` with level
`j`.  Put `Y_m = P_(n−m) · u_m` and `r_m := log u_m`.  Because `δ P_k / P_k = S_(k−1)`,

`Y_(m+1) = δY_m / Y_m = S_(n−m−1) + δ r_m`,   hence   `u_(m+1) = σ_(n−m−1) + δ r_m / P_(n−m−1)`.

Let `d_m := deg(u_m − 1) < 0` and `ℓ_m := lev(u_m − 1)`.  For any `f` whose part of level `ℓ` has
degree `−w_ℓ`, the term of `δ f = ∑_k (∂_k f) P_k` coming from `k = ℓ` has degree
`(−2w_ℓ) + W_ℓ = W_(ℓ−1) − w_ℓ`, and this is maximal over `ℓ` exactly when the sequence
`ℓ ↦ W_(ℓ−1) − w_ℓ` decreases, i.e. when

`w_(ℓ+1) > 2 w_ℓ`   — take `w_ℓ = 3^ℓ`.

With that choice, `deg(δ(u_m − 1)) = d_m + W_(ℓ_m − 1)` and the recursion reads

`d_(m+1) = max( −w_(n−m−1),  d_m + W_(ℓ_m−1) − W_(n−m−1) )`.

Base: `Y_1 = P_(n−1)` exactly, `Y_2 = S_(n−2)`, so `u_2 = σ_(n−2)`, `d_2 = −w_(n−2)`, `ℓ_2 = n−2`.
Induction: if `d_m = −w_(n−m)` and `ℓ_m = n−m`, the second entry is `−w_(n−m)` and the first is
`−w_(n−m−1)`; since the weights increase, `−w_(n−m−1) > −w_(n−m)`, so

`d_(m+1) = −w_(n−m−1)`,  `ℓ_(m+1) = n−m−1`.

Hence `u_m = 1 + (lower)`, so **`lf(Y_m) = P_(n−m)`, a monomial with top index exactly `n − m`**, for
`1 ≤ m ≤ n−1`, and `lf(Y_0) = X_n`.  The gradient exponents are therefore

`deg ∂_j Y_m = deg Y_m − w_j` for `j ≤ n−m`,  and strictly smaller for `j > n−m`,

which is exactly the staircase hypothesis with `K(m) = n − m`.  The `n = 4` computation recorded
above (`ε_2 = w_2` against threshold `w_1`) is the first instance and matches.

Two independent checks of the general degree computation: `∂_m Y_3` has numerator
`P_(m−1)(S_(m−1)² − N')` with `N' = ∑_(i<m) P_i S_(i−1)`, giving `ε_m = w_m` exactly; and the closed
form reproduces the hand values `−X_2` (`n=2`) and `−X_1²X_2X_3²` (`n=3`).

### Lean status of step 1

The combinatorial half is built and axiom-clean:
`HTGeometry/StaircaseAssignment.lean` — `perm_eq_of_le` (a permutation dominated pointwise by a
permutation equals it), `unique_max_of_staircase`, `hasLogScaleExponent_det_of_staircase`,
`det_ne_zero_of_staircase`.  `HTGeometry/LogScaleMonomialCurve.lean` adds the measuring device:
`HasLogScaleExponent.inv`, `.div`, and `hasLogScaleExponent_zpow` (a monomial curve measures its own
weighted degree).

What is left for step 1 in Lean is the degree bookkeeping above: a weighted-degree and leading-form
calculus on `Frac (MvPolynomial (Fin n) ℂ)`, and the recursion `d_(m+1) = …`.  Because every
`lf(Y_m)` is a *monomial*, the bridge from weighted degree to the measured exponent on the curve
`X_j = t^(w_j)` needs no genericity: a monomial never vanishes on the curve.

## The algebraic degeneration toolchain is Lean (2026-09-01)

Three further modules, all unconditional and axiom-clean, complete the algebraic half of the route.

| Module | Contents |
|---|---|
| `HTGeometry/StaircaseAssignment.lean` | `perm_eq_of_le`; `unique_max_of_staircase` (over any linearly ordered abelian group); `hasLogScaleExponent_det_of_staircase`; `det_ne_zero_of_staircase` |
| `HTGeometry/LogScaleMonomialCurve.lean` | `HasLogScaleExponent.inv`, `.div`, `hasLogScaleExponent_zpow` |
| `HTGeometry/DegreeDeterminantNonCancellation.lean` | `IsDegree` (a `WithBot ℤ`-valued degree on a domain); `IsDegree.map_one`, `.map_neg`, `.map_add_of_lt`, `.sum_lt`, `.map_sum_of_unique_max`, `.map_prod`; `det_ne_zero_of_unique_max_deg`; **`det_ne_zero_of_staircase_deg`** |
| `HTGeometry/WeightedDegreeFunction.lean` | `curveHom` (substitution `X_j ↦ X_j·t^(w_j)`), `curveHom_injective`, `wdeg`, **`isDegree_wdeg`**, `wdeg_X`, `wdeg_C` |

`det_ne_zero_of_staircase_deg` is the purely algebraic form of the criterion: if the entry degrees
satisfy `d (M j i) = c i − w j` for `j ≤ P i` and `d (M j i) < c i − w j` for `j > P i`, the
determinant is nonzero.  Entries may vanish off the staircase — `⊥` is below every integer — so no
separate treatment of null entries is needed, unlike the measured version.

`isDegree_wdeg` supplies the concrete instance: the weighted degree with natural weights on
`MvPolynomial (Fin n) ℂ`.  Injectivity of the curve substitution (undone by `t ↦ 1`) is what makes
the `t`-degree additive on products, so no non-cancellation argument is required.

### How this is used, and what remains

The chain `Y_m` is rational, but nothing needs a degree function on the fraction field: writing
`Y_m = N_m/D_m` and scaling row `m` of the gradient matrix by `D_m²` makes every entry a polynomial
and multiplies the determinant by the nonzero factor `∏_m D_m²`.  The row constants `c` of the
staircase absorb the shift.  So the remaining work is exactly:

1. the explicit numerators `N_m`, `D_m` of the cascade chain and their weighted degrees — the
   recursion `d_(m+1) = max(−w_(n−m−1), d_m + W_(ℓ_m−1) − W_(n−m−1))` proved on paper above, with
   weights `w_ℓ = 3^ℓ`;
2. the perturbed chain's degrees, one scalar (`κ_n = X_n h_n'(X_n) → 0`) per level.

Everything downstream of those two is now built: `det_ne_zero_of_staircase_deg` →
`outputJacobian_det_ne_zero_of_gradientMatrix` → the cards' step 2.

### First cascade-specific weighted degrees

`HTGeometry/TowerWeightedDegree.lean` (unconditional, axiom-clean) computes the weighted degrees the
staircase needs at the bottom of the chain, on top of the corpus's polynomial tower model
(`ExponentialTowerModel.towerMonomial`, `ExponentialTowerLowAlgebra.towerSum`):

* `towerWeight w k = ∑_(1≤j≤k) w j`, with `towerWeight_succ` and strict monotonicity for positive
  weights (`towerWeight_lt`);
* `wdeg_towerMonomial : wdeg w (towerMonomial k) = towerWeight w k` — the products of distinct
  coordinates;
* `wdeg_towerSum : wdeg w (towerSum m) = towerWeight w m` for positive weights — the top monomial is
  the unique maximum, read off by `IsDegree.map_sum_of_unique_max`.

These are `Y_1 = P_(n−1)` and `Y_2 = S_(n−2)` of the chain.  The next brick is the support calculus
for `wdeg` (`wdeg (monomial α c) = ⟨w,α⟩` for `c ≠ 0`, and `⟨w,α⟩ ≤ wdeg p` for `α` in the support),
which gives `wdeg (pderiv j p) + w j ≤ wdeg p` with equality exactly when the top-weight part of `p`
involves `X_j` — the two facts the staircase hypotheses `heq`/`hlt` are made of.

## The staircase hypotheses are now Lean facts about weighted degrees (2026-09-01)

`HTGeometry/WeightedDegreeSupport.lean` (unconditional, axiom-clean) proves the support calculus of
the weighted degree, and with it exactly the two facts a staircase hypothesis consists of.

| Statement | Theorem |
|---|---|
| the curve image of a monomial | `curveHom_monomial` |
| the curve image as a support sum | `curveHom_eq_sum` |
| the `t`-coefficient is the weight-graded part | `coeff_curveHom` |
| no cancellation in a graded part | `coeff_curveHom_ne_zero` |
| `wdeg (monomial α c) = ⟨w,α⟩` for `c ≠ 0` | `wdeg_monomial` |
| every support weight is at most the degree | `wdegOf_le_wdeg` |
| the degree is attained on the support | `exists_mem_support_wdegOf_eq` |
| `wdegOf w (α + e_j) = wdegOf w α + w j` | `wdegOf_add_single` |
| **`wdeg (∂_j p) + w_j ≤ wdeg p`** | `wdeg_pderiv_add_le` |
| **equality when a top-weight exponent involves `X_j`** | `wdeg_pderiv_add_eq` |
| **strict when none does** | `wdeg_pderiv_add_lt` |

The last three are `heq` and `hlt` of `det_ne_zero_of_staircase_deg` verbatim: for a row `p` of a
gradient matrix, the entry degrees are `wdeg p − w_j` exactly on the coordinates occurring in the
top-weight part of `p`, and strictly smaller off them.  So the staircase criterion is now reduced to
the single geometric statement

> the top-weight part of `Y_m` involves exactly the coordinates `X_1, …, X_(n−m)`,

which is the paper-proved recursion recorded above.  Nothing else about weighted degrees is needed.

### Rational entries need no denominator clearing

`HTGeometry/FractionDegreeExtension.lean` (unconditional, axiom-clean) extends a degree function
from a domain to its fraction field:

* `degZ`, `coe_degZ`, `degZ_mul` — the integer value of a degree at a nonzero element;
* `fracDeg` — `deg(a/b) = deg a − deg b`, defined through `IsLocalization.sec`;
* `fracDeg_eq` — **well-definedness**: any representation `x·ι b = ι a` computes it;
* `fracDeg_algebraMap` — it restricts to the original degree;
* **`isDegree_fracDeg`** — the extension is again a degree function.

Multiplicativity is the product of two representations and subadditivity is the common denominator,
so `det_ne_zero_of_staircase_deg` now applies verbatim to matrices of rational functions — in
particular to the chain-gradient matrix `(∂_j Y_m)`, whose entries are rational.  The earlier plan of
clearing one denominator per row is no longer needed.

**State of the toolchain.**  Every general step of the cards' step 2 is now Lean:

```
staircase of top-weight supports          (wdeg_pderiv_add_eq / _add_lt)
  ⟹ unique optimal assignment            (unique_max_of_staircase)
  ⟹ det (∂_j Y_m) ≠ 0                    (det_ne_zero_of_staircase_deg, over fracDeg ∘ wdeg)
  ⟹ det (∂_j δ^i X_n) ≠ 0                (outputJacobian_det_ne_zero_of_gradientMatrix)
  ⟹ the jets of X_n are independent      (Jacobian criterion, corpus)
  ⟹ ord_DA = n                           (exactDifferentialOrder_entireCascade_of_transcendental)
```

The last link is important and was found by search rather than built: the corpus already discharges
the cards' Clunie/Gold'berg growth inputs.  `CascadeExactOrder.exactDifferentialOrder_entireCascade_of_transcendental`
needs only entireness, transcendence, a first-order equation per constituent, and **the jet
independence** — consecutive-state independence is automatic
(`pairAlgIndep_of_transcendental`).  So cards 13 and 14 reduce, with no analytic residue, to the
single geometric statement about the chain's top-weight supports.
