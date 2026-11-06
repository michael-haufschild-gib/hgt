# Review-0611 §2.1 effectivization and assembly tasks (A9–A14)

- **ID:** review-0611-effectivization
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean), one per task
- **Source:** [Obstacles summary §2.1](../../../reports/review-0611/obstacles-summary.md), "Effectivization and assembly"
- **Statement:** Each task A9–A14 gets a complete unconditional Lean theorem, easiest first.

## Status

| Task | Status | Lean |
|---|---|---|
| A13 Γ-limit lower bound | done | `ArithmeticHodgeTheoryOfDegenerations/TheCriticalFormHasAGammaLiminf.lean`: `eventually_lt_weilQuad_of_L1_limit_full`, liminf `Q(U_N) ≥ Q_T(F) + α_R ∫_{y<0} F²e^{−8y}` for every `T ≥ e^{G₀}`, along every `L¹` limit with `‖U_N‖₂ ≤ 1` and bounded eighth mass; `tendsto_integral_sq_sub_of_bounded_weilQuad`, bounded form upgrades the limit to `L²`. Inputs `CriticalArithmeticCorrelationTheory/{ThePrimeAndPoleFormsAreContinuousInTheWeightedNorm,BoundedWeilEnergyUpgradesL1LimitsToStrongLimits}.lean` |
| A14 star horizons, gcd strata, Künneth jets | done | Star horizon `HodgeTheoryWithoutVarieties/TheDepthLawIsEffective.lean`. Primitive horizon `HodgeTheoryWithoutVarieties/ThePrimitiveDepthLawIsEffective.lean`: `renormalizedPrimeForm_starRestrict_ge_primitive_of_horizon`, `R_N ≥ (log d + 2 log 2 − ε)|x|²` once `⌊N/d⌋ ≥ primitiveDepthHorizon ε`, a closed expression; tensorization `C = (1+η)e^{3A}` in `RenormalizedArithmeticPotentialTheory/TheTensorizationConstantIsExplicit.lean`. Gcd strata: exact identity `completeWeilEnergy_gcd_stratification`. Künneth jets: equivalence `ArithmeticHarmonicAnalysis/SameOrderJetRecoveryIsHomogeneousLogIndependence` |
| A10 explicit `R₀` | done | `CriticalArithmeticCorrelationTheory/TheDyadicReserveHasAnExplicitConstant.lean`: bump `S(2−|t|)` of slope `≤ 8`, `|φ| ≤ e⁴/2`, `|φ′| ≤ 6e⁴`, `dyadicArchConstant`. `TheFarComplementHasAnExplicitRatioInterval.lean`: `farMargin R = 3D/(8R) − C − C′R`, `farMargin_pos_iff`: positive iff `R < farRatioRoot`, root of `C′R² + CR − 3D/8 = 0`; `far_complement_coercive_below_root`: floor `min(1, farMargin R)` on `(V_{N^θ})ᗮ`. `TheCriticalComplementOnTheCertifiedRatioInterval.lean`: complement of the low packet for `R ≤ min(1, (5/6) R₀)`. The retained archimedean quarter raises the doc's `D/8` to `3D/8`. Full space at these ratios still needs the low packet and Schur constants of A9 |
| A11 literal channels | done for gcd twists; other periodic twists upward only | `ReceivingCharges/LiteralChannelScaleDomination.lean`, upward channel for every `M`-periodic twist, uniform in period and in the integer offset count `B = ⌈ce⌉` on `ceMQ⁵⌈log N⌉ ≤ N`. `ReceivingCharges/TheFourChannelsOfAPeriodicCharge.lean`: `exists_gcdTwistedCharge_four_channels`, joint bound for `G = g(gcd(·,M))`, on vectors orthogonal to `V₁` and to each other; `eventually_four_channels_small`, center, cross, overlap and upward coefficients `≤ ε` on `2α < β`, `β + 2α < 1/2`, nonempty iff `α < 1/8`. The Mertens remainder stays bounded, `log 8 + 4`, not small. Other periodic twists leave the conductor subspace: the overlap bound uses `divisorJetHorizonVector_mem_conductorSubspace`, the closure of Ramanujan modes under the downward prime shift, which they lack |
| A12 mixed Schur debit | done | `CompletedArithmeticForms/TheSchurDebitIsPaidOnGrowingBlocks.lean`: `exists_plateauPrefixSchur_floor_on_growing_blocks`, half the conductor floor uniformly in `M ≥ M₀`, `log M ≤ √log N`, `c ≤ b log log N`, `Q ≤ (log N)^{1/32}`; `dotProduct_prefixSchur_ge_of_floor`, `eventually_plateauPrefixSchur_floor_on_full_tail`: a full-space floor passes to every tail, so the full tail is paid to the certified boundary. Above the boundary full-tail payment is positivity of `W`. Fixed-cell first-prime, coarse and polar costs: `ArithmeticIndexDescent/FixedCoarseCellsControlTheEntireWeilIndex.lean`, index `≤ R+A` |
| A9 explicit `K₀` | stopped by user | No Lean. `K₁ = min(K_far, g/(64(C+1)), K_low)`; `K_low` needs `K_bi`, `K_d7` of the log-free conductor residuals, behind about 20 nested `∃ C` lemmas |

## Rule

Explicit means a closed expression. A theorem `∃ C, RHVerifiedThrough (C …) → X` with `X` implied by RH is classically
trivial, so heights carry explicit values.
