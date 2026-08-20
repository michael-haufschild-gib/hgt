# ULF-SRFM-5 — Lean formalization record

**Card:** `bounded-positive-conservation-blindness-and-modular-producer-criterion-law.md`
**Module:** `formal/GaloisForLFunctions/HTGeometry/BoundedConservationBlindness.lean`
**Namespace:** `GaloisForLFunctions.HTGeometry`
**Umbrellas:** `GaloisForLFunctions.HTGeometry`, `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Card object → Lean object

| Card | Lean |
|---|---|
| `P_m`, `Q_m`, (2.1) | `Po((m : ℝ≥0) * α)`, `Po((m : ℝ≥0) * β)` |
| `ℓ_m`, (2.4) | `superpositionCocycle` (identified with `llr` by `llr_superposition_ae`) |
| `d_TV` | `tvDist` (sup convention), `tvNorm` (atom `L¹` convention) |
| `Aff`, `H²` | `hellingerAffinity`, `hellingerSq` |
| `JS`, `M = (P+Q)/2` | `jensenShannon`, `jsMixture` |
| `J(P,Q)` | `jeffreys` |

## Card result → Lean declaration

| Card result | Lean declaration |
|---|---|
| (2.2) `J(P_m,Q_m) = mC = B_m + H_m` | `jeffreys_superposition` (with `formation_conservation`) |
| (2.3)–(2.4) the likelihood cocycle | `llr_superposition_ae` |
| **Theorem 3.1**, (3.1) signed mass | `signedMass_eq_zero` |
| (3.1) total variation | `tvDist_le_one`, `tvNorm_le_two` |
| (3.1) Jensen–Shannon | `jensenShannon_le_log_two` (via `toReal_klDiv_jsMixture_le`) |
| **(3.2)** exact Hellinger affinity | `hellingerAffinity_poissonMeasure`, `hellingerAffinity_superposition` |
| **(3.3)** `H² → 2` | `tendsto_hellingerSq_superposition` |
| **(3.3)** `B_m → 0`, `H_m → ∞` | `tendsto_formationBooleanWork_zero`, `tendsto_formationHistoryWork_atTop` |
| **Theorem 3.1** packaged | `boundedConservation_blindness` |
| **Corollary 3.2**, (3.4) | `reflected_signed_family_insufficient` |
| **Theorem 4.1**, (4.1) | `jeffreys_eq_integral_llr_sub`, `jeffreys_le_integral_abs_llr` |
| (4.2) `H ≤ J` | `hiddenHistoryWork_nonneg` + `formation_conservation` (`jeffreys_superposition`) |
| **Corollary 4.2**, (4.3) | `eq_of_bddAbove_modular_mass` |
| **Corollary 4.3**, (4.4) | `eq_of_bdd_modular_oscillation` |
| sign flip of the cocycle | `llr_symm` |

## Method notes

* `llr_symm` (a mathlib gap) follows from `Measure.inv_rnDeriv` plus `ENNReal.toReal_inv`.
* Both corollaries are stated **without** an integrability hypothesis: for the Poisson pair the
  cocycle is affine in the count and `integrable_superpositionCocycle` discharges integrability
  from the Poisson first moment.
* The Jensen–Shannon bound is proved on atoms: `r|log r| ≤ 2` on `(0,2]` (`mul_abs_log_le_two`)
  gives summability, and `dP/dM ≤ 2` gives the value bound `log 2`.
* The Hellinger affinity is the exponential series in `√(ab)`, evaluated with
  `hasSum_pow_div_factorial`.

## Verification

* `lake env lean` on the module: 0 errors, 0 warnings.
* Axiom audit: 28 public declarations, only `propext`, `Classical.choice`, `Quot.sound`.
