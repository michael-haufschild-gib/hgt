# Canonical formation-graph codiagonal topology-fracture law

- **ID:** ULF-TAFM-29
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Constant codiagonal recovery is closable in the base `ℓ²` source gauge exactly at zero coefficient, but every coefficient becomes bounded after the canonical `(N+1)` formation-graph loading.

## Higher-law interpretation

Topological admission is constitutive, not neutral. A response obstruction can disappear solely
because source history is measured in a stronger formation gauge. Therefore compact resolvent,
graph properness, or bounded formation action cannot by itself be a selection law. A valid
arithmetic selector must compare two source-fixed gauges or preserve a channel that canonical graph
regularization cannot absorb.

## Corpus audit

Before stating the theorem, corpus search was run for formation number, graph norm, weighted
codiagonal, shell recovery, and Rees resolvent. Relevant certified facts were:

1. `formationResolventMultiplier n = (n+1)⁻¹` and `formationResolvent` is compact
   (`CanonicalThermalReesFormationField`).
2. A weighted codiagonal on `ℓ²` is bounded exactly for square-summable weights; nonsummable
   weights are not sequentially closable (`WeightedCodiagonalDichotomy`).
3. Constant shell recovery is the actual obstruction in the replicated source geometry
   (`HighExponentShellOrthogonalDivisorReplication` and the shell Ward modules).
4. No existing theorem joined canonical formation loading to the codiagonal closability
   dichotomy.

## Theorem

Let `D = c₀₀(ℕ; ℂ)` and `j : D → ℓ²(ℕ; ℂ)` be the finite-support embedding. Define

`C_c(x) = Σ_n c x_n`,

`L(x)_n = (n+1)x_n`,

and `r_n = (n+1)⁻¹`. Then:

1. `C_c` is sequentially closable relative to `j` iff `c = 0`.
2. `r ∈ ℓ²`.
3. The bounded weighted codiagonal `B_c(y) = Σ_n c r_n y_n` satisfies
   `B_c(j(Lx)) = C_c(x)` for every `x ∈ D`.
4. The canonical formation resolvent satisfies `R(j(Lx)) = j(x)`.

Hence every constant response, including every nonzero response excluded by base-gauge
closability, is continuous in the canonical formation-graph gauge.

## Proof [PROVED HERE]

For `c ≠ 0`, weights `a_n = c` have constant squared norm `|c|² > 0`, so
`Σ_n |a_n|²` diverges. The weighted-codiagonal dichotomy gives nonclosability of `C_c`. For
`c = 0`, every response sequence is constantly zero; uniqueness of limits proves sequential
closability. This proves (1).

For (2),

`Σ_n |r_n|² = Σ_n 1/(n+1)² < ∞`

by the convergent `p`-series with exponent two. The bounded half of the weighted-codiagonal
dichotomy therefore supplies the continuous map with weights `r_n`; scalar multiplication by `c`
gives `B_c`.

For finite-support `x`, termwise cancellation gives

`B_c(j(Lx)) = Σ_n c (n+1)⁻¹ (n+1)x_n = Σ_n c x_n = C_c(x)`,

proving (3). The same cancellation in every coordinate gives

`R(j(Lx))_n = (n+1)⁻¹(n+1)x_n = x_n`,

proving (4). All sums in the identities are finite. No hypothesis, zero-location input, or
computation is used.

## RH impact

This theorem does not prove RH. It removes a false closing mechanism. In the shell Ward
calibration, base-gauge closability detects vanishing of the reflection-odd coefficient, but the
canonical formation graph makes every coefficient bounded. Therefore the already-proved compact
formation resolvent/global properness law cannot be composed with shell closability as a selector.

Remaining producer must supply one of:

- a source-derived reason canonical formation loading is inadmissible for the physical recovery;
- a functorial comparison between base and formation gauges whose boundedness forces the
  coefficient to vanish; or
- an adjacent-grade, reflection-odd response not regularized by the `(N+1)` load.

This sharpens the TAFM live boundary from “bounded formation-graph action” to
“source-fixed cross-gauge compatibility retaining the nonzero oriented channel.”

## Gates

- [x] 0 → 1: source-pure statement and hostile test identified by corpus search
- [x] 1 → 2: complete proof above; dependencies already certified
- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.CanonicalFormationGraphCodiagonalFracture`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only
- [ ] 3 → 4: publication-ready synthesis


## Lean certificate

Module `GaloisForLFunctions.HTGeometry.CanonicalFormationGraphCodiagonalFracture` (14 constants, axiom audit clean).

| Claim | Lean declaration |
|-|-|
| 1. `C_c` closable relative to `j` iff `c = 0` | `constantCodiagonal_closable_iff` (with `not_summable_sq_norm_const`) |
| 2. `r = ((n+1)⁻¹) ∈ ℓ²` | `summable_sq_norm_formationResolventMultiplier` |
| 3. `B_c(j(Lx)) = C_c(x)` | `formationGraphRecovery_after_load`, `inverseGradeCodiagonal_after_formationGraphLoad` |
| 4. `R(j(Lx)) = j(x)` | `formationResolvent_after_formationGraphLoad` |
| conclusion (topology fracture) | `formationGraphTopologyFracture` |

## Log

- 2026-09-01 — corpus-derived hostile test proved on paper.
- 2026-09-28 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
