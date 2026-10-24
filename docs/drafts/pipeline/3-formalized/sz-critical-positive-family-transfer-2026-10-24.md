# Strict Suzuki pairing deficit on the compact critical arithmetic family

- **ID:** sz-critical-positive-family-transfer-2026-10-24
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean; complete paper proof below)
- **Source:** Suzuki first variation; Arithmetic Positivity Theory's compact
  critical-source positivity and BiScale's finite-jump smoothing theorem.
- **Statement:** Every nonzero sufficiently high dyadic critical source, at
  every allowed compact truncation, has mollifications whose literal Suzuki
  pairing is strictly below their source mass for all sufficiently small
  positive shifts.

## Exact statement

Let `g = criticalTruncatedTest hV S b`, with `S` a dyadic scale block at
`M`, a nonzero coefficient pattern `b`, and `V` above the existing truncation
threshold. There exists one `M₀` such that, whenever `M ≥ M₀`, `Q(g)>0` and
for every sufficiently large mollification index `k`, for every sufficiently
small positive `ω`,

`ω Q(g)/4 < autocorr(g_k)(0) - suzukiCriticalSourcePairing g_k ω`,

where `g_k = smoothCompactSource g k` and `Q = compactFullWeilEnergy`.
In particular, the actual finite-shift source pairing is strictly below mass.
The shift threshold may depend on `M,V,S,b,k`; no uniformity in these variables
is claimed. The truncation parameter `V` is unbounded.

## Dependency-closed paper proof — [PROVED HERE]

1. `exists_compactFullWeilEnergy_criticalTruncatedTest_pos` supplies a common
   high-block threshold and `Q(g)>0`, without any positivity premise.
2. `exists_lipschitz_criticalTruncatedSource` and compactness imply finite
   Lévy energy by `integrableOn_levy_of_lipschitz`.
3. `re_weilFullFunctional_smooth_tendsto` gives `Q(g_k) → Q(g)`. Hence
   `Q(g_k)>Q(g)/2` for every sufficiently large `k`.
4. Each `g_k` is compact and C². The complete literal Suzuki first variation
   gives `(autocorr(g_k)(0)-P_ω(g_k))/ω → Q(g_k)`. For this fixed `k`, the
   quotient is therefore greater than `Q(g)/4` for all sufficiently small
   positive `ω`. Multiplication by `ω>0` proves the claimed strict inequality.

## What this discharges

This is an actual source inequality for an arithmetic family of unbounded
support length, not a new positivity criterion. Its inputs are existing
unconditional family positivity and the literal source limit. It does not
prove nonnegativity on arbitrary compact sources, or supply a common positive
shift across growing apertures. Those remain the hard mathematical blockers.
Unbounded support length does not assert density of these positive families in
the complete Weil energy domain or control of arbitrary mixed coefficient blocks.

This is a formal transfer of existing mathematics, not a scientific novelty claim.

## Gates

- [x] Exact family, quantifier order, and positive margin specified.
- [x] Complete paper proof with all source regularity premises discharged.
- [x] Canonical Lean check and transitive axiom audit.

## Formalization certificate

Module: `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCriticalFamilyContraction.lean`.
Declaration: `RHTower.exists_suzukiCriticalFamily_strict_deficit`.

The canonical command
`lake --old env lean GaloisForLFunctions/RHTower/Suzuki/SuzukiCriticalFamilyContraction.lean`
passed. Its transitive axiom audit reports exactly `propext`, `Classical.choice`,
and `Quot.sound`. No positivity premise is present in the theorem's binders;
family positivity is supplied by the existing unconditional arithmetic theorem.
The leaf is wired into `RHTower.lean`; no umbrella was compiled.
