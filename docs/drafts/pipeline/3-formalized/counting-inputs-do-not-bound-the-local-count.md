# Counting inputs do not bound the local count

- **ID:** local-count-falsifier
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), WP-A falsifier
- **Source:** `1-in-progress/reboot-programme-conjecture-loop-2026-10-30.md` #26; `review-3010/reboot-final.md` §6 WP-A
- **Statement:** There is a zero configuration `Z'` (Zeta23 `ZeroConfig`) with
  `RiemannVonMangoldt Z'` (dyadic main term `N(T, 2T) = (T/2π) ell1 T + O(log T)` and unit-window
  count `N(t, t + 1) ≤ A₀ log(|t| + 3)`), `N₀(Z') = N₀(ζ)` on every window,
  `N_ζ(T₁, T₂) ≤ N_{Z'}(T₁, T₂) ≤ N_ζ(T₁, T₂) + 4 log(|T₂| + 3)`, the zero-counting Lindelöf property
  (`N(σ; T, T + 1] = o(log T)` for every `σ > ½`) whenever `ζ` has it, for no `C`:
  `#{ρ : |ρ − (½ + δ + it)| ≤ δ} ≤ C(δ log t + 1)` for all `0 < δ ≤ ½`, `t ≥ 3`, and for no `M`: the
  off-line multiplicity of every window `(T − 1, T + 1]` is `≤ M`.
  Positive survivor: for every configuration with Riemann–von Mangoldt, `0 < δ ≤ ½`, `C > 0`, there is
  `K` with `|{t ∈ [T, 2T] : #disc(½ + δ + it, δ) > C(δ log t + 1)}| ≤ T/(πC) + K` for large `T`.

## Lean
Module `SquareRootThreshold/CountingInputsDoNotBoundTheLocalCount.lean` (namespace
`RHTower.LocalCountFalsifier`): `superpose`, `finsum_superpose`, `N_superpose`, `N0_superpose`,
`clusterPoint`, `clusterConfig`, `clusterConfig_N_le`, `clusterConfig_N0`,
`riemannVonMangoldt_superpose`, `discCount`, `LocalCountBound`, `mult_le_discCount`,
`not_localCountBound_superpose`, `LindelofCount`, `lindelofCount_superpose`, `OffLineLocallyBounded`, `not_offLineLocallyBounded_superpose`,
`exists_zeroConfig_rvm_not_localCountBound`, `discCount_eq_sum`, `volume_localCount_gt_le`,
`eventually_volume_localCount_gt_le`.
Axioms: `propext`, `Classical.choice`, `Quot.sound`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized

## Paper proof
`Z' = ζ ⊕ clusters`: carriers united, multiplicities added, so window counts add. The clusters are
`½ ± 1/(k+3) + i exp(eᵏ)` with multiplicity `⌊log γ⌋ = ⌊eᵏ⌋`. A cluster below `T₂` has
`eᵏ ≤ log T₂`, so `k ≤ ⌊log log T₂⌋` and the clusters carry at most
`2Σ_{k ≤ ⌊log log T₂⌋} eᵏ ≤ 2e^{n}/(e − 1) ≤ (2e/(e − 1)) log T₂ ≤ 4 log T₂` zeros, `n = ⌊log log T₂⌋ + 1`.
They are off the line, so `N₀` is unchanged. The RvM main term gains `≤ 4 log(2T + 3) ≤ 8 log T` and
the unit-window count `≤ 4 log(|t + 1| + 3) ≤ 8 log(|t| + 3)` (`ζ` satisfies RvM:
`Zeta23.riemannVonMangoldt_zeta`). At `δ = 1/(k+3)`, `t = exp(eᵏ)` the disc about `½ + δ + it` holds
the cluster, `⌊eᵏ⌋ > eᵏ − 1`, against `C(δ log t + 1) ≤ |C|eᵏ/(k+3) + |C| ≤ eᵏ/2 + |C|` once
`k ≥ 2(|C| + 2)`; then `eᵏ ≥ k + 1 > 2|C| + 4`. At `k = M + 1` the window about `exp(eᵏ)` holds the
off-line cluster of multiplicity `⌊eᵏ⌋ ≥ M + 1`. Above `σ > ½` only the clusters with
`k + 3 ≤ 1/(σ − ½)` lie, all below `exp(e^K)`, so the Lindelöf count is that of `ζ` from there on.

In measure: on `[T, 2T]` the disc count is `Σ_{ρ ∈ F} m_ρ 1[ρ ∈ disc(t)]` over the zeros `F` of
`(T − 1, 2T + 1]`, and `{t : ρ ∈ disc(t)} ⊆ [Im ρ − δ, Im ρ + δ]`. So `∫_T^{2T} #disc ≤ 2δ N(T − 1, 2T + 1)`
(Tonelli), and Markov at level `C(δ log T + 1) ≥ Cδ log T` gives measure `≤ 2N(T − 1, 2T + 1)/(C log T)`.
RvM gives `N(T − 1, 2T + 1) ≤ (T/2π) log T + (|C₀| + 4A₀) log T` (`ell1 T ≤ log T`), hence
`T/(πC) + 2(|C₀| + 4A₀)/C`.

## What it changes (WP-A)
A1 is not a consequence of any input that counts zeros in windows of height `≥ 1` with an `O(log T)`
slack, even with the zero-counting form of Lindelöf added: Riemann–von Mangoldt with its remainder, the unit-window count, the critical census
(`N₀` is that of `ζ`), and near-line densities with a `K log U` term all hold for `Z'`. The clusters
are doubly exponentially sparse yet collapse `⌊log γ⌋` zeros onto one point at depths `→ 0`. A proof
of A1 has to use the explicit formula (arithmetic) at scale `δ`, not counting. The same holds for
the input of the lag family (`OffLineCopiesLocallyBounded M`): no counting input bounds the off-line
multiplicity of unit windows. What counting does give is A1 in density: violations with constant
`C` occupy a proportion `≤ 1/(πC)` of `[T, 2T]`. A configuration that clumps each unit window's
`(log T)/2π` critical zeros at one point violates A1 for `δ < 1/(2πC)` on a proportion `≍ 1/C`
(inference, not formalized), so the density `1/C` is the right order.

## Log
- 2026-10-31 — created; proved; formalized.
