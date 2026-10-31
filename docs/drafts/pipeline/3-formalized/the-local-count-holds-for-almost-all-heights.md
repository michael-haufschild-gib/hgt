# The local count holds for almost all heights

- **ID:** local-count-almost-all
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `1-in-progress/reboot-programme-conjecture-loop-2026-10-30.md` #28
- **Statement:** For `0 < δ ≤ ½` and `C > 0`, for all large `T`,
  `|{t ∈ [T, 2T] : #{ρ : |ρ − (½ + δ + it)| ≤ δ} > C(δ log t + 1)}| ≤ T/(C√(δ log T))`, zeros of `ζ`
  counted with multiplicity. So A1 holds with every constant on a set of heights of density one.

## Lean
Module `SquareRootThreshold/TheLocalCountHoldsForAlmostAllHeights.lean` (namespace
`RHTower.LocalCountFalsifier`): `abs_sub_im_le_of_mem_disc`, `volume_localCount_gt_le_sqrt`,
`sq_sum_sqrt_le`, `sum_mult_max_le_offLineMoment`, `eventually_volume_zeta_localCount_gt_le`; uses
`exists_N_window_le` (`CountingInputsDoNotBoundTheLocalCount`).
Axioms: `propext`, `Classical.choice`, `Quot.sound`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized

## Paper proof
The disc about `½ + δ + it` of radius `δ` is tangent to the critical line. A zero `ρ` with
`η = Re ρ − ½` lies in it iff `(η − δ)² + (Im ρ − t)² ≤ δ²`, so `|t − Im ρ| ≤ √(2δη₊)`: a critical zero
is seen at one height only. Writing the disc count on `[T, 2T]` as `Σ_{ρ ∈ F} m_ρ 1[ρ ∈ disc(t)]` over
the zeros `F` of `(T − 1, 2T + 1]`, Tonelli gives `∫_T^{2T} #disc ≤ Σ m_ρ 2√(2δη₊)`, and Markov at
level `C(δ log T + 1)` bounds the violating set. Cauchy–Schwarz with `f = √m`, `g = 2√m√(2δη₊)`:
`(Σ m 2√(2δη₊))² ≤ 8δ (Σ m)(Σ m η₊)`. Riemann–von Mangoldt (`Zeta23.riemannVonMangoldt_zeta`) gives
`Σ m = N(T − 1, 2T + 1) ≤ (T/2π + K) log T ≤ (T/5) log T`, and the explicit off-line first moment
(`eventually_offLineMoment_le`) gives `Σ m η₊ ≤ (21/100)(2T + 1) ≤ 0.43 T`. So the sum is
`≤ √(0.69 δ T² log T) ≤ T√(δ log T)`, and dividing by `Cδ log T` gives `T/(C√(δ log T))`.

## What it changes (WP-A)
A1 is true for almost all heights, with every constant, unconditionally, while #26 shows that no
counting input proves it at every height. The improvement over #27 (density `1/(πC)`) comes from
tangency: off a null set only off-line zeros enter, and the off-line first moment makes them
`O(1/√(δ log T))` in density. The exceptional heights are where off-line zeros of depth `≍ δ` cluster.
That is exactly the set the lag family and heat detection have to handle, and the off-line moment
alone does not make it empty.

## Log
- 2026-10-31 — created; proved; formalized.
