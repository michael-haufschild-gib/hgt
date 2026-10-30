# Krein index: selection at growing resolution and the producer

- **ID:** kisp
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (four targets)
- **Source:** docs/reports/review-3010/route-unification-ledger.md §5 (Krein index: has 1, 2; lacks 3 and a producer)
- **Statement:** Find the Euler-product-specific content of the Weil-kernel index and the block that a producer must pay.

## Goal
The Krein index `κ(K_ζ)` is critical and amplifiable but has no producer and no proved selectivity at growing
resolution. Targets:
1. twin index growth (selection as an index statement);
2. low-mode localization of the complete Weil matrix (where selection lives);
3. uniform finite index for growing Euler heads `p ≤ (log N)^A`;
4. the first-prime tail on complete cells.

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized

## Findings

**T1 as stated (index ≥ #{p ∈ S : Kp ≤ c⁷} via per-prime trials) is false in the trial span.**
Every prime-square trial is `β₁·(pole vector) + (p-adic part)`, `β₁ = 1 − 2/p + 2/p²`. At leading order in
`1/p` the flip gain sits entirely in the pole–p-adic cross term; the pure p-adic part has no gain, and a flip at
`q` penalizes the pole by `+4 log q/q`. On the span `{pole, p-adic parts}` the twin form is an arrowhead
matrix with nonnegative diagonal block, so by Haynsworth it has at most one negative square. Selection at
bounded overlap through exact prime ratios is a rank-one phenomenon carried by the pole.

**Exact separated form (atomic kernel).** A sign gauge acts on the exact-ratio prime kernel by congruence;
only the pole moves. So the twin and `ζ` pole-hyperplane indices differ by at most one at every horizon
(HKT `hermNegIndex_gaugeAtom_eq` + `hermNegIndex_le_add_one_of_eq_on_ker`). The selective content of the
atomic index is one square.

**Where growth survives.** On the tower of the flipped prime, with a test of support below `log p/4`, the
twin kernel is `K_ζ + 2 log p ‖f‖² p^{−|n|/2}[n odd]`. The added kernel has symbol of the sign of `cos θ`
(infinite index), and its decay `p^{−|n|/2}` is that of the archimedean tail. On the finite stratum `K_ζ` on
the tower is a Bohr series with nonnegative weights plus finitely many pairs, so frequency-localized blocks
near `θ = π` give twin index growing linearly in the tower length. Target form:
`negIndex zetaKernel = ⊤ ∨ negIndex (twin tower kernel) = ⊤`.

## Status

| Target | Result | Lean |
|---|---|---|
| T1 trial-span growth | false: one square (pole carrier) | `poleNegIndex_gauge_le_add_one`, `abs_poleNegIndex_gauge_sub_zeta_le_one`, `eventually_poleNegIndex_window` (HKT `TheSelectiveIndexOfTheAtomicKernelIsOneSquare`) |
| T1 flip index on its tower | `κ(K_ζ) = ∞ ∨ κ(K_{ω_p}) = ∞`; on the finite stratum the twin has `≥ n − #R` squares for every `n` | `weightKernel_flip_tower`, `negIndex_flip_eq_top_of_finite`, `negIndex_zetaKernel_eq_top_or_flip` (HKT `OnTheFiniteStratumEveryFlipHasInfiniteIndex`); `exists_frequency_thin` (HKT `APurePointSpectrumIsThinAtMostFrequencies`) |
| T2 fixed overlap | low spectral subspace ε-close to the Ramanujan span of conductors with `E_m(c) < T`, both directions | `eventually_completeWeil_lowSpace_near_ramanujan`, `tiltedUnitSpline_lowSpace_near_ramanujan` |
| T2 growing overlap | along a diagonal schedule `c_N → ∞` | `exists_overlap_schedule_lowSpace_near_ramanujan` (RAPT `TheLowCompleteWeilSpectrumLivesOnTheLowConductors`) |
| T3 | open | — |
| T4 | open | — |

## Approach
- T1a: one-square rigidity of the pole-hyperplane index under every sign gauge (atomic model).
- T1b: odd-Poisson flip difference; Bohr-part frequency selection on a grid (exact average identity,
  heavy/light split); assemble `n − κ` negative squares.
- T2: fixed overlap — Davis–Kahan from exact spectral counts and Ramanujan quasimodes.
- T3, T4: read AID's finite-Euler and first-prime modules; test growth of constants.

## Log
- 2026-10-30 — created in 1-in-progress
