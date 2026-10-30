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
| T1 index growth | the `S`-flipped complete Weil matrix has `≥ n` negative eigenvalues at every overlap `c ≥ c₀(S, n)` (conductor blocks `m·d`, `(m, Q) = 1`, carry the flip packet with diagonal limit form) | `eventually_flip_negative_eigenvalues`, `exists_overlap_flip_negIndex_ge` (RAPT `EveryLowConductorSeesTheFlipSet`) |
| T1 `κ(K_{ω_p}) = ∞` | unconditional over tests: `sup_g κ(K_{ω_S,g}) = ∞` for every nonempty finite flip set; for `ζ` the same supremum is `κ(K_ζ)` | `iSup_negIndex_weightKernel_finiteFlip_eq_top`, `iSup_negIndex_weightKernel_primeFlip_eq_top`, `iSup_negIndex_weightKernel_vonMangoldt` (HKT `EveryFlipSetHasInfiniteIndexOnTheHeckeLattice`) |
| T1 trial-span growth | one square (pole carrier) in the trial span; growth lives in the conductor blocks | `poleNegIndex_gauge_le_add_one`, `abs_poleNegIndex_gauge_sub_zeta_le_one`, `eventually_poleNegIndex_window` (HKT `TheSelectiveIndexOfTheAtomicKernelIsOneSquare`) |
| T1 flip index on its tower | `κ(K_ζ) = ∞ ∨ κ(K_{ω_p}) = ∞`; on the finite stratum the twin has `≥ n − #R` squares for every `n` | `weightKernel_flip_tower`, `negIndex_flip_eq_top_of_finite`, `negIndex_zetaKernel_eq_top_or_flip` (HKT `OnTheFiniteStratumEveryFlipHasInfiniteIndex`); `exists_frequency_thin` (HKT `APurePointSpectrumIsThinAtMostFrequencies`) |
| T2 fixed overlap | low spectral subspace ε-close to the Ramanujan span of conductors with `E_m(c) < T`, both directions | `eventually_completeWeil_lowSpace_near_ramanujan`, `tiltedUnitSpline_lowSpace_near_ramanujan` |
| T2 growing overlap | along a diagonal schedule `c_N → ∞` | `exists_overlap_schedule_lowSpace_near_ramanujan` (RAPT `TheLowCompleteWeilSpectrumLivesOnTheLowConductors`) |
| T3 growing head | index `≤ ⌈exp cost(P)⌉`, `cost(p ≤ Y) ≤ 32√Y log Y`; head `p ≤ (log N)^a` has index `≤ exp(C(log N)^{a/2} log log N)` — not uniform | `finiteEulerGamma_negative_dimension_le_exp`, `finiteEulerMixedGammaCost_eulerHead_le`, `eulerHead_negative_dimension_le` (AID `TheGammaReservePaysEulerHeadsUpToTheSquareOfTheDepth`) |
| T4 tail | no-go for coefficient-wise Gamma payment at any depth; survivor: depth `A` reaches `Y` with `32√Y log Y ≤ log A` | `not_summable_primeEulerMixedWeightTotal`, `exists_eulerHead_cost_gt` |

Formalized summary: ../3-formalized/krein-index-selection-localization-and-gamma-reach.md

## T3 plan: the head index grows (uniform extension is false)
Form `Q_Y = Γ − source(eulerHead Y)` at horizon `X ≥ (K+1)Y`. Details `e_a` (`haarAtom a`, `a ≤ K`),
coarse windows `C_b = Σ_{Yb ≤ n < Y(b+1)} coarseAtom n` = indicator of `log Y + [log 2b, log 2(b+1))`.
Orientation 2 vanishes (`inner_shift_coarseSection_haarSection`). Source matrix
`B_Y[a,b] = ∫ h_a(u) S_Y(u) du`, `S_Y(u) = Σ_{m ∈ head, m ∈ [2bY e^{-u}, (2b+2)Y e^{-u})} 2Λ(m)/√m`.
PNT: `S_Y/√Y → 4(√min((2b+2)e^{-u},1) − √min(2b e^{-u},1))₊` (sharp head edge at `m = Y`; proper prime
powers above `Y` are `o(√Y)`). Limit `L[a,b] = 0 (a<b)`, `−4√(2a) J_a (a=b)`, `4(√(2b+2)−√(2b)) J_a (a>b)`,
`J_a = ∫ h_a e^{-u/2} > 0`: invertible. Test `v(x) = (x, (s/√Y) Lᵀx)`, `Γ(f+g) ≤ 2Γ(f)+2Γ(g)`, Lévy
translation invariance: `Q_Y(v(x)) ≤ 2g_H|x|² + 2s²g_C‖L‖²|x|²/Y − s xᵀ(B_Y/√Y)Lᵀx < 0` for large `Y`.
Hence index `≥ K` once `Y ≥ Y₀(K)`; for heads `p ≤ (log N)^A` at horizon `N` the index → ∞.

## Approach
- T1a: one-square rigidity of the pole-hyperplane index under every sign gauge (atomic model).
- T1b: odd-Poisson flip difference; Bohr-part frequency selection on a grid (exact average identity,
  heavy/light split); assemble `n − κ` negative squares.
- T2: fixed overlap — Davis–Kahan from exact spectral counts and Ramanujan quasimodes.
- T3, T4: read AID's finite-Euler and first-prime modules; test growth of constants.

## No-go closure
- **T1 (trial-span growth).** Killing mechanism: the per-prime trials share the pole direction;
  the flip gain is the pole–p-adic cross term; on `{pole, p-adic parts}` the twin form is an
  arrowhead with nonnegative diagonal block, index `≤ 1`. Exact separated form: pole indices of any
  two sign gauges differ by `≤ 1`. Survivor: twin index grows linearly in the aperture of the
  flipped prime's tower (archimedean-rate odd kernel), and finite index for `ζ` forces infinite index
  for every flip. Status: Lean, see the formalized card.
- **T4 (tail).** Killing mechanism: the Gamma capacity at depth `A` is `log A + O(1)` while the
  Euler costs of the primes diverge (`Σ 4 log p/(√p − 1) ≥ Σ 1/p`). Survivor: the reach law
  `32√Y log Y ≤ log A`; at horizon depth `A ≍ N` Gamma pays the head `p ≲ (log N)²/C`, which contains
  the flip selection front `p ≲ log N log log N`. New insight: selection is payable by Gamma; the
  tail beyond `(log N)²` needs cancellation among the primes, i.e. the square-root count. Status: Lean.

## Log
- 2026-10-30 — created in 1-in-progress
