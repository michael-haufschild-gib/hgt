# CCM-FU: geometric defect reserve

- **Stage:** 1-in-progress
- **Parent:** [adaptive prime ceiling](ccm-fu-adaptive-prime-ceiling.md)
- **Frozen question:** Does the sufficient state certificate `Q_P+2 sqrt(G_P D_P)<=Q_empty` admit a complete prime order at every stored cutoff? Separately, does the weaker first-prime estimate with Q_empty replacing G certify every second-prime extension?
- **Scope:** Every stored subset state through32, original tolerance; no regeneration of channels or greedy paths.

Recover the signed head from the exact isolated late-prime energy law, and recover source coefficients by finite subset inversion of those heads. Restrict to the exact squarefree source support, then regroup coefficients by each remaining label to obtain G and D. Verify reconstructed energies and heads against every stored state. Numerical values guide the next paper proof and are not Lean premises.

Failure of a sufficient geometric reserve is not a failure of the actual energy ceiling: the bound discards prime-specific signed overlap. Keep that distinction when selecting the next arithmetic input.

## Current stored-data evidence

`defect_reserve_reanalysis.py` and `defect-reserve-reanalysis.json` in the [saved computation directory](../2-fully-proven/computations/ccm-fu-adaptive-prime-energy-2026-09-06/README.md) cover all 8860 stored states. They retain the original input hash and tolerance `1e-12*max(1,Q_empty)`. Maximum energy reconstruction error is about 5.82e-14; maximum head reconstruction error is about 4.05e-14.

There are 1478 states failing the sufficient geometric certificate. The first is M=13, P={5,7,11}: actual energy is about 0.112242482719, original energy 0.195027952331, and the sufficient upper bound 0.204871656029. This is a numerical failure of the estimate only; no Lean obstruction is claimed.

Every stored cutoff through32 admits a complete path whose preterminal states satisfy the geometric certificate. At cutoff32 one such order is `31,29,23,19,2,17,13,7,5,11,3`. All 192 first-prime states satisfy the weaker sufficient reserve `Q_{p}+2 sqrt(Q_empty D_{p})<=Q_empty`, which would certify every second-prime extension there. Both all-cutoff assertions remain open; none of these computed values enters Lean.

The separate [bounded first-prime extension](ccm-fu-two-prime-local-blocks.md) checks every first-prime state at cutoffs33..1024 and finds no failure among 95747 states. Its original energies agree with the saved greedy data. The one-dimensional divisor-defect/unit-clock table and all first-prime records are saved. This extends only the numerical first-prime reserve evidence; complete geometric paths remain checked only through32.

## Source-derived reserve scale

The [direct extension induction](ccm-fu-reserve-extension-induction.md)
tests the stronger local property that every certified proper state has a
certified successor or can complete. All 7350 certified proper saved states
through32 pass. A complete all-state extension to cutoffs33..64 finds no
failure among 999880 certified proper states. Homogeneous certificate
descent, which would discard unused initial reserve, fails in 975 saved
states through32. These finite numerical results leave the source-specific
extension inequality open. Positivity, factor-two channel comparisons and
first-prime reserve alone do not prove it; the card gives an explicit paper
model and identifies the exact missing paired contraction/defect comparison.

The [uniform channel square-root bound](../3-formalized/ccm-fu-uniform-channel-square-root-bound.md) proves `K_d(M)<=7 sqrt(M)` at every cutoff and dilation. An initial late block leaving its head above `-sqrt(M)` releases at most `57M` total energy, uniformly over the block, including removed singleton squares. This excludes treating the initial balancing reserve as quadratic. It does not bound the reserve released by subsequent smaller-prime contractions. The next missing input is an arithmetic comparison of actual paired contraction and created sign defects, compatible with a complete growing interleaving.
