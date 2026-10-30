# Fixed-overlap positivity is selective against the Liouville twin

- **ID:** fixed-overlap-positivity-is-selective-against-the-liouville-twin
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** walls-ledger 1.18 (gauge selection: a form margin through non-ratio lags at bounded
  overlap, B3.16); route-obstacles "first windows" (Liouville fails where `ζ` is positive, full `ζ`
  floor uncertified); TM Robin–Euler breakdown; CACT positivity at every overlap for profiles
  without real Fourier zeros.
- **Statement:** There is an explicit `C²` profile `φ*` on `[0,1]` (the Liouville selector) with
  `robinEulerThreshold φ* < 1` such that for every fixed `c > robinEulerThreshold φ*`, in particular
  every `c ≥ 1`, eventually in `N`: Weil's form of `ζ` is strictly positive on every nonzero atomic
  family `Σ_{n≤N} x_n φ*_{c/N}(· − log n)`, and the complete form of the Liouville twin `λΛ` is
  strictly negative on some family of the same width.

## Goal

Before: full `ζ` positivity with Liouville failure on the same family was known only up to the
touching ratio (`transMetzlerProfile`, `c ≤ 1 + 10⁻¹⁸`); every positivity proved at separated widths
is shared by all bounded twists. Now: the complete-Weil margin at bounded overlap is gauge selective
at every overlap from `0.72` to `∞` — the Liouville gauge is excluded at each fixed scale, while
`ζ` keeps the full positive definite matrix.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized: `CACT/FixedOverlapPositivityIsSelectiveAgainstTheLiouvilleTwin.lean`,
  `lake --old env lean` clean, axioms `[propext, Classical.choice, Quot.sound]`, wired into
  `CriticalArithmeticCorrelationTheory.lean`.

## Proof

1. **Robin constant of a near plateau** (`bumpRobin_le_of_nearPlateau`). If `0 ≤ g ≤ B` on `[0,1]`,
   `g ≥ m₀` on `[η, 1−η]`, `g` is `K`-Lipschitz, then for `0 < a ≤ 1`
   `β(g) = ∫_0^1 Q(y)/(2y) dy ≤ KBa + (B² − m₀² + 2ηm₀²) log(1/a) + m₀²(1 − a)`, where
   `Q(y) = ∫(g(u) − g(u+y))²`. Below `a`: `Q(y) ≤ 2K|y|‖g‖₁`. Above `a`:
   `Q(y) = 2‖g‖² − 2∫g g(·+y)` and `∫ g g(·+y) ≥ m₀²(1 − 2η − y)`.
2. **The profile.** `P_w(x) = ∫_{x−L}^{x+L} B_w`, `L = 1/2 − 4w`, `B_w = U_w^{⋆4}`. Then
   `P_w = 2L (U_L ⋆ B_w)` is `C³`, `0 ≤ P_w ≤ 1`, `P_w = 1` on `|x| < 1/2 − 8w`, `P_w = 0` on
   `|x| > 1/2`, and `P_w` is `1/w`-Lipschitz (`B_w ≤ 1/(2w)`). The selector
   `φ*(u) = e^{τu} P_w(u − 1/2)`, `w = 1/1000`, `e^τ = 1001/1000`, is `e^τ(1/w + τ)`-Lipschitz.
3. **No real Fourier zeros.** `φ̂*(ξ) = e^{i(ξ−iτ)/2} · 2L · Û_L(ξ − iτ) Û_w(ξ − iτ)⁴`, and
   `Û_w(z) ≠ 0` off the real axis.
4. **Threshold.** With `B = 1.001`, `m₀ = 1`, `η = 9w`, `a = 10⁻⁴`, `log 10⁴ ≤ 10`:
   `β ≤ 0.1003 + 0.2001 + 0.9999`, `‖φ*‖² ≥ 1 − 18w = 0.982`, so `β/‖φ*‖² ≤ 3/2` and
   `e^{3/2} < 2.7182818286 · 2 < 2π`.
5. **Selectivity.** `ζ`: `CACT.eventually_noRealZero_completeWeilMatrix_posDef` at `c`, converted to
   `weilQuad > 0` by `completeWeilMatrix_inner_eq_weilQuad`. Twin:
   `TM.eventually_liouville_weilQuadTw_neg_of_gt_robinEuler` with `w_N = c/N`.

## Lean

`bumpRobin_le_of_nearPlateau`, `boxPlateau`, `paperFT_boxPlateau_ne_zero`,
`paperFT_tiltedBoxPlateau_ne_zero`, `abs_tiltedBoxPlateau_sub_le`, `liouvilleSelector`,
`robinEulerThreshold_liouvilleSelector_lt_one`, `liouvilleSelector_selective`,
`liouvilleSelector_selective_of_one_le`.

## Log
- 2026-10-30 — paper proof and Lean formalization.
