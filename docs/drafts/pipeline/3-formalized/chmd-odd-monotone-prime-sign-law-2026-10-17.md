# Monotone prime-sign law on the one-signed odd cone

- **ID:** chmd-odd-monotone-prime-sign-law
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), sharp
- **Source:** conjecture loop after Step A (two-leg level) · STATUS MUST-1574
- **Statement:** `g ≥ 0` nonincreasing on `[c,a]`, zero beyond `a` ⟹ `∫_0^u g g(u−·) ≥ 2∫_0^∞ g g(·+u)` for
  `u ≥ max(2a/3, (a+c)/2)`; on the odd cone with unimodal Doob profile (mode ≤ c) every prime with
  `log n` beyond the threshold helps; `L ≤ 3 log 2`, `c ≤ 2log2 − L/2` ⟹ `E(v) ≥ Λ∞(Θ|v|) + 4·bonus`;
  indicator profile gives `3u − 2a` (sharp).
- **Vacuity check:** the first version assumed monotone on `[0, L/2]`; odd tests vanish at `0`, so that cone
  is `{0}`. Corrected to the unimodal form with mode `c > 0`; models `v = sign(x)p(|x|)/Θ(x)`, `p` C²
  vanishing to second order at `0`, nonincreasing on `[c,a]`.

## Proof mechanism
Split `[0,u]` at `b = a − u` and `u − b` (possible iff `b ≤ u/2` iff `u ≥ 2a/3`); the far piece reflects
onto the near piece (`integral_comp_sub_left`); the middle is nonnegative; on `[0,b]` both `u − s ≥ 2u − a ≥ c`
and `s + u ≤ a` lie in the monotone tail, so `g(u − s) ≥ g(s + u)`. The autocorrelation lives on `[0, b]` because `g` vanishes beyond `a`.

## Falsification attempts
- Without monotonicity: `g = 1_{[0,δ]} + 1_{[a−δ,a]}`, lag `u ≈ a − δ ≥ 2a/3`: `2(g*g) − 4(g⋆g) ≈ 2δ − 4δ < 0`. False.
- Threshold `2a/3`: indicator profile, `3u − 2a < 0` for `u < 2a/3`. Sharp [L].
- Threshold `(a+c)/2`: two-step profile `M·1_{[0,1)} + 1_{[1,2]}` (`a = 2`, `c = 1`): difference
  `−M(6 − 4u − M(2 − u)) < 0` for `u ∈ (4/3, 3/2)` and small `M`. Sharp [L]
  (`conv_sub_two_mul_autocorr_twoStepProfile_neg`). Piecewise-constant profiles are L¹-limits of
  continuous ones, so the thresholds are sharp for the continuous class too.

## Gates
- [x] 0 → 1 → 2 (paper proof above)
- [x] 2 → 3: `RHTower/CHMDOddMonotoneProfilePrimeSignLaw`, clean, olean, standard axioms, wired

## What it does not do
The archimedean part `Λ∞(Θv)` on the window `3 log 2` is still the obstacle (prime-free). The Doob cone has
no pole term, so the `4/9` pole-assisted machinery does not transfer; see the follow-up on the Doob Lévy
window.

## Log
- 2026-10-17 — created; STATUS MUST-1574.
