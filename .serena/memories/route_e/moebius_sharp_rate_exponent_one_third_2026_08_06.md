# The sharp Möbius sum has an explicit rate at exponent 1/3

`RHTower.Sieve.exists_norm_sum_moebius_kappa_two_rate`
(`RHTower/Sieve/MoebiusSharpKappaTwo.lean`):

    ∃ B ≥ 0, ∀ᶠ N in atTop,  ‖∑_{n ≤ N} μ(n)‖ ≤ B · N · exp( -(log N)^{1/3} / 108 ).

Unconditional.  The corpus previously had only `tendsto_norm_sum_moebius_div` (`o(N)`, no rate) for
the untwisted sum, and `exists_norm_sum_moebiusTwist_rate` at exponent `1/10` for the twisted one.

## The chain (all new, all instantiations — nothing κ=9 was touched)

`MoebiusContourKappaTwoGeneral` → `…Ratio` → `MoebiusContourParamTwo` + `MoebiusRatePowers` +
`MoebiusKappaTwoTerms` → `MoebiusKappaTwoRate` → `MoebiusWidthTwo` + `MoebiusAbsorbTwo` →
`MoebiusSharpKappaTwo`.

## The two tunings that are *not* transferable from the κ=9 chain

1. **The contour parameter needs the factor 2**: `contourParamTwo x = ⌈exp(2(log x)^{1/3})⌉₊`.
   At `log K = (log x)^{1/3}` exactly, the left-edge saving `exp(-log x/log²K)` and the right-line
   growth `x^{1/log²K}/K` cancel *exactly* and nothing is saved.  Doubling splits them: `1/9` to the
   left, `7/4` to the right.  (Compare `contourParam x = ⌈exp((log x)^{1/10})⌉₊`, no factor.)

2. **The smoothing width is a fraction of the same power, not a smaller power**:
   `smoothRatioTwo N = exp((log N)^{1/3}/54)`.  The corpus's `smoothWidth` uses the *smaller* power
   `(log N)^{1/20}`, which against a `1/3` saving makes the smooth-vs-sharp comparison dominate.
   Narrowing to `exp((log N)^{1/3})` fails from the other side: the contour coefficient carries
   `(N/H)²`.  `1/54` is where `L²·exp(-t/18)` meets `1/L`.

## Reusable arithmetic

- `sq_le_exp_div : t² ≤ 216²·exp(t/108)` — from `Real.add_one_le_exp` squared.  This is the generic
  "absorb a polynomial into an exponential" step; no `tendsto` needed.
- `mul_three_le`, `absorb_rate` — abstract, no zeta.
- `log_shift_le` : `N + H + 1 ≤ N²` for `N ≥ 3`, so the shift costs `t ≤ s ≤ 2t`.

## Traps

- `norm_sub_norm_le a b : ‖a‖ - ‖b‖ ≤ ‖a - b‖` — the *wrong direction* for bounding the sharp sum by
  the smooth one.  Swap the arguments and `rw [norm_sub_rev]`.
- `1 ≤ Real.log N` gives `linarith` nothing about `N` (mathlib's `log` is `0` off the positives).
  Carry `0 < N` explicitly.
- Assemblies of this size hit the 200000-heartbeat limit.  Fix: lift every coefficient-absorption
  step to a **top-level** lemma (heartbeats are per-declaration) and replace `nlinarith` on degree-5
  products by `mul_le_mul_of_nonneg_*` plus `linarith`.

See `mem:route_e/moebius_saving_exponent_one_third_2026_08_06`,
`mem:route_e/moebius_kappa_two_contour_proved_2026_08_06`.
