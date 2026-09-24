# A zero-free region of width `1/(100 log γ)` valid from ordinate four

- **ID:** ZFR-4-001
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** MUST-270; `zeta-logderiv-sharp-landau.md`
- **Statement:** every zero copy of `ξ` with `Im ρ ≥ 4` satisfies `Re ρ ≤ 1 − 1/(100 log (Im ρ))`.

## What is proved

Module [`ZeroFreeRegionFromFour`](../../../../formal/GaloisForLFunctions/RHTower/ZeroFreeRegionFromFour.lean):

- `RHTower.re_logDeriv_Gammaℝ_le_half_log` — **`Re (Γ_ℝ'/Γ_ℝ)(σ+it) ≤ (log t)/2 + 1/4`** for
  `1 ≤ σ ≤ 2`, `t ≥ 4`. Only the real part is ever used and it is half the modulus bound: with
  `z = s/2` one has `2 ≤ ‖z‖ ≤ t`, so `Re ψ(z) ≤ log‖z‖ + 3/‖z‖ ≤ log t + 3/2`, and `log π ≥ 1`.
- `RHTower.neg_re_logDeriv_riemannZeta_le_half` — `−Re (ζ'/ζ)(σ+it) ≤ (log t)/2 + 1/2`.
- `RHTower.neg_re_logDeriv_riemannZeta_le_half_sub` — the same with the zero's resolvent term
  retained.
- `RHTower.dlvp_half` — `4/(σ−β) ≤ 3/(σ−1) + (5/2) log γ + dlvpHalfConstant A`,
  `dlvpHalfConstant A = 3A + 5/2 + (log 2)/2`. **Coefficient `5/2`**, against `5` before and `400`
  in `dlvp_inequality`.
- `RHTower.xiZeroCopy_zero_free_from_four` — **the region, with no threshold beyond `Im ρ ≥ 4`.**
  At `c₀ = 1/16`, `c = 1/100` the surplus is `1600/29 − 48 − 5/2 = 271/58 ≈ 4.67`, and
  `K = dlvpHalfConstant 1 ≈ 5.85`, so the contradiction needs only `log γ ≥ K·58/271 ≈ 1.25`, which
  `log 4 > 1.386` already gives.

Built, wired, axiom-clean, lint clean.

| | width | valid from |
|-|-|-|
| `Sieve.exists_zero_free_region` | `1/10000` | `e^{40804}` |
| `exists_xiZeroCopy_zero_free_sharp` | `1/100` | existential |
| `xiZeroCopy_zero_free_explicit` | `1/100` | `e^{22.8}` |
| `xiZeroCopy_zero_free_from_four` | `1/100` | **`4`** |
| `xiZeroCopy_zero_free_fiftyEight` | **`1/58`** | **`4`** |
| `riemannZeta_ne_zero_of_one_sub_lt_re` (for `ζ` itself) | **`1/58`** | **`4`** |

## The remaining gap in MUST-269, quantified

The hyperbolic condition `β(1−β)γ² ≥ 1/4` needs, exactly,
`4(1/4 − b)²γ² ≤ (b + γ²)² b` with `b = β(1−β)`. The region gives `b ≥ (c/L)(1 − c/L)`,
`L = log γ`. With `c = 1/100` that holds for `γ ≥ 7` but fails at `γ = 4.53`, where
`γ² > 41/2` is all the corpus certifies. **So the uncovered range is now `4.53 ≤ |γ| < 7`**, against
`4.53 ≤ |γ| ≤ 8·10^9` before.

Route 2 of the two has been carried out — see
[`DigammaLeLog`](../../../../formal/GaloisForLFunctions/RHTower/DigammaLeLog.lean):

- `RHTower.re_digamma_le_log` — **`Re ψ(y) ≤ log y` for every `y > 0`**, missing from mathlib. The
  `n`-fold recurrence `Re ψ(y) = Re ψ(y+n) − Σ_{k<n} 1/(y+k)` plus `‖ψ(z) − log z‖ ≤ 3/‖z‖` and
  `Σ_{k<n} 1/(y+k) ≥ log(y+n) − log y` give `Re ψ(y) ≤ log y + 3/(y+n)` for every `n`; let `n → ∞`.
  No convexity of `log Γ` and no Gauss series are needed.
- `RHTower.two_fifths_le_log_pi_sub_log_two` — `log π − log 2 ≥ 2/5`, from `exp(1/10) ≤ 10/9`
  (which is `1 − x ≤ exp(−x)`) raised to the fourth power, against `π > 3.14`.
- `RHTower.neg_re_logDeriv_riemannZeta_real_le_neg` — **`−ζ'/ζ(σ) ≤ 1/(σ−1) − 1/5`**. One shift
  `ψ(σ/2) = ψ(σ/2+1) − 2/σ` cancels the `1/σ` of the four-factor identity exactly, leaving the
  σ-independent `(log 2 − log π)/2`.
- `RHTower.xiZeroCopy_zero_free_fiftyEight` — **the region of width `1/(58 log γ)`, still valid from
  ordinate `4`**, at `c₀ = 1/9`: the surplus is `2088/67 − 27 − 5/2 = 223/134`, and
  `(223/134)·log 4 ≥ dlvpHalfConstant (−1/5)` because `log 2 > 0.6931`.

## The region for `ζ` itself

[`ZetaZeroFreeRegionSharp`](../../../../formal/GaloisForLFunctions/RHTower/ZetaZeroFreeRegionSharp.lean)
transports it off the `ξ` copies:

```text
RHTower.riemannZeta_ne_zero_of_one_sub_lt_re :
  4 ≤ |γ| → 1 − 1/(58 log |γ|) < β → riemannZeta (β + iγ) ≠ 0
```

with the contrapositive `re_le_one_sub_of_riemannZeta_eq_zero`. Only `xi_eq_zero_iff` inside the
strip and `xiZeroCopyConjEquiv` for negative ordinates are needed; `β < 1` comes from
`riemannZeta_ne_zero_of_one_le_re` and `β > 0` from `1/(58 log|γ|) ≤ 1/58`. This is the drop-in
replacement for `Sieve.exists_zero_free_region`.

## No exceptional range

Every zero of `ξ` has squared ordinate above `41/2 > 16`, so the threshold `|γ| ≥ 4` excludes
nothing.
[`ZetaZeroFreeRegionAllZeros`](../../../../formal/GaloisForLFunctions/RHTower/ZetaZeroFreeRegionAllZeros.lean)
records that:

- `RHTower.four_le_abs_im_of_zeta_zero` — every nontrivial zero has `|Im ρ| ≥ 4`.
- `RHTower.re_le_one_sub_of_zeta_zero` — **every** nontrivial zero satisfies
  `Re ρ ≤ 1 − 1/(58 log |Im ρ|)`.
- `RHTower.one_div_le_re_of_zeta_zero` — and, by the functional equation,
  `1/(58 log |Im ρ|) ≤ Re ρ`.
- `RHTower.mul_one_sub_re_ge_of_zeta_zero` — hence
  `Re ρ (1 − Re ρ) ≥ u(1−u)`, `u = 1/(58 log |Im ρ|)`.

So the final statement carries no threshold, no exceptional set, and no existential constant.

[`ZetaZeroFreeRegionUnrestricted`](../../../../formal/GaloisForLFunctions/RHTower/ZetaZeroFreeRegionUnrestricted.lean)
states it without any case hypothesis on the ordinate, using the scale `log(|Im s| + 4)`:

- `RHTower.riemannZeta_ne_zero_of_abs_im_lt_four` — the strip `|Im s| < 4` is zero-free outright.
- `RHTower.riemannZeta_ne_zero_of_lt_re` — **`0 < Re s → 1 − 1/(58 log(|Im s| + 4)) < Re s → ζ(s) ≠ 0`**,
  with `Re s ≥ 1` covered by `riemannZeta_ne_zero_of_one_le_re`.
- `RHTower.riemannZeta_ne_zero_of_lt_re_coords` — the same in `(β, t)` coordinates, matching the
  corpus's region interfaces.

## What remains of MUST-269

With `c = 1/58` the hyperbolic condition holds at the lowest certified ordinate. In the exact form
`1/4 ≤ b(γ² + 2 − 2b)`, `b = β(1−β)`, the region gives `b ≥ u(1−u)` with `u = 1/(58 log γ)` — the
lower bound `β ≥ u` comes from applying the region to the partner copy at `1 − ρ̄`, which has the
same ordinate. At `γ² = 41/2` this reads `0.25367 ≥ 0.25`, a margin of `1.5%`, and the margin grows:
`(γ² + K)/log γ` is increasing for `γ ≥ √(41/2)` because `2γ₀² log γ₀ ≥ γ₀² + K`, which follows from
`log γ ≤ log γ₀ + γ/γ₀ − 1` alone.

So MUST-269 reduces to assembling exactly that: the two applications of the region (to `q` and to
`lagPartner q`, plus `xiZeroCopyConjEquiv` for negative ordinates) and the monotonicity comparison.

## Log
- 2026-09-24 — created; archimedean real-part bound, half-coefficient chain and the region from
  ordinate four proved in Lean.
