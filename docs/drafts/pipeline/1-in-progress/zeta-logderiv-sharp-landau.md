# A sharp Landau-type bound for `−Re ζ'/ζ` right of the abscissa

- **ID:** ZFR-SHARP-001
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** MUST-269; `Sieve/DeLaValleePoussinInequality.lean`, `Sieve/ZeroFreeRegionKappaOne.lean`
- **Statement:** for `1 < σ ≤ 2` and `t ≥ 4`, `−Re (ζ'/ζ)(σ+it) ≤ 1/5 + log t + digammaVerticalLogConstant`.

## Goal

The corpus's zero-free region `Sieve.exists_zero_free_region` has width `1/(10000 log|γ|)` and a
threshold `T = exp(u₀²)` with `u₀ ≥ 202`, i.e. `|γ| ≥ e^{40804}`. Both come from one lossy input: the
Landau step in `dlvp_inequality`, which contributes `320·(5/4) log(7 + 8|γ|)` — a coefficient of
`400` on `log|γ|`. Everything downstream (the zero-free region, MUST-269, the lag lane's threshold)
inherits that loss.

## What is proved

Module [`ZetaLogDerivSharpLandau`](../../../../formal/GaloisForLFunctions/RHTower/ZetaLogDerivSharpLandau.lean):

`RHTower.neg_re_logDeriv_riemannZeta_le` — for `1 < σ ≤ 2` and `4 ≤ t`,

```text
−Re (ζ'/ζ)(σ + it) ≤ 1/5 + log t + digammaVerticalLogConstant.
```

Mechanism: the four-factor identity `ξ'/ξ = 1/s + 1/(s−1) + Γ_ℝ'/Γ_ℝ + ζ'/ζ`
(`logDeriv_xi_fourFactor`) together with `re_logDeriv_xi_pos_of_one_le_re` — the completed
logarithmic derivative has *positive* real part right of the strip, so dropping it only helps. What
is left is elementary: `Re(1/s) ≤ 2/17`, `Re(1/(s−1)) ≤ 1/16`, and `Re(Γ_ℝ'/Γ_ℝ) ≤ ‖Γ_ℝ'/Γ_ℝ‖ ≤
log t + C` by `norm_logDeriv_Gammaℝ_le`. **The coefficient of `log t` is one**, against `400` in the
current Landau input.

Built, wired into `GaloisForLFunctions.RHTower`, axiom-clean.

## What it would give

Substituting into the three-four-one step, a zero `β + iγ` gives
`4/(σ−β) ≤ 3/δ + 3A + 5 log|γ| + C` with `σ = 1 + δ`. Putting `δ = c₀/log|γ|` and
`1 − β < c/log|γ|`, the region survives whenever `4/(c₀+c) − 3/c₀ > 5`; the left side is maximised at
`c₀ = √3 c/(2−√3)` with value `0.0717/c`, so any `c < 0.0143` works — a width of about
`1/(70 log|γ|)` instead of `1/(10000 log|γ|)`, and a threshold governed by the size of `C` rather
than by `e^{40804}`.

## The companion bound, with the zero retained

Module [`ZetaLogDerivSharpLandauZero`](../../../../formal/GaloisForLFunctions/RHTower/ZetaLogDerivSharpLandauZero.lean)
supplies the sharp form:

- `RHTower.xiPairedResolventTerm_nonneg` — every paired resolvent term is nonnegative right of the
  strip.
- `RHTower.coe_xiZeroCopyReflect`, `RHTower.xiPairedResolventTerm_reflect` — reflection permutes the
  two halves of a paired term, so `paired (reflect q) = paired q`.
- `RHTower.resolventTerm_le_re_logDeriv_xi` — **`(σ − β)/|s − ρ|² ≤ Re (ξ'/ξ)(s)` for `Re s ≥ 1`,
  with no loss from the pairing.** Summing over the two-element set `{q, reflect q}` gives
  `2·(σ−β)/|s−ρ|²` in both cases: when the copies are distinct the pair contributes twice, and when
  they coincide the single paired term is already `2·(σ−β)/|s−ρ|²` because `ρ = 1 − ρ`. Extracting
  only `{q}` would have cost a factor `2`, and that factor is fatal — with `2/(σ−β)` the bracket
  `2/(c₀+c) − 3/c₀` is negative for every `c₀`.
- `RHTower.neg_re_logDeriv_riemannZeta_le_sub_resolvent` —
  `−Re (ζ'/ζ)(σ+it) ≤ 1/5 + log t + C − (σ − β)/|s − ρ|²`.

Built, wired, axiom-clean.

## The assembly and the sharpened region

[`DlvpSharp`](../../../../formal/GaloisForLFunctions/RHTower/DlvpSharp.lean) —
`RHTower.dlvp_sharp`: for a zero copy of `ξ` at `ρ = β + iγ` with `γ ≥ 4`, every `1 < σ ≤ 2` and any
pole bound `A`,

```text
4/(σ − β) ≤ 3/(σ − 1) + 5 log γ + dlvpSharpConstant A,
dlvpSharpConstant A = 3A + 5(1/5 + digammaVerticalLogConstant) + log 2.
```

**The coefficient of `log γ` is `5`, against `320·(5/4) = 400` in `dlvp_inequality`.** The three
inputs are the bound at height `2γ`, the bound with the zero retained at height `γ`, and the
three-four-one inequality `Sieve.re_logDeriv_shift_le`.

[`ZeroFreeRegionSharp`](../../../../formal/GaloisForLFunctions/RHTower/ZeroFreeRegionSharp.lean) —
`RHTower.exists_xiZeroCopy_zero_free_sharp`:

```text
∃ T ≥ 4, ∀ q : XiZeroCopy, T ≤ Im ρ_q → Re ρ_q ≤ 1 − 1/(100 log (Im ρ_q)).
```

Choosing `δ = 1/(16 log γ)` turns the inequality into `(1600/29) log γ < 53 log γ + K`, i.e.
`(63/29) log γ < K`, impossible once `log γ ≥ 29|K|/63`. **The width is `1/100`, against `1/10000`.**

All built, wired, axiom-clean, lint clean.

## The explicit pole bound and the explicit threshold

[`ZetaPoleBoundExplicit`](../../../../formal/GaloisForLFunctions/RHTower/ZetaPoleBoundExplicit.lean):

- `RHTower.re_digamma_ofReal_le` — `Re ψ(x) ≤ log 3 − 3/10` for `1/2 < x ≤ 1`. Two steps of
  `ψ(z+1) = ψ(z) + 1/z` move the argument to `x + 2 ∈ (5/2, 3]`, where
  `HTGeometry.norm_digamma_sub_log_le_of_re_pos` gives `‖ψ(z) − log z‖ ≤ 3/‖z‖ ≤ 6/5`; the two
  subtracted reciprocals are at least `1` and `1/2`.
- `RHTower.neg_re_logDeriv_riemannZeta_real_le` — **`−ζ'/ζ(σ) ≤ 1/(σ−1) + 1` for `1 < σ ≤ 2`**, the
  explicit pole bound. The four-factor identity at a real point gives
  `−ζ'/ζ(σ) ≤ 1/σ + 1/(σ−1) + Re ψ(σ/2)/2 − (log π)/2`, and `3 ≤ π` makes the archimedean term
  negative.
- `RHTower.forty_four_le_dlvpSharpConstant_one`, `RHTower.xiZeroCopy_zero_free_explicit` — the
  zero-free region with an **explicit** threshold:

```text
∀ q : XiZeroCopy, exp (29 K / 63) ≤ Im ρ_q → Re ρ_q ≤ 1 − 1/(100 log (Im ρ_q)),
K = dlvpSharpConstant 1 = 14 + 10π + 6 log 2 ≈ 49.58,  exp (29K/63) ≈ e^{22.8}.
```

Against `Sieve.exists_zero_free_region`: width `1/100` instead of `1/10000`, threshold `e^{22.8}`
instead of `e^{40804}`.

All built, wired, axiom-clean, lint clean.

## Open successor

MUST-269 stays open at bounded height: the hyperbolic condition `β(1−β)γ² ≥ 1/4` now follows for
`|γ| ≥ e^{22.8}`, but the corpus can only certify `γ² > 41/2` from below, so the range
`4.53 ≤ |γ| ≤ 8·10^9` is uncovered. Narrowing it further means sharpening `K`: the dominant part is
`5·digammaVerticalLogConstant = 10 + 10π + 5 log 2 ≈ 45`, and `digammaVerticalLogConstant = 2 + 2π +
log 2` is itself a crude bound on `‖Γ_ℝ'/Γ_ℝ‖` — replacing it by a real-part bound would roughly
halve `K` and take the threshold to about `e^{11}`.

## Log
- 2026-09-24 — created; the sharp bound proved and checked with `lake env lean`.
