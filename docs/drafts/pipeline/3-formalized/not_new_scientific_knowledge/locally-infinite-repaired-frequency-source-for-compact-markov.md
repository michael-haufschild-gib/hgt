# Locally Infinite Repaired-Frequency Source For Compact Markov Targets

- **ID:** locally-infinite-repaired-frequency-source-for-compact-markov
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / source-admissibility guardrail
- **Source:** `infinite-half-turn-frequency-source-admissibility-split.md`;
  `seam-log-markov-pick-rh-equivalence.md`
- **Statement:** For any compact Stieltjes/Markov target whose representing
  measure is not supported only at `0`, every positive half-turn
  repaired-frequency source realizing its positive moments has infinite mass in
  every neighborhood of frequency `0`.

## Goal

Strengthen the infinite repaired-frequency split. The earlier finite-mass
obstruction showed that a finite positive repaired-frequency source cannot
realize a compact Markov target with nonzero positive moments. This theorem
shows more: local finiteness at the zero-frequency border is already
impossible. Thus the zero-frequency reservoir is forced locally by the
factorial moment transform, not merely by a bad global choice of representing
source.

## Theorem

[PROVED HERE]

Let `nu` be a finite positive measure supported in `[0,R]`, not supported only
at `0`, and define

`S_k = int y^k dnu(y)`, for `k >= 1`.

Assume `mu` is a positive measure on `(0,infty)` with finite positive moments
and

`int x^k dmu(x) = (2k-1)! S_k`, for every `k >= 1`.

Then for every `delta > 0`,

`mu((0,delta)) = infinity`.

## Proof

Set

`dlambda(x) = x dmu(x)`.

Since `int x dmu(x) < infinity`, `lambda` is a finite positive measure on
`(0,infty)`. Its moments are

`int x^n dlambda(x) = int x^(n+1) dmu(x) = (2n+1)! S_(n+1)`.

The shifted factorial moment problem is determinate by the same Carleman
estimate used in `infinite-half-turn-frequency-source-admissibility-split.md`:
compact support gives `S_(n+1) <= C R^(n+1)`, so

`((2n+1)! S_(n+1))^(-1/(2n)) >= C'/n`

for all large `n`, and the Carleman series diverges.

One representing measure for these moments is

`lambda_0 = pushforward of lambda_base(a) x (y dnu(y)) under x = a y`,

where

`dlambda_base(a) = e^(-sqrt(a)) da/2`.

Indeed,

`int a^n dlambda_base(a) = (2n+1)!`,

so

`int x^n dlambda_0(x)
 = int (a y)^n y dlambda_base(a) dnu(y)
 = (2n+1)! S_(n+1)`.

By determinacy, `lambda = lambda_0`. Since `lambda = x mu`, on `(0,infty)`

`dmu(x) = x^(-1) dlambda_0(x)`.

Fix `delta > 0`. Because `nu` is not supported only at `0`, there is `eta > 0`
with `nu([eta,R]) > 0`. For `y in [eta,R]` and `0 < a < delta/R`, one has
`a y < delta`. Therefore

`mu((0,delta))
 >= int_(y in [eta,R]) int_(0<a<delta/R)
      (a y)^(-1) y dlambda_base(a) dnu(y)`

`= nu([eta,R]) int_0^(delta/R) e^(-sqrt(a)) da/(2a)
 = infinity`,

because the integrand is asymptotic to `1/(2a)` as `a -> 0+`.

Thus every zero-frequency neighborhood has infinite `mu`-mass.

## Consequence For The RH Route

The positive repaired-frequency model has only two remaining forms:

1. It permits locally infinite mass at frequency `0`; then a source theorem
   must explain why the Euler/Gamma/FE law selects exactly the needed border
   reservoir without using the target Markov positivity as input.
2. It requires local finiteness, Radon behavior, a finite border counterterm, or
   a finite-part mass at the zero-frequency endpoint; then it cannot realize
   even a compact Markov target not supported only at `0` through this model.

Therefore a source-built proof of the Markov/Pick cone cannot be recovered by
adding a finite border correction to the positive repaired-frequency expansion.
It must either supply a noncircular selection law for a locally infinite border
source or move to the completed boundary/index object.

## Gates

- [x] 0 -> 1 in-progress: local-finiteness loophole isolated inside the
  infinite repaired-source split.
- [x] 1 -> 2 fully-proven: determinate shifted-factorial representing measure
  and local divergence proof completed.
- [x] 2 -> 3 formalized: measure-theoretic determinacy/local-divergence theorem
  unconditionally proved in Lean 4 (see `## Lean formalization`).

## Log

- 2026-06-24 -- Codex: split from
  `infinite-half-turn-frequency-source-admissibility-split.md` after the
  monotone border audit.

## Lean formalization

Unconditional; axiom profile `[propext, Classical.choice, Quot.sound]` on every capstone.

**Modules**

- `formal/GaloisForLFunctions/HTGeometry/SqrtExponentialMoments.lean`
  `integral_pow_mul_exp_neg_sqrt : ∫ a in Ioi 0, a ^ n * exp (-√a) = 2 * (2n+1)!`
  (the base-measure moment identity `∫ a^n dλ_base = (2n+1)!`).
- `formal/GaloisForLFunctions/HTGeometry/ShiftedFactorialMomentDensity.lean`
  Replaces the card's two-dimensional pushforward `λ₀` by an explicit density on `(0,∞)`:
  `factorialMomentDensity ν x = (∫ y, exp (-√(x/y)) ∂(ν.restrict (Ioi 0))) / 2`,
  `factorialMomentMeasure ν = (volume.restrict (Ioi 0)).withDensity (ofReal ∘ factorialMomentDensity ν)`.
  Proved: joint measurability, Tonelli/Fubini integrability of `(x,y) ↦ x^n e^{-√(x/y)}`,
  `integral_pow_factorialMomentMeasure : ∫ x^n dλ₀ = (2n+1)! * ∫ y^(n+1) dν`,
  finiteness, and the Hardy/Carleman-type bound
  `integrable_exp_sqrt_factorialMomentMeasure` for every `c < 1/(2√R)`.
- `formal/GaloisForLFunctions/HTGeometry/RepairedFrequencyLocalDivergence.lean`
  `le_factorialMomentDensity : 0 < η → x ≤ η → e^{-1} · ν([η,∞)).toReal / 2 ≤ factorialMomentDensity ν x`
  (the border lower bound; on `x ≤ η ≤ y` one has `√(x/y) ≤ 1`).
  `integral_pow_shiftedMeasure`, `integrable_pow_shiftedMeasure`,
  `isFiniteMeasure_shiftedMeasure` realize `dλ = x dμ` as `μ.withDensity (ofReal ·)`
  and transfer the shifted moments.
  `shiftedMeasure_eq_factorialMomentMeasure` is the determinacy step: both measures are finite
  Stieltjes representatives of the same sequence and `λ₀` satisfies Hardy's condition, so
  the corpus theorem `measure_eq_of_hasStieltjesMoments_of_hardy` forces `λ = λ₀`.
  **Capstone** `measure_Ioo_eq_top_of_shiftedFactorialMoments`:

  ```text
  ν finite, ν-a.e. supported in [0,R] (R > 0), ν([η,∞)) ≠ 0 for some η > 0,
  μ with μ-a.e. nonnegative support, ∫ x^{n+1} dμ integrable and
  ∫ x^{n+1} dμ = (2n+1)! ∫_{(0,∞)} y^{n+1} dν  for every n
  ⟹ μ((0,δ)) = ∞ for every δ > 0.
  ```

**Route change against the card's prose.** The card divides by `x` inside a two-dimensional
pushforward and reads off `∫_0^{δ/R} e^{-√a} da/(2a) = ∞`. Formalizing a pushforward under
`(a,y) ↦ a y` of a product of a density and `y dν` would need a change-of-variables layer mathlib
does not have. The Lean route keeps the divergence but obtains it from the density directly:
with `t = min δ η`, the dyadic blocks `A_j = (t/2^{j+1}, t/2^j)` satisfy
`ofReal c · vol(A_j) ≤ λ₀(A_j) = λ(A_j) ≤ ofReal(t/2^j) · μ(A_j)`, hence
`ofReal c / 2 ≤ μ(A_j)` for **every** `j`; the blocks are disjoint and inside `(0,δ)`, so
`N · (ofReal c / 2) ≤ μ((0,δ))` for all `N`, and `ENNReal.exists_nat_mul_gt` closes it.
This is the harmonic-series divergence of `∫ dx/x` in a form that needs no improper integral.

**Reusable assets left behind.** `∫_0^∞ a^n e^{-√a} da = 2(2n+1)!`; the `factorialMomentDensity`
convolution-type density with its Fubini and Hardy layers; the `x ↦ x·μ` shifted-measure transfer
(`integral_pow_shiftedMeasure` and companions), usable for any Stieltjes moment shift; and the
dyadic-block device for turning a two-sided density comparison into a local infinity.
