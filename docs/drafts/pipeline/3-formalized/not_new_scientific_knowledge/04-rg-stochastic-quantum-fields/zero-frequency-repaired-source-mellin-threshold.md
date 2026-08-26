# Zero-Frequency Repaired Source Mellin Threshold

- **ID:** zero-frequency-repaired-source-mellin-threshold
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / source-admissibility guardrail
- **Source:** `locally-infinite-repaired-frequency-source-for-compact-markov.md`;
  `infinite-half-turn-frequency-source-admissibility-split.md`
- **Statement:** For compact Markov targets not supported only at `0`, every
  positive half-turn repaired-frequency source has exact local integrability
  threshold exponent `0` at zero frequency: all positive Mellin powers are
  locally finite, while exponent `0` and every negative exponent are locally
  infinite.

## Purpose

The local-infinity theorem kills local finiteness of the repaired-frequency
source. This card records the adjacent threshold. It prevents a weaker
admissibility condition, such as finite positive fractional moments or finite
positive Mellin energy near frequency `0`, from being mistaken for a real
source selector.

## Theorem

[PROVED HERE]

Let `nu` be a finite positive measure supported in `[0,R]`, not supported only
at `0`, and define

`S_k = int y^k dnu(y)`, for `k >= 1`.

Assume `mu` is a positive measure on `(0,infty)` with finite positive integer
moments and

`int x^k dmu(x) = (2k-1)! S_k`, for every `k >= 1`.

Then for every `delta > 0`:

1. for every `q > 0`,

   `int_(0,delta) x^q dmu(x) < infinity`;

2. for `q = 0`,

   `mu((0,delta)) = infinity`;

3. for every `q < 0`,

   `int_(0,delta) x^q dmu(x) = infinity`.

Thus `0` is the exact local Mellin integrability threshold.

## Proof

As in `locally-infinite-repaired-frequency-source-for-compact-markov.md`, set

`dlambda(x) = x dmu(x)`.

Then `lambda` is a finite positive measure and

`int x^n dlambda(x) = (2n+1)! S_(n+1)`, for every `n >= 0`.

The compact-support estimate

`S_(n+1) <= C R^(n+1)`

gives Carleman determinacy for this shifted factorial moment problem.

The representing measure is

`lambda_0 = pushforward of lambda_base(a) x (y dnu(y)) under x = a y`,

where

`dlambda_base(a) = e^(-sqrt(a)) da/2`.

Indeed,

`int a^n dlambda_base(a) = (2n+1)!`,

so `lambda_0` has the same moments as `lambda`. By determinacy,
`lambda = lambda_0`. Since `lambda = x mu`,

`dmu(x) = x^(-1) dlambda_0(x)`.

Let `q > 0`. Then

`int x^q dmu(x)
 = int (a y)^q (a y)^(-1) y dlambda_base(a) dnu(y)`

`= (int a^(q-1) dlambda_base(a)) (int y^q dnu(y))`.

The first factor is finite:

`int a^(q-1) dlambda_base(a)
 = (1/2) int_0^infty a^(q-1) e^(-sqrt(a)) da`

`= int_0^infty r^(2q-1) e^(-r) dr = Gamma(2q) < infinity`.

The second factor is finite because `nu` is finite and compactly supported.
Therefore every positive Mellin moment of `mu` is finite, hence its restriction
to `(0,delta)` is finite in the same weighted sense.

For `q = 0`, the previous local-infinity theorem gives

`mu((0,delta)) = infinity`.

For `q < 0`, on `(0,delta)` one has `x^q >= delta^q > 0`; hence

`int_(0,delta) x^q dmu(x) >= delta^q mu((0,delta)) = infinity`.

This proves the threshold.

## Consequence For The RH Route

The zero-frequency reservoir is invisible to all positive local Mellin
finiteness tests: those tests are automatically satisfied for compact Markov
targets. But local finiteness itself, or any nonpositive Mellin threshold,
excludes the same compact Markov targets.

Therefore a repaired-frequency source proof cannot be rescued by adding a
condition such as finite positive fractional moments near zero frequency. Such
conditions are too weak. Conversely, Radon/local-finite conditions at the
border are too strong for this model. The remaining live alternatives are:

1. permit the locally infinite reservoir and give a noncircular source law that
   selects it;
2. replace the additive repaired-frequency model by a completed
   boundary/index object.

## Gates

- [x] 0 -> 1 in-progress: weaker Mellin-admissibility loophole isolated.
- [x] 1 -> 2 fully-proven: exact local Mellin threshold proved from the
  determinate shifted-factorial representing measure.
- [x] 2 -> 3 formalized: exact positive/zero/negative Mellin threshold
  formalized for every source realizing the shifted-factorial moments.

## Log

- 2026-06-24 -- Codex: created after the local zero-frequency infinity theorem
  to classify which local integrability restrictions actually constrain the
  repaired-frequency source.

## 2026-06-24 weighted-integrability strengthening

`zero-frequency-repaired-source-dx-over-x-law.md` strengthens this Mellin-power threshold to every nonnegative local weight. Under the same compact Markov-target hypotheses,

`int_(0,delta) w dmu < infinity <=> int_0^delta w(x) dx/x < infinity`.

This card is the special case `w(x)=x^q`: `x^q` is `dx/x`-integrable near `0` exactly when `q>0`.

## 2026-08-26 Lean formalization

Formalized unconditionally in
`GaloisForLFunctions.HTGeometry.RepairedFrequencyMellinThreshold`.
The capstone declaration is `source_exact_localMellin_threshold`; it includes
all real exponents in the three exact regimes. Target module build passed.
Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
Module is wired into the `GaloisForLFunctions.HTGeometry` umbrella.
