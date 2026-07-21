# Squared-Xi dyadic half-plane rigidity RH bridge

- **ID:** `squared-xi-dyadic-half-plane-rigidity-rh`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / RH BRIDGE
- **Claim labels:** `[BRIDGE] [NOVELTY UNVERIFIED]`
- **Source lane:** squared-Xi fixed-order atom positivity

## Exact claim

For `z : ℂ`, set

```text
DyadicHalfPlane(z) := for every k : ℕ, 0 <= Re(z^(2^k)).
```

Then

```text
DyadicHalfPlane(z) <-> z.im = 0 and 0 <= z.re.                 (D)
```

For a multiplicity-exact Xi zero copy `q`, write

```text
delta(q) = Re(q) - 1/2,
gamma(q) = Im(q),
A(q)     = gamma(q)^2 - delta(q)^2 + 1,
B(q)     = 2 delta(q) gamma(q),
Z(q)     = ((A(q) : ℂ) - B(q) I)^(-1).
```

Define the fixed-shift squared-seam condition

```text
XiSquaredSeamDyadicHalfPlane :=
  for every q and k, 0 <= Re(Z(q)^(2^k)).
```

The Xi specialization is

```text
XiSquaredSeamDyadicHalfPlane <-> RiemannHypothesis.            (RH-D)
```

The already formalized theorem `xiOrderSixteenReciprocalPower_re_pos`, specialized to `y = 1`,
unconditionally discharges the rung `k = 4` because `2^4 = 16`.

## Internal frontier

- `[CORPUS]` `xiOrderSixteenReciprocalPower_re_pos` proves strict half-plane positivity at power
  `16` for every Xi zero copy and every `y > 1/4`.
- `[CORPUS]` `xiOrderNineteenReciprocalPower_re_pos` proves the analogous statement at power `19`.
- `[CORPUS]` consecutive source-exclusion modules currently reach powers `15, 16, 17, 18, 19`.
- `[CORPUS]` `riemannHypothesis_of_xiSpectralPoint_real` turns reality of every centered Xi
  spectral point into RH.
- Corpus search found no theorem using signs of the sparse powers `2^k` to kill the phase of the
  squared-seam coordinate. The unrelated endpoint-central dyadic bridge is a negative-binomial
  value transform, not phase dynamics.

Per user direction, this lane is an internal-corpus theorem search, not a literature or priority
claim. Scientific novelty is not asserted.

## Paper proof of (D)

The reverse implication is immediate: if `z` is a nonnegative real number, every natural power of
`z` is a nonnegative real number.

Assume `DyadicHalfPlane(z)`. If `z = 0`, the conclusion is immediate. Suppose `z != 0`, put
`r = |z| > 0`, and normalize `u = z/r`, so `|u| = 1`. For every `k`, positivity of `r^(2^k)` gives

```text
x_k := Re(u^(2^k)) >= 0.
```

Since `|u^(2^k)| = 1`, also `x_k <= 1`. Squaring a unit complex number gives the exact recurrence

```text
x_(k+1) = 2 x_k^2 - 1.                                        (1)
```

Indeed, if `v = u^(2^k)`, then

```text
Re(v^2) = Re(v)^2 - Im(v)^2
        = 2 Re(v)^2 - (Re(v)^2 + Im(v)^2)
        = 2 x_k^2 - 1.
```

Set `d_k = 1 - x_k`. From (1),

```text
d_(k+1) = 2 d_k (1 + x_k) >= 2 d_k,                            (2)
```

because `x_k >= 0`. Hence induction gives `d_k >= 2^k d_0`. If `d_0 > 0`, Archimedean growth of
`2^k` supplies `k` with `2^k d_0 > 1`. Then `d_k > 1`, contradicting `x_k >= 0`, which gives
`d_k <= 1`. Therefore `d_0 = 0`, so `Re(u) = 1`. Together with `|u| = 1`, this forces
`Im(u) = 0` and `u = 1`. Thus `z = r` is a positive real number. This proves (D).

## Paper proof of (RH-D)

First assume `XiSquaredSeamDyadicHalfPlane`. Fix `q`. The critical-strip bound gives
`delta(q)^2 < 1/4`, so

```text
A(q) = gamma(q)^2 - delta(q)^2 + 1 > 3/4.
```

Consequently `(A(q) : ℂ) - B(q) I` and `Z(q)` are nonzero. Applying (D) to `Z(q)` gives
`Im(Z(q)) = 0`. Direct inversion yields

```text
Im(Z(q)) = B(q) / (A(q)^2 + B(q)^2).
```

The denominator is positive, hence `B(q) = 0`. Every Xi divisor support point has nonzero
imaginary part, so `gamma(q) != 0`. From

```text
0 = B(q) = 2 delta(q) gamma(q)
```

we obtain `delta(q) = 0`, i.e. `Re(q) = 1/2`. Therefore every centered Xi spectral point is real,
and `riemannHypothesis_of_xiSpectralPoint_real` gives RH.

Conversely, assume RH. Every support point satisfies `Re(q) = 1/2`, so `delta(q) = B(q) = 0` and

```text
Z(q) = ((gamma(q)^2 + 1 : ℝ) : ℂ)^(-1).
```

This is positive real. Every dyadic power has nonnegative real part, proving
`XiSquaredSeamDyadicHalfPlane`.

## Hostile audit

1. **Finite prefixes do not suffice.** For any fixed `K`, a nonzero phase `theta` small enough
   makes `Re(exp(i theta)^(2^k)) > 0` for every `k <= K`. Thus powers `15` through `19`, or any
   other finite list, cannot force RH.
2. **A bare dyadic tail does not suffice.** If `z = exp(2 pi i / 2^K)`, then
   `z^(2^k) = 1` for every `k >= K`, although `z` is not real. Including all `k`, or supplying a
   separate root-ambiguity killer, is load-bearing.
3. **Nonnegativity suffices.** Boundary values cannot create a periodic exception because (2)
   uses only `x_k >= 0`; any `x_k = 0` makes `x_(k+1) = -1`, immediately violating the hypothesis.
4. **Zero causes no gap.** The pure theorem handles `z = 0` separately. Xi coordinates are nonzero
   because `A(q) > 0`.
5. **No hidden RH input occurs in the forward implication.** Critical-strip membership and
   nonvanishing of the imaginary coordinate are unconditional divisor-support facts. RH enters only
   in the reverse implication.
6. **Verdict:** `BRIDGE`. The theorem is a sparse phase-rigidity consumer, not an unconditional
   producer of dyadic signs. It shortens the source problem from consecutive all-order positivity
   to the exponentially sparse sequence `1, 2, 4, 8, 16, 32, ...`, but does not itself prove the
   open high dyadic rungs.

## Exact open core after this bridge

`[OPEN CORE]` Produce `Re(Z(q)^(2^k)) >= 0` unconditionally for every Xi zero copy and every
`k >= 5` (together with the low dyadic rungs), or find a stronger source invariant that implies
the complete dyadic half-plane condition without assuming an RH-equivalent phase conclusion.

The next source question is whether the existing quartet/source-exclusion mechanism has a
dyadic recurrence or a uniform corner budget. Repeating the fixed-order proof independently at
orders `32, 64, ...` is not yet a structural producer.

## Gates

- [x] Internal corpus and failed-route audit
- [x] Exact conjecture and hostile falsity/circularity audit
- [x] Dependency-closed paper proof written
- [x] Hostile second pass and Stage-2 promotion: `[PAPER-PROVED]`
- [ ] Exact Lean theorem
- [ ] Axiom/lint/module audit and Stage-3 promotion
- [ ] Unconditional dyadic source producer
- [ ] Full RH proof
