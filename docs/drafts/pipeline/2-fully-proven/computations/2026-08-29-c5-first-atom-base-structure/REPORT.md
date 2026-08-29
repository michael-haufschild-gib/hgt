# CLG exact first-atom base-margin structure

Date: 2026-08-29  
Status: computation complete; diagnostic only; physical base sign independently formalized

## Route question

At the start of this run, CLG direct fixed-action transport reduced in the structural first-atom
tail to positivity of `c5SingleAtomBaseCompensationMargin A t`. This run tried to kill that exact
margin on the enlarged
chamber

```text
A ≥ 6,
0 < ρ = λ(A)(cosh(2t)-1) < 1/2.
```

The chamber contains the physical same-half-line region used by the route.

## Exact reduction

Write `z=cosh(2t)-1` and `s=2sinh(2t)`. After clearing the already-positive rational factors and
using `s²=4z(z+2)`, the numerator reduces exactly to

```text
8 * (s*(P₀(A,z) + t² P₂(A,z)) + t Q₀(A,z)).
```

Its denominator is

```text
(2A-3) * (-4A²+12Az+12A-9)³,
```

which is negative when `A≥6` and `ρ<1/2`. Therefore the base margin is positive exactly when

```text
s*(P₀+t²P₂) + t Q₀ < 0.                         (CLG-B)
```

The first coefficient factors completely:

```text
P₀ = A² z (72z+25)
     (-4A²+12Az+12A-15)
     (-4A²+12Az+12A-9)
     (-8A³+24A²z+36A²-36Az-42A+45).
```

All three nontrivial factors have the signs needed to give `P₀<0` on the chamber. For the cubic
factor, substitute `ρ=12Az/(2A-3)²<1/2`; its upper bound is
`-4A³+18A²-15A+63/2<0` for `A≥6`.

## Killed proof shortcut

`P₂` is not sign-definite. Exact rational witnesses already occur at `A=6`:

```text
ρ=1/4:    P₂/(20A²) = -42145677/64,
ρ=49/100: P₂/(20A²) = 2043490479363/1000000.
```

Thus termwise negativity of `P₀`, `P₂`, and `Q₀` cannot prove `(CLG-B)`. Hyperbolic compensation
between all three terms is essential.

## Positive seam survivor

The base margin vanishes through order `t⁵`. Its first nonzero term is order `t⁷`, with coefficient

```text
4096 A² p(A) / (9(2A-3)⁷),

p(A) = 1664A⁷ - 17472A⁶ + 78624A⁵ - 121536A⁴
       + 13968A³ - 181656A² + 254340A - 78975.
```

Putting `A=6+x` gives coefficients

```text
1664, 52416, 707616, 5382144, 25401744,
75714696, 132334884, 102433977,
```

all strictly positive. This is a computation-free paper proof that the desingularized seam
coefficient is positive for every `A≥6`.

## Hostile scan and interpretation

- 204,288 deterministic points;
- 200,000 randomized boundary-biased points;
- 100 decimal digits;
- `6 ≤ A ≤ π exp(40)` and `10^-12 ≤ ρ < 1/2`;
- no nonpositive base margin and no nonnegative centre numerator.

These signs are diagnostic only.  During this audit the physical same-half-line base sign and full
first-atom compensation were independently proved and formalized as
`c5SingleAtomBaseCompensationMargin_pos_of_sameHalfLine` and
`c5SingleAtomCompensationMargin_pos_of_sameHalfLine`.  This computation therefore records an
enlarged-chamber audit and the killed termwise-`P₂` shortcut; it is no longer the live CLG core.

Current route target is higher-atom likelihood interference.  The next route-level computations
are recorded in `../2026-08-29-c5-likelihood-interpolation/REPORT.md` and
`../2026-08-29-c5-likelihood-tangent-reserve/REPORT.md`.

## Reproduction

RunPod used 128 workers with one BLAS thread each. `verify_results.py` checks the exact factor
identity, opposite-sign `P₂` witnesses, order-seven seam coefficient, and scan signs.
`SHA256SUMS` authenticates downloaded artifacts.

```bash
python3 run_experiments.py --workers 128 --dps 100 \
  --A-points 192 --rho-points 640 --random-points 200000 \
  --max-u 20 --output results.json
python3 verify_results.py .
```
