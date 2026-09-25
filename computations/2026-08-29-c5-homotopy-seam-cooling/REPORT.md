# C5 likelihood-homotopy seam cooling reconnaissance

## Question

Can exact computation kill the likelihood-homotopy curvature route, or expose a proof-sized
survivor? Computation is diagnostic only and is not, directly or indirectly, a Lean premise.

## Exact symbolic outcome

The first nonzero seam coefficient of `M'''` factors as

```text
(8 F2^3 / 3) *
  [9 (2 x y - z) + 2 (x + r) (y - s)^2 / (-a2)],
```

where `x=-F3/F2`, `y=F4/F2`, `z=-F5/F2`, and the atom variables satisfy the already-proved
signs. Thus the new source obligation is

```text
F2 * F5 - 2 * F3 * F4 > 0,
```

equivalently strict increase of `F4/F2^2`. A sufficient split is

```text
3 A F2 < -F3,       -F5 < 6 A F4.
```

The first inequality has a short paper proof from the corpus theorem `2 variance < thirdCumulant`
and `A>=6`. The second is exactly

```text
d/dx (exp(3 A) * F4) > 0.
```

For its one-particle ordinary sector, the complete `n=2` atom-plus-ray reserve is

```text
exp(-3 A) * 32/P *
  12 A P9(A) / (2 A - 3)^6,
```

up to the common positive normalization, with

```text
P9(A) = 27648 A^9 - 266976 A^8 + 1120128 A^7 - 2666128 A^6
      + 3891600 A^5 - 3546654 A^4 + 1938420 A^3 - 573156 A^2
      + 68850 A - 1215.
```

After `A=y+6`, every coefficient of `P9` is positive. This dominant reserve is therefore an exact
paper-level positive statement for every `A>=6`; it does not depend on sampled numbers.

## Hostile numerical outcome

RunPod used 32 of 128 CPUs, 80 decimal digits, exact atom-plus-ray moment formulas, `n<=12`, and
4,096 logarithmically spaced scales on `6<=A<=1000`. Independent anchors used 120 digits and
`n<=20`.

- No counterexample to `3AF2 < -F3`, `-F5 < 6AF4`, or `F2F5-2F3F4>0` appeared.
- `R2=(-F3)/(AF2)` and `R4=(-F5)/(AF4)` increased throughout the grid. `2R2-R4` decreased but
  remained above `6.0000049` at `A=1000`.
- Worst theta tail opposition occurs at `A=6`: the full `n>=3` ordinary loss is only
  `2.007544941...e-10` of the exact positive `n=2` reserve.
- At `A=6`, `F5+6AF4 = 3.000820912...`; ordinary reserve is `3.000787484...`, so the resolved Bell
  correction is favorable.
- Exact dominant asymptotics are
  `R2=6-4/A+19/(12A^2)+...`, `R4=6-8/A-7/(4A^2)+...`, and
  `2R2-R4=6+59/(12A^2)+...`.

These values are route-selection evidence only. They are not continuous interval certificates.

## Routes killed and opened

Killed: pointwise fourth/sixth Cauchy. Exact score algebra gives

```text
p4(z) p6(z) - p5(z)^2 = -z^3 Q6(z),
```

with `Q6(z)>0` in the physical tail. Pointwise `p5 <= 3A p4` also fails away from the minimal
spectral edge. Generic moment/log-convexity proofs therefore cannot establish the cooling law.

Opened: exact dominant-atom/ray absorption. Required proof has three explicit pieces:

1. use positive shifted polynomial above for `n=2` ordinary reserve;
2. absorb all `n>=3` ordinary loss using theta exponential gap `8-3=5`;
3. prove Bell correction cannot consume remaining reserve, using existing tail-probability and
   moment-product bounds.

This is substantially narrower than original seven-jet curvature conjecture and reuses existing
spectral/Fock infrastructure. Failure of either absorption step would kill this sufficient route
without killing the full source inequality.

## Files

- `run_experiments.py`: exact symbolic identities plus multicore scan.
- `results.json`: machine-readable exact and numeric output.
- `verify_results.py`, `verify-output.txt`: independent high-precision anchor audit.
