# PS4 Inversion Turns The HD3 Gauge Into Ghost Power Sums

- **ID:** ps4-hd3-gauge-ghost-power-sums
- **Stage:** 3-formalized
- **Type:** THEOREM (paper), proof-route atlas normalization
- **Source:** random formula-graph node 44/100, `PS4` in `docs/consolidated/revision01/formulas-graph.md`
- **Statement:** If the HD3 zero-free gauge shift `delta lambda_n = c n^2` is blindly inverted through the PS4 Li/binomial transform, it appears as the finite ordinary-power-sum perturbation

```text
delta P_1 = c,
delta P_2 = -2c,
delta P_j = 0  for j >= 3,
```

even though the zero divisor has not changed.

## Goal

Make the PS4 atlas normalization problem exact. The formula `lambda_n <-> P_j` is a divisor identity for canonical Li coefficients. It is not safe for arbitrary log-defined Li coefficients unless the zero-free Hadamard gauge has already been fixed or subtracted.

## Gates

- [x] 0 -> 1 in-progress: random formula selected and checked against existing Li/HD3 cards
- [x] 1 -> 2 fully-proven: binomial finite-difference proof complete
- [x] 2 -> 3 formalized: unconditional forward-difference identification
  `RHTower.ps4QuadraticGhost_eq_signed_fwdDiff`, exact degree-one and
  degree-two values, all-higher-degree vanishing, and real-parameter capstone
  `RHTower.ps4QuadraticGaugeGhost_classification` in
  `formal/GaloisForLFunctions/RHTower/PS4GaugeGhostPowerSums.lean`; exact
  target build passed and the capstone audit reports only `propext`,
  `Classical.choice`, and `Quot.sound`.
- [ ] 3 -> 4 publication-ready: fold into the Li/Jensen/Hadamard atlas notes

## Proof

[PROVED HERE]

For the canonical divisor chart, PS4 is the lower-triangular transform

```text
lambda_n = sum_{j=1}^n (-1)^(j+1) binom(n,j) P_j,
```

with inverse

```text
P_j = sum_{n=1}^j (-1)^(n+1) binom(j,n) lambda_n.
```

The HD3 card proves that the zero-free FE-symmetric gauge

```text
F_c(s)=exp(c(s-1/2)^2) xi(s)
```

does not move any zero but shifts the log-defined Li coefficients by

```text
delta lambda_n = c n^2.
```

Apply the PS4 inverse to this shift. The apparent power-sum perturbation is

```text
delta P_j
  = c sum_{n=1}^j (-1)^(n+1) binom(j,n) n^2.
```

These are signed finite differences of the polynomial `n^2`. Hence all terms vanish for `j >= 3`. Directly,

```text
delta P_1 = c,
delta P_2 = c(2*1^2 - 2^2) = -2c.
```

Thus blind PS4 inversion of the gauged log-defined Li sequence manufactures exactly two nonzero ordinary power sums:

```text
delta P_1 = c,   delta P_2 = -2c.
```

The forward transform confirms the localization:

```text
binom(n,1)c - binom(n,2)(-2c)
  = cn + c n(n-1)
  = c n^2.
```

But `F_c` has the same zero divisor as `xi`, since `exp(c(s-1/2)^2)` is zero-free. Therefore these `delta P_j` are not divisor power sums. They are gauge ghosts created by applying the divisor PS4 transform outside its normalized domain.

## Route Consequence

The ordinary power-sum side of the Li atlas is low-order gauge fragile. Before comparing `lambda_n`, `P_j`, Jensen coefficients, or reciprocal moments, the route must specify one of:

1. canonical completed `xi` normalization;
2. divisor-defined Li coefficients, independent of zero-free factors;
3. explicit subtraction of the zero-free Hadamard gauge.

Otherwise a zero-free multiplier can look like a real change in `P_1` and `P_2` under PS4 while leaving every zero, contour count, and reciprocal divisor atom fixed.

This is distinct from the HD3 gauge-shift card: that card locates the shift in the Li sequence; this card locates its exact image in the PS4 ordinary-power-sum chart.

## Computation

The finite-difference audit is archived at:

- `computations/2026-06-21-conway-ps4-gauge-ghost-power-sums.py`
- `computations/2026-06-21-conway-ps4-gauge-ghost-power-sums.txt`

## Log

- 2026-06-21 -- Conway: created from random formula-graph node 44/100 (`PS4`). Existing Li cards handled the reciprocal Chebyshev kernel and HD3 handled the direct Li gauge shift; this card records the PS4 inverse image of that shift as a finite ghost in the ordinary power-sum chart.
