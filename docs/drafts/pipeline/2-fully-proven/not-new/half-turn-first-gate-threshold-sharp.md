# Half-Turn First-Gate Threshold Is Sharp

- **ID:** half-turn-first-gate-threshold-sharp
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / source-transfer guardrail
- **Grade:** BRIDGE / route splitter. This theorem shows that the first
  repaired Hankel gate is not enough to kill broad positive repaired packets.
- **Source:** `bounded-half-turn-frequency-packets-fail-hankel.md`

## Statement

Let `x>0`, `y>0` be two squared frequencies. Consider the half-turn repaired
two-frequency packet with weights

`c_x=y^2`, `c_y=x^2`.

Equivalently, the probability weights

`p_i=c_i x_i^2/M_2`

place mass `1/2` at each endpoint. Its repaired moments are

`U_k=(c_x x^k+c_y y^k)/(2k-1)!`.

Then

`U_1 U_3-U_2^2`

`= x^3 y^3 (3x^2-34xy+3y^2)/360`.

Consequently:

1. If `3(x^2+y^2)>34xy`, the first shifted Hankel determinant is positive.
2. If `3(x^2+y^2)=34xy`, the first shifted Hankel determinant is zero.
3. If `3(x^2+y^2)<34xy`, the first shifted Hankel determinant is negative.

For `r=y/x>=1`, the threshold equation is

`3r^2-34r+3=0`,

so the upper threshold is

`theta=(17+2 sqrt(70))/3`.

Thus the spread threshold in
`bounded-half-turn-frequency-packets-fail-hankel.md` is sharp for the first
Hankel gate: above it, a positive repaired two-endpoint packet can already pass
that gate.

## Proof

For the balanced endpoint packet,

`M_1=y^2 x+x^2 y=xy(x+y)`,

`M_2=y^2 x^2+x^2 y^2=2x^2y^2`,

`M_3=y^2 x^3+x^2 y^3=x^2y^2(x+y)`.

Therefore

`U_1U_3-U_2^2`

`= M_1M_3/120-(M_2/6)^2`

`= x^3y^3(x+y)^2/120 - x^4y^4/9`

`= x^3 y^3(3x^2-34xy+3y^2)/360`.

Since `x^3y^3/360>0`, the determinant has exactly the sign of

`3x^2-34xy+3y^2`.

Putting `r=y/x` gives the threshold quadratic

`3r^2-34r+3`.

Its roots are

`(17-2 sqrt(70))/3` and `(17+2 sqrt(70))/3`.

For `r>=1`, the determinant is positive exactly beyond the upper root, zero at
the upper root, and negative below it.

## Consequence

The first repaired Hankel gate is now completely separated from the all-order
problem:

- Below `theta`, positive repaired packets are impossible at gate one.
- Above `theta`, gate one can be passed by an explicit positive packet.

Therefore the surviving half-turn route cannot be rejected merely because the
first gate is hard. The real obstruction has moved to source-building the
required broad spread and proving the higher shifted Hankel gates, or replacing
the repaired-packet model with a multiplicative or boundary/index object.

## Boundary

This theorem proves only first-gate sharpness. It does not prove that any broad
positive repaired packet is Markov/Stieltjes, and it does not supply the
completed Euler/Gamma/FE source mechanism that would force the packet. Passing
one `2 x 2` determinant is not RH-bearing.

## Theatre Test

For any proposed repaired-packet proof:

1. If it never produces squared-frequency spread at least `theta`, it fails at
   the first Hankel gate.
2. If it does produce spread above `theta`, it has only cleared gate one.
3. The proof must then explain why all higher shifted Hankel determinants are
   nonnegative from source data, without feeding the zero divisor as input.

## Novelty Status

The computation is elementary. The significance is route control: the
quantitative first-gate obstruction is exact, so further work must not pretend
that improving the first determinant alone is progress toward the full Markov
cone.

## Gates

- [x] 0 -> 1 in-progress: first-gate sharpness question isolated.
- [x] 1 -> 2 fully-proven: explicit balanced endpoint determinant computed.
- [x] formal core: determinant identity and positive-above-threshold criterion
  proved as
  `GaloisForLFunctions.twoFrequency_halfTurn_balanced_det_identity` and
  `GaloisForLFunctions.twoFrequency_halfTurn_balanced_det_pos`.

## Log

- 2026-06-24 -- Codex: created to close the sharpness question left by
  `bounded-half-turn-frequency-packets-fail-hankel.md`.
