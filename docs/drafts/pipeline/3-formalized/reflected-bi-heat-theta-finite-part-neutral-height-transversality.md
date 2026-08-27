# Reflected bi-heat theta finite-part neutral-height transversality

- **ID:** RBH-TFPN
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / EXACT LOCAL TRANSVERSALITY
- **Parent:** RBH-TFPK
- **Frontier-map policy:** read only

## Theorem

For every heat datum `P`, every `0 < sigma < 1`, and the vertical family

`z(gamma) = sigma + i gamma`,

the imaginary part of the canonical theta-pole finite part has the exact
absolutely convergent paired expansion

`sum_{d,N>=1} h_x(d) N^-1
  (r^(sigma-1) - r^(-sigma)) sin(gamma log r)`,

where `r=(N+d)/N`.  Its derivative at neutral height is

`sum_{d,N>=1} h_x(d) N^-1
  (r^(sigma-1) - r^(-sigma)) log r`.

Every slope atom has strict sign `sign(sigma-1/2)`, the Gaussian/inverse-square
bound `2 d h_x(d)/N^2` is summable, and therefore the complete slope is positive
for `sigma>1/2`, negative for `sigma<1/2`, and zero exactly at `sigma=1/2`.
Consequently the canonical imaginary finite part is nonzero throughout a
punctured neighborhood of `gamma=0` off wall.  More sharply, its quotient by
`gamma` has the same local sign as `sigma-1/2`.

## Corpus basis

- `ReflectedBiHeatThetaResidue` supplies canonical row subtraction, exact
  finite part, and a normally convergent regular series.
- `ReflectedBiHeatThetaFinitePartWallSchwarz` identifies the imaginary channel
  as wall-odd.
- `ReflectedBiHeatThetaFinitePartKleinFourNoGo` proves the unavoidable wall plus
  real-axis zero cross and isolates nonreal divisor support as the survivor.
- `GammaJumpMultiplier` supplies the inverse-square summability bridge used by
  the Gaussian lattice majorant.
- Mandatory corpus searches found no existing paired phase formula, signed
  neutral-height slope theorem, or derivative identification for the canonical
  reflected bi-heat finite part.

## Paper proof

Write positive additive difference as `d=k+1`, smaller lattice coordinate as
`N=n+1`, and `r=(N+d)/N>1`.  The zero-difference upper row vanishes after row
subtraction.  Pair the successor upper row with the strict lower row.  Positive
real-base complex-power multiplication gives

`upper = N^-1 r^(-z)` and `lower = N^-1 r^(z-1)`

up to real row-model subtractions.  Taking imaginary parts at
`z=sigma+i gamma` yields the sine atom in the theorem.  The existing regular
series is summable; splitting its sum index into zero and successor upper rows,
then pairing successor upper with lower, transports summability and identifies
the paired `tsum` with the actual finite-part imaginary channel.

Differentiating each sine atom gives the slope atom times
`cos(gamma log r)`.  For `0<sigma<1`, both powers of `r` are at most one, so the
power difference has absolute value at most two.  Since
`log r <= d/N`, the derivative is bounded by `2 d h_x(d)/N^2`, whose double
series converges.  The Weierstrass derivative theorem therefore identifies the
derivative of the complete phase series.

At `gamma=0`, `cos 0=1`.  Strict monotonicity of real powers for `r>1` shows

`r^(sigma-1) - r^(-sigma)`

has strict sign `sigma-1/2` atom by atom.  A summable series of strictly
same-signed atoms retains that strict sign.  Nonzero derivative at a zero gives
punctured local nonvanishing; convergence of secant slopes gives the sharper
oriented quotient law.

## Formal theorem package

- `reflectedBiHeatUpperSucc_add_lower_im_eq_mixedPhaseAtom`
- `summable_reflectedBiHeatFinitePartMixedPhaseAtom`
- `reflectedBiHeatFinitePart_vertical_im_eq_mixedPhase`
- `summable_reflectedBiHeatFinitePartMixedSlopeMajorant`
- `abs_reflectedBiHeatFinitePartMixedSlopeAtom_le`
- `reflectedBiHeatFinitePartMixedSlopeAtom_pos_of_half_lt`
- `reflectedBiHeatFinitePartMixedSlopeAtom_neg_of_lt_half`
- `reflectedBiHeatFinitePartMixedSlope_pos_of_half_lt`
- `reflectedBiHeatFinitePartMixedSlope_neg_of_lt_half`
- `reflectedBiHeatFinitePartMixedSlope_eq_zero_iff`
- `hasDerivAt_reflectedBiHeatFinitePartMixedPhase`
- `hasDerivAt_reflectedBiHeatFinitePart_vertical_im_zero`
- `eventually_reflectedBiHeatFinitePart_vertical_im_ne_zero`
- `eventually_reflectedBiHeatFinitePart_vertical_im_div_pos_of_half_lt`
- `eventually_reflectedBiHeatFinitePart_vertical_im_div_neg_of_lt_half`

## Provisional literature audit

Searches through August 2026 checked primary sources on Gaussian-weighted double
Dirichlet series, theta/heat-kernel regularization, critical-line derivatives,
and log-derivative positivity.  Located work concerns different double
Dirichlet series, generic heat regularization, or conditional zeta derivative
bounds; no exact complementary-order additive-heat pairing, paired sine
expansion, or signed canonical finite-part transversality theorem was found.
Priority remains provisional pending expert review.

## New exact insight

The real-axis branch exposed by the Klein-four no-go is a simple, oriented
zero of the canonical wall-odd channel at every off-wall strip coordinate.  It
is not an accidental cancellation: its first height jet is nonzero and has
exact horizontal orientation `sign(sigma-1/2)`.

This closes the local source-transversality burden at neutral height.  Remaining
RBH producer burden is genuinely global: exclude additional phase zeros at the
nonzero heights occurring on actual Xi divisor support, or propagate this local
orientation along height without crossing another zero.  The present theorem
does not assert that global step.

## Audit

- Module:
  `GaloisForLFunctions.RHTower.ReflectedBiHeatThetaFinitePartNeutralHeightTransversality`
- Direct `lake env lean` check passed.
- Targeted `lake build` passed.
- Axiom audit passed: only `propext`, `Classical.choice`, and `Quot.sound`.
- Umbrella import wired.
- Full umbrella build intentionally not run.

## Log

- 2026-08-27 — conjectured from corpus row pairing and Klein-four zero cross.
- 2026-08-27 — exact phase expansion, derivative M-test, strict slope
  classification, punctured nonvanishing, and oriented crossing formalized.
