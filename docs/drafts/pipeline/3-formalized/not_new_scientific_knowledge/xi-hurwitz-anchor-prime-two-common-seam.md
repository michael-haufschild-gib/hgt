# Xi Hurwitz anchor and prime flux have one first-prime seam

- **ID:** xi-hurwitz-anchor-prime-two-common-seam
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** cross-corpus value synthesis from canonical Hurwitz anchor transversality and orbitwise von Mangoldt first-coefficient extraction
- **Statement:** After explicit first-prime normalization, the reflected Hurwitz anchor-tail difference and the far-right all-prime flux difference converge to the same faithful FE--Schwarz seam charge.

## Theorem

For `Re s>0`, define the normalized canonical Hurwitz anchor tail

```text
A_r(s)
  = d_a^r continuedHzeta(s,1) / ((-1)^r (s)_r) - 1.
```

Then Lean proves unconditionally

```text
2^r A_r(s) -> 2^(-s).
```

For an open-strip point `rho`, put

```text
H_r(rho)
  = log(2) 2^r [A_r(conj rho) - A_r(1-rho)],

P_r(rho)
  = 2^r [infinitePrimeFlux(conj rho+r)
           - infinitePrimeFlux(1-rho+r)].
```

Both sequences converge to

```text
C_2(rho)
  = log(2) [2^(-conj rho) - 2^(-(1-rho))].
```

Consequently,

```text
H_r(rho) - P_r(rho) -> 0
```

for every open-strip point, without an Xi-zero or RH assumption.

## Proof

The canonical anchor formula gives

```text
d_a^r continuedHzeta(s,1)=(-1)^r (s)_r zeta(s+r).
```

The Pochhammer coefficient is nonzero in `Re s>0`, so `A_r(s)=zeta(s+r)-1`.  Twist the zeta
Dirichlet coefficients by `n^(-s)` and delete the unit coefficient.  The resulting L-series has
zero coefficients at `n=0,1` and first surviving coefficient `2^(-s)` at `n=2`.  Mathlib's
first-coefficient L-series asymptotic therefore gives

```text
2^r (zeta(s+r)-1) -> 2^(-s).
```

Taking the FE--Schwarz difference yields the Hurwitz limit.  The already formalized orbitwise
von Mangoldt theorem gives the prime-flux limit with exactly the same value.

## RH interface

The common charge is faithful:

```text
C_2(rho)=0 <-> Re rho=1/2.
```

Lean therefore also proves

```text
all Xi-indexed Hurwitz anchor first-prime seams tend to zero -> RH.
```

This corollary is a criterion, not an unconditional RH proof.  The unconditional content is the
common-seam value relation and the asymptotic equality of the two independently presented source
channels.

## Positive use

Any later argument which controls either channel can be transported to the other without another
continuation, density, or divisor-reconstruction theorem.  In particular:

```text
local canonical Hurwitz coefficients
  <-> first-prime FE--Schwarz seam
  <-> far-right all-prime logarithmic flux.
```

The remaining orientation theorem must force the common charge to vanish.  Orbit composition does
not do so: the associated multiplicative transport is an exact coboundary and cancels on every
forward--reverse loop.

The follow-up module `XiHurwitzAnchorPrimeTwoOrientationEnergy` removes any ambiguity about this
remaining assertion: all common charges vanish exactly when the already formalized scalar
Xi--Hurwitz orientation energy `E_Xi` is zero.  Thus this is not an additional gap beyond the
regular-Cauchy source-core sign.  Source-core nonnegativity would discharge the common seams
immediately; proving that sign remains open.

## Scientific status

`[NOT NEW SCIENTIFIC KNOWLEDGE]` The proof is a direct composition of the canonical Hurwitz anchor
formula, the standard first-coefficient asymptotic for absolutely convergent Dirichlet series, and
the existing first-prime source seam theorem.  Its value is the exact cross-interface and Lean
closure, not a new parent theorem.

## Lean surface

```text
anchorShiftedZetaCoeff
anchorShiftedZetaTailCoeff
tendsto_two_cpow_mul_riemannZeta_shift_sub_one
normalizedHurwitzAnchorTail
normalizedHurwitzAnchorTail_eq
tendsto_two_cpow_mul_normalizedHurwitzAnchorTail
xiHurwitzAnchorPrimeTwoSeam
tendsto_xiHurwitzAnchorPrimeTwoSeam
xiPrimeFluxPrimeTwoSeam
tendsto_xiPrimeFluxPrimeTwoSeam
tendsto_anchorPrimeTwoSeam_sub_primeFluxPrimeTwoSeam_zero
re_eq_half_of_xiHurwitzAnchorPrimeTwoSeam_tendsto_zero
XiHurwitzAnchorPrimeTwoSeamsVanish
riemannHypothesis_of_xiHurwitzAnchorPrimeTwoSeamsVanish
```

Module:

```text
GaloisForLFunctions.RHTower.XiHurwitzAnchorPrimeTwoSeam
```

## Gates

- [x] 0 -> 1: exact cross-channel value relation identified
- [x] 1 -> 2: complete proof from the anchor and first-coefficient formulas
- [x] 2 -> 3: formalized in Lean
- [ ] 3 -> 4: not a publication target by itself

## Verification

- [x] exact file typecheck
- [x] no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration
- [x] formal lint
- [x] generated index refresh

## Log

- 2026-07-13 -- formalized first-prime recovery from normalized Hurwitz anchor jets, identified its
  FE--Schwarz difference with the existing orbitwise prime-flux seam, and added the conditional RH
  corollary.
