# Centre PF54 from the paired low-height Gamma bound

- **Wall:** Σ72.
- **Stage:** 3-formalized.
- **Theorem:** The centre Taylor sequence of ξ is PF54; its first 55 reciprocal even coefficients are nonnegative.
- **Owner:** `SquareRootThreshold/EffectiveHorizons/LowHeightGammaPF54.lean`.

## Proof

Fix σ = 5/4. For t ≥ 14, put z = (σ + it)/2. Then
`t/2 ≤ |z| ≤ 101t/200`. The proved digamma estimate
`|ψ(z) − log z| ≤ 3/|z|`, together with
`log(101/100) ≤ 1/100`, `log 2 ≥ 69/100` and `log π ≥ 11/10`, gives
`Re Γℝ′/Γℝ(σ+it) ≤ (log t)/2 − 27/40`.
The two rational pole terms total at most `6/784 < 1/120`, so
`−Re ζ′/ζ(σ+it) ≤ (log t)/2 − 2/3 − Re ξ′/ξ(σ+it)`.

The three-four-one inequality and the existing real pole bound
`−ζ′/ζ(5/4) ≤ 4 − 1/5` imply
`4 Re ξ′/ξ(5/4+it) ≤ 12 + (5/2)log t + (log 2)/2 − 59/15`.
For t ≤ 16 the right side is at most `12 + 41/12`, using `log 2 < 7/10`.
For t ≤ 18 it is at most `12 + 47/12`, using `log 18 < 3`.

An off-line zero β+iγ and its distinct line-conjugate copy 1−β+iγ contribute
`1/(5/4−β) + 1/(1/4+β) = (3/2)/((3/4)²−(β−1/2)²)`
to `Re ξ′/ξ(5/4+iγ)`. All other paired terms are nonnegative.
This expression increases strictly with β > 1/2. At β = 11/12 its quadruple
is `108/7 > 12 + 41/12`; at β = 15/16 it is `1536/95 > 12 + 47/12`.
Thus β ≤ 11/12 through height 16 and β ≤ 15/16 through height 18.
Schwarz and critical-line reflection give depth bounds `5/12` and `7/16` respectively.

Every off-line zero already satisfies `γ² ≥ 431/2`.
The elementary cosine bound gives `1−cos(π/55) ≥ 162/100000`.
Split absolute heights into three bands:

| Height | Squared-height floor | Squared-depth ceiling |
|---|---|---|
| ≤ 16 | 431/2 | 25/144 |
| (16,18] | 256 | 49/256 |
| > 18 | 324 | 1/4 |

In each row, the height floor times `162/100000` exceeds twice the depth ceiling.
Consequently `cos(π/55)(γ²+(β−1/2)²) ≤ γ²−(β−1/2)²`.
Critical-line zeros satisfy this immediately. The existing cone theorem gives PF54;
the complementary-minor identity gives reciprocal coefficient signs through index 54.

## Novelty and boundary

Corpus supplies PF45, the height floor, a weaker logarithmic zero-free strip, and the paired
partial-fraction identity. The new estimate retains both resonant copies and the negative
Gamma constant on the only heights where PF54 can fail. No low critical-line zero,
sixth-moment quadrature certificate or numerical zero data enters.
All-order centre positivity remains equivalent to RH.

## Verification

Direct audit passed without warnings:

```text
cd formal
lake --old env lean GaloisForLFunctions/SquareRootThreshold/EffectiveHorizons/LowHeightGammaPF54.lean
```

`xiZeroCopy_depth_le_five_twelfths`, `xiZeroCopy_depth_le_seven_sixteenths`,
`xi_centre_pfSeq_fiftyFour` and `evenRecipCoeff_XiC_nonneg_of_le_fiftyFour`
all have exactly `[propext, Classical.choice, Quot.sound]` as transitive axioms.
Namespace: `GaloisForLFunctions.SquareRootThreshold`. Wired into its umbrella.
