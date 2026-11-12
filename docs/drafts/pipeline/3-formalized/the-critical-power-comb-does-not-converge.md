# The critical power comb diverges and measures the zero width

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Target:** A82; the previously excluded parameter `a=1/2`.
- **Statements:** `¬ PowerCombTailConverges (1/2)` and, for every real `σ`,
  `StrictNaturalPowerGrowth (powerCombTail (1/2)) σ ↔ zetaZeroWidth ≤ σ`.

## Finite parts and forced drift

The critical archimedean jet is
`1/(√t(1+√t)) + 1/(√t(1+t))`, decreasing on `(0,1]`.
Its mesh error is at most `4/√N`; its row error is at most
`5/(2(N+1))+4/√(N+1)`. Harmonic weighting makes the row error summable.

The power-prefix finite-part error is `O(X^-a)` at every real cutoff
`X≥1`, for `0<a<1`. Subtracting `Re ζ(1/2)/t` from the critical reference
profile therefore leaves an integrable profile with convergent meshes.
The removed mesh is exactly `Re ζ(1/2) H_N`.

Consequently the critical comb equals a convergent elementary remainder
minus twice `contacts(N)-C H_N`. Central ξ symmetry and the Gamma row give
`C=-ζ′/ζ(1/2)-ζ(1/2)`: harmonic subtraction removes the actual real pole.

## Ordinary divergence

Convergence would give a holomorphic restored contact transform on
`Re s>0` and zero residues at nonzero boundary frequencies. Its actual
symbol is `ζ(s+1)(-ζ′/ζ(s+1/2)-ζ(s+1/2))`.

Every zero with `Re ρ≥1/2` supplies a nonzero interior or boundary residue:
`ζ(ρ+1/2)` lies in the zero-free closed outer half-plane. Unconditional
zero existence and reflection supply such a zero, contradicting convergence.

## Exact positive survivor

Convolution by `n⁻¹` preserves every strict nonnegative growth threshold.
Removing the remaining `n⁻¹ᐟ²` weight identifies critical contact growth
with the square-root prime-error criterion. Harmonic subtraction and the
convergent elementary remainder preserve that criterion.

Thus the literal critical comb has strict growth threshold `σ` exactly
when `zetaZeroWidth≤σ`. Negative thresholds would force convergence to zero
and are excluded by ordinary divergence. In particular, every positive
power bounds the critical comb exactly under RH.

## Lean declarations

- `not_powerCombTailConverges_half` in `TheCriticalPowerCombDoesNotConverge`.
- `strictGrowth_criticalPowerCombTail_iff_zeroWidth` in `CriticalPowerCombGrowthDetectsRH`.
- `strictGrowth_criticalPowerCombTail_iff_rh`.
- `powerCombTail_half_eq_elementary_sub_contacts` and
  `tendsto_criticalPowerCombElementaryRemainder`.

Both capstones and all supports passed `lake --old env lean`; umbrella wired.
No stronger Abel conclusion is claimed here.
[Critical Abel integrability and its finite limit](../1-in-progress/critical-power-comb-abel-integrability-detects-rh.md)
remain a separate candidate.
