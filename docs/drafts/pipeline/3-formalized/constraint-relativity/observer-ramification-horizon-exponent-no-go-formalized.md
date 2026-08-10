# Observer ramification and horizon-exponent no-go — formalized

- **ID:** `observer-ramification-horizon-exponent-no-go-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `observer-ramification-horizon-exponent-no-go.md` (same directory)
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module | Path |
|---|---|
| `GaloisForLFunctions.HTGeometry.ConstraintRelativity.SincHorizonExponent` | `formal/GaloisForLFunctions/HTGeometry/ConstraintRelativity/SincHorizonExponent.lean` |

Wired into `GaloisForLFunctions.HTGeometry`.

## New infrastructure

Mathlib has the cubic lower bound `Real.sin_gt_sub_cube : x − x³/6 < sin x` but **not** the quintic
upper bound; its `Real.sin_bound` only gives the weaker constant `4/100·|x|⁵`, which yields
`19/150 x²` instead of the card's `19/120 x²`.  Two new bounds are therefore built here by
monotonicity arguments on `Ici 0`:

- `cos_le_quartic : cos x ≤ 1 − x²/2 + x⁴/24` (from mathlib's cubic sine bound);
- `sin_le_quintic : sin x ≤ x − x³/6 + x⁵/120` (from `cos_le_quartic`),

with the supporting derivative computations `hasDerivAt_cosQuartic`, `hasDerivAt_sinQuintic`.

## Formal theorem chain

All declarations live in namespace `HTGeometry.ConstraintRelativity`.

Theorem 1 — the observer-ramification exponent:

1. `exponent_ratio_tendsto` — the abstract limit: if the reporter and decoder logarithms are affine
   in a divergent scale with vanishing corrections, the ratio `log K / (−log e)` converges to the
   ratio of slopes.
2. `tendsto_log_abs_atBot` — `log|t| → −∞` as `t → 0`, `t ≠ 0`.
3. `observed_exponent_tendsto` — **card `(1)`–`(2)`**: the observed exponent is exactly `β/m`.
4. `observed_exponent_reporter_tendsto` — **card `(3)`**: composing the reporter with a power `r`
   rescales the observed exponent to `β/(m r)`, so the raw exponent is not intrinsic until
   normalized by the reporter ramification order.

Theorem 2 — the exact sinc square-root horizon:

5. `one_sub_sinc_le` — **card `(5)`, upper**: `1 − sin x / x ≤ x²/6`.
6. `le_one_sub_sinc` — **card `(5)`, lower**: `(19/120) x² ≤ 1 − sin x / x` for `0 < x ≤ 1`.
7. `sqrt_le_of_sinc` — **card `(6)`, lower**: `√(6y)/T ≤ |δ|`.
8. `le_sqrt_of_sinc` — **card `(6)`, upper**: `|δ| ≤ √(120y/19)/T`.
9. `one_sub_sinc_even` — the sinc defect is even, so the inversion loses the sign of `δ`: exponent
   `1/2` and sign loss occur entirely inside one fixed operator algebra, with no non-Morita event.

Theorem 2, the general power reporter:

10. `tendsto_abs_rpow_nhdsGT`, `powerReporter_exponent_tendsto`,
    `powerReporter_inverse_exponent_tendsto` — the generalization the card states at the end of
    Theorem 2: the fixed-theory reporter `q_r(t) = exp(−|t|^{2r})` has horizon exponent `2r` and
    inverse exponent `1/(2r)`, for every `r > 0`.  The slope input
    `(1 − e^{−u})/u → 1` is **reused** from `RHTower.CCMBoundaryStripTransfer`
    (`tendsto_one_sub_exp_neg_div`), not rebuilt.  Since every positive exponent occurs inside one
    fixed operator algebra, a rational exponent alone classifies no law-horizon singularity — which
    is the card's closing claim.

The card's "positive survivor" three-slot diagnostic and its physics consequences are definitional
and interpretive; the card itself records that only slot 3 is a theorem, and that is items 3–9
above.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstraintRelativity/SincHorizonExponent.lean  # clean
lake build GaloisForLFunctions.HTGeometry                                                   # green
```
