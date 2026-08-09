# Two-prime Kummer precision horizon and compact-repair no-go — Lean certificate

- **ID:** `two-prime-kummer-precision-horizon-and-compact-repair-no-go-formalized`
- **Stage:** 3-formalized
- **Type:** CERTIFICATE (Lean 4)
- **Paper proof:** `two-prime-kummer-precision-horizon-and-compact-repair-no-go.md`
- **Status:** `[LEAN-FORMALIZED] [UNCONDITIONAL]`

## Modules

| File | Contents |
|---|---|
| `HTGeometry/FiniteDiagonalOperator.lean` | general finite diagonal multiplier: smallest singular value, inverse norm, approximate left inverses |
| `RHTower/TwoPrimeKummerClockSeparation.lean` | the arithmetic clock separation, its elementary window, and injective mode families |
| `RHTower/TwoPrimeKummerPrecisionHorizon.lean` | §2 Thm 2.1, §3 Thm 3.1, §4 Thm 4.1 |
| `RHTower/DiagonalMultiplierSpectrum.lean` | spectrum and Weyl sequences of a general `ℓ²` diagonal multiplier |
| `RHTower/TwoPrimeKummerEssentialSpectrum.lean` | §5 Thm 5.1, §6 Thm 6.1 |

Namespaces `GaloisForLFunctions.HTGeometry` and `GaloisForLFunctions.RHTower`.

## Card statement to Lean name

| Card | Lean |
|---|---|
| general diagonal symbol and its extreme values | `diagOp`, `diagMin`, `diagMax`, `le_diagMin` |
| smallest singular value of a diagonal operator | `smallestSingularValue_diagOp`, `normalDiagOp_single` |
| inverse norm and approximate left inverses | `opNorm_diagOp_inv`, `le_opNorm_of_approxLeftInverse` |
| §1 two-prime clock frequency and the finite mode box | `kummerFreq`, `kummerBox`, `kummerFreq_injective` |
| §1 separation of two logarithms of integers | `inv_max_le_abs_log_sub_log`, `kummerFreq_lower_bound` |
| §3 the elementary window `3^{-N} ≤ d_N ≤ log 2 / ⌊N/2⌋` | `kummerSeparation_lower_bound`, `kummerSeparation_upper_bound`, `tendsto_kummerSeparation_zero` |
| §2 Thm 2.1 exact Kummer precision law | `kummerSymbol`, `diagMin_kummerSymbol`, `smallestSingularValue_kummerSection` |
| §3 Thm 3.1 horizon window and its collapse | `kummerSectionGap`, `kummerSectionGap_window`, `tendsto_kummerSectionGap_zero` |
| §4 Thm 4.1 approximate inverse uncertainty law | `opNorm_kummerSection_inv`, `le_opNorm_of_approxLeftInverse_kummerSection`, `tendsto_kummerSectionInverseCapacity_atTop` |
| general multiplier spectrum and Weyl sequences | `spectrum_deningerMultiplier`, `hasEigenvalue_deningerMultiplier`, `tendsto_weylSequence`, `tendsto_inner_lp_single_zero` |
| §5 Thm 5.1 the essential spectrum is a full interval | `kummerTransform`, `closure_range_kummerFullSymbol`, `spectrum_kummerTransform` |
| §6 Thm 6.1 compact corrections cannot close the horizon | `exists_singular_weylSequence`, `not_injective_and_isClosed_range_kummerTransform_add_compact` |

## Verification

Foreground per-file elaboration and a cached foreground `lake build` of the five modules pass.
The axiom audit of `tendsto_kummerSectionInverseCapacity_atTop` and
`not_injective_and_isClosed_range_kummerTransform_add_compact` reports only `propext`,
`Classical.choice`, `Quot.sound`.

The clock separation is elementary throughout: the lower bound is a sign analysis plus the integer
separation `1 / max(A,B) ≤ |log A − log B|`, and the upper bound is Dirichlet approximation of
`log 3 / log 2`.  No transcendence measure is used.

Remark 3.2 (the sharper Baker bound) is explicitly not used by any theorem of the card, and
Corollary 6.2 is a classification reading of Theorem 6.1; neither adds mathematical content.

## Boundary

The no-go says that no compact correction repairs the two-prime Kummer horizon.  It does not
exclude unbounded corrections, and it makes no statement about the zeros of any `L`-function.
