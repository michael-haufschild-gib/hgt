# Prime Gamma–Bockstein/Rees event germ and cofinal normal nonuniformity law — Lean certificate

- **ID:** `cmr-prime-gamma-bockstein-rees-event-germ-cofinal-normal-nonuniformity-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `prime-gamma-bockstein-rees-event-germ-and-cofinal-normal-nonuniformity-law.md`
  (same directory).
- **Status:** `[UNCONDITIONAL]` `[NO SORRY / NO AXIOM / NO PROP INTERFACE]`

## Lean module

`formal/GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/PrimeGammaReesEventGerm.lean`,
namespace `HTGeometry.ConstraintMotiveRelativity`, imported by `GaloisForLFunctions.HTGeometry`.

Per §9 of the card, the module introduces a **new** analytic extension (`eventGerm`) and does not
touch the existing zero-radical coordinate in
`RHTower/PrimeGammaBocksteinReesCoronaComparison.lean`.

## Formal statement chain

### §2–§3 — the two coordinates and the event germ

1. `sinhc`, `sinhc_zero`, `sinhc_mul`, **`sinhc_pos`** — the entire even extension of
   `sinh x / x`, with value `1` at the origin and everywhere positive.
2. `fisherDensity` — `(GBR.1)`; `gammaTransgression` — `(GBR.2)`; `reesSlope`, `reesWeight` —
   `(GBR.5)`; `eventConstant` — `(GBR.6)`; `eventGerm`, `eventGerm_zero` — `(GBR.7)` with the
   removable value `L_p` at the event.
3. **`eventGerm_pos`** — the comparison factor is positive on the whole real grade line.
4. `rpow_sub_rpow_eq_sinh` — `p^{-t} - p^{t} = -2 sinh(t log p)`.
5. **`eventConstant_mul_reesSlope`** — the algebraic core: `L_p κ_p = 2 F_p log p`.
6. **`gammaTransgression_eq`** — Theorem 3.1, `(GBR.8)`: `β_p(t) = -g̃_p(t) w_p(t)` for every real
   `t`, including the event.  The two coordinates therefore have the same zero, and their raw
   coorientations differ exactly by the displayed reflection-odd minus.
7. **`event_derivative`** — Corollary 3.2, `(GBR.9)`: both coordinates have a simple zero at
   `t = 0` with `β'_p(0) = -L_p w'_p(0)`; the comparison identifies transverse derivatives.

### §4 — the normalization discontinuity

8. **`eventConstant_two_lt`** — Proposition 4.1, `(GBR.10)`: `L₂ < 2/3`, hence `L₂ ≠ 1`, so the
   piecewise factor that assigns the value `1` at the event is discontinuous there.  The bound uses
   `Real.log_two_lt_d9`.

### §5 — cofinal normal nonuniformity

9. `log_le_two_sqrt`, `log_sq_le`, **`eventConstant_le_32`**, `eventConstant_pos` — the comparison
   constants are positive and uniformly bounded.
10. **`tendsto_eventConstant_zero`** — Theorem 5.1, `(GBR.11)`: `L_p → 0`, by the squeeze
    `L_n ≤ 8 (log n)²/n` and `Real.tendsto_pow_log_div_mul_add_atTop`.
11. `diagCoef`, `norm_diagCoef`, `diagCoef_ne_zero`, `norm_diagCoef_le`, `memℓp_diagMul`,
    `norm_diagMul_le`, **`diagCompare`** — `(GBR.12)`: the diagonal comparison map on the prime
    source chart `ℓ²(P)`, bounded with norm at most `32`.
12. **`diagCompare_injective`**, `norm_diagCompare_srcBasis`, `norm_srcBasis` — it is injective, and
    it sends the coordinate vector at `p` to a vector of norm exactly `L_p`.
13. **`no_uniform_inverse_diagCompare`** — Corollary 5.2: no constant `C` satisfies
    `‖x‖ ≤ C ‖D_L x‖`, since `1 ≤ C L_p` fails for large primes.
14. **`range_diagCompare_not_closed`** — Corollary 5.2: the range is not closed.  A closed range
    would be complete, and the open mapping theorem (`ContinuousLinearEquiv.ofBijective` on the
    corestriction) would supply the uniform inverse just excluded.

## Verification

```
lake env lean GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/PrimeGammaReesEventGerm.lean
lake build GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.PrimeGammaReesEventGerm
```

Green with no warnings.  `#print axioms` on `sinhc_pos`, `eventGerm_pos`,
`eventConstant_mul_reesSlope`, `gammaTransgression_eq`, `event_derivative`,
`eventConstant_two_lt`, `eventConstant_le_32`, `tendsto_eventConstant_zero`,
`diagCompare_injective`, `norm_diagCompare_srcBasis`, `no_uniform_inverse_diagCompare` and
`range_diagCompare_not_closed` reports only `propext`, `Classical.choice`, `Quot.sound`.

## Scope notes

The card's `(GBR.3)`–`(GBR.4)` (the BV masses, Wold clocks and their alternating connection
coefficient) enter only through the resulting slope `κ_p`, which the module takes as the definition
`reesSlope`; that is exactly `(GBR.5)`, and the arithmetic that produces it from `(GBR.3)`–`(GBR.4)`
is one line of algebra recorded in the paper card.

Theorem 5.1's asymptotic equivalence `L_p ~ 2(log p)²/p` is recorded through the bound
`L_n ≤ 8(log n)²/n` together with `L_n → 0`, which is what Corollary 5.2 and the card's conclusions
use; the exact ratio limit adds no further consequence in the card.

The `ℓ^∞` and `c₀` cases of Corollary 5.2 are the same statement about the same coefficient
sequence: the obstruction is `1 ≤ C L_p` with `L_p → 0`, which is
`no_uniform_inverse_diagCompare`'s content and does not depend on the ambient sequence space.  The
closed-range half is proved in the Hilbert chart, where the card states it.

§§6–8 are programme meaning and hostile-loop bookkeeping and claim no further theorem.
