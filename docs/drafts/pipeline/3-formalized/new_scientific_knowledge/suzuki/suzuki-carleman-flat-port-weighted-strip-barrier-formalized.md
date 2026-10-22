# The flat Carleman port blocks every weighted strip, formalized

- **ID:** `suzuki-carleman-flat-port-weighted-strip-barrier`
- **Stage:** 3 — formalized in Lean 4
- **Claim:** `[PROVED HERE] [UNCONDITIONAL]`
- **Paper proof:** `./suzuki-carleman-flat-port-weighted-strip-barrier.md`
- **Lean:**
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCarlemanFlatPortProfile.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCarlemanFlatPortChart.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCarlemanFlatPortResponse.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCarlemanFlatPortAsymptotic.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCarlemanFlatPortBarrier.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCarlemanFlatPortGap.lean`

## Formal content

| Card | Lean |
|---|---|
| `(1)`–`(2)` the flat profile | `flatPortProfile`, `flatPortAntiderivative`, `hasDerivAt_flatPortAntiderivative` |
| `(3)` flatter than every root grade | `tendsto_sqrt_mul_flatPortProfile` |
| `(17)` exact tail integral | `integral_Ioi_flatPortProfile` = `2(√L+1)e^{-√L}` |
| `(14)` `L²` membership | `integrableOn_flatPortValueDensity` |
| `(4)`, `(12)`–`(13)` `H¹` failure | `flatPortDerivativeDensity`, `tendsto_flatPortDerivativeDensity`, `not_integrableOn_flatPortDerivativeDensity` |
| `(5)`, `(15)` log-chart response | `carlemanCutoffFactor`, `carlemanLogResponse`, `carlemanLogResponseLimit` |
| `(21)`, `(22)` logistic kernel | `logisticKernel`, `logisticPrimitive`, `hasDerivAt_logisticPrimitive`, `integral_logisticKernel` = `1` |
| `(20)` differentiation under the integral | `hasDerivAt_carlemanLogResponse` |
| `(19)`, `(23)`, `(24)` uniform ratio bound | `flatPortProfile_ratio_le` (`≤ e^{|y|/2}` for `L ≥ 4`), `abs_carlemanShiftedRatio_le` |
| `(7)` derivative asymptotic | `tendsto_carlemanLogResponseDeriv_div` |
| `(6)`, `(18)` endpoint gap | `carlemanLogResponse_gap_eq`, `tendsto_tail_integral_ratio`, `tendsto_carlemanLogResponse_gap` |
| `(8)`, `(25)` weighted strip barrier | `not_integrableOn_weighted_carlemanLogResponseDeriv` |

## What the card actually closes

The counterexample is now a Lean object, not a sketch.  The profile `F(L) = e^{-√L}` has an exact
closed antiderivative, so its tail integral is `2(√L+1)e^{-√L}` on the nose; in the physical chart
its square is integrable while the square of its spatial derivative is not, because
`L - 2√L - log L → ∞` — the profile sits in the completed boundary class and outside `H¹`.

The Carleman response in the logarithmic chart differentiates under the integral sign against the
`1/4` bound of the logistic kernel, and the resulting logistic average is compared to the profile
by one uniform estimate: `√L - √(L+y) ≤ |y|/2` once `L ≥ 4`, so the shifted ratio is dominated by
`e^{|y|/2}` while the kernel decays like `e^{-|y|}`.  Dominated convergence then gives the exact
rate `B'(L)/F(L) → 1`, and integrating that comparison over the ray gives the endpoint gap
`B_∞ - B(L) = 2√L F(L)(1+o(1))`.  Because `exp(2σL - 2√L) → ∞` for every `σ > 0`, the weighted
derivative is not square integrable on any ray: zero half-log trace, `L²` membership, Carleman
boundedness, and subtraction of the endpoint counterterm are jointly insufficient for a positive
Gamma strip.

## Hypotheses

Object data only: `σ > 0` for the weight, `L ≥ 4` for the uniform ratio bound, `L > 0` for the tail
integral, and the comparison scale `L₀` produced unconditionally by
`exists_carlemanDeriv_comparison`.  No RH, no spectral premise, no `sorry`, `axiom`, `opaque`, or
`unsafe`.  Every theorem named above audits to `[propext, Classical.choice, Quot.sound]`.

## Open boundary

The card's conclusion is a barrier, so what stays open is the coupled replacement `(27)`
`SUZUKI-CLOSED-TWO-PORT-RETURN` — exterior evaluation plus the completed zero equation plus both
zero half-log traces — and, beyond it, completed Evans injectivity and RH.
