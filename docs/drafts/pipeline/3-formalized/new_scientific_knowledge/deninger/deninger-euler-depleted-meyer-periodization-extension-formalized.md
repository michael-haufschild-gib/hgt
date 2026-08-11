# Euler-depleted Meyer periodization extension — formalization certificate

- **ID:** `deninger-euler-depleted-meyer-periodization-extension-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `deninger-euler-depleted-meyer-periodization-extension.md` (same directory)
- **Label:** `DAC_DENINGER_EULER_DEPLETED_MEYER_PERIODIZATION_EXTENSION`

## Lean modules

All under `formal/GaloisForLFunctions/RHTower/`, all imported by `GaloisForLFunctions.RHTower`.

| Module | Content |
|---|---|
| `DeningerPeriodCutoff` | the bump adapted to a period |
| `DeningerPeriodizationSmooth` | `Per_L h` is `C^∞` and lies in `C^∞(ℝ/Lℤ)` |
| `DeningerPeriodizationMap` | `Per_L` as a linear map; `ker Per_L = Δ_L H_-` |
| `DeningerPartitionBump` | compactly supported smooth functions lie in `H_-`; the periodized bump is positive |
| `DeningerPeriodizationSplit` | the partition of unity, the section `s_χ`, surjectivity |
| `DeningerDepletedQuotient` | `M_ζ`, `M_ζ^{(p)}`, `ι_p`, `Per̄_p`, exactness |
| `DeningerPeriodizationBounded` | `(Per_L h)^{(r)} = Per_L(h^{(r)})`; `Per_L` bounded |
| `DeningerSplitBounded` | the `C^r` seminorms of the circle; `s_χ` bounded |
| `DeningerCircleTopology` | `DeningerCircle`, `withSeminorms`, both arrows continuous |
| `DeningerNuclearPullback` | nuclearity pulls back along a surjection |
| `DeningerMeyerOscillator` | the restricted oscillator family is nuclear |
| `DeningerExpWeightDeriv` | Leibniz bounds for an exponential weight |
| `DeningerBoundedMultiplier` | multipliers with bounded derivatives |
| `DeningerSechMultiplier` | `1/(2\cosh Kt)` is such a multiplier |
| `DeningerTwoSidedWeight` | `w_K` is an automorphism; the two-sided oscillator family is nuclear |
| `DeningerTwoSidedSchwartzBound` | Schwartz seminorms of `w_K h` ≤ Meyer seminorms |
| `DeningerSechDecay` | `‖u^{(j)}‖ ≤ C_j u` and `e^{K|t|}u ≤ 1` |
| `DeningerMeyerFromTwoSided` | Meyer weights ≤ derivatives of `w_K h` |
| `DeningerMeyerOscDomination` | `sup_s q ≤ C·Q_m(w_A ·)` |
| `DeningerOscMeyerDomination` | `Q_m(w_K ·) ≤ C·sup_s q` |
| `DeningerMeyerNuclear` | **`H_-` is nuclear**; every quotient is nuclear |

## Formal theorem chain

1. `deningerEulerDepletion` — `(3)`, the Euler-depletion identity.
2. `deningerPeriodizationMem` — `Per_L h ∈ C^∞(ℝ/Lℤ)`.
3. `deningerPeriodizationMap_ker` — `(6)`, `im Δ_L = ker Per_L`.
4. `deningerGreenSum_telescope`, `deningerGreenSeries_expBound` — `(7)`, `(8)`.
5. `deningerPeriodizationMap_surjective`, `deningerPeriodizationSplit` — surjectivity and the section.
6. `deningerPeriodizationSequence_exact` — `(5)` as an exact sequence with a section.
7. `deningerPeriodizationLM_continuous`, `deningerSplitLM_continuous`,
   `deningerPeriodizationSequence_splitStrict` — `(5)` is **split strict**.
8. `deningerDepletedPoisson_injective` — `(9)`.
9. `DeningerMeyerQuotient`, `DeningerDepletedQuotient` — `(10)`.
10. `deningerIota`, `deningerPerBar` — `(11)`.
11. `deningerDepletedSequence_exact` — `(12)`.
12. `deningerIota_range_eq_perBar_ker` — `(13)`.
13. `deningerOnePrimeConservativity` — `(14)`.
14. `deningerDepletion`, `deningerDepletion_injective`, `deningerDepletion_conservativity` —
    `(15)`–`(17)`.
15. `deningerMeyerSup_isNuclearSpaceC` — **`H_-` is a nuclear space.**
16. `deningerMeyerQuotient_nuclear`, `deningerDepletedQuotient_nuclear` — `M_ζ` and `M_ζ^{(p)}`
    are nuclear.

## Proof mechanisms worth recording

- `Per_L h` is smooth although the lattice sum has **no** summable majorant on `ℝ`: cutting by a
  `ContDiffBump` equal to `1` on one period restores one, since `|t+jL| ≥ |j|L - R` there, and
  periodicity propagates smoothness to the line.
- Nuclearity is proved for the **finite suprema** of the `q_{A,n}`; the bare family is not directed,
  the same obstruction the Schwartz seminorms have.
- The comparison family must use the **two-sided** weight `w_K = e^{Kt}+e^{-Kt}`. The one-sided
  family is not directed in `k`, so `e^{A|t|} ≤ e^{At}+e^{-At}` could not be collapsed to one index.
- `w_K` is an automorphism of `H_-` because `1/w_K` is a bounded multiplier; that in turn rests on
  the closed ODE `v' = K^2 - v^2` for `v = w_K'/w_K`, which makes every `v^{(j)}` a polynomial in
  `v` with `|v| ≤ |K|`.
- The backward Leibniz bound is the forward one applied to the inverse weight — no inverse-Leibniz
  identity is needed.

## Verification

- Every module checks under `lake env lean GaloisForLFunctions/RHTower/<module>.lean` with no errors.
- `lake build GaloisForLFunctions.RHTower` completes 18675 jobs.
- `#print axioms` on every theorem above reports exactly `[propext, Classical.choice, Quot.sound]`.
- No `sorry`, `admit`, `axiom`, `opaque` or `unsafe` declaration in any module.
