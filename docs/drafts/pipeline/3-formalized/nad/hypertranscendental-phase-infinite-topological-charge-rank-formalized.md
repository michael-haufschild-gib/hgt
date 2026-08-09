# Hypertranscendental scattering requires infinite active topological charge rank — formalized

- **ID:** `hypertranscendental-phase-infinite-topological-charge-rank-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `hypertranscendental-phase-infinite-topological-charge-rank.md`
- **Umbrella import:** `GaloisForLFunctions.HTGeometry`

## Lean modules

| Module | Content |
|---|---|
| `formal/GaloisForLFunctions/HTGeometry/RealExponentialPolynomial.lean` | exponential-polynomial spaces and block calculus |
| `formal/GaloisForLFunctions/HTGeometry/RealConstantCoefficientAnnihilator.lean` | constant-coefficient operator calculus and its solution space |
| `formal/GaloisForLFunctions/HTGeometry/AnseloneKorevaarTranslationRank.lean` | translation rank and the Anselone–Korevaar equivalence |
| `formal/GaloisForLFunctions/HTGeometry/EntireExponentialCompositionDA.lean` | `exp ∘ (differentially algebraic entire)` is differentially algebraic |
| `formal/GaloisForLFunctions/HTGeometry/ActiveChargeRankHypertranscendence.lean` | Theorems A and C |
| `formal/GaloisForLFunctions/HTGeometry/ChargeRankDressingExamples.lean` | the exact examples and the anti-converse |

All declarations live in the namespace `GaloisForLFunctions.HTGeometry`.

## Formal theorem chain

1. **Definitions.**  `realTranslate a f = fun x => f (x − a)`; `translationSpan f` is the
   `ℂ`-span of `Set.range fun a => realTranslate a f`, so `Module.finrank ℂ (translationSpan f)`
   is the translation rank `(1)`.  `BilinearChargeFactorization Φ N` is the existence of charge
   profiles `q : Fin N → ℝ → ℂ` and a form `Ω` with
   `Φ (x − y) = ∑ₐ ∑_b Ω a b · q a x · q b y`, i.e. `(2)`–`(3)`.

2. **Theorem A, `(4)`–`(5)`.**  `translationSpan_le_span_of_bilinearChargeKernel` — every
   translate lies in the span of the charge profiles.  Numerically,
   `finrank_translationSpan_le_of_bilinearChargeFactorization` gives
   `Module.finrank ℂ (translationSpan Φ) ≤ N`, and
   `finiteDimensional_translationSpan_of_bilinearChargeFactorization` records finiteness.

3. **Separating evaluations.**  `exists_eval_separating` — a finite-dimensional subspace of
   `ℝ → ℂ` is separated by finitely many point evaluations.  This makes the coordinate curve of
   the translate family continuous.

4. **Regularity.**  `differentiable_of_mem_translationSpan` — for continuous `f` of finite
   translation rank every member of `translationSpan f` is differentiable.  The proof integrates
   the coordinate curve: the differences `P − τ_ε P` of a primitive `P` of `f` lie in the span,
   are differentiable, and their coordinate vectors span the whole coordinate space because the
   coordinate curve is their derivative and a finite-dimensional subspace is closed.

5. **Closure under differentiation.**  `deriv_mem_translationSpan` — a finite-dimensional
   subspace of `ℝ → ℂ` is closed for pointwise convergence, so the difference quotients of a
   member converge inside it.  `contDiff_of_mem_translationSpan` bootstraps to `C^∞`.

6. **The annihilator, `(8)`.**  `exists_nonzero_realConstCoeffOp_of_finrank` — the jets of `f`
   then lie in a finite-dimensional space, hence satisfy a nonzero constant-coefficient linear
   relation `realConstCoeffOp L f = 0` with `L ≠ 0`.  Conversely
   `exists_nonzero_realConstCoeffOp_eq_zero_of_mem_expPolySpace` exhibits
   `∏ⱼ (X − λⱼ)^{1+deg Pⱼ}` for an exponential polynomial.

7. **Theorem B, `(6)`–`(7)`.**  `mem_expPolySpace_of_realConstCoeffOp_eq_zero` integrates the
   operator one root at a time, and `finiteDimensional_translationSpan_of_mem_expPolySpace` is the
   converse; together
   `mem_expPolySpace_iff_finiteDimensional_translationSpan` states
   `f ∈ expPolySpace ↔ FiniteDimensional ℂ (translationSpan f)` for continuous `f`.

8. **Differential algebraicity.**  `differentiallyAlgebraic_of_mem_expPolySpaceC` — every entire
   exponential polynomial is differentially algebraic; `differentiallyAlgebraic_cexp_comp` — the
   exponential of a differentially algebraic entire function is differentially algebraic;
   `eq_of_eqOn_real` — two entire functions agreeing on `ℝ` are equal.

8b. **Entire extension.**  `exists_entire_differentiallyAlgebraic_extension_of_finiteDimensional_translationSpan`
   — a continuous phase of finite translation rank extends from the real rapidity axis to an entire
   function of the complex rapidity which satisfies an algebraic differential equation.  This is the
   packaged form of Theorem B that Theorem C consumes.

9. **Theorem C, `(11)`.**  `not_finiteDimensional_translationSpan_of_hypertranscendental` — if
   `S` is entire, `S x = ε·exp(i Φ x)` for every real `x`, and `S` is hypertranscendental, then
   `translationSpan Φ` is infinite-dimensional.  Its source form,
   `not_bilinearChargeFactorization_of_hypertranscendental`, states
   `∀ N, ¬ BilinearChargeFactorization Φ N`.

10. **Example `(12)`.**  `finrank_translationSpan_phiJT` — for `κ ≠ 0` the flat-JT phase
    `phiJT κ = fun x => κ · sinh x` has translation rank exactly `2`.

11. **Examples `(13)`–`(14)`.**  `finrank_translationSpan_phiSpin_le` — the finite higher-spin
    dressing `phiSpin F α = fun x => ∑_{s ∈ F} α s · sinh (s·x)` has translation rank at most
    `2·|F|`; `realConstCoeffOp_phiSpin_eq_zero` together with `prod_XsqSubC_ne_zero` exhibits the
    nonzero annihilator `∏_{s ∈ F} (X² − s²)`.

12. **Anti-converse `(15)`.**  `not_mem_expPolySpace_phiCDD` and
    `not_finiteDimensional_translationSpan_phiCDD` — for `B > 1` the elementary CDD shell phase
    `phiCDD B = fun x => 4·arctan (sinh x / B)` has infinite translation rank.  Were it an
    exponential polynomial its derivative would extend to an entire function `E`, and
    `E z · (B² + sinh² z) = 4B·cosh z` would hold on `ℝ`, hence everywhere; evaluating at
    `cddPole B`, where `sinh` takes the value `i·B`, gives `0 = 4B·cosh (cddPole B)` while
    `cosh² − sinh² = 1` forces `cosh (cddPole B) ≠ 0`.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/RealExponentialPolynomial.lean
lake env lean GaloisForLFunctions/HTGeometry/RealConstantCoefficientAnnihilator.lean
lake env lean GaloisForLFunctions/HTGeometry/AnseloneKorevaarTranslationRank.lean
lake env lean GaloisForLFunctions/HTGeometry/EntireExponentialCompositionDA.lean
lake env lean GaloisForLFunctions/HTGeometry/ActiveChargeRankHypertranscendence.lean
lake env lean GaloisForLFunctions/HTGeometry/ChargeRankDressingExamples.lean
lake build GaloisForLFunctions.HTGeometry.ChargeRankDressingExamples
```

All six modules compile without error and are imported by the
`GaloisForLFunctions.HTGeometry` umbrella.  `#print axioms` on
`translationSpan_le_span_of_bilinearChargeKernel`,
`finrank_translationSpan_le_of_bilinearChargeFactorization`,
`mem_expPolySpace_iff_finiteDimensional_translationSpan`,
`exists_nonzero_realConstCoeffOp_of_finrank`,
`exists_nonzero_realConstCoeffOp_eq_zero_of_mem_expPolySpace`,
`contDiff_of_mem_translationSpan`, `differentiallyAlgebraic_cexp_comp`,
`not_finiteDimensional_translationSpan_of_hypertranscendental`,
`not_bilinearChargeFactorization_of_hypertranscendental`,
`finrank_translationSpan_phiJT`, `finrank_translationSpan_phiSpin_le`,
`realConstCoeffOp_phiSpin_eq_zero`, `prod_XsqSubC_ne_zero`,
`not_mem_expPolySpace_phiCDD` and `not_finiteDimensional_translationSpan_phiCDD`
reports exactly `propext`, `Classical.choice`, `Quot.sound`.

## Boundary

The formal surface is the source no-go itself.  It does not construct a countably gauged or
measure-valued topological path integral, and it does not assert that infinite translation rank
implies hypertranscendence — `not_finiteDimensional_translationSpan_phiCDD` is the formal proof
that the converse fails.
