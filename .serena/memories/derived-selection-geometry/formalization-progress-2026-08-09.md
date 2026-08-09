# derived-selection-geometry card: Lean formalization progress

Card: `docs/drafts/pipeline/2-fully-proven/derived-selection-geometry/universal-monodromy-cartier-torsion-fitting-energy-law.md`
(one card only in the folder). Target: full stage-3 promotion.

Lean home: `formal/GaloisForLFunctions/HTGeometry/DerivedSelectionGeometry/`
Namespace: `GaloisForLFunctions.HTGeometry.DerivedSelection`

## Modules built and CLEAN (`lake env lean` silent)

| module | card content |
|---|---|
| `IdentityWall.lean` | R=k[q,q⁻¹], I=(q-1), `evalOne`, `ker_evalOne`, `identityFibreEquiv : R/I ≃ₐ[k] k`, `monodromyRefl`, `monodromyRefl_wallEquation`, `portCofactor`, `wallEquation_mul_portCofactor`, `evalOne_portCofactor = M` |
| `TwoPathIncompatibility.lean` | §2–3 (3.1)(3.3)(3.4): defect closed forms, `minStableBoundary_eq = wallSquare`, `range_wallSmul`, `incompatEquiv : Q ≅ (R/I)²`, `annihilator_incompatModule = I` |
| `SourceOrientation.lean` | §4A (4A.4)(4A.6)(4A.11): `srcBoundary_eq_ker_coordSum`, `srcIncompatEquiv : Q_src ≅ R/I`, `annihilator_srcIncompatModule`, `ker_coordSumQuot = range antidiagonal`, `exists_srcData` |
| `RegularReaderExclusion.lean` | (4.1)+(4A.8) Hom vanishing into torsion-free readers |
| `ReflectionEnergy.lean` | §5.1/5.2/5.3 global: `mul_reflEnergy`, `reflEnergy_eq`, `mul_ambiCurvature_sq` (5.8), `ambiCurvature_sub_two_wall` (5.9), `span_reflEnergy_eq` ((E)=I²), `monodromyRefl_energy`, `toCotangent_monodromyRefl_wall` (σ = −1 on I/I²) |
| `FibreDichotomy.lean` | Cor 4.2 (4.4) field dichotomy; §7 (7.2); Cor 8A.3 arithmetic `riemannSpecial_eq_one_iff` |
| `ExteriorResponse.lean` | §6 Thm 6.1 (radical = 0⊕ker ΛS, port bound, two-leg inseparability) and Thm 6.2 (|c|√N sharp, `graph_mem_closure`, `not_continuous`) |
| `FittingPresentation.lean` | NEW INFRA: `presDetIdeal`, `extendGen`, `borderMat`/`det_borderMat`, `liftMat`/`det_liftMat`, `presDetIdeal_extendGen` |
| `FittingInvariance.lean` | NEW INFRA: `reindexGen`, `addGens`+closed form, `presDetIdeal_eq_of_surjective`, **`fittingIdealZero`** + `fittingIdealZero_eq_presDetIdeal` (mathlib has NO Fitting ideals) |
| `FittingEnergy.lean` | (3.2)(4A.7)(4A.12)(5.3): `fittingIdealZero_quotient = I`, `fittingIdealZero_quotient_sq = (t)²`, `fittingIdealZero_incompatModule`, `..._srcIncompatModule`, `..._eq_sq`, `span_monodromyEnergy_eq_fittingIdealZero` |
| `LocalPort.lean` | Cor 5.2/5.3 local: `identityIdeal_isMaximal`, `portCofactor_notMem_identityIdeal` (CharZero), `span_pow_sub_one_localized`, `span_energyPow_localized`, `span_curvature_localized` |

## Still TO DO

1. **Ext/Tor** (Thm 4.1 (4.2), Cor 4.2 (4.5), Thm 8A.1): `Ext¹_R(Q,R) ≅ Q`, `Tor₁^R(Q,R/I) ≅ k²`,
   `Lf*Q_src ≃ [A →^{u−1} A]` i.e. `H^{-1} = Ann_A(u−1)`, `H^0 = A/(u−1)`.
   mathlib: `CategoryTheory.Abelian.Ext` (LES available; used in RHTower/DeningerFlasqueAcyclic.lean),
   `CategoryTheory.Tor'` (left-derive in FIRST factor) + `ProjectiveResolution.isoLeftDerivedObj`.
2. **Associated graded** (Thm 5.4): mathlib has NO gr_I R. Options investigated: build
   `⨁ I^j/I^{j+1}` with DirectSum.GCommRing (heavy), or via `reesAlgebra I ⧸ I·Rees` (quotient ring
   gives multiplication free; for principal (t) with t regular, Rees ≅ R[Y] and gr ≅ (R/t)[Y] using
   `Ideal.polynomialQuotientEquivQuotientPolynomial`). Content: I^j/I^{j+1} ≅ k·e^j, σ(e)=−e,
   in_I(K)=2e, in_I(E)=e², in_I(q^M−1)=Me, in_I(E_M)=M²e².
3. **Thm 8A.2**: `End_R(Q_src) ≅ R/I` (8A.4) — concrete; plus support preservation (thick
   subcategory). Plan: formalize the module-level closure (annihilated by I ⇒ localizes to 0 away
   from H) + the three consequences via 8A.1.
4. Umbrella `DerivedSelectionGeometry.lean` + wire into `HTGeometry.lean`; `formal_tools.py index`;
   `formal_tools.py lint`; `#print axioms` audit; move card to `docs/drafts/pipeline/3-formalized/`.

## Lean traps hit

- `(Ideal.span s).prod (Ideal.span t)` elaborates to `Ideal.prod` (an `Ideal (R×R)`), NOT
  `Submodule R (R×R)`. Write `Submodule.prod (I : Ideal R) (J : Ideal R)`.
- Applying a general lemma to a quotient module times out at 200000 heartbeats unless module and
  ring element are given explicitly: `lemma (M := incompatModule q c) (t := q-1)`.
- `Function.Surjective fun x => c * eps x` blocks `rw`; state as `∀ r, ∃ x, c * eps x = r`.
- `Ideal.neg_mem` → use `Submodule.neg_mem`. `isUnit_of_mul_eq_one` does not exist.
- `ext x` on a `LinearMap` equality can pick `LinearMap.single`-style ext lemmas; use
  `refine LinearMap.ext fun x => ?_`.
- `Ideal.Quotient.mk I x = 0 ↔ x ∈ I` is `Ideal.Quotient.eq_zero_iff_mem`, NOT
  `Submodule.Quotient.mk_eq_zero`.
- `ring` fails on module goals (`-μ + μ = 0`); use `abel`.
- `MulEquiv.isField (hB : IsField B) (e : A ≃* B)` — field arg first.
- `Real.sqrt_atTop` does not exist; compose `Real.continuous_sqrt` with `tendsto_inv_atTop_zero`
  and unfold with `Function.comp_def`.
- Finset Cauchy–Schwarz is root-namespace `sq_sum_le_card_mul_sum_sq`.
