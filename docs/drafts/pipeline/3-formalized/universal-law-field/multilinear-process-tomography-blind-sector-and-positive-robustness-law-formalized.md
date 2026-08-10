# Multilinear process tomography, blind sector, positive robustness — Lean certification

- **ID:** ULF-MPTB-1
- **Paper card:** `multilinear-process-tomography-blind-sector-and-positive-robustness-law.md`
- **Lean modules:** `GaloisForLFunctions.HTGeometry.ConstitutiveProcessTomography`,
  `…TomographyDimension`, `…TomographyPositivity`
- **Universal-law umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Model

A `k`-slot constitutive process is an element of the dual of `E₁ ⊗ ⋯ ⊗ E_k`, realised as
`Module.Dual K (PiTensorProduct K E)`; an instrument family is a subspace `U` of the tensor
product and the experimental record is `U.dualRestrict`.  Theorem 2.1 is then mathlib's
`Subspace.dualRestrict_ker_eq_dualAnnihilator` plus the finite-dimensional injectivity criterion.

The product-instrument case is the one that needed building.  The joint intervention space of a
product family is presented as the *range* of the slotwise inclusion
`PiTensorProduct.map (fun i => (V i).subtype)` rather than as a span, which makes the dimension
count a rank computation:

* the map is injective because over a field every inclusion `V i ↪ E i` splits
  (`LinearMap.exists_leftInverse_of_injective`), and a slotwise left inverse induces a left inverse
  of the tensor map through `PiTensorProduct.map_comp` and `PiTensorProduct.map_id`;
* the dimension of a finite tensor product is the product of the dimensions, read off
  `Basis.piTensorProduct` and `Fintype.card_pi`;
* the range is exactly the span of the product interventions, by `Submodule.map_span` applied to
  `PiTensorProduct.span_tprod_eq_top`.

The positivity clause is stated with a *uniform positivity constant* — `∀ x, c‖x‖² ≤ re ⟪W₀x,x⟫` —
rather than with `λ_min` symbolically.  `exists_uniform_positive` produces that constant as the
minimum of the quadratic form on the unit sphere, which in finite dimension is exactly the least
eigenvalue; carrying `c` through keeps the perturbation estimate free of any spectral
decomposition, and the whole argument is then Cauchy–Schwarz plus `‖Dx‖ ≤ ‖D‖‖x‖`.

## Certified declarations, by clause

| Clause | Lean |
|---|---|
| 2.1 (1)(2): record and blind sector | `constitutiveProcessRestriction_ker_eq_dualAnnihilator` |
| 2.1 (3): exact reconstruction iff spanning | `constitutiveProcessRestriction_injective_iff_eq_top` |
| 2.1 (4): nontrivial indistinguishable family | `constitutiveProcess_blindDirection_exists_iff_ne_top`, `constitutiveProcess_affineBlindFamily_sameRecord` |
| open-interior robustness, qualitative | `constitutiveOpenConstraint_blindDirection_persists` |
| (6): product span is the tensor product | `productInterventionSpace`, `productInterventionSpace_eq_span` |
| dimension of a tensor product | `finrank_piTensorProduct`, `finiteDimensional_piTensorProduct`, `piTensorProduct_map_injective`, `finrank_productInterventionSpace` |
| **(7): hidden constitutive dimension** | **`finrank_dualAnnihilator_productInterventionSpace`** |
| completeness criterion | `productInterventionSpace_eq_top_of_forall`, `productInterventionSpace_eq_top_iff` |
| quadratic-form calculus | `reApplyInnerSelf_add`, `reApplyInnerSelf_sub`, `abs_reApplyInnerSelf_le`, `continuous_reApplyInnerSelf` |
| least eigenvalue as a constant | `exists_uniform_positive` |
| **(8): positive robustness** | **`reApplyInnerSelf_pos_of_perturb`, `reApplyInnerSelf_pos_of_smul_perturb`** |
| distinctness and record equality | `perturb_ne`, `record_eq_of_blind` |
| **capstone** | **`interiorPositivity_blindDirection_persists`** |

## What the certification does and does not say

It says: the blind sector of any instrument family is the dual annihilator, exactly; a product
family's blind sector has dimension `∏ dim Eᵢ − ∏ dim Vᵢ`, exactly; and interior positivity cannot
remove a blind direction, since a whole interval of positive definite processes shares one record.

It does not construct a common process for two given proof routes, does not supply the positivity
or causal constraints of any particular application, and says nothing about RH.

## Verification

Targeted foreground `lake env lean` on both new modules green; umbrella
`GaloisForLFunctions.HTGeometry.UniversalLawField` green at 11 577 jobs; `#print axioms` on every
capstone reports only `propext`, `Classical.choice`, `Quot.sound`.
