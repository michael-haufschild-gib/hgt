# Suzuki, "Duality invariance of Faltings heights…" (arXiv:2504.04993) — Lean status

Card: `docs/drafts/pipeline/1-in-progress/suzuki-duality-faltings-heights-2504.04993.md`.

## What landed (11 modules, unconditional; axioms = propext/Classical.choice/Quot.sound)

All in `formal/GaloisForLFunctions/HTGeometry/`, all wired into `HTGeometry.lean`:

1. `InvolutionTateCohomology.lean` — **Tate cohomology of an involution + the ℤ/2 Herbrand
   quotient** (mathlib gap). `dlt`, `nrm`, `plusPart`, `minusPart`, `H0`, `H1`,
   `defect σ = Λ/(Λ⁺⊔Λ⁻)`; `card_defect_mul_card_H1 : #defect·#Ĥ¹ = 2^{rk Λ⁻}`;
   `herbrand : #Ĥ⁰·2^{rk Λ⁻} = #Ĥ¹·2^{rk Λ⁺}`; `card_H0_eq_card_H1` (balanced);
   `finrank_plusPart_add_finrank_minusPart`; finiteness; balanced model `modelInvolution` on
   `ℤ × ℤ` with `#Ĥ⁰ = #Ĥ¹ = 2` (the two real components of `ℂ/(ℤ+ℤi)`).
2. `InvolutionTateDualLattice.lean` — **Tate duality for ℤ/2**: `card_H1_dual`, `card_H0_dual`,
   `card_defect_dual`. Equal eigenranks via injective restriction of functionals; equal defects via
   `Λ⁺ ⊔ Λ⁻ = (σ-1)⁻¹(2Λ)`, `defect ≅ im(σ-1) ⊆ Λ/2Λ`, the mod-2 evaluation pairing
   `Λ^∨/2Λ^∨ ≃ Dual_{𝔽₂}(Λ/2Λ)`, and rank-of-transpose.  Avoids Reiner's classification.
3. `RealTorusComponentGroup.lean` — `quotEquivTateH1 : A^σ/image(V^σ) ≅ Ĥ¹(⟨σ⟩,Λ)`.
4. `RealTorusDualPeriodComponents.lean` — `card_H1_eq_card_H1_neg_dualInvolution`:
   **`#π₀(A(ℝ)) = #π₀(B(ℝ))`**, Suzuki's final reduction in Prop 5.1.
5. `DualZLatticeCovolume.lean` — dual lattice, `dual_span_eq`,
   `covolume_mul_covolume_dual : covol Λ · covol Λ* = 1`, matrix forms.
6. `ComplexTorusFaltingsPeriod.lean` — `norm_det_dzFrame = 2^g`,
   `faltingsNormSq_eq_sq_det_mul_dual`.
7. `SelfInverseLatticeValuationRing.lean` — over a valuation ring a rank-one lattice equal to its
   own inverse is trivial (the named step of Prop 3.4).
8. `RealTorusEigenLatticeCovolume.lean` — `covolume_eigenSum : covol(Λ⁺⊕Λ⁻) = #defect·covol Λ`;
   `covolume_eigenSum_mul_card_H1` = Suzuki's `det Q = (2^g/#π₀)·det M`.
9. `RealTorusIdentityComponent.lean` — **topological** upgrade: `span_fixedLattice`,
   `isCompact_imageFixed`, `connectedComponent_eq` (image of `V^σ` *is* the identity component of
   `A(ℝ)`), `card_quotient_realPoints` (`#π₀ = #Ĥ¹` for the genuine π₀),
   `card_piZero_eq_card_H1_neg_dual`.
10. `HaarMeasureSubgroupIndex.lean` — `measure_univ_eq_index_mul : μ(G) = [G:H]·μ(H)`
    (mathlib gap).
11. `RealTorusRealPeriod.lean` — `measure_univ_realPoints : μ(A(ℝ)) = #Ĥ¹·μ(A(ℝ)⁰)`,
    Suzuki's `(5.1)` modulo the normalisation `∫_{A(ℝ)⁰} dz = 1`.

## Out of reach (do not re-attempt without new foundations)
Néron models, Illusie's Lie complex + determinants of perfect complexes, fppf quotients
(Anantharaman 4.C), Raynaud group schemes, Chai's base change conductor, Suzuki's Tate–Shafarevich
group schemes, Breen–Serre duality, Serre duality on a complex torus, integration of differential
forms over complex/real tori.  These block Thms 1.1/2.5, Props 2.1–2.4, 3.1–3.3, Thm 3.5, and the
assembly Thms 4.2, 5.2.

## Reusable Lean lessons
- `Submodule.mkQ`/`Submodule.Quotient` over **ℤ** hits the `Quotient.module` vs
  `AddCommGroup.toIntModule` diamond.  Define composite maps *without* a type ascription
  (`def psi hσ := p.mkQ ∘ₗ f`) and prove kernels by `ext` + `Submodule.Quotient.mk_eq_zero`
  instead of `rw [LinearMap.ker_comp, Submodule.ker_mkQ]`.
- `Mathlib.LinearAlgebra.FreeModule.ModN` is the home for `Λ/nΛ`: `Module (ZMod n)` instance,
  `ModN.basis`, `ModN.liftEquiv`, `AddMonoidHom.toZModLinearMap`.  Use `ModN.liftEquiv`, not
  `Submodule.liftQ`, to avoid `isDefEq` timeouts.
- `Field (ZMod 2)` needs `Mathlib.Data.ZMod.Basic` + `Mathlib.FieldTheory.Finite.Basic`.
- `Module.finrank_linearMap_self ℤ ℤ M : finrank ℤ (Dual ℤ M) = finrank ℤ M`
  (`Mathlib.LinearAlgebra.FreeModule.Finite.Matrix`).
- `AddSubgroup.isOpen_of_isClosed_of_finiteIndex` lives in
  `Mathlib.Topology.Algebra.Group.ClosedSubgroup`; `AddSubgroup.finiteIndex_of_finite_quotient`
  turns `Finite (G ⧸ H)` into the `FiniteIndex` instance.
- To lift a `Submodule.Quotient` to a *non-module* target, use `Quotient.lift` with
  `Submodule.quotientRel_def`.
