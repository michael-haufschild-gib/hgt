# Suzuki, "Duality invariance of Faltings heights…" (arXiv:2504.04993) — Lean status

Card: `docs/drafts/pipeline/1-in-progress/suzuki-duality-faltings-heights-2504.04993.md`.

## What landed (all unconditional; axioms = propext/Classical.choice/Quot.sound)

New `formal/GaloisForLFunctions/HTGeometry/` modules (all wired into `HTGeometry.lean`):

1. `InvolutionTateCohomology.lean` — **Tate cohomology of an involution + the ℤ/2 Herbrand
   quotient**. Genuine mathlib gap: mathlib has no Tate cohomology and no Herbrand quotients.
   - `dlt σ = σ - 1`, `nrm σ = σ + 1`, `plusPart`, `minusPart`, `H0`, `H1`, `defect σ = Λ/(Λ⁺⊔Λ⁻)`.
   - `card_defect_mul_card_H1 : #defect · #Ĥ¹ = 2 ^ rk Λ⁻` (the exact sequence
     `0 → Λ/(Λ⁺⊕Λ⁻) --(σ-1)--> Λ⁻/2Λ⁻ → Ĥ¹ → 0`).
   - `herbrand : #Ĥ⁰ · 2^{rk Λ⁻} = #Ĥ¹ · 2^{rk Λ⁺}` — no hypothesis beyond involutivity.
   - `card_H0_eq_card_H1` (balanced case), `finrank_plusPart_add_finrank_minusPart`,
     finiteness of all three groups, and a balanced model `modelInvolution` on `ℤ × ℤ`.
2. `InvolutionTateDualLattice.lean` — **Tate duality for ℤ/2**: `card_H1_dual`, `card_H0_dual`,
   `card_defect_dual`. Two independent halves:
   - equal eigenranks via *injective restriction of functionals* `Λ^∨_± ↪ (Λ_±)^∨` plus rank
     additivity (avoids annihilator rank theory entirely);
   - equal defects via `Λ⁺ ⊔ Λ⁻ = (σ-1)⁻¹(2Λ)`, `defect ≅ image of σ-1 in Λ/2Λ`, and the mod-2
     evaluation pairing `Λ^∨/2Λ^∨ ≃ Dual_{𝔽₂}(Λ/2Λ)` intertwining `σ^∨-1` with `(σ-1)^T`, then
     `LinearMap.finrank_range_dualMap_eq_finrank_range`.
   This avoids Reiner's classification of ℤ[C₂]-lattices.
3. `RealTorusComponentGroup.lean` — `quotEquivTateH1 : A^σ/image(V^σ) ≅ Ĥ¹(⟨σ⟩,Λ)`
   (= Milne I.3.7, `π₀(A(ℝ)) ≅ Ĥ¹`). Works over any `CommRing R` with `Invertible (2:R)`.
4. `RealTorusDualPeriodComponents.lean` — `card_H1_eq_card_H1_neg_dualInvolution`:
   **`#π₀(A(ℝ)) = #π₀(B(ℝ))`**, Suzuki's final reduction in Prop 5.1.
5. `DualZLatticeCovolume.lean` — dual lattice for the standard pairing; `dual_span_eq`;
   `covolume_mul_covolume_dual : covol Λ · covol Λ* = 1`; matrix forms `rowLattice`,
   `dual_rowLattice`, `covolume_rowLattice`.
6. `ComplexTorusFaltingsPeriod.lean` — `norm_det_dzFrame = 2^g` (the `2^g` in `‖dz₁∧…∧dz_g‖²`);
   `faltingsNormSq_eq_sq_det_mul_dual` (the `det M`-scaling is an isometry).
7. `SelfInverseLatticeValuationRing.lean` — over a valuation ring, a rank-one lattice equal to its
   own inverse is the unit lattice (the named step in Prop 3.4).

## Out of reach (do not re-attempt without new foundations)
Néron models, Illusie's Lie complex + determinant of perfect complexes, fppf quotients
(Anantharaman 4.C), Raynaud group schemes, Chai's base change conductor, Suzuki's Tate–Shafarevich
group schemes, Breen–Serre duality, Serre duality on a complex torus. These block Thms 1.1/2.5,
Props 2.1–2.4, 3.1–3.3, Thm 3.5 and the assembly Thms 4.2, 5.2.

## Reusable Lean lessons from this build
- `Submodule.mkQ`/`Submodule.Quotient` over **ℤ** hits the `Quotient.module` vs
  `AddCommGroup.toIntModule` diamond. Fix: define composite maps *without* a type ascription
  (`def psi hσ := p.mkQ ∘ₗ f`), and prove kernels by `ext` + `Submodule.Quotient.mk_eq_zero`
  rather than `rw [LinearMap.ker_comp, Submodule.ker_mkQ]`.
- `Mathlib.LinearAlgebra.FreeModule.ModN` is the right home for `Λ/nΛ`: it carries a
  `Module (ZMod n)` instance, `ModN.basis`, `ModN.liftEquiv` (AddMonoidHom universal property) and
  `AddMonoidHom.toZModLinearMap` — use `ModN.liftEquiv` instead of `Submodule.liftQ` to avoid
  `isDefEq` timeouts.
- `Field (ZMod 2)` needs `Mathlib.Data.ZMod.Basic` + `Mathlib.FieldTheory.Finite.Basic` imported.
- `Module.finrank_linearMap_self ℤ ℤ M : finrank ℤ (Dual ℤ M) = finrank ℤ M`
  (in `Mathlib.LinearAlgebra.FreeModule.Finite.Matrix`).
