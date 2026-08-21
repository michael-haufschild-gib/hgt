# Group-scheme foundations for the Faltings-height duality theorems

- **ID:** gs-foundations-faltings
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) — infrastructure programme
- **Source:** required by `suzuki-duality-faltings-heights-2504.04993.md` (arXiv:2504.04993)
- **Statement:** Build, in Lean 4 and unconditionally, the algebraic-geometry stack that Sections 2
  and 3 of Suzuki's paper stand on, until Theorems 2.5 and 3.5 (and hence 1.1, 1.2, 4.2, 5.2)
  become provable.

## Why this card exists

Sections 4 and 5 of the paper are Lean-closed (see the companion card).  Every remaining statement
— Thm 1.1 = Thm 2.5, Props 2.1–2.4, Props 3.1–3.4, Thm 3.5, and the assembly Thms 4.2 and 5.2 —
needs objects that do not exist in mathlib.  This card holds the bottom-up build of those objects.

## Dependency tree of the paper's open statements

```
Thm 1.3 = Thm 4.2 + Thm 5.2      (metrized omega_A ≅ omega_B)
 |- Prop 4.1  DONE quantitative core; needs Serre duality for the transition factor ±det M
 |- Prop 5.1  DONE arithmetic core; needs form integration for the normalisation
 |- Thm 1.2 = Thm 3.5            (omega_A ≅ omega_B as line bundles on X)
      |- Prop 3.4
           |- semistable case  <- Prop 3.3 + [self-inverse lattice DONE]
           |    |- Prop 3.3    (det RLie N <-> (det RLie M)^{-1} as lattices)
           |         |- Prop 3.2  perfectness of the extended pairing <- Raynaud group schemes
           |         |- Prop 3.1  extension of the Cartier pairing to Neron models
           |         |             <- derived category of fppf sheaves, [Mil06 III C.10]
           |         |- Prop 2.2(2)(4)  det RLie N ≅ (det RLie M)^{-1}, Cartier duals
           |- general case <- Chai base change conductor, [OS23 Thm 1.2]   (EXTERNAL PAPER)
Thm 1.1 = Thm 2.5                (deg Lie A = deg Lie B)
 |- Prop 2.4 <- [GRS24 Thm 10.3]                                          (EXTERNAL PAPER)
 |- Prop 2.3 <- Prop 2.1 + deg on Pic of a curve
 |- Prop 2.1 <- Illusie's Lie-complex triangle + determinants of perfect complexes
 |- Suzuki20a Tate-Shafarevich duality + Breen-Serre duality              (EXTERNAL PAPER)
```

Three of the leaves are theorems of *other* papers (GRS24, OS23, Suz20a).  Formalising them is part
of the transitive closure and is tracked here as separate future layers.

## Brick order (bottom-up)

**L1 — affine commutative group schemes as commutative bialgebras/Hopf algebras.**
- [x] `L1.1` augmentation ideal, co-Lie module `omega_A = I/I^2`, the universal differential `d`
      with its Leibniz rule, point derivations, and `PointDerivation ≃ Hom_R(omega_A, R) = Lie A`
      → `HTGeometry/AffineGroupSchemeCoLie.lean`
- [x] `L1.2a` functoriality: `coLieMap (f : A →ₐc[R] B) : omega_A →ₗ omega_B` with `coLieMap_d`,
      the functor laws `coLieMap_id`, `coLieMap_comp`, and `Subsingleton (coLie R R)` (the trivial
      group scheme has zero Lie algebra)
- [x] `L1.5` **inversion acts by `-1` on the co-Lie module**: `d (S a) = - d a`, equivalently
      `S x + x ∈ I^2` for `x ∈ I` → `HTGeometry/HopfAntipodeCoLie.lean`
- [ ] `L1.2b` base change `omega_{A ⊗ S} ≅ omega_A ⊗ S`
- [x] `L1.7` **the co-Lie module is `e^* Ω¹`** → `HTGeometry/CoLieKaehler.lean`:
      `smul_coLie` (the `A`-action on `I/I²` is through the counit), `dDerivation`,
      `kaehlerToCoLie`, and **`coLieEquivKaehlerQuotient : I/I² ≅ Ω[A⁄R] / I·Ω[A⁄R]`** — this is
      exactly Suzuki's definition `omega_A = e^* Omega^1` matched with the construction of `L1.1`,
      and the entry point into `L4` (the cotangent complex)
- [ ] `L1.6` `omega` of a product: `omega_{A ⊗ B} ≅ omega_A ⊕ omega_B`
- [x] `L1.3` dual-numbers description `dualNumberEquiv : pointDerivations ≃ {f : A →ₐ R[e] | fst∘f = ε}`
- [x] `L1.4a` non-vacuity certificate: the group algebra `R[G]` of a finite abelian group is a
      finite free commutative Hopf algebra with nonzero augmentation ideal
      → `HTGeometry/GroupAlgebraCoLieExample.lean` (`Spec R[G] = D(G)`, e.g. `mu_n`)
- [x] `L1.4b` **`alpha_2 = Spec R[eps]` in characteristic 2** → `HTGeometry/AlphaTwoHopfAlgebra.lean`:
      the bialgebra structure with `eps` primitive (`epsTensor_sq` needs `2 = 0`), built with
      `DualNumber.lift` and `Bialgebra.ofAlgHom`, plus `Module.Free`/`Module.Finite`, and
      **`primitives_ne_bot`** — so `CartierDual.primitivesEquivCartierLie` is not a statement about
      zero modules

**L2 — Cartier duality.**
- [x] `L2.1a` **dual coalgebra of a finite free algebra** → `HTGeometry/DualCoalgebraFiniteFree.lean`
      (`dualComul`, `dualCounit`, `T2_dualComul`, `dual_coassoc`,
      `dual_rTensor_counit_comp_comul`, `dual_lTensor_counit_comp_comul`, `dualCoalgebra`)
- [x] `L2.1c` **`T2` is multiplicative on pure tensors** (`T2_tmul_convOf`) together with
      `convOf_apply_repr` — the last compatibility needed to see `A^dual` as a bialgebra
- [ ] `L2.1b` bundle the algebra structure on `Module.Dual R A` itself (mathlib has it only on
      the structure `WithConv (C →ₗ[R] A)`, so this is type-synonym bookkeeping)
- [x] `L2.2a` **bialgebra compatibility of the Cartier dual** → `HTGeometry/CartierDualLieAlgebra.lean`:
      `convOf` (convolution on the dual of any coalgebra), `convOf_comp_coalgHom`
      (functoriality — the engine), `T2_dualComul_conv` (`Δ'` is multiplicative, via mathlib's
      `Bialgebra.mulCoalgHom`), `dualCounit_conv`, `convOf_counit_left/right`,
      `T2_dualComul_counit`, `dualCounit_counit`
- [ ] `L2.2b` bundle these as a `Bialgebra`/`HopfAlgebra` structure on `A^dual`; `A^{dual dual} ≅ A`
      as a bialgebra
- [x] `L2.3a` `primitives R A : Submodule R A`, `counit_eq_zero_of_mem_primitives`,
      `primitives_le_augIdeal`
- [x] `L2.3b` **`Lie (Spec A^dual) ≅ Prim A`** → `primitivesEquivCartierLie`, together with
      `cartierPointDerivations`, `evalEquiv_mem_cartierPointDerivations_iff`, `eq_of_T2_tmul_eq`
- [ ] `L2.4` the canonical pairing `N x N^dual → Gm` and its perfectness

**L3 — determinants.**
- [x] `L3.1` **`exteriorPower.pairingDual` is an isomorphism for finite free modules**; the
      determinant line `det M = ⋀^{rank M} M` is free of rank one; `det (M^dual) ≅ (det M)^dual`
      canonically → `HTGeometry/DeterminantLine.lean`
- [ ] `L3.2` determinant of a two-term perfect complex; multiplicativity in exact sequences

**L4 — the Lie complex.**
- [ ] `L4.1` naive cotangent complex of a finite flat group scheme (mathlib has
      `Algebra.Extension.Cotangent` / `Algebra.H1Cotangent`)
- [ ] `L4.2` `RLie N` and `det RLie N`; Illusie VII 3.1.1.5 triangle → Prop 2.1

**L5 — Néron models.**  (largest layer; not started)

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  fully-proven on paper for each brick
- [ ] 2 → 3  formalized in Lean
- [ ] 3 → 4  publication-ready

## Log
- 2026-08-21 — card created; dependency tree frozen.  Bricks `L1.1`, `L1.2a`, `L1.3`, `L2.3a`
  landed in `HTGeometry/AffineGroupSchemeCoLie.lean` (wired into the HTGeometry umbrella, axiom
  audit clean).  Next brick: `L2.1`, the dual coalgebra of a finite free algebra —
  `comul' = (TensorProduct.dualDistribEquiv R A A).symm ∘ Dual.transpose (LinearMap.mul' R A)`,
  `counit' = evaluation at 1`; the work is coassociativity, to be proved by transporting along
  `dualDistribEquiv` and testing on pure tensors (`f (a*b*c)` on both sides).
- 2026-08-21 — brick `L2.1a` landed: `HTGeometry/DualCoalgebraFiniteFree.lean` proves all three
  coalgebra axioms for the linear dual of a finite free commutative algebra and bundles them as
  `dualCoalgebra` (a `@[reducible] def`, deliberately not a global instance).  The proof technique
  that worked: comparison equivalences `T2 : A'⊗A' ≃ (A⊗A)'`, `T3`, `T3L` built from
  `TensorProduct.dualDistribEquiv`, characterisation lemmas by `TensorProduct.induction_on`, and
  `TensorProduct.ext'` at the end.  Next brick: `L2.1b` / `L2.2` — the dual algebra structure on
  `Module.Dual R A` and the bialgebra compatibility, then `A^{∨∨} ≅ A`.
- 2026-08-21 — bricks `L2.2a` and `L2.3b` landed in `HTGeometry/CartierDualLieAlgebra.lean`:
  the convolution product on the dual of a coalgebra, its functoriality along coalgebra morphisms
  (the lemma that makes the bialgebra compatibility a one-liner via `Bialgebra.mulCoalgHom`), and
  **Cartier duality on Lie algebras**, `Lie (N^∨) ≅ Prim A`.  Next: `L1.4` (worked examples: the
  truncated polynomial Hopf algebra `R[X]/(X^p)` in characteristic `p`, giving `α_p` with
  `Prim ≠ 0`, and the group algebra `R[G]`), then `L3` determinants.
- 2026-08-21 — bricks `L3.1` and `L1.4a` landed: `HTGeometry/DeterminantLine.lean`
  (`pairingDual_bijective`, `pairingDualEquiv`, `detLine`, `finrank_detLine`, `detLineDualEquiv`)
  and `HTGeometry/GroupAlgebraCoLieExample.lean` (non-vacuity of the whole layer).
  Next: `L2.2b` — `T2` is a ring isomorphism from the tensor-square algebra `A^∨ ⊗ A^∨` to the
  convolution algebra `Dual (A ⊗ A)`, which upgrades the compatibility lemmas of `L2.2a` into a
  genuine `Bialgebra`/`HopfAlgebra` structure on the Cartier dual; then `L3.2` (determinant of a
  two-term perfect complex).
- 2026-08-21 — brick `L1.4b` landed (`alpha_2`).  Session total for this card: six modules
  (`AffineGroupSchemeCoLie`, `DualCoalgebraFiniteFree`, `CartierDualLieAlgebra`, `DeterminantLine`,
  `GroupAlgebraCoLieExample`, `AlphaTwoHopfAlgebra`), all wired, all axiom-clean.
  Remaining open bricks: `L1.2b` (base change of `omega`), `L2.1b`/`L2.2b` (bundling the Cartier
  dual as a Hopf algebra, `A^{dual dual} ≅ A`), `L2.4` (the Cartier pairing), `L3.2` (determinant of
  a perfect complex), all of `L4` (Lie complex) and all of `L5` (Neron models).
- 2026-08-21 — bricks `L1.5` (antipode acts by `-1`), `L2.1c` (`T2` multiplicative) and `L1.7`
  (**the co-Lie module is `e^* Omega^1`**) landed.  `L1.7` is the entry point into `L4`: mathlib's
  naive cotangent complex has `H^0 = Omega`, so the co-Lie complex `NL ⊗_A A/I` has
  `H^0 = omega_A` by `coLieEquivKaehlerQuotient` plus right-exactness of `⊗`.  For `L1.2b`, mathlib's
  `KaehlerDifferential.tensorKaehlerEquivBase` supplies the Kaehler half; what is still missing is a
  bialgebra structure on the base change `S ⊗_R A`.
