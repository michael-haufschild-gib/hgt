# Finite-reporter admission, hyperbolic reduction, and composition law — Lean certificate

- **ID:** `cmr-finite-reporter-admission-hyperbolic-composition-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `finite-reporter-admission-hyperbolic-reduction-composition-law.md`
  (same directory).
- **Status:** `[UNCONDITIONAL]` `[NO SORRY / NO AXIOM / NO PROP INTERFACE]`

## Lean module

`formal/GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/FiniteReporterAdmission.lean`,
namespace `HTGeometry.ConstraintMotiveRelativity`, imported by `GaloisForLFunctions.HTGeometry`.

§5's prime-port instantiation is built on the corpus parent
`ConstraintMotiveRelativity/PrimeAugmentationCompletion.lean` (`lpEmb`, `augment`, `augIdeal`,
`augCLM`, `exists_small_spread_lp`, `exists_small_spread_top`,
`eq_zero_on_range_of_vanishing_on_augIdeal`), which is imported rather than re-derived.

## Formal statement chain

### §0 — separation infrastructure

1. **`exists_continuous_annihilator_of_notMem_closure`** — Hahn–Banach for subspaces: a point
   outside the closure of a subspace of a normed `ℂ`-space is separated from it by a continuous
   functional annihilating the subspace.  A real separating functional
   (`geometric_hahn_banach_closed_point`) is bounded above on the subspace, hence vanishes on it by
   scaling, and `StrongDual.extendRCLike` carries both properties to `ℂ`.  Mathlib has only the
   algebraic (`Submodule.exists_dual_map_eq_bot_of_notMem`) and the geometric point/convex-set
   versions; this subspace form is new here.

### §1 — setup

2. `restrictAlong`, `restrictAlong_apply` — restriction of a continuous reporter along
   `j : X₀ →ₗ[ℂ] X`.
3. **`restrictAlong_injective`** — the continuous extension is unique when `j` has dense range.
4. **`admitted`** — `(FR.3)`: the admitted reporter subspace `L_X = L ⊓ range(res_j)`, with
   `mem_admitted_iff` and `admitted_le`.
5. `contAnnihilator`, `mem_contAnnihilator` — the continuous annihilator `S^⊥_X ⊆ X'`.

### §2 — the finite-reporter admission theorem

6. **`dualAnnihilator_dualCoannihilator`** — `(FR.15)`: `I^⊥ = L` for finite-dimensional `L`.
7. `apply_eq_zero_of_mem_dualCoannihilator` and **`closure_map_dualCoannihilator`** — `(FR.4)`:
   `closure(j(I)) = {x : ∀ φ ∈ X' with φ∘j ∈ L, φ x = 0}`, that is the joint kernel of the admitted
   reporters.  The nontrivial inclusion is item 1 plus `(FR.15)`.
8. `restrictAlong_mem_admitted`, **`exists_contAnnihilator_of_mem_admitted`**, **`resEquiv`** —
   `(FR.6)`: restriction along a dense `j` is a linear isomorphism
   `closure(j(I))^⊥_X ≅ L_X`.
9. **`algQuotEquiv`** — `(FR.7)`: `X₀/I ≅ L^∨`.
10. **`topologicalClosure_eq_ker_contAnnihilator`** — the bipolar theorem for subspaces of `X`.
11. `evalCont`, `evalCont_apply`, **`ker_evalCont`** — `(FR.16)`: the evaluation `E_X` and its
    kernel, the completed constraint.
12. `contAnnihilatorAlg`, `contAnnihilatorAlgEquiv`, **`dualCoannihilator_contAnnihilatorAlg`**,
    `evalCont_eq`, **`evalCont_surjective`** — `E_X` is onto whenever the continuous annihilator is
    finite dimensional, via mathlib's nondegenerate quotient pairing
    `Submodule.quotDualCoannihilatorToDual`.
13. **`completedQuotEquiv`** — `(FR.5)`: `X/closure(j(I)) ≅ L_X^∨`.

### §2 — the Chu mate

14. `admittedIn`, **`iotaX`** `(FR.9)`, **`rhoX`** `(FR.8)`, **`chu_compatibility`** `(FR.10)`,
    `range_iotaX`.
15. **`kerRhoEquiv`** and `kerRhoEquiv_apply` — `(FR.11)`, `(FR.14a)`: `ker ρ_X ≅ (L/L_X)^∨` by the
    perfect pairing `⟨ξ,[λ]⟩ = ξ(λ)`.
16. **`cokerIotaEquiv`** — `(FR.11)`: `coker ι_X ≅ L/L_X`.
17. **`admittedIn_eq_top_iff`**, **`unique_loss_iff`** — the transition is invertible exactly when
    `L_X = L`.

### §3 — hyperbolic doubles and the two reductions

18. `hyperbolicPairing`, `cotangentForm` — `(FR.11a)`, with `hyperbolicPairing_comm`,
    `cotangentForm_antisymm`, `cotangentForm_self`, `hyperbolicPairing_sub_cotangentForm`.
19. `constraintIsotropic`, **`constraintIsotropic_isotropic`**, `formOrth`, `mem_formOrth`,
    **`formOrth_constraintIsotropic`** — `I^ω = X₀ ⊕ I^⊥`.
20. `reductionMap`, **`ker_reductionMap`**, **`reductionMap_surjOn`** — the reduction of the
    cotangent double is onto `(V/I) ⊕ I^⊥` with kernel exactly the constraint.
21. **`contAnnihilator_topologicalClosure`**, `contCotangentForm`, `contCotangentForm_antisymm`,
    `contConstraintIsotropic`, `contFormOrth`, **`contFormOrth_contConstraintIsotropic`** — the
    same statements in the continuous double `X ⊕ X'`: `N^ω = X ⊕ N^⊥_X`.
22. **`algReductionEquiv`** — `(FR.12)`: `Red₀(I) ≅ ℍ(L^∨)`.
23. **`completedReductionEquiv`** — `(FR.13)`: `Red_X(Ī) ≅ ℍ(L_X^∨)`.
24. **`lossEquiv`** — `(FR.14)`: `𝔎_X = ker ρ_X ⊕ coker ι_X ≅ ℍ((L/L_X)^∨)`, the perfect
    hyperbolic pair.

### §4 — the serial doctrine-composition law

25. `flagIncl`, `flagProj`, `ker_flagIncl`, `flagIncl_injective`, `range_flagIncl`, `ker_flagProj`,
    `flagProj_surjective`.
26. **`serial_exact`** — `(FR.20)`: `0 → L₁/L₂ → L₀/L₂ → L₀/L₁ → 0` is exact.
27. **`serial_exact_dual`** — `(FR.21)`: the dual sequence
    `0 → (L₀/L₁)^∨ → (L₀/L₂)^∨ → (L₁/L₂)^∨ → 0` is exact.
28. **`finrank_serial`** — `(FR.22)`: `dim(L₀/L₂) = dim(L₀/L₁) + dim(L₁/L₂)`.
29. **`flag_pairing_trivial`**, `serialLagrangian`, **`serialLagrangian_isotropic`**,
    `prodSubmoduleEquiv`, **`finrank_serialLagrangian`** — `(FR.21a)`: the two summands of
    `𝔐 = (L₀/L₁)^∨ ⊕ (L₁/L₂)` pair trivially, so `𝔐` is isotropic, and `2·dim 𝔐 = dim 𝔎₀₂`, i.e.
    `𝔐` is a canonical Lagrangian.

### §5 — the literal prime-port instantiation

30. `augLine`, `finiteDimensional_augLine`, `augment_ne_zero`, `augLineEquiv`,
    **`dualCoannihilator_augLine`** — `(FR.23)`: `L = ℂ·ε` and `I = ker ε`.
31. **`admitted_augLine_one`**, **`unique_loss_augLine_one`** — `(FR.24)`: in `ℓ¹` the augmentation
    extends continuously, so `L_X = L` and `𝔎_{ℓ¹} = 0`.
32. **`admitted_augLine_eq_bot`** — `(FR.25)`, the generic erasure criterion: a chart carrying
    vectors of augmentation one and arbitrarily small norm has `L_X = 0`.
33. **`admitted_augLine_lp_eq_bot`**, **`admitted_augLine_top_eq_bot`** — `(FR.25)`: `ℓ^p` for
    `p > 1` (in particular `ℓ²`) and `ℓ^∞` erase the port.
34. `admittedIn_eq_bot_of_admitted_eq_bot`, **`loss_augLine_erasure`** — `(FR.25)`: in an erasing
    chart the reporter loss is the whole line `ℂ`, so `𝔎 ≅ ℍ(ℂ)`.

## Verification

```
lake env lean GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/FiniteReporterAdmission.lean
lake build GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.FiniteReporterAdmission
```

Green with no warnings.  `#print axioms` on
`exists_continuous_annihilator_of_notMem_closure`, `restrictAlong_injective`,
`dualAnnihilator_dualCoannihilator`, `closure_map_dualCoannihilator`, `resEquiv`, `algQuotEquiv`,
`topologicalClosure_eq_ker_contAnnihilator`, `evalCont_surjective`, `completedQuotEquiv`,
`chu_compatibility`, `kerRhoEquiv`, `cokerIotaEquiv`, `unique_loss_iff`, `lossEquiv`,
`formOrth_constraintIsotropic`, `reductionMap_surjOn`, `contFormOrth_contConstraintIsotropic`,
`algReductionEquiv`, `completedReductionEquiv`, `serial_exact`, `serial_exact_dual`,
`finrank_serial`, `serialLagrangian_isotropic`, `finrank_serialLagrangian`,
`dualCoannihilator_augLine`, `admitted_augLine_one`, `admitted_augLine_lp_eq_bot`,
`admitted_augLine_top_eq_bot` and `loss_augLine_erasure` reports only `propext`,
`Classical.choice`, `Quot.sound`.

## Scope notes

The card allows `k = ℝ` or `ℂ`; the module fixes `k = ℂ`, which is the case every instantiation in
the corpus uses, and takes the ambient `X` to be a normed space rather than a general Hausdorff
locally convex space.  Both restrictions only affect the separation step, item 1, whose proof is
the standard geometric Hahn–Banach argument and carries over verbatim to the locally convex case;
nothing downstream uses the norm.

`(FR.5)` is stated as a linear isomorphism `X/closure(j(I)) ≃ₗ[ℂ] L_X^∨`.  The card additionally
records that this is a *topological* isomorphism once `L_X^∨` carries its unique finite-dimensional
Hausdorff topology; that is automatic for a linear bijection between finite-dimensional Hausdorff
topological vector spaces and adds no algebraic content to the reduction statements
`(FR.12)`–`(FR.14)`, which is where `(FR.5)` is used.

The reductions `(FR.12)`–`(FR.13)` are recorded as the surjection-plus-kernel-plus-form-transport
package (`formOrth_constraintIsotropic`, `reductionMap_surjOn`, `ker_reductionMap`, and the
`≃ₗ` on the reduced double) rather than as a quotient of a subtype by a subtype, since
`↥S ⧸ T` for `T` a submodule of the ambient does not synthesise `HasQuotient`.  The two
presentations carry exactly the same information: the displayed maps are the reduction and its
kernel.

§6's source-dagger prediction, §7's virtual-equipment programme and §8's falsifier table are
statements about what a future indexed equipment must satisfy; the card itself says no such
equipment is constructed, and the module accordingly formalizes the admission criterion
(`unique_loss_iff`, `admitted_augLine_one`, `admitted_augLine_lp_eq_bot`) which is what those
sections quantify over.
