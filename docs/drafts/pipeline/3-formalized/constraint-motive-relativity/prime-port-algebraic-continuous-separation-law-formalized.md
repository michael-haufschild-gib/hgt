# Prime-port algebraic–continuous separation law — Lean certificate

- **ID:** `cmr-prime-port-algebraic-continuous-separation-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `prime-port-algebraic-continuous-separation-law.md` (same directory).
- **Status:** `[UNCONDITIONAL]` `[NO SORRY / NO AXIOM / NO PROP INTERFACE]`

## Lean modules

In `formal/GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/`, namespace
`HTGeometry.ConstraintMotiveRelativity`, both imported by `GaloisForLFunctions.HTGeometry`:

1. `PrimeAugmentationSymplectic.lean` — §1, the algebraic one-port reduction.
2. `PrimeAugmentationCompletion.lean` — §2 and §3, the completion phases and the separation defect.

## Formal statement chain

### §1 — algebraic one-port reduction (Theorem 1)

1. `augment`, `augment_single`, `augment_apply`, `augIdeal`, `augment_surjective` — `(RC.1)`:
   `ε x = ∑ x_p` on `K₀ = P →₀ ℂ` and its kernel `I₀`.
2. `sub_single_mem_augIdeal` — every difference `e_p - e_q` lies in `I₀`.
3. **`dualAnnihilator_augIdeal`** — `(RC.3)`: `I₀^⊥ = ℂ ε` in the algebraic dual.  A covector
   annihilating `I₀` takes one common value `a` on all coordinate vectors, hence equals `a ε`.
4. `PortDouble`, `portForm`, `portOrth`, `augIsotropic`, `augIsotropic_isotropic` — `(RC.2)`: the
   cotangent double with `ω((x,α),(y,β)) = α y - β x` and the isotropic subspace `I₀ ⊕ 0`.
5. **`portOrth_augIsotropic`** — `(RC.3)`: `(I₀ ⊕ 0)^ω = K₀ ⊕ ℂ ε`.
6. `portRed`, `hyperbolicForm`, **`portForm_eq_hyperbolicForm_aug`**, **`portRed_surjOn`**,
   **`ker_portRed_inf`** and **`coisotropic_reduction`** — `(RC.4)`: the reduction
   `(x, a ε) ↦ (ε x, a)` maps `I₀^ω` onto `ℂ × ℂ`, its kernel there is exactly `I₀`, and it carries
   the cotangent form to the hyperbolic form.  So `I₀^ω/I₀ ≅ ℍ(ℂ)`.
7. **`augIdeal_quotient_equiv`** — the second half of `(RC.4)`: `K₀/I₀ ≅ ℂ` through `ε`.

### §2 — completion phases (Theorems 2 and 3)

8. `lpEmb`, `lpEmb_single`, `lpEmb_eq_sum`, `lpEmb_apply_coord` — the chart embedding of the
   finitely supported prime coordinates into `lp (fun _ : P => ℂ) p`.
9. **`mem_closure_image_augIdeal`** — the generic erasure criterion: if the chart contains vectors
   of augmentation one and arbitrarily small norm, the augmentation constraint is dense in the
   chart image.  This is `(RC.9)` stripped to the only property it uses.
10. `spreadVec`, `wtPort_spreadVec`, `lpEmb_spreadVec` — the spread vector
    `N⁻¹(e_{q₁} + ⋯ + e_{q_N})` has augmentation one.
11. **`exists_small_spread_lp`** — in `ℓ^p` with `p > 1` its norm is `N^{1/p-1} → 0`; the proof
    computes `‖·‖^{p} = N^{1-p}` with `lp.norm_sum_single`.
12. **`exists_small_spread_top`** — in `ℓ^∞` its norm is `N⁻¹ → 0`.
13. **`closure_image_augIdeal_lp`** and **`closure_image_augIdeal_top`** — `(RC.8)`: in `ℓ^p`
    (`1 < p < ∞`) and in `c₀` — the closure of the finitely supported vectors inside `ℓ^∞` — the
    augmentation constraint is dense in the chart image.
14. **`eq_zero_on_range_of_vanishing_on_augIdeal`** — `(RC.8)`, annihilator half: any continuous
    functional vanishing on the constraint vanishes on the whole chart image, so `I₀^⊥ = 0` and
    Hausdorff reduction of the port is zero.
15. `summable_norm_lp_one`, `summable_lp_one`, `norm_eq_tsum_one`, `wtLin`, `wtCLM`,
    `wtCLM_apply`, **`augCLM`**, `augCLM_lpEmb` — the augmentation extends to a continuous
    functional of norm at most one on `ℓ¹`, by `‖∑' x_q‖ ≤ ∑' ‖x_q‖ = ‖x‖₁`.
16. `coeFn_trunc_one`, `norm_sub_trunc_one` — the truncation error in `ℓ¹` is the tail mass.
17. **`closure_image_augIdeal_one`** — `(RC.7)`: in `ℓ¹` the closure of the constraint is exactly
    `ker ε`.  Truncate, then correct the finite augmentation in one coordinate; both errors tend to
    zero because the tail mass and the partial sums do.
18. **`augCLM_surjective`** — the closed constraint has codimension one.
19. **`eq_smul_augCLM_of_vanishing`** — the continuous annihilator of `ker ε` is the line `ℂ ε`.

### §3 — the separation defect (Corollary 4)

20. **`separation_defect_one`** — `𝔎_{ℓ¹} = 0`: completion is injective on the algebraic port
    (`ker q_{ℓ¹} = 0`), and every algebraic annihilator `a ε` of the constraint is the restriction
    of the continuous annihilator `a ε` (`coker a_{ℓ¹} = 0`).
21. **`separation_defect_erasure`** — `𝔎_X ≅ ℍ(ℂ)` in every chart with arbitrarily small vectors
    of augmentation one: completion sends the whole algebraic port into the closure of the
    constraint (`ker q_X = K₀/I₀ ≅ ℂ`), and no continuous annihilator restricts to a nonzero
    algebraic one (`range a_X = 0`, so `coker a_X ≅ I₀^⊥ = ℂ ε ≅ ℂ`).  Applying it to
    `exists_small_spread_lp` and `exists_small_spread_top` gives `(RC.13)` for `ℓ^p` (`p > 1`) and
    for `c₀`.

## Verification

```
lake env lean GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/PrimeAugmentationSymplectic.lean
lake env lean GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/PrimeAugmentationCompletion.lean
lake build GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.PrimeAugmentationCompletion
```

Green with no warnings.  `#print axioms` on `dualAnnihilator_augIdeal`, `portOrth_augIsotropic`,
`coisotropic_reduction`, `augIdeal_quotient_equiv`, `mem_closure_image_augIdeal`,
`exists_small_spread_lp`, `exists_small_spread_top`, `closure_image_augIdeal_lp`,
`closure_image_augIdeal_top`, `eq_zero_on_range_of_vanishing_on_augIdeal`,
`closure_image_augIdeal_one`, `augCLM_surjective`, `eq_smul_augCLM_of_vanishing`,
`separation_defect_one` and `separation_defect_erasure` reports only `propext`, `Classical.choice`,
`Quot.sound`.

## Generality note

Both modules are stated for an arbitrary nowhere-vanishing (respectively unimodular) coefficient
covector `c` — `wtPort`, `wtIdeal`, `wtIsotropic`, `wtRed`, `dualAnnihilator_wtIdeal`,
`portOrth_wtIsotropic`, `coisotropic_reduction_wt`, `wtIdeal_quotient_equiv`,
`mem_closure_image_wtIdeal`, `closure_image_wtIdeal_lp/_top/_one`, `wtCLM`, `wtCLM_surjective`,
`eq_smul_wtCLM_of_vanishing`, `separation_defect_one`, `separation_defect_erasure`.  The
augmentation `ε x = ∑ x_p` is the case `c ≡ 1`, and every statement of this card is the
corresponding instance under the `aug`-prefixed name listed above.  The general form is what the
phase-port card `prime-phase-port-recurrence-completion-law` instantiates at `c = (p^{-it})`.

## Scope notes

`(RC.4)` is stated as the reduction data — surjection onto `ℂ × ℂ`, kernel exactly the constraint,
and transport of the cotangent form to the hyperbolic form — rather than as a packaged
`LinearEquiv` on a subtype quotient.  The reason is mechanical: in this mathlib the quotient of a
*submodule of a `Finsupp` submodule* fails instance synthesis (`HasQuotient ↥S (Submodule ℂ ↥S)`
does not resolve when `S : Submodule ℂ (P →₀ ℂ)`), while ambient quotients resolve fine.  The three
recorded facts are exactly what a symplectic isomorphism `I₀^ω/I₀ ≅ ℍ(ℂ)` asserts, and the
`K₀/I₀ ≅ ℂ` half is packaged as a genuine `LinearEquiv` in `augIdeal_quotient_equiv`.

`c₀` is realized as the closure of the finitely supported vectors inside `ℓ^∞ = lp _ ⊤`, which is
its standard description; the density statement `closure_image_augIdeal_top` is therefore literally
"the constraint is dense in `c₀`".

The defect `(RC.12)` is recorded through the two elementary conditions that determine `ker q_X` and
`coker a_X` rather than by constructing the quotient maps: `ker q_X = 0` is
"`emb l` in the closure of the constraint implies `ε l = 0`", and `coker a_X = 0` is "every
algebraic annihilator extends continuously".  Corollary 4.1 is the observation that the induced
seminorm on `K₀/I₀` is zero in the erasure phases, which is exactly `separation_defect_erasure`'s
first conjunct.

§4–§8 are source interpretation and no-go bookkeeping and claim no further theorem.
