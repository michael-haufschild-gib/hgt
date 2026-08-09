# Cyclic bulk-boundary character, fusion recurrence, open lift — Lean certification

- **ID:** ULF-BULK-1
- **Paper card:**
  `cyclic-bulk-boundary-character-fusion-recurrence-and-open-lift-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveBulkBoundaryFusion`
- **Universal-law umbrella:**
  `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Certified declarations

### The marked root of unity

`omega = exp(2πi/3)`; `omega_isPrimitiveRoot` identifies it as a primitive cube root of unity via
mathlib's `Complex.isPrimitiveRoot_exp`, giving `omega_pow_three` and the reduction
`omega_pow_mod`.

### Theorem 2.1 — boundary indistinguishability

`boundaryChar j = ω^{j.val}` is the value of the bulk character of `M j` at the marked generator.

- `finrank_boundary` — every boundary condition is one-dimensional;
- `finrank_boundaryEnd` — its endomorphism algebra is one-dimensional (the equivalence
  `(ℂ →ₗ[ℂ] ℂ) ≃ₗ[ℂ] ℂ`, `f ↦ f 1`, is constructed explicitly), and `intertwines_self` shows every
  linear endomorphism is automatically `A`-equivariant, so this really is `End_A(M j)`;
- `norm_boundaryChar` and `normSq_boundaryChar` — the positive character shadow is constantly one;
- `boundary_scalar_data_constant` — the three scalar readings agree for every pair of boundaries;
- `boundary_not_isomorphic` — for `i ≠ j` no linear equivalence intertwines `M i` with `M j`;
- `boundaryChar_injective` — the bulk character separates them, using primitivity.

Together: scalar boundary data cannot reconstruct the boundary condition, and a bulk phase
observable can.

### Theorem 3.1 — fusion recurrence and open history

- `boundaryChar_add` — fusion multiplies characters, hence adds the grade mod three;
- `fusion_iterate` — `n` fusions with the defect `M 1` starting from `M 0` give the character `ω^n`
  and the grade `n mod 3`;
- `fusion_period_exact` — the boundary observer closes after exactly three fusions and after no
  smaller positive number;
- `fusionGrade_not_injective` — the projection `ℕ → ZMod 3` forgets the completed cycles;
- `fusionLift` is the logarithmic lift `2πin/3`, with `exp_fusionLift` relating it to `ω^n` and
  `fusionLift_injective` showing the lifted history is open.

### Capstone

`bulk_boundary_fusion_law` bundles the seven conclusions.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveBulkBoundaryFusion.lean
lake build GaloisForLFunctions.HTGeometry.ConstitutiveBulkBoundaryFusion
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
```

All checks passed with no warnings.  `#print axioms` on character injectivity, nonisomorphism, the
endomorphism dimension, the exact fusion period, the lift injectivity, and the capstone reports only
`propext`, `Classical.choice`, and `Quot.sound`.  No project axiom, placeholder, hypothesis
interface, or unresolved theorem premise is used.

## Scope note

Boundary conditions are certified through their bulk character at the marked generator, which is a
complete invariant of a one-dimensional module over the group algebra of `C₃`; the group algebra and
its Hopf comultiplication are not constructed, since every statement of the card is a statement
about that character and about equivariant linear maps, both of which are formalized directly.

## Exact field consequence

Equal dimension, equal endomorphism algebra, and equal positive character norm are compatible with
genuinely different boundary conditions.  What separates them is a bulk phase, and the fusion action
of a defect makes the boundary observer exactly recurrent while the marked count — and its
logarithmic lift — remain open.  Positive scalar boundary data is a strictly lossy reader of a
bulk-boundary law.
