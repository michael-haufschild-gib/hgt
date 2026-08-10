# Initial-execution symmetry inheritance and anomaly necessity — formalized

- **ID:** `initial-execution-symmetry-inheritance-and-anomaly-necessity-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `initial-execution-symmetry-inheritance-and-anomaly-necessity.md` (same directory)
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module | Path |
|---|---|
| `GaloisForLFunctions.HTGeometry.ConstraintRelativity.SymmetryInheritance` | `formal/GaloisForLFunctions/HTGeometry/ConstraintRelativity/SymmetryInheritance.lean` |

Wired into `GaloisForLFunctions.HTGeometry`.

## Formal theorem chain

All declarations live in namespace `HTGeometry.ConstraintRelativity`.

Theorem 1 — initial objects inherit symmetry:

1. `initialCompare` — the canonical arrow `α_F : I ⟶ F I` of card `(2)`.
2. `initialCompare_unique` — it is the only such arrow, so the equivariant structure exists and is
   unique.
3. `initialCompare_id` — card `(3)`, first half: `α_1 = id`.
4. `initialCompare_comp` — card `(3)`, second half: the strict cocycle law
   `α_{F⋙F'} = α_{F'} ≫ F'(α_F)`.
5. `isInitialMap` — an autoequivalence sends an initial object to an initial object.
6. `isIso_initialCompare` — `α_F` is an isomorphism.
7. `initialIsoMap` — the resulting isomorphism `I ≅ F I`.

The card's strict action `F_1 = id`, `F_g F_h = F_{gh}` enters only through the two instances
`F = 𝟭` and `F = F ⋙ F'`, which items 3 and 4 state directly.  Stating them this way avoids
equalities of functors, which carry no mathematical content here.

Theorem 2 — equivariant execution lands in the fixed locus:

8. `smul_obs_initial` — for a group acting by autoequivalences and an isomorphism-invariant
   equivariant observation `P`, `g • P I = P I` for every `g`.
9. `not_free_orbit_obs_initial` — no free nontrivial orbit contains `P I`.
10. `stabilizer_obs_initial_eq_top` — the stabilizer of `P I` is the whole group.

Corollary 3 — the trilemma — is the contrapositive of items 8–10: with an equivariant doctrine and
an initial successor, the successor is equivariant; a non-equivariant canonical event therefore
requires either failure of the action (anomaly) or nonuniqueness (an orbit plus a selection rule).

Generator-commutator necessity:

11. `RadialFlow` — the radial flow `Γ_c` acting on each eigenspace of the grading operator
    `∂ = ∂_log` by a scalar, with eigenvectors spanning.
12. `commute_flow_of_commute_grading` — **card `(6)`, the necessary condition**: if
    `[d, ∂_log] = 0` then `d Γ_c = Γ_c d` for every `c`.
13. `grading_commutator_ne_zero` — the contrapositive: a differential that breaks radial
    equivariance must have `[d, ∂_log] ≠ 0`.

14. `diagonalGrading`, `diagonalRadialFlow` — **radial flows exist**: for any weight family `μ`
    and any weight law `g` the graded space `Kⁿ` carries a radial flow whose grading is diagonal
    with eigenvalues `μ` and whose flow is diagonal with entries `g c (μ i)`.  Items 11–13 are
    therefore statements about an inhabited class.
15. `anomalyFlow`, `anomalyDifferential`, `anomalyDifferential_not_commute_flow`,
    `anomalyDifferential_grading_commutator_ne_zero` — **the anomaly condition is satisfiable**:
    on the two-weight model `μ = (0, 1)` the lowering operator `d(v₀,v₁) = (v₁,0)` fails to commute
    with the radial flow, so the hypothesis of item 13 is met and its conclusion
    `[d, ∂_log] ≠ 0` is a genuine obstruction rather than a vacuous implication.

Prime-component refinement, card `(7)`:

16. `anomalyBracket`, `anomalyBracket_eq_zero_iff` — **card `(5)`/`(7)`**: the commutator
    `A = [d, ∂]` of the new differential with a derivation, and its vanishing criterion.
17. `anomalyBracket_id`, `anomalyBracket_add`, `anomalyBracket_smul` — the anomaly is linear in the
    derivation slot and kills the central operator.
18. `anomalyBracket_sum_smul` — **the contraction law**: `[d, ∑ c_ℓ ∂_ℓ] = ∑ c_ℓ [d, ∂_ℓ]`, so the
    anomaly of the contracted derivation is the same contraction of the components `A_ℓ` of card
    `(7)`.
19. `exists_anomalyBracket_ne_zero_of_contraction_ne_zero` — a nonzero contracted anomaly forces at
    least one nonzero component anomaly.
20. `anomalyBracket_grading_ne_zero_of_not_commute_flow`,
    `anomalyBracket_anomalyDifferential_grading_ne_zero` — items 13 and 15 in bracket form.
21. `partialComponents`, `partialComponents_bracket_one_eq_zero`,
    `partialComponents_contraction_ne_zero` — **the contraction does not detect the components**:
    a two-component family whose contracted anomaly is nonzero for every coefficient family with a
    nonzero first entry, while its second component anomaly is `0`.
22. `logContractionCoeff`, `entangledComponents`, `entangledComponents_bracket_ne_zero`,
    `entangledComponents_contraction_eq`, `entangledComponents_contraction_ne_zero`,
    `entangledComponents_anomaly_contraction_eq_zero` — **the card's caveat, proved**: "scalar
    nonzero commutator is insufficient if it appears only after logarithmic contraction".  Against
    the prime logarithms `log 2`, `log 3` there are two component derivations whose contraction
    `∂_log` is a nonzero derivation and whose component anomalies `A_2`, `A_3` are both nonzero,
    yet `[d, ∂_log] = 0`.  Condition `(6)` is therefore strictly weaker than the componentwise
    refinement `(7)`, in both directions.
23. `sum_log_primes_mul_rat_ne_zero` — a nontrivial rational combination of distinct prime
    logarithms is nonzero, from `GaloisForLFunctions.linearIndependent_log_primes`.
24. `contraction_ne_zero_of_rational_components`, `rationalComponents_contraction_ne_zero` —
    **the exact obstruction to the cancellation of item 22**: if the component anomalies `A_ℓ` are
    rational multiples of one nonzero operator, not all zero, then the logarithmic contraction
    against distinct prime logarithms has nonzero anomaly.  The cancellation in item 22 requires
    irrational entanglement of the components, and the class is inhabited.

Card equations `(8)` and `(9)` are explicitly labelled placeholders on the paper card, not
theorems, and are not formalized.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstraintRelativity/SymmetryInheritance.lean  # clean
lake build GaloisForLFunctions.HTGeometry                                                   # green
```

`#print axioms` on `initialCompare_comp`, `isIso_initialCompare`, `smul_obs_initial`,
`commute_flow_of_commute_grading` returns only `[propext, Classical.choice, Quot.sound]`, and the
same on `anomalyBracket_sum_smul`, `exists_anomalyBracket_ne_zero_of_contraction_ne_zero`,
`partialComponents_contraction_ne_zero`, `entangledComponents_bracket_ne_zero`,
`entangledComponents_anomaly_contraction_eq_zero`, `sum_log_primes_mul_rat_ne_zero`,
`contraction_ne_zero_of_rational_components`, `rationalComponents_contraction_ne_zero`.
