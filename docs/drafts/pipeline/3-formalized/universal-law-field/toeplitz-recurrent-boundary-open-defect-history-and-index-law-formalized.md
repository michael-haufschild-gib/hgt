# Toeplitz recurrent boundary, open defect history, index — Lean certification

- **ID:** ULF-TOEPLITZ-1
- **Paper card:** `toeplitz-recurrent-boundary-open-defect-history-and-index-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutiveToeplitzDefectIndex`
- **Universal-law umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Model

`ToeplitzSpace = lp (fun _ : ℕ => ℂ) 2` is the Hardy space `ℓ²(ℕ₀)`.  The `n`-fold shift is defined
once as a coordinate reindexing,

```
shiftFun n f k = if k < n then 0 else f (k − n),
backFun  n f k = f (k + n),
```

so `Sⁿ` and `S*ⁿ` are primitive and every clause is proved without induction on operator powers.
New infrastructure built here: the `ℓ²`-summability of both reindexings, the norm identity for the
forward reindexing, the adjoint relation, the defect projection and its explicit `ℂⁿ` coordinate
isomorphism, the cokernel isomorphism, and the compact-perturbation rigidity argument.

## Certified declarations, by clause

| Clause | Lean |
|---|---|
| 1: `S*ⁿSⁿ = 1` | `shiftIsom`, `shiftOp`, `backOp`, `adjoint_shiftOp`, `backOp_comp_shiftOp`, `adjoint_comp_shiftOp` |
| 2: `Dₙ` is the truncation projection | `defectOp`, `defectOp_apply`, `defectOp_comp_self`, `adjoint_defectOp` |
| 2: `rank Dₙ = n` | `defectSubmodule`, `range_defectOp`, `coordVec`, `defectCoordEquiv`, `finrank_defectSubmodule` |
| 3: cocycle law (4) | `defectOp_add` |
| 3: orthogonality | `defectOp_orthogonal` |
| 4: observer periodicity | `boundaryObserver`, `boundaryObserver_add` |
| 5: return + divergence | `boundaryObserver_mul`, `finrank_defect_return_tendsto`, `recurrent_boundary_open_defect` |
| 6: `ind Sⁿ = −n` | `ker_shiftOp`, `range_shiftOp`, `cokerShiftEquiv`, `finrank_ker_shiftOp`, `finrank_coker_shiftOp`, `shiftIndex`, `shiftIndex_eq` |
| 7: `∂[zⁿ] = −[Dₙ]` | `coDefect_eq_zero`, `boundaryClass`, `boundaryClass_eq_neg_defect`, `boundaryClass_eq`, `boundaryClass_eq_shiftIndex` |
| 8: no unitary lift | `shiftOp_not_surjective`, `no_invertible_compact_perturbation`, `no_unitary_compact_perturbation` |
| all eight on one producer | `toeplitz_recurrent_boundary_open_defect_index` |

### The mechanism of clause 8

Suppose `U` is invertible with inverse `V` and `U − Sⁿ` is compact.  Then `C = V(U − Sⁿ)` is compact
and `V Sⁿ = 1 − C`.  Since `Sⁿ` is injective and `V` is injective, `1 − C` is injective, so `1` is
not an eigenvalue of `C`; mathlib's Fredholm alternative
(`IsCompactOperator.hasEigenvalue_or_mem_resolventSet`) then places `1` in the resolvent set of `C`,
so `1 − C` is invertible and therefore surjective — which forces `Sⁿ` to be surjective.  But `Sⁿ`
misses `e₀` for `n > 0`.  This is strictly stronger than the card's clause 8, since it rules out
*every* invertible compact perturbation, not only unitary lifts inside `𝒯`.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveToeplitzDefectIndex.lean
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
```

Both pass with no warnings; the umbrella build completed 11,427 jobs.  `#print axioms` on the twelve
declarations audited (clause capstones plus the bundle) reports only `propext`, `Classical.choice`,
and `Quot.sound`.  No project axiom, placeholder, hypothesis interface, or computation proof is used.

## Scope, stated explicitly

Clause 7 is certified **computationally, not K-theoretically**.  Mathlib has no C*-algebra K-theory:
the module does not construct `K₀(𝒦)`, the Toeplitz extension `0 → 𝒦 → 𝒯 → C(S¹) → 0`, or the
six-term exact sequence.  What is certified is the operator content that the connecting map
evaluates — `1 − S*ⁿSⁿ = 0`, `1 − SⁿS*ⁿ = Dₙ`, and the resulting class `−rank(Dₙ) = −n` under the
standard rank isomorphism `K₀(𝒦) ≅ ℤ` — together with the identification of that number with the
Fredholm index.  Clause 8 needs no C*-packaging at all and is certified in the stronger operator
form above.

## Exact field consequence

One one-sided isometry forces the whole package: positivity (`S*ⁿSⁿ = 1`), a unitary phase quotient,
a recurrent finite boundary observation, a defect whose rank grows linearly *along the observer's
exact returns*, an index equal to minus that rank, and the impossibility of restoring reversibility
upstairs.  Reversible and irreversible organs are not stored in independent slots here; they are two
readings of one relation.
