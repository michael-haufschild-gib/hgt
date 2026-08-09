# Source-word filtration and fixed-action selection no-go — formalized

- **ID:** `source-word-filtration-and-selection-no-go-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `source-word-filtration-and-selection-no-go.md` (same directory)
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module | Path |
|---|---|
| `GaloisForLFunctions.HTGeometry.ConstraintRelativity.WordFiltrationSelection` | `formal/GaloisForLFunctions/HTGeometry/ConstraintRelativity/WordFiltrationSelection.lean` |
| `GaloisForLFunctions.HTGeometry.ConstraintRelativity.QuestionRelationBalance` | shared exact-sequence infrastructure |

Wired into `GaloisForLFunctions.HTGeometry`.

## Realization

| Card | Lean |
|---|---|
| filtered algebra `A_{≤n}` | `AlgebraFiltration` (structure: `fil`, `mono`, `one_mem`, `mul_le`, `iSup_eq`) |
| seed `V ⊆ M` | `V : Submodule k M` |
| `P n = A_{≤n} ⊗ V` | `presentation F V n = range (rTensor V (F.fil n).subtype) ≤ A ⊗[k] V` |
| `ev` | `wordEval V = TensorProduct.lift (seedAction V)` |
| `R n = ker ev ∩ P n` | `relationSpace F V n` |
| `K n = A_{≤n} V` | `wordSpace F V n = F.fil n • V` |
| `A V` | `fullWordSpace F V = ⨆ n, wordSpace F V n` (`= ⊤ • V`, `fullWordSpace_eq_top_smul`) |

`presentationEquivTensor` certifies `presentation F V n ≅ A_{≤n} ⊗ V`; the identification
`P n ⊆ P (n+1)` of the card is then the literal submodule inclusion `presentation_mono`.

## Formal theorem chain

All declarations live in namespace `HTGeometry.ConstraintRelativity`.

Master theorem:

1. `presentationQuotEquivWordSpace` — **(1)** `P n / R n ≅ K n`.
2. `relationSpace_inf_presentation` — **(2)** and **(4)**: `R m ∩ P n = R n` for `n ≤ m`; in
   particular `(P (n−1) ∩ R n)/R (n−1) = 0`, the vanishing killed-old-freedom term.
3. `wordSpace_mono` — **(2)**, second half: `K n ⊆ K (n+1)`.
4. `map_wordEval_presentation` — `ev(P n) = K n`.
5. `presentation_inf_comap_wordSpace` — **(3)**, the graded kernel identity
   `P (n+1) ∩ ev⁻¹(K n) = R (n+1) + P n`.  With item 2 this is the short exact sequence
   `0 → R n/R (n−1) → P n/P (n−1) → K n/K (n−1) → 0`: it is the instance
   `(Rold, Pold, Rnew, Pnew) = (R n, R (n+1), P n, P (n+1))` of the four-term balance sequence of
   `dynamic-question-relation-balance-law`, whose killed term is `⊥` by item 2 and whose created
   term is `K (n+1)/K n` by items 4 and 5.
6. `finrank_presentation` — `dim P n = dim A_{≤n} · dim V`.
7. `finrank_relationSpace_add_finrank_wordSpace` — `dim R n + dim K n = dim A_{≤n} · dim V`.
8. `finrank_budget` — **(3)**, the exact graded budget
   `(dim R (n+1) − dim R n) + (dim K (n+1) − dim K n) = (dim A_{≤n+1} − dim A_{≤n}) · dim V`.

Degree-one plateau theorem:

9. `wordSpace_succ` — under `(4)`, `K (n+1) = K n + A_{≤1} K n`.
10. `smul_le_of_degreeOne_stable` — a stage stable under `A_{≤1}` is stable under all of `A`.
11. `wordSpace_succ_eq_iff` — **(5)** `K (n+1) = K n ⟺ K n = A V`.
12. `wordSpace_lt_succ`, `finrank_wordSpace_succ`, `finrank_wordSpace_ge` — before stabilization the
    dimension grows by at least one per step.
13. `exists_wordSpace_eq_full` — **stabilization depth**: `∃ n ≤ dim A V − dim V` with `K n = A V`.

Necessity of the degree-one hypothesis:

14. `degreeTwoFiltration` — the filtration of `k × k` with `A_{≤0} = A_{≤1} = k·1` and
    `A_{≤n} = k × k` for `n ≥ 2`; its only generator sits in degree two.
15. `degreeTwo_plateau_not_stable` — `K 0 = K 1` while `K 1 < K 2`: one plateau does not force
    stabilization without `(4)`.

Card consequence 1 ("longer words under one fixed action never perform selection") is items 2 and
11–13 together: the killed-freedom term is identically zero and the reachable space saturates in
bounded depth.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstraintRelativity/WordFiltrationSelection.lean  # clean
lake build GaloisForLFunctions.HTGeometry                                                       # green
```

`#print axioms` on `wordSpace_succ_eq_iff`, `exists_wordSpace_eq_full`, `finrank_budget`,
`presentationQuotEquivWordSpace`, `degreeTwo_plateau_not_stable` returns only
`[propext, Classical.choice, Quot.sound]`.
