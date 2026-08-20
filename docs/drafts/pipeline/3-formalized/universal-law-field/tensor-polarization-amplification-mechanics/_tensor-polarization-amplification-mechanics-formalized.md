# Tensor polarization amplification mechanics — Lean certification (folder record)

| Card | Lean module |
|---|---|
| `tensor-formation-inertia-conservation-amplification-and-global-selection-law` (ULF-TPAM-1) | `HTGeometry.TensorPolarizationAmplification` |
| `amplified-form-embedding-port-budget-and-subrank-selection-law` (ULF-TPAM-2) | `HTGeometry.ConstitutiveAmplifiedPortBudgetSelection` |

## Coverage

* **ULF-TPAM-1.**  Theorem 2.1 (tensor-polarization fusion) — `negIndex_kronecker`,
  `posIndex_kronecker`, with the counting lemmas `card_mul_neg`, `card_mul_pos`,
  `negIndex_diagonal_kronecker`, `posIndex_diagonal_kronecker`.  Theorem 3.1
  (rank/signature conservation) — `tensorPolar_total`, `tensorPolar_signature`.  Theorem 4.1
  (formation-depth properness) — `tensorPolar_twice_negative`,
  `tensorPolar_negative_ge_total_prev`, `tensorPolar_negative_strictly_amplifies`,
  `tensorPolar_negative_sublevel_window`, `tensorPolar_no_uniform_negative_budget`.
  Theorem 4.2 (global selection) — `tensorPolar_uniform_negative_budget_iff`, with the two closed
  capstones `tensorPolarizationAmplification_closed` and `tensorPolarizationSelection_closed`.
* **ULF-TPAM-2.**  Theorem 2.1 — `negIndex_le_of_injective_formEmbedding`.  Theorem 3.1 — the
  amplification floor `tensorPolar_negative_ge_total_prev` (imported).  Theorem 4.1 —
  `tensorPolar_zero_of_strict_portBudget`, `tensorPolar_zero_of_formEmbedding_portBudget`.
  Corollary 4.2 — `tensorPolar_zero_of_eventual_subrankBudget`.  Capstone —
  `amplifiedPortBudgetSelection_closed`.

Sections 5–7 of both cards are interpretation, a fourth-organ prediction, and a *conditional* RH
interface; neither card asserts an RH statement, and none is formalized as one.

## Verification (2026-08-20)

Both modules elaborate from the tree with 0 errors; all 22 public `theorem`/`lemma` declarations
across them report only `propext`, `Classical.choice`, `Quot.sound`.  Both are imported by
`GaloisForLFunctions.HTGeometry.UniversalLawField`.
