# ULF-EARM-1 — Lean certification record

**Card:** `abelian-repair-least-action-green-work-recurrence-and-properness-law.md`
**Module:** `formal/GaloisForLFunctions/HTGeometry/AbelianRepairLeastAction.lean` (98 public
declarations, axiom-clean)

## Card result → Lean declaration

| Card | Statement | Lean |
|---|---|---|
| §1, (AR.1) | the reduced Laplacian of a sink-connected multigraph | `ReducedLaplacian`, `deg`, `mat`, `mat_symm`, `mat_self`, `mat_nonpos_of_ne` |
| (AR.2)–(AR.3) | stability and legal toppling | `Stable`, `topple`, `Legal`, `applyOdo` |
| Lemma 2.1, (AR.4) | the quadratic form is edge differences plus sink squares | `two_mul_quadratic` |
| Lemma 2.1 | positive definiteness and inverse positivity | `quadratic_nonneg`, `quadratic_pos`, `nonneg_of_act_nonneg`, `injective_actMap`, `surjective_actMap` |
| (AR.5) | the strictly positive unit potential | `potential`, `act_potential`, `potential_pos` |
| (AR.6) | the odometer | `odo`, `odo_apply`, `configAfter`, `configAfter_eq_applyOdo` |
| (AR.8) | one repair spends one unit of potential | `work`, `work_topple` |
| Thm 3.1, termination | every legal execution is finite | `length_le_work`, `exists_legal_stable` |
| Thm 3.1, (AR.7) | least action | `odo_le_of_legal` |
| Thm 3.1, abelian | schedule independence | `odo_eq_of_legal_stable`, `stabOdo_eq`, `stab_eq` |
| Cor 3.2, (AR.11) | conservative exactification | `applyOdo_add`, `act_odo_eq` |
| §4, (AR.14) | the source-driven sequence | `sourceAdd`, `stabIter`, `odoIter`, `workIter` |
| Lemma 4.1, (AR.15) | formation/stabilization exchange | `stab_stab_add` |
| Lemma 4.1, (AR.16) | the sequence is one map's orbit | `stabIter_succ` |
| (AR.17) | the Green operator and form | `green`, `act_green`, `green_act`, `greenForm`, `greenPair`, `greenForm_add`, `greenForm_smul` |
| (AR.18)–(AR.19) | lineage work and exact balance | `lineageWork`, `act_odoIter`, `act_real_odoIter`, `chargeIter` |
| (AR.20) | total-repair conservation | `sum_odo_eq_potential_pairing`, `sum_potential_mul_mat` |
| (AR.21) | exact Green work | `lineageWork_eq_greenForm`, `workIter_eq`, `workIter_expand` |
| (AR.22) | the cofinal limits | `tendsto_odoIter_div`, `tendsto_workIter_div` |
| (AR.23) | the observer group and its translation law | `chargeLattice`, `observerGroup`, `observer_class_applyOdo`, `observer_class_stab`, `observer_class_stabIter`, `exists_eventual_period` |
| (AR.24) | the return odometer is `P · G a` | `return_odometer` |
| (AR.25) | the closed-loop work is `P² aᵀGa` | `return_work` |
| Thm 6.1, (AR.27) | bounded lineage work selects the neutral source | `bddAbove_workIter_iff` |
| §7, (AR.28)–(AR.31) | the two-vertex prediction | `TwoVertex.pair`, `pair_mat`, `pair_act_holonomy`, `pair_return`, `pair_cycle_work` |

## Proof notes

* The card's positivity argument is factored into two reusable pieces: a **minimum principle**
  (`nonneg_of_act_nonneg`) proved by propagating equality along a graph path to the sink, and the
  **quadratic identity** (AR.4).  Invertibility of the reduced Laplacian, entrywise inverse
  positivity, and strict positivity of `g = Δ⁻¹1` all follow from the first.
* Termination is the potential argument (AR.8): each legal toppling decreases `gᵀη` by exactly one
  and the potential stays nonnegative, so `length l ≤ work η`.  Existence of a maximal legal
  execution then comes from `Nat.sSup_mem` on the (bounded) set of legal lengths.
* Least action (AR.7) is proved by induction on the execution list, using only that the head vertex
  must have `1 ≤ u a` — if `u a = 0` the candidate endpoint would be unstable at `a`.  This avoids
  the "first time the prefix exceeds" bookkeeping of the paper proof.
* Boundedness of the residual terms in (AR.22) and Theorem 6.1 uses that the set of stable
  configurations `{s | ∀ v, 0 ≤ s v < deg v}` is a finite product of integer intervals, so the
  residual Green quantities take finitely many values.
* The two-vertex prediction is verified by exhibiting the explicit legal execution `[0,0,1]` and
  computing its odometer; the work value `6` is then the general (AR.25) specialised, not a
  separate numerical claim.

## Verification

* `lake env lean` on the module: 0 errors, 0 warnings.
* `#print axioms` over all 98 public declarations: only `propext`, `Classical.choice`, `Quot.sound`.
* No `sorry`, `admit`, `axiom`, `opaque`, `unsafe`.
* Wired into `GaloisForLFunctions.HTGeometry` and `UniversalLawField.lean`.

## Not claimed

The card makes no RH claim and none is made here.  Clause 4 of Theorem 6.1 ("the lifted odometer of
one eventual observer cycle is zero") is covered by `return_odometer` together with
`greenForm_pos`; the equivalence is stated in the form the card boxes, `sup_n W_n < ∞ ↔ a = 0`.
