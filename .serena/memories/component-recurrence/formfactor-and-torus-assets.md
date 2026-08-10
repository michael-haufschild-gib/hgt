# Component recurrence torus + spectral form factor — assets and traps

State after closing the Lean gate of
`docs/drafts/pipeline/3-formalized/component-recurrence-torus-and-replica-factorization-law.md`
(2026-08-10).

## New reusable assets (do not rebuild)

`HTGeometry/TupleHistogramCount.lean`
- `tupleHistogram f i = card {s | f s = i}`, `sum_tupleHistogram`, `tupleHistogram_cons`;
- `card_tupleHistogram_fiber m k (h : ∑ i, k i = m) :
  (univ.filter fun f : Fin m → I => tupleHistogram f = k).card = Nat.multinomial univ k`;
- `card_componentHistogram_fiber`: the product-alphabet version, `∏ c multinomial (k c)`.
This is the fibre count mathlib does not have.  Proof: split a tuple by its first entry
(`Finset.card_eq_sum_card_fiberwise` on `f ↦ f 0`, then `Finset.card_nbij'` with `Fin.tail`/
`Fin.cons`) and land on the corpus Pascal rule `multinomial_sum_update_pred`.

`HTGeometry/ComponentSpectralFormFactorProduct.lean`
- `sum_multinomial_piAntidiag_eq_sum_tuple` (and the pair form): every multinomial-weighted replica
  sum over `piAntidiag m` is a plain sum over tuples.  This is the general translator between the
  corpus's multiplicity-vector definitions and tuple combinatorics;
- `histogramCollisionCount X m = ∑_{|k|=m} multinomial(k)^2`, `replicaFormFactorCoefficient` =
  `a_{d,m}`, `componentHistogramCollisionCount_eq_prod`, and the uniform-mass evaluation
  `fidelityReplicaComponentCollisionMassOn_microcanonical`.

`HTGeometry/ComponentFormFactorExponentialLimit.lean` — `a_{d,m} → m!` and the `(m!)^c` product.
`HTGeometry/ComponentRecurrenceTorus.lean` — `phaseEmbed` (the recurrence torus embedding), its
injectivity/continuity/additivity, the orbit-closure identification, and the completed Haar law.

## Traps hit

1. **Umbrella name collision.** `tendsto_descFactorial_div_pow` already existed in
   `HTGeometry/EndpointChirpGlue.lean` (complex form, `(M+u).descFactorial j / M^j → 1`).
   `lake env lean` on a single file cannot see this; only `lake build <umbrella>` does, and it
   reports the collision through an auto-generated `._simp_1_3` name.  Grep every new top-level
   declaration name against the area before building.
2. **`Fintype.sum_prod_type` on big function types** blew the whnf heartbeat limit.  Reindex with
   `Equiv.piComm` on a single sum instead of pairing two sums, then use `Finset.prod_univ_sum` and
   `Fintype.piFinset_univ`.
3. `rw [someDef]` fails for definitions applied under a binder (`microcanonicalWeight`,
   `replicaFormFactorCoefficient`, `gapPhase`): use `simp only [someDef]`.
4. `omit [inst] in` must come **before** the docstring, not between docstring and `theorem`.
5. `Fin.tail_cons`/`Fin.cons_succ` fail to unify through an unreduced beta-redex in
   `Finset.card_nbij'` obligations; `simp` closes those goals.

## Concurrent-agent breakage fixed

`HTGeometry/ConstitutiveThreeRealizationPacket.lean` had a second
`mulVec_injective_of_det_ne_zero` (special case of the general one in
`HTGeometry/ExpandedEvaluationSampling.lean`), which broke the whole `HTGeometry` umbrella.
Fixed by marking the newer copy `private` — the minimal change that does not touch anyone's proof.
Prefer this over deleting another session's declaration.
