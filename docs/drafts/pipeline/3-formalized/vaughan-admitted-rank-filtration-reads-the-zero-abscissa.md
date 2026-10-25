# The Vaughan coefficient rank filtration reads the zero abscissa

- **ID:** vaughan-admitted-rank-filtration-reads-the-zero-abscissa
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Verification:** All twelve targets passed the final direct Lean check. Transitive axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- **Source:** ../1-in-progress/q-i-selective-square-root-band.md
- **Statement:** For every fixed pair of cutoffs, the damping set where the admitted Vaughan coefficient space acquires its receiver direction equals the actual receiver damping set. The lower accumulation boundary is exactly `zetaZeroAbscissa-1/2`.
- **Novelty status:** Exact finite-family realization of existing receiver index laws; no external novelty claim.

## Rank detects precisely the original receiver

Let `D_ε(U,V)` be the subspace of coefficients whose actual Vaughan packet has bounded
pronic norm over every horizon. Put

`b(U,V)=2` if both cutoffs are positive, and `b(U,V)=3` otherwise.

The lower-half classification, zero-cutoff boundary, and half-damping phase law give,
for every `ε>0`,

`b(U,V)+1 ≤ dim D_ε(U,V)  ↔  the actual interior receiver is admitted at ε`.

Below half damping this is exactly the two possible dimensions already classified.
At half damping the dimension is three at positive cutoffs and four at zero cutoffs;
the source receiver is admitted there. Above half damping the dimension is four for
all cutoffs, and the source receiver is again admitted.

Consequently the set

`R_(U,V)={ε>0 : b(U,V)+1 ≤ dim D_ε(U,V)}`

equals `interiorReceiverDampings`, which equals `receiverDampings` by the checked
`interiorReceiverDampings_eq_receiverDampings` theorem. Energy admission and pronic-norm
admission agree because the energy is the squared norm. All cutoff pairs therefore
give the same set, despite their different pointwise coefficient dimensions.

## Existing analytic index transfers exactly

Substitute this set identity into the checked theorem
`sInf_derivedSet_interiorReceiverDampings_eq_zetaZeroAbscissa_sub_half` to obtain

`inf derivedSet R_(U,V) = zetaZeroAbscissa - 1/2`.

In particular, a fixed zero-free strip is equivalent to
`inf derivedSet R_(U,V)<1/2`. The checked
`riemannHypothesis_iff_accPt_zero_receiverDampings` gives

`RH ↔ 0 is an accumulation point of R_(U,V)`.

Equivalently, for every `δ>0` there is `0<ε<δ` with
`b(U,V)+1≤dim D_ε(U,V)`, by the existing cofinal-budget criterion. Under RH this rank
inequality holds at every positive damping, since every positive damping is admitted.
Conversely that inequality at every positive damping gives the cofinal condition by
taking `ε=δ/2`; thus the all-positive-damping formulation is also an equivalence.

These exact substitutions supply a concrete five-coefficient version of the corpus's
payment-index viewpoint. It does not turn admission into a finite test: `D_ε(U,V)` is
defined by boundedness over all horizons, and its additional direction is precisely
the original, unresolved interior receiver.

## Lean declarations

The extra rank also equals square summability of the actual first centered
damping-chain column, equivalently every centered column. All statements are
checked in `BezoutValuationIncidence/TheVaughanAdmissionRankReadsTheZeroAbscissa.lean`:

- `pmPronicVaughan_extra_rank_iff_receiver`
- `exists_pronicNorm_interior_bound_iff_energy_bound`
- `pmPronicVaughanRankDampings_eq_interiorReceiverDampings`
- `pmPronicVaughanRankDampings_eq_receiverDampings`
- `pmPronicVaughanRankDampings_eq`
- `sInf_derivedSet_pmPronicVaughanRankDampings`
- `zetaZeroAbscissa_lt_one_iff_vaughan_rank_boundary`
- `riemannHypothesis_iff_accPt_zero_vaughan_rank`
- `riemannHypothesis_iff_cofinal_vaughan_rank`
- `riemannHypothesis_iff_forall_pos_vaughan_rank`
- `pmPronicVaughan_extra_rank_iff_first_column_summable`
- `pmPronicVaughan_extra_rank_iff_all_columns_summable`

The module is imported by its programme umbrella. Its final direct check and
all twelve `#print axioms` audits passed, including the endpoint, upper-half,
zero-cutoff, and analytic-index dependencies. These exact equivalences supply
no new receiver admission or fixed strip; full Q-I remains open.
