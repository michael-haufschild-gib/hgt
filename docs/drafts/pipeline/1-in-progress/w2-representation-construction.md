# W2: arithmetic characters of symmetric groups

- **ID:** w2-representation-construction
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `docs/reports/review-0611/obstacles-summary.md`, W2.
- **Target:** Construct the arithmetic symmetric-group character from prime/theta data, prove its exact cycle values, and derive the existing unconditional RH equivalence without assuming positivity.

## Exact distinctions

Three consistency laws must be distinguished: restriction of characters along `S_n ⊂ S_(n+1)`, deletion of a label from random permutations, and Young-graph branching of irreducible multiplicities. The existing `PrimeCycleDeletionCoherence` classifies the second law, not the first. Sorted word multiplicities are not automatically Schur–Weyl shapes.

## Conjectures and proof obligations

1. An independent finite coloring gives a positive-definite class function by the probability that a permutation preserves every color. Prove positivity, restriction, and disjoint-support factorization from the coloring law; identify cycle values as power sums.
2. Mixing coloring frequencies preserves positivity and restriction, but its disjoint-cycle factorization defect is a covariance. Prove the exact variance obstruction and identify the deterministic survivor.
3. Test the sorted-multiplicity Young producer against branching at sizes two and three. Extract the correct representation-theoretic replacement if it fails.
4. Construct arithmetic coloring frequencies or an equivalent positive representation independently of zeros. Match every cycle value to the arithmetic logarithmic coefficients; finite-rank tests alone do not establish this identity.
5. Audit the coordinate and sign conventions connecting W2's `1/(ρ(1−ρ))` to the corpus centre PF criterion. Formalize the exact bridge, then the RH capstone only when its source input is proved.
6. Extend independent coloring to summable countable alphabets: finite-word products have total mass `(Σw)^n`; fixed-word sums are dominated by this mass; finite sums of stabilizer kernels are positive and their entrywise limit remains positive. Apply the construction to normalized positive endpoint real parts and identify its exact transposition discrepancy.
7. Define the prescribed cycles without zeros: put `F(X)=logDeriv xi(1/2+√X)/√X`. The cycle of length `n+1` has value `Re[(-1)^n F^(n)(1/4)/n!]/poleSharpConstant^(n+1)`. The corpus resolvent derivative identity proves exact agreement with the endpoint power sums. This defines arithmetic values, not a positive representation.
8. Identify the coloring character with the literal cycle-product class function on every permutation. Split invariant supports by `subtypeCongr`; transitivity makes fixed words constant on each cycle, and disjoint supports factor. This supplies the reverse direction of the full arithmetic character/RH equivalence from the existing positive endpoint family.
9. Distinguish stabilizing a partition from stabilizing each block. At rank two every partition is invariant under the transposition. At rank three its extension fails precisely when the fixed letter matches exactly one swapped letter. Predict a restriction discrepancy `2R`, with `R = Σ_(a≠b) w_a²w_b`. The survivor is blockwise stabilization, which is exactly the fixed-word character. On an infinite set with every occupied block infinite, a finitely supported permutation preserving the partition must fix each block: moving one block would put that entire infinite block in its finite support. This is the structural limit mechanism absent from finite unmarked stabilizers.
10. Test the gap between generic Hankel tests and full character positivity on `p_n=t^n`. All normalized pivot tests should be positive for `|t|≤1`, whereas full character positivity should quantize nonzero `t` to signed reciprocals of positive integers. The proposed detector is the alternating sum over `S_n`, with value `Π_(j<n)(1−jt)`. This is a separate conjecture; the endpoint equivalence uses the actual divisor and does not assert a generic converse.
11. Complete the countable curve calibration. The phase alphabet `1/(1/4+(Im ρ_(i,k))²)` is positive and summable by the corpus periodic-height bound. Its normalized coloring character exists for every nonempty curve datum. Coordinatewise identification with the actual endpoint alphabet should hold exactly for unitary Frobenius data; phase positivity alone forgets radial eigenvalue information.

## Current evidence

- `riemannHypothesis_iff_forall_pfSeq_centre` is an equivalence, not a positivity producer.
- `cycleWeight_eq_geometric_of_shapeBlind` concerns random-permutation deletion.
- Existing prime–theta Young and colored-cycle cards leave positive source weights, branching, and exact Xi identification open.
- `HTGeometry/SymmetricCharacters/FiniteColoring.lean`: positive-definite finite coloring characters, conjugation invariance, identity mass, disjoint-block multiplication, and normalized restriction are kernel-checked.
- `HTGeometry/SymmetricCharacters/MixtureRigidity.lean`: the exact variance defect and equality classification by positive-support alphabets are kernel-checked. The all-moment version includes moment zero; normalized character applications must separately account for moments zero and one.
- `HTGeometry/SymmetricCharacters/CharacterMixtures.lean`: positivity, restriction, exact double-cycle covariance, and alphabet rigidity are kernel-checked. Fixed alphabet cardinality supplies moment zero; cycle values supply every positive moment.
- The centered real-part construction already occurs in `PrimeArchThermalKrylovEquivalence`: its second moment exceeds the source by `xiThermalOrientationEnergy`, zero exactly under RH. The endpoint analogue must use `xiStripEdgeWeight` and its existing first and second sum rules; it is not a new positivity mechanism.

## Exact source tests

- **Occupancy versus Young branching:** for letter weights `w`, let `R = Σ_(a≠b) w_a² w_b`. The occupancy mass of `(2,1)` is `3R`; Young down-transition assigns half to `(2)`. Its row discrepancy is `R/2`, zero only when at most one letter has positive weight. `MultiplicityBranching.lean` is kernel-checked. The positive survivor is the independent-color character, not the sorted occupancy law.
- **Cycle formula:** a cycle of length `k` fixes precisely constant words, giving `Σ_a w_a^k`. `CyclicTrace.lean` also proves the product formula for disjoint cycle representatives.
- **Endpoint real-part candidate:** `RHTower/Representation/EndpointCharacterDefect.lean` is kernel-checked: absolute convergence, positive mass `2+γ−log(4π)`, exact gap `Σ(Re α)² − Re Σα² = Σ(Im α)²`, and equality iff RH. Dividing by the squared mass gives the exact normalized transposition defect.
- **Curve branch test:** `endpointCoordinate_im_eq_zero_iff` proves that `1/(s(1−s))` is real exactly on the critical line or real axis. `ArithmeticCastelnuovoSeveri/Representation/EndpointCalibration.lean` is kernel-checked: positive real endpoint weights over all periodic copies iff Frobenius purity; one first-period representative per eigenvalue suffices. `golden_endpoint_period_test` proves every principal golden weight is positive real while the first-period test fails.
- **Infinite alphabet:** `CountableColoring.lean` is kernel-checked: absolute convergence, normalized identity and restriction, conjugation, positivity, disjoint-block multiplication, and the complete cycle-product formula. `WordProducts.lean` supplies the independent-word mass identity.
- **Literal cycle identification:** `CycleCharacterIdentification.lean` is kernel-checked: invariant-support splitting and disjoint-cycle induction identify the fixed-word character with the cycle-product class function on every finite symmetric group. The resulting literal cycle family is positive.
- **Positive endpoint character:** `PositiveEndpointCharacter.lean` is kernel-checked. Normalized endpoint real parts give a positive coherent family at every finite rank. Its transposition gap is `xiEndpointOrientationEnergy / xiEndpointColorMass²`; matching the prescribed transposition, or matching every prescribed cycle value, is equivalent to RH. This construction uses the divisor and does not furnish an independent arithmetic producer.

## Primary-source check

Simon Thomas, [Characters and invariant random subgroups of the finitary symmetric group](https://ow3.math.rutgers.edu/~sthomas/Fin-chars.pdf), §1: fixed-point probabilities give characters; the pure row Thoma character is the product of color power sums. These are classical foundations, not novelty claims.

## Exact character-to-moment receiver

Cycles with a common pivot and otherwise disjoint supports have a product cycle of combined length minus one. Replicating each arm gives a Gram matrix
`G_N((i,a),(j,b)) = H_ij + δ_((i,a),(j,b))(1−H_ii)`, where `H_ij = p_(r_i+r_j+1)`.
`ReplicatedKernel.lean` proves the exact classification: every `G_N` is positive semidefinite iff `H` is positive semidefinite and `H_ii≤1`. Constant block vectors give `N²Q_H(v)+NΣ_i(1−H_ii)v_i²`; differences of two replicas give the diagonal upper bound. The exact finite threshold for a negative test is `NQ_H(v)+Σ_i(1−H_ii)v_i²<0`. All three statements are kernel-checked.

`CommonPivotCycles.lean` is kernel-checked: the literal cycle-product class function on finite symmetric groups has exactly these Gram matrices, using independently tagged arms and one pivot. Thus character positivity implies every Hankel test without invoking Thoma classification.

The existing `riemannHypothesis_iff_forall_xiResolventHankelMatrix_posSemidef` applies at shift `1/4`: its reciprocal spectral coordinate is exactly `xiStripEdgeWeight`. Normalization of cycle values is an invertible positive diagonal congruence of these Hankel matrices. `EndpointHankelReceiver.lean` is kernel-checked: both the common-pivot tests and positivity of the full arithmetic cycle family are equivalent to RH. `EndpointArithmeticMoments.lean` identifies the same values from arithmetic jets without using the divisor in their definition. Neither receiver supplies the arithmetic positivity producer.

## Completion gates

- [x] Finite coloring representation, positivity, restriction, cycle formula.
- [x] Mixture covariance and deterministic survivor.
- [ ] Young-shape producer audited and corrected.
- [x] Curves and fake models tested symbolically.
- [x] Countable coloring character and actual positive endpoint application.
- [x] Canonical arithmetic cycle function: positivity is equivalent to the existing RH moment criterion.
- [ ] Arithmetic source representation and exact character identification.
- [ ] RH conclusion kernel-checked; direct leaf checks and imports complete.

No numerical experiments are used. No RH-strength input may enter a theorem as an unproved premise.
