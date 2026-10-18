# Integer affine shear: coefficient recovery modulo compact operators

- **ID:** wall14-integer-affine-shear-size
- **Stage:** 3-formalized
- **Type:** THEOREM (paper; Lean audit in progress)
- **Source:** read-only Wall 14; `SuccessorSequenceHilbert.lean`, `CoprimeShearAndMultiplicativeGraphUncertainty.lean`, `PhysicalAffineAction.lean`, `PhysicalAffineSharpNorm.lean`.
- **Statement:** The actual integer successor–dilation commutators retain every absolutely summable scale coefficient modulo compact operators.

## Goal and scope

Develop the size law for the mixed additive/multiplicative action itself. This is field research, without zeta, zeros, or an RH claim. The general all-walls objective remains active. Both field READMEs and the walls ledger are read-only.

On H = real l2(N), let S e_n = e_(n+1), V_d e_n = e_((d+2)n), and C_d = S V_d - V_d S. For a real l1 sequence a, construct T_a = sum_d a_d C_d in operator norm. Investigate:

1. Exact columns C_d e_n = e_((d+2)n+1) - e_((d+2)(n+1)).
2. For every d and n >= d+2, the two indicated coordinates of T_a e_n are exactly a_d and -a_d.
3. For every compact K, the corresponding coordinates of (T_a-K)e_n converge to a_d and -a_d. Hence T_a is compact iff a=0; equality modulo compact operators recovers the whole coefficient sequence.
4. Quantitative positive survivor: every finite set F of scale labels obeys 2 sum_(d in F) a_d^2 <= norm(T_a-K)^2. Operator norm is bounded above by 2 norm(a)_1. This retains nonzero coupling size after arbitrary compact corrections.

The single-scale residue identity is supporting infrastructure, not the main contribution. General-lag resonance and weighted-column compactness are separate possible successors, not claimed here.

## Dependency-closed paper proof [PROVED HERE]

Each V_d is the isometry induced by the injection n |-> (d+2)n. Its adjoint is the literal multiplicative pullback; S's adjoint is the already constructed successor pullback. Thus C_d is the adjoint, up to sign, of the discrete shear already present in the field.

Since S and every V_d are isometries, norm(C_d) <= 2. Hence sum_d norm(a_d C_d) <= 2 sum_d abs(a_d) = 2 norm(a)_1. Completeness constructs T_a in operator norm and proves its stated upper bound. Linearity gives T_(a-b)=T_a-T_b.

If n >= d+2, no scale e can make (e+2)(n+1) = (d+2)n+1. For e>=d the left side is larger; for e<d the gap (d-e)n exceeds e+1. Also (e+2)n+1 = (d+2)n+1 forces e=d. For the other endpoint, equality (e+2)n+1=(d+2)(n+1) would require (e-d)n=d+1: e<=d is impossible, and e>d implies the left side is at least n>=d+2. Equal negative endpoints force e=d. Bounded coordinate evaluation commutes with the norm-convergent l1 operator series, giving both exact readouts.

Compact operators send the standard orthonormal sequence to zero in norm: every image subsequence has a norm-convergent subsequence by compactness, while its weak limit is zero because the input basis is weakly null and the adjoint preserves the weak pairings. Thus each cluster limit is zero. This general lemma already exists in `HTGeometry/ObserverHorizonStability.lean` and its proof was inspected.

Coordinate absolute value is bounded by the vector norm, so compact corrections vanish in every moving coordinate. For a fixed finite scale set F, all its two output coordinates are distinct once n >= sum_(d in F)(d+2). Bessel's inequality bounds the sum of the squares of those coordinates of (T_a-K)e_n by norm((T_a-K)e_n)^2 <= norm(T_a-K)^2. Each coordinate tends to a_d or -a_d; the finite sum therefore tends to 2 sum_(d in F) a_d^2. This proves the quantitative bound. If T_a is compact, take K=T_a or use either readout to deduce every a_d=0. Conversely a=0 produces the zero compact operator. Applying the result to a-b gives compactness of T_a-T_b iff a=b. No unproved cancellation estimate is used.

New field insight: absolute summability of scale coefficients does not suppress their infinite spatial multiplicity. The complete signed scale data remain visible modulo compact perturbations. This supplies a concrete noncompact mixed-action family; it does not identify an arithmetic spectral model or close the full Wall 14 size law.

## Corpus audit

- Ran documented hybrid searches `additive successor dilation commutator noncompact` and `coprime shear multiplicative shift Hilbert operator compact` (the second filtered to BiScaleUncertainty). Inspected returned declarations, candidate lemmas and source arguments. Raw evidence: `/tmp/bsu-wall14-shear-frontier.json`, `/tmp/bsu-wall14-shear-field.json`.
- Both searches are partial: retrieval/reranking interrupted by local runtime deadline; coverage snapshot is older and semantic completeness is unavailable. Useful hits were retained, not treated as a novelty certificate.
- Exact lexical `successor dilation` returned 12 declarations, none the proposed sequence-operator result (`/tmp/bsu-wall14-exact-frontier.json`). Direct field source searches found existing continuum affine norms, discrete telescoping, coprime projection commutators and sequence shifts.
- Existing physical affine norm and projection-angle results must not be counted again. No external novelty claim is made.
- Follow-up lexical `integer shear compact` returned seven declarations in `HTGeometry/CompactShearDescent.lean`. Source inspection shows these classify compact families invariant under affine integer translations, not successor/dilation operators on l2. Raw evidence: `/tmp/bsu-wall14-integer-compact-lexical.json`.

## Persistent plan

1. [complete] Dependency-closed paper proof; general compact-basis decay reused. API probe r4 and both arithmetic separation lemmas passed without errors/warnings (`/tmp/bsu-wall14-shear-api-r4.log`).
2. [complete] Three field modules Lean-verified without warnings: `IntegerAffineShear`, `SummableIntegerAffineShear`, `IntegerAffineShearCompactness`.
3. [complete] All 26 public signatures and axiom closures audited. Exact signed coefficient readouts, compactness classification, and finite-energy lower bounds verified.
4. [complete] Final named-leaf check, umbrella wiring, index/discoverability, lint, memory, and scratch archival complete; verification manifest retained. No full builds, no heartbeat increases, no numerical experiments.

`update_plan` is unavailable in this session; this card is the durable task tracker. One owned foreground Lean process at a time. Other worktree changes are concurrent and must be preserved.

## Formal result and verification

The namespace is `GaloisForLFunctions.BiScaleUncertainty.IntegerAffineShear`.
`State` is the existing real sequence Hilbert space; `Weights` is actual real `lp` at exponent 1.
The three source modules export 11, 8, and 7 public declarations respectively.
`series_single_plus` and `series_single_minus` recover each signed coefficient for every `n ≥ d+2`, with all infinitely many scales active.
`series_compact_iff` and `series_sub_compact_iff` classify zero and equality modulo compact operators.
`finite_coefficient_energy_le` gives the quantitative positive survivor for every finite coefficient set and every compact correction.

- Each named source leaf passed `lake --old env lean -j 1`; the final direct check of `GaloisForLFunctions/BiScaleUncertainty/IntegerAffineShearCompactness.lean` exited 0 with an empty diagnostic log. No umbrella build was run.
- All 26 full signatures and `#print axioms` outputs were inspected. Axiom dependencies are subsets of `propext`, `Classical.choice`, and `Quot.sound`; no added axiom or proof gap occurs. Evidence: `/tmp/bsu-wall14-signatures-axioms.log` and `/tmp/bsu-wall14-axiom-audit.json`.
- All three imports are wired once into the field umbrella. `scripts/formal_tools.py index` refreshed exactly three changed source modules. Complete paginated lexical discovery recovered all 26 public exports: `/tmp/bsu-wall14-discovery-check.json`.
- Global `scripts/formal_tools.py lint` exited 1 for six unreachable modules outside this package: `SuzukiCriticalBetaKernel`, `ClampedRampLatticeSum`, `FactorialMuntzBoundaryPole`, `FactorialMuntzBoundaryRepair`, `StationaryResolventMarkovPositivityAndNodalDefectProducer`, and `SharpInitialPrefixObservabilityAndExactGramDeterminants`. It reported no diagnostic for these three modules. Full evidence: `/tmp/bsu-wall14-lint-summary.json` and `/tmp/bsu-wall14-lint.log`.
- Source hashes and check records: `/tmp/bsu-wall14-manifest.json`. Nine obsolete probes and failed or warning-bearing logs were safely archived in `/tmp/bsu-wall14-retired`; final evidence remains available.

This is a concrete infinite-dimensional mixed-action size theorem. It does not establish an arithmetic spectral realization, exact essential norm, or Wall 14 closure. Initial hybrid corpus coverage was partial; no external novelty claim is made.

## Gates

- [x] 0 -> 1: concrete objects, source-pure mechanism, relation to selected wall.
- [x] 1 -> 2: dependency-closed paper proof and bounded corpus audit; no external novelty claim.
- [x] 2 -> 3: all statements Lean-verified, direct leaf and full axiom audits, imports wired. Global lint limitations recorded above.
- [ ] 3 -> 4: standalone publication audit.

## Log

- 2026-10-18: rotated from completed Wall 13 sharp Gram threshold to Wall 14. Selected cofinal recovery of all summable scale coefficients, rather than another single-scale noncommutation statement.
- 2026-10-18: formalized the complete three-module package. New insight: absolute summability across scales controls boundedness but does not remove infinite spatial multiplicity; every nonzero coefficient survives every compact correction. Wall 14 remains open.
