# KMSS source transposition isotypic classification

- **ID:** KMSS-STIC
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** `rh-current-frontier-map.md` · route KMSS (read-only ledger)
- **Statement:** The actual all-prime Calderón--Witt cup has a canonical coefficient-faithful sign-character lift of every complex scalar, whereas a trivial-character lift exists exactly for the zero scalar; for the Xi mixed jet, trivialization is exactly nodal superselection.

## Goal

Separate source existence from orientation erasure in KMSS.  Prove unconditional source production in the correct transposition representation, identify the exact character mismatch that kills order-blind descent, then test whether a literal source symmetry canonically identifies the Koszul transposition with theta half-density deck spin.  No numerical estimate or divisor-specific assumed lift is allowed.

## Gates

- [x] 0 → 1 in-progress: current KMSS open core audited; source-pure section and skew law found; attack is an `S₂` isotypic classification.
- [x] 1 → 2 fully-proven: dependency-closed classification and hostile source-level no-go.
- [x] 2 → 3 formalized: Lean theorem `deningerCalderonWittKoszulTranspositionClassification`, targeted `lake build`, and axiom audit green.
- [ ] 3 → 4 publication-ready: external novelty audit and standalone proof.

## Corpus basis

- `DeningerCalderonWittMilnorIncidence.lean`: explicit one-prime global exterior-cup section and exact section law.
- `DeningerCalderonWittOrientedSource.lean`: coefficient-faithful global center-orientation section and trace retraction.
- `XiKoszulMutualStatisticsSuperselection.lean`: opposite cups cannot both represent one order-blind scalar unless the Xi mixed jet vanishes.
- `XiSourceSpinThinningCoherence.lean`: literal theta source has half-density monodromy `-1`; centered Xi deformation preserves it exactly on the critical line.

## Conjecture loop

### C1 — source transposition classification

For any prime `p` and scalar `c : ℂ`, use the explicit cup section to construct legs `g_p` and `h_{p,c}` with traced cups `c` and `-c`.  Prove the ordered source cup is nonzero exactly when `c ≠ 0`.  Independently classify lifts for which both orders trace to `c`: they exist iff `c = 0`.

- **Status:** proved in `XiKoszulSourceTranspositionClassification.lean`.  The stronger theorem `nonempty_deningerCalderonWittKoszulCharacterLift_iff` classifies every scalar transposition multiplier `χ`: a lift exists exactly when `(χ + 1) * c = 0`.
- **Novelty boundary:** alternating sign representation is classical.  Candidate new result is its exact coefficient-faithful realization and exhaustive source-lift classification in the all-prime Calderón--Witt RH object.

### C2 — diagonal Koszul/theta sign cancellation

Conjecture that source construction supplies a canonical identification between source-leg transposition and one logarithmic turn of the literal theta half-density.  Under diagonal action, the two sign characters cancel.  Test whether this identification follows from existing source functoriality or is an additional RH-strength premise.

- **Status:** falsified.  `deningerCalderonWittKoszulThetaSpinCompensation_universal` proves that multiplying reverse order by a second `-1` sign restores the coefficient for every scalar.  This diagonal cancellation is unconditional and therefore cannot select the critical line.
- **Failure criterion:** if corpus exposes no naturality square connecting transposition to deck transport, record exact independence no-go and retain C1 as positive survivor.

## No-go closure

- **Exact killing theorem/mechanism:** `not_nonempty_deningerCalderonWittOrderBlindCoefficientFaithfulCompletion` proves no linear scalar completion can be both invariant under source-leg transposition and coefficient-faithful on even one prime orientation section.  Skewness forces opposite values; faithfulness fixes them as `1` and `-1`.
- **Strongest positive survivor:** Every scalar has an explicit coefficient-faithful sign-character source lift.  Its source cup is nonzero exactly when the coefficient is nonzero.  For the Xi mixed jet, the canonical cup vanishes exactly on the critical line, and universal vanishing at any fixed prime is exactly RH.
- **New insight:** KMSS `LAND` was not missing.  Its proposed `ORIENT` operation is impossible if “functorial” includes source-leg swap and the scalar target is order blind.  Twisting target by sign repairs descent universally and loses all RH selectivity.  Any surviving route must retain an ordered/orientation-valued target or introduce a non-equivariant fixed-orientation source law; neither is supplied by KMSS.
- **Status:** retired as stated.  Positive survivor formalized in `formal/GaloisForLFunctions/RHTower/XiKoszulSourceTranspositionClassification.lean`; leaf `lake env lean` and `lake build` pass; `scripts/check_axioms.sh` audits five capstones with only `[propext, Classical.choice, Quot.sound]`.  Global lint finds unrelated concurrently unwired modules, while this leaf is wired into `GaloisForLFunctions.RHTower` and contains no forbidden declaration.

## Literature audit

Searches through 2026-08-28 found no external paper defining this source-specific all-prime Calderón--Witt cup or proving its transposition-character classification.  Nearest primary literature concerns rational Witt-vector geometry ([Deninger 2025](https://arxiv.org/abs/2508.05329)), the semilocal scaling Hamiltonian ([Connes--Consani 2019](https://arxiv.org/abs/1910.14368)), and the BC-system as a universal Witt ring ([Connes--Consani 2021](https://arxiv.org/abs/2112.08820)); none supplies the claimed KMSS producer.  Alternation and the abstract sign/trivial representation obstruction are classical, so novelty is restricted to the exact coefficient-faithful realization and no-go for this corpus-defined RH source.  Search-negative status is not a substitute for independent expert novelty review.

## Log

- 2026-08-28 — Created directly in 1-in-progress after current frontier audit.  Rejected numerical optimization; selected structural source/transposition problem.
- 2026-08-28 — C1 proved and formalized.  C2 sign-cancellation conjecture failed by an unconditional universal compensation theorem.  Stronger coefficient-faithful order-blind completion was proved impossible; card retired with formalized positive survivor.
