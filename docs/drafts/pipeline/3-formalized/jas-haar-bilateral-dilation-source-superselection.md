# JAS Haar bilateral dilation source superselection

- **ID:** jas-haar-bilateral-dilation-source-superselection
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** corpus-derived JAS positive survivor after prime-coordinate toggle and nilpotent-landing no-go theorems
- **Statement:** `[PROVED HERE]` For `0 < σ`, a nonzero closed densely defined single-valued `C(PrimeTorus)`-linear sewing from the prime-Poisson multiplication representation at `(σ,t)` to the Haar multiplication representation exists exactly when `1/2 < σ`.

## Goal

Classify the canonical oriented bilateral completion exposed by the JAS Boolean-toggle no-go.  The
unweighted bilateral shift has Haar joint spectral law, so its source-linear landing is precisely a
Poisson-to-Haar multiplication-representation sewing.  The theorem must decide that landing at the
critical wall before further creator-compression work is attempted.

Exact RH contribution chain:

`oriented coefficient-faithful bilateral landing`
→ `literal Gamma-theta creator obtained by Boolean compression`
→ `prime-support/grade-synchronized source coefficients`
→ `divisor-independent Xi prime-Poisson reflection sewing`
→ `xiPrimePoissonReflectionSewing_iff_internalOnly`
→ `xiDivisorSyndromeIsInternalOnly_iff_re_eq_half`
→ RH.

This card attacks the first arrow.  Failure at `σ = 1/2` kills the canonical unweighted Haar
bilateral completion before any coefficient or Xi assembly.  The positive `σ > 1/2` half identifies
the only survivor: a measure-class half-density transport, which must be altered at the wall rather
than extended there.

## Corpus origin and novelty gate

All conjecturing inputs came from `scripts/formal_tools.py research` searches, not remembered
literature:

- `primePoissonMeasure_mutuallyAbsolutelyContinuous_torusHaar_iff`: exact threshold `1/2 < σ`.
- `primePoissonMeasure_mutuallySingular_torusHaar_of_le_half`: wall and left side are singular.
- `continuousL2Mul_operatorFamiliesDisjoint_of_mutuallySingular`: singular measures give disjoint
  continuous multiplication representations.
- `closedDenseSingleValuedRelation_mem_iff_output_eq_zero_of_disjoint`: disjoint families forbid a
  nonzero closed densely defined single-valued relation.
- `weightedDensityUnitary`: positive-density square-root transport between weighted and unweighted
  `L²` spaces.
- `probabilityMeasure_ext_of_infiniteTorusFourier_integral_eq`: joint Fourier moments determine the
  infinite-torus spectral law.
- Searches for `NonzeroClosedSourceLinearSewing unitary intertwiner graph`, `continuousL2Mul
  mutually absolutely continuous measure sewing`, and `densityLinearIsometryEquiv intertwines
  multiplication weighted L2` found no general positive sewing theorem.

Targeted literature searches for multivariable unitary dilation vacuum Haar laws and closed
intertwiners of multiplication representations found standard dilation and measure-class theory,
but no theorem coupling the prime-Poisson critical threshold to this JAS closed-relation landing.
Global novelty remains unverified; exact route theorem is corpus-novel.

## Gates

- [x] 0 → 1 in-progress: well-posed, corpus-derived, exact RH chain, attack and falsifier fixed
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: Lean theorem, exact leaf build green, axiom audit clean
- [ ] 3 → 4 publication-ready: standalone theorem/proof/Lean certificate/novelty audit

## Approach

1. Prove generic graph infrastructure: a continuous linear equivalence intertwining two operator
   families yields `NonzeroClosedSourceLinearSewing` when target space is nonzero.
2. Repair the Radon–Nikodym derivative on its null exceptional set to an everywhere positive finite
   real density without changing the weighted measure.
3. Use `weightedDensityUnitary` and prove it intertwines every continuous multiplication operator.
4. For `1/2 < σ`, the corpus measure-class theorem supplies both absolute-continuity directions and
   hence the unitary sewing.
5. For `σ ≤ 1/2`, singularity plus closed-relation splitting forces every output to vanish,
   contradicting nonzero sewing.

The early falsifier did not fire: repaired density gives an exact `L²` unitary intertwiner.  Lean
forced an explicit everywhere-positive finite repair of the Radon--Nikodym derivative before the
existing square-root unitary could apply.

## No-go closure

- **Exact killing theorem/mechanism:** `primePoisson_haar_nonzeroClosedSourceLinearSewing_iff`.
  At and left of the wall, prime-Poisson and Haar are mutually singular; continuous multiplication
  families are disjoint; closed densely defined single-valued invariant relations have zero output.
- **Strongest positive survivor:** For every `σ > 1/2`, repaired Radon--Nikodym half-density gives an
  explicit unitary multiplier intertwiner and hence a nonzero closed sewing.  More generally,
  `continuousL2Mul_nonzeroClosedSourceLinearSewing_of_mutuallyAbsolutelyContinuous` proves this for
  any equivalent finite measures with nonzero target `L²`.
- **New insight:** canonical unweighted bilateral creator completion is governed by global joint
  measure class, not local prime-coordinate atomlessness or invertibility.  It exists throughout the
  open right half-plane but fails exactly where the RH endpoint needs it.  Critical JAS must retain a
  Poisson-weighted oriented dilation; Haar transport cannot be continued to the wall.
- **Status:** `[PROVED IN LEAN] [CORPUS-NOVEL ROUTE THEOREM] [TARGETED EXTERNAL NO-MATCH]
  [GLOBAL NOVELTY UNVERIFIED]`.  Module
  `GaloisForLFunctions.RHTower.JointAncestryHaarBilateralDilationSourceSuperselection`; exact leaf
  build succeeded (`12129/12129`); all audited declarations use only `propext`, `Classical.choice`,
  and `Quot.sound`.  Formal lint reports only pre-existing large-file and umbrella-reachability
  findings.

## Log

- 2026-08-29 — created directly in 1-in-progress after corpus search fixed conjecture, RH chain,
  attack, and early falsifier.
- 2026-08-29 — paper proof closed; Lean formalization and leaf build completed; moved to
  3-formalized.
