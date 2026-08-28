# JAS ell-two amplified prime-Poisson superselection

- **ID:** JAS-L2APPS-1
- **Stage:** 3-formalized
- **Type:** THEOREM / HARD ROUTE-CLASS FALSIFIER
- **Source:** read-only `rh-current-frontier-map.md`, JAS `ORIENT + COMP` open core

## Hard frontier target

JAS and RFHM retain arbitrarily many valuation, compound, and finite-prime-support channels. A
naive cofinal completion places those channels as Hilbert multiplicities beside the ordinary-prime
`C(PrimeTorus)` representation. Determine whether this amplification can create a reflected
source-linear sewing that is absent in each prime-Poisson fibre.

For arbitrary Hilbert spaces `H1`, `H2`, index family `A`, `B`, and multiplicity type `Gamma`, form
the diagonal actions on `ell2(Gamma, H1)` and `ell2(Gamma, H2)`. The formal theorem package proves:

1. `OperatorFamiliesDisjoint A B` implies disjointness of both amplified families;
2. reflected prime-Poisson amplification has a nonzero closed densely-defined
   `C(PrimeTorus)`-linear sewing iff `sigma = 1/2`;
3. on the wall, actual completed-theta grade norms mark a nonzero linearly independent countable
   packet family in the amplified carrier.

Consequently every diagonal/separable prime x grade completion is terminal: multiplicity,
countably many valuation depths, and finite compounds cannot evade off-wall superselection. JAS
then requires genuinely nonseparable prime--grade incidence whose `C(PrimeTorus)` action mixes the
completion coordinates. C3 is the mandatory positive survivor.

## Corpus basis

All conjecture-forming searches used `scripts/formal_tools.py research`. Corpus provides:

- `OperatorFamiliesDisjoint`, defined by vanishing of bounded intertwiners in both directions;
- exact prime-Poisson reflected sewing iff `sigma = 1/2` before amplification;
- `ell^p` coordinate-single density and continuous-map extensionality;
- actual completed-theta all-grade nonvanishing and `L2` linear independence;
- faithful finite-support/history RFHM packets, but no amplified disjointness theorem.

The block-matrix proof is forced by corpus structure: every coordinate projection of an amplified
intertwiner is a base intertwiner, hence zero; density of coordinate singles then kills the whole
operator. No spectral theorem or zero data is inserted.

## Conjecture loop and resolution

### C1 — arbitrary ell-two amplification stability — PROVED

Bounded coordinatewise amplification, coordinate injections, projections, and adjoint covariance
are constructed. Every amplified intertwiner has all matrix coefficients zero; coordinate-single
density kills the whole operator for arbitrary multiplicity type.

### C2 — reflected prime-Poisson exact wall — PROVED

Applying C1 to corpus mutual-singularity disjointness proves that a countably amplified nonzero
closed densely-defined source-linear sewing exists exactly when `sigma = 1/2`.

### C3 — completed-theta source-marked survivor — PROVED

The `r`-th coordinate single is weighted by the nonzero norm of actual completed-theta grade `v_r`.
The full countable packet family is linearly independent and supplies a nonzero critical diagonal
sewing witness.

## Lean artifacts

- Generic module: `GaloisForLFunctions.HTGeometry.L2OperatorFamilyAmplificationDisjointness`
- JAS module: `GaloisForLFunctions.RHTower.JointAncestryAmplifiedPrimePoissonSuperselection`
- `operatorFamiliesDisjoint_l2Amplification`
- `adjoint_l2Amplification`
- `primePoisson_reflection_nonzeroClosedSourceLinearSewing_l2Amplification_iff`
- `linearIndependent_jointAncestryCriticalPrimeThetaGradePacket`
- `jointAncestryCriticalPrimeThetaGrade_sourceLinearSewing`

## Route consequence

Countable Hilbert multiplicity is not the missing JAS completion mechanism. It cannot mix prime and
valuation/compound coordinates, and it preserves the exact off-wall superselection obstruction.
This kills at once all diagonal direct-sum, separable tensor-with-trivial-grade-action, and
coefficient-blind multiplicity completions covered by the amplified representation. Surviving JAS
must change the `C(PrimeTorus)` action itself through genuinely nonseparable prime--grade incidence;
merely adding infinitely many faithful RFHM channels cannot work.

## Hostile falsification

1. Arbitrary multiplicity type, not fixed finite rank.
2. Closed densely-defined relations, not bounded intertwiners alone.
3. Actual `C(PrimeTorus)` prime-Poisson representation.
4. Actual completed-theta grade nonvanishing in positive survivor.
5. No Xi zero, RH premise, numerical computation, new axiom, or compact cutoff.

## Novelty audit

The abstract fact that disjoint representations remain disjoint under multiplicity is compatible
with standard operator-algebra representation theory and is not claimed as literature-level novelty
by itself. Targeted literature searches found work on induced/amplified Hilbert-module
representations, but no prime-Poisson/reflection theorem tied to completed theta, JAS grades, or an
RH source-linear sewing classification. The new route-specific knowledge is the exact countably
amplified prime-Poisson wall plus actual completed-theta independent critical survivor. This is a
targeted no-match audit, not a proof of global absence from literature.

`[PROVED HERE] [LEAN CLOSED] [INTERNAL SEARCH COMPLETE] [TARGETED EXTERNAL NO-MATCH AUDIT]`

## Formal audit

- Both modules passed `lake env lean <file>`.
- Exact leaf builds passed for both modules; no umbrella or full build was run.
- Axiom probes for generic disjointness, exact amplified wall, independent source packets, and
  critical sewing report only `propext`, `Classical.choice`, and `Quot.sound`.
- Formal lint reports no error involving either module and no forbidden declaration; repository-wide
  exit remains nonzero from unrelated concurrent umbrella-reachability failures.
- Both modules are wired into their umbrellas; frontier map remained read-only.

## Log

- 2026-08-28 — selected after all-grade completed-theta Mellin chain closure. Frontier map read-only.
  Target derived from exact corpus search no-match for disjointness under Hilbert multiplicity.
- 2026-08-28 — C1--C3 proved in Lean. Diagonal/separable JAS completion retired with actual
  completed-theta critical survivor; promoted to `3-formalized`.
