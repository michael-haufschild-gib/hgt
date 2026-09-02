# Failed mechanism: rooted pointing or label-retaining completion supplies selection

- **ID:** ULF-CITM-RPLC-FAIL
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** fresh corpus audit of actual fixed-left Big-Witt source rows
- **Statement:** Rooting the coherent cross-prime history does not construct the missing incidence; the source already supplies every fixed-left root, and retaining those root labels removes rather than proves the RH selection constraint.

## Goal tested

Use a distinguished source root to make the puncture in the coherent Big-Witt cross-pair fibre
canonical, preventing complete-fibre trace cancellation and producing the missing asymmetric
cross-cell incidence.

## Exact failure

`XiGammaSixWoldJordanSingularSourceDescent.lean` already constructs genuine normalized Big-Witt
rows for every fixed left prime.  Every such row disappears in the ambient edge Hilbert space and
converges in the one-leg graph completion to the same vertical generator, while the finite
Wold--Jordan reporter retains its left-prime value.

`XiGammaSixWoldJordanParametricVacuity.lean` proves the complete classification: an arbitrary
prime-labelled reporter descends through this scalar singular graph exactly when its coefficients
are constant along the prime enumeration.  The Wold--Jordan coefficient is only the free scalar
profile `A/p`; its descent is therefore equivalent to `A = 0`, and the Xi statement is merely the
pullback of that arithmetic-free classification.

Adding a label-retaining boundary coordinate would separate the rooted limits instead of
identifying them.  Then the reciprocal-prime profile is admissible for every scalar `A`; the
critical-line constraint disappears.  Root forgetting is selective but nonconservative, while
root retention is conservative but nonselective.

The next attempted repair—put the differences between roots in the source's complete-prime
Dirichlet form—is also already present.  `DeningerBigWittPrimeSeamDirichletTransport.lean` proves
that the literal Big-Witt atoms `1/(pq)` give exactly the reciprocal-prime pair energy, and
`XiPrimeSeamPairEnergy.lean` proves uniform boundedness exactly for constant prime potentials and,
on the Xi seam, exactly for RH.  Its missing premise remains the source-derived uniform upper
bound.

## No-go closure

- **Exact killing theorem/mechanism:**
  `primeLabelledActualSourceDescends_iff` classifies scalar descent as constancy;
  `woldJordanSourceDescent_parametric_vacuity` shows the Xi endpoint depends only on a free scalar;
  `deningerBigWittXiPrimeSeamSourceEnergyBounded_iff_riemannHypothesis` shows transition energy is
  already an RH-equivalent receiver.
- **Strongest positive survivor:** source rooting is genuine and canonical, but its completion
  collision should be retained as a *typed identification with transition data*, not repaired by
  either scalarization or a direct-sum label coordinate.  Any new mechanism must construct a
  source law controlling those transition data before the RH-dependent reporter is inserted.
- **New insight:** selection lives in the incompatibility between conservative provenance and
  label-forgetting descent.  Neither endpoint is missing; the missing datum is a source-generated
  law on the arrows that identify their completions.
- **Status:** killed unconditionally by existing Lean theorems; no new Lean module required.

## Log

- 2026-09-02 — created directly in Stage 5 after corpus audit found the complete rooted-source and
  prime-labelled descent classifications already formalized.
