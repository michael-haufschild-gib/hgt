# Finite Weil quadratic tilt equality and finite witnesses

Status: formalized and natively audited (2026-10-12).

## Objective and corpus evidence

Replace equality of the actual finite tilted probability measures by an explicit
finite condition on their quadratic potentials. Then replace the measure-level
condition in fast replication and the complete replication spectrum by finite
point witnesses. Only local Lean sources provide mathematical evidence.

The scoped WeilLogShift quadratic-tilt/equality query returned no declarations.
The four HTGeometry tilt/equality and two tilted/constant records do not provide
this criterion. Exhaustive local source search for tilted equality iff found no
matching probability-measure theorem. Existing TiltedRelativeEntropy and Mathlib
Tilted provide exact log-density identities, tilt composition, and constant-tilt
invariance. WeilLogShiftObservableLaw represents the canonical law as a finite
atomic probability measure; every canonical edge mass is strictly positive.

## Dependency-closed proof

1. For a probability measure mu and exponentially integrable real potentials f,g,
   mu.tilted f = mu.tilted g iff f-g is mu-almost-everywhere constant. Forward:
   equality identifies their log Radon-Nikodym derivatives; subtract the two
   existing log-density formulas. Backward: replace f by g+c almost everywhere,
   use tilt composition, and use invariance under a constant tilt.
2. For every canonical observable law, a predicate holds almost everywhere iff
   it holds at every source atom. Express the measure as its finite positive
   weighted Dirac sum. This needs no measurability assumption on the predicate
   and no injectivity assumption on the observable (measurable singletons suffice).
3. For all finite r,k and all six real coefficients, equality of the quadratic
   tilted laws is equivalent to constancy, across i:Fin(r+1), of
   Q(a-A,b-B,d-D)(finiteWeilCanonicalFluctuationPoint r k i).
   Fin(r+1) has the distinguished atom 0, so this is equivalent to every value
   equalling its value at atom 0. Negation gives one explicit atom whose value
   differs from that anchor, avoiding a second existential index.
4. Substitute this equivalence into the previously verified fast-separation
   criterion and complete replication spectrum. All analytic assumptions are
   discharged at actual-law roots. The finite equality and fast criterion allow
   arbitrary depth schedules and all real coefficients; the full spectrum keeps
   its existing subcritical domains and canonical-depth assumptions.

## Plan

1. Verify local APIs in native scratch; formalize generic tilt rigidity.
2. Formalize canonical support predicate and exact finite quadratic equality.
3. Formalize fast and full-spectrum finite-witness roots.
4. Build sequential leaves; wire umbrellas; audit all declarations, direct
   dependencies, axioms, index coverage, whitespace, and repository lint once.

## Working verification log

- Ten local API checks passed natively.
- TiltedEqualityRigidity and WeilLogShiftObservableSupport passed with empty
  native logs. The support proof requires Measure.ae_ennreal_smul_measure_iff;
  the similarly named general scalar lemma has an IsDomain premise unavailable
  for ENNReal.
- WeilLogShiftQuadraticTiltEquality passed natively with an empty log: the
  constant-potential, anchor-value, and unequal-witness equivalences are verified.
  WeilLogShiftQuadraticReplicationWitness also passed with an empty native log.

## Formalized leaves

- HTGeometry/TiltedEqualityRigidity.lean: tilted_eq_iff_sub_ae_const.
- RHTower/WeilLogShiftObservableSupport.lean: finiteWeilCanonicalObservableLaw_ae_iff.
- RHTower/WeilLogShiftQuadraticTiltEquality.lean: the constant, anchored-value,
  and unequal-witness equivalences for actual finite tilted laws.
- RHTower/WeilLogShiftQuadraticReplicationWitness.lean: the fast-zero and complete
  spectrum existence criteria with explicit finite anchored witnesses.

## Verification

- Four sequential native leaf builds passed with empty logs; both umbrellas are
  wired without building them.
- Metadata: seven unique declarations, eight direct import edges, seven incoming
  imports, four fresh native objects, direct dependency freshness, and one
  umbrella import per leaf.
- Scoped index publication covers all seven declarations (2 replication,
  3 equality, 1 support, 1 generic), with no partial flags, markers, or stderr.
- Source and umbrella whitespace checks passed.
- Single repository lint snapshot: six unrelated errors and 367 warnings.
  Unreachable modules: RHTower.CCMPolarOddPrimeJumps, RHTower.PaperWoldPrimeWindows,
  RHTower.Sieve.FourthDerivativeTestSharp, RHTower.ZetaFiveSeventhsLineBound,
  HTGeometry.QKrawtchoukCompanionTriangular. Existing sorry:
  RHTower/CCM/CCMPolarOddPrimeJumps.lean:104, ccmPolarOddSource_eq_core_add_atoms.
  No owned error.
- Final native scratch audit passed seven axiom reports and ten API checks.
  Only propext, Classical.choice, and Quot.sound occur. Artifacts use
  /tmp/hgt-weil-tilt-equality-; native leaf logs use /tmp/hgt- followed by the
  leaf basename and .log.

## Boundary

This replaces comparisons of measures by explicit finite quadratic evaluations.
It does not yet classify the resulting coefficient subspace uniformly in r,k.
The subsequent finite-weil-tilt-variance-kernel increment identifies the same
equality condition as zero variance under any finite probe tilt, and establishes
that all real observables have a common zero-variance kernel across these tilts.
Prescribed replication schedules and monotone intermediate schedules remain open.
The corpus-wide research goal remains active.
