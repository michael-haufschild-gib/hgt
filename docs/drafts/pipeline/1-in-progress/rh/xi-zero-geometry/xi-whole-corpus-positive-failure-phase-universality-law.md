# Xi whole-corpus positive/failure-phase universality law

## Status

Paper proof complete. Lean source written; exact typecheck awaits final dependency-aware module
build because several recently added terminal universality modules have no cached `.olean`.

## Theorem-first source

Whole-corpus terminal scan exposed sixteen high-level certificate families that are individually
equivalent to RH but not jointly synchronized:

- terminal analytic-source and terminal geometric-phase certificates;
- countable Hankel test sets and every dyadic descent level;
- Euclidean--Krylov--Jensen reflection and Hedenmalm orientation endpoint certificates;
- all-right-zero local analytic-order phases and every-zero local critical phases;
- prime-seam Calkin, reciprocal-square source, squared-Euler diagonal-correlation,
  Cassini--theta reciprocal-source, and squared-seam Cassini--dyadic certificates;
- Xi--Hurwitz orientation and prime--archimedean thermal endpoint certificates;
- fixed-Cauchy reciprocal-Krylov source-contrast saturation.

The scan also found global failure certificates for the corresponding negative chambers, but no
product theorem across those capstones.

## Universal laws

Under only the source/window hypotheses already required by the parameterized capstones, RH is
equivalent to simultaneous realization of all sixteen positive certificate families, including
all dyadic levels and all relevant zero-local charts.

Failure of RH is equivalent to simultaneous realization of all available global failure
certificates, failure of some dyadic level and the all-right-zero local phase, failure of the
thermal endpoint certificate, and strict positive fixed-Cauchy Krylov source contrast.  The
whole-corpus positive and negative phases are exact logical complements.

## Paper proof

Map RH into every positive field through each corpus equivalence; recover RH from the terminal
geometric component.  Map `¬RH` into every negative field through the synchronized failure
equivalences.  If no dyadic level fails, all levels hold and the all-level certificate theorem
forces RH; the same argument applies to the right-zero local phase and thermal endpoint.  Recover
`¬RH` from the terminal geometric failure component.  Negating the positive equivalence and
composing with the negative equivalence gives exact complementarity.

## Lean formalization

- Module: `GaloisForLFunctions.RHTower.XiWholeCorpusPositivePhaseUniversalityLaw`
- Positive theorem:
  `RHTower.riemannHypothesis_iff_wholeCorpusPositivePhaseUniversalCertificate`
- Failure theorem:
  `RHTower.not_riemannHypothesis_iff_wholeCorpusFailurePhaseUniversalCertificate`
- Complement theorem:
  `RHTower.not_wholeCorpusPositivePhase_iff_wholeCorpusFailurePhase`
- Development check attempted:
  `lake env lean GaloisForLFunctions/RHTower/XiWholeCorpusPositivePhaseUniversalityLaw.lean`
- Current blocker: missing cached object
  `GaloisForLFunctions/RHTower/XiCassiniThetaReciprocalSourceUniversalityLaw.olean` before
  typechecking begins.  Per build discipline, dependency construction is reserved for final
  `lake build <module>` audit.

## Novelty audit

Pending literature audit after theorem-generation phase. Corpus audit is negative.
