# NDS reduced-conductor/Roos regulator classification

- **ID:** NDS-RCRRC
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** `rh-current-frontier-map.md` · route NDS (read-only ledger)
- **Statement:** A regulator depending only on the reduced universal-node fibre and exact multiplicity conductor recovers every Xi transverse Roos class if and only if RH already holds; adjoining the actual theta terminal-jet holonomy gives an unconditional exact regulator but preserves, rather than kills, the Roos obstruction, and compatibility of its arithmetic monodromy with Picard--Lefschetz monodromy is itself exactly RH.

**Scope clarification (2026-10-06).** The retired proposal is the inference that reduced nodal
data alone automatically supplies the needed source law. The cited equivalences do not prove
nonexistence of a regulator for actual Xi, nor falsify actual arithmetic/geometric compatibility:
those assertions remain open and RH-equivalent. Assuming compatibility to prove RH would be
circular; proving it independently from the arithmetic source is still a legitimate target.
The stage and historical `FALSIFIED` label must be read only in this restricted sense.

## Goal

Resolve the missing NDS conductor-to-nearby-cycle regulator at its strongest nonnumerical source interface.  Determine whether reduced nodal geometry plus protected multiplicity can force derived exactness, or whether an oriented scheme-theoretic coordinate is logically necessary.  No zero-location hypothesis, analytic-family premise, numerical estimate, or assumed RH-strength regulator is allowed.

## Gates

- [x] 0 → 1 in-progress: NDS conductor, nearby-cycle, reflection, formal-unramified, and Roos carriers audited from corpus.
- [x] 1 → 2 fully-proven: dependency-closed reflection classification and unconditional oriented repair.
- [x] 2 → 3 formalized: Lean theorems `xiConductorRoosRegulator_orientationClassification` and `everyXiThetaTerminalArithmeticNearbyMonodromyTwo_eq_picardLefschetz_iff_riemannHypothesis`; targeted leaf checks/builds and axiom audit green.
- [ ] 3 → 4 publication-ready: independent expert novelty review and standalone paper.

## Corpus basis

- `XiThetaNodalConductorDegeneration.lean`: every reduced Xi nodal fibre is the same coordinate cross; exact multiplicity survives only in the conductor coefficient and its universal-node Picard--Lefschetz invariant class.
- `ConductorNearbyCycleSpecialization.lean`: universal-node conductor specialization is injective and its range is exactly the monodromy-invariant line.
- `PreDivisorTransverseRamificationRoosTransgression.lean`: transverse Roos class is coefficient-faithful, reflection-odd, and vanishes exactly on the critical wall.
- `XiHedenmalmMultiplicityChain.lean` and `RiemannVonMangoldt.lean`: exact analytic multiplicity is invariant under functional-equation reflection and Schwarz conjugation.
- `XiTerminalMultiplicityJetCurvatureTransgression.lean`: nonzero theta terminal multiplicity jet has exact cut log gain `x(2 Re rho - 1)/2`.

## Conjecture loop

### C1 — reduced-conductor regulator

Conjecture that a single regulator from the universal-node invariant lattice to the fixed transverse Roos target can recover the derived class on every Xi fibre using only reduced node plus exact multiplicity conductor.

- **Status:** classified, not constructed unconditionally.  `nonempty_xiReducedConductorRoosRegulator_iff_riemannHypothesis` proves existence is equivalent to RH even when regulator is an arbitrary function: no linearity, continuity, or monodromy condition is needed for the obstruction.
- **Mechanism:** reflected Xi fibres have identical multiplicity-conductor inputs, so any reduced regulator gives identical outputs.  The actual Roos outputs are negatives.  Complex scalar division by two forces that common class to vanish, hence every Xi fibre lies on the critical line.

### C2 — oriented terminal-jet repair

Pivot by adjoining one source-derived reflection-odd coordinate without inserting a zero location: terminal multiplicity jet's logarithmic norm gain at cut two.

- **Status:** proved.  `xiThetaTerminalMultiplicityCutLogGain_two` identifies this coordinate with the full pre-divisor centered rate.  `canonicalXiOrientedConductorRoosRegulator` then reconstructs the coefficient-faithful derived class on every Xi fibre unconditionally.
- **Consequence:** orientation repairs information loss but does not yield exactness.  Off-line orientation is carried faithfully into the nonzero Roos class.

### C3 — arithmetic/Picard--Lefschetz naturality square

Conjecture that the actual Deninger arithmetic monodromy on the specialized nonzero terminal conductor class agrees with universal-node Picard--Lefschetz monodromy, providing the missing conductor-to-nearby-cycle naturality.

- **Status:** classified as RH-equivalent.  `xiThetaTerminalArithmeticNearbyMonodromyTwo_eq_picardLefschetz_iff` proves pointwise commutation exactly on the critical line.  `everyXiThetaTerminalArithmeticNearbyMonodromyTwo_eq_picardLefschetz_iff_riemannHypothesis` proves global commutation exactly under RH.
- **Mechanism:** Picard--Lefschetz fixes the conductor invariant line.  Arithmetic clock-two monodromy scales its nonzero terminal coefficient by the half-density mate gain.  Equality forces gain one; coefficient non-erasure makes this equivalent to critical-line placement.

## No-go closure

- **Exact killing theorem/mechanism:** `nonempty_xiReducedConductorRoosRegulator_iff_riemannHypothesis` kills reduced factorization, and `everyXiThetaTerminalArithmeticNearbyMonodromyTwo_eq_picardLefschetz_iff_riemannHypothesis` kills the proposed unconditional naturality square.  Reduced conductor is reflection-even; transverse Roos class is reflection-odd.  On every free reflection orbit, factorization through reduced conductor identifies a class with its negative.  After orientation is retained, universal Picard--Lefschetz monodromy fixes the conductor class whereas arithmetic monodromy scales it by the nontrivial horizontal gain.  Both compatibility demands force RH.
- **Strongest positive survivor:** `canonicalXiOrientedConductorRoosRegulator` is an unconditional, coefficient-faithful regulator after adding exactly one actual theta-source terminal-jet holonomy coordinate.  `xiConductorRoosRegulator_orientationClassification` packages the impossibility/repair dichotomy.
- **New insight:** Missing NDS regulator is not blocked by absence of nearby-cycle infrastructure.  Reduced conductor-to-Roos factorization and arithmetic/Picard--Lefschetz naturality are each circular at exact RH strength.  Scheme-theoretic orientation does exist canonically in the terminal theta jet, but it transports the derived obstruction rather than annihilating it.  Surviving NDS burden is a genuinely new global source principle that proves the monodromy naturality square, not construction of either side of that square.
- **Status:** reduced-conductor NDS subroute retired.  Oriented NDS survivor remains open and is not an RH proof.  Formalized in `formal/GaloisForLFunctions/RHTower/XiReducedConductorRoosRegulatorClassification.lean` and `formal/GaloisForLFunctions/RHTower/XiNodalConductorHolonomyNaturalityClassification.lean`; both are wired into `GaloisForLFunctions.RHTower` without building the umbrella.

## Literature audit

Searches through 2026-08-28 found no paper constructing this Xi-specific nodal family, its terminal-jet/Roos regulator, or the reflection-even/odd factorization classification.  Nearest primary literature treats Picard--Lefschetz cycles in semistable Lefschetz fibrations ([Consani--Kim 2002](https://arxiv.org/abs/math/0207059)), Cartier divisors and theta geometry on the scaling site ([Connes--Consani 2016](https://arxiv.org/abs/1603.03191)), and the complex-lift/Witt Riemann--Roch strategy ([Connes--Consani 2018](https://arxiv.org/abs/1805.10501)).  None identifies protected Xi multiplicity conductor with a transverse `lim¹` class or proves this factorization obstruction.  Picard--Lefschetz monodromy and even/odd representation arguments are classical; novelty claim is restricted to the exact corpus-defined Xi regulator classification and source-terminal-jet repair.  Search-negative status is not independent expert certification.

## Log

- 2026-08-28 — Created from read-only NDS frontier row after excluding all numerical branches.
- 2026-08-28 — C1 proved RH-equivalent in Lean; no continuity or linearity assumptions required.
- 2026-08-28 — C2 proved: terminal-jet holonomy supplies canonical oriented regulator unconditionally, preserving exact multiplicity and Roos obstruction.  Reduced subroute retired with formalized positive survivor.
- 2026-08-28 — C3 proved RH-equivalent: actual arithmetic and universal Picard--Lefschetz monodromy commute on every terminal conductor class exactly under RH.  Missing NDS naturality square isolated as the full surviving theorem, not infrastructure.
