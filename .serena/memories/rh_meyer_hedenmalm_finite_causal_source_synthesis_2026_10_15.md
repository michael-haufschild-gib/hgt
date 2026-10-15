# Finite Meyer–Hedenmalm source synthesis (2026-10-15)

Formalized four new RH leaves:
- DeningerMeyerCausalDivision.lean: a vanishing Mellin moment admits an explicit causal primitive in the literal all-derivative/all-exponential Meyer target. Exact generator and entire Mellin division identities.
- DeningerMeyerXiCausalChains.lean: repeatedly divide the fixed exact Xi cap boundary through every actual Xi multiplicity. Exact local orders; all permitted jets vanish at other Xi divisor points. Negative log differentiation descends through actual Poisson boundaries.
- DeningerMeyerFiniteXiCausalSplitting.lean: the actual finite chain family is independent, its jet matrix is invertible, and every finite full-jet quotient has a source-constructed generator-invariant section. Projectors commute with the actual generator; disjoint packets annihilate each other. Every finite packet endomorphism lifts faithfully with composition preserved.
- DeningerMeyerHedenmalmSourceRealization.lean: multiplying the k-times divided source by I^k gives centered Mellin transform exactly xiThetaDividedChain at the centered divisor point. The Hedenmalm Jordan recurrence holds in actual Meyer cohomology. Before quotienting, every finite raw source packet has one common boundary defect: A G(c)=J(c)+b(c) Z(f_Xi), where b is the sum of bottom-chain coefficients. Projector range has exact dimension equal to the finite full-multiplicity slot count.

All four leaves passed direct lake --old env lean audits and are explicitly wired into RHTower.lean. Scratch #print axioms audit of twelve principal results passed with only propext, Classical.choice, Quot.sound. No new axioms, sorry, numerical experiments, heartbeat changes, full builds, or umbrella builds.

Scope: algebraic finite spectral source admission, not global spectral synthesis. No projector continuity, infinite-packet convergence, completeness, vanishing of the jet-invisible kernel, positivity, or RH is claimed. Operator identity is the finite projector, not identity on whole cohomology.

Research card: docs/drafts/pipeline/3-formalized/cross-route-structural-obstacle-2026-10-15.md. Includes paper proof, failed conjectures, exact significance, and integration audit. At last lint run all new modules were clear; repository lint exited 1 on unrelated concurrent unwired modules CHMDStage16GrowthPositivityCollapseAndTwoPointCriterion and CHMDStage20TwoPointCoshSinhClosedFormsAndRhoCosShiftDecomposition. Do not treat that historical shared-workspace lint state as current without checking.
