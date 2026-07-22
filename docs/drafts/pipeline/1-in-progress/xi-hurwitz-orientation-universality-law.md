# Xi--Hurwitz orientation universality law

- **ID:** xi-hurwitz-orientation-universality-law
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper proved, hostile-audited, Lean-direct-checked; no priority claim)
- **Source:** Post-Law-20 terminal/dependency scan of the actual Xi--Hurwitz theorem component
- **Statement:** Zero canonical Xi--Hurwitz orientation energy is equivalent to one
  simultaneous certificate spanning exact monodromy values, centered reciprocal-square reality,
  Hilbert/Weil positivity, central Hankel positivity, differential circuits, finite rational
  Hurwitz values and refinements, continued prime--Gamma source passivity, sharp rectangular
  growth, and tropical Sonin compact absorption. The underlying Xi-indexed continued-Hurwitz
  family remains unconditionally differentially independent.

## Gates

- [x] 0 → 1 in-progress: theorem-first component and exact candidate boundary
- [x] Complete paper proof with no open dependency
- [x] Lean direct check
- [x] Hostile literature noncollision audit
- [ ] Final module build, lint, and axiom audit

## Exact theorem component read

1. `xi_hurwitz_scalar_constraint_orientation_product_law` and
   `xi_hurwitz_constraint_orientation_product_law` join unconditional differential independence
   to zero orientation energy and exact height-normalized monodromy values.
2. `xi_hurwitz_orientation_energy_positivity_compression_law` joins zero energy to the complete
   trace-Hankel, leading-Hankel-determinant, and square-summable Weil positivity cones.
3. `xiHurwitzOrientationVector_eq_zero_iff_energy_eq_zero` and
   `xiHurwitzOrientationVector_weil_nonneg_iff_fullWeil_nonneg` identify the canonical Hilbert
   vector and its one-vector Weil test.
4. `xiHurwitzFESchwarzPairCircuit_iff_orientationEnergy_zero`, the FE--Schwarz aperture laws,
   `xiHurwitzFESchwarzTripleCircuit_iff_riemannHypothesis`, and
   `xiHurwitzAnchorJetProjectiveReflectionLaw_iff_FESchwarzPairCircuit` join rank-two/rank-three
   differential circuits, anchor jets, common prime seams, and all-positive seam damping.
5. `xiRationalHurwitzFiberTwoReflectionFixed_iff_riemannHypothesis` and the arbitrary two-scale,
   all-power, bounded-ray, and dyadic refinement classifiers identify the finite rational-Hurwitz
   value charts.
6. Exterior, positive-paired core, and positive-paired reduced-source passivity classifiers at the
   exact rational radius `218/25` identify three continued prime--Gamma source charts.
7. Continued-core and separated finite-packet reconstruction theorems identify explicit sequences
   converging to the orientation vector and energy; eventual nonnegativity is the RH boundary.
8. `riemannHypothesis_iff_xiHurwitzRightPrincipalPhaseSup_eq_zero`, both rectangular subpower
   criteria, and `riemannHypothesis_iff_xiHurwitzTropicalLoop_compactEq_direct` identify sharp
   growth and Sonin Calkin-memory charts.
9. Anchored Vandermonde reality and scalar-energy classifiers identify every actual critical-line
   anchor chart.

## Internal noncollision audit

`scripts/formal_tools.py research "Xi Hurwitz orientation energy central spectrum Hankel trace Weil
orientation vector exterior passivity tropical loop"` returned local bridge modules and individual
classifiers. Direct reference search found no consumer crossing positivity compression, finite
Hurwitz circuits/refinements, source passivity/reconstruction, principal-phase growth, and tropical
Sonin memory. Existing capstones close strict subcomponents only.

## Paper proof

Use `xiHurwitzOrientationEnergy = 0 ↔ RiemannHypothesis` as an internal connector, never as an
extra hypothesis. Forward, recover RH and apply every exact classifier in Items 1--9. Universal
quantification over moduli, powers, distinct scales, widths, and Sonin parameters is legitimate
because each input classifier is exact for every admissible parameter. The unconditional continued
and separated reconstruction theorems supply sequences converging to the orientation vector and to
the negative orientation energy; RH supplies termwise, hence eventual, nonnegativity. Every actual
critical-line anchor satisfies both anchored classifiers. This constructs all 26 certificate
components.

Conversely, the certificate's first component is the exact negative-character chamber, which
recovers RH and hence zero orientation energy. `xi_zero_hurwitz_differentialIndependent_all` is
unconditional, so adjoining it preserves the equivalence and strictly subsumes both earlier
constraint-orientation product laws.

For the complementary chamber, positive orientation energy gives failure of RH. Existing exact
classifiers then produce an off-line divisor point, a negative trace-Hankel polynomial, a nonpositive
leading Hankel determinant, a negative square-summable Weil vector, strict negativity of the
canonical orientation vector, and positive principal-phase supremum simultaneously. Conversely,
the off-line witness alone forces positive energy. `[PROVED HERE]`

## Formalization

- Module: `formal/GaloisForLFunctions/RHTower/XiHurwitzOrientationUniversalityLaw.lean`
- Quantified master classifiers:
  `xiRationalHurwitzAllFiniteRefinements_iff_riemannHypothesis`,
  `xiHurwitzAllWidthRectangularNormSubpower_iff_riemannHypothesis`,
  `xiHurwitzAllWidthRectangularTailSubpowerLower_iff_riemannHypothesis`, and
  `xiHurwitzAllScaleTropicalLoopAbsorption_iff_riemannHypothesis`
- Source-sequence classifiers:
  `xiHurwitzContinuedCauchySequenceNonnegative_iff_riemannHypothesis` and
  `xiHurwitzSeparatedSourceSequenceNonnegative_iff_riemannHypothesis`
- Positive capstones: `xiHurwitzOrientationEnergy_eq_zero_iff_universalCertificate` and
  `xi_hurwitz_differential_orientation_universality_law`
- Failure capstone: `xiHurwitzOrientationEnergy_pos_iff_failureUniversalCertificate`

## Hostile literature audit

Exact searches for the named energy and combinations of Xi/Hurwitz monodromy, rational-Hurwitz
reflection values, differential independence, central Hankel determinants, Weil positivity,
continued prime--Gamma sources, rectangular subpower growth, and Sonin compact absorption found no
collision. Connes--Consani's
[Weil positivity and Trace formula, the archimedean place](https://arxiv.org/abs/2006.13771)
develops the Hilbert/Sonin trace framework and relates semilocal Weil positivity to RH, but has no
Hurwitz monodromy energy, finite rational-fibre refinement, differential-circuit, or 26-chart
certificate. Their
[Scaling Hamiltonian](https://arxiv.org/abs/1910.14368) develops the semilocal operator picture,
again without these Xi-indexed Hurwitz interfaces. Ashton--Fokas'
[Relations among the Riemann zeta and Hurwitz zeta functions as well as their products](https://arxiv.org/abs/1809.09440)
studies analytic relations and large-parameter behavior, not this orientation/positivity synthesis.
Nakamura's
[Zeros and the functional equation of the quadrilateral zeta function](https://arxiv.org/abs/1712.05169)
studies bilateral Hurwitz/periodic combinations and their zeros, not rational-fibre reflection at
Xi zeros or the universal certificate. Evidence supports noncollision only; no priority claim is
made.

## Log

- 2026-07-21 — Post-Law-38 current-delta rescan strengthened certificate from 26 to 28 charts by
  adding exact algebraic-eigencharacter and determinant-one FE-trace continued-Hurwitz dependence
  interfaces. Unconditional pointwise joint-algebraicity theorem was deliberately excluded as an
  unrelated conjunct. Exact direct Lean recheck passes. Targeted hostile searches over Hurwitz
  value distribution/relations, differential dependence, monodromy, Arakelov coordinates, and
  rank-two character traces found no matching RH interface; nearest literature treats these
  ingredients separately. No collision found; no priority claim.

- 2026-07-22 — Law20 added to corpus; full endpoint pass restarted.
- 2026-07-22 — Read exact Xi--Hurwitz energy, consumer, Hilbert/Weil, source reconstruction,
  source-passivity, FE-circuit, rational-fibre, refinement, principal-phase, and tropical Sonin
  theorem bodies. No common consumer found; candidate promoted only after this dependency closure.
- 2026-07-22 — Formalized six quantified/source-sequence master classifiers, the 26-chart
  zero-energy certificate, differential-independence capstone, and complementary six-witness
  positive-energy certificate. Exact direct check
  `lake env lean GaloisForLFunctions/RHTower/XiHurwitzOrientationUniversalityLaw.lean` passed.
- 2026-07-22 — Hostile exact and neighboring-concept literature audit passed; nearest
  Connes--Consani, Hurwitz-relation, and quadrilateral-zeta sources are materially different.
