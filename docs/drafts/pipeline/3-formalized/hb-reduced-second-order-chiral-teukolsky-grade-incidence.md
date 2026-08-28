# HB reduced second-order chiral Teukolsky grade incidence

- **ID:** HC62
- **Stage:** 3-formalized
- **Type:** THEOREM / NONLINEAR SOURCE INCIDENCE / HARD FRONTIER / LEAN-PROVED
- **Routes:** HB, with HC58 clock images in FZZ-P, PW-B, and RBH
- **Source:** Full-Einstein exact `2s` grade selection; exact BM radial Green and helicity
  projection; HC58 source-FE clock transduction; doubled-weight self-adjointness endpoint
- **Statement:** The grade-resolved reduced second-order chiral Teukolsky source has an exact
  holomorphic `2s` coefficient. It equals the physical mixed-horizon source projection and hence a
  nowhere-zero transducer times the HC57 centered source-FE clock defect. For a nonzero Einstein
  seed, this `2s` coefficient is nonzero exactly at tilted divisors, exactly where its doubled
  angular weight is nonunitary. Thus tilted sectors cannot be removed by mixed/anti-chiral
  same-grade cancellation; they must leak into other angular sectors or violate self-adjoint
  one-sector closure.

## Corpus-led conjecture

Define the weight-resolved reduced Teukolsky source by composing three already-constructed physical
maps: the full Einstein quadratic grade source, the exact ingoing BM Green coefficient, and the
orthogonal-helicity Teukolsky projection. At the doubled holomorphic weight `2s(q)` prove:

1. the coefficient is exactly the existing nonlinear BM optical source projection;
2. it is exactly `T_A(q) D_n(q)`, HC58 transducer times HC57 clock defect;
3. for `A ≠ 0`, it is nonzero iff `Re(q) ≠ 1/2`;
4. it is nonzero iff the doubled cusp weight fails the unitary Eisenstein-line condition;
5. the global rule “every nonzero doubled principal source lies on the unitary line” is equivalent
   to RH;
6. every tilted divisor has a nonzero doubled source and a nonzero residual against any symmetric
   one-sector horizon angular operator when realized by a nonzero source vector.

## Why this is frontier-level

`ThetaCuspHawkingTeukolskyThermalDealiasingEndpoint` explicitly leaves nonvanishing of the reduced
second-order chiral `2s` source coefficient open. `ThetaCuspHawkingFullEinsteinGaugeFixedRadiationGram`
later proves same-grade Einstein selection, but the corpus has no theorem composing it through the
actual BM radial/helicity Teukolsky projection or identifying the result with source-FE clock
defect. HC62 attacks that exact missing nonlinear incidence. It does not assume passivity,
self-adjoint spectral admission, RH, or a nonzero projection.

## Hostile checks

- Build the coefficient from existing Einstein, Green, and Teukolsky projection maps; do not insert
  a free nonzero coefficient.
- Use exact grade separation to exclude mixed/anti-chiral same-grade counterterms.
- Require only `amplitude ≠ 0` for zero-locus results.
- Distinguish source nonvanishing from the still-unproved physical law forbidding angular leakage.
- Keep the primary coefficient unsquared and phase-sensitive.
- Audit every public theorem for axioms and keep the frontier map read-only.

## Novelty boundary as of 2026-08-28

Bounded primary-source audit found explicit nonlinear second-order Teukolsky sources
(Spiers--Pound--Moxon, PRD 108 (2023)), analytic source separation (Spiers, PRD 109 (2024)), and
numerical quadratic Kerr QNM excitation/angle-overlap studies (Ma--Yang, PRD 109 (2024); later
quadratic-mode classifications). No audited source states a completed-zeta divisor-indexed `2s`
source coefficient equals a source-FE centered-QNM clock defect, nor its exact equivalence with
failure of self-adjoint doubled-weight admission. This is a bounded, not exhaustive, priority
claim.

## Gates

- [x] 0 -> 1 in-progress: corpus gap, exact conjecture, hostile proof route, bounded literature audit
- [x] 1 -> 2 fully-proven: dependency-closed paper proof
- [x] 2 -> 3 formalized: closed Lean theorem, target build, axiom/lint audit, umbrella wire
- [ ] 3 -> 4 publication-ready: independent priority audit and standalone exposition

## Log

- 2026-08-28 — Opened after HC61 proved radial conservation faithfully transports clock defect and
  corpus search exposed a previously uncomposed full-Einstein `2s` grade-selection theorem.
- 2026-08-28 — Proved exact reduced-source identity with physical BM optical projection and with
  HC58 transducer times HC57 defect; nonvanishing iff tilted iff doubled weight is nonunitary;
  universal extinction and one-sector unitary admission iff RH; every nonzero tilted separated
  source forces angular leakage against any symmetric one-sector operator. Direct Lean check and
  target-only build passed (`12034/12034`); nine public theorem axiom audits report only `propext`,
  `Classical.choice`, and `Quot.sound`; umbrella wired. Global lint reports only unrelated existing
  unreachable modules and no HC62 issue.
