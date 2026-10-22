# HB pre-divisor optical-cancellation holomorphy obstruction

- **ID:** HC74
- **Stage:** 3-formalized
- **Type:** THEOREM / LEAN-PROVED NONLINEAR PRE-DIVISOR ANALYTIC NO-GO / HARD FRONTIER
- **Routes:** HB, FZZ-P, PW-B; RBH comparison
- **Source:** exact moving-horizon/AIME optical triangle; pre-divisor horizontal-rate formal
  neighbourhood; corpus holomorphic real-profile rigidity
- **Statement:** The unique scalar coefficient closing the moving-horizon radial--temporal--chiral
  optical triangle extends coefficient-for-coefficient to the open pre-divisor critical strip, but
  no holomorphic scalar function on that strip can equal this cancellation profile everywhere.

## Corpus-led conjecture

The corpus gives the physical cancellation coefficient on an Xi fibre as

`thirdMassReflectionSusceptibility(q) * thetaMirrorAIMEDenominator(q) / 12`.

Every factor is an explicit rational function of `x = Re(q)`. Define its pre-divisor profile before
zero selection by replacing the two reflected horizon shifts with

`A(x) = x(3-x)`, `B(x) = (1-x)(2+x)`

and retaining the exact third-mass cross numerator and AIME denominator. First prove literal
specialization to every `XiZeroCopy`.

The profile depends only on `Re(s)` and is nonconstant on `0 < Re(s) < 1`. Corpus period/identity
rigidity then predicts that no function holomorphic on the connected open critical strip can equal
this profile at every pre-divisor point: vertical accumulation forces a holomorphic real-profile
function to be constant, contradicting two exact interior values.

## Why this is frontier-level

The frontier map says the exact positive AIME susceptibility closes the radial--temporal--chiral
triangle identically, so sign/passivity cannot protect the tilted defect. HC74 attacks the analytic
status of that cancellation itself. A complete pre-divisor Einstein--Teukolsky coefficient is
expected to vary holomorphically/meromorphically with complex frequency away from Green poles. If
the unique cancelling scalar is intrinsically horizontal and nonconstant, it cannot be a globally
holomorphic scalar coefficient on the source strip.

Success does not prove RH and does not exclude divisorwise interpolation. It supplies a sharp
positive survivor: any source-global cancellation of the optical triangle must introduce a pole,
antiholomorphic dependence, support-domain discontinuity, or genuinely operator-valued data. This
removes the natural regular scalar completion and isolates the singular/nonlinear fork demanded by
the frontier map.

## Hostile checks

- Define coefficient on full open strip before selecting Xi zeros.
- Prove exact specialization to the corpus physical susceptibility, not merely the same zero set.
- Use holomorphy on the open strip, not global entirety.
- Prove nonconstancy at two interior points exactly; no numerical approximation or optimized bound.
- Do not claim discrete Xi values form a uniqueness set; divisorwise holomorphic interpolation
  remains possible.
- Do not claim the profile itself is the complete Einstein coefficient; it is the unique scalar
  counterweight required to erase the already-closed optical triangle.
- Keep frontier map read-only.

## Novelty boundary as of 2026-08-28

Mandatory Lean-corpus search found the exact Xi-fibre optical triangle, the unique positive
cancellation coefficient, pre-divisor transverse whole-plane data, a general entire real-profile
rigidity theorem, and a separate holomorphic defect-compensator no-go. It found no pre-divisor
extension of this physical optical susceptibility and no strip-holomorphy obstruction for its
Einstein--Teukolsky cancellation. Bounded primary-source audit covered Sberna--Bosch--East--Green--
Lehner's third-order absorption-induced mode excitation (arXiv:2112.11168), Kerr adjoint-current/QNM
projection identities (arXiv:2210.15935), Lagos--Hui's second-order Green-function causal analysis
(arXiv:2208.07379), Lestingi--Sberna--Green's July 2026 all-order QNM perturbation framework with
continuous-spectrum terms (arXiv:2607.19492), and Su--Khera--Chowdhuri--Casals--Yang's August 2026
Kerr Green-function decomposition (arXiv:2608.17943). No audited source states this exact
pre-divisor susceptibility specialization or holomorphic scalar no-go. Bounded, not exhaustive,
priority claim.

## Gates

- [x] 0 -> 1 in-progress: corpus gap, exact conjecture, hostile proof route, bounded literature audit
- [x] 1 -> 2 fully-proven: dependency-closed paper proof
- [x] 2 -> 3 formalized: closed Lean theorem, target build, axiom/lint audit, umbrella wire
- [ ] 3 -> 4 publication-ready: independent priority audit and standalone exposition

## Log

- 2026-08-28 — Opened after HC73 proved abstract Green splitting adds no restriction beyond
  skewness/Schwarz oddness. HC74 moves to the analytic status of the actual nonlinear optical
  counterweight. Frontier map left unchanged.
- 2026-08-28 — First conjecture succeeded. Constructed the whole-strip profile from the two exact
  reflected horizon shifts, third-mass cross numerator, and theta-mirror AIME denominator, and
  proved literal specialization to the existing Xi-fibre physical susceptibility. Proved a general
  strip identity theorem: every holomorphic function agreeing throughout the open critical strip
  with a profile depending only on `Re(s)` is constant. The optical susceptibility has distinct
  exact values at `1/4` and `1/2`, so no holomorphic scalar pre-divisor completion can track it.
- 2026-08-28 — Formalized in
  `ThetaCuspHawkingPreDivisorOpticalCancellationHolomorphyObstruction.lean`. Direct
  `lake env lean` passed; target-only
  `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingPreDivisorOpticalCancellationHolomorphyObstruction`
  passed (`12138/12138`); all four exported theorem axiom audits report only `propext`,
  `Classical.choice`, and `Quot.sound`; umbrella import present. Formal lint reports no finding in
  this module and remains nonzero only for the pre-existing unrelated unreachable-module list.
