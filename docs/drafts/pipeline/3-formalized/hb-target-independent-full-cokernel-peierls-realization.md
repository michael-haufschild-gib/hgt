# HB target-independent full-cokernel Peierls realization

- **ID:** HC69
- **Stage:** 3-formalized
- **Type:** THEOREM / LEAN-PROVED FULL-COKERNEL PRODUCER INCIDENCE / HARD FRONTIER
- **Routes:** HB, FZZ-P, RBH, PW-B
- **Source:** HC68 four-route current transmutation; global left-coordinate Peierls incidence;
  total third-order retarded-minus-advanced cokernel cut
- **Statement:** One fixed, target-independent global Peierls propagator and literal BM source
  packets admit a canonical retarded/advanced response split whose complete nonlinear cokernel cut
  equals the BM polarized current on every Xi fibre. Its reflected orbit therefore obeys all exact
  HC68 negative-square laws and universal extinction is RH.

## Corpus-led conjecture

Use the corpus's finite-support global carrier, coordinate pairing, pointwise quadratic residual,
diagonal Peierls propagator, and algebraic BM branch lift. Define retarded response in both graded
channels to be the fixed global Peierls propagator and advanced response to be zero. This gives the
same target-independent causal jump in both channels without scaling any operator by a requested
divisor target.

At fixed radial midpoint `z=1/2`, prove unconditionally:

1. complete full-cokernel causal cut equals the phase-normalized global cubic cut;
2. it equals the literal BM unit-carrier polarized cut;
3. its reflected orbit equals HC67's Peierls orbit current;
4. the full-cokernel orbit is a negative multiple of HB optical power and negative squares of FZZ
   force, every-grade PW imbalance, and actual RBH imbalance;
5. universal full-cokernel extinction is RH.

## Why this is frontier-level

Existing global incidence closes the source pairing and phase-normalized cubic algebra, while the
route cards still mark equality with the abstract full-cokernel causal cut as open. The missing
step is to provide actual response maps in the complete retarded-minus-advanced section, not merely
an incidence scalar. This conjecture supplies a fixed global response realization and transfers
the exact signed four-route current into the full cokernel.

Scope remains strict: this is an algebraic global Peierls model with a canonical response split.
It does not prove that the physical Einstein--Teukolsky retarded and advanced Green operators equal
these maps, nor source-fixed FE--Schwarz covariance of the branch lift; corpus proves universal
branch covariance is RH-equivalent.

## Hostile checks

- No divisor-dependent target fitting in pairing, propagator, or response maps.
- Fix the midpoint and unit-carrier normalization; no free radial or amplitude hypotheses.
- Use the complete total third-order cokernel causal-cut definition, not only a phase-normalized
  proxy.
- Prove exact equality before route zero-locus corollaries.
- Keep the physical Green-operator and FE--Schwarz covariance boundary explicit.
- Keep frontier map read-only.

## Novelty boundary as of 2026-08-28

Lean-corpus search found target-fitted full-cokernel realization and target-independent global
phase-normalized incidence, but no target-independent full-cokernel theorem. Bounded primary-source
search covered covariant phase space/Peierls formalism (Khavkine, arXiv:1402.1282), conserved QNM
currents and bilinear forms (arXiv:2210.15935), and nonlinear black-hole mode excitation
(arXiv:2112.11168; arXiv:2310.04489). No audited source states this Xi-fibre BM full-cokernel
realization or four-route negative-square orbit law. Bounded, not exhaustive, priority claim.

## Gates

- [x] 0 -> 1 in-progress: corpus gap, exact conjecture, hostile proof route, bounded literature audit
- [x] 1 -> 2 fully-proven: dependency-closed paper proof
- [x] 2 -> 3 formalized: closed Lean theorem, target build, axiom/lint audit, umbrella wire
- [ ] 3 -> 4 publication-ready: independent priority audit and standalone exposition

## Log

- 2026-08-28 — Opened after HC68 reduced the remaining causal seam to full-cokernel source/response
  incidence. Frontier map left unchanged.
- 2026-08-28 — Proved the fixed global response realization in
  `ThetaCuspHawkingTargetIndependentFullCokernelPeierlsRealization.lean`: complete nonlinear
  cokernel cut equals phase-normalized global Peierls cut, equals literal BM candidate at midpoint,
  and its unit-carrier reflected orbit equals HC67's concrete current. Derived strict off-line
  negativity, pointwise orientation classification, exact HB/FZZ-P/PW-B/RBH presentations, and
  universal extinction/orientation equivalences with RH.
- 2026-08-28 — Verification: direct `lake env lean` passed; target-only
  `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingTargetIndependentFullCokernelPeierlsRealization`
  passed (`12009/12009`); all twelve exported theorem axiom audits report only `propext`,
  `Classical.choice`, and `Quot.sound`; umbrella import present; formal lint reports no finding in
  this module (only unrelated unreachable modules).
