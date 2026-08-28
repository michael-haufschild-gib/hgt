# HC92 — Horizon/boundary relative source-FE cocycle common-gauge rigidity

Status: formalized in Lean

Route: HB, with FZZ-P / RBH / PW-B relevance through detector-normalization rigidity

## Hard frontier question

HC90 shows positive Hermitian structure can coexist with every off-line source-FE orbit. HC91
shows one physical Ward channel can be made positive-real by a global unit phase gauge. Those
facts kill positivity and single-channel reality as selectors. The strongest surviving local
burden is relational: can one common source gauge make the functional-equation gains measured at
the horizon and at the normalizable AdS boundary agree?

## Corpus basis

Mandatory corpus searches:

- `scripts/formal_tools.py research "multiple independent BM source channels common phase gauge simultaneous realification relative phase holonomy Ward amplitude orthogonal mixing"`
- `scripts/formal_tools.py research "BM gravitational normalizable boundary transfer reflection conjugate source functional equation phase ratio Xi copy"`
- `scripts/formal_tools.py research "second harmonic boundary transfer conjugation common gauge relative cocycle collision critical line"`

Audit result:

- `d4BMMixedHorizonOpticalSourceProjection` is independent of its `orthogonalMixing` argument, so
  changing that parameter does not create a second detector channel.
- `d4BMXiSecondHarmonicBoundaryTransfer` is an actual independent horizon-to-normalizable-boundary
  BM readout. Its coefficient is nonzero at every Xi copy.
- `d4BMXiSecondHarmonicBoundaryTransfer_reflect_conj_collision_iff` already proves, through the
  exact gamma connection coefficient and strict horizontal transfer-modulus rigidity, that
  reflected and Schwarz-conjugate transfers collide exactly when `Re rho = 1/2`.
- HC89 supplies actual radiative source-FE cocycle `kappa_H`; HC91 supplies arbitrary common
  diagonal gauge conjugation.

## Frozen conjecture HC92

Let `T(q)` be exact BM normalizable-boundary transfer and `kappa_H(q)` the actual horizon
radiative source-FE cocycle. Define boundary response `P_B(q) = T(q) P_H(q)` and induced boundary
cocycle

`kappa_B(q) = T(Rq) kappa_H(q) / conj(T(q))`.

For every nowhere-zero common diagonal gauge `b`, let

`kappa_X^b(q) = b(Rq)^(-1) kappa_X(q) conj(b(q))`, for `X = H,B`.

Prove:

1. `T(Cq) = conj(T(q))` from the exact gamma quotient.
2. `kappa_B` transports the physical boundary response, is nonzero, and is involutive.
3. Common gauge cancels from relative transport:
   `kappa_B^b(q) = kappa_H^b(q) ↔ T(Rq) = conj(T(q))`.
4. Hence for every nowhere-zero `b`,
   `kappa_B^b(q) = kappa_H^b(q) ↔ Re(q) = 1/2`.
5. Existence of one global nowhere-zero common gauge with equal horizon/boundary gains at every Xi
   copy is equivalent to `RiemannHypothesis`.

The main result must be a closed universal proposition/theorem, unconditional in Lean, with no new
axioms.

## Kill criterion and survivor

- If common gauge can force equality off line, common-gain rigidity is dead; extract exact relative
  holonomy classification and retire route.
- If equality is gauge-invariant and exactly critical-line, HC92 closes the gauge loophole left by
  HC91. Surviving RH burden becomes physical derivation of universal horizon/boundary gain matching,
  not choice of phase convention.

## Literature audit (through 2026-08-28)

- Birmingham–Mokhtari, *Exact Gravitational Quasinormal Frequencies of Topological Black Holes*
  (arXiv:hep-th/0609028), derives gauge-invariant gravitational modes and exact hypergeometric
  solutions under horizon/AdS boundary conditions.
- Green–Hollands–Sberna–Toomani–Zimmerman, *Conserved currents for Kerr and orthogonality of
  quasinormal modes* (arXiv:2210.15935v3), derives reflection-based conserved bilinear forms and QNM
  excitation projections, motivating source-channel normalization.
- Sberna et al., *Nonlinear effects in the black hole ringdown: absorption-induced mode excitation*
  (arXiv:2112.11168), explicitly distinguishes horizon amplitude from boundary-normalized QNM
  profile and notes their nontrivial proportionality.
- Targeted searches found no paper stating the common diagonal-gauge cancellation theorem, the
  horizon/boundary relative source-FE cocycle classification, or its equivalence with RH. This is a
  bounded novelty audit, not a claim of exhaustive literature coverage.

## Formal result

Formal module:
`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMRadiativeSourceFEHorizonBoundaryRelativeCocycleRigidity`

Closed theorem:
`hbXiPhaseSensitiveUnitRadiativeSourceFEHorizonBoundaryRelativeCocycleRigidity`.

Proved unconditionally:

- exact gamma-quotient Schwarz law `T(Cq) = conj(T(q))` and Xi-copy nonvanishing;
- physical boundary response transport by a nonzero involutive boundary source-FE cocycle;
- common-gauge invariant relative cocycle
  `kappa_B^b(q) / kappa_H^b(q) = T(Rq) / conj(T(q))`;
- for every nowhere-zero common gauge,
  `kappa_B^b(q) = kappa_H^b(q) ↔ Re(q) = 1/2`;
- existence of one global nowhere-zero common-gain gauge is equivalent to
  `RiemannHypothesis`.

Interpretation: HC91's phase-realification escape is completely classified. One detector can be
realified by following its source phase, but a common rephasing cannot erase relative
horizon/boundary FE holonomy. Remaining HB burden is now sharply physical: derive universal equality
of those two gains from detector/locality/field equations without assuming critical-line placement.

## Lean audit checklist

- [x] Scratch proof with `lake env lean /tmp/hc92.lean`
- [x] No `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`
- [x] Closed theorem and `#print axioms` audit; only `propext`, `Classical.choice`, `Quot.sound`
- [x] Add new module and wire `GaloisForLFunctions.RHTower`
- [x] Targeted module build passed: 13097/13097 jobs
- [x] Formal lint has no HC92 finding; reported failures are unrelated pre-existing unreachable modules
- [x] Promote card to `3-formalized` after dependency-closed audit

