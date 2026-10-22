# HB radiative anti-linear positive-Hermitian-metric no-go

- **ID:** HC90
- **Stage:** 3-formalized
- **Type:** CONJECTURE / POSITIVE-METRIC SELECTION NO-GO
- **Source:** read-only `rh-current-frontier-map.md` · HC89 radiative source-FE involution · finite Xi packets

## Goal

Attack hardest survivor after HC89: perhaps coherent cancellation remains unphysical because a
positive/Hermitian detector metric must make functional-equation transport antiunitary, and that
positivity might force reflection-real or fixed weights and hence RH.

Use actual HC89 radiative source-FE cocycle, not abstract free data. Lift it to full finite Xi
packets and decide whether it admits a positive-definite invariant Hermitian energy off line. A
construction kills positivity alone as an RH selector. Then isolate exact stronger survivor:
fixed/source-independent metric data or reflection-real coordinate weights.

## Gates

- [x] 0 → 1 in-progress: corpus audit; exact conjecture frozen
- [x] 1 → 2 fully-proven: dependency-closed paper proof and bounded primary-literature audit
- [x] 2 → 3 formalized: unconditional Lean theorem, targeted build, axiom and lint audit
- [ ] 3 → 4 publication-ready: independent mathematical/physical review and broader novelty search

## Corpus audit

- `[CORPUS]` HC89 constructs a nowhere-zero actual radiative source-FE cocycle `κrad` and proves
  `κrad(Rq) conj(κrad(q)) = 1` at every Xi copy.
- `[CORPUS]` the existing literal-source packet transport is an anti-linear involution, but its
  cocycle predates actual Green dressing.
- `[CORPUS]` fixed complex-bilinear packet Ward covariance is classified orbitwise; identifying
  transported weights with fixed unit weight is equivalent to RH.
- `[CORPUS]` reflection-real nonzero weights plus packet Ward covariance recover RH.
- `[CORPUS NEGATIVE]` mandatory searches found no full finite-packet lift of actual HC89 radiative
  transport, no positive-definite invariant Hermitian energy for it, and no theorem deciding
  whether positivity alone forces reflection-real/fixed weights.

## Conjecture HC90-A: actual radiative packet involution

Define the conjugate-linear packet map

`(T_rad x)(q) = κrad(Rq) conj(x(Rq))`.

Prove its exact action on coefficients and singleton packets and prove `T_rad (T_rad x) = x` for
every finite Xi packet. No RH premise or critical-line restriction is allowed.

## Conjecture HC90-B: canonical positive invariant energy

For finite packets define base Hermitian energy

`E0(x) = Σ_q |x(q)|²`

and involution-symmetrized energy

`Erad(x) = E0(x) + E0(T_rad x)`.

Prove unconditionally:

1. `Erad(x) ≥ 0`;
2. `Erad(x) = 0 ↔ x = 0`;
3. `Erad(T_rad x) = Erad(x)`.

This is positive definiteness plus exact antiunitary energy invariance for actual radiative
transport. Also expose the sharper orbitwise diagonal survivor

`h(q)=‖κrad(q)‖ > 0`,  `h(Rq) |κrad(q)|² = h(q)`.

Thus even a positive diagonal orbit metric exists on every reflected pair, including off-line
copies where both physical Ward channels are bright.

## Conjecture HC90-C: closed route-killing theorem

Package, without external premises, universal packet involution, positive definiteness, exact
energy invariance, positive orbit weights, and HC89 off-line bright-pair cancellation. The theorem
must demonstrate coexistence, not merely prove unrelated facts: actual source/Green FE transport
admits positive metric geometry while two nonzero reflected nonlinear channels cancel.

## Paper proof

The singleton and coefficient laws follow by reflection reindexing, coefficient conjugation, and
diagonal multiplication by `κrad`. Applying transport twice gives coefficient
`κrad(q) conj(κrad(Rq))`; this is one after conjugating/reflection-relabeling HC89's involution law.

Every base-energy summand is a complex norm square, hence nonnegative. A finite sum of these
summands vanishes exactly when every supported coefficient vanishes, hence exactly when packet is
zero. Therefore `Erad` is positive definite. Invariance is formal:

`Erad(Tx)=E0(Tx)+E0(T²x)=E0(Tx)+E0(x)=Erad(x)`.

Taking complex norms in `κrad(Rq) conj(κrad(q))=1` gives
`‖κrad(Rq)‖ ‖κrad(q)‖=1`. Multiplication by `‖κrad(q)‖` yields the orbit balance law for
`h(q)=‖κrad(q)‖`; nowhere-vanishing gives strict positivity.

## Hostile checks

- Use actual HC89 Green-dressed source-FE cocycle and full finite Xi packets.
- Prove coefficient, singleton, and involution laws exactly.
- Prove energy zero iff packet zero, not only nonnegativity.
- Prove exact transport invariance and strictly positive orbit weights.
- Exhibit coexistence with HC89 off-line bright-pair cancellation.
- Do not infer canonicality, locality, or source-independence from positivity; those are surviving
  constraints.
- No RH hypothesis, computation, numerical bound, new axiom, `sorry`, or `admit`.

## Expected route impact

If proved, positivity/Hermiticity is dead as a standalone route selector: every actual radiative
anti-linear FE involution supports a positive-definite invariant finite-packet energy, and its
orbit cocycle supports positive diagonal weights even off line. Remaining HB/FZZ-P/PW-B/RBH burden
is sharper: derive one metric before divisor/source transport, or force coordinate weights to be
fixed/reflection-real from local dynamics.

## Bounded primary-literature audit (2026-08-28)

- `[LITERATURE]` Bargmann,
  [*Note on Wigner's Theorem on Symmetry Operations*](https://doi.org/10.1063/1.1704188),
  proves quantum symmetries are represented by unitary or antiunitary maps, but does not construct
  this arithmetic Green/source-FE packet metric or classify its RH-bearing fixed-weight survivor.
- `[LITERATURE]` Mostafazadeh,
  [*Pseudo-Hermiticity versus PT-Symmetry III*](https://arxiv.org/abs/math-ph/0203005), relates
  invertible anti-linear symmetries, pseudo-Hermiticity, and positive inner products for
  diagonalizable Hamiltonians. It does not treat this Xi divisor packet transport, actual BM
  radiative cocycle, or reflected bright Ward cancellation.
- `[NOVELTY CLAIM, BOUNDED]` Targeted primary-source and exact corpus searches found no theorem
  combining actual topological-black-hole Green-dressed source FE, finite Xi packet involution,
  explicit positive invariant energy, orbitwise positive cocycle metric, and off-line bright-pair
  cancellation. This is bounded, not exhaustive.

## Formalization result

Formalized in
`GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMRadiativeSourceFEPositiveHermitianMetricNoGo`.

- Actual HC89 radiative cocycle is lifted to a conjugate-linear finite-packet transport with exact
  coefficient and singleton formulas and an unconditional involution theorem.
- `hbXiPeierlsFiniteHermitianForm` and its norm-square diagonal are proved sesquilinear,
  conjugate-symmetric, nonnegative, and zero only on the zero packet.
- Symmetrizing this form along actual radiative transport produces
  `hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianForm`. Lean proves both scalar laws, both
  additive laws, conjugate symmetry, positive definiteness of its diagonal energy, and exact
  antiunitary transport.
- Cocycle modulus gives a strictly positive diagonal orbit weight with exact reflected gain
  balance `h(Rq) |κrad(q)|² = h(q)`.
- Closed theorem
  `hbXiPhaseSensitiveUnitRadiativeSourceFEPositiveHermitianBrightCancellation` packages these
  laws together with HC89's universal off-line nonzero bright-pair cancellation. It has no
  external premise.

Audit: direct `lake env lean` passed; targeted
`lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMRadiativeSourceFEPositiveHermitianMetricNoGo`
passed all 12,019 jobs. Representative `#print axioms` outputs contain only `propext`,
`Classical.choice`, and `Quot.sound`. Formal lint reports only pre-existing unreachable modules
and no HC90 finding. Module is wired into `GaloisForLFunctions.RHTower` without a full umbrella
build.

## Open core after HC90

Positivity/Hermiticity is dead as a standalone selector: actual source/Green FE transport admits
positive-definite antiunitary packet geometry and positive diagonal orbit weights on every
reflection orbit, while off-line physical Ward channels remain bright and cancel coherently.

Remaining burden is strictly structural: derive detector metric before inspecting divisor/source
transport, prove that metric is fixed under source changes, or force coordinate weights to be
reflection-real. Existing corpus equivalences show reflection-real nonzero transported weights
recover RH; hardest next question is whether local detector/source algebra genuinely forces that
reality, or admits a phase gauge that defeats it too.

## Log

- 2026-08-28 — created directly in 1-in-progress after HC89 and mandatory corpus/literature audit.
