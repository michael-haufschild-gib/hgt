# HB source-FE QNM Shale--Stinespring obstruction

- **ID:** HC80
- **Stage:** 3-formalized
- **Type:** THEOREM / INFINITE-DIMENSIONAL SCATTERING ENDPOINT
- **Source:** read-only `rh-current-frontier-map.md` · HB/FZZ-P/PW-B/RBH shared Ward core

## Goal

Pass from HC79's exact fibrewise `SU(1,1)` completion to the full infinite
Birmingham--Mokhtari overtone ladder. The literal source-FE cocycle and its canonical pair
amplitude are independent of QNM overtone. Therefore a tilted Xi orbit repeats one strictly
positive partner occupation at every overtone.

Freeze the overtone-diagonal Shale predicate as square summability of this repeated pair block.
Prove it holds at one Xi orbit exactly on the critical wall and holds on every orbit exactly under
RH. This is an infinite-dimensional obstruction, not a finite-packet restatement or numerical
bound.

## Gates

- [x] 0 → 1 in-progress: corpus audit; exact statement frozen
- [x] 1 → 2 fully-proven: dependency-closed paper proof and bounded primary-literature audit
- [x] 2 → 3 formalized: unconditional Lean theorem, targeted build, axiom and lint audit
- [ ] 3 → 4 publication-ready: independent mathematical/physical review and broader novelty search

## Corpus audit

- `[CORPUS]` `ThetaCuspHawkingBMSourceFEModularBogoliubovDilationNoGo.lean` constructs the exact
  source-orbit pair amplitude `beta(q)` with `‖beta(q)‖²=N(q)`, where `N(q)>0` exactly off wall.
- `[CORPUS]` `ThetaCuspHawkingBMSourceFEClockChiralAmplitudeTransduction.lean` proves the centered
  source-FE clock defect is independent of BM overtone. HC79's cocycle gain and pair amplitude are
  themselves defined without an overtone parameter.
- `[CORPUS]` Birmingham--Mokhtari QNM modules define the full natural-number overtone ladder and
  its distinct frequency shifts. Existing packet locality is finite and does not impose a global
  Fock implementability condition.
- `[CORPUS]` `HilbertSchmidtOperatorBridge.lean` contains Hilbert--Schmidt tail/approximation
  infrastructure, but no theorem applies Shale--Stinespring square summability to the literal BM
  source-FE partner block.
- `[CORPUS NEGATIVE]` exact searches for Shale--Stinespring, Bogoliubov implementability, repeated
  source-FE partner occupation, and infinite QNM overtone Hilbert--Schmidt obstruction returned no
  matching theorem.

## Conjecture HC80-A: repeated partner block

For one `q : XiZeroCopy`, define the overtone partner sequence

`beta_q(n) = hbXiPeierlsUnitSourceFEOrbitBogoliubovPair(q)`.

Its squared norm is the constant sequence `N(q)`. Define

`HBXiPeierlsUnitSourceFEOvertoneShaleImplementable(q)`

to mean `Summable (fun n : Nat => ‖beta_q(n)‖²)`.

Then

`HBXiPeierlsUnitSourceFEOvertoneShaleImplementable(q) iff N(q)=0`

and hence iff `Re(q)=1/2`.

Paper mechanism: every summable real sequence tends to zero. A constant sequence can tend to zero
only when its value is zero. Conversely the zero sequence is summable. HC79 identifies that value
with exact partner occupation.

## Conjecture HC80-B: global endpoint

Define full orbitwise overtone implementability by requiring the preceding Shale predicate for
every Xi copy. Then

`(forall q, HBXiPeierlsUnitSourceFEOvertoneShaleImplementable(q)) iff RH`.

The same local predicate is equivalent to HB optical darkness, Deninger Ward cancellation, FZZ-P
equilibrium, every-grade PW-B balance, and canonical-copy RBH balance.

## Conjecture HC80-C: finite truncation divergence law

For each orbit the partial Hilbert--Schmidt mass through overtone `N` is exactly

`(N+1) * N(q)`.

Thus every tilted orbit has unbounded linear Shale mass, while every wall orbit has identically
zero mass. This exact formula is a structural multiplicity law, not optimization of a bound.

## Hostile checks

- Do not claim that damped QNMs already form an orthonormal one-particle Hilbert basis. HC80
  formalizes the overtone-diagonal Shale obstruction. The physical producer must still construct a
  faithful orthogonal/biorthogonal one-particle realization whose beta block has these coefficients.
- Do not replace the infinite overtone ladder by a finite cutoff; every finite cutoff is
  implementable off wall.
- Do not assume RH or partner-vacuum extinction.
- Distinguish the proved square-summability classification from the external Shale--Stinespring
  theorem connecting beta Hilbert--Schmidt class to Fock-unitary implementability.
- Prove exact partial mass and strict divergence off wall; do not use numerical overtone checks.

## Expected route impact

HC80 supplies a new infinite-frequency route absent from the current frontier: fibrewise
CCR completion is harmless, but coherent repetition across the complete QNM ladder has infinite
particle-production norm unless the shared Ward charge vanishes. Remaining burden becomes precise:
derive a faithful one-particle QNM realization and identify its global beta block with the literal
source-FE overtone sequence. If physical Fock implementability of that realization follows, RH
would follow immediately. Without that realization HC80 is an exact endpoint, not an RH proof.

## Bounded primary-literature audit (2026-08-28)

- `[LITERATURE]` David Shale, *Linear Symmetries of Free Boson Fields*, Trans. Amer.
  Math. Soc. 103 (1962), DOI
  [`10.1090/S0002-9947-1962-0137504-6`](https://doi.org/10.1090/S0002-9947-1962-0137504-6),
  is the classical regular-Fock implementability source. HC80 does not re-prove or internalize that
  operator theorem; it proves the source-specific beta-square summability classification needed to
  invoke it after a faithful one-particle realization exists.
- `[LITERATURE]` Sascha Lill,
  [*Bogoliubov Transformations Beyond Shale--Stinespring: Generic v* v for bosons*](https://arxiv.org/abs/2208.03487),
  explicitly separates regular Fock implementability (trace-class `v* v`) from extended
  implementations that survive its failure. This is a hostile check: HC80 obstructs ordinary Fock
  unitarity, not every enlarged or renormalized representation.
- `[LITERATURE]` Danny Birmingham and Susan Mokhtari,
  [*Exact Gravitational Quasinormal Frequencies of Topological Black Holes*](https://arxiv.org/abs/hep-th/0609028),
  gives the exact discrete complex gravitational QNM ladder used by the corpus. It does not attach
  the source-FE cocycle or a Shale beta block to that ladder.
- `[LITERATURE]` Jérémy Besson and José Luis Jaramillo,
  [*Quasi-normal mode expansions of black hole perturbations: a hyperboloidal Keldysh's approach*](https://arxiv.org/abs/2412.02793),
  treats QNMs through a non-selfadjoint resonant expansion and stresses that scalar-product
  structure is extra input for bulk coefficients. This supports, rather than removes, HC80's
  one-particle-realization caveat.
- `[NOVELTY CLAIM, BOUNDED]` These primary sources and targeted corpus searches exposed no result
  identifying the literal Xi source-FE orbit pair coefficient with an overtone-diagonal BM beta
  block, no exact partial-mass law `(N+1) * partnerNumber(q)`, and no resulting iff-RH
  square-summability endpoint. This audit is bounded, not an exhaustive claim over all literature.

## Formalization result

Module:
`GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSourceFEQNMShaleStinespringObstruction`

Lean proves unconditionally:

- exact overtone independence of the canonical source-FE pair coefficient;
- exact coefficient identity `‖beta_q(n)‖² = partnerNumber(q)`;
- local Shale square summability iff partner vacuum iff `Re(q)=1/2`;
- exact finite mass `(N+1) * partnerNumber(q)` and threshold-unboundedness off wall;
- universal orbitwise Shale square summability iff `RiemannHypothesis`;
- local equivalences with HB optical darkness, Deninger Ward cancellation, FZZ-P information
  equilibrium, every-grade PW-B balance, and canonical-copy RBH leading balance.

Audit:

- direct `lake env lean` check: passed;
- targeted `lake build
  GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSourceFEQNMShaleStinespringObstruction`: passed
  `12019/12019`;
- `#print axioms` on local classification, off-wall unboundedness, global iff-RH, and RBH bridge:
  only standard `[propext, Classical.choice, Quot.sound]`;
- formal lint: no finding in HC80 or its umbrella wiring; global failure remains only unrelated
  pre-existing/shared unreachable modules.

## Open core after HC80

The coefficient theorem is closed. The hardest remaining issue is not summability arithmetic: it is
the physical/operator realization. One must either construct a faithful one-particle realization
of the non-selfadjoint BM resonances whose beta block is HC80's literal repeated coefficient and
derive ordinary Fock implementability from the route physics, or prove that such a realization is
impossible. The latter would retire this naive Shale route early and force a biorthogonal/rigged or
extended-representation replacement theorem.
