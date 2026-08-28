# HB source-FE QNM Riesz--Shale rigidity

- **ID:** HC81
- **Stage:** 3-formalized
- **Type:** THEOREM / REALIZATION NO-GO + BASIS-ROBUST SHALE ENDPOINT
- **Source:** read-only `rh-current-frontier-map.md` · HC79--HC80 source-FE QNM endpoint

## Goal

Attack the hardest realization gap left by HC80 before building a physical Fock model.

First, prove that neither exact Birmingham--Mokhtari QNM branch on an actual Xi copy can be a
normalized eigenmode of even a pointwise-symmetric complex Hilbert-space generator: every such QNM
frequency has strictly negative imaginary part, whereas symmetry at one normalized eigenvector
forces its eigenvalue to be real. This retires the naive self-adjoint QNM-eigenbasis bridge.

Second, extract the strongest positive survivor. Model every Riesz/biorthogonal realization obtained
from an orthonormal overtone basis by a bounded invertible synthesis map `U`. Transport the literal
source-FE scalar beta block by similarity,

`U * (beta(q) I) * U^{-1}`.

Prove Hilbert--Schmidt membership is invariant under this transport and holds exactly when
`beta(q)=0`, hence exactly on the critical wall. Allow `U` to depend arbitrarily on `q`; universal
Riesz-transported Hilbert--Schmidt membership must still be equivalent to RH.

## Gates

- [x] 0 → 1 in-progress: corpus audit; exact statement frozen
- [x] 1 → 2 fully-proven: dependency-closed paper proof and bounded primary-literature audit
- [x] 2 → 3 formalized: unconditional Lean theorem, targeted build, axiom and lint audit
- [ ] 3 → 4 publication-ready: independent mathematical/physical review and broader novelty search

## Corpus audit

- `[CORPUS]` `ThetaCuspHawkingTopologicalBlackHoleQNMIncidence.lean` gives both exact BM branches,
  their imaginary parts, and conformal decay `2n+3/2`.
- `[CORPUS]` `abs_xiSpectralPoint_im_lt_half` places the centered Xi transverse coordinate strictly
  inside `(-1/2,1/2)`. Substitution makes both BM branch imaginary parts strictly negative for every
  Xi copy and every overtone.
- `[CORPUS]` `eigenvalue_conj_eq_self_of_symmetric_at` proves that symmetry only against one
  normalized eigenvector forces its eigenvalue to equal its conjugate. No global self-adjointness or
  domain theory is needed for the contradiction.
- `[CORPUS]` `ContinuousLinearMap.IsHilbertSchmidt.comp_left` and `.comp_right` prove the two-sided
  Hilbert--Schmidt ideal law. Applying the inverse transport on the left and the forward transport on
  the right proves similarity invariance under every continuous linear equivalence.
- `[CORPUS]` `ContinuousLinearMap.isHilbertSchmidt_iff_summable` makes scalar-identity
  Hilbert--Schmidt membership a constant-sequence question on any `Nat`-indexed Hilbert basis.
- `[CORPUS]` HC79 identifies `‖beta(q)‖²` with exact partner occupation; HC80 identifies its
  vanishing with every route receiver and RH.
- `[CORPUS NEGATIVE]` targeted searches exposed no theorem combining exact BM damping, the local
  symmetric-eigenmode no-go, arbitrary Riesz similarity transport, and the literal Xi source-FE beta
  coefficient.

## Conjecture HC81-A: self-adjoint QNM eigenmode no-go

For every complex Hilbert space, Xi copy `q`, and overtone `n`, no normalized vector can satisfy the
positive- or negative-branch BM eigenrelation for an operator symmetric at that vector.

This is stronger than saying a chosen differential generator is not self-adjoint: no positive
Hilbert eigenmode realization of either damped frequency can exist at all.

## Conjecture HC81-B: Riesz similarity invariance

For any complete complex Hilbert space `E`, continuous linear equivalence `U : E ≃L[ℂ] E`, and
bounded operator `T : E →L[ℂ] E`,

`IsHilbertSchmidt (U T U^{-1}) iff IsHilbertSchmidt T`.

The reverse implication uses the two-sided ideal law with `U`; the forward implication applies the
same law with `U^{-1}`. No unitary or normality hypothesis is allowed.

## Conjecture HC81-C: source-FE Riesz endpoint

Let `E` have a `Nat`-indexed Hilbert basis and let `U(q)` be any family of bounded invertible basis
transports. Then

`IsHilbertSchmidt (U(q) (beta(q) I) U(q)^{-1}) iff Re(q)=1/2`.

Universally over all Xi copies this is equivalent to RH. The same local statement is equivalent to
HB optical darkness, Deninger Ward cancellation, FZZ-P equilibrium, every-grade PW-B balance, and
canonical-copy RBH balance.

## Hostile checks

- A damped QNM is a resonance of a non-selfadjoint boundary problem; do not promote it to an
  ordinary self-adjoint eigenvector.
- Riesz transport covers bounded invertible images of an orthonormal basis only. It does not cover
  arbitrary complete minimal systems with unbounded synthesis, rigged-Hilbert generalized modes, or
  Lill-style extended Fock representations.
- Similarity invariance must be proved in both directions. One-sided ideal closure alone is not the
  result.
- The scalar beta block is the overtone-diagonal coefficient model. Do not claim the physical
  non-selfadjoint QNM Green operator has already been identified with it.
- No finite cutoff, numerical spectrum, optimized bound, RH assumption, or external Shale theorem.

## Expected route impact

HC81 decides the first realization fork early. Ordinary self-adjoint QNM eigenbases are impossible.
Every bounded Riesz repair nevertheless preserves HC80's infinite beta obstruction, so basis
nonorthogonality cannot hide off-wall partner production. A surviving physical route must therefore
prove that the relevant QNM resonant expansion is Riesz-controlled and identifies this beta block,
or develop a genuinely non-Riesz/rigged implementability principle and explain why the route physics
selects ordinary Fock space rather than an extended representation.

## Bounded primary-literature audit (2026-08-28)

- `[LITERATURE]` Birmingham--Mokhtari,
  [*Exact Gravitational Quasinormal Frequencies of Topological Black Holes*](https://arxiv.org/abs/hep-th/0609028),
  supplies exact discrete complex QNM frequencies and their dissipative interpretation, but no
  positive-Hilbert eigenbasis, source-FE beta block, or Riesz/Shale classification.
- `[LITERATURE]` Green--Hollands--Sberna--Toomani--Zimmerman,
  [*Conserved currents for Kerr and orthogonality of quasinormal modes*](https://arxiv.org/abs/2210.15935),
  constructs an unconventional symmetric bilinear form after contour regularization. The paper
  explicitly distinguishes it from a positive-definite Hilbert inner product and does not assert an
  ordinary complete QNM Hilbert basis. This is a direct hostile check against the naive bridge.
- `[LITERATURE]` Besson--Jaramillo,
  [*Quasi-normal mode expansions of black hole perturbations: a hyperboloidal Keldysh's approach*](https://arxiv.org/abs/2412.02793),
  formulates QNMs as a non-selfadjoint spectral problem and separates resonant expansions from the
  extra norm structure needed for bulk coefficients.
- `[LITERATURE]` Jaramillo--Macedo--Al Sheikh,
  [*Pseudospectrum and black hole quasi-normal mode (in)stability*](https://arxiv.org/abs/2004.06434),
  exhibits the non-selfadjoint/pseudospectral character and high-overtone instability of black-hole
  QNMs. Thus bounded Riesz control is a serious remaining producer, not a routine fact.
- `[LITERATURE]` Shale,
  [*Linear Symmetries of Free Boson Fields*](https://doi.org/10.1090/S0002-9947-1962-0137504-6),
  and Lill,
  [*Bogoliubov Transformations Beyond Shale--Stinespring: Generic v* v for bosons*](https://arxiv.org/abs/2208.03487),
  delimit regular Fock implementability and its extended-representation escape. HC81 formalizes the
  source-specific Hilbert--Schmidt ideal/similarity statement, not the external Fock theorem.
- `[NOVELTY CLAIM, BOUNDED]` Targeted primary-source and exact corpus searches found no theorem
  coupling the literal Xi source-FE beta coefficient to arbitrary bounded invertible QNM synthesis,
  proving its Hilbert--Schmidt classification invariant under every such transport, or deriving the
  resulting iff-RH endpoint. Exact searches for a black-hole QNM Riesz basis found no matching
  primary result. This is a bounded audit, not an exhaustive literature claim.

## Formalization result

Module:
`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceFEQNMRieszShaleRigidity`

Lean proves unconditionally:

- both exact BM QNM branches on every Xi copy and overtone have strictly negative imaginary part;
- neither branch can be a normalized eigenmode of an operator symmetric even only at that vector;
- Hilbert--Schmidt membership is invariant under every bounded invertible similarity between two
  complete complex Hilbert spaces;
- on any model Hilbert space with a `Nat`-indexed Hilbert basis, a scalar identity block is
  Hilbert--Schmidt iff its scalar is zero;
- after any bounded invertible Riesz synthesis into any complete complex Hilbert carrier, the
  literal source-FE beta block is Hilbert--Schmidt iff partner occupation is zero iff
  `Re(q)=1/2`;
- this remains true for an arbitrary Xi-dependent family of transports, universally iff RH;
- exact local equivalences with HB optical darkness, Deninger Ward cancellation, FZZ-P equilibrium,
  every-grade PW-B balance, and canonical-copy RBH leading balance.

Audit:

- direct `lake env lean` check: passed;
- targeted `lake build
  GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceFEQNMRieszShaleRigidity`: passed
  `12174/12174`;
- `#print axioms` on positive-branch no-go, generic similarity invariance, global iff-RH, and RBH
  bridge: only standard `[propext, Classical.choice, Quot.sound]`;
- formal lint: no finding in HC81 or its umbrella wiring; global failure remains only unrelated
  pre-existing/shared unreachable modules.

## Open core after HC81

Naive self-adjoint QNM eigenmode realization is dead. Every bounded Riesz/biorthogonal repair is too
regular to evade the source-FE Shale obstruction. Remaining live producer is now sharply isolated:
prove the physical BM resonant expansion admits bounded Riesz synthesis and identify its beta block
with the literal source coefficient, or prove that high-overtone pseudospectral growth makes every
such synthesis unbounded. In the latter case, ordinary-Fock HC80--HC81 cannot be the final RH route;
the positive survivor must be a rigged/Krein or extended-Fock implementability principle strong
enough to exclude off-wall beta while not assuming RH.
