# Deninger coarse invariant-sheaf existence and functoriality

- **ID:** `deninger-coarse-invariant-sheaf-existence`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Label:** `DAC_COARSE_INVARIANT_SHEAF_EXISTENCE`
- **Parent:** `deninger-coarse-invariant-sheaf-rost-schmid-descent`
- **Statement:** degreewise fixed sections of an equivariant dg-algebra
  sheaf on Deninger's suspension cover form a genuine dg-algebra sheaf
  on the coarse quotient, functorially for every commuting source
  operation.

## Goal

Close existence and operation-descent part of Deninger's Definition
10.1 without replacing underived invariants by group cohomology,
quotient-stack descent, or global chart cochains.

## Setup

Let a group \(G\) act on a topological space \(Y\), let
\(\pi:Y\to X=Y/G\) be the coarse quotient map, and let
\(\widetilde{\mathscr A}^{\bullet}\) be a \(G\)-equivariant sheaf of
unital dg \(R\)-algebras on \(Y\).  For every open \(U\subseteq X\)
define
\[
 \mathscr A_X^n(U)
 =
 \widetilde{\mathscr A}^n(\pi^{-1}U)^G.                            \tag{1}
\]

## Theorem

`[PROVED HERE] [DAC_COARSE_INVARIANT_SHEAF_EXISTENCE]`

Formula `(1)` has the following properties.

1. Each \(\mathscr A_X^n\) is a sheaf of \(R\)-modules.
2. The differential, unit, and multiplication of
   \(\widetilde{\mathscr A}^{\bullet}\) restrict to `(1)`, making
   \(\mathscr A_X^\bullet\) a sheaf of unital dg \(R\)-algebras.
3. Every equivariant morphism of cover dg algebras descends
   functorially.
4. Every flow, Galois action, Frobenius/Verschiebung correspondence,
   residue, or trace map commuting with \(G\) descends to `(1)`.
5. Formation of `(1)` preserves kernels and all limits.  It need not
   preserve cokernels, cohomology objects, homotopy pushouts, or
   quasi-isomorphisms.

## Proof

Direct image is a right adjoint.  Hence
\[
 (\pi_*\widetilde{\mathscr A}^n)(U)
 =
 \widetilde{\mathscr A}^n(\pi^{-1}U)
\]
is a sheaf.  Its invariant subsheaf is the limit
\[
 (\pi_*\widetilde{\mathscr A}^n)^G
 =
 \operatorname{Eq}\!\left(
   \pi_*\widetilde{\mathscr A}^n
   \rightrightarrows
   \prod_{g\in G}\pi_*\widetilde{\mathscr A}^n
 \right),                                                         \tag{2}
\]
where the two arrows send a section to its \(g\)-translates and to
the constant family with that section.  Limits of sheaves are
computed sectionwise, so `(2)` is a sheaf and agrees with `(1)`.

Equivariance of the differential gives
\[
 g(d a)=d(g a)=d a
\]
for every invariant section \(a\); hence the differential restricts.
The same calculation for the unit and multiplication proves the
dg-algebra assertion.  A commuting operation sends invariant
sections to invariant sections, and composition is unchanged after
restriction, proving functoriality.

Finally, fixed points are right adjoint to the trivial-action
functor.  They therefore preserve all limits and, in an abelian
setting, are left exact.  Infinite-group invariants are not generally
right exact.  This proves clause 5 and prevents any illicit
commutation of invariants with cohomology or derived colimits.

## Deninger consequence

Take
\[
 Y=\check X(\mathbb C)\times\mathbb R_{>0},
 \qquad G=\mathbb Q_{>0},
\]
and let \(\widetilde{\mathscr A}^{\bullet}\) be the equivariant
Tate--Milnor cover sheaf of
`DAC_LEAFWISE_KUMMER_SHEAF_AMALGAMATION_EXISTENCE`.  Then
\[
 \boxed{\mathscr E_{\mathrm{Den}}^\bullet
   =
   (\pi_*\widetilde{\mathscr A}^{\bullet})^{\mathbb Q_{>0}}}
                                                                    \tag{3}
\]
exists as a genuine source coefficient with all already-constructed
commuting operations.  Arithmetic cohomology must now be built from
\(R\Gamma(X,\mathscr E_{\mathrm{Den}}^\bullet)\), finite-place
Rost--Schmid localization, and the real signature boundary.

The theorem does not compute `(3)`.  In particular it proves neither
internal amplitude nor exactness of the generic/prime localization
sequence.  Those are the source-native open gates.

## Hostile audit

- Replacing `(3)` by
  \(R\Gamma(Y,\widetilde{\mathscr A})^G\) commutes derived sections
  with invariants and is not justified by this theorem.
- Replacing `(3)` by derived \(G\)-invariants introduces group
  cohomology absent from Deninger's definition.
- Chartwise two-term cohomology does not imply two-term stalks or
  coarse hypercohomology.
- The theorem uses no zeta zero, RH premise, spectral model, CCM
  object, or numerical computation.

## Gates

- [x] 0 → 1 in-progress: source-pure and well posed
- [x] 1 → 2 fully-proven: complete limit/equalizer proof
- [ ] 2 → 3 formalized: invariant subcomplex and descended-flow
  theorem written in Lean; categorical sheaf theorem and final audit
  remain
- [ ] 3 → 4 publication-ready: standalone source note and Lean audit

## Novelty audit

The categorical theorem is standard.  Its role is decisive: it closes
existence of Deninger's corrected coarse coefficient while preserving
the exact non-right-exactness where spectral middle cohomology may
live.  No broader novelty is claimed.

## Lean status

`DeningerArithmeticCoarseInvariants.lean` unconditionally defines the
degreewise invariant subcomplex and proves descent of every equivariant
commuting transverse generator.  Its Mathlib invariant-submodule API
was checked in isolation with
`lake env lean /tmp/deninger_invariants_api.lean`; after repairing four
Lean 4.30 subtype coercions in the existing three-term dependency, the
project file passes
`lake env lean
GaloisForLFunctions/RHTower/DeningerArithmeticCoarseInvariants.lean`.
Its two central theorems have only Lean's standard `propext` and
`Quot.sound` axioms.  The full sheaf-category equalizer statement
remains to be formalized.

## References

- Christopher Deninger, *Dynamical systems for arithmetic schemes*,
  Definition 10.1 and §12: https://arxiv.org/abs/1807.06400
- Christopher Deninger, *Rational Witt vectors and associated
  sheaves*: https://arxiv.org/abs/2508.05329

## Log

- 2026-07-27 — source existence and operation descent isolated and
  proved; derived quotient explicitly removed from the construction.
