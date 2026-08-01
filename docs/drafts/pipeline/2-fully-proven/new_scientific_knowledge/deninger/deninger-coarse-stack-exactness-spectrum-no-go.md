# Coarse/stack exactness scalar-spectrum no-go

- **ID:** `deninger-coarse-stack-exactness-spectrum-no-go`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Label:** `DAC_COARSE_STACK_EXACTNESS_SCALAR_SPECTRUM_NO_GO`
- **Parent:** `deninger-coarse-invariant-sheaf-rost-schmid-descent`
- **Statement:** if underived coarse invariants agree with derived
  quotient-stack descent, locally scalar power cohomology remains
  scalar and cannot realize the nontrivial zeta spectrum.

## Setup

Let \(G=\mathbb Q_{>0}\) act on Deninger's suspension cover
\(\widetilde X\), let
\[
 c:[\widetilde X/G]\longrightarrow X=\widetilde X/G
\]
be the map from the quotient stack to the coarse quotient, and let
\(\widetilde{\mathscr A}\) be a \(G\)-equivariant coefficient complex.
Deninger's degreewise invariant coefficient is
\[
 \mathscr A_X=c_*\widetilde{\mathscr A}
 =(\pi_*\widetilde{\mathscr A})^G.                                \tag{1}
\]
There is a canonical comparison
\[
 c_*\widetilde{\mathscr A}
 \longrightarrow
 Rc_*\widetilde{\mathscr A}.                                     \tag{2}
\]

## Theorem

`[PROVED HERE] [DAC_COARSE_STACK_EXACTNESS_SCALAR_SPECTRUM_NO_GO]`

Assume:

1. `(2)` is a quasi-isomorphism;
2. on quotient-stack cohomology, the rational power action in degree
   one is the scalar Tate action;
3. its suspension is strongly continuous.

Then Deninger's coarse invariant-sheaf \(H^1\) has scalar flow and its
generator has only the scalar Tate weight as a point eigenvalue.

## Proof

Applying \(R\Gamma(X,-)\) to `(2)` and using derived descent gives a
flow-equivariant quasi-isomorphism
\[
 R\Gamma(X,c_*\widetilde{\mathscr A})
 \simeq
 R\Gamma([\widetilde X/G],\widetilde{\mathscr A}).                 \tag{3}
\]
Thus the scalar rational-time action on stack \(H^1\) transports to
Deninger's \(H^1\).  Strong continuity and density of
\(\log\mathbb Q_{>0}\subset\mathbb R\) make the entire flow scalar.
`DAC_PURE_SUSPENSION_SCALAR_SPECTRUM_NO_GO` then implies that its
generator has no other point eigenvalue.

The nontrivial zeta divisor contains infinitely many distinct points,
so it cannot be the point spectrum of this scalar generator.

## Consequence

Any successful source construction must have a nonzero comparison
defect
\[
 \mathscr D_c
 =
 \operatorname{Cone}\!\left(
 c_*\widetilde{\mathscr A}\to
 Rc_*\widetilde{\mathscr A}\right)[-1].                            \tag{4}
\]
This conclusion does not replace Deninger's definition by derived
invariants.  It identifies the obstruction to doing so.

## Gates

- [x] dependency-closed paper proof
- [x] dense-time scalar-flow and scalar-eigenvalue core formalized in
  `DeningerArithmeticPureSuspensionNoGo.lean`
- [ ] derived-topos comparison formalization in Lean

## Falsifiers and scope

- Nonzero \(\mathscr D_c\) does not prove that its cohomology contains
  zeta eigenvalues.
- Higher group cohomology alone is not Deninger's cohomology; only its
  proved interaction with `(4)` matters.
- The theorem makes no Xi, RH, positivity, or determinant assumption.

## Log

- 2026-07-26 — Isolated the canonical coarse-moduli exactness
  obstruction forced by Deninger's underived invariant sheaf.

## Lean status

### What landed

`formal/GaloisForLFunctions/RHTower/DeningerCoarseStackScalarNoGo.lean`, on top of the already
formalized dense-time core in `DeningerArithmeticPureSuspensionNoGo.lean`.  Axiom audit for all 5
declarations: `propext, Classical.choice, Quot.sound`.

- `deningerScalarFlow_transport` — **the transport step of `(3)`**: if the comparison induces an
  isomorphism intertwining the two flows, a scalar flow on the stack side is a scalar flow, with
  the same scalars, on the coarse side.  Hypothesis 1 of the theorem enters exactly here, as the
  equivariant isomorphism it provides.
- `deningerPointSpectrum`, `deningerScalarGenerator_pointSpectrum_subset` — a scalar generator has
  at most its weight in the point spectrum.
- `deningerScalarGenerator_no_two_eigenvalues`,
  `deningerScalarGenerator_not_scalar_of_two_eigenvalues` — **the conclusion**: two distinct point
  eigenvalues are impossible for a scalar generator, so a spectrum with two distinct points — in
  particular the infinite nontrivial zeta divisor — cannot be realized, and any coefficient that
  realizes it has nonzero comparison defect `(4)`.
- Hypothesis 3, strong continuity, together with the density of `log ℚ_{>0}` in `ℝ`, is
  `deningerPureSuspension_flow_eq_of_dense`; the scalar-eigenvalue step is
  `deningerPureSuspension_eigenvalue_eq_weight`.  Both were already in the tree.

### What is still missing, and why

The derived-topos step itself — applying `RΓ` to `(2)` and invoking derived descent for the
quotient stack to obtain `(3)` — cannot be stated: mathlib has no derived categories of sheaves on
a site, no quotient stacks and no descent for them.  So the gate
`derived-topos comparison formalization in Lean` stays open, and the card stays at stage 2.  What
is formalized is the whole consequence chain that follows once `(3)` is granted: transport of
scalarity, dense-time rigidity, and the impossibility of two distinct eigenvalues.
