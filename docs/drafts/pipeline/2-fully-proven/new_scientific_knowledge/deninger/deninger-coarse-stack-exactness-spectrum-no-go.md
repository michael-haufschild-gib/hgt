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
