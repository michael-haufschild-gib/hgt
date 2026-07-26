# Endpoint purity from \(H^0\) and Poincaré duality

- **ID:** `deninger-endpoint-purity-from-h0-duality`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Parent:** `deninger-three-term-cup-poincare-descent`
- **Statement:** One-dimensional \(H^0\) with trivial flow and perfect weight-one endpoint
  duality force \(H^2\simeq R(-1)\) and \(\Theta_2=1\).

## Goal

Remove \(H^2\) and its weight from the list of independent arithmetic conjectures.
Deninger's approximation already proves the \(H^0\) input.  Corrected coefficients need only
preserve it and supply perfect endpoint duality.

## Gates

- [x] 0 → 1 in-progress: exact hypotheses isolated
- [x] 1 → 2 fully-proven: dependency-closed proof below
- [ ] 2 → 3 formalized: direct Lean check of
  `DeningerArithmeticEndpointPurity.lean`
- [ ] 3 → 4 publication-ready: instantiate on the arithmetic coefficient complex

## Theorem

`[PROVED HERE] [DAC_ENDPOINT_PURITY]`

Let \(H^0,H^2\) be modules with a pairing
\[
 \langle-,-\rangle_{02}:H^0\times H^2\to R
\]
that separates \(H^2\).  Suppose
\[
 \Theta_0=0
\]
and the pairing has weight one:
\[
 \langle\Theta_0x,z\rangle_{02}
   +\langle x,\Theta_2z\rangle_{02}
 =\langle x,z\rangle_{02}.                                             \tag{1}
\]
Then
\[
 \Theta_2=1.                                                           \tag{2}
\]

If moreover \(H^0\simeq R\) and the pairing is perfect, then
\[
 H^2\simeq (H^0)^\vee\simeq R,
\]
with flow of weight one, conventionally written \(H^2\simeq R(-1)\).

## Proof

Substituting \(\Theta_0=0\) in `(1)` gives
\[
 \langle x,(\Theta_2-1)z\rangle_{02}=0
\]
for every \(x\).  Separation in the second variable gives
\((\Theta_2-1)z=0\) for every \(z\), proving `(2)`.  Perfectness identifies \(H^2\) with
the dual of \(H^0\); the dual of the rank-one free module is rank-one free.

## Arithmetic input and consequence

Deninger, Theorem 10.2 of *Dynamical systems for arithmetic schemes*, proves that the
zeroth leafwise cohomology of the rational-Witt dynamical systems under consideration
consists only of constants and carries trivial \(\mathbb R_{>0}\)-action.  Therefore the
derived correction must prove:

1. realified higher coefficient terms do not create new degree-zero invariants;
2. the corrected \(H^0\) comparison with Deninger's constant class is an isomorphism;
3. endpoint cup/trace pairing is perfect and has weight one.

Once these hold, the expected top cohomology and its generator are consequences.

## Hostile audit

- The theorem does not construct endpoint Poincaré duality; it shows its exact payoff.
- Separation, not merely a nonzero pairing, is required.
- Deninger's \(H^0\) theorem concerns the approximation with its leafwise sheaf.  Preservation
  under the derived coefficient correction is still an arithmetic comparison obligation.

## Reference

- Christopher Deninger, *Dynamical systems for arithmetic schemes*, Theorem 10.2:
  https://arxiv.org/abs/1807.06400

## Log

- 2026-07-26 — endpoint weight reduced to \(H^0\) preservation plus perfect duality.
