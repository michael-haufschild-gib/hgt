# Prime Vandermonde defect as a scalar Schur residual

- **ID:** prime-vandermonde-schur-residual
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) - grade **BRIDGE**
- **Source:** `../../2-fully-proven/not_new_scientific_knowledge/pinned-affine-prime-jet-rigidity.md`
- **Statement:** The canonical one-sided and functional-equation-paired first omitted-order defects
  are the negative scalar Schur complements of their bordered moment matrices. The one-sided
  residual is `Q_k'(0)>0`; the paired residual is the alternating constant term `Q_k(0)` at squared
  prime-log nodes.

## Goal

Identify the exact finite-dimensional linear-algebra object behind the previously proved defect
`-Q_k'(0)`. This is the finite-section prerequisite for asking whether those defects converge to,
or approximate, a defect of a fixed global Hilbert sampling operator.

## Theorem

For distinct frequencies `f_i`, let

`A_(j,i) = f_i^j`, `0 <= j < k`,

let `B_j = delta_(j,1)`, let `C_i=f_i^k`, and let `D=delta_(k,1)`. Define the canonical interpolation
packet `a=A^(-1)B`. The scalar Schur complement of the bordered moment matrix is

`R_k = D-C A^(-1) B`.

Then

`C a-D = -R_k`

and

`det [[A,B],[C,D]] = det(A) R_k`.

For real nodes, the existing node-polynomial calculation gives

`R_k = Q_k'(0)`, where `Q_k(X)=prod_i (X-f_i)`.

At the prime-log nodes `f_i=-log p_i`, with distinct labels `p_i>1`, one has `R_k>0`; hence the
canonical next-order defect is exactly `-R_k=-Q_k'(0)<0`.

Under functional-equation pairing, antisymmetric evaluation at `+/-log p_i` kills the even moments
and reduces the odd moments to origin-value interpolation at `x_i=(log p_i)^2`. The paired scalar
Schur residual is

`R_k^FE = Q_k(0) = prod_i (-(log p_i)^2)`,

and the first omitted odd defect is `-R_k^FE`. Thus reflection changes the Schur invariant from the
derivative `Q_k'(0)` to the constant term `Q_k(0)`. Its sign alternates with `k`; completion does not
preserve the one-sided positive orientation and does not create a positive Gram residual.

## Scope

- `[PROVED]` This is a genuine scalar Schur complement of a bordered, generally non-Hermitian
  moment matrix.
- `[PROVED]` It is not a positive-semidefinite Gram Schur complement. Its positivity comes from the
  orientation of the negative real prime-log nodes.
- `[PROVED]` Functional-equation pairing changes the residual to the signed squared-log product.
  The alternating sign rules out interpreting the paired finite defects as positive Gram Schur
  complements.
- `[NOT CLAIMED]` No global sampling operator, infinite-section convergence, closed-range theorem,
  or theta-source adjoint-range membership follows from the finite identity.
- `[OPEN CORE]` Construct the actual canonical Hilbert sampling operator and prove whether these
  bordered finite sections approximate its projection or reconstruction residual.

## Gates

- [x] 0 -> 1 in-progress: exact bordered moment system and scalar residual identified.
- [x] 1 -> 2 fully-proven: inverse solution, Schur identity, determinant factorization, and prime
  sign proved algebraically.
- [x] 2 -> 3 formalized: Lean modules `PrimeVandermondeSchurResidual` and
  `FEPairedVandermondeSchurResidual`; focused builds green; axiom audits report only
  `[propext, Classical.choice, Quot.sound]`.
- [ ] 3 -> 4 publication-ready: package only together with a proved global finite-section limit.

## Lean certificate

- `finiteDerivationSchurResidual_apply`
- `canonicalFiniteDerivationNextDefect_eq_neg_schurResidual`
- `finiteDerivationBorderedMatrix_det_eq_sampling_det_mul_schur`
- `finitePrimeDerivationSchurResidual_eq_nodePolynomialDerivative`
- `finitePrimeDerivationSchurResidual_re_pos`
- `canonicalFiniteOriginNextDefect_eq_neg_schurResidual`
- `finiteOriginBorderedMatrix_det_eq_sampling_det_mul_schur`
- `fePairedPrimeBarycentricFirstOmitted_eq_neg_schurResidual`
- `finiteFEPairedPrimeSchurResidual_eq_signedLogSqProduct`

## Novelty and significance

The Schur-complement identity is standard finite-dimensional algebra and therefore not new
scientific knowledge. Its value is diagnostic: it fixes the sign and exact matrix meaning of the
finite obstruction while preventing an unjustified identification with a global Hilbert or Pick
residual.

## Log

- 2026-07-11 - Proved and formalized the exact one-sided and FE-paired Schur-complement identities,
  determinant factorizations, node-polynomial values, positive one-sided orientation, and
  alternating paired orientation.
