# Xi heat-moment Ritz velocity

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Statement:** A stationary or right-moving differentiable generalized eigenvalue branch of the actual finite Xi heat-moment pencil falsifies RH.

## Source and novelty question

`HankelHeatAdmissionFlow` supplies the actual moment evolution `s'_k=-s_(k+1)` and the
canonical polynomial connection. Existing heat-moment work resolves determinant signs, singular
gaps, Padé cancellation, and escaping polynomial roots. The candidate concerns the sign of motion
inside a regular finite section, not a determinant defect or a nonreal zero.

## Proposed identity

Let `H=(s_(i+j))`, `K=(s_(i+j+1))`, and `J=(s_(i+j+2))` at positive heat time.
For a differentiable real branch `K v = lambda H v`, differentiation and symmetry cancel all
eigenvector-velocity terms:

`lambda' (vᵀ H v) = -vᵀ J v + lambda² vᵀ H v`.

For `p(X)=sum_i v_i X^i`, the right side is
`-L(((X-lambda)p)^2)`. Under RH the actual heat moment form is strictly positive; both
`p` and `(X-lambda)p` are nonzero. Therefore `lambda'<0`.

## Required audits

- Search for existing generalized heat eigenvalue monotonicity endpoints.
- Verify the actual heat-moment positivity and derivative inputs in Lean.
- Prove the exact finite variance identity without assuming spectral simplicity.
- Formalize the closed existential witness implication to `¬ RiemannHypothesis`.
