# Xi heat-moment Ritz velocity

- **Stage:** 1-in-progress
- **Type:** THEOREM; generic final source audit pending
- **Statement:** A stationary or right-moving differentiable generalized eigenvalue branch of the actual finite Xi heat-moment pencil falsifies RH.

## Source and novelty question

`XiGaussianHeatEndpointRigidity.hasDerivAt_heatMomentInner` supplies the actual moment
evolution `s'_k=-s_(k+1)`. Existing heat-moment work resolves determinant signs, singular
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

The same identity holds in any fixed finite polynomial trial space: test the differentiated
weak eigenvalue equation against `p`, and the original equation against `p'`.
No simplicity assumption or monomial basis is required.

## Lean

- `HilbertMetric/MomentFlow/RitzVelocity.lean`: `ritz_velocity_identity`, `ritz_velocity_neg`.
- `arithmetic-positivity-theory/MomentFlow/XiRitzVelocity.lean`:
  `xiHeatRitz_velocity_neg_of_rh`,
  `not_riemannHypothesis_of_xiHeatRitz_nonnegative_velocity`.

Generic dependency build and actual Xi source audit pass; all printed transitive axioms are
`propext`, `Classical.choice`, `Quot.sound`. Both modules are wired into their owning umbrellas.
No umbrella build was run. The generic module still requires its final no-output-file check.
