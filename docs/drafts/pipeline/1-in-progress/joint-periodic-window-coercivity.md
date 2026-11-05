# Joint periodic window coercivity

- **ID:** joint-periodic-window-coercivity
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** review-0411 §2.1, A3.

## Target

For finitely many smooth windows `gᵢ` and mean-zero periodic twists `χᵢ`,
possibly of different periods, prove eventual positivity of the complete
tilted-spline Weil Gram matrix at every positive critical multiple.
Require independence of the joint functions `(y,r) ↦ gᵢ(y)χᵢ(r)` on a common
period, rather than independence of each factor separately.

## Candidate mechanism

The low-frequency and pole transforms of a coefficient vector `v` are bounded
by `C‖v‖₁/N` after Riemann normalization. Their possible negative contribution
to the normalized form is at most `C′‖v‖₂²/N²`. Above the fixed archimedean
horizon the complete symbol is nonnegative. On `[512N,1024N]`, the mean-value
theorem gives

`∫|Dₓ|² ≥ 256N Σxₙ²`,

since its error is `208Σn xₙ²≤208NΣxₙ²`. The tilted-spline lower bound then
pays `a(log N)/c⁸` times the mass, for `a>0`. The mass matrices converge to
the Gram matrix obtained by averaging over residues and integrating over
the window. Joint independence gives a positive lower eigenvalue `μ`.
Thus the normalized form dominates `(aμ/K−o(1))‖v‖₂²` along
`c_N=max(1,(K log N)^(1/8))`. Real and imaginary coefficient parts give
the same conclusion on the full complex coefficient space. Different
periods pass to their product without changing the actual twists.

Conversely, every relation among the joint functions gives a zero atomic
test at every resolution, so no positive-definite Gram matrix can exist.
Thus joint independence is necessary and sufficient for eventual positivity.

Same-parity character cross spectra are already computed by
`crossSpectralSum_charTwist`. Single-family polarization alone does not
determine mixed terms when both the twist and the spatial window vary.

## Status

`JointPeriodicWindowMass.lean` proves common-period transfer, mixed mass
convergence, positivity of the residue-averaged Gram matrix and its uniform
discrete coercivity. Direct source check and four transitive axiom audits
passed, using only `propext`, `Classical.choice`, and `Quot.sound`.

The existing same-parity cross-spectrum formula and opposite-parity
decoupling passed direct source checking and three transitive axiom audits.

The complete Weil coercivity theorem remains under formalization. No row
closure is claimed.
