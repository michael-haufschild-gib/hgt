# Local filtering of the exceptional prime current

- **Obstacle:** B13; cancellation in B134 for several top ordinates.
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Statement:** In the finite-layer world, every top ordinate can be recovered from finitely many normalized Gaussian-current readings inside any prescribed positive height window. A fixed linear combination, divided by that ordinate's unit phase, has a nonzero limit.

## Mathematical target

Write the known normalized current as
`J(t) = -Σγ mγ exp(πγ/4) exp(iγ φ(t)) + o(1)`,
where `φ(t)=(at+log(t/2))/2` and the sum runs over distinct top ordinates.
For any window length `L>0`, choose `h>0` small enough that the nodes
`zγ=exp(iγah/2)` are distinct and `(r−1)h<L`, where `r` is their number.
For a target `γ₀`, let `P(X)=Πγ≠γ₀(X−zγ)`.
The proposed extraction is

`Σj P.coeff(j) J(t+jh) / exp(iγ₀φ(t)) → -mγ₀ exp(πγ₀/4) P(zγ₀) ≠ 0`.

The logarithmic phase correction tends to zero under each fixed height shift.
Polynomial evaluation annihilates the other ordinates. This would force a
uniform positive normalized reading among the finite probes at every large
height, even when the unfiltered current cancels.

## Novelty boundary

The corpus proves a sharp envelope recurring with bounded gaps and pointwise
divergence for one top quartet. It also proves abstract Vandermonde window
bounds and nonvanishing oscillatory jets. The target here is exact recovery
of each actual top multiplicity from the complete infinite prime current,
with all probes confined to an arbitrarily short prescribed window.

## Remaining input for B13

An independent arithmetic upper estimate for these local current readings.
Filtering alone supplies no such estimate and excludes no zero.
