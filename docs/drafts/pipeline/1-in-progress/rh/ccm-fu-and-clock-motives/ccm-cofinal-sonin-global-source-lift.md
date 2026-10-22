# CCM cofinal Sonin global source lift

Status: in progress

## Open core

For the shifted orthonormal exterior-shell embedding
\[
U_N:\ell^2(\mathbb N)\to L^2(\mathbb R),\qquad
U_N e_k=g_{N+k},
\]
prove
\[
\|(P_a-I)U_Nx\|\to0
\]
for every `x`, where `P_a` is the central Sonin projection and the existing
shell theorem gives the convergence only for each basis vector.  Prove the
same after the dilation corner.

## Why this is frontier work

This upgrades the existing one-shell Sonin statement to a single cofinal
isometric transport of the complete infinite Euler source.  Combined with
`dyadicSquarefreeSquareUnitary`, it removes the finite-carrier obstruction
without changing the exact four-unit Fisher norm.  Remaining step is identify
the transported coarea/Laplace column with the Gamma-completed Ward source.

## Falsifier

Any `x ∈ ℓ²` for which the defect fails to tend to zero disproves the proposed
global lift.  Proof must use uniform contraction plus finite-support density;
pointwise shell convergence alone is insufficient.
