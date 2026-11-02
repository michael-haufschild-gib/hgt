# Large prime spikes have a logarithmic defect gap

- **Stage:** 1-in-progress.
- **Type:** CONJECTURE.
- **Wall:** Σ1e.
- **Statement:** On the span of the pole and prime conductors `p>sqrt N`, prime defect is at least `(log N)/2` times squared distance from the pole.

Write `L=log N`, `b_p=a_p/sqrt(p−1)`, and
`A(n)=Σ_p p b_p 1_(p|n)`. Every packet in this span has coordinates
`(A(n)+s)/sqrt(nL)` for some real `s`.

Only dilation by a selected prime changes its incidence indicator. Since
`p²>N`, no higher power of that prime occurs among horizon edges, and every
source `n≤N/p` satisfies `p∤n`. The predicted exact defect is therefore

`D_N = (1/L) Σ_p log p · [p/(p−1)] H_floor(N/p) a_p²`.

Distinct spike supports are disjoint. Put
`D=Σ_p [p/(p−1)] H_floor(N/p) a_p²` and
`T=Σ_p b_p H_floor(N/p)`. Orthogonal removal of the pole gives

`‖u−proj_pole u‖² = (D−T²/H_N)/L ≤ D/L`.

Since `log p>L/2`, the claimed gap follows. This argument needs no upper
polynomial cutoff on the selected primes and no residual-average estimate.

For `p≤N`, write `d_p=[p/(p−1)]H_floor(N/p)` and
`t_p=H_floor(N/p)/sqrt(p−1)`. The centered Gram is exactly
`[diag(d_p)−t tᵀ/H_N]/L`, while the defect matrix is predicted to be
`diag(d_p log p)/L`. Thus pole centering makes the norm smaller without
changing the diagonal defect. This rank-one structure suggests interlacing
of the centered defect eigenvalues with the ordered values `log p`.
The interlacing claim is a separate, unproved strengthening.

Corpus boundary: `jumpEnergy_eq_poleDefect` identifies the exact Dirichlet
form, and the incidence packet formula identifies prime-power jumps.
Existing conductor gap estimates use a below-square-root frame or a small
multiple of `log Q`; the proposed finite gap reads the disjoint large-prime
edges directly. Exact incidence reduction and Lean formalization remain open.

`jumpEnergy_incidencePacket` is the exact incidence-square formula.
For a contributing dilation `k`, its least prime factor lies in the selected
band. The bound `minFac(k)²≤k` for a positive composite `k` forces `k` itself
to be prime because `k≤N`. Hence the exact harmonic diagonal follows by
summing `1/n` on `n≤N/p`.
