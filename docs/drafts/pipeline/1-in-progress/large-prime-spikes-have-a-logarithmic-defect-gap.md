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

Corpus boundary: `jumpEnergy_eq_poleDefect` identifies the exact Dirichlet
form, and the incidence packet formula identifies prime-power jumps.
Existing conductor gap estimates use a below-square-root frame or a small
multiple of `log Q`; the proposed finite gap reads the disjoint large-prime
edges directly. Exact incidence reduction and Lean formalization remain open.
