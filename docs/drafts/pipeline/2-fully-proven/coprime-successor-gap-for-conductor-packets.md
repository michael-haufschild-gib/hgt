# Coprime successor gaps for conductor packets

- **ID:** coprime-successor-gap-for-conductor-packets
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** The proved successor-gap step in `shell-degree-bounds-and-complete-packet-rigidity.md`.
- **Statement:** A finite Ramanujan packet has successor difference energy at least
  its nonconstant mass. Coprime dilation preserves this bound; a window of length
  `K≥Q(Q−1)` retains at least `(K−Q(Q−1))` times that mass.

## Proof

Write `F(n)=Σ_(1≤m≤Q) a_m c_m(n)` and
`M=Σ_(2≤m≤Q) φ(m)a_m²`. Exact period orthogonality gives

`mean (F(n+1)−F(n))² = Σ_m 2(φ(m)−μ(m))a_m²`.

The constant mode contributes zero and parity contributes `4a_2²`.
For `m≥3`, the proved bound `|μ(m)/φ(m)|≤1/2` gives a contribution
at least `φ(m)a_m²`. Thus the energy is at least `M`.

If `gcd(p,Q!)=1`, each Ramanujan mode satisfies `c_m(pn)=c_m(n)`.
Multiplication by `p` permutes residues modulo `Q!`, so the complete-period
energy of `F(pn+1)−F(n)` equals that of `F(n+1)−F(n)`.
The relative affine-window estimate has error at most `Q(Q−1)` times
this exact period energy. Its lower bound is therefore
`(K−Q(Q−1))M` when `K≥Q(Q−1)`.

## Lean

`CriticalScaleArithmeticRigidity/CoprimeSuccessorGap.lean`; direct audit pending.
The full Weil-energy comparison is not part of this statement.
