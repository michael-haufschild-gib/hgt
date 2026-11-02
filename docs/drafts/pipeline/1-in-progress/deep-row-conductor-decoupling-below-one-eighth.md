# Deep-row conductor decoupling below the eighth root

- **Stage:** 1-in-progress.
- **Type:** CONJECTURE.
- **Wall:** Σ1b; completion of the all-vector range `α<1/8`.
- **Parent:** [eighth-root positivity](off-pole-nonratio-cross-and-one-eighth-weil-positivity.md).

## Target

Write `L=log N`, `Q=floor(L^q)`, `R=floor(N^θ)`,
`y=Σ_(m≤Q) a_m v_m`, and `E(a)=Σ_(m≤Q) E_m(c)a_m²`.
For `0<α<1/8`, choose `3α<q<(1−α)/2` and sufficiently small fixed `θ>0`.
Conjecturally, for every `ε>0`, eventually uniformly in `1≤c≤L^α`,

`2|⟨W y,u⟩| ≤ ε E(a)+ε‖u‖²`

for every `u∈V_R∩V_Q^⊥`. The required conclusion is all-vector complete
Weil positivity below `1/8`, after combining this estimate with the existing
packet, band, far-complement, and band–far bounds. This card alone does not
establish that conclusion.

## Proposed mechanism

Split the residual `r_m=Wv_m−E_m(c)v_m` at
`M=floor(N exp(−sqrt L))`. Orthogonality removes its eigenvector term.
The conductor large-sieve estimate should bound the terminal mass of every
`u∈V_R` by `O(L^(−1/2))‖u‖²`. Combining this with the existing global
inverse-energy residual bound gains half a logarithmic power in the
terminal pairing.

The deep rows have `N/n≥exp(sqrt L)`. The existing
`exists_deepMass_conductorResidual_le` retains the completed-shell
cancellation: its prime term is `O(m(1+log m)²/L)`, independent of `c`;
near channels vanish; other channels carry inverse powers of `X` or `N`,
apart from the uniform shifted-shell error. Its inverse-energy prime sum
is `O((c⁷+Q²(1+log Q)²)/L)`, which tends to zero.

The terminal packet estimate is already available as
`harmonicConductorPacket_terminal_le`. The complement assembly is also
available as `exists_complement_block_reserves_below_one_eighth`.
The new obligation is their uniform combination with the deep-row rate
and low-packet Schur estimate, followed by the all-vector conclusion.

## Remaining proof obligations

1. Specialize the existing deep-row estimate and shifted-shell rates to
   an inverse-energy sum tending uniformly to zero.
2. Transfer the terminal packet bound to horizon vectors and prove the
   displayed cross estimate.
3. Pay the low-packet/far interaction from the retained far-block reserve.
4. Assemble all blocks, formalize the all-vector theorem, and audit its
   transitive axioms. No wall-status change before this conclusion is proved.
