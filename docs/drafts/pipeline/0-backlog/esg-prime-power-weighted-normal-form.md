# Prime-power weights and persistent torsion exponents

- **ID:** esg-prime-power-weighted-normal-form
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Status:** Candidate extension; full paper, novelty and Lean audits pending

## Target

Replace prime-valued weights by `d_r(e_p)=p^r`, for integers `r≥0`.
The actual product-cutoff chain persistence should again admit a two-prime
normal form over every commutative ring, now with row `(2^r,3^r)` and column
`(−3^r,2^r)`. Its four birth heights should remain `m,2m,3m,6m`.

The expected lower branch is `R[m,2m)→R/2^rR[2m,3m)`, with reduction.
The upper branch is `Ann_R(2^r)[2m,3m)→R[3m,6m)`.
Over the integers this would give sharp torsion exponent `2^r` for `r≥1`;
at `r=0` it should recover the unweighted odd-squarefree barcode.

## Candidate mechanism

Choose integers `a,b` with `a2^r+b3^r=1`, possible since the two powers are
coprime. Put `u=ae₂+be₃`; let `ψ` retain the large-prime weights and vanish
at two and three. Then `φ_r(u)=1`, `ψ(u)=0`. The same square-zero correction
`H=u∧ιψ` should give inverse cutoff-preserving maps `1−H`, `1+H`.

For `A=2^r`, `B=3^r`, a row cycle `Ax+By=0` should have the unique form
`(x,y)=(Bc,−Ac)`, with `c=bx−ay`. On `Ann_R(A)`, inclusion into the later
free kernel coordinate is multiplication by `b`; its inverse on that
annihilator is multiplication by `B`. The resulting transition should be
independent of the chosen Bézout coefficients.

## Required comparison and boundary

The [ordinary prime-weight normal form](../3-formalized/esg-two-prime-weighted-normal-form.md)
provides the mechanism at `r=1`. General weighted Koszul and simplicial torsion
theory is classical; the arithmetic cutoff and transition comparison needs
its own audit. The corpus search currently surfaces the proved exponent-two
classification, not the stated full prime-power extension.

A contribution must identify actual chain and homology persistence, prove the
sharp exponent and transition laws, and retain canonical coefficient maps.
Changing torsion exponents while retaining the same height factors would
separate coefficient arithmetic from the geometry of birth times. This alone
would give no signed Euler cancellation or arithmetic height sign.
