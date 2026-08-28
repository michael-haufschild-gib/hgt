# FZZ-P diagonal Riesz stabilization (2026-08-28)

Module: `formal/GaloisForLFunctions/RHTower/FZZCigarParityDiagonalRieszStabilization.lean`.

For `P=P(beta)`, `Q=P(2 beta)`, `R=P(4 beta)`, `E=Q²-PR>0`, the HC3 unit second-coordinate reporter `D=diag(0,1)` has exact source-metric Riesz representative `B_D=E⁻¹[[0,Q],[0,-P]]`. The family `A_gamma=A+gamma B_D` is formally Krein-self-adjoint with trace `-gamma P/E`, determinant `Delta_0(1+gamma/E)`, and characteristic discriminant `gamma²P²/E²-4Delta_0(1+gamma/E)`.

At canonical source-only coupling `gamma_*=-E<0`, the second column vanishes: `A_gamma*=[[P,0],[-PQ/R,0]]`. Hence `A_gamma*²=P A_gamma*`, determinant zero, characteristic discriminant `P²`, and every eigenvalue is real. Explicit eigenpairs have eigenvalues `0` and `P`. This stabilization exists at every positive scale without Mellin/divisor input.

The generating unit diagonal energy remains an exact critical-line detector: reflected equality on the centered FZZ Mellin carrier iff `rho.re=1/2`. Therefore finite local spectral stability and reflected-energy matching are distinct; stability is unconditional, matching on all divisor modes remains RH-strength.

Cards: `docs/drafts/pipeline/3-formalized/fzz-p-diagonal-riesz-stabilization.md` and `docs/drafts/pipeline/5-failed/fzz-p-local-spectral-stability-selector-no-go.md`. Module wired into `GaloisForLFunctions.RHTower`. Direct Lean and targeted build pass. Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`. Frontier map untouched.