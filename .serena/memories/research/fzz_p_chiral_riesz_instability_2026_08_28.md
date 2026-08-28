# FZZ-P chiral Riesz instability (2026-08-28)

Module: `formal/GaloisForLFunctions/RHTower/FZZCigarParityChiralRieszInstability.lean`.

Let `P=P(beta)`, `Q=P(2 beta)`, `R=P(4 beta)`, and `E=Q²-PR>0`. The HC2 unit chiral Hermitian form `Y=[[0,i],[-i,0]]` has exact source-metric Riesz representative `B=G⁻¹Y=E⁻¹[[-iQ,-iR],[iP,iQ]]` for `G=[[P,Q],[Q,R]]`. It is formally G-self-adjoint.

For the canonical traceless FZZ source-Krein generator `A`, every real perturbation `A_gamma=A+gamma B` is formally G-self-adjoint. Its exact instability discriminant is `Delta_gamma=Delta_0+gamma²/E>0`. The module constructs an explicit nonzero eigenvector with eigenvalue `i sqrt(Delta_gamma)`, proves that eigenvalue nonreal and the eigenvector G-neutral for every gamma, and proves strict imaginary-gap growth for gamma≠0. Thus no real chiral Riesz coupling restores spectral reality; it is strictly anti-stabilizing.

Cards: `docs/drafts/pipeline/3-formalized/fzz-p-chiral-riesz-instability.md` and `docs/drafts/pipeline/5-failed/fzz-p-chiral-riesz-stabilization-no-go.md`. Module wired into `GaloisForLFunctions.RHTower`. Direct Lean and targeted build pass. Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`. Frontier map untouched.

Research implication: HC2's chiral reporter now has a canonical dynamical realization, but it closes negatively. A surviving FZZ/GFZZ stability interaction must add a diagonally dominating cone component or use genuinely nonlocal, nonlinear, independent-channel, or singular data before divisor selection.