# Theta Mellin-six formation of T

- Stage2 card: `docs/drafts/pipeline/2-fully-proven/universal-law-field/restricted-grassmannian-formation-geometry/theta-mellin-six-holonomy-integral-nuclear-formation.md` (ULF-TM6H-001).
- Lean: `RHTower/ThetaMellinSixIntegralNuclearFormation.lean`, wired into `RHTower.lean`; targeted module build green.
- Literal first theta atom Mellin response `A(s)=s(s-1) Gamma_R(s)/2`. Forced pole-stripped response `Gθ(s)=2A(s)/(s(s-1))=Gamma_R(s)` for `Re(s)>1`.
- Normalized six-step holonomy `H_n=[Gθ(2n+3)/Gθ(2n+9)]/[Gθ(3)/Gθ(9)]` equals `PrimeHodgeHistory.m n=105/((2n+3)(2n+5)(2n+7))` exactly.
- Adjacent loss `H_n-H_(n+1)=w_n`; tail sum reconstructs `H_n`; `primeHodgeHistoryDiagonalWeight` equals this theta flux times coefficient-faithful prime density. Thus T history is literally theta-formed before divisor input.
- Hodge interpretation: `h(a)=-(1/(2pi))Gθ(2a+1)/Gθ(2a+4)`; the two forced grades `a=n+1,n+5/2` telescope through shared Mellin grade `2n+6`, producing one global six-step holonomy.
- Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`.
- Remaining RH edge: prove completed Xi relative energy is the same boundary functional after forced covariance/metric renormalization and residual completion boundary vanishes. Divisor-specialized flatness or finite Gamma energy is circular.
- Failed selectors recorded in STATUS: Petz/common recovery is information-neutral at all grades; nonseparable flatness is RH-equivalent after divisor specialization; strict contraction holds off-neutral; small trace selfcommutator cannot kill Fredholm index due scalar shift scaling.