Formalized exact valuation-one arithmetic root target in `formal/GaloisForLFunctions/RHTower/XiPoleClearedFirstTraceRootReduction.lean`, wired into `RHTower.lean`.

Key objects:
- `squarefreeCarlemanHalfDet(s)=exp((1/2)*squarefreeCarlemanLogDet(s))`; explicit analytic square root of `squarefreeCarlemanDet` on rightHalf.
- `poleClearedFirstTraceExponentialContinuation(s)=squarefreeMobiusCriticalPoleUnit(s)/squarefreeCarlemanDet(s)`.
- This field is analytic on rightHalf and has exactly Xi's analytic divisor.
- On farHalf Re(s)>1 it equals `(s-1)*exp(coronaPrimeZeta(s))`.
- Fixed arithmetic Euler half-germ `poleClearedPrimeZetaHalfEulerGerm(s)=exp((1/2)*(log(s-1)+coronaPrimeZeta(s)))`, analytic and squaring to first-trace field on farHalf.
- Exact theorem `rhLadder_one_iff_poleClearedPrimeZetaHalfEulerGerm_extends`: RHLadder1 iff fixed Euler half-germ literally extends to an analytic square root on rightHalf. Sign oriented at s=2; connected root uniqueness yields EqOn over all farHalf.

Interpretation: archimedean completion, doubled zeta, and every valuation>=2 prime-power term have explicit analytic halves. Sole open core is single-valued continuation/monodromy of pole-cleared valuation-one prime trace. Writing exp(P/2) without proving this continuation is circular.

Verification: direct lean and targeted build passed. All audited theorems depend only on propext, Classical.choice, Quot.sound.