# FZZ parity source-balanced Mellin reflection (F10)

F10 proved and formalized. For beta>0 let a=sqrt(P(4 beta)/P(beta)) and w_beta(rho)=(1,a^-1 chi(rho)), where chi is the centered dyadic Mellin character. The canonical F9 source-metric antiunitary satisfies J_beta(w_beta(rho))=conj(chi(rho)) • w_beta(1-conj rho). Thus in balanced projective coordinate a*u2/u1 it implements functional-equation reflection exactly.

The balanced grade crossing normalized by the norm of the second coordinate has exact formula q*chi/|chi| + r*a^-1*|chi|. Its reflected defect is a^-1 times the F8 raw defect, so equality iff Re rho=1/2. Matching on all open-strip parity-Mellin modes at one positive scale iff RH.

New insight: F9's unique inverse-diagonal correction is square of the forced source half-density coordinate. Antiunitary/reflection-carrier construction is now unconditional; remaining FZZ-P burden is dynamical equality of balanced grade crossings on literal divisor modes.

Module: formal/GaloisForLFunctions/RHTower/FZZCigarParitySourceBalancedMellinReflection.lean. Card: docs/drafts/pipeline/3-formalized/fzz-parity-source-balanced-mellin-reflection.md. Wired umbrella. Direct Lean and targeted module build pass. Axioms only [propext, Classical.choice, Quot.sound]. Global lint has no issue in module; failures are unrelated unreachable modules. Frontier map not edited.