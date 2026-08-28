# FZZ-P Hermitian reflection detector cone (2026-08-28)

Module: `formal/GaloisForLFunctions/RHTower/FZZCigarParityHermitianReflectionDetectorCone.lean`.

Sharp theorem: a fixed Hermitian reporter with block coefficients `(a,b,c,d)` separates every carrier `(1,r(x+iy))`, `r>0`, `r≠1`, `x²+y²=1`, from reciprocal-radius reflection iff `d≠0 ∧ b²+c²≤d²`. Exact defect is `(r-r⁻¹)(d(r+r⁻¹)+2(bx-cy))`; `a` cancels. Sufficiency uses Cauchy--Schwarz and `(r+r⁻¹)²>4`. Necessity is constructive for `d=0` and `d²<b²+c²`.

For the centered dyadic FZZ Mellin character, critical-line reflection preserves phase and inverts radius, while radius one is equivalent to `rho.re=1/2`. Hence every reporter in the punctured Lorentz cone has reflected reading equality iff the critical-line condition. Universal matching on parity-Mellin divisor modes is equivalent to RH; deriving matching from FZZ/GFZZ dynamics remains open.

Cards: `docs/drafts/pipeline/3-formalized/fzz-p-hermitian-reflection-detector-cone.md` and `docs/drafts/pipeline/5-failed/fzz-p-hermitian-reporters-outside-reflection-cone.md`. Module is wired into `GaloisForLFunctions.RHTower`. Direct Lean and targeted build pass. Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`. Frontier map untouched.

Research implication: source chiral orientation and phase-uniform radial reflection are distinct. Chiral-only `d=0` reporters always have blind phases; viable fixed reflection reporters need a nonzero diagonal coefficient dominating off-diagonal magnitude.