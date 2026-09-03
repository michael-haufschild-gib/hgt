# Theta/Xi leading-jet parity cancellation (2026-09-02)

Active card: `docs/drafts/pipeline/1-in-progress/multiplicity-parity-ladder-route.md`.

New unconditional Lean module: `formal/GaloisForLFunctions/RHTower/HedenmalmThetaXiJetParityCancellation.lean`, wired into `RHTower.lean`.

Theorems:
- `xiJetParity_mul_thetaDepthCharacter_eq_neg_one`: at every Xi divisor support point of multiplicity m>0, the Xi leading-jet FE parity `(-1)^m` times the actual theta terminal-current depth character `(-1)^(m-1)` is exactly `-1`.
- `ccmRationalAdelicPrimeXiCartierCoefficient_reflection_mul_thetaDepthCharacter`: leading-coefficient-weighted terminal theta current is reflection-odd for every multiplicity.

Interpretation: actual Xi on-shell Wronskian/leading-jet orientation cannot force even multiplicity. Its unconditional oddness includes the Xi leading-coefficient parity, which cancels the terminal depth parity. Dividing out the coefficient recovers the desired bare character but loses the arithmetic orientation being used as producer. This closes equation-Wronskian, first-nonzero-jet, and coefficient-normalized determinant-line orientation as base-rung producers.

Verification: direct `lake env lean` and targeted `lake build GaloisForLFunctions.RHTower.HedenmalmThetaXiJetParityCancellation` passed. Axioms: `propext`, `Classical.choice`, `Quot.sound` only. Scoped `git diff --check` passed.

External audit: Alpöge--Furman arXiv:2608.13637 gives unconditional density of simple on-line zeros; Ivić arXiv:math/0501434 gives multiplicity bounds. Neither constructs half-divisor or constrains parity of hypothetical right-half zeros.

Open core unchanged: construct analytic `g` on Re(s)>1/2 with `g^2=xi`, equivalently force bare `thetaDepthCharacter=-1` on every right-half Xi support point from a source law that does not reinsert leading Xi coefficient.