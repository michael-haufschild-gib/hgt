# TG — Finite-height transfer: RH up to height T ⇒ central budget on (0, πT/2]

- **ID:** TG-FH-1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean, unconditional)
- **Statement:** ∃ universal C: ∀T ≥ 2, if every zero copy with |Im ρ| ≤ T has Re ρ = ½, then
  |G(u)| ≤ C for all 0 < u ≤ πT/2 (G = central Gaussian gap in the log scale).

## Proof
G + Σ ½Γ((ρ−½)/2)e^{(ρ−½)u/2} bounded on u>0 (cycle 31). Critical zeros: term ≤ W|ρ−½|^{-2}. Zeros above T:
‖amp‖e^{(β−½)u/2} ≤ ‖amp‖e^{u/4} ≤ ‖amp‖e^{π|γ|/8} ≤ D|ρ−½|^{-2} for u ≤ πT/2 (sharp strip Γ decay, cycle 28).

## Lean
`RHTower/GaussianCentralGapFiniteHeightTransfer.lean`, wired after GaussianCentralGapFilterLightCone.
`exists_abs_gaussianCentralGapLog_le_of_criticalUpTo`. Axioms [propext, Classical.choice, Quot.sound].

## Reading
Scale–height duality made quantitative: the TG budget at scale u is a statement about zeros of height ≲ 2u/π.
A finite verification of RH (height T) certifies the budget on (0, πT/2] with a T-independent constant.
Converse (budget on (0,U] ⇒ zero-free wedge) needs Pintz/Turán frequency localization (open in corpus).
