# Compact cores cannot fund an all-degree Gamma norm

- **Stage:** 1-in-progress.
- **Question:** Can a fixed compact core pay the natural Gamma norm at every degree?
- **Corpus inputs:** `parabolicPowerEnergy`, `integrable_polynomial_sq_sech`, `firstAtom_polynomial_gamma_payment`.

Conjecture: for every `R>0` and integer core power `m`, no finite `C` satisfies

`∫ℝ P(b)²/cosh(πb/2) db ≤ C · parabolicPowerEnergy R m P`

for every real polynomial `P`.

Candidate quantitative witness: `P_n(b)=(b/R)^n`. Its core energy is at most `2R`, whereas restricting the Gamma norm to `[2R,3R]` gives at least

`R·4^n/cosh(3πR/2)`.

Even and odd subsequences separately escape every fixed comparison constant. The positive survivor is an explicit exponential lower bound on the required degree-dependent payment constant. This would rule out all-rank proofs based only on a fixed compact reserve and a full-support unsigned tail charge; it would not disprove positivity of the actual signed current. The full-support Gamma reserve avoids this particular obstruction. Lean formalization is pending.
