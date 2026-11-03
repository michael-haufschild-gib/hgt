# F2 — arithmetic reflection on the physical Mellin side

- **Stage:** 1-in-progress
- **Question:** Can spectral reflection be realized by an arithmetic operator on actual core functions, with its physical domain and norm controlled?
- **Target:** A source-defined reflection law, including the Cauchy averaging factors. Positivity remains a separate obligation.

## Candidate mechanism

Write `w=2s`, `w♯=1−conjugate(w)`, `G_w=Γℝ(w)fieldCore_w`, and `Λ(u)=Γℝ(u)ζ(u)`. Existing theta factorization gives `M G_w(u)=Λ(u)Λ(w−u)` on its initial strip. At a resonance, the improved endpoints allow continuation across the imaginary Mellin axis.

The functional equation suggests

`M G_(w♯)(u) = S(u) conjugate(M G_w(−conjugate(u)))`,

where the arithmetic multiplier is

`S(u) = ((u+1)/(u−1)) ξ(u)/ξ(−u)`.

On `u=it`, this should have modulus one. The apparent singularity at `u=0` has already been removed in this xi expression. The proposed physical operator is conjugate inversion followed by this Mellin multiplier. Establish the literal transform identity and its Haar-space realization before claiming an operator theorem.

For averaged PM cores the multiplier additionally contains

`Γℝ(conjugate(w))/Γℝ(w♯) · symbol(w♯,u)/symbol(conjugate(w),−u)`.

Its Gamma quotient suggests frequency order `1/2−Re w`; boundedness on one fixed Haar space must be checked. An algebraic parameter identity alone does not establish boundedness, intertwining of the full transfer family, or positivity.

## Gates

- [ ] Audit novelty and existing arithmetic-reflection results.
- [ ] Prove the literal imaginary-axis Mellin identity for resonant fields and averaged cores.
- [ ] Determine the exact physical operator domain and norm law.
- [ ] Formalize the resulting source theorem; retain any regularity obstruction explicitly.
