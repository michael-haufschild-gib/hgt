# Hyperbolic volume and the finite cubic quotient

- **ID:** hyperbolic-volume-and-finite-cubic-quotient
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [cubic theta residue](../1-in-progress/cubic-theta-residue-and-gauss-coefficients.md)
- **Statement:** Construct the invariant upper-half-space measure `dx dy dv/v³`; prove that the actual cubic kernel quotient has positive finite volume.

Euclidean inversion has derivative equal to a reflection scaled by
`‖p‖⁻²`. Its absolute Jacobian `‖p‖⁻⁶` cancels the transformed height
weight. Horizontal translations and complex diagonal dilations preserve
the same density. The explicit Möbius coordinate formulas and Bruhat
factorization therefore prove invariance under every `SL₂(ℂ)` matrix.

A horizontal unit box above height `a>0` has volume `2/a²`. The finite Ford
cover bounds the measure of the measurable fundamental selector by finitely
many such boxes. Positivity follows because a countable union of null
translates cannot cover a nonzero invariant measure. Pushforward of the
restricted measure defines the quotient volume independently of the selector.

Sources: external OpenAI `CubicSieve/ArithmeticBins.lean`,
`Eisenstein/HyperbolicVolume.lean`, `Eisenstein/FundamentalDomain.lean`,
and `QuadraticSieve/SelectedExponents.lean`.
Lean `HyperbolicVolumeIsInvariant.lean` proves inversion invariance, the full
Möbius coordinate formula, and `hyperbolicVolume_invariant`. Direct source
check passed; the three transitive axiom audits contain only `propext`,
`Classical.choice`, `Quot.sound`.

`TheCubicQuotientHasFiniteVolume.lean` proves
`integralQuotientVolume_independent`, `euclideanCuspBox_volume`,
`kernelQuotientVolume_pos_finite`, and `kernel_eisenstein_invariant`.
Direct source check passed; all four transitive axiom audits contain only the
same three standard axioms. The compact Sobolev estimate and spectral residue
remain separate analytic obligations.
