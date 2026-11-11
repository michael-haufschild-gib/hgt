# Exact eventual positivity of fixed comb windows

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Targets:** A80/A94; finite-scale sign without a mass error.
- **Lean:** `HodgeTheoryOfAFixedPart.riemannHypothesis_iff_ratioWindow_positive_mass_floor` in `TheRiemannHypothesisIsExactEventualCombPositivity.lean`.

RH holds iff, for every integer `Q≥2`, there is `γ>0` such that at every
sufficiently large `N`, every real coefficient vector on `(N,QN]` satisfies
`γ Σ c_n² ≤ combForm(c)`. Exact eventual nonnegativity is equivalent too,
as `riemannHypothesis_iff_eventually_combForm_nonneg` proves on the cofinal
windows `(N,N+3KN]`.

## Proof

Strict decrease of the restricted Weil ground energy makes its value
strictly positive at every finite aperture under RH. Its Rayleigh bound
passes through simultaneous smoothing of the full packet form and mass.
Consecutive flat packets are orthogonal and each has squared mass one;
the resulting step-form floor is independent of the number of blocks.

Split each finite divisor into block means and a mean-zero remainder.
Charge the Schur error only to the means and retain a positive part of
the counterterm's residual coercivity. Uniform convergence of block forms
pays the mean error. Orthogonality of this decomposition gives a positive
floor for the entire divisor. Zero extension preserves form and mass,
transferring the bound from complete blocks to every fixed ratio window.
The existing asymptotic-floor criterion supplies the converse.

## Scope

The finite-scale converse in A80 is proved. This supplies an exact RH
criterion, not an independent sign producer for B152. Unshifted index
convergence on indefinite windows remains open in A94.

## Formalization

Capstone passed `lake --old env lean`. Supporting modules
`AbsoluteGeometryOfSpecZ/WeilGroundEnergyBoundsBoundedPackets` and
`AbsoluteGeometryOfSpecZ/StepPacketMassAndGroundEnergy` passed with required
oleans. All three umbrella imports are wired.
