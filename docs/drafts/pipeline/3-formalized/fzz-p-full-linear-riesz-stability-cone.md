# FZZ-P full linear Riesz stability cone

## Status

Formalized in Lean 4 on 2026-08-28. Frontier label: HC35.

## Route

FZZ parity-delay (FZZ-P).

## Problem

The literal parity-delay source has two canonical Hermitian reporters on its indefinite two-scale Krein block: unit second-scale diagonal energy and oriented chiral crossing. Their source-metric Riesz representatives define a full real two-parameter local interaction plane. HC34 classifies the diagonal axis; earlier work proves the chiral axis always unstable. Determine whether genuine mixtures create a rigid stability selector.

## Result

For every positive scale `beta`, real diagonal coupling `gamma`, and real chiral coupling `eta`, Lean constructs the mixed source operator and proves it remains formally Krein-self-adjoint. All imaginary cross terms cancel from trace and determinant:

\[
  \operatorname{tr}A_{\beta,\gamma,\eta}
    =\operatorname{tr}A_{\beta,\gamma,0},
\]

\[
  \det A_{\beta,\gamma,\eta}
    =\det A_{\beta,\gamma,0}+\frac{\eta^2}{E_\beta},
\]

and therefore

\[
  \Delta_{\rm mix}(\beta,\gamma,\eta)
    =\Delta_{\rm diag}(\beta,\gamma)-\frac{4\eta^2}{E_\beta}.
\]

Define

\[
  r_{\beta,\eta}
  =\sqrt{r_\beta^2+\frac{4\eta^2}{E_\beta P_\beta^2}}.
\]

Lean proves the exact hyperbolic phase diagram

\[
  \operatorname{Spec}(A_{\beta,\gamma,\eta})\subset\mathbb R
  \Longleftrightarrow
  r_{\beta,\eta}\le
    \left|\frac{\gamma}{E_\beta}-c_\beta\right|.
\]

For every fixed `eta`, two distinct source-defined boundary couplings are spectrally real. Every coupling strictly between them is not spectrally real and carries an explicit positive-imaginary eigenvalue with a nonzero neutral eigenvector.

## Proof content

The matrix calculation proves real trace/determinant despite complex chiral entries. A generic two-coordinate elimination shows every nonzero eigenpair satisfies the real characteristic quadratic without diagonalizability assumptions. Nonnegative discriminant forces every root real. Negative discriminant gives the explicit quadratic-formula root and upper-column eigenvector; negativity itself proves that upper coordinate cannot vanish. Formal source self-adjointness then forces neutral Krein norm. Completing the square produces the exact two-sheet stability cone.

## Lean artifact

- Module: `GaloisForLFunctions.RHTower.FZZCigarParityFullLinearRieszStabilityCone`
- File: `formal/GaloisForLFunctions/RHTower/FZZCigarParityFullLinearRieszStabilityCone.lean`
- Umbrella: `formal/GaloisForLFunctions/RHTower.lean`
- Mixed discriminant: `fzzCigarParityDilatedMixedRieszCharacteristicDiscriminant_eq`
- Spectral converse: `fzzCigarParityDilatedMixedRieszSpectrallyReal_iff_discriminant_nonneg`
- Cone classification: `fzzCigarParityDilatedMixedRieszSpectrallyReal_iff_outside_cone`
- Instability witness: `fzzCigarParityDilatedMixedRieszInstabilityEigenpair`
- Neutrality: `fzzCigarParityDilatedMixedRieszInstabilityEigenvector_null`
- Nonuniqueness: `fzzCigarParityDilatedMixedRiesz_twoStableBranches`

## Verification

- Direct `lake env lean` check: passed with no warnings.
- `lake build GaloisForLFunctions.RHTower.FZZCigarParityFullLinearRieszStabilityCone`: passed (9,762 jobs).
- `#print axioms` on eleven public endpoints: only `propext`, `Classical.choice`, `Quot.sound`.
- `scripts/formal_tools.py lint`: no HC35 finding; only unrelated pre-existing unreachable-module failures.

## Corpus audit

Mandatory searches located the separate diagonal and chiral Riesz operators, their source-metric representation laws and axis discriminants, HC34's true diagonal spectral converse, and no mixed operator or two-parameter stability theorem. HC35 is based entirely on those literal corpus definitions. No divisor-fitted coefficient or external target enters the construction.

## Literature audit

Primary-source searches covered [Hikida–Schomerus, *The FZZ-Duality Conjecture—A Proof*](https://arxiv.org/abs/0805.3931), [Creutzig–Hikida–Rønne, *The FZZ duality with boundary*](https://arxiv.org/abs/1012.4731), and indefinite/Krein two-by-two stability literature such as [Chugunova–Pelinovsky, *Block-diagonalization of the linearized coupled-mode system*](https://arxiv.org/abs/math/0504442). Generic finite-dimensional discriminant algebra is standard. No source found the parity-delay Fermi block, its two literal Riesz directions, or this exact mixed hyperbolic cone and neutral-mode classification. Absence is a bounded search result, not proof of priority.

## New insight and route consequence

Genuine linear mixing does not rescue selection. Chiral interaction merely widens the diagonal instability window by an exact Pythagorean square; it never removes the two stable sheets. Thus every local linear combination of the two canonical source reporters is nonrigid. This closes the complete local-linear Riesz mechanism as an FZZ-P producer. Surviving possibilities must add an independent channel or use nonlinear, nonlocal/infinite, or singular dynamics with actual parity-Mellin landing.
