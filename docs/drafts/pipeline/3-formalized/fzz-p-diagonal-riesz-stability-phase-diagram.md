# FZZ-P diagonal Riesz stability phase diagram

## Status

Formalized in Lean 4 on 2026-08-28. Frontier label: HC34.

## Route

FZZ parity-delay (FZZ-P).

## Problem

The literal Fermi-delay source gives an indefinite two-scale Krein form, a canonical formally self-adjoint generator, and a Riesz interaction representing unit second-scale energy. Earlier work found one negative diagonal coupling with real spectrum, while every real chiral coupling remains unstable. Classify the entire diagonal coupling line: is the known stable point rigid enough to orient FZZ modes, or is stability nonselective?

## Result

For every positive physical scale `beta`, Lean defines explicit source-normalized center `c_beta` and radius `r_beta>0` and proves the completed-square identity

\[
  \Delta_\beta(\gamma)
  =P_\beta^2\left[
    \left(\frac{\gamma}{E_\beta}-c_\beta\right)^2-r_\beta^2
  \right].
\]

It then proves the genuine spectral converse, not merely an algebraic proxy:

\[
  \operatorname{Spec}(A_{\beta,\gamma})\subset\mathbb R
  \Longleftrightarrow
  \Delta_\beta(\gamma)\ge0
  \Longleftrightarrow
  r_\beta\le\left|\frac{\gamma}{E_\beta}-c_\beta\right|.
\]

Inside the complementary bounded open window, Lean constructs an explicit positive-imaginary eigenvalue, a nonzero eigenvector, proves the eigenpair equation, and proves the eigenvector is neutral for the literal source Krein form. Outside the window lie two disjoint unbounded spectrally-real coupling rays.

## Mathematical content

Every eigenvalue of the source matrix is first shown to satisfy its real quadratic characteristic equation without assuming diagonalizability. Nonnegative discriminant forces the imaginary part of any complex root to vanish. For negative discriminant, the explicit quadratic-formula root

\[
  \lambda_+=\frac{\operatorname{tr}A}{2}
    +\frac{i}{2}\sqrt{-\Delta}
\]

and vector `(upper coefficient, lambda_+ - P_beta)` form a nonzero eigenpair. Formal Krein self-adjointness and nonreality force its self-pairing to vanish. The completed square then gives the exact stability chamber geometry.

## Lean artifact

- Module: `GaloisForLFunctions.RHTower.FZZCigarParityDiagonalRieszStabilityPhaseDiagram`
- File: `formal/GaloisForLFunctions/RHTower/FZZCigarParityDiagonalRieszStabilityPhaseDiagram.lean`
- Umbrella: `formal/GaloisForLFunctions/RHTower.lean`
- Spectral converse: `fzzCigarParityDilatedSecondDiagonalPerturbedSpectrallyReal_iff_discriminant_nonneg`
- Phase diagram: `fzzCigarParityDilatedSecondDiagonalPerturbedSpectrallyReal_iff_outside_window`
- Instability witness: `fzzCigarParityDilatedSecondDiagonalPerturbedInstabilityEigenpair`
- Neutrality: `fzzCigarParityDilatedSecondDiagonalPerturbedInstabilityEigenvector_null`
- Nonuniqueness: `fzzCigarParityDilatedSecondDiagonalPerturbed_twoStableRays`

## Verification

- Direct `lake env lean` check: passed with no warnings.
- `lake build GaloisForLFunctions.RHTower.FZZCigarParityDiagonalRieszStabilityPhaseDiagram`: passed (9,761 jobs).
- `#print axioms` on eight public endpoints: only `propext`, `Classical.choice`, `Quot.sound`.
- `scripts/formal_tools.py lint`: no HC34 finding; only unrelated pre-existing unreachable-module failures.

## Corpus audit

Mandatory searches covered FZZ diagonal Riesz stabilization, characteristic discriminants, two-by-two spectral converses, and exact stability intervals. Corpus supplied the literal source matrix, trace, determinant, discriminant, formal self-adjointness, one source-gap stable coupling, and the complementary chiral all-coupling no-go. It contained no theorem classifying all diagonal couplings, no converse from actual spectral reality to discriminant sign, and no explicit neutral instability mode throughout the full negative-discriminant chamber.

## Literature audit

Primary-source search included [Hikida–Schomerus, *The FZZ-Duality Conjecture—A Proof*](https://arxiv.org/abs/0805.3931), [Creutzig–Hikida–Rønne, *The FZZ duality with boundary*](https://arxiv.org/abs/1012.4731), and searches for FZZ/Krein/Riesz spectral phase diagrams. Generic `2×2` discriminant algebra is elementary and no novelty is claimed for it alone. No source found this parity-delay Fermi block, its source-metric Riesz perturbation, or the exact two-ray/neutral-window classification. Absence is a bounded search result, not proof of global priority.

## New insight and route consequence

The known source-gap coupling is not rigid: diagonal stabilization occupies two unbounded chambers. Hence local spectral reality plus formal Krein self-adjointness cannot select the critical sector even after coupling to the literal diagonal reporter. Together with the existing theorem that every chiral Riesz coupling remains unstable, HC34 retires both canonical single-reporter linear interaction directions as standalone FZZ-P selectors. Surviving dynamics must mix directions nontrivially or use nonlinear, nonlocal, infinite, or singular structure tied to parity-Mellin divisor landing.
