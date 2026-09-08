# Uniform cusp control of the original regularized curvature

- Stage: 2-fully-proven; Lean scratch work pending.
- Parent: [Selberg loop](../1-in-progress/selberg-quarter-conjecturing-loop.md), cycle 38.
- Previous goal turn: progress; exact cell unfolding and the signed finite quotient-functional budget completed and audited.

## Paper proof under formalization

Write a=sqrt(D), rho_e=sqrt(D+e^2), with the original finite congruence-trace density D. The checked square-root estimates give 0<=rho_e-e<=a and D/rho_e<=a for every positive e. The actual retained-curvature identity and its nonnegativity imply Delta rho_e>=-|lambda|a/y^2. This strengthens the initial proposed lower bound using rho_e: the new forcing is independent of the regulator. Consequently the following argument applies to every positive regulator, not only e<=1.

Original uniform cusp decay of D implies uniform cusp decay of a. Unit horizontal averaging therefore gives e<=u_e(y)<=e+delta beyond one height independent of e, for every positive delta. Averaging the source Laplacian identity gives u_e''>=-|lambda|/y^2 beyond a fixed height where a<=1. The existing source theorems identify u_e' with the actual averaged vertical current and u_e'' with the averaged planar Laplacian.

For a function u with derivative v and v'>=-C/y^2, the checked corrected derivative v-C/y is monotone. Its forward and backward unit secants give

v(y)<=u(y+1)-u(y)+C/y,
u(y)-u(y-1)-C/(y-1)<=v(y).

If L<=u<=L+delta at these three heights, then |v(y)|<=delta+C/(y-1). Apply this with L=e, C=|lambda|, and the uniform source mean bounds. Choosing the height so that both delta and C/(y-1) are small proves uniform decay of the original averaged current over all positive regulators. Its checked equality with the centered Stokes top current gives the same uniform decay for that literal boundary term.

In the exceptional interval, subtract the actual truncated curvature identity from the proved full-domain identity. The resulting curvature outside the truncation is lambda times the corresponding regularized amplitude tail minus the actual top current. All functions are genuinely integrable from the previous source results, so subtraction of set integrals is justified. Since 0<=D/rho_e<=sqrt(D), the regularized amplitude tail is bounded by the fixed integrable original amplitude tail. That tail tends to zero by the actual domain exhaustion. The uniform current estimate therefore forces curvature tails uniformly to zero over all positive regulators.

## Scope

The source uniform-tail conjecture is the target of this formalization. Identification of total mass of the limiting orbit functional still requires constructing or identifying an appropriate compact-orbit exhaustion. The spectral quarter lower comparison remains unproved. No entropy bound, physical evaporation law, or pointwise limiting curvature density is substituted for the original Maass identities.

## Corpus mechanisms

The explicit --any uniform-secant/one-sided-curvature/uniform-derivative/cusp-tail/uniform-tightness/tail-mass query reached 737 declarations in 176 modules. Coverage counts do not mean every source was read. Inspected source mechanisms: SelbergOneSidedCurvatureDecay's corrected derivative and two unit secants, SelbergSquareRootRegularizationError's original-amplitude domination, SelbergMaassRegularizedCusp's exact horizontal derivative identifications, and SelbergMaassFullCurvatureBudget's actual exhaustion and full-integrability results. The previous evaporation/entropy searches require any proposed tail law to be derived from the actual source; this proof does so through these checked Maass identities.

## Audit

Pending scratch proofs, needed source oleans, umbrella wiring, single-module final builds, and axiom/lint checks.
