# SQB original cutoff forcing

Status: eight public declarations formalized. Isolated module build and all
eight axiom audits passed. RH remains unproved. Frontier map is read-only.

Full chain: original modular source → entire-transform operator → independent
occurrence at every full Xi parameter → critical-line classifier → RH.

## Exact retained source

For an actual Xi copy rho, set u=(rho−1)/2, k=1−rho/2 and
c=Lambda(rho−1). The original scalar source E_u has principal part c y^k,
with c nonzero. The completed modular cusp subtraction retains the full
Fourier remainder. Its literal cell equation has forcing

`H(z)=c [Delta_H(eta(y)y^k)−k(k−1)eta(y)y^k]`.

Here eta is the original smooth transition from height two to height three.
The equality is derived from the complete source equation and the actual
second derivatives; it is not a Fourier truncation. The existing commutator
admission theorem proves H belongs to native L² on the full closed modular
cell. Its actual Hilbert representative is constructed as `forcingVector`.

## Nonvanishing and exact scalar cancellation

For an arbitrary complex k, the proved complementary boundary moment is

`integral_1^4 y^(−k−1) [Delta_H(eta(y)y^k)−k(k−1)eta(y)y^k] dy = 2k−1`.

The exact cutoff-power flux formula proves this: complementary exponents
cancel the bulk coefficient, and the endpoint power becomes one. For the
original k, this moment is 1−rho, which is nonzero because Re rho<1.

If the admitted H vector were zero, it would vanish almost everywhere on the
cell. Continuity and `fd=closure(interior fd)` upgrade this to pointwise
vanishing on the closed cell. The points iy for 1≤y≤4 belong to that cell;
the nonzero coefficient c would therefore force the full commutator, and
hence its complementary moment, to vanish. This contradicts 1−rho≠0.

The original scalar calibration simultaneously gives

`integral_fd E_u(z) H(z) dvol = 0`.

Absolute integrability of this full product is proved before evaluating it.
This is a **bilinear** pairing: it contains no complex conjugation. Thus the
actual source exhibits zero scalar pairing with a nonzero retained forcing.
It supplies no inference that the vector vanishes or that its entire-operator
transport vanishes.

## Remaining bridge

Let V be the admitted corrected source and C the constructed entire covariance.
The previous module identifies the transformed residual
`G=V−(2+mu)CV`. The present H is the literal differential forcing, not G.
Native graph admission of V and `(A−e)V=H` still require proof before applying
resolvent transport. Even after that identification, occurrence requires
independent control of the transported forcing.

## Lean evidence

Module: `GaloisForLFunctions.RHTower.SelbergScatteringCutoffForcing`.
Namespace: `RHTower.SelbergScatteringCutoffForcing`.

Public declarations: `cutoffForcing_eq_commutator`, `cutoffForcing_memLp`,
`forcingVector`, `forcingVector_coe`, `cutoffCommutator_complement_moment`,
`forcingVector_ne_zero`, `scalar_forcing_integrable`,
`scalar_forcing_pairing_zero`.

The complete scratch passed `lake env lean /tmp/sqb9_forcing.lean`.
The final `lake build` named only this module; its preflight and every `Built`
line confirmed it was the sole newly compiled module, finishing in 4.2s.
Each of the eight `#print axioms` reports contains only `propext`,
`Classical.choice`, and `Quot.sound`. The module is imported once by its umbrella.
No numerical experiment, computed proof input, added axiom or placeholder was used.
Logs: `/tmp/sqb9_forcing_build.log`, `/tmp/sqb9_forcing_axioms.log`.

All eight public declarations are present in the refreshed corpus index.
The full formal lint run reports one unrelated missing umbrella import for
the untracked `HTGeometry.FokasLenellsRegularOrigin` module; it reports no
error for this forcing module. That unrelated module was left untouched.
