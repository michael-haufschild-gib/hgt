# FZZ parity source-balanced Mellin reflection

## Status

Formalized in Lean. Conjecture F10 proved unconditionally.

## Theorem

At every physical scale `beta>0`, put

`a_beta=sqrt(P(4 beta)/P(beta))`

and encode the centered dyadic Mellin character by the source-balanced carrier

`w_beta(rho)=(1,a_beta⁻¹ chi(rho))`.

The canonical F9 source-metric antiunitary then obeys the exact equivariance law

`J_beta(w_beta(rho))=conjugate(chi(rho)) w_beta(1-conjugate(rho))`.

The scalar is nonzero, so in the balanced projective coordinate

`a_beta u₂/u₁`

the source antiunitary implements functional-equation reflection exactly, with no diagonal tilt.

Normalize the grade crossing by the norm of the balanced carrier's second coordinate. Lean proves
the closed formula

`Cbal_beta(rho)=q_beta chi(rho)/|chi(rho)| + r_beta a_beta⁻¹ |chi(rho)|`.

Its reflected defect is exactly `a_beta⁻¹` times the unbalanced F8 defect. Therefore

`Cbal_beta(rho)=Cbal_beta(1-conjugate(rho))`

if and only if `Re rho=1/2`. Matching balanced crossings for all open-strip parity-Mellin modes at
one positive scale is equivalent to RH.

## New knowledge

F9's unique correction `P(4 beta)/P(beta)` is the square of a canonical half-density coordinate,
not an arbitrary fitted scalar. Source-metric antiunitarity and functional-equation reflection are
fully compatible after this forced balancing. The critical-line detector survives unchanged up to
a positive source scalar.

This closes construction of the FZZ-P antiunitary reflection carrier. Remaining proof burden is
strictly dynamical: show that literal interacting FZZ/GFZZ divisor modes have equal balanced grade
crossings. Antiunitarity and reflection covariance themselves no longer remain assumptions.

Lean module:
`formal/GaloisForLFunctions/RHTower/FZZCigarParitySourceBalancedMellinReflection.lean`.

Key declarations:

- `fzzCigarParitySourceBalancedMellinCarrier`
- `fzzCigarParitySourceMetricReflection_balancedMellinCarrier`
- `fzzCigarParitySourceMetricReflection_balancedCoordinate`
- `fzzCigarParitySourceBalancedMellinNormalizedCrossing_eq`
- `fzzCigarParitySourceBalancedMellinNormalizedCrossing_sub_reflection`
- `fzzCigarParitySourceBalancedMellinNormalizedCrossing_eq_reflection_iff`
- `fzzCigarParitySourceBalancedMellinReflectionCrossingMatchedAt_iff_riemannHypothesis`

## Corpus audit

- F8 provided character reflection and the raw grade-crossing detector.
- F9 provided the canonical weighted source antiunitary, its tilted raw fixed axis, and the unique
  inverse-diagonal correction.
- Fresh searches for source balancing, metric whitening, half-density Mellin carriers, and
  weighted FZZ reflection found no existing balanced-carrier theorem.

## Literature audit (28 August 2026)

- Jafferis–Schneider, *Semi-Classical Analysis of the String Theory Cigar*, arXiv:2004.05223,
  studies the exact cigar reflection coefficient via complex saddles and bound-state poles, but not
  this parity-Fermi source half-density or projective Mellin equivariance:
  https://arxiv.org/abs/2004.05223
- Halder–Jafferis, *Stretched horizon, replica trick and off-shell winding condensate, and all
  that*, arXiv:2402.00932v3, gives exact-in-alpha-prime cigar thermodynamics and winding dynamics,
  but no two-scale source-balanced Mellin carrier: https://arxiv.org/abs/2402.00932
- Burnol, *Entrelacement de co-Poisson*, arXiv:math/0407443, develops Mellin/zeta intertwining and
  reflection, but does not couple it to the FZZ parity source metric:
  https://arxiv.org/abs/math/0407443
- Sierra, *The Riemann zeros as energy levels of a Dirac fermion in a potential built from the
  prime numbers in Rindler spacetime*, arXiv:1404.4252, uses reflection phases and transfer matrices
  in a spectral RH model, but has no FZZ/Fermi half-density balancing law:
  https://arxiv.org/abs/1404.4252
- Targeted primary-source searches found no exact synthesis. Absence claim remains bounded by the
  searched arXiv corpus.

Novelty verdict: exact source half-density repair, projective antiunitary equivariance, and
balanced-crossing RH endpoint appear corpus-new and literature-unlocated.

## Lean verification

- Direct check passed:
  `lake env lean GaloisForLFunctions/RHTower/FZZCigarParitySourceBalancedMellinReflection.lean`
- Targeted build passed:
  `lake build GaloisForLFunctions.RHTower.FZZCigarParitySourceBalancedMellinReflection`
- Key theorem axiom audit: `[propext, Classical.choice, Quot.sound]` only.
- Scoped banned-token and diff checks passed.
- Module is wired into `GaloisForLFunctions.RHTower` umbrella.
- Authoritative global lint has no error in this module; current failures are unrelated
  concurrently owned unreachable-module entries.

## Remaining gate

Derive equal reflected balanced grade crossings from an interacting FZZ/GFZZ Ward identity,
positive commutator, or source-native flux conservation law. Restating matching as a premise is
exactly RH-strength and is not progress.
