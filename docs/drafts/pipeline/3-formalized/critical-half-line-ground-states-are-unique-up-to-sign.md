# Critical half-line ground states are unique up to sign

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Target:** B104; rigidity of the actual critical state.
- **Statement:** At a finite global window threshold, any two actual normalized critical half-line ground states agree almost everywhere up to sign.
- **Status:** Verified in Lean; umbrella wired.

## Exact relation

For every `s>0`, critical states F and G satisfy

`F = (L_F(s)/L_G(s))G` almost everywhere,

where `L_F(s)=∫ F(u) exp(su) du`. Both Laplace values are nonzero.

The weak equation makes every linear combination of F and G have zero full
energy. The actual-domain combination `H=F−(L_F(s)/L_G(s))G` cancels one
positive Laplace value. The reflection theorem forces H to vanish almost
everywhere. Unit norms then force the scalar to be `1` or `−1`.

No positivity, polar-threshold equality, smoothness, or spectral simplicity
assumption is used.

## Lean

Module: `ArithmeticHodgeTheoryOfDegenerations/TheCriticalHalfLineStateIsUniqueUpToSign`.

- `integrable_halfLineLaplace_of_domain`: actual positive Laplace integrability.
- `criticalHalfLineGroundState_eq_laplace_ratio_ae`: exact scalar relation.
- `criticalHalfLineGroundState_unique_up_to_sign`: normalized uniqueness.
- `riemannHypothesis_or_exists_unique_criticalHalfLineGroundState`: RH, or a finite global threshold with one normalized critical-state line whose positive Laplace values never vanish.

Inputs: the verified [weak equation](critical-half-line-states-have-causal-logarithmic-coordinates.md)
and [zero-energy Laplace exclusion](critical-half-line-states-have-no-positive-laplace-zero.md).

The arithmetic polar pairing can still vanish on this single line; B104
is not closed.
