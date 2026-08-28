# FZZ parity all-scale Krein crossing

## Status

Formalized in Lean. Conjecture loop F7 succeeded. Complete positive-scale source carrier built;
divisor-to-carrier landing remains open.

## New all-scale law

Let `P(t)=1/(exp(t)+1)` be the parity-subtracted literal FZZ delay source. For each physical
dilation `beta>0`, set

`p_beta=P(beta), q_beta=P(2 beta), r_beta=P(4 beta)`.

Lean proves

`p_beta*r_beta - q_beta^2 < 0`

for every positive `beta`. With `x=exp(beta)>1`, the substantive inequality is the exact algebraic
factor comparison

`(x^2+1)^2 < (x+1)(x^4+1)`.

Thus the bare multiplicative Fermi-Hankel block is strictly indefinite over the entire positive
scale ray, not merely at the previously checked unit scale.

## All-scale Krein normal form

For each positive dilation, the module constructs from `p_beta,q_beta,r_beta` alone:

- the source-exact Hermitian pairing `B_beta`;
- a canonical traceless `B_beta`-self-adjoint operator `A_beta`;
- a positive discriminant `Delta_beta` and eigenvalue `lambda_beta=i*sqrt(Delta_beta)`;
- a nonzero eigenvector `v_beta=(q_beta,lambda_beta-p_beta)`.

Lean proves `A_beta v_beta=lambda_beta v_beta`, `Im lambda_beta>0`, `lambda_beta` is nonreal, and
`B_beta(v_beta,v_beta)=0` for every `beta>0`.

For the natural scale grade `D(u1,u2)=(0,u2)` and crossing `C_beta(u)=B_beta(u,D u)`, the exact law
is

`C_beta(v_beta)=q_beta^2*lambda_beta`.

Hence `Im C_beta(v_beta)>0`; the conjugate eigenline has exactly the opposite crossing and negative
imaginary part. The physical source therefore carries one fixed orientation convention across all
positive dilations before any Xi divisor specialization.

## Significance and remaining burden

This closes the finite-source scale-family infrastructure missing after the unit-scale no-go:
strict indefiniteness and oriented neutral lines persist at every scale, so varying FZZ level does
not destroy the source orientation.

It does not prove RH. The surviving hard gate is now exact and narrower: construct a
source-faithful map sending each zero of the parity FZZ Mellin transform into one of these physical
scale-dependent eigenlines, and prove the interacting dynamics selects one chamber. The map cannot
choose a zero or its chamber by hand. Existing `FZZCigarReplicaKreinScale` proves that physical
finite levels cover every positive response scale, but not that one Mellin divisor mode is
transported across levels.

## Lean artifact

Module:
`formal/GaloisForLFunctions/RHTower/FZZCigarParityAllScaleKreinCrossing.lean`.

Key declarations:

- `fzzCigarParityDilatedTwoScaleHankelMinor_neg`
- `fzzCigarParityDilatedTwoScaleKreinOperator_formallySelfAdjoint`
- `fzzCigarParityDilatedTwoScaleKreinDiscriminant_pos`
- `fzzCigarParityDilatedTwoScaleKreinEigenpair`
- `fzzCigarParityDilatedTwoScaleKreinEigenvector_null`
- `fzzCigarParityDilatedTwoScaleKreinEigenvector_gradeCrossing`
- `fzzCigarParity_allPositiveScales_conjugatePair_gradeCrossing_oriented`

## Corpus basis and novelty audit

- `FZZCigarParityFermiHankelPositivityNoGo` proves determinant negativity only at `beta=1`.
- `FZZCigarParityTwoScaleKreinSelfAdjointNoGo` constructs the neutral complex pair only at that
  fixed scale.
- `FZZCigarParityKreinGradeCrossingOrientation` orients that single pair.
- `FZZCigarReplicaKreinScale` supplies the complete finite-level response-scale parameter but no
  parity-source carrier or divisor transport.
- Corpus searches found no prior all-positive-scale FZZ parity determinant theorem or
  scale-parameterized oriented neutral-pair normal form.

Novel contribution is the exact all-scale synthesis for the literal FZZ parity source. Generic
Krein spectral facts and generic Hankel/total-positivity theory are not claimed as novel.

## Literature audit (27 August 2026)

- Salazar, *Order-Moment Transport and Hankel Determinants in Special-Function Inequalities*,
  arXiv:2606.31647, develops positive moment criteria for totally nonnegative Hankel kernels; it
  does not treat this sign-reversed Fermi multiplicative minor or FZZ carrier:
  https://arxiv.org/abs/2606.31647
- Belton--Guillot--Khare--Putinar, *Totally positive kernels, Polya frequency functions, and their
  transforms*, arXiv:2006.16213, classifies broad total-positivity preservers but gives no FZZ
  parity/Krein specialization: https://arxiv.org/abs/2006.16213
- Halder--Jafferis, *Stretched horizon, replica trick and off-shell winding condensate, and all
  that*, arXiv:2402.00932, provides the finite-level replica deformation context but no Fermi
  Hankel or Krein-crossing theorem: https://arxiv.org/abs/2402.00932
- Targeted searches found no primary source containing this full coefficient-level combination.
  Absence claim is bounded by searched sources.

## Verification

- Direct check passed:
  `lake env lean GaloisForLFunctions/RHTower/FZZCigarParityAllScaleKreinCrossing.lean`
- Targeted build passed:
  `lake build GaloisForLFunctions.RHTower.FZZCigarParityAllScaleKreinCrossing`
- Key theorem axiom audit: `[propext, Classical.choice, Quot.sound]` only.
- Scoped banned-token and diff checks passed.
- Wired into `GaloisForLFunctions.RHTower` umbrella.
- Global lint reports no error in this module; failures are unrelated concurrently owned
  unreachable modules.
