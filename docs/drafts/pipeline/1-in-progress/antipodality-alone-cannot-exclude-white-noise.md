# Antipodality alone cannot exclude white noise

- **ID:** antipodality-alone-cannot-exclude-white-noise
- **Stage:** 1-in-progress
- **Type:** FALSIFIED
- **Source:** `docs/reports/review-2410/opus.md`, §2.1 and Q-III milestones.
- **Statement:** The proposed exclusion of white noise by antipodality alone fails; every positive kernel admits a unique antipodal extension.

## Goal

Audit the proposed white-noise exclusion while retaining the strongest positive
rigidity statement. This concerns the abstract Gram constraints, not realization
as an actual Möbius escape state.

## Paper proof

Let `K` be a positive kernel, realized by vectors `v_x`, and fix `o`. Adjoin
`v_none = -v_o`. The extended Gram kernel remains positive and has
`J(none,none)=K(o,o)` and `J(none,o)=-K(o,o)`.

Conversely, any positive extension with these two entries satisfies
`||v_none+v_o||^2=0`; hence `v_none=-v_o`. All new covariances are forced:
`J(none,y)=-K(o,y)` and `J(x,none)=-K(x,o)`.

For white noise, `K(j,k)=1_{j=k}/j`. Its packet energy is
`sum_j c(j)^2/j`, and dilation multiplies that energy by `1/p`. The diagonal
entries attain the cofactor radius and all off-diagonal entries vanish. The
generic theorem gives a positive antipodal residual of unit mass and pairing
minus one.

## No-go closure

- **Exact killing mechanism:** Every positive kernel, including white noise,
  admits the required antipodal coordinate. Antipodality imposes no further
  restriction on the original cofactor kernel.
- **Strongest positive survivor:** The antipodal extension is unique at any
  distinguished point, without rank or dimension restrictions. Every mixed
  residual covariance is determined by the original kernel.
- **New insight:** An extra antipodal Gram coordinate carries no independent
  covariance data. A source exclusion must use the realization of that coordinate
  by the moving cofactor sum and pole subtraction.
- **Status:** Dependency-closed paper proof. The generic existence and uniqueness
  module passed Lean and its transitive axiom audit uses only `propext`,
  `Classical.choice`, and `Quot.sound`. White-noise specialization, final
  source checks, and umbrella wiring remain pending. This no-go is not yet closed.

## Lean declarations

- `HTGeometry.IsPSDKernel.antipodalExtension`
- `HTGeometry.antipodalKernelExtension_unique`
- `HTGeometry.existsUnique_antipodalKernelExtension`
- Draft: `ArithmeticDefectRigidity.whiteNoise_has_unique_antipodal_extension`

Files: `HTGeometry/AntipodalKernelExtension.lean` and
`ArithmeticDefectRigidity/WhiteNoiseAndAntipodalEscapeData.lean`.

## Gates

- [x] Precise failed assertion and source distinction recorded.
- [x] Positive survivor has a complete paper proof.
- [x] Generic survivor passed Lean.
- [ ] White-noise application, axiom audit, final checks, and imports complete.
- [ ] Retire only after all preceding gates pass.
