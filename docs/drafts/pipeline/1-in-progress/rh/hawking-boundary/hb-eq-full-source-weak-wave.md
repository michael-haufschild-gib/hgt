# Weak wave equation of the original infinite future response

Status: the existing full-source future response satisfies the original
reduced weak wave equation in Lean. This is a required part of full
temporal/metric/QNM matching; that matching, extinction and RH remain open.

[BRIDGE] For every joint smooth compact test `Phi(tau,x,X+ik)` supported in
`x<0`, the verified identity is

`integral A*[exp(-k)*wave_tau_x(Phi)-T_X_k(Phi)/cosh(x)^2]`
`= integral exp(-k)*Q*S*Phi`.

`A` is the original admitted future response, `S` the original reduced
source with fixed onset, and `T` the proved weighted angular test operator.
The test is joint in all four variables; no tensor-separability premise or
replacement field is allowed.

Exact ingredients: EP's original Dirichlet kernel temporal weak
equation for general compact time/radius tests; EO's full angular
transposition; EN's already-proved source-event formula for the original
future field. The source-event change of variables is not an open step.

The target integral uses Lebesgue measure in `(tau,x,X,k)`. The source
integral uses `s>0`, `y<0` and all angular positions; its integrand is
`exp(-k)*Q(X,exp(k))*S(s,y)*Phi(s,y,X+ik)`. Both sides are absolutely
admitted. The factor `exp(-k)` is the original hyperbolic angular area.

Dependency-closed proof:

1. Actual slice derivatives agree with joint directional derivatives, so
   the complete test operator is smooth and compactly supported.
2. For each fixed source event, closed-cone kernel and angular-action
   extensions are jointly continuous. Compact target tests admit temporal
   and angular Fubini; EP and EO combine to the full kernel identity.
3. For the original source-event density, the majorant
   `C*exp(-g*tau+g*abs(k))*exp((g-alpha)*s)*exp((2-alpha)*y)`
   has `g<alpha<2`. Multiplication by a compact joint target test admits
   the source/target interchange for the actual future response.
4. Apply the kernel identity inside the admitted original source integral.

Angular derivatives must move onto tests before the infinite source
interchange. No strict pointwise angular-jet growth estimate is assumed.

The kernel calculation retains the direct-minus-image half-factor. EP
gives the two source vertices `Q*(Phi(s,y,z)-Phi(s,-y,z))`; the image value
vanishes because `y<0` and the full test support lies in `x<0`. EO transfers
the angular action to `T(Phi)` on each angular slice. Joint compact support
and continuity admit both orders of target integration, so this argument
applies to general joint tests without a tensor-density premise.

For the infinite source, the majorant in step 3 is uniform in target radius
and horizontal position. Its source factors are integrable on the original
source event domain. The remaining target factor multiplied by the norm of
the compact test is integrable. Admitted Fubini and EN's exact source-event
formula therefore identify the actual response pairing with the original
source integrated against the full kernel pairing. Substitution of the
kernel identity proves the stated equation.

Lean results in
[ThetaCuspHawkingBMFullSourceWeakWave.lean](../../../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMFullSourceWeakWave.lean):

- `kernel_joint_transposition`: the full kernel identity for general joint
  compact tests, with original source vertex and image normalization.
- `originalTestDensity_integrable`, `original_response_test_integrable`,
  `original_source_test_fubini`: absolute admission and source/target
  interchange for the existing infinite future response.
- `forcingTestPair_integrable`, `original_future_weak_wave`: absolute
  forcing admission and the original response's full reduced weak equation.

Verification: `lake env lean` scratch passed without warnings. Isolated
`lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullSourceWeakWave`
passed in 31.02 seconds, two jobs. Single-threaded foreground checks had a
240-second hard timeout. The leaf is wired into `RHTower.lean`; no umbrella
build ran. No added axioms, admitted proofs or heartbeat overrides.
The repository lint gate reports the pre-existing unrelated unwired module
`ThetaCuspHawkingBMOnsetTransgressionHorizon`; the new leaf has no lint error.

Whole-route consequence: the original infinite future response now has its
proved reduced temporal/angular equation, rather than only a kernel
equation or separate angular pairing. The remaining matching problem must
identify the original lift and cap, their equations and boundary data, and
the resulting full physical metric/left-QNM action. This theorem does not
supply those identifications or a uniqueness theorem for that full field.
