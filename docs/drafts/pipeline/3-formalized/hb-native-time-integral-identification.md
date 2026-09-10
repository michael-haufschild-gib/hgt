# Native response: original Bochner time equation

Stage: 3-formalized. Both exact leaf builds and the five-new-theorem axiom audit passed. RH, native/physical response equality and complete physical-current cancellation remain open.

Chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

## Exact construction

Let `U(t)=nativeJointResidual q (physicalRate q branch) a t`, let `F(t)=causalCuspSourceVector q branch a t`, and set

```
P2 f(t) = integral_0^t (t-u) f(u) du,
B = formEmbeddingCovariance jointEmbedding.
```

The construction identifies both literal scalar time integrals with their Bochner integrals in the original radial/modular Hilbert space:

```
L2(nativeJointTimePrimitiveField(t)) = P2 U(t),
L2(nativeJointIntegratedForcing(t)) = P2 F(t).
```

Substitution in the previously proved original operator equation gives

```
B U(t) + (I-B) P2 U(t) = B P2 F(t).
```

All statements retain the actual three principal amplitudes, original cutoff commutators, horizon factor, onset and original product measure. They hold for every real time. The native primitive identity also holds for arbitrary complex source rates. No native/physical response equality is assumed.

## Proof

For a continuous L2 curve with a jointly continuous literal representative, pair its Bochner interval integral with an arbitrary L2 vector. The continuous linear pairing commutes with the integral. Almost-everywhere representative equality identifies each spatial slice. The bound

```
integral |inner(g(x),u(t,x))| dx <= ||g||^2 + ||u(t)||^2
```

gives product integrability on the finite time interval. Fubini exchanges time and space. The scalar pairing then commutes with the literal time integral, identifying the target L2 vector. Reversing interval orientation handles negative times. This extends the existing principal-channel comparison argument to the original radial/modular product measure.

For the forcing, `principalNullResponse_physical_ae` identifies each of the three original physical principal responses with its literal native coefficient. The actual cutoff map is multiplication by `horizonCoordinate` followed by restriction to the negative radial ray. The exact identity `horizonCoordinate(x)=1/cosh(x)^2` supplies the original geometric weight. Tensor-product representative identities include the original angular commutator. On the negative ray the odd source equals the original reduced coefficient. Adding these four contributions gives the actual physical source vector's literal native forcing representative. The same L2 integral argument then identifies its double time integral.

## Remaining hard step

Both original time equations are now proved. The [physical Volterra equation](hb-physical-volterra-equation.md) holds almost everywhere for the constructed causal response, obtained from its original Laplace-domain operator equation and weighted L1 uniqueness. It requires no norm continuity of that representative.

For their locally integrable difference `u`, subtract the equations to obtain `B u+(I-B)P2 u=0` almost everywhere. Integrating twice gives `B P2 u+(I-B)P4 u=0` everywhere. The fourth primitive `Z=P4 u` is C2, satisfies `Z''=P2 u`, and has zero position and velocity at time zero. The next proof target is conservation and nonnegativity of

```
E(t)=||J.adjoint Z'(t)||^2+||Z(t)||^2-||J.adjoint Z(t)||^2,
J=jointEmbedding.
```

The actual embedding is contractive and dense, so zero energy should force `J.adjoint Z'=0`, then `Z'=0`, `Z=0`, and finally `u=0` almost everywhere by injectivity of B. This applied regularity and uniqueness argument remains to be formalized. Complete physical-current cancellation and Hawking-clock extinction remain open.

## Search and verification

Own broad corpus search `Bochner` and deep representative/Fubini search recovered the existing private `l2_integral_eq` in `ThetaCuspHawkingBMNativePhysicalIdentification`. Its actual proof supplied the generalization above. Declaration, candidate, source-method and proposed ingredient views were inspected. Search coverage was partial and mostly source-only; actual Lean checks determine applicability.

A separate deep covariance-energy search recovered the original Friedrichs covariance injectivity and Klein–Gordon energy differentiation. Its proposed collision-energy ingredient set does not establish this wave uniqueness argument and was not used. Broad arXiv searches with independently chosen terms did not produce a verified recent applicable result; no external result enters the proof.

## Lean modules and audit

[ThetaCuspHawkingBMNativeTimeIntegralIdentification.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMNativeTimeIntegralIdentification.lean) contains four public theorems:

- `nativeJointTimePrimitive_eq_bochner`: actual native primitive equals the original-space Bochner integral.
- `causalCuspSourceVector_native_forcing_ae`: complete physical source represents the literal native forcing.
- `nativeJointIntegratedForcing_eq_bochner`: exact original-source double time integral.
- `nativeJointResidual_bochner_covariance_equation`: actual native bounded Volterra equation.

[ThetaCuspHawkingBMNativeResidualAdmission.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMNativeResidualAdmission.lean) exposes the already proved literal joint continuity as `nativeJointResidualField_joint_continuous`; its existing private construction is preserved.

The complete candidates passed `lake env lean`. Final audits in the isolated cached leaf environment passed:

- `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeResidualAdmission`: two jobs, 115 seconds reported build time.
- `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeTimeIntegralIdentification`: 243 lines, two jobs, 136 seconds reported build time.

Only the five new public theorems were checked with `#print axioms` in a separate scratch file. Each uses exactly `propext`, `Classical.choice` and `Quot.sound`. No added axiom, numerical result, native-response equality premise or forcing-identification premise enters the proof. Sources and five artifacts per module were installed byte for byte. The new module is imported by `RHTower.lean`. Repository-wide `scripts/formal_tools.py lint` passed; pre-existing large-file warnings remain. No umbrella build, numerical experiment, Git command, launcher or frontier-map edit ran.

All 39 relative links in the three affected reports resolve. Owned scratch and process cleanup is completed before reporting this result.
