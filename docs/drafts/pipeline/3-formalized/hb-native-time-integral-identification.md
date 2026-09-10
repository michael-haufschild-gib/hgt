# Native response: original Bochner time equation

Stage: 3-formalized. Both exact leaf builds and the five-new-theorem axiom audit passed. [Native/physical response equality](hb-native-causal-equality.md) is now proved almost everywhere. RH and complete physical-current cancellation remain open.

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

## Completed causal comparison and remaining physical current

The [physical Volterra equation](hb-physical-volterra-equation.md) gives the same bounded time equation almost everywhere for the constructed physical response. The [applied covariance-energy proof](hb-native-causal-equality.md) now identifies the native residual with that physical response almost everywhere in real time. It proves local integrability and integrated regularity from the actual data; no norm continuity of the physical representative or extra native growth premise is assumed.

The full Einstein/current pairing, its derivative and boundary transfer, fixed Hawking-clock extinction and RH remain open. All onset, horizon, AdS, temporal and cusp terms and independent tensor amplitudes must still be included in that action.

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
