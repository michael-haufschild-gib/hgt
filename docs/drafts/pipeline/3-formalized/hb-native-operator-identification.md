# Native primitive and the original joint operator

Stage: 3-formalized. The literal native double time primitive belongs to the original Friedrichs operator domain, with its actual mass-plus-forcing as operator value. [Native/physical causal-response equality](hb-native-causal-equality.md) is now proved almost everywhere. RH and complete physical-current cancellation remain open.

Chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

## Exact proved statements

Let `U(t)` be `nativeJointResidual`, `W(t)` the literal double time primitive in the original joint L2 space, and `F2(t)` the literal integrated residual forcing. Write `G=F2-U`, `J=jointEmbedding`, and `B=J J.adjoint`. The proved identities are

```
B (W+G) = W,
W in jointEnergyOperator.domain,
jointEnergyOperator W = W+G,
B U + (I-B) W = B F2.
```

All fields retain the original source, radial measure, angular modular measure, cusp subtraction, and geometric angular weight. The construction is for every Xi occurrence, complex source rate and amplitude, and real time. It assumes no native operator-domain or response-identification premise.

## Proof

1. For an arbitrary original angular core test `g`, take compact cell supports for both `g` and its original chart Laplacian. Choose a native cusp cutoff beyond both supports. On their union, equality of actual modular germs identifies the cutoff field and its chart Laplacian with the untruncated primitive and its chart Laplacian. Apply the original completed Green identity in both orders and conjugate one identity. This proves `integral conj(Delta g) W = integral conj(g) Delta W`, with integrability of both pairings. The original glued modular sides and elliptic corners are retained.
2. For an arbitrary original radial core test `f`, its field and both derivatives have compact support inside the negative ray. Two whole-line integration-by-parts identities apply to the actual first and second radial derivatives of the primitive. Compact support identifies their integrals with the original negative-ray integrals. Thus `integral conj(f'') W = integral conj(f) W''`.
3. The native value and pure second spatial jets are jointly continuous. Products with compact radial tests and compact angular cell tests are integrable: restrict the continuous product to the compact product support, then identify it almost everywhere in the original product measure. Fubini therefore combines the two transpositions. The actual elliptic equation `-W_xx-sech(x)^2 Delta W=G` gives
   `inner (jointCoreDifferential f g) W = inner (f tensor g) (W+G)`.
4. [Native form admission](../3-formalized/hb-native-form-admission.md) gives `v` in the original completed graph with `J v=W`. `jointCoreDifferential_inner` converts the preceding equality to `inner (jointGraph f g) (v-J.adjoint(W+G))=0`. The original domain is the closure of the span of these exact graph generators. A continuous inner-product functional vanishing on those generators therefore vanishes on the whole domain, including its own representing vector. Consequently `v=J.adjoint(W+G)` and `B(W+G)=W`.
5. The existing covariance-inverse construction of the actual Friedrichs operator gives its domain and value at `W`. Substituting the original `G=F2-U` gives the bounded covariance equation.

## Completed causal comparison

The [Bochner time identification](hb-native-time-integral-identification.md) identifies both literal native time integrals with their original-space Bochner integrals. The [physical Volterra construction](hb-physical-volterra-equation.md) proves the same equation almost everywhere for the constructed physical response. Finally, [applied covariance-energy uniqueness](hb-native-causal-equality.md) identifies the two time families almost everywhere. The physical response's norm continuity and a native global growth bound are not assumptions.

The original full physical-current action, its derivative/trace transfer and all boundary limits remain to be evaluated. Native/physical time-class equality alone is not a proof of current cancellation or RH.

## Search and external method check

Own broad corpus query `Green` recovered the completed original Green identities and the exact core differential pairing. Deep operator-domain search supplied graph-adjoint candidates, but their graph-core premises were not established; the proof above instead uses the already proved original form admission and original graph-generator closure. Broad `Volterra` and deep covariance/uniqueness searches were inspected in declaration, candidate, and proof-method views. Partial/source-only search metadata is not verification.

Own broad arXiv query `duality` found [Kinra, 9 September 2026, sections 8–8.1](https://arxiv.org/html/2609.09946v1). The paper proves weak-adjoint uniqueness using admissible forward tests and retains the endpoint terms in its duality identity. The applicable methodological question is which test space permits each cancellation; its fluid equations do not supply the native wave identity. No external theorem is used as a Lean premise.

## Lean modules and final audit

[ThetaCuspHawkingBMNativeCoreTransposition.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMNativeCoreTransposition.lean) contains:

- `nativeTimePrimitive_angular_transposition`: integrability and exact angular second Green identity for every original core test.
- `nativeTimePrimitive_radial_transposition`: exact negative-ray second Green identity for every original radial core test.
- `nativeTimePrimitive_core_transposition`: the literal native equation against every original separated joint graph generator.

[ThetaCuspHawkingBMNativeOperatorIdentification.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMNativeOperatorIdentification.lean) contains:

- `nativeJointTimePrimitive_covariance`: `B(W+G)=W` for the actual original embedding.
- `nativeJointTimePrimitive_operator_action`: original unbounded operator-domain membership and exact operator value.
- `nativeJointResidual_covariance_equation`: `B U+(I-B)W=B F2` for the literal native residual and integrated forcing.

Both complete candidates passed `lake env lean` scratch checks. Exact-module final audits passed in the isolated cached leaf environment:

- `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNativeCoreTransposition`: 330 lines, two jobs, 8.5 seconds reported build time.
- `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNativeOperatorIdentification`: 115 lines, three jobs, 137 seconds reported build time.

Only the six new public theorems were checked with `#print axioms` in a separate scratch file. Each uses exactly `propext`, `Classical.choice`, and `Quot.sound`. No added axiom, numerical result, native domain premise, or response-equality premise enters these proofs. Sources and five artifacts per module were installed byte for byte, and both imports were added to `RHTower.lean`. No umbrella or dependency rebuild ran.

The follow-up deep primitive search recovered `waveCausalKernel_independent_on_ray` in `ThetaCuspHawkingBMJointKernelCoherence`. Its actual source reduces vector equality to scalar Laplace injectivity and then uses `bochnerL2_ae_zero_on_of_inner_probes`; the physical bounded equation is now proved by the L1 scalar-probe/set-integral argument documented in its own report. Generated energy and Bochner ingredient sets did not prove the needed identities and were not used as proof evidence.

## Repository gate and cleanup

Current repository-wide `scripts/formal_tools.py lint` passes. Pre-existing large-file warnings remain. Both operator-identification modules and the subsequent time-equation module have their original umbrella imports and passed exact leaf builds.

Relative links are checked with the time-equation report. The frontier map and universal-law ledger were not modified. No numerical experiment, umbrella build, Git command or launcher ran.
