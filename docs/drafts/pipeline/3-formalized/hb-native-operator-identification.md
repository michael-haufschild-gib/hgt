# Native primitive and the original joint operator

Stage: 3-formalized. The literal native double time primitive belongs to the original Friedrichs operator domain, with its actual mass-plus-forcing as operator value. RH, native/physical causal-response equality, and complete physical-current cancellation remain open.

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

## Remaining causal comparison

The next task is to identify the native original-space time primitive with the Bochner double primitive of `nativeJointResidual`, match the literal integrated forcing at the physical rates, and prove equality with the constructed causal joint response. Its current construction is an exponentially weighted time-L2 family with a Laplace-domain operator equation; norm continuity of that representative must not be presumed. The bounded equation above supplies the native side of this comparison.

A positive uniqueness mechanism to test is conservation of `inner(B Z',Z') + inner((I-B)Z,Z)` for a homogeneous difference satisfying `B Z''+(I-B)Z=0`, with zero initial data. Here `0<=B<=I` follows from the actual contractive form embedding, and `B` is injective. Zero conserved energy forces `B Z'=0`, hence `Z'=0` and `Z=0`, without a bounded inverse for `B`.

There is a concrete way to handle the physical response's time-L2 regularity. First obtain its bounded equation almost everywhere from its actual Laplace-domain equation and uniqueness of the exponentially weighted vector Laplace transform. For the locally integrable difference `u`, write `P2 u(t)=integral_0^t (t-s)u(s) ds`. Its bounded equation is `B u+(I-B)P2 u=0` almost everywhere. Integrate twice to obtain `B P2 u+(I-B)P4 u=0` everywhere. The fourth primitive `Z=P4 u` is C2 (indeed C3), `Z''=P2 u`, and has zero initial value and derivative. The preceding conserved energy therefore gives `P2 u=0`, then `B u=0` almost everywhere and finally `u=0` almost everywhere. The required Bochner primitive identities, physical forcing equality, Laplace inversion, and conserved-energy argument remain to be verified and formalized for these actual fields.

## Search and external method check

Own broad corpus query `Green` recovered the completed original Green identities and the exact core differential pairing. Deep operator-domain search supplied graph-adjoint candidates, but their graph-core premises were not established; the proof above instead uses the already proved original form admission and original graph-generator closure. Broad `Volterra` and deep covariance/uniqueness searches were inspected in declaration, candidate, and proof-method views. Partial/source-only search metadata is not verification.

Own broad arXiv query `duality` found [Kinra, 9 September 2026, sections 8–8.1](https://arxiv.org/html/2609.09946v1). The paper proves weak-adjoint uniqueness using admissible forward tests and retains the endpoint terms in its duality identity. The applicable methodological question is which test space permits each cancellation; its fluid equations do not supply the native wave identity. No external theorem is used as a Lean premise.

## Lean modules and final audit

[ThetaCuspHawkingBMNativeCoreTransposition.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMNativeCoreTransposition.lean) contains:

- `nativeTimePrimitive_angular_transposition`: integrability and exact angular second Green identity for every original core test.
- `nativeTimePrimitive_radial_transposition`: exact negative-ray second Green identity for every original radial core test.
- `nativeTimePrimitive_core_transposition`: the literal native equation against every original separated joint graph generator.

[ThetaCuspHawkingBMNativeOperatorIdentification.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMNativeOperatorIdentification.lean) contains:

- `nativeJointTimePrimitive_covariance`: `B(W+G)=W` for the actual original embedding.
- `nativeJointTimePrimitive_operator_action`: original unbounded operator-domain membership and exact operator value.
- `nativeJointResidual_covariance_equation`: `B U+(I-B)W=B F2` for the literal native residual and integrated forcing.

Both complete candidates passed `lake env lean` scratch checks. Exact-module final audits passed in the isolated cached leaf environment:

- `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeCoreTransposition`: 330 lines, two jobs, 8.5 seconds reported build time.
- `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeOperatorIdentification`: 115 lines, three jobs, 137 seconds reported build time.

Only the six new public theorems were checked with `#print axioms` in a separate scratch file. Each uses exactly `propext`, `Classical.choice`, and `Quot.sound`. No added axiom, numerical result, native domain premise, or response-equality premise enters these proofs. Sources and five artifacts per module were installed byte for byte, and both imports were added to `RHTower.lean`. No umbrella or dependency rebuild ran.

The follow-up deep primitive search recovered `waveCausalKernel_independent_on_ray` in `ThetaCuspHawkingBMJointKernelCoherence`. Its actual source reduces vector equality to scalar Laplace injectivity and then uses `bochnerL2_ae_zero_on_of_inner_probes`; this is a relevant existing mechanism for the pending physical bounded equation. Generated energy and Bochner ingredient sets did not prove the needed identities and were not used as proof evidence.

## Repository gate and cleanup

Repository-wide `scripts/formal_tools.py lint` did not pass: it reported five modules outside this change that were unreachable from their theorem-area umbrellas: `RHTower.BorisovGabberVasiuReservoirDeterminant`, `RHTower.FokasLenellsCausalBoundedPolynomialEigenmodes`, `HTGeometry.BorisovGabberVasiuDeterminant`, `HTGeometry.BorisovGabberVasiuObservationDeterminant`, and `HTGeometry.BorisovGabberVasiuSpectralDeterminant` (all under `GaloisForLFunctions`). The Fokas–Lenells module had a live Lean process belonging to concurrent work. These files and their imports were not changed. Large-file warnings elsewhere also remain. Both new HB modules have their original umbrella imports and passed their exact leaf builds.

All 40 relative links in the three affected reports resolve. The frontier map and universal-law ledger were not modified. No numerical experiment, umbrella build, Git command, or launcher ran. Owned scratch/process cleanup is completed before reporting this construction.
