# HB: equality of native and physical causal responses

Stage: 3-formalized. Native/physical equality is proved almost everywhere in the original Hilbert space. Exact leaf build and new-theorem axiom audit passed. [Both original time equations](hb-physical-volterra-equation.md) are also formalized. Full physical-current cancellation, fixed Hawking-clock extinction and RH remain open. Frontier map read only.

Chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

## Exact proved statement

For every original Xi occurrence q, branch and amplitude a, Lean proves

```
nativeJointResidual q (physicalRate q branch) a
  = causalJointForcedResponse q branch a
```

almost everywhere on the original real time line, as vectors in the original radial/modular product-measure Hilbert space. No growth bound on the native response or norm continuity of the physical representative is assumed.

## Paper proof

Let N be the native response, U the physical response, `u=N-U`, `J=jointEmbedding`, `B=J J.adjoint`, and `P2 f(t)=integral_0^t (t-s)f(s) ds`.

1. N is continuous, hence locally integrable. The physical weighted time-L2 theorem gives local integrability after damping. Multiplication by the continuous inverse exponential removes the damping on each compact interval, so U and u are locally integrable.
2. Both proved time equations have the identical complete source. Their difference is `B u+(I-B)P2 u=0` almost everywhere.
3. For any locally integrable f, linearity gives `P2 f(t)=t integral_0^t f-integral_0^t s f(s) ds`. Both ordinary primitives are continuous. Thus `y=P2 u` is continuous; no derivative of u is taken.
4. Integrate the homogeneous equation twice. Bounded maps commute with Bochner integration; local integrability proves every integral exists. An almost-everywhere zero function has zero interval integral. Consequently `B y+(I-B)P2 y=0` at every real time.
5. Put `z=P2 y` and `v(t)=integral_0^t y(s) ds`. The decomposition in step 3 and FTC for continuous y give `z'=v`, `v'=y`, and `z(0)=v(0)=0`.
6. Define the complex energy `E=inner(J* v,J* v)+inner(z,z)-inner(J* z,J* z)`. Differentiate these three bounded inner products. The adjoint identities move J and J* between their arguments. Substitution of `B y=B z-z` cancels every term, so `E'=0` and E is identically zero.
7. J is contractive in its original completed differential graph, hence J* is contractive. Taking real parts of E gives `norm(J* v)^2+norm(z)^2-norm(J* z)^2=0`. Nonnegativity forces `J* v=0`. The original dense range of J makes J* injective, so v=0. Then z=0 from its derivative and initial value, and y=0 from the derivative of v.
8. The original almost-everywhere equation reduces to `B u=0`. The already proved injectivity of the actual covariance gives u=0 almost everywhere, as required.

The energy step is an internal uniqueness lemma, applied to the actual difference using proved regularity and both original field equations. It is not an extra premise on the physical response.

## Remaining physical action

The equality identifies the original time-Hilbert-space classes and supplies the native continuous representative of the physical response. The full current still requires its actual derivative/trace transfer and evaluation, including response-response, contact and cross terms, independent SS/SV/VV amplitudes, and onset, horizon, AdS, temporal and cusp terms. The finite-domain [spin-two transfer](../1-in-progress/hb-spin-two-kernel-transfer.md) and [terminal source bounds](../1-in-progress/hb-full-source-terminal-decay.md) supply existing source-side identities; their assembly into `2 Omega(B(p,p)/2,B(m,m)/2)=0` remains open.


## Search and verification

Broad `quadratic conservation` (OR) and deep weak-wave energy searches recovered scalar energy conservation and the Klein–Gordon bounded-inner-product derivative mechanism. Their statements do not directly apply to this joint operator; the actual covariance proof above was built and applied. A broad triangle search did not supply the needed weak-regularity identity; the first-moment decomposition in step 3 removes that dependency. All candidate and source-method views were inspected; partial/source-only metadata was not treated as verification.

Broad `symplectic` and deep causal-reciprocity searches supplied candidates for subsequent current transfer, including the original joint core transposition and modular Green identity. Their proposed boundary-incidence ingredient group does not establish the physical current assembly. The present equality proof needs none of those proposed extra hypotheses.

[ThetaCuspHawkingBMNativeCausalEquality.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMNativeCausalEquality.lean) has 273 lines and one public theorem: `RHTower.D4BMJointSource.nativeJointResidual_eq_causalJointForcedResponse`. Internal conditional uniqueness lemmas are applied with every condition proved for the actual objects. The public theorem has only the original q, branch and amplitude parameters.

Scratch checks validated the construction and the isolated derivative normalization. Final `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeCausalEquality` passed: three jobs, 20 seconds reported build time. The physical-equation artifact was replayed from cache; only the new equality module was compiled. Only this new public theorem was axiom-checked in a separate scratch file. Its axioms are exactly `propext`, `Classical.choice`, `Quot.sound`. Source and five build artifacts were installed byte for byte. The module is wired into `RHTower.lean`; no umbrella or full build ran.

Repository-wide `scripts/formal_tools.py lint` passed after installation. Only existing large-file warnings remain. Both new modules and all ten cached artifacts match the audited copies exactly. Local report links were checked. Frontier map and universal-law ledger are unchanged; no numerical experiment, Git command or launcher ran.

All owned Lean/Lake and search processes completed. The isolated audit directory and owned scratch/search files were removed after installation and verification.
