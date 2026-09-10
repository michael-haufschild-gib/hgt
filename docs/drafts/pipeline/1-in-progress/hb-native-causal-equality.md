# HB: equality of native and physical causal responses

Stage: 1-in-progress. The covariance-energy argument and its regularity reduction have a dependency-closed paper proof. The complete Lean application is being checked. [Both original time equations](../3-formalized/hb-physical-volterra-equation.md) are formalized. Full physical-current cancellation, fixed Hawking-clock extinction and RH remain open. Frontier map read only.

Chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

## Exact target

For every original Xi occurrence q, branch and amplitude a, identify

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

The equality identifies the original time-Hilbert-space classes and supplies the native continuous representative of the physical response. The full current still requires its actual derivative/trace transfer and evaluation, including response-response, contact and cross terms, independent SS/SV/VV amplitudes, and onset, horizon, AdS, temporal and cusp terms. The finite-domain [spin-two transfer](hb-spin-two-kernel-transfer.md) and [terminal source bounds](hb-full-source-terminal-decay.md) supply existing source-side identities; their assembly into `2 Omega(B(p,p)/2,B(m,m)/2)=0` remains open.
