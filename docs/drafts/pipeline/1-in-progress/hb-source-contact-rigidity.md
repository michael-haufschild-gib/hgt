# HB: source-contact rigidity under a first-order current repair

Status: literal source differential identity and nonzero coefficient formalized; complete commutator/current transport remain paper work. No extinction or RH proof.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal/left-QNM action → original common Hawking-clock extinction → RH.

The obstacle is cancellation of the complete oriented physical pairing. This attack tests whether the original common source producer admits a local differential symmetry after its radial transpose is repaired. It retains the original clock and full angular Laplacian. It does not replace the complete tensor source by its mixed scalar master.

## Canonical first-order repair

Use the original optical operator M=-partial_x²-2 partial_x partial_v+V Delta, V=u²-1, u=-tanh x, so u'=V. The common source producer has radial coefficient b=K b0, where

```
K=(7lambda-2-2Delta)/8,
b0=u²/(1-u).
```

For T=A+b partial_x+c partial_v, direct product differentiation gives

```
M T-(T+2b') M
 =2(b'-c') partial_x partial_v
  -(2A'+b'') partial_x-(2A'+c'') partial_v
  -A''-b V' Delta-2b' V Delta.
```

Primes are actual x derivatives; all angular operators commute here. Eliminating the derivative terms requires c'=b' and A'=-b''/2. Thus, up to x-independent commuting terms, the canonical repair is

```
T=K[b0(partial_x+partial_v)-b0'/2],
M T-(T+2K b0') M
 =K[b0'''/2-(b0 V'+2b0' V)Delta].
```

This permits a zeroth-order adjustment as well as a time derivative. It is more permissive than repairing only the principal terms of the original producer. With e=exp(-2x), b0=(e-1)/2-u,

```
b0'=-e-V,
b0''=2e-2uV,
b0'''=-4e-2V(3u²-1).
```

At the actual AdS endpoint x=0, b0=b0'=0 and b0'''=-6. The surviving multiplier is therefore -3K. This is an interior operator identity with an endpoint trace, not a full spacetime boundary cancellation. On the literal seed its trace is -3 a² chi(v) exp(2sv) KQ. A physical conservation proof must absorb this source term or use a different mechanism.

## Positive differential identity for the literal angular contact

Let f be the actual theta scalar, lambda=q(q-1), Q=f²/2, and use the complex bilinear hyperbolic gradient pairing. Put

```
E=grad f dot grad f,
J=KQ=(7lambda-2)Q/8-Delta Q/4,
k=(3lambda-2)/4,
m=lambda-k=(lambda+2)/4.
```

The original eigen-equation Delta f=lambda f and half-square identity give J=(k f²-E)/4. The proposed exact source identity is

```
(lambda-2)(lambda-6) f² E
 =16(lambda-2)[2f grad f dot grad J+J E]
  -32 E Delta J-128 grad J dot grad J.                 (1)
```

Paper proof: in an orthonormal hyperbolic frame let g=grad f and H=Hess f. Then tr H=lambda f,

```
grad J=(k f g-Hg)/2,
2 Delta J=k lambda f²+(k-lambda+1)E-tr(H²).
```

The second line follows from the complex bilinear Bochner identity Delta E=2tr(H²)+2(lambda-1)E, whose curvature sign is fixed by curvature -1. Contract the two-dimensional Cayley-Hamilton identity for H against g:

```
(Hg) dot (Hg)-lambda f(g dot Hg)
  +[(lambda f)²-tr(H²)] E/2=0.
```

Substitute the preceding two lines and use m²-k=(lambda-2)(lambda-6)/16. This yields (1), without division by f, E, J, or an onset factor. This is a bilinear identity, not a positivity estimate.

If J vanishes on an open set, all its displayed derivatives vanish there. Equation (1) together with E=k f² then forces f=0 there when lambda avoids 2, 6 and 2/3. At actual Xi occurrences Re(lambda)<0 follows from the open strip and nonzero imaginary part, so those exceptional parameters are absent. Establishing a global nonzero scalar witness and its Lean attachment remains a separate verification step; it is not assumed here.

The positive formalized result is the stronger form (2) below on the literal theta scalar, with actual derivatives and no source equation or regularity premises supplied by callers. Even a nonzero J does not prove nonzero complete radiative action: other physical channels and faces can compensate it.

Eliminating E from the left side with 4J=k f²-E gives the stronger denominator-free form closed in Lean:

```
(lambda-2)(lambda-6)(3lambda-2) f^4
 =16(lambda-2)(lambda-6) f² J
  +64(lambda-2)[2f grad f dot grad J+J E]
  -128 E Delta J-512 grad J dot grad J.                 (2)
```

The same leaf proves that the coefficient on f^4 is nonzero for every actual Xi occurrence. The proof derives all contact derivatives from the original theta field. It does not specialize the absolute-convergence Poincare theorem beyond its domain. The [formalized proof and audit](../3-formalized/hb-source-contact-differential-rigidity.md) records the successful 172-second exact cached leaf build. The commutator identity and endpoint trace above remain paper results.

## Search and candidate tests

Deep searches on complete variational reciprocity, oriented source pairing, source-contact Green methods, and square-eigenfunction rigidity were inspected in statement and proof-method views. Coverage was partial; some requests exhausted their bounded retrieval deadline. Existing common-source and mixed-action theorems supply exact local inputs, but no returned theorem proves the completed physical sign. The existing actual Bochner theorem concerns the absolute-convergence Poincare chamber, so its method may be reused; its parameter cannot be replaced by an actual Xi occurrence without a separate proof.

Broad date-sorted arXiv searches used reciprocity and homotopy, with additional concomitant, transgression and flux attempts. [Camacho et al., 10 September 2026](https://arxiv.org/html/2609.11577v1), equation E12 and its discussion, prove temporary monotone intensity decrease after a topological time interface under specified two-mode symmetries. This is not exact finite-time extinction, and the source's complete action is not identified with that model.

[Druzhkov–Shevyakov, 2 September 2026](https://arxiv.org/html/2609.03197v1), Sections 3–5, require an adjoint-symmetry/multiplier identity and its invariance before reducing a variational structure. Their method motivates the explicit multiplier test above; invariance is not obtained merely from the existence of a variational action. No computations or external theorem assumptions are used in the paper derivation.

The broad reciprocity search also found [Jiang, 8 September 2026](https://arxiv.org/abs/2609.10609): real stability follows from a particular two-path reflection and Jacobi interlacing. A positive combinatorial representation of the complete HB action has not been constructed, so that result supplies no source positivity premise.

## Remaining complete interface

The actual extinction target remains Cphys(q,n)=K(q,n)=-Sigma(q,n)|D(q,n)|² with Sigma>0. A source-derived bound Re Cphys>=0, or -Re Cphys<=epsilon Sigma|D|² with epsilon<1, would force D=0. Equation (1) does not give that bound. It identifies the local contact that a proposed symmetry must carry through the complete ++/+- corrections, all nine independent SS/SV/VV pairings, metric-weight variations, and temporal, horizon, exterior, cusp, characteristic and source-contact faces. The original Hawking clock is unchanged.

The next [retained spin-two contact balance](hb-source-contact-spin-two-balance.md) derives a paper Green identity for the actual characteristic-face density J[-Delta(Delta-2)Q]. It retains the bilinear contact-gradient term and gives every principal cusp flux power for the constant test and the same-occurrence angular QNM test. No constant-power collision occurs in those cases. Closing the regulated integral in Lean and matching the original physical subtraction remain open; the resulting quartic-period balance is not a positivity or extinction theorem.
