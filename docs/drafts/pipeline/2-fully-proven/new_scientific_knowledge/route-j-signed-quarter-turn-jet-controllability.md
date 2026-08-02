# Route J signed quarter-turn jet controllability

- **ID:** `route-j-signed-quarter-turn-jet-controllability`
- **Stage:** 2 — fully proven on paper
- **Type:** THEOREM / SHARP THEATRE BOUNDARY
- **Scientific status:** `[CORPUS-NEW SOURCE-SPECIFIC CLASSIFICATION]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/XiCTaylorSignedAtomicJetControllability.lean`
- **Parent:** `route-j-moving-positive-completion-gauge-rigidity.md`

## Result

The moving positive-completion theorem is a genuine positivity theorem, not a generic consequence
of the half-plane kernel. Once real signs and mesh-dependent source locations are allowed, four
atoms control the complete complex value--derivative jet at every point with positive real part.

Fix

```text
z=u+iy,   u>0,
T=pi/(2u),   r=exp(-Ty)>0.
```

For real weights `a_1,...,a_4`, put

```text
G_a(z)=sum_(k=1)^4 a_k(1-exp(i kTz)),
H_a(z)=sum_(k=1)^4 a_k(-i kT)exp(i kTz).
```

Then

```text
(a_1,a_2,a_3,a_4) |-> (G_a(z),H_a(z)) in C^2
```

is an isomorphism of real vector spaces. Consequently every prescribed pair `(G,H) in C^2` is
realized by one signed four-atom packet.

This is the exact local boundary of the signed-conditioning no-go. Define

```text
F=iG/z,                     G=-izF,
D=(iH-F)/z,                 H=-i(F+zD).
```

For any independent mesh scale `delta>0` and any real charge `m`, choose

```text
G=1,
H=i(m/delta+Im(1/z)).
```

Then `F` is nonzero and the four-atom packet satisfies

```text
delta Im(D/F)=m                                         (JQ1)
```

exactly, not only asymptotically.

## Exact quarter-turn matrix

At the four support points the phases are

```text
 exp(iTz)=ir,
 exp(2iTz)=-r^2,
 exp(3iTz)=-ir^3,
 exp(4iTz)=r^4.
```

Therefore

```text
| Re G |   |  1   1+r^2      1    1-r^4 | | a_1 |
| Im G | = | -r      0      r^3      0   | | a_2 |
| Re H |   | Tr      0    -3Tr^3     0   | | a_3 |
| Im H |   |  0    2Tr^2      0   -4Tr^4 | | a_4 |.       (JQ2)
```

Its determinant is

```text
4 T^2 r^6 (1+r^2)^2 > 0.                               (JQ3)
```

The Lean certificate avoids relying on a determinant normalization. It solves the odd block
`(Im G,Re H)` first and then the even block `(Re G,Im H)`:

```text
a_1=-(3T Im G+Re H)/(2Tr),
a_3=-(T Im G+Re H)/(2Tr^3),

R=Re G-a_1-a_3,
a_4=(R-(1+r^2)Im H/(2Tr^2))/(1+r^2)^2,
a_2=Im H/(2Tr^2)+2r^2 a_4.                             (JQ4)
```

Direct substitution proves `(JQ2)` has output `(G,H)`.

## Proof of exact charge

The source connections imply

```text
D/F=H/G-1/z.                                            (JQ5)
```

For the specialized jet,

```text
Im(H/G)=m/delta+Im(1/z).
```

Subtracting the last term in `(JQ5)` and multiplying by `delta` proves `(JQ1)`.

## Scalar charge collapses uniquely to two atoms

For the specialized scalar jet `G=1`, `H=iq`, the odd block in `(JQ2)` is homogeneous and
nonsingular, so `a_1=a_3=0`. The even block then has the unique solution

```text
a_4=[1-(1+r^2)q/(2Tr^2)]/(1+r^2)^2,
a_2=q/(2Tr^2)+2r^2a_4.
```

Thus atoms at `2T` and `4T` suffice for every scalar horizontal charge, and every four-atom
quarter-turn realization of that scalar jet is this same two-atom packet. Four atoms are needed
only for an arbitrary pair `(G,H) in C^2`.

The unique weights expose a cross-mesh invariant:

```text
delta a_2+(1-r^2)delta a_4=delta/(1+r^2).
```

Any normalized limit `(b_2,b_4)` therefore lies on
`b_2+(1-r^2)b_4=0`. A common nonzero limiting profile at two fibres forces their radii to agree.
On the Xi mesh,

```text
r(sigma)=exp[-pi(1/2-Re sigma)/(2 Im sigma)].
```

The functional-equation mate `1-conj(sigma)` has reciprocal radius. Hence a common
reflection-invariant nonzero profile at both fibres forces `Re sigma=1/2`. For nonzero charge,
the exact fourth-weight limit is

```text
delta a_4 -> -m/[2Tr^2(1+r^2)] != 0.
```

Full proof and Lean certificate:

```text
docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/
  route-j-signed-charge-ray-reflection-rigidity.md
```

## What this closes

This theorem refutes a possible overclaim from the preceding linear-conditioning lower bound:
one cannot eliminate arbitrary signed moving completions by strengthening the same pointwise
absolute-variation estimate. The signed atomic jet map is already onto. In particular:

1. finite source support does not force zero anisotropic charge;
2. the two exact integration-by-parts connections do not force zero charge;
3. a scalar logarithmic derivative does not force zero charge;
4. pointwise source integrability or a finite-dimensional source model cannot distinguish an
   independently produced gauge from a divisor-fitted interpolation.

The displayed screening packet is deliberately **not** a Route-J construction. Its target jet
contains `m`. Calling it source-defined would be representation theatre. The theorem instead
proves that the remaining valid hypothesis must be global:

```text
one pre-divisor source law
  -> all mesh points coherently
  -> without Xi-zero location or multiplicity in its coefficients.
```

Thus `J-SF6` is narrowed from “some indefinite signed density” to a coherent, divisor-independent
signed source family. Pointwise signed/singular transgression is algebraically universal and
therefore scientifically nonselective.

The construction also proves the preceding linear condition-number obstruction has the correct
order. Suppose `z_n=u_n+iy_n` stays in a compact subset of `u>0`, let
`delta_n->0`, and keep `m!=0`. Then `T_n=pi/(2u_n)` and `r_n=exp(-T_n y_n)` stay in compact
positive parameter ranges. Formula `(JQ4)` is affine in `H_n`, while
`||H_n||=O(1/delta_n)`. Hence every atomic weight is `O(1/delta_n)`. The absolute completion mass
is bounded by twice the sum of those weights, while `||G_n||=1`, so

```text
kappa_n=O(1/delta_n).
```

The signed-conditioning theorem gives the matching `Omega(1/delta_n)` lower bound at a screened
nonzero divisor charge. Thus pointwise signed screening has exact condition-number order
`Theta(1/delta_n)`. The remaining obstruction cannot be improved from linear to superlinear
without a cross-mesh source hypothesis.

## Honest density extension

The atomic statement is singular but not isolated. Replace each Dirac atom by a unit-mass bump on
a small disjoint interval around its support. The four value--derivative columns converge to the
columns of `(JQ2)`. Determinant is continuous and nonzero at the atomic packet, so it remains
nonzero for all sufficiently narrow bumps. Solving the perturbed real system gives a compactly
supported signed `L^1` density realizing the same prescribed `(G,H)` exactly.

This perturbation argument proves local surjectivity for honest signed densities as well. The
exact atomic model is retained in Lean because it is the minimal source interface and records the
closed-form inverse rather than hiding it behind a general perturbation theorem.

## Novelty and collision audit

Hermite interpolation and Prony interpolation by exponential sums are classical themes. No
standalone novelty is claimed for the abstract fact that enough exponential coordinates can
interpolate a value and derivative. Relevant modern primary examples include Ali--Páles,
*Hermite-type interpolation in terms of exponential polynomials* (arXiv:2412.07925), and Chunaev,
*Interpolation by generalized exponential sums with equal weights* (arXiv:1906.01332).

Targeted searches found no source-specific statement combining:

1. the one-sided completion atoms `1-exp(itz)`;
2. the explicit quarter-turn source locations `(T,2T,3T,4T)`;
3. the nonzero determinant `(JQ3)`;
4. the covariant connections `(JQ5)`; and
5. exact Xi anisotropic horizontal-charge interpolation `(JQ1)`.

The corpus-new content is this explicit classification and its sharp use as a theatre boundary
for Route J. External priority is not claimed.

## Lean audit

The formal module proves unconditionally:

- all four exact quarter-turn phase values;
- exact physical-to-real-coordinate completion and derivative bridges;
- explicit inverse weights and full jet surjectivity;
- unique reduction of every scalar charge jet to the two even atoms;
- both source connections and the logarithmic-current identity;
- exact prescribed horizontal charge at every point with positive real part;
- normalized charge-ray and reflection-mate rigidity.

Direct command:

```text
cd formal
lake env lean GaloisForLFunctions/RHTower/XiCTaylorSignedAtomicJetControllability.lean
```

passes with no warnings. No `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration occurs.

## Route consequence

Route J remains open. New surviving `J-SF6` core:

```text
construct or exclude one coherent divisor-independent signed Gamma/theta/co-Poisson source family;
pointwise moving signed interpolation receives no source-construction credit; within the
quarter-turn scalar channel an off-line survivor must break functional-equation reflection
equivariance in its leading normalized weights.
```
