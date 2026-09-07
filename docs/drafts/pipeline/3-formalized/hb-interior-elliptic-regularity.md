# HB actual interior elliptic regularity

Stage: formalized in Lean 4; final leaf audits passed. Type: `[BRIDGE]`.
RH remains open.

Chain: literal theta cusp → Xi occurrence → retained spin-two source → physical
causal response and left-QNM pairing → independent fixed Hawking-clock extinction → RH.

Every compact interior localization of the constructed full-forcing angular
response has planar Sobolev order two. Its actual localized Laplacian belongs to
L², and its Fourier transform has an L¹ representative. The proof derives these
properties from the original modular energy domain and the complete forcing;
it supplies no regularity or differential-equation hypothesis on the response.
Higher interior regularity and smooth reconstruction on the open cell are proved
in [smooth interior response](hb-interior-smooth-response.md). Reconstruction across
modular seams remains open.

## Actual tests and distributional equation

Use the actual domain V, scalar projection J, and unique response h from
[the modular energy-domain construction](hb-modular-energy-domain-and-weak-response.md).
Write `D_i h` for its two completed hyperbolic-frame components, `i=1,I`.
The native measure is `mu=dx dy/y²` on the modular cell. The physical parameter
L and full cusp-subtracted forcing F retain their original definitions.

For every globally smooth compact complex test g supported inside the open cell,
construct its modular periodization. It equals g on the closed cell and hence
has the actual same derivatives on the open cell. The periodization of conj(g)
therefore gives an energy-domain test whose scalar component is conj(g) and whose
gradient components are conj(y*partial_i g), almost everywhere in the native
measure. These identities are proved from the actual fields before pairing.

The completed graph constraints give

`integral y*g*D_i h dmu = -integral y²*(partial_i g)*Jh dmu`.

Use the derivatives of g as tests and substitute the constructed energy test into
the full response equation. Both derivatives move onto g, giving

`integral y²*(Delta_E g)*Jh dmu - L*integral g*Jh dmu = integral g*F dmu`.

This is a proved distributional equation for the actual response. It is not an
assumption that the abstract form operator agrees with the differential operator.

## Native-to-planar localization

For u in the actual angular L² space, define

`localValue(g,u)(z)=g(z)*u(ofComplex z)`.

The test support lies inside the open cell, so this function vanishes outside
the closed cell. The native measure's proved pushforward has density `1/y²`.
For every nonnegative integer n, compactness bounds the smooth coefficient
`y^n*g`, proving that `y^n*localValue(g,u)` is L² under that pushforward measure.

The n=2 case first supplies planar L¹ integrability: the exact with-density
integrability theorem cancels `y²/y²`. The squared norm of the n=1 case supplies
planar square integrability by the same cancellation. Together these prove
`localValue(g,u)` belongs to planar L². This applies to the scalar response,
both completed gradients, and the original forcing vector. The proof does not
assume a globally measurable extension of `ofComplex` or a smooth representative
of u.

For each n, `g/y^n` is itself a smooth compact interior test. On the test support,
height is positive and inversion is smooth. Off the support, the whole function
vanishes in a neighborhood, including near the real axis. Thus all inverse-height
coefficients used in the next step have proved smooth zero extensions.

Native integral transport gives the exact planar equations

```
integral (g/y)*D_i h + integral (partial_i g)*Jh = 0,
integral (Delta_E g)*Jh - L*integral (g/y²)*Jh = integral (g/y²)*F.
```

## Full cutoff commutator

Let T(g,u) be the tempered distribution represented by the proved planar L²
function `localValue(g,u)`. Pair the completed derivative constraint against
`g*psi`, where psi is an arbitrary Schwartz test. The literal product derivative
and the proved integrability of each product give

`partial_i T(g,Jh) = T(partial_i g,Jh) + T(g/y,D_i h)`.

Apply the original forced weak equation to the same product test. It gives the
localized current divergence

```
sum_i partial_i T(g/y,D_i h)
  = sum_i T((partial_i g)/y,D_i h) + L*T(g/y²,Jh) + T(g/y²,F).
```

The actual orthonormal basis `(1,I)` identifies the distributional Laplacian.
Combining the two identities proves

```
Delta_E T(g,Jh)
  = sum_i T(partial_i² g,Jh)
    + 2*sum_i T((partial_i g)/y,D_i h)
    + L*T(g/y²,Jh) + T(g/y²,F).
```

Both cutoff terms survive. Every term on the right is a proved L² distribution;
their finite sum proves that the actual localized Laplacian is L².

## Fourier regularity gain

The current mathlib defines the Bessel potential B_s by Fourier multiplier
`(1+|xi|²)^(s/2)`. Its precise normalization gives

`B_2 u = u - (2*pi)^(-2)*Delta_E u`.

This identity is proved through the actual Fourier multiplier calculus.
If u and its Laplacian belong to H^s, the right side belongs to H^s. The proved
composition law for Bessel potentials therefore gives u in H^(s+2).
Apply this result at s=0 to T(g,Jh) and the actual L² Laplacian above. It proves
H² for every compact interior localization of every actual Xi response on both
physical branches. Since the real planar dimension is two, mathlib's proved
Sobolev Fourier estimate also gives an L¹ representative of its Fourier transform.

## Lean surface and validation

| Module | New public theorems | Exact surface |
|---|---:|---|
| `RHTower.ThetaCuspHawkingBMInteriorDistributionEquation` | 10 | Actual modular energy tests, both derivatives, complete native distributional PDE |
| `RHTower.ThetaCuspHawkingBMPlanarLocalDomain` | 5 | Planar L² localization, inverse-height tests, exact planar forced PDE |
| `HTGeometry.PlanarSobolevLaplacianGain` | 2 | Fourier-normalized Bessel identity and two-derivative gain |
| `RHTower.ThetaCuspHawkingBMInteriorEllipticRegularity` | 11 | Original local derivatives and current, complete cutoff commutator, actual local H² and Fourier L¹ |

All seven development scratch modules passed `lake env lean` without diagnostics.
The four canonical leaves passed their individual `lake build <module>` audits
in a cache-only package: 6.8s, 22s, 2.5s and 10s in table order. Only these four
leaves compiled; existing dependencies were reused. Audited and canonical source
bytes match. Exactly eight new olean/ilean artifacts are installed, and each leaf
is wired once into its theorem-area umbrella. No umbrella build ran.

One scratch `lake env lean` audit checked exactly these 28 new public theorem
axiom sets. All contain only `propext`, `Classical.choice` and `Quot.sound`, with
no diagnostics. Scoped whitespace checks passed. No numerical experiment or
numerical certificate is used. The generated source index was refreshed. The
final global `lint --check-generated` reports an unrelated missing umbrella import
for `RHTower.MontgomeryPrimeSideBounds` and a stale `formal/LEAN_API.md` during
concurrent source edits. It reports no errors in these four new leaves. Global
lint is therefore not claimed to pass.

## Remaining bridge

The [smooth interior response](hb-interior-smooth-response.md) supplies every local
Sobolev order and a smooth representative of the actual native class on the open
cell. Extend the weak equation and regularity proof across the modular side identifications
and stabilizer charts. Construct the global cusp-cutoff extension and assemble
the full angular field. Then prove the physical causal prescription, horizon and
radial boundary conditions, gauge conditions, and original left-QNM pairing.
The SS/VV sectors and independent fixed Hawking-clock extinction remain open.
Local H² regularity alone establishes none of those remaining physical conclusions.
