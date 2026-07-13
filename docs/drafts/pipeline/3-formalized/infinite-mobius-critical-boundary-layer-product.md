# Critical boundary-layer product of the all-prime Möbius channel

- **ID:** `infinite-mobius-critical-boundary-layer-product`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / source-side RH-chain bridge
- **Scientific status:** `[PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean module:**
  `formal/GaloisForLFunctions/RHTower/InfiniteMobiusCriticalBoundaryLayer.lean`
- **Statement:** The positive squarefree norm distribution and the signed all-prime Möbius shift
  have reciprocal critical responses on the same moving logarithmic aperture. Their product
  cancels the singular shifted zeta factor exactly before the critical limit and tends to
  `zeta(2)` independently of the aperture parameter.

## Theorem

Let

\[
\varepsilon=\sigma-1,
\qquad
s_\sigma(u)=\sigma+u(\sigma-1)=1+(1+u)\varepsilon,
\qquad
x_\sigma(u)=\frac{u(\sigma-1)}{\pi},
\]

where `sigma > 1` and `u >= 0`.  Write

\[
P_\sigma(n)
=\frac{\mu(n)^2n^{-\sigma}}
       {\sum_{d\ge1}\mu(d)^2d^{-\sigma}}
\]

for the squared-coordinate probability law of the unit-normalized squarefree Möbius channel. Its
moving-scale Laplace transform is

\[
B_\sigma(u)
=\sum_{n\ge1}P_\sigma(n)n^{-u(\sigma-1)}
=\frac{
   \sum_{n\ge1}\mu(n)^2n^{-s_\sigma(u)}}
  {
   \sum_{n\ge1}\mu(n)^2n^{-\sigma}}
.
\]

Lean proves the exact summand identity, summability, and total-sum identity above.  It then proves

\[
B_\sigma(u)\longrightarrow\frac1{1+u}
\qquad(\sigma\to1^+).
\]

Thus the formalized Laplace transforms are those of a mean-one exponential boundary layer for the
rescaled coordinate `(sigma - 1) log n`.

For the signed multiplier

\[
\tau_\sigma(x)
=\frac{\zeta(2\sigma)}
       {\zeta(\sigma)\zeta(\sigma+\pi x)},
\]

the moving aperture has the reciprocal second-order response

\[
\frac{\tau_\sigma(x_\sigma(u))}{(\sigma-1)^2}
\longrightarrow
\zeta(2)(1+u).
\]

The stronger finite-scale identity is

\[
B_\sigma(u)
\frac{\tau_\sigma(x_\sigma(u))}{(\sigma-1)^2}
=
\frac{\zeta(2\sigma)^2}
{\zeta(2s_\sigma(u))G(\sigma)^2},
\qquad
G(\sigma)=(\sigma-1)\zeta(\sigma).
\]

The factor `zeta(s_sigma(u))`, which carries the moving critical pole, cancels exactly. Therefore

\[
B_\sigma(u)
\frac{\tau_\sigma(x_\sigma(u))}{(\sigma-1)^2}
\longrightarrow\zeta(2),
\]

independently of `u`.

## Proof

The squarefree Dirichlet-series identity gives

\[
\sum_{n\ge1}\mu(n)^2n^{-s}=\frac{\zeta(s)}{\zeta(2s)}.
\]

Substitution at `s=s_sigma(u)` and `s=sigma` gives the exact formula for `B_sigma(u)`.  Introduce
the analytic residue unit

\[
G(s)=(s-1)\zeta(s),\qquad G(1)=1.
\]

Since `s_sigma(u)-1=(1+u)(sigma-1)`, division by the two residue units gives the positive limit.
The exact signed multiplier identity and the same residue factorization give its second-order
limit. Multiplication cancels `zeta(s_sigma(u))` algebraically and yields the finite-scale product
identity. Continuity at `2` and `G(1)=1` give the constant product limit.

The analytic input is the classical simple pole of zeta at one with residue one; see
[DLMF §25.2](https://dlmf.nist.gov/25.2). No Tauberian theorem, Xi divisor, or zero-location input
is used.

## Proof-chain contribution

```text
unit-normalized squarefree Möbius analysis
  -> exact positive moving-aperture Laplace transform
  -> exponential critical boundary-layer transforms
  -> exact signed second-order moving response
  -> exact positive/signed product cancellation
  -> [OPEN] realize this product as the covariance of the doubled charged continuation graph
  -> [OPEN] source-defined nonexpansive pole-to-divisor continuation
  -> four-unit divisor-energy bound
  -> RH.
```

The moving critical scale and the cancellation between positive escaped mass and signed arithmetic
response are no longer hypotheses. The remaining RH-bearing theorem must construct an
archimedean charged graph whose covariance preserves this exact product while retaining the
Euler-pole contour jump. Ordinary fixed compact synthesis remains excluded because it kills the
escaping channel mass.

## Lean certificate

Declarations:

- `mobiusCriticalBoundaryRate`;
- `mobiusCriticalBoundaryParameter`;
- `squarefreeMobiusBoundaryLayerLaplace`;
- `squarefreeMobiusBoundaryLayerTerm`;
- `squarefreeMobiusBoundaryLayerTerm_eq`;
- `summable_squarefreeMobiusBoundaryLayerTerm`;
- `tsum_squarefreeMobiusBoundaryLayerTerm`;
- `ofReal_tsum_squarefreeMobiusBoundaryLayerTerm`;
- `tendsto_squarefreeMobiusBoundaryLayerLaplace`;
- `tendsto_infiniteMobiusLaplaceMultiplier_moving_boundary`;
- `squarefreeMobiusBoundaryLayerLaplace_mul_signed_eq`;
- `tendsto_squarefreeMass_mul_signedMobius_moving_boundary`.

The module is imported by `formal/GaloisForLFunctions/RHTower.lean`.  The direct module and target
builds pass; the complete RHTower umbrella passes `9971/9971`; formal lint passes; and every theorem
above depends only on the standard axioms `propext`, `Classical.choice`, and `Quot.sound`.

## Gates

- [x] positive boundary-layer transform formalized from the actual channel probabilities
- [x] moving signed response formalized
- [x] exact finite-scale cancellation formalized
- [x] scale-independent product limit formalized
- [x] no Xi-divisor or RH-equivalent input
- [ ] charged graph covariance realization
- [ ] nonexpansive pole-to-divisor continuation
- [ ] four-unit bound
- [ ] RH
