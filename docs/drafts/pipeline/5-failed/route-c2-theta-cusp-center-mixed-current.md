# Route C2 — theta-cusp center-mixed Fourier current

- **ID:** `route-c2-theta-cusp-center-mixed-current`
- **Stage:** 5-failed
- **Type:** RETIRED ROUTE / UNCONDITIONAL LEAN NO-GO WITH POSITIVE SURVIVOR
- **Statement:** C2 positivity is exactly Xi zero-width and therefore reaches RH only at width zero;
  every off-line zero remains visible as an oriented odd-order germ of the completed current.

## Terminal theorem

For every `tau>0` and `alpha>=0`,

```text
HedenmalmGaussianHankelTailCone tau alpha
  <-> XiZeroHalfPlaneBound alpha.
```

At `alpha=0` this is RH. The exact zero-safe divisor theorem strengthens the negative diagnosis:
if `alpha` is a centered Xi zero of multiplicity `m` and `Q(alpha)!=0` is its terminal cofactor,
then on the transverse through the zero,

```text
C_Xi(a,b0)
  = x^(2m-1)
      [2m|Q(z_a)|² + 2x Im(Q'(z_a) conjugate(Q(z_a)))],
```

whose bracket is strictly positive at `x=0`. In the full plane,

```text
C_Xi(a,b)
  = (x²+y²)^(m-1)
      [2m x |Q(z)|² + 2(x²+y²) Im(Q'(z) conjugate(Q(z)))].
```

Thus no infinite shell, product-fibre, or tangential compensation can erase the leading oriented
cone of an off-critical zero.

## No-go closure

- **Exact killing theorem/mechanism:** complete C2 tail positivity is equivalent to the actual Xi
  divisor width bound. The requested final aperture `alpha=0` is RH, not a source theorem produced
  by the theta coordinates.
- **Dead mechanisms:** pointwise cone-kernel positivity; finite shell prefixes; fixed endpoint jet
  order; fixed Bochner/Hankel rank; generic positivity; generic log-concavity; total-variation
  bounds that destroy signed ground-shell cancellation; tangential compensation after cofinal
  product-fibre completion.
- **Strongest positive survivor:** completed C2 current is an exact zero-safe divisor transducer.
  It recovers horizontal width globally and side, location, and analytic multiplicity locally.
- **New insight:** the full planar leading germ is
  `2m|Q(alpha)|² x(x²+y²)^(m-1)`. Tangential displacement contributes only to the radial factor and
  higher coefficient, so it cannot rotate away the leading transverse sign.
- **Status:** dependency-closed paper proof and unconditional Lean formalization complete. Axiom
  audit is `[propext, Classical.choice, Quot.sound]`. Direct foreground Lean checks pass; full build
  intentionally omitted. Repository lint sees both C2 modules and is blocked only by unrelated
  untracked `BVCoPoissonCompactSeedRigidity` and `DeningerEnergyIdentity` modules missing umbrella
  imports.

## Published ownership boundary

- Sondow--Dumitrescu already own strict horizontal Xi-modulus monotonicity in zero-free half-planes.
- Planat's June 2026 paper already owns theta-kernel positivity framing and critical-aperture
  localization.
- These exact statements are formalized in
  `RHTower/ThetaCuspCenterMixedPublishedGrowthPriorArt.lean` and classified as not new.
- External novelty of the separate zero-safe odd divisor germ remains unverified; it is a bridge,
  not an RH result.

## Formal artifacts

- `RHTower/HedenmalmGaussianHankelApertureWidthSpectrum.lean`
- `RHTower/ThetaCuspCenterMixedDivisorTomography.lean`
- `RHTower/ThetaCuspCenterMixedPublishedGrowthPriorArt.lean`

## Successor rule

Reopening C2 requires a literal new source theorem that shrinks the actual Xi divisor width to
zero without assuming an equivalent positivity or zero-free premise. More coordinates or another
conditional monotonicity theorem do not reopen it.

## Log

- 2026-08-01 — complete phase law audited; zero-width endpoint identified as RH itself.
- 2026-08-01 — exact transverse and planar divisor tomography formalized; C2 retired with its
  strongest positive survivor.
- 2026-08-01 — Sondow--Dumitrescu and June 2026 Planat ownership formalized explicitly.
