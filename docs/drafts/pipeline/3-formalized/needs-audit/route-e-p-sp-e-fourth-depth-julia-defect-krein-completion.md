# Route E/P/SP-E fourth-depth Julia-defect Krein completion

- **ID:** `route-e-p-sp-e-fourth-depth-julia-defect-krein-completion`
- **Stage:** 3-formalized / needs audit
- **Type:** `[POSITIVE SURVIVOR] [THEOREM] [SOURCE DERIVATION] [P-G104]`
- **Parents:**
  `route-p-primitive-depth-square-modular-defect.md`,
  `route-p-primitive-hankel-depth-square-intertwiner.md`,
  `route-e-p-sp-e-cubic-source-normalization-debt.md`,
  `route-e-p-sp-e-source-normalization-krein-shorting.md`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/RouteEPCubicSourceNormalizationJuliaDefectCompletion.lean`

## Conjecture attacked

P-G103 proved that one-negative-index shorting restores literal fourth-depth energy `w/64` to
parent energy `w` exactly when off-diagonal cross equals `(sqrt 63 / 8)w`. That coefficient was
classified uniquely but not sourced. Treating it as an independently adjustable Gamma/polar
overlap would still be target fitting.

P-G104 asks whether Route P's already formalized depth-square contraction canonically produces
the cross.

## Failed reading and pivot

One depth-square step contracts squared energy by `1/8`; its Hilbert-amplitude factor is therefore
`1/sqrt 8`, not `1/8`. Using that one-step defect does not produce P-G103's `63/64` debt.

The relevant P-G100/P-G103 leg is fourth depth: two coefficient-faithful depth-square steps.
Squared energy is then `1/64`, so normalized Hilbert amplitude is exactly

```text
c = 1/8.
```

Its canonical Julia defect is

```text
d = sqrt(1-c^2) = sqrt(63/64) = sqrt 63 / 8.
```

Thus P-G103's apparently new coefficient is not free. It is forced by the minimal unitary
completion of Route P's literal two-step source contraction.

## Paper proof

For primitive cell `pe`, let

```text
w = routePPrimitiveBaseCauchyCubicWeight pe > 0.
```

P-G100 gives the coefficient-faithful fourth-depth law

```text
w(routePPrimitiveFourthDepth pe) * modularGain(pe)^2 = w/64 = c^2 w.
```

Let parent amplitude be `a=sqrt w`. The canonical Julia rotation with first column `(c,d)` sends
the source axis to

```text
(a,0) -> (c a, d a),
```

and preserves squared norm because `c^2+d^2=1`. Therefore

```text
(c a)^2 = w/64,
(d a)^2 = 63w/64,
(c a)^2 + (d a)^2 = w.
```

The off-diagonal parent--defect pairing is not `d sqrt w`; it is the product of the two source
amplitudes:

```text
a * (d a) = d a^2 = d w = (sqrt 63 / 8)w.
```

This is exactly P-G103's unique polar cross. Substitution into its negative-pivot Schur law gives

```text
w/64 - ((sqrt 63 / 8)w)^2 / (-w) = w.
```

The same factor is physical, not only arithmetic. P-G179 identifies one depth-square step with
half-amplitude dyadic dilation `f(r) -> f(2r)/2`, of squared-energy factor `1/8`. Two iterations are

```text
f(r) -> f(4r)/4
```

with exact squared-energy factor `1/64`. Hence `c=1/8` is the Hilbert norm factor of the literal
fourfold physical dilation. `QED`

## Uniqueness and minimality

Scalar multiplication by `c=1/8` is not an isometry. Among orientation-preserving plane
isometries whose first column is `(c,d)`, the second column is uniquely `(-d,c)`. One environment
coordinate is therefore both sufficient and minimal for positive isometric completion of this
source axis. The subsequent polar short still needs one negative pivot; Julia completion explains
cross magnitude, while Krein orientation explains correction sign.

## New knowledge and anti-theatre audit

Generic facts used here are standard:

- Julia operator of a contraction is unitary and has defect `(I-A*A)^(1/2)`; see P. L. Robinson,
  *Julia operators and Halmos dilations*, <https://arxiv.org/abs/1803.09329>.
- Schur complements extend to weakly complementable selfadjoint Krein-space operators; see
  Contino--Maestripieri--Marcantognini,
  *Schur complements of selfadjoint Krein space operators*,
  <https://arxiv.org/abs/1809.01695>.

Neither source contains Route P's primitive fourth-depth carrier, its exact `1/64` arithmetic and
physical energy law, P-G103's `63/64` normalization debt, or their identification. Corpus search
found generic Julia source lifts and generic Krein no-go laws, but no fourth-depth/Julia theorem
and no parent--defect pairing producing this coefficient.

New content is exact causal identification

```text
literal Route-P fourth-depth contraction
  -> canonical Julia defect
  -> unique P-G103 polar cross.
```

This removes coefficient fitting but does not construct Gamma/polar orientation or Xi landing.
Claiming RH, cofinal divisor identification, or completed countercurrent from this local source
completion would be theatre.

## Formal status

Lean proves unconditionally:

- `routeEPCubicFourthDepthNormalizedContraction_sq`;
- `routeEPCubicFourthDepthJuliaDefect_eq_sqrt63_div_eight`;
- `routeEPCubicFourthDepthJuliaSourceTransportV_normSq`;
- `routeEPCubicFourthDepthNormalizedContraction_not_scalar_isometry`;
- `routeEPCubicFourthDepthJuliaSourceTransportV_unique_positive_lift`;
- `integral_normSq_routePPrimitiveFourthDepthPhysicalDilation`;
- `routePPrimitiveFourthDepth_literalEnergy_eq_JuliaCompression`;
- `routePPrimitiveFourthDepthJulia_defectCompletesLiteralEnergy`;
- `routePPrimitiveFourthDepthJulia_parent_defect_pairing`;
- `routePPrimitiveFourthDepth_JuliaKreinCompletion`.

Direct `lake env lean` and exact target-only OLean build pass. `#print axioms` on all capstones
reports only `propext`, `Classical.choice`, and `Quot.sound`. Forbidden-token scan is clean.
RHTower umbrella import is wired; no umbrella build was run.

## Strongest positive survivor

P-G103's cross-magnitude construction gate is closed: coefficient is canonical parent--Julia-
defect source pairing. Successor P-G105/P-G105B now realizes contraction, defect, negative pivot,
and exact shorting inside Burnol co-Poisson source spaces; see
`route-p-fourth-depth-copoisson-julia-krein-pivot.md`. Remaining gate is no longer “find a cross or
pivot of this size.” It is:

1. identify P-G105B's Julia co-graph pivot through a source-defined intertwiner with literal
   oriented Gamma/Stokes co-source;
2. prove cellwise pairing respects primitive incidence and assembles cofinally;
3. identify resulting completed moments or divisor with Xi without target-selected fitting.

## Higher universal principle

Normalization debt is conservation leakage into a minimal environment. Positive Julia completion
determines how much energy is missing; one-negative-index Krein geometry determines how that
environment re-enters with opposite shorting sign. Previous scalar repairs failed because they
asked one positive channel to perform both tasks after compression.

## Log

- 2026-08-16 — P-G104 arithmetic/physical Julia defect, parent--defect cross derivation, unique
  positive lift, and Julia--Krein capstone formalized.
- 2026-08-16 — superseded locally by P-G105/P-G105B actual co-Poisson colligation and exact
  Julia co-graph Krein pivot.
