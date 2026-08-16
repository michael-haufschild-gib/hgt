# Route U/Q quadratic concentration law

- **ID:** `route-u-q-quadratic-concentration-law`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE + dependency-closed `[BRIDGE]`
- **Scientific status:** `[FROZEN CONJECTURE] [ACTIVE ATTACK]`
- **Statement:** Route U admission walls and Route Q continued-source poles are two representations
  of one quadratic concentration defect; a source-pure finite quadratic-energy law excludes both
  while signed or absolute first-moment control cannot.

## Public sentence

False RH can hide from averages by concentrating obstruction into narrower boundary layers, but it
cannot hide from the quadratic energy of those layers.

## Frozen conjecture: quadratic concentration conservation

There is a canonical source-side quadratic concentration energy `E_src`, defined before divisor
reconstruction, with these two shadow maps.

1. **Route Q shadow.**  On a continued prime--Gamma frequency slice, `E_src` dominates the `L²`
   energy of every conjugate-paired relative-resolvent profile.
2. **Route U shadow.**  On a strict shifted-Hankel frontier chamber, `E_src` dominates the local
   quadratic energy of the Christoffel source wall after the canonical mass/frequency change.
3. **Source finiteness.**  Prime--Gamma source construction gives a finite cofinal bound for
   `E_src`, with no RH, zero-location, source-sign, or positivity premise.

The primitive is concentration energy, not pointwise sign or total source mass.  Route Q positive
spikes have bounded signed/first-moment footprint because opposite Cauchy lobes cancel.  Route U
walls have a regular literal numerator but singular endogenous admission scale.  Both defects are
therefore boundary concentration of a conserved source orientation.

### Why this is not a local restatement

- Route Q currently asks for pointwise upper boundedness or nonpositive source response.
- Route U currently asks for a moving-degree upper rate, accumulated source budget, or local
  integrability of the endogenous Christoffel quotient.
- A single source quadratic energy would imply both through different coordinate maps.  It changes
  the object being controlled from a response value to concentration carried across representations.
- Existing finite off-line Cauchy energy concerns Laplace profiles
  `sum_j exp(-(a_j+i gamma_j)t)`.  The bridge below concerns a moving transverse-frequency
  difference of two Poisson densities and its blow-up as the probe reaches an off-line displacement.

### Risky consequence

An unconditional uniform quadratic-energy ceiling may prove RH even when no pointwise source sign
and no uniform `L¹` estimate is available.  Conversely, any proposed `E_src` whose Q shadow controls
only signed mass or `L¹` mass is falsified by the exact bridge below.

### Falsifiers

- A source-pure candidate energy finite on the arithmetic side but failing to dominate either the
  Q pair profile or U Christoffel wall.
- A representation in which the required domination constant degenerates at exactly the off-line
  displacement/frontier.
- A finite quadratic-energy countermodel carrying either a nonzero simple Q pole or a strict U
  admission wall after the asserted shadow map.

## New bridge Q1: exact transverse Cauchy concentration

For `0 < y < b`, put

```text
P_{b,y}(t)
  = (b-y)/((b-y)^2+t^2) - (b+y)/((b+y)^2+t^2).
```

This is exactly the imaginary profile of one line-conjugate relative-resolvent pair after translating
frequency by the zero height.  Writing `alpha=b-y` and `beta=b+y`, it is the difference of the two
Poisson densities at transverse distances `alpha` and `beta`.

The following claims are dependency-closed.

1. `P_{b,y}` is integrable and

   ```text
   integral_R P_{b,y}(t) dt = 0.
   ```

   Thus signed frequency averaging annihilates the off-line pair exactly.

2. `P_{b,y}^2` is integrable and

   ```text
   integral_R P_{b,y}(t)^2 dt
     = pi*y^2 / (b*(b^2-y^2)).
   ```

3. Consequently this quadratic energy tends to `+infinity` as `y -> b` from below.

### Paper proof

For positive `c`, the Poisson identities are

```text
integral_R 1/(c^2+t^2) dt = pi/c,
integral_R 1/(c^2+t^2)^2 dt = pi/(2*c^3).
```

For positive `alpha,beta`, partial fractions give

```text
integral_R 1/((alpha^2+t^2)(beta^2+t^2)) dt
  = pi/(alpha*beta*(alpha+beta)).
```

The first claim follows because each normalized Poisson density has mass `pi`.  Expanding the
square gives

```text
pi/(2*alpha) + pi/(2*beta) - 2*pi/(alpha+beta)
  = pi*(beta-alpha)^2/(2*alpha*beta*(alpha+beta)).
```

Substitution `alpha=b-y`, `beta=b+y` yields the displayed formula.  Since its numerator tends to
`pi*b^2>0` and denominator tends to zero from above as `y -> b-`, the energy diverges.

### Meaning

This sharply separates failed strategies.  First-moment frequency averaging is not merely too
weak quantitatively: the off-line pair lies in its exact kernel.  Squaring before integration
removes the cancellation and produces a canonical blow-up coefficient.  Any successful Route Q
upper budget must therefore retain quadratic concentration or stronger information.

## Shadow table

| Corpus item | Quadratic-concentration shadow |
|---|---|
| Route Q source imaginary part exceeds every ceiling under false RH | Point evaluation of a narrowing Cauchy concentration layer |
| Line-conjugate relative-resolvent pair formula | Unsquared signed density `P_{b,y}` |
| Reflection-fixed mixed incidence survives diagonal packet collapse | Cross term retained when `P_{b,y}` is squared |
| Route U strict-frontier Christoffel wall is non-`L¹` | Admission-coordinate concentration layer |
| Route U literal numerator remains continuous/integrable | Concentration belongs to denominator scale, not raw source mass |
| Moving-degree delayed-switch no-go | Pointwise/cofinal data without a width-sensitive energy cannot control concentration |

## Attack loop

1. **Conjecture Q1:** signed frequency mass detects an off-line conjugate pair.
   **Failed:** exact mass is zero.  This is not an estimation loss.
2. **Pivot Q2:** positive-part `L¹` mass must diverge as the pole is approached.
   **Failed on paper:** the narrowing positive lobe has bounded mass; simple-pole height and width
   compensate.
3. **Pivot Q3:** quadratic frequency energy diverges.
   **Proved on paper:** exact formula above.
4. **Next hard attack:** construct the source-pure arithmetic quadratic energy and prove a finite
   cofinal ceiling before continuation; then identify its Q shadow without diagonalizing away mixed
   reflection incidence.
5. **Parallel U attack:** identify the same energy under the frontier mass/frequency coordinate and
   prove it dominates the Christoffel wall's local quadratic energy with nondegenerate constant.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure target, hostile failures recorded, corpus novelty audited
- [ ] Q1 paper bridge formalized in Lean and wired into `GaloisForLFunctions.RHTower`
- [ ] Source-pure arithmetic quadratic energy constructed
- [ ] Route Q domination proved with nondegenerate constant
- [ ] Route U domination proved with nondegenerate constant
- [ ] Unconditional source finiteness proved
- [ ] RH closed in Lean without premises

## Log

- 2026-08-16 — Frozen after corpus search eliminated existing pointwise, Bernstein-mass,
  full-density-current, affine-pencil, and finite Laplace Cauchy-energy formulations.  Q1 paper
  bridge proved; Lean formalization started.
