# Route E/P/SP-E source-normalization Krein shorting law

- **ID:** `route-e-p-sp-e-source-normalization-krein-shorting`
- **Stage:** 3-formalized / needs audit
- **Type:** `[POSITIVE SURVIVOR] [THEOREM] [EXACT CONSTRUCTION TARGET] [P-G103]`
- **Parents:**
  `route-e-p-sp-e-cubic-source-normalization-debt.md`,
  `prime-gamma-physical-plucker-boundary-spectral-shell-no-go.md`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/RouteEPCubicSourceNormalizationKreinShorting.lean`

## Conjecture attacked

P-G102 proves no scalar resolvent channel of current positive physical operator supplies required
amplitude eight near zero.  P-G103 asks for smallest operator-changing source/co-source geometry
capable of restoring coefficient-faithful fourth-depth energy `w/64` to parent energy `w`.

Conjecture: ordinary positive Schur shorting through parent channel can pay `63w/64` debt.

## Exact classification

For positive parent pivot `w` and real cross `r`, positive shorting is

```text
w/64 - r^2/w <= w/64 < w.
```

It can never rebalance.  Replacing pivot by oriented polar channel `-w` gives

```text
w/64 - r^2/(-w) = w
  <=> r^2 = (63/64)w^2.
```

Unique nonnegative cross is

```text
r = (sqrt 63 / 8) w.
```

At exact coupling, two-channel determinant is `-w²<0`.  A negative channel is forced.  Naive full
cross `r=w` produces `65w/64`, exactly same value as original coefficient-faithful parent-plus-child
trace.  Full polar coupling therefore reproduces debt rather than repairs it; required attenuation
is rigid.

## Positive survivor

- **New exact target:** construct literal Gamma/co-Poisson/Stokes source/co-source cross term with
  magnitude `(sqrt 63 / 8)w` against polar pivot `-w`, before positive spectralization.
- **No-go boundary:** any positive-pivot Schur complement fails regardless cross coefficient;
  scalar polar residue of magnitude `w` also fails, returning `65w/64`.
- **One-negative-index law:** determinant `-w²` certifies irreducible indefinite two-channel block.
  This matches P-G205 architecture, where raw negative Weil energy is neutralized by positive
  fundamental-symmetry gap.  Both normalization and orientation demand same Krein ordering.

## Higher universal principle

All prior repairs were attempted after positivity: probability reweighting, trace counterterms,
boundary transfer, normalized inverse, unnormalized inverse.  These preserve or reduce positive
spectral budget.  Required correction adds energy.  Exact Schur law shows why repeated failures are
shadows of one principle: **completion is one-negative-index source geometry before positive
compression, not scalar amplification after it**.  Number `63/64` is cross-square deficit, not free
trace mass.

## Conjecture loop audit

1. **Conjecture:** existing orthogonal `4+4` source decomposition supplies gain eight.
   **Failed:** squared norm eight is not amplitude eight; transverse pointed source has energy four.
2. **Conjecture:** positive source/source cross shorting can increase depleted leg.
   **Failed universally:** Schur correction has negative sign.
3. **Conjecture:** negative polar pivot restores energy with full cross `w`.
   **Failed sharply:** result is `65w/64`, original pair trace.
4. **Pivot proved:** attenuated cross `(sqrt 63 / 8)w` restores exactly, uniquely among nonnegative
   cross terms, and forces determinant `-w²`.
5. **Successor P-G104:** Route P's literal fourth-depth amplitude is `1/8`; its canonical Julia
   defect is `sqrt(63)/8`, and parent--defect pairing is exactly this attenuated cross. Magnitude is
   source-derived. Orientation and identification with actual Gamma/polar co-source remain open.

## Formal status

Lean proves without added axioms:

- `routeEPCubicPositivePivotShortedFourthDepthEnergy_ne_parent`;
- `routeEPCubicPolarPivotShortedFourthDepthEnergy_eq_parent_iff`;
- `routeEPCubicFourthDepthQuantizedPolarCross_sq`;
- `routeEPCubicFourthDepthQuantizedPolarCross_unique`;
- `routeEPCubicPolarBlockDet_quantized`;
- `routePPrimitiveFourthDepth_sourceFaithful_pairTrace_eq_fullPolarShort`;
- `routePPrimitiveFourthDepth_sourceNormalizationKreinShorting_classification`.

Direct `lake env lean` and exact target build pass. `#print axioms` reports only `propext`,
`Classical.choice`, and `Quot.sound`. RHTower umbrella import is wired; no umbrella build was run.

## Open core

P-G104 closes cross magnitude. Identify canonical fourth-depth Julia defect coordinate with literal
oriented Gamma/co-Poisson/Stokes co-source, prove summable cofinal incidence assembly, and identify
resulting indefinite shorted divisor with Xi before any positive determinant.

## Log

- 2026-08-16 — P-G103 positive/Krein shorting classification and `65/64` full-cross duality
  formalized.
- 2026-08-16 — P-G104 successor derives unique cross as parent--Julia-defect source pairing.
