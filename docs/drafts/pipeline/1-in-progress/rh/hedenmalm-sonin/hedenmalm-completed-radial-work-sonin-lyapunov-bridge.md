# Hedenmalm completed radial work / Sonin Lyapunov bridge

- **Label:** `P-G129`
- **Route:** P
- **Parents:** `P-G126`, `P-G127`, `P-G128`, `BurnolBilateralApertureRH`, `XiHedenmalmBorelSoninApertureComparison`
- **Status:** theorem proved in Lean; umbrella integration complete

## Conjecture tested

Canonically orient every off-line Xi multiplicity copy toward the strict right half of the
completed strip.  Let

```text
lambda(q) = |Im(xiSpectralPoint(q))|
```

and let `k_N(q)` be Burnol's actual completed-Mellin Sonin evaluation vector along geometric
apertures `a r^(-N)` at the oriented completed Xi divisor point.  Test the two exact laws

```text
log ||k_N(q)|| / (N log r) -> lambda(q),
W(q) = lambda(q)^2 ||completedXiFirstDividedL2(q)||^2.
```

The first law must use the literal Sonin vector and actual Xi support; the second must use P-G126's
literal completed radial source work.  No proxy sequence, RH premise, positivity hypothesis,
computation, or added axiom is allowed.

## Scientific decision gate

- **Success:** local prime/Ward/Dirac dissipation is the quadratic shadow of the cofinal Sonin
  escape exponent.  This proves finite-scale positive repairs and aperture completion are one
  obstruction class, so Route P must pivot before positive completion to a source-level null trace.
- **Failure:** identify exact mismatch between support orientation, completed Mellin fibre, or
  local source normalization; retain strongest dependency-closed survivor.
- This is progress only if both constructions are joined on actual Xi fibres.  Reproving that
  either side vanishes on the critical line counts as theatre and is excluded.

## Prior-research audit

- 2026-08-13 — Audited multiplicative-jet, Cartier, same-fibre Ward, arbitrary finite aggregation,
  Burnol conormal, Green boundary, reflection quartet, common-forcing, and Sonin aperture modules.
  Finite connections are the flat tautological class `z`; reflection cancels signed current but
  doubles positive work; regular Hilbert source forms are nonclosable; Sonin completion escapes at
  exponent `|Re rho-1/2|`.
- Existing `GammaCoPoissonSoninQuadrantCharge` identifies one ladder-character exponent with
  centered divisor charge.  Existing `XiHedenmalmBorelSoninApertureComparison` identifies Borel
  and actual Sonin norm-growth exponents.  No theorem joins either exponent quantitatively to
  literal completed radial source work.

## Conjecturing log

- 2026-08-13 — C1 opened: canonical off-line right orientation preserves spectral width and lands
  at the actual completed Xi support.
- 2026-08-13 — C2 opened: actual Sonin evaluation-vector Lyapunov rate equals original-copy width.
- 2026-08-13 — C3 opened: completed radial work equals Lyapunov rate squared times divided-source
  energy.

## Verification log

- 2026-08-13 — Direct foreground check passed:
  `lake env lean GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmCompletedRadialWorkSoninLyapunovBridge.lean`.
- 2026-08-13 — Imported by `GaloisForLFunctions/RHTower.lean`.
- 2026-08-13 — Exact module build passed:
  `lake build GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCompletedRadialWorkSoninLyapunovBridge`
  (`12956/12956`).
- 2026-08-13 — Axiom audit passed for all new theorems; dependencies are exactly `propext`,
  `Classical.choice`, and `Quot.sound`.

## Result and pivot

- C1 proved. `xiSoninRightOrientedCopy` preserves multiplicity, its spectral width has the same
  absolute value as the original copy, every off-line oriented spectral imaginary part is negative,
  and its centered affine completed point is exactly its Xi divisor support.
- C2 proved for the literal Burnol completed-Mellin evaluation vectors at every geometric aperture
  tower: normalized log norm tends to `lambda(q)=|Im z_q|`.
- C3 proved coefficient-exactly:

  ```text
  W(q)=lambda(q)^2 ||completedXiFirstDividedL2(q)||^2.
  ```

- No-go closure: finite prime translation excess, Ward/Krein anomaly energy, completed Dirac radial
  work, Borel tail condition number, and cofinal Sonin evaluator escape are successive finite/local/
  cofinal presentations of one horizontal Lyapunov class. Positive completion cannot neutralize
  the local work; it transports its square root to infinity. Next producer must occur before both
  positive scalarization and Hilbert completion, through a literal source null trace or saturation
  law. Repackaging any post-radial positive detector is retired.
