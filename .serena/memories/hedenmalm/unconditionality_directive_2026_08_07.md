# DIRECTIVE: the Hedenmalm Lean layer must be UNCONDITIONAL — no hypotheses

The user's standing rule for this work: **Lean proofs must be unconditional. No premises, no
hypotheses.**  Working over a hypothesis class is not acceptable as the final form.

## What this changes

Everything built in `hedenmalm/folder_formalization_progress_2026_08_07` is currently stated over
the *class*

```
structure PositiveDensitySource where
  k : ℝ → ℝ ; continuous_k ; pos_k ; integrable_k
```

plus, in places, extra hypotheses: `HedenmalmQuantile.HasShiftedTail S z`,
`RootModeEndpoints S z`, evenness `hk : ∀ x, S.k (-x) = S.k x`, boundedness `∀ x, S.k x ≤ C`,
decay `Tendsto S.k atBot (𝓝 0)`.

**These must all be discharged**, by instantiating at the actual Hedenmalm theta source and proving
each side condition, so the headline theorems carry no hypotheses at all.

## The instantiation to build (top priority)

The corpus already owns the real source:

- `RHTower.thetaCuspStripSource : ℂ → ℂ` — `formal/GaloisForLFunctions/RHTower/ThetaCuspComplexStrip.lean:213`
  (`thetaCuspComplexSeed`, `thetaCuspComplexTerm` at lines 28/43; strip at 217)
- continuity on horizontal lines — same file, line 646
- `integrable_thetaCuspStripSource_horizontal` — same file, line 660
- `thetaCuspStripSource_ofReal`, `thetaCuspStripSource_neg` (evenness) — cited by
  `hedenmalm-reflection-folded-dirac-source-defect`
- `thetaCuspFourierLaplace_eq_XiC_on_strip` (`RHTower/ThetaCuspFourierLaplace.lean`) — identifies the
  transform with `XiC`, so `HedenmalmQuantile.xiC thetaSource = XiC` should be a theorem, not a
  definition mismatch.

**Build `def thetaSource : PositiveDensitySource`** with
`k x := (thetaCuspStripSource (x : ℂ)).re` (or the real form the corpus exposes), fields:
`continuous_k` from line 646 at `u = 0`; `pos_k` from the term-wise positivity of the theta series;
`integrable_k` from line 660 at `δ = 0, u = 0`.

Then add, as theorems about `thetaSource` (not hypotheses):
- evenness `∀ x, thetaSource.k (-x) = thetaSource.k x` (from `thetaCuspStripSource_neg`);
- boundedness `∀ x, thetaSource.k x ≤ C` for an explicit `C`;
- decay `Tendsto thetaSource.k atBot (𝓝 0)` and `atTop`;
- `HasShiftedTail thetaSource z` for every `z` in the relevant strip (from the horizontal
  integrability at `u = z.im`);
- `xiC thetaSource z = XiC z`.

Finally restate every headline theorem of the folder as an unconditional corollary at
`thetaSource`, and make the card `## Lean status` tables cite those hypothesis-free forms.

`RootModeEndpoints` is the one genuinely deeper item: its two endpoint limits must be *derived*
from the theta tail asymptotics (`1 - p(x) ≍ k(x)e^{-2x}` at `+∞`, `p(x) ≍ k(x)e^{2x}` at `-∞`,
per the compressed-inverse card), not assumed.

## Note

Keeping the general `PositiveDensitySource` layer is still correct engineering — it is where the
proofs live — but the *card-facing* statements must be the unconditional instantiations.

## Hypothesis audit (2026-08-07, after the directive was repeated)

Classify every hypothesis in the Hedenmalm layer into two kinds:

* **Data hypotheses** — quantifying over a test class (`ContDiff ℝ 1 f`, `HasCompactSupport f`,
  `0 ≤ L`, `z ≠ 0`, `|z.im| < 1`).  These are the statement, not an assumption; a formal-adjoint
  identity cannot be stated without naming its core.  Keep, but keep MINIMAL: prefer
  `ContDiff ℝ 1 f` + `HasCompactSupport f` over separate derivative/continuity/support hypotheses
  (`ContDiff.differentiable`, `ContDiff.continuous_deriv`, `HasCompactSupport.deriv` derive the
  rest).  `integral_weighted_symmetry` was tightened from 8 hypotheses to 3 this way; the 8-hypothesis
  version survives as `integral_weighted_symmetry_core`.
* **Assumption hypotheses** — standing in for unproven mathematics about the source
  (`HasShiftedTail S z`, `HasFiniteKernelEnergy S`, evenness, boundedness, decay,
  `RootModeEndpoints S z`).  These MUST be discharged at `thetaSource`.

Discharged so far: `HasShiftedTail` (`hasShiftedTail_thetaSource`, |Im z| < 1),
`HasFiniteKernelEnergy` (`hasFiniteKernelEnergy_thetaSource`), evenness (`thetaSource_even`),
boundedness (`thetaSource_le`), decay (`tendsto_thetaSource_atBot/atTop`),
metric-symbol bound (`norm_metricSymbol_thetaSource_le`).

### The ONE assumption bundle still standing: `RootModeEndpoints thetaSource z`

It is used by `rootFlux_identity` (card 1 statement (11)), and card 1 is ALREADY in stage 3, so
this must be closed for that card to be honest.

PROVEN ROUTE (analysed, not yet built).  `rootH S z t = -(1/M) · sourceModeU S z (Q t)` where
`sourceModeU S z x = e^{-izx} ∫_{Iic x} k χ_z`.  The whole bundle reduces to ONE global bound

    ‖sourceModeU thetaSource z x‖ ≤ C e^{-|x|}   for |z.im| < 1 AND XiC z = 0.

* x → −∞: `∫_{Iic x} k e^{-z.im y} dy ≤ C e^{(1-z.im)x}/(1-z.im)` (uses k ≤ C e^{-|y|}), times
  `‖e^{-izx}‖ = e^{z.im x}`, gives `C e^{x}/(1-z.im)`.
* x → +∞: at a zero, `∫_{Iic x} k χ = -∫_{Ioi x} k χ`, bounded by `C e^{-(1+z.im)x}/(1+z.im)`,
  times `e^{z.im x}`, gives `C e^{-x}/(1+z.im)`.
* `XiC z = 0` is REQUIRED for the +∞ half — without it `rootH` does not vanish at t → 1 when
  z.im > 0.  So the correct unconditional statement is
  `RootModeEndpoints thetaSource z` for `|z.im| < 1` and `XiC z = 0`, which is exactly how the
  flux identity is used.
* Then: `integrableValue` because rootH is BOUNDED on a finite-measure interval;
  `integrableEnergy` because `∫ q ‖rootH‖² = M⁻² ∫ ‖u(x)‖² dx` after the quantile change of
  variables, and `‖u‖ ≤ C e^{-|x|}`;
  `tendstoLeft/Right` from `Tendsto Q (𝓝[>]0) atBot` / `(𝓝[<]1) atTop` composed with the bound.
