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
