# The completed xi theta source is an exact two-sided seam

- **ID:** xi-theta-source-seam
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), `[PROVED]`
- **Date:** 2026-07-10
- **Module:** `GaloisForLFunctions.RHTower.XiThetaSourceSeam`
- **Paper proof:** `../../2-fully-proven/new/xi-theta-source-seam.md`

## Formal surface

- `modifiedEvenKernel_of_one_lt` — the positive modified source is the raw theta tail.
- `evenKernel_zero_sub_one_pos` — strict positivity of that tail.
- `modifiedEvenKernel_exp_neg` — exact reciprocal-scale law.
- `xiThetaLogSource` — critical logarithmic normalization.
- `xiThetaLogSource_neg` — literal evenness.
- `xiThetaLogSource_ne_zero` — nonvanishing off the reflection point.
- `xiThetaPositiveSource` / `xiThetaReflectedSource` — canonical half-sources.
- `xiThetaPositiveSource_hasAELowerSupport` — direct discharge of the lower-support Prop.
- `xiThetaLogSource_split` — exact pointwise source-plus-reflection decomposition.
- `xiThetaReflectedSource_eq` — reflected source equals the negative-half indicator.
- `xiThetaLogSource_not_hasAELowerSupport` — universal failure of lower support for the full target.

## Certificate

- Targeted source check: passed.
- Targeted module build: passed; no umbrella/full build run.
- Axiom audit: `[propext, Classical.choice, Quot.sound]` only.
- Active `sorry`, `admit`, `axiom`, `opaque`, `unsafe`: none.
- Generated API refreshed; formal lint passed.

## Scope

The theorem identifies and splits the actual completed source.  It does not yet construct the
half-source's non-diagonal coefficient coordinate or compute the reflected half's Perron charge.
