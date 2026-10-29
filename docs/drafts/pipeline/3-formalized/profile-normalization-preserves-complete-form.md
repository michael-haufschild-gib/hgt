# Profile normalization preserves the complete form

- **ID:** profile-normalization-preserves-complete-form
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Normalizing profile support `[a,b]` to `[0,1]` multiplies width and overlap
  by `b-a`, divides inverse-width height by `b-a`, and preserves the complete Weil value
  and both actual and coefficient-normalizing masses.
- **Module:** `SpacingScaleHarmonicAnalysis/ProfileNormalizationPreservesTheCompleteForm.lean`.

## Proof

For `a<b`, put `d=b-a` and `ψ(v)=φ(a+dv)`. The normalized profile vanishes outside
`[0,1]` whenever `φ` vanishes outside `[a,b]`. At every positive width,
`φ(u/w)=ψ((u-aw)/(dw))`; all logarithmically centered atoms undergo the same translation.
Thus their synthesized tests agree after translation by `aw`.

Translation invariance of the full Weil form preserves its value, including both poles.
Translation invariance of Lebesgue measure preserves the synthesized squared mass and
the mass of one atom. Their atom-mass-normalized complete values therefore agree exactly.
The width change gives overlap `dc` and height `T/d`.

In particular, support `[-1,1]` at overlap `c` becomes support `[0,1]` at overlap `2c`.
This is a reparametrization of the same profile, not a transfer between the distinct plateau
and Steklov profiles.

## Lean declarations

- `unitIntervalProfile_eq_zero_outside`
- `atomDilate_profile_normalization`, `atomicTest_profile_normalization`
- `weilQuad_atomicTest_profile_normalization`
- `integral_atomicTest_sq_profile_normalization`
- `integral_atomDilate_sq_profile_normalization`
- `normalized_weilQuad_profile_normalization`
- `height_profile_normalization`, `weilQuad_symmetric_profile_overlap`

Direct `lake --old env lean` check and all three transitive axiom audits passed.
Only `propext`, `Classical.choice`, and `Quot.sound` occur. Umbrella import is wired.
