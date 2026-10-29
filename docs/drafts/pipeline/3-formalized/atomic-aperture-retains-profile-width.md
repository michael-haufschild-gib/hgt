# Atomic aperture retains the profile width

- **ID:** atomic-aperture-retains-profile-width
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For a profile supported in `[a,b]`, positive width `w`, and length `N`,
  the atomic test is supported in `[aw,log N+bw]`. Its centered enclosing aperture is
  `(log N+(b-a)w)/2`, with outer autocorrelation cutoff `N exp((b-a)w)`.
- **Module:** `SpacingScaleHarmonicAnalysis/TheAtomicApertureRetainsTheProfileWidth.lean`.

## Proof

An atom with index `1≤n≤N` can be nonzero only when
`aw≤u-log n≤bw`. Since `0≤log n≤log N`, every summand vanishes outside the stated
interval. Translating its midpoint to zero gives the aperture. Exponentiating twice
that aperture gives the cutoff for `N≥1`.

For support `[0,1]`, the cutoff is `N exp w`; for support `[-1,1]`, it is `N exp(2w)`.
These are enclosing support bounds, not assertions of minimal support for arbitrary
profiles or coefficient vectors. Polynomial length alone omits this profile-width factor.
Nor does an aperture inclusion identify an arbitrary aperture witness with a fixed-profile
atomic test.

## Lean declarations

- `atomicTest_atomDilate_eq_zero_outside`
- `centered_atomicTest_eq_zero_outside_aperture`
- `profileAtomicAperture_eq_nominal_add`
- `exp_two_profileAtomicAperture`
- `plateau_aperture_cutoff`, `symmetric_profile_aperture_cutoff`

Direct `lake --old env lean` check and all three transitive axiom audits passed.
Only `propext`, `Classical.choice`, and `Quot.sound` occur. Umbrella import is wired.
