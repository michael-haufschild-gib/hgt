# Absolute-mass continuity of actual separated cross terms

Status: formalized, individually checked, and wired.

## Proved statements

For arbitrary continuous compactly supported real profiles `f,g`, the actual
autocorrelations obey

```
L1(bumpAutocorr(f)-bumpAutocorr(g))
  <= L1(f-g)*(L1(f)+L1(g)).
```

If both profiles are supported in `[0,w]` and `s>w`, then

```
abs(atomCrossTerm(f,s)-atomCrossTerm(g,s))
  <= archLevyDensity(s-w)*L1(f-g)*(L1(f)+L1(g)).
```

Both statements retain arbitrary profile signs. No positive square mass or
smoothness beyond continuity is required.

## Mechanism

The difference of the autocorrelation integrands factors as
`(f-g)(u)*f(u+z)+g(u)*(f-g)(u+z)`. Compact support gives an integrable
product envelope, so Fubini and translation invariance yield the absolute
mass bound. The actual separated cross integral equals the full shifted
density integral. On its support the density is at most
`archLevyDensity(s-w)`; multiplying the already integrable difference proves
the second estimate.

## Lean closure

`TheSeparatedCrossTermIsContinuousInAbsoluteMass.lean` contains
`integral_abs_bumpAutocorr_sub_le`,
`atomCrossTerm_eq_full_shift_integral`, and
`abs_atomCrossTerm_sub_le_absolute_mass`.

Final individual no-output-file check3265 passed clean. Both printed capstone
dependency lists contain only `propext`, `Classical.choice`, and `Quot.sound`.
The module is imported by the programme umbrella. No full or umbrella build
was run.

## Boundary

The normalized dilation-width estimate and the proposed whole-form payment
`C_phi*(c-1)*(D_N+mass)` remain unproved. They are recorded as conjectural
extensions on `0-backlog/cact-successor-correction-beyond-touching.md`.
No completed paper proof of either transfer is claimed. Genuine adjacent
overlap requires the cancelled mixed Robin calculus; the separated density
bound above does not extend across its singular boundary.
