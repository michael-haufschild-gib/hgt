# The zero-aperture anchor of the precontact kernel

- **ID:** precontact-kernel-zero-aperture-anchor
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Wall:** Σ75; Σ35.
- **Statement:** The finite evaluation Grams extend continuously by zero at aperture zero, are absolutely continuous on every `[0,b]` strictly before contact, and equal the integral of their endpoint trace energy from zero.

## Anchor and integral reconstruction

Fix a strictly precontact enclosure `c`. For `0<a≤c`, physical
Cauchy–Schwarz and the ground-energy floor in `c` give

`μ(c) K_a(z,z) ≤ 2a exp(2c |Im z|)`.

Indeed, `K_a=eval_a(z,E_a)`, the physical source is supported in `[-a,a]`,
and isometric inclusion gives `μ(c)‖E_a‖²_L²≤K_a`. Squaring the Fourier
integral bound and cancelling the positive `K_a` gives the estimate.
Finite Gram Cauchy–Schwarz then gives the zero limit for every fixed frame.
Monotonicity makes the ordinary derivative integrable on `[0,b]`. The
precontact right trace derivative agrees with it almost everywhere.
Continuity at zero and the one-sided fundamental theorem then identify
every increment from zero with its trace integral. Absolute continuity of
that integral transfers to the Gram function.

The literal bounds are `norm_suzukiCompactL2Fourier_le` and
`integral_norm_suzukiCutoff_sq_le`; the latter has the exact factor `2a`.

## Formal results

Module `CanonicalSystemOfTheWindowTower/TheWeilKernelVanishesAtZeroAperture`,
wired into the programme umbrella:

- `WeilHilbertBeforeContact.groundEnergy_mul_kernel_le_aperture`: the exact fixed-enclosure bound above.
- `CriticalHardyTheoryOfTheWindowCone.groundEnergy_mul_evalGram_le_aperture`: its finite-frame version.
- `continuousWithinAt_evalGram_zero_aperture`: right continuity at zero.
- `integral_evalGramEndpointEnergy_from_zero`: integrability and exact reconstruction from zero.
- `absolutelyContinuousOnInterval_evalGram_from_zero`: absolute continuity on `[0,b]`.

The final source check used `lake --old env lean` without output artifacts.
All five printed transitive axiom audits contain only `propext`,
`Classical.choice`, and `Quot.sound`. No contact-uniform estimate is asserted.
