# Strict eighth theta section

- **ID:** theta-cusp-strict-eighth-section
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Wall:** Σ6
- **Statement:** The actual signed center-mixed theta Hankel matrix of size eight is positive definite for every `0 < a < 1/2`; its seventh successor integral is strictly positive.

## Mechanism

The even block is a principal block of the strict seventh section. For the odd block, write its quadratic form as `∫ r sinh(ar) F_v(r) dr`. The existing seam certificate gives `∫ r² min(F_v,0)` below `r_c=log(5/π)`, plus `∫ r²F_v` above it, nonnegative. Above `log(6/π)`, the native first-atom estimate bounds `F_v` below by a positive multiple of the squared norm of invertible central coordinates.

For nonzero `v`, retain the difference between the aperture integrand and `sinh(a r_c)/r_c` times the seam integrand. It is nonnegative everywhere and strictly positive on an interval beyond `log(6/π)`, because `sinh(ar)/r` is strictly increasing. Its integral is positive. Thus the odd block is strict, and parity gives the full eighth section.

No new numerical certificate is required. All-order positivity remains open.

## Strictness

For `0 < y < Y`, put `d=Y−y`. The difference `y sinh Y−Y sinh y` equals
`y sinh y(cosh d−1) + y cosh y(sinh d−d) + d(y cosh y−sinh y)`, which is positive. Hence the aperture-weight comparison is strict above `r_c`.

The central-coordinate map is invertible. The existing bound `F_v(r) ≥ (8q f₁(r/2)²/24)‖coordinates(q,v)‖²` is therefore positive for nonzero `v` beyond scale six; the first theta atom is positive there. The nonnegative difference of the two integrable functions is positive on every interval in that ray, so its integral is positive. Adding the nonnegative seam integral proves the strict odd block. The strict even block and vanishing mixed-parity entries prove rank eight. The determinant Schur identity at the strict rank-seven head gives `I₇(a)>0`.

## Lean certificate

Source: `formal/GaloisForLFunctions/ThetaCuspSections/StrictEighthSection.lean`.
Namespace `GaloisForLFunctions.ThetaCuspSections`:

- `oddFour_fibre_pos_of_log_six`: strict native odd tail.
- `thetaCuspCenterMixedOddFour_posDef`: strict integrated odd block.
- `thetaCuspCenterMixedSignedHankel_eight_posDef`: strict eighth section.
- `thetaCuspNativeSuccessorIntegral_seven_pos`: strict successor integral.

Direct `lake --old env lean` check passed with default limits. All four transitive axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`. The programme umbrella and `MainTheorems.lean` import the result; neither umbrella was compiled.

Rank nine still requires the sign of the native successor integral at order eight. This result removes the rank-eight radical and does not prove the all-order hierarchy.
