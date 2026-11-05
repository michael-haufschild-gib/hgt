# The complete Weil form controls both collars and the kernel increment

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** In a fixed enclosing precontact aperture, the full Weil energy controls both physical collar masses with leading coefficient `log(1/h)`. The actual kernel increment is bounded by the complete residual masses on those collars.

## Exact bounds

Let `B_c` be the complete bounded Weil remainder, `A_c` the logarithmic
adjustment, and `λ>0` the ground energy of the old aperture `a`. Set
`C=2π+‖B_c‖`, `D=‖B_c-A_c‖`, and `E=D+C+2C²/λ`. For `0<h≤1`, every actual source supported in
`[-a-h,a+h]` has an exact sharp decomposition `u=r+l+ιp`, with `p` in the
old space, satisfying

`(log(1/h)-E)(‖l‖₂²+‖r‖₂²) ≤ ‖u‖²_Weil`.

For `b=a+h≤c`, the actual evaluation increment `δ_ab(z)` obeys

`(log(1/h)-E)‖δ_ab(z)‖²_Weil ≤ ‖1_(0,h]F⁻_ac(z)‖₂² + ‖1_(0,h]F⁺_ac(z)‖₂²`,

where `F⁻_ac,F⁺_ac` are the actual complete left and right residuals in
fixed enclosure `c`.

## Proof

The complete Weil form is the positive logarithmic form plus the bounded
physical operator `B_c-A_c`. Thus each collar costs at least
`(log(1/h)-D)` times its mass; constant interval tests have the matching
upper bound `h(log(1/h)+3+D)` and belong to the complete domain.

All three crossings have physical bound `C`. If `x,y,z` are the old, left,
and right physical norms, subtracting the proposed floor from the full
lower bound gives

`((λx-C(y+z))²+(λC+C²)(y-z)²)/λ ≥ 0`.

Sharp interval restriction supplies the decomposition for every supported
source. Apply it to the actual increment included into `c`. Orthogonality
eliminates its old-space pairing. The exact collar equations and Cauchy–Schwarz
give `e²≤mf`, where `e` is its squared Weil norm, `m` is total collar mass,
and `f` is total restricted residual mass. The floor gives `km≤e`, hence
`ke≤f` for `k>0`; for `k≤0` the same bound is immediate.

## Lean

All modules belong to `CanonicalSystemOfTheWindowTower`.

| Module | Main declarations |
|---|---|
| `TheWeilFormRetainsLogarithmicCollarEnergy` | `ccmWeilForm_eq_logarithmic_add_correction`, `ccmWeilForm_ge_log_inverse_width`, `exists_ccm_form_of_intervalSource`, `ccmWeilForm_intervalSource_upper` |
| `TheFullWeilFormControlsBothCollars` | `WeilHilbertBeforeContact.twoCollar_energy_floor`, `WeilHilbertBeforeContact.exists_twoCollar_decomposition_with_floor` |
| `TheWeilKernelIncrementHasItsCollarEnergyBound` | `WeilHilbertBeforeContact.norm_increment_sq_mul_collar_floor_le` |

Plain Lean audits pass. Printed main dependencies contain only
`propext`, `Classical.choice`, and `Quot.sound`.
