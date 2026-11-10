# Green damping resolves the Weil operator

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Obstacle:** B133: passage from the saturated geometric Green form to its actual inverse.

## Statement

Fix a physical aperture. Write `J` for the complete Weil form embedding,
`B` for its literal bounded polar–prime remainder, and `c=‖B‖+1`.
For `0≤r<1`, define on physical L²

`A_r = ∫₀∞ K_r(t)(2I−U_t−U_{−t})dt + I+B+cI`,

with the jump operator compressed to the aperture. The integral is strong
on each L² vector. Then `A_r` is bounded, self-adjoint, and `A_r≥I`.
Its inverse `S_r` exists and satisfies `‖S_r g‖≤‖g‖`.
As `r↑1`, `S_r g` converges strongly to the actual shifted Weil covariance
`C g = J( I+J†BJ+cJ†J )⁻¹J†g`, for every physical L² source `g`.
Moreover,

`‖S_r g−Cg‖² ≤ Re⟨g,S_r g⟩−Re⟨g,Cg⟩`,

and the jump energies of `S_r g` converge to the critical jump energy of
`Cg`. No energy is lost through the moving-state limit.

## Proof [PROVED HERE]

The integral is bounded because `‖(2I−U_t−U_{−t})f‖≤4‖f‖` and
`K_r` is nonnegative and integrable. Unitarity gives its exact pairing
`∫₀∞ K_r(t)⟨(U_t−I)f,(U_t−I)h⟩dt`. Thus its diagonal is the
existing damped Green jump energy `G_r(f)`. The remainder estimate
`Re⟨Bf,f⟩≥−‖B‖‖f‖²` gives coercivity and hence the bounded inverse.

Put `x_r=S_r g` and `e_r=Re⟨g,x_r⟩`. For `r≤s`, expanding
`⟨A_r(x_r−x_s),x_r−x_s⟩` and using `A_r≤A_s` gives
`‖x_r−x_s‖²≤e_r−e_s`. The energies are nonnegative and decreasing.
Consequently `x_r` is Cauchy and converges strongly to some `x`.

Write `D(f)=‖f‖²+Re⟨Bf,f⟩+c‖f‖²`. This is continuous, and
`G_r(x_r)=e_r−D(x_r)→M=Re⟨g,x⟩−D(x)≥0`.
For each fixed `s<1`, continuity of `G_s` and `G_s(x_r)≤G_r(x_r)`
for all `r≥s` give `G_s(x)≤M`. The established extended Green limit
then gives `G_crit(x)≤M<∞`. Its exact domain characterization yields
`x=Ju` in the complete form domain, with shifted form energy
`Q(u)≤Re⟨g,x⟩`.

Let `v=(I+J†BJ+cJ†J)⁻¹J†g`, so `Jv=Cg`. Square completion at
`x_r` gives `2Re⟨g,Jv⟩−⟨A_rJv,Jv⟩≤e_r`.
The established full-domain Green limit and the Riesz equation yield
`Q(v)≤Re⟨g,x⟩`. That same equation gives
`Re Q(v,u)=Re⟨g,x⟩`. Hence
`Q(u−v)=Q(u)+Q(v)−2Re⟨g,x⟩≤0`.
Riesz coercivity forces `u=v`, proving the asserted strong limit.
Passing `s↑1` in the two-state estimate proves the error bound.
Finally `G_r(x_r)=e_r−D(x_r)` and the exact Riesz equation identify
its limit as `G_crit(Cg)`.

## Lean declarations

Module: `GaloisForLFunctions.HyperbolicArakelovTheory.TheGreenDampingResolvesTheWeilOperator`.
Namespace: `GaloisForLFunctions.HyperbolicArakelovTheory`.

- `greenJumpOperator_pair`: literal integrated translation-loss pairing.
- `greenWeilPrecision_quadratic`: exact saturated Green energy and coercive shift.
- `precision_resolvent`, `resolvent_precision`: two-sided bounded inverse identities.
- `tendsto_greenWeilResolvent`: strong convergence to `ccmRestrictedWeilCovariance`.
- `greenWeilResolvent_error_sq_le`: squared physical error bounded by the inverse-energy gap.
- `tendsto_greenWeilResolvent_jumpEnergy`: convergence of the moving damped jump energy.

Plain `lake --old env lean` audit passes without warnings. All seven declarations above
have exactly the standard axioms `[propext, Classical.choice, Quot.sound]`.

## Boundary

This is an aperturewise result for the saturated arithmetic Green form,
with its separate polar and prime terms and an explicit coercive shift.
It assumes no positivity of the unshifted Weil form. It does not identify
one invariant adelic torus Robin kernel with Weil's diagonal and does not
assert norm resolvent convergence or an aperture-independent global shift.
