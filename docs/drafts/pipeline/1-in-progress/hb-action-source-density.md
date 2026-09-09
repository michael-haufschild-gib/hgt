# HB — Action pairing of the complete cubic Einstein source

Status: complete cubic/mixed bulk coefficients and local Einstein–Hilbert first variation formalized; physical endpoint action and extinction open.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

Hardest obstacle: prove extinction of the complete radiative causal pairing at the fixed Hawking clock. The proposed variational reduction must use the actual action pairing and its complete boundary contribution.

For the literal corrected metric path `g(t)=g0+t*h+t²*k+t³*l`, let `E(t)` be its covariant cosmological Einstein residual. The normalized volume factor is `v(t)=exp(log(det(g(t))/det(g0))/2)`, with its branch fixed at `v(0)=1`. For a fixed covariant testing tensor `M`, the bulk contraction uses

`W(t)=v(t)*g(t)^(-1)*M*(g(t)^(-1))^T`.

Write `Ej=E^(j)(0)/j!`, `W0=W(0)`, and `W1=W'(0)`. On the vacuum background and an actual linearized solution, the exact cubic coefficient is

`sum_ij W0_ij E3_ij + sum_ij W1_ij E2_ij`.

Thus changing the metric-dependent pairing contributes the **complete quadratic residual**, including `Lk`, to the cubic coefficient. Only the full second-order equation removes this term. An angular-component cancellation alone does not justify its removal. The determinant and both inverse-metric variations must be differentiated in the same path.

The [formal bulk audit](../3-formalized/hb-action-source-density.md) proves the complete relation, including the determinant derivative, both index-raising terms, and specialization to both literal fundamental BM branches. Three leaves and 23 new public declarations passed individual builds and new-only axiom checks.

After the full quadratic equation is solved, the varying bulk weight supplies no additional cancellation: its contribution is exactly zero. This calculation does not establish an Einstein action variation formula, integrated cyclicity, physical adjoint admission, boundary-current extinction, or RH.

The [formal mixed-coefficient audit](../3-formalized/hb-mixed-action-source-coefficient.md) proves

`P_ppm = <W0,E3_ppm> + <W1(p),E2_pm> + <W1(m),E2_pp>`.

Here `E2_pp=L k_pp+B(p,p)/2`, `E2_pm=L k_pm+B(p,m)`, and `E3_ppm=L l_ppm+B(p,k_pm)+B(m,k_pp)+C(p,p,m)/2`. The source definitions retain all correction slots; actual differentiation selects the displayed ones. Vanishing of these two complete quadratic grades suffices to remove the varying-weight terms. All 16 tensor components are required; the `--` correction and other cubic slots remain unrestricted apart from regularity. The linear cubic residual remains present.

Both original BM branches discharge the full linearized-equation premises. The affine literal specialization also discharges all regularity premises and retains the direct cubic term plus both quadratic weight contractions. Four additional leaves and 14 new public declarations passed individual builds and new-only axiom checks.

The [formal action-current audit](../3-formalized/hb-einstein-action-boundary-current.md) proves the local identity
`δ[v(R-2Λ)] = -<raised h,Einstein+Λg> + sum_a ∂_a[ν_x V^a](x)`,
with `V^a=g^{ij}δΓ^a_ji-g^{ia}δΓ^u_ui` and `ν_x(y)=exp(log(det(g(y))/det(g(x)))/2)`. The reference point is fixed during spatial differentiation. Metric compatibility, the determinant trace formula, and every actual spatial derivative are derived from the original contractions. The connection-trace volume term remains in the divergence. Complete field-jet linearity identifies this with the density formed from the actual affine field.

The literal BM specialization retains the complete original source and an independent literal testing field, discharging all regularity and symmetry premises in a nondegenerate amplitude neighborhood at each exterior point. No field equation is assumed. Six leaves and 21 new public declarations passed individual builds and new-only axiom checks.

The remaining direct attack is the physical Green-current identity and its contribution to the complete radiative pairing. A common physical volume normalization, domain reaching both endpoints, boundary-counterterm variations, and actual horizon/AdS limits remain required. The pointwise amplitude neighborhood supplies none of these automatically. Neither the current's physical cancellation nor fixed-clock extinction is proved.

The active attack is the [direct source-period conjecture loop](hb-radiative-source-period-attack.md). General Green-current development is paused unless a specific source-level proof requires it. The full tensor causal pairing and its fixed-clock extinction remain the target; no zero-current, correction-equation, or endpoint-cancellation premise may substitute for deriving them.
