# HB FH: global polar identity for the original horizon cap

Target: full temporal/metric/left-QNM matching. RH and full matching remain open.
FG proves absolute admission of the original two-arm plane integrand and its
pointwise radial density. The global change of variables remains to be proved.

[BRIDGE] The original fixed-radius horizon cap equals its absolutely admitted
fixed-plane integral, including both characteristic arms, complete source,
original squared amplitude and normalization.

Analytical coordinate choice derived from `NativeCircleChart`: set
`u=x/y`, `v=(x^2+y^2-1)/(2y)`, `E=sqrt(1+u^2+v^2)`, `L=E-v>0`.
The inverse is `(x,y)=(u/L,1/L)`. This is a global chart from the entire
Euclidean plane to the positive-height plane; its Jacobian is `1/(E L^2)`.
Multiplication by the original hyperbolic density `y^-2=L^2` leaves `1/E`.
The actual native circle becomes `(u,v)=(sinh(d) sin(theta),sinh(d) cos(theta))`.
Euclidean polar measure contributes `r dr dtheta`; substituting `r=sinh(d)`
gives `sinh(d) dd dtheta` because `E=cosh(d)` and `dr=cosh(d)dd`.
Translation and positive dilation carry the formula from i to the original
target `X+i exp(k)`, preserving `dx dy/y^2`. FG's pointwise density and
absolute admission then justify Fubini and the fixed-arm identification.

Formal status: under construction. The hyperboloid chart is an integration
coordinate change, not a new field or clock. Parameter differentiation and
physical left-QNM pairing remain separate even after this bridge is proved.
Frontier map is read-only. No computations are used.

Broad arXiv hyperboloid/disintegration search found Namazi,
[arXiv:2607.29319](https://arxiv.org/abs/2607.29319), July 2026: frame-flow
resolvent estimates on closed hyperbolic manifolds. Its abstract does not
provide this noncompact source-specific change of variables; no theorem from
that paper is assumed.
