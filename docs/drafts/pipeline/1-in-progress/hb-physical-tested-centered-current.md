# HB: original physical scalar-tested centered current

- **ID:** HB-QTCC
- **Stage:** 1-in-progress
- **Parent:** [Complete response cusp current](../3-formalized/hb-full-response-cusp-current.md)
- **Route:** Literal theta source → Xi occurrence → retained spin two → physical causal/left-QNM action → common Hawking-clock extinction → RH

Last verified progress: the original complete incoming cusp current now has
an exact full-mean/contact/nonconstant decomposition. Its last term vanishes
under every complex height weight, including the original physical scalar
principal factor. The full scalar test remains to be attached. No complete
physical-clock extinction or RH theorem is proved.

## Hard source target and proof mechanism

Put U_b=R_b-M R_b, G_b=F_b-M F_b and let T be the actual physical scalar
test. The established source equations give
`U_b,yy=-U_b,xx+alpha_b*U_b/y^2+G_b/y^2`. For
`L_ab=M[T*U_a,y*U_b]`, periodic integration by parts gives the candidate
identity

```
L_ab' = M[T_y*U_a,y*U_b] + M[T*U_a,y*U_b,y]
      + M[T*U_a,x*U_b,x] + M[T_x*U_a,x*U_b]
      + alpha_a/y^2*M[T*U_a*U_b] + 1/y^2*M[T*G_a*U_b].
```

All six terms must be retained. No conjugation enters this bilinear identity.
Bounds for T,T_x,T_y by a fixed height power turn Cauchy--Schwarz into a
majorant using the already admitted E_a,E_b, rapid U_a,U_b masses and the
source forcing mass. Taking a sufficiently larger polynomial weight gives
both `y^N L_ab` and its derivative in L1. The same W1,1 upper-trace theorem
used for the native current would then prove its zero limit. This is a paper
proof mechanism with source interfaces still to be attached in Lean, not a
completed tested-current theorem.

The linear terms `M[T*U_b]` and `M[T*U_a,y]` must be treated as well when
expanding H_b=M H_b+U_b. The former is bounded directly by the rapid U_b
mass; the latter has an analogous differentiated source identity. Products
with the original full response means require their source-derived height
growth bounds. Replacing T by T*Q handles the derivative-response source
contacts, while `M[T*Q*Q_y]` is a purely literal source-jet contribution.
These steps would identify the full tested upper trace, not cancel its
remaining mean/contact principal terms or its finite lower endpoint.

The focused deep tail/derivative search completed retrieval with 57,202
inventoried files, pending compiler metadata and unmeasured semantic coverage.
It found actual `weighted_tail_bounded`, `tail_vertical_bounded`,
`scalarTail_power_response_integrable` and the forced angular-covector
equation. The suggested zero-delay primitive is radial and does not establish
this angular product identity. The derivative-stable signed Fourier family
and square-source jet bounds supply the applicable source methods.
