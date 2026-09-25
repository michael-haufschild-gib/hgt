# Actual BM quadratic angular source

RunPod exact symbolic calculation completed in 9.91 seconds with three workers
(SymPy 1.13.3). All sixteen background and sixteen first-order Ricci equations passed
in each of SS, VV and S+V: 96 checks. An initial Python 3.8 compatibility failure
preceded the calculation; replacing `functools.cache` with `lru_cache(maxsize=None)`
fixed it without changing the protocol. Its log is retained.

Let `H=(S Hess_gamma S)_TF`, `G=(dS tensor dS)_TF`, and let rotation act on a
trace-free symmetric tensor by `(Txx-Tyy,Txy) -> (2Txy,-(Txx-Tyy)/2)` in the
oriented conformal chart. For the actual fundamental scalar and coexact-vector
metric fields, the computed epsilon² angular trace-free Einstein residual is

`B² [aS² C(2H+G) + aS*aV F rotation(H+G) + aV² D G]`,

where

```
C = s² ((s+1)²-4r²)/(8r⁴)
D = s² (3s²+12s+11)/(2r⁴)
F = s² (s+1)/r³.
```

The script evaluates y=1 and B=1 after taking the full coordinate derivatives.
The covariant all-y form above is a derived theorem candidate, not a computational
conclusion. Its proof must establish the coordinate transformation or verify the
all-y identity directly.

The SS formula also has an independent hand derivation: the temporal/radial
matrix has zero background trace. Its squared trace is
`s²((s+1)²-4r²)/(2r⁴)`. The block metric Ricci formula then gives
`B² C(2H+G)`. The unexpected simplifications concern the other channels:
all second and third scalar angular derivatives cancel in VV, and SV is
`F/2` times the rotated trace-free Hessian of `S²`.

This changes the source-reduction problem concretely. The three radial coefficients
have different r dependence. The mixed source is an angular derivative, so its
paired reduction requires integration by parts with the actual left test and its
boundary terms. Neither deleting it nor replacing all channels by one scalar
mixing amplitude is justified by this calculation. The scalar metric boundary
forcing remains present.

This is a local source evaluation. It does not establish a gauge-invariant
Teukolsky projection, a retarded/advanced response, a left-QNM pairing, or fixed-clock
extinction. It is not evidence admitted into a Lean proof.

The [independent Lean proof](../../3-formalized/hb-quadratic-angular-source-and-correction.md)
now establishes the exact source at arbitrary complex height on the nondegenerate
chart. It also constructs a particular second-order angular correction and proves
that the actual corrected source has remainder `B²*(aV²*D-aS²*C)*G`. The three
new leaves passed targeted final builds; all fourteen new public theorems use only
the standard Lean axioms. Physical admission of the correction, its other Einstein
components, and the actual causal left pairing remain open.
