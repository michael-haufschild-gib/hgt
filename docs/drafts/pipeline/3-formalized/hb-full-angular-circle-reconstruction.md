# HB: reconstruction of the full angular and onset circular kernels

Status: formalized. The complete physical pulse convolution, mixed action and RH remain open.

Chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

Owner: [ThetaCuspHawkingBMFullAngularCircleReconstruction.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMFullAngularCircleReconstruction.lean), namespace `RHTower.D4BMFullAngularReconstruction`.

For either actual Xi branch, put `s=physicalRate q branch`, `alpha=(2s+1)(2s+2)`, `p(d)=legendreKernel (2s+1) (cosh d)`. Write `h(d)` for the original full angular circle mean and `m(d)` for the literal half-square mean. The new closed reconstruction is

```
h(D) = p(D) [H(z) + integral_0^D K(u) du],
K(u) = alpha [integral_0^u sinh a p(a) m(a) da] / [sinh u p(u)^2].
```

It holds for every finite nonnegative radius. The source density `K` contains no unknown angular response. Its interval integrability, including the origin, is proved.

The key step is nonvanishing of the original Legendre kernel. Its actual ODE gives

```
(Z^2-1) Im(conj(P(Z)) P'(Z)) = Im(alpha) integral_1^Z |P(z)|^2 dz.
```

The existing physical parameter theorem proves `Im(alpha) != 0` on both Xi branches without a critical-line assumption. Since `P(1)=1`, the integral is strictly positive for `Z>1`; consequently `P(Z)` cannot vanish for `Z>=1`. Thus `p` is smooth and nonzero at every real radius. The previously proved circular Green identity determines `(h/p)'=K` at positive radius. Smoothness of `h/p` admits `K` on the whole interval, and the fundamental theorem retains the exact initial value `H(z)`.

Substitute `D=arcosh(invariant(h,x,y))` within each original causal gate. The full angular circular kernel splits into the homogeneous physical Legendre kernel times `H(z)` plus the literal-source correction. For the unchanged onset coefficients `C_H` and `C_Q`, its direct/image circular kernel is exactly

```
C_H homogeneousDirichletKernel H(z)
  + C_H sourceDirichletCorrection
  + C_Q nativeDirichletCausalKernel(Q).
```

Both gates, reflection `y -> -y`, the factor `1/2`, and the original onset derivative and clock remain intact. This theorem identifies the circular kernels pointwise. The full-angular kernel's [original wave action](hb-full-angular-circle-action.md) is separately formalized. Subsequent physical convolution and current evaluation remain open; this result does not assign the retained characteristic datum to zero.

## Public proof API

| Theorem | Content |
|---|---|
| `radialLegendre_smooth` | Actual physical radial kernel is smooth |
| `radialLegendre_ne_zero` | Nonvanishing on both actual Xi branches |
| `sourceDensity_intervalIntegrable` | Literal-source nested density is integrable through radius zero |
| `angularMean_reconstruction` | Full angular mean from its original datum and literal source |
| `angularDirichletKernel_reconstruction` | Original direct/image angular kernel decomposition |
| `onsetDirichletKernel_reconstruction` | Exact unprojected onset circular kernel reconstruction |

## Validation

Foreground scratch checks used `lake env lean`. Final `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullAngularCircleReconstruction` passed without warnings: two jobs, 252 seconds, in an isolated audit using 3,992 cached project dependencies and 12 local dependency stubs. No dependency or umbrella build ran. All six new public theorem axiom reports contain exactly `propext`, `Classical.choice`, and `Quot.sound`. Source and five installed build artifacts match the audited files byte for byte. The module is wired once into `RHTower.lean`.

Source SHA-256: `f7ab17cd0f54835122ad862a7de61da762f6140cae0ce5cdb6499ab6543588d4`.

The corpus index refreshed once (10 changed files, zero removed). All 12 new public API rows, the unique umbrella import, final local document links and installed artifacts were verified. Repository-wide `scripts/formal_tools.py lint` passed after unrelated concurrent umbrella additions settled; existing large-file warnings remain. All owned Lean/Lake processes terminated, and the shared isolated audit, scratch files and five search-result files were removed. The [analytical card](../1-in-progress/hb-onset-pulse-green-action.md) records the paper derivation and remaining causal-pairing target. The frontier map and universal `STATUS.md` were not edited.
