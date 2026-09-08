# HB native cusp spectral ray

- **ID:** hb-native-cusp-spectral-ray
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), `[BRIDGE]`
- **Source:** [cusp spectrum and causal continuation](../1-in-progress/hb-cusp-spectrum-and-causal-continuation.md)
- **Statement:** The original modular energy operator has explicitly constructed unit approximate eigenvectors at every `lambda=5/4+tau²`, and no bounded left inverse at any real `lambda>=5/4`.

RH remains open. Chain: literal theta cusp → Xi occurrence → retained spin-two
source → original causal response and left-QNM pairing → independent
Hawking-clock extinction → RH.

## Construction and exact proof

Use the original smooth real window
`eta(x)=smoothTransition(x+1)-smoothTransition(x)`. Its derivatives are compactly
supported in `[-1,1]`. Let `A_j=integral eta^(j)(x)^2 dx`. Smooth compact support
proves each moment finite and nonnegative. The actual value `eta(0)=1` and
continuity prove `A_0>0`; no evaluated integral or numerical lower bound is used.

For `L>0`, set `R_L=log(2)+2L+1` and
`f_L(t)=exp(i*tau*t)*eta((t-R_L)/L)`. Its support is contained in
`[R_L-L,R_L+L]`, strictly inside `t>log(2)`. The previously constructed inverse
log-height transform therefore gives an actual vector `v_L=U f_L` in the
original operator domain. This retains full modular periodization and the
native hyperbolic measure; no model operator replaces the original `T=1-Delta_H`.

The exact intertwining `(T-lambda)U f=U((5/4-lambda)f-f'')` gives, at
`lambda=5/4+tau²`,

`(5/4-lambda)f_L-f_L'' = -exp(i*tau*t)*(2*i*tau*eta'(x)/L+eta''(x)/L²)`.

Both window derivatives are real. Their two complex coefficients are
perpendicular, so the mixed term cancels exactly. Translation and dilation of
the actual Lebesgue integral yield the native identities

`||v_L||² = L*A_0`,

`||(T-lambda)v_L||² = 4*tau²*A_1/L+A_2/L³`.

Normalize inside the actual operator domain by `u_L=||v_L||^(-1) v_L`.
Then `||u_L||=1` and

`||(T-lambda)u_L||² = (4*tau²*A_1/A_0)/L²+(A_2/A_0)/L⁴`.

The explicit sequence `L=n+1` has residual norm tending to zero, including
`tau=0`. A bounded left inverse R would give
`1<=||R||*||(T-lambda)u_L||`, contradicting that limit. Choosing
`tau=sqrt(lambda-5/4)` covers every real `lambda>=5/4`.

For doubled time rate `w=-3/2+i*tau`, the exact quadratic shift
`1-(w+1)(w+2)` equals `5/4+tau²`. The same original operator therefore has no
bounded left inverse at those shifts. This identity does not identify a
retarded convergence chamber or prescribe a continuation across that line.

## Positive content and scope

The positive construction is the actual unit approximate family, with exact
native residual costs and domain membership. The inverse obstruction follows
from that construction. No route is retired. No complete-spectrum equality,
essential-spectrum classification, source projection, radiation condition,
retarded-sheet identification, left-QNM extinction or RH is asserted.

In particular, failure of bounded inversion for arbitrary data does not imply
a singularity in the response to the particular full forcing. Computing its constant-mode
projection must retain the full principal–tail and tail–tail interactions and
the cutoff terms after the principal cusp subtraction. Their contribution
remains part of the source-continuation problem.

## Lean surface and audit

Modules are under `GaloisForLFunctions.RHTower`, with prefix
`ThetaCuspHawkingBM`; declaration namespace is `RHTower.D4BMModularCore`.

| Module suffix | New public theorems |
|---|---:|
| `CuspWindowMoments` | 6 |
| `CuspPacketProfile` | 5 |
| `CuspPacketDerivatives` | 2 |
| `CuspPacketNativeNorms` | 4 |
| `CuspPacketApproximation` | 4 |
| `CuspSpectralRay` | 3 |

The 24 public theorems close all claims above. In particular:
`cuspPacketVector_residual_norm_sq`, `cuspUnitPacket_residual_norm_sq`,
`cuspApproximateVector_norm`, `cuspApproximateVector_residual_tendsto`,
`energyOperator_cusp_ray_no_bounded_left_inverse` and
`energyOperator_critical_time_no_bounded_left_inverse`.

All six development scratch checks passed without diagnostics. Each exact
canonical leaf passed its final `lake build <module>` audit through an isolated
package using existing import caches; only the requested new leaf compiled.
The 12 new olean/ilean copies match the audited artifacts. All six imports are
wired once into the umbrella, without building it. A single scratch axiom audit
checked only the 24 new public theorems: `propext`, `Classical.choice` and
`Quot.sound` only. No previous theorem was re-audited. No computational
certificate, numerical experiment, dependency rebuild, full build or umbrella
build was used. The source index was refreshed and scoped whitespace/import
checks passed. `scripts/formal_tools.py lint --check-generated` reported one
unrelated concurrent module, `RHTower.DivisorContinuousUnitMoment`, unreachable
from its theorem-area umbrella, plus existing large-file warnings. That module
was already present before this work and was left untouched. The six new HB
modules have exactly one umbrella import each. Owned scratch files were removed;
no owned Lean/Lake process remains.
