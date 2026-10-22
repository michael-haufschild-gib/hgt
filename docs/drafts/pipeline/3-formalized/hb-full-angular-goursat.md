# Full angular and original onset-pulse Goursat equations

Status: formalized; scratch checks, exact-module build and all five new public theorem axiom audits passed. Complete physical pulse/current pairing and RH remain unproved.

Lean module: `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFullAngularGoursat`.
Namespace: `RHTower.D4BMFullAngularGoursat`.

Chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

## Characteristic derivative

Let `H` be the constructed full angular response, `Q` the original theta half-square, `alpha = parameter q branch`, and `h(d), m(d)` their actual hyperbolic circle means at `z0=(X,exp k)`. The existing full equation is

`(sinh d)^2 h″(d) + sinh d cosh d h′(d) = (sinh d)^2 alpha (h(d)+m(d))`.

The full mean is smooth and its forcing continuous on the entire radial line. Cancel one `sinh d` away from zero and take the limit at zero to obtain `h′(0)=0`. Divide by `sinh d` again, using the derivative's slope limit, to obtain

`h″(0) = alpha (H(z0)+Q(z0))/2`.

The actual derivative of `h(arcosh z)` for `z>1` is `h′(arcosh z)/sinh(arcosh z)`. Its right limit at one is the displayed second radial derivative. The within-set derivative theorem then gives the actual derivative on `[1,infinity)` at one. No differentiable continuation below the physical invariant interval is assumed.

For the fixed onset coefficients `C_H, C_Q`, the original pulse's right derivative is exactly

`C_H alpha (H+Q)/2 + C_Q Delta Q/2`.

Both coefficients retain the original transition derivative and exponential clock.

## Closed causal cone

For the existing invariant put

`Z_y(u,v) = invariant((u+v)/2, y+(u-v)/2, y)`.

The explicit factorization is

`Z_y(u,v) = 1 + 2 sinh(u/2) sinh(v/2)/(cosh(y+(u-v)/2) cosh y)`.

Thus `Z>=1` on the closed nonnegative null quadrant and `Z>1` in its interior. The null derivative of `Z` vanishes on its corresponding characteristic axis. Multiplying by the finite angular derivative limit therefore gives zero null-axis current. The interior mixed derivative is the literal forcing divided by `4 cosh(y+(u-v)/2)^2`.

Continuous extensions through `arcosh(max(1,Z))` justify finite integration. They are removed everywhere on the admitted causal cone. One fundamental-theorem identity integrates the mixed derivative from its zero axis limit; a second integrates the remaining first derivative from the original datum `H(z0)`. Consequently the existing full kernel `K_H` obeys, for every original causal point `(h,x,y)`,

`K_H(h,x,y) = H(z0) + integral_0^(h+x-y) integral_0^(h-x+y) alpha (K_H+K_Q)((a+b)/2,y+(a-b)/2,y)/(4 cosh(y+(a-b)/2)^2) db da`.

The theorem includes both characteristic axes and their intersection. `K_Q` is the already constructed original native theta-source kernel.

## Original pulse

Define `C(h,x,y)` as the displayed double integral in the original direct causal support and zero outside it. Apply the identity separately to the existing direct and image terms. The existing full angular Dirichlet kernel is its gated datum difference divided by two plus `(C(h,x,y)-C(h,x,-y))/2`.

Linearity of the existing pulse kernel, followed by the already proved native `Q` Volterra identity, gives its original pulse vertex plus

`C_H (C(h,x,y)-C(h,x,-y))/2 + C_Q (C_Qnative(h,x,y)-C_Qnative(h,x,-y))/2`.

Here `C_Qnative` denotes the existing native angular correction, not the onset coefficient. The original reflection sign, two causal gates, factor one half, full angular datum, half-square source and clock are preserved. The statement is an identity for the already defined pulse kernel; it introduces no replacement response or vanishing premise.

## Public API

| Theorem | Content |
|---|---|
| `fullAngularKernel_right_derivative` | Actual full angular characteristic derivative |
| `onsetAngularKernel_right_derivative` | Both original pulse characteristic channels |
| `fullAngularRiemannKernel_goursat` | Literal forced equation on the whole closed cone |
| `fullAngularDirichletKernel_volterra` | Existing direct/image full angular kernel |
| `onsetDirichletKernel_volterra` | Existing pulse kernel with its actual source vertex |

`fullAngularCorrection` is the one new public definition.

## Remaining physical step

The dependent target is formation and evaluation of the original pulse's time/source convolution, then its signed current with the incoming wave image, both cross terms and every physical face. The exact target and the nonzero AdS pulse trace that governs source-integral admission are recorded in the [analytical card](../1-in-progress/hb-onset-pulse-green-action.md). Kernel characteristic matching and the Volterra identity do not by themselves establish extinction.

## Search evidence

Independent broad corpus terms included `transversal`, `Darboux Goursat` with OR matching, and `backstepping`, alongside a deep mechanism query about regular-singular radial derivatives and causal Volterra integration. Candidate declarations, source-method arguments and proposed ingredient groups were inspected. Searches reported partial source and semantic coverage; candidates were source-only and some stale. The relevant actual mechanisms were checked from the existing native characteristic and Goursat sources and then instantiated in the new Lean proof. Proposed search groups were not treated as proved facts. Broad external backstepping leads are separated from the proof in the analytical card.

## Validation

Foreground scratch checks used `lake env lean`. Final `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFullAngularGoursat` passed without warnings: two jobs, 323 seconds, with only this new module reported built. The isolated audit reused 3,994 cached project modules and installed dependency caches; no dependency, full-project or umbrella build ran.

All five new public theorem axiom reports contain exactly `propext`, `Classical.choice` and `Quot.sound`. No existing theorem axiom audit was repeated. Source and all five installed build artifacts match the audited files byte for byte. The new module is wired once into `RHTower.lean`.

Source SHA-256: `2be351569394318dc60e450411b036911aca521616852c7a2c39aabac6594d99`.

The corpus index refresh ran once: four changed files, zero removed. All six new public API rows, the unique umbrella import and local document links were verified. Repository-wide `scripts/formal_tools.py lint` reported an unrelated module unreachable from its theorem-area umbrella: `GaloisForLFunctions.RHTower.ChronologicalTailTransform`; existing large-file warnings were also reported. The new module is reachable. This global lint result does not invalidate its successful exact-module build or axiom audit.

All owned Lean/Lake and search processes terminated. The isolated audit workspace, scratch files, four search-result files and lint capture were removed. No computations, Git commands, launcher commands, full builds or umbrella builds ran. The frontier map and universal `STATUS.md` were not edited.
