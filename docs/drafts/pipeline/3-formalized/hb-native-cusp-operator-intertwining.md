# HB native cusp operator intertwining

Stage: formalized in Lean 4. Type: `[BRIDGE]`. RH remains open.

Chain: literal theta cusp → Xi occurrence → retained spin-two source → physical
causal response and left-QNM pairing → independent Hawking-clock extinction → RH.

Every smooth compact function f supported in `t>log(2)` now has a constructed
vector `U f` in the domain of the original modular energy operator `T=1-Delta_H`.
The construction proves both exact identities

`<U f,U g> = integral_(t>log(2)) conjugate(f(t))*g(t) dt`,

`(T-lambda) U f = U ((5/4-lambda)*f-f'')`.

The expression on the right is itself constructed as an admitted compact test.
Its native modular squared norm is exactly the flat squared norm of the displayed
residual. No operator-domain, coordinate-isometry, spectral or approximate-mode
premise is supplied to these final constructions.

## Actual operator domain

The existing completed Green identity holds against every vector in the full
modular energy completion. For an actual periodized compact planar test g it gives
`<g,v>_energy = <Jg-P(Delta_H g),Jv>_L2`. The adjoint of the actual embedding J
therefore sends `Jg-P(Delta_H g)` to g. The covariance `J J*` sends that vector
to `Jg`. Its original closed graph inverse is T, proving domain membership and
`T(Jg)=Jg-P(Delta_H g)`. This includes seam-crossing tests and every translate.

## Exact modular cusp construction

The horizontal window is
`eta(x)=smoothTransition(x+1)-smoothTransition(x)`.
It is smooth, supported in `[-1,1]`, and its integer translates sum to one on
the closed modular strip. Its three possible contributing second derivatives
sum to zero there. These are exact symbolic identities.

For a compact height profile h supported above 2, periodize
`eta(Re z)*h(Im z)` over the full projective modular group. Every nontranslation
term vanishes: its height is at most `1/Im z<2` on the original closed cell.
The remaining projective translations have a proved injective integer indexing.
Their full sum is exactly `h(Im z)`, including on both joined sides.

The planar generator is smooth and compactly supported in positive height, so
the operator-domain construction applies. Its Laplacian initially contains
both `y² eta''(x) h(y)` and `y² eta(x) h''(y)`. Only after full periodization
does the first term cancel. The resulting actual operator vector has the native
representative `h(y)-y² h''(y)`.

## Native measure and logarithmic coordinate

The original modular measure is transported to its literal planar density
`dx dy/y²`. Above height 2 the cell is the full width-one rectangle. The actual
pairing of two cusp vectors is therefore
`integral_(y>2) conjugate(h(y))*k(y)/y² dy`.

The proved substitution `y=exp(t)` and transform
`u(t)=exp(-t/2)*h(exp(t))` give the flat pairing. Differentiating twice gives

`exp(-t/2)*(h(exp(t))-exp(2t)*h''(exp(t))) = (5/4)*u(t)-u''(t)`.

Conversely, every compact smooth log-height test f is reconstructed by
`h(y)=exp(log(y)/2)*f(log(y))` for positive y and zero for nonpositive y.
Its compact support stays strictly above 2. The proof establishes smoothness
also through zero and recovers `u=f` exactly. Reconstructing the compact test
`(5/4-lambda)*f-f''` then proves the operator identity in the original Hilbert
space, rather than only a coordinate expression.

## Lean surface and audit

Modules are under `GaloisForLFunctions.RHTower`, with prefix
`ThetaCuspHawkingBM`; declaration namespace is `RHTower.D4BMModularCore`.

| Module suffix | New public theorems |
|---|---:|
| `OperatorCore` | 3 |
| `CuspPeriodization` | 8 |
| `CuspHeightTest` | 4 |
| `CuspWindowDifferential` | 4 |
| `CuspHeightOperator` | 3 |
| `CuspNativeIntegral` | 2 |
| `CuspLogCoordinate` | 3 |
| `CuspLogTest` | 4 |
| `CuspOperatorIntertwining` | 2 |

All nine development scratch checks passed without diagnostics. Each exact
canonical leaf passed its final `lake build <module>` audit, compiling only
that new leaf through an isolated package using existing import caches.
All 18 new olean/ilean artifacts match those audits, and all nine modules are
wired into the umbrella without building it. One scratch axiom audit checked
exactly these 33 new public theorems: only `propext`, `Classical.choice` and
`Quot.sound`. No previous theorem was re-audited. The source index was refreshed;
`scripts/formal_tools.py lint --check-generated` passed with existing large-file
warnings. Scoped whitespace checks passed. No full, dependency or umbrella build
was run.

## Remaining causal question

The operator and norm transfer needed for actual cusp wave packets is closed.
The [native cusp spectral ray](hb-native-cusp-spectral-ray.md) now constructs a
unit approximate family at `5/4+tau²`, proves its residual tends to zero, and
excludes bounded left inversion at every real `lambda>=5/4` in Lean.

That spectral result does not identify the original full forcing's projection,
its retarded continuation, or a homogeneous cusp radiation correction.
Those source and causal obligations, physical gauge, the original left-QNM
pairing, remaining response sectors and independent extinction remain open.
No route is retired. The frontier map is read-only. No numerical experiment or
computational certificate enters these proofs.
