# HB seam-crossing distribution equation

Stage: formalized in Lean 4; leaf and axiom audits passed. Type: `[BRIDGE]`. RH remains open.

Chain: literal theta cusp → Xi occurrence → retained spin-two source → physical
causal response and left-QNM pairing → independent fixed Hawking-clock extinction → RH.

The actual full-forcing angular weak response satisfies a second-order modular
distribution equation against every smooth compact positive-height planar test.
Tests may cross either modular seam and contain elliptic fixed points. Both
derivatives are transferred to the actual test through the full completed energy
domain. No smooth representative or seam-trace hypothesis on the response is used.

## Compact quotient support and actual admission

Let P denote the full projective modular periodization. For every modular element
gamma and upper-half-plane point z, the literal Mobius height formula gives

`height(gamma*z) <= max(height(z), 1/height(z))`.

If the lower-left integral matrix entry vanishes, the lower-right entry has
absolute value at least one. Otherwise the squared denominator is at least y².
Applying this bound to inverse translates of a compact test support gives one
uniform upper height bound for every translate meeting that support. The closed
modular cell truncated at that height is compact: its real part lies between
-1/2 and 1/2, and its imaginary part is bounded below by 1/2.

Thus Pg has compact quotient support. Previously proved local finiteness,
smoothness and invariance make Pg an actual `CoreField`; its scalar and both
original weighted derivatives have the required L² membership. Its complete
graph is therefore an admitted energy-domain test. A nonnegative compact bump
equal to one at any chosen point gives `(Pg)(z).re >= 1`. This includes seams and
elliptic fixed points, with stabilizer multiplicities retained.

## Exact scalar and gradient unfolding

Proper discontinuity applied to the compact truncated cell and compact test
support proves that only finitely many test translates contribute anywhere on
the whole closed cell. It also proves summability of every orbit series. The
actual fundamental-domain integral theorem then gives exact scalar unfolding.

For the gradient, the original Mobius chart derivative is multiplication by
`j = 1/(cz+d)^2`. For any two real-linear complex-valued derivatives A and B,

`conj(A(j))*B(j) + conj(A(j*i))*B(j*i)`
`  = |j|² * (conj(A(1))*B(1) + conj(A(i))*B(i))`.

The height transformation cancels this squared Jacobian factor. Consequently the
full hyperbolic Dirichlet density

`E(g,h) = sum_i conj(y*partial_i g) * (y*partial_i h)`

is invariant under simultaneous modular pullback. A locally finite neighborhood
sum can be differentiated in full; every omitted translate and its derivative
vanish there. Against an invariant smooth core field k this proves

`E(Pg,k) = P(E(g,k))`,
`integral_cell E(Pg,k) dmu = integral_halfplane E(g,k) dmu`.

Compact support in the first argument supplies integrability of the full energy.
There is no interchange of an uncontrolled derivative, sum or integral.

## Green identity and graph completion

The exact pushforward of full hyperbolic volume is planar volume on positive
height with density y^-2. Squared height therefore cancels this density in the
literal integral. For compact planar g supported in positive height and arbitrary
chart-smooth k, planar integration by parts applies: differentiability of k is
needed only on the opposite compact test support. This gives

`integral_halfplane E(g,k) dmu`
`  = -integral_halfplane conj(Delta_H g)*k dmu`,

where `Delta_H g = y²*(partial_x² g + partial_y² g)`. All derivative tests retain
compact positive-height support. No modular side is removed and no side-boundary
term is discarded. Scalar unfolding of the Laplacian test gives the original
Hilbert identity

`sum_i <D_i(Pg),D_i k> = -<P(Delta_H g),k>`.

The difference is a continuous linear functional on the full value-plus-gradient
Hilbert space. It vanishes on every original core graph, hence on its linear span
and topological closure. Therefore the identity holds for every vector in the
actual completed energy domain, including the previously constructed weak
response h to the complete original forcing F.

Substituting it in the original variational equation yields

```
integral_cell conj(P(Delta_H g))*Jh dmu
  - L*integral_cell conj(Pg)*Jh dmu
  = integral_cell conj(Pg)*F dmu.
```

Here J is the original scalar projection, L the actual branch parameter, and F
the literal complete cusp-subtracted forcing. Every scalar and gradient vector
is identified with its native integral. The final actual-response theorems have
no additional response-regularity, test-admission or trace premises.

## Lean surface and validation

All modules below are under `GaloisForLFunctions.RHTower`.

| Module | New public theorems | Surface |
|---|---:|---|
| `ThetaCuspHawkingBMCompactModularPeriodization` | 4 | Orbit-height bound and compact quotient support |
| `ThetaCuspHawkingBMGlobalChartTests` | 5 | Actual energy admission and full seam-test variational equation |
| `ThetaCuspHawkingBMCompactTestUnfolding` | 6 | Finite translates, summability and scalar unfolding |
| `ThetaCuspHawkingBMGlobalChartTestSeparation` | 2 | Nonzero admitted tests at every point |
| `ThetaCuspHawkingBMModularDirichletCovariance` | 4 | Original Mobius derivative and invariant full energy |
| `ThetaCuspHawkingBMModularDirichletUnfolding` | 6 | Full differentiated periodization and energy unfolding |
| `ThetaCuspHawkingBMHalfPlaneGreen` | 5 | Full native measure transport and integration by parts |
| `ThetaCuspHawkingBMGlobalChartGreen` | 3 | Literal hyperbolic Laplacian and full Green identity |
| `ThetaCuspHawkingBMGlobalDistributionEquation` | 5 | Completed global Green identity and actual response equation |

All nine development files passed individual `lake env lean` checks with no
diagnostics. All nine canonical leaves passed individual `lake build <module>`
audits in a cache-only package, compiling exactly one new leaf per invocation.
Build times in table order were 3.1s, 18s, 14s, 15s, 11s, 5.5s, 8.3s, 4.9s and
5.6s. Audited source bytes match the canonical files. Exactly 18 new olean/ilean
artifacts are installed, and all nine leaves are wired once into their theorem-area
umbrella. No dependency, umbrella or full build ran.

One completed scratch `lake env lean` audit checked all 40 new public theorem
axiom sets, once. Every set contains only `propext`, `Classical.choice` and
`Quot.sound`. No older theorem batch was re-audited. There are no added axioms,
proof gaps or numerical certificates. Scoped source whitespace checks passed.
The source index was refreshed once. Final `lint --check-generated` reports three
unrelated modules unreachable from the RHTower umbrella:
`DivisorSmoothBlockOrientation`, `SquareBlockSqrtClockMoment` and
`SymmetricSqrtClockBounds`. It reports no errors in these nine new HB leaves.
Global lint is therefore not claimed to pass. Unrelated work is left intact.

## Remaining bridge

The equation above is a global modular distributional identity expressed through
periodized chart tests and native quotient L² vectors. Its actual scalar lift,
local Sobolev identification and smooth reconstruction across seams and elliptic
points are formalized in
[globally smooth angular response](hb-global-smooth-angular-response.md).

Construct the global cusp-cutoff extension and assemble the full angular field.
Physical causal admission, horizon and radial boundary conditions, gauge
conditions, original left-QNM pairing, SS/VV sectors and independent fixed
Hawking-clock extinction remain open. This bridge does not prove RH. The frontier
map is read-only; no numerical experiment or computational certificate is used.
