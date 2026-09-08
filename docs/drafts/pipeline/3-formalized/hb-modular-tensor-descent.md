# HB modular tensor descent and quotient Einstein equation

Stage: formalized in Lean 4. Type: `[BRIDGE]`. RH remains open.

Chain: literal theta cusp → Xi occurrence → retained spin-two source → physical
causal response and left-QNM pairing → independent fixed Hawking-clock extinction → RH.

The actual constructed mixed metric, complete original mixed source and BM
background now obey the full modular tensor transformation law. Both endpoint
values obey the same law. The original coordinate differentials define an actual
group action on angular points and two spacetime tangent vectors. The metric,
source and actual Einstein variation have well-defined evaluations on its orbit
quotient, and the complete forced Einstein equation holds on every quotient
tangent pair. No covariance, source-equation or response-realization assumption is
supplied to the final construction.

## Coexact differentiation and the original Jacobian

For a smooth scalar f in the original upper-half-plane chart, define its coexact
differential on a real tangent vector represented by a complex number v as

`C_f(z,v)=d f_z(I*v)`.

The proved derivative of the original modular map A is multiplication by
`c_A(z)=1/(denom(A,z))²`. This multiplication commutes with the rotation I.
The actual chain rule therefore gives

`C_(f composed with A)(z,v)=C_f(Az,c_A(z)*v)`.

Scalar invariance gives the corresponding covector pullback law. The exact
angular coordinate identification shows that this chart differential is the
original coordinate covector evaluated as

`Re(v)*V_0 + Im(v)*V_1`, with `V=(partial_y f,-partial_x f)`.

No componentwise scalar invariance is assigned to derivative fields.

## Both original source channels are retained

The full angular response H is already smooth and invariant. Thus its actual
coexact covector A has the full pullback law. The literal half-square
`P=S²/2` is invariant, so its coexact covector J transforms by the same law.

The entire gradient-source scalar is
`G=y²*(Sx²+Sy²)`. Its smoothness follows from actual scalar derivatives.
The already proved identity `Delta P=2(s+1)(s+2)P+G`, together with the
actual modular Laplacian covariance, proves that G is invariant. Since
`coexact(G)=2K`, the complete original gradient-source covector K also
transforms with the same Jacobian. This retains all scalar terms and derivatives.

## Four-dimensional geometry and tensor pullback

The actual coordinate map fixes time and radius and sends the angular point z
to Az. Its full real differential is proved by differentiating that map. Its
complexification has the block matrix

`J_A=diag(I_2, [[Re(c_A),-Im(c_A)],[Im(c_A),Re(c_A)]])`.

Both differential factors occur in the tensor pullback
`J_A.transpose * M(Az) * J_A`. The original Möbius height law cancels exactly
against `normSq(c_A)`, proving background isometry.

The A/J covector laws prove this tensor law for the actual reconstructed mixed
metric. The J/K laws prove it separately for every original mixed-source
component. The radial coefficients, envelope and time dependence are retained.
The full ingoing inverse-radius metric and its exact horizon and radial boundary
values satisfy the same tensor law; the radial-angular boundary term remains
present.

## Actual quotient tangent geometry and forced equation

The identity differential is the identity map. The product differential law is
derived from the actual four-dimensional coordinate-map composition and
uniqueness of its Fréchet derivative. Thus

`(z,u,v) -> (Az,D_A(z)u,D_A(z)v)`

defines a proved SL(2,Z) group action on an angular point and two real
four-dimensional tangent vectors. Its orbit quotient identifies both vectors
with the point; all stabilizers are retained. This construction does not assume
that the quotient is a smooth manifold.

The actual bilinear tensor evaluation

`sum_(i,j) u_i*M_ij*v_j`

commutes with the displayed two-index pullback. Consequently the original
background, constructed metric and full original source have well-defined
evaluations on this same tangent-pair quotient. Their values on every lifted
representative equal the original expressions.

At each exterior radius, the Einstein tensor used here is literally
`Linearization.cosmological(backgroundJet,ofMetricField(forcedMetricField),-3)`.
The proved sixteen-component equation identifies this actual differential
tensor with the negative original source. It therefore descends through the
same group action. On every quotient tangent pair,

`quotientForcedEinstein + quotientMixedSource = 0`.

Both physical branches of every actual Xi occurrence are covered. The final
theorem takes an exterior radius as a subtype and supplies no field-equation,
inverse, modularity or critical-line premise.

## Lean surface and validation

Modules are under `GaloisForLFunctions.RHTower`; declaration namespace is
`RHTower.D4BMModularCore`.

| Module | New declared public theorems |
|---|---:|
| `ThetaCuspHawkingBMModularCoexact` | 5 |
| `ThetaCuspHawkingBMFullCovectorModular` | 6 |
| `ThetaCuspHawkingBMModularSpacetimeCoordinates` | 3 |
| `ThetaCuspHawkingBMModularMixedTensor` | 6 |
| `ThetaCuspHawkingBMModularBackground` | 2 |
| `ThetaCuspHawkingBMModularMetricEndpoints` | 3 |
| `ThetaCuspHawkingBMModularTangentAction` | 3 |
| `ThetaCuspHawkingBMModularTensorQuotient` | 7 |
| `ThetaCuspHawkingBMModularQuotientEinstein` | 4 |

All nine final development files passed individual `lake env lean` checks without
diagnostics. Each canonical leaf passed one `lake build <module>` final audit in
an exact-source cache-only package, compiling exactly its requested new leaf.
All canonical source bytes match the audited copies. All 18 new olean/ilean
artifacts are installed and byte-matched; all nine modules are wired once into
the RHTower umbrella. No dependency, umbrella or full build ran.

One scratch `lake env lean` audit checked exactly these 39 newly declared public
theorem axiom sets, once. Each contains only `propext`, `Classical.choice` and
`Quot.sound`. Earlier batches were not re-audited. Source indexing and
`lint --check-generated` passed, with existing large-file warnings. Scoped
whitespace checks passed. No added axiom, proof gap, numerical experiment or
computational certificate was used. All owned Lean/Lake jobs completed, and the
owned scratch and isolated audit package were removed.

## Remaining physical bridge

The modular tensor and quotient-equation gap is closed. Identify this metric
with the original causal response, establish the physical gauge conditions,
and construct and evaluate the original left-QNM pairing, including its
source domain and all boundary terms. Quotient-compatible endpoint geometry
does not establish causal support, response uniqueness or pairing finiteness.

The corpus's cubic Peierls polarization theorem still requires the augmented
horizon/AdS responses to be blocks of one original causal propagator and the
unit-Wronskian left-QNM functional to come from that same action pairing.
Those premises are not supplied by tensor descent.

SS/VV sectors, higher-return response and independent fixed Hawking-clock
extinction remain open. Neither a complete nonlinear response nor RH is proved.
The frontier map is read-only. No numerical experiment supplies proof evidence.
