# HB full classical angular response and mixed-current defect

Stage: formalized in Lean 4; leaf, axiom and source-lint audits passed. Type: `[BRIDGE]`. RH remains open.

Chain: literal theta cusp → Xi occurrence → retained spin-two source → physical
causal response and left-QNM pairing → independent fixed Hawking-clock extinction → RH.

For both physical branches of every actual Xi occurrence, the constructed full
angular response H is smooth and modular invariant on the entire upper half-plane
and satisfies the original equation

`(Delta-L)H = (L/2)*S²`, where `L=(2s+1)(2s+2)`.

S is the literal completed theta cusp scalar, including both Weyl terms and every
Fourier mode. H is the global extension of the original complete cusp cutoff plus
the actual native energy-domain correction. No inverse, regularity, modularity or
critical-line premise is supplied to these actual-response theorems.

## From the distribution equation to the classical equation

Compact positive-height planar tests identify the already constructed smooth
response and forcing with their original measurable representatives. Two actual
integrations by parts give `integral f*Delta(g)=integral Delta(f)*g`; compact
support and smoothness establish integrability of every term. The smooth response
therefore has continuous residual

`Delta_Euclidean(h) - (L*h+F)/y²`.

Its integral against every compact smooth test is zero. Smooth-test separation
makes the residual zero almost everywhere; continuity on the open positive-height
chart makes it zero at every point. Multiplication by y² gives the original
hyperbolic differential equation throughout the upper half-plane, including seams
and elliptic points.

## Complete cusp cutoff and modular assembly

The original cutoff response is `kappa=chi(y)*H0`, with
`chi(y)=smoothTransition(y-2)` and H0 the complete three-power response to the full
squared cusp principal part. On a closed-cell overlap, a nontranslation modular
map puts both heights strictly below 2, where kappa vanishes on a neighborhood.
Translation overlaps preserve height. Thus the full cutoff germs agree.

A general closed-cell germ extension chooses an orbit representative. Germ
compatibility proves independence of the choice, invariance, agreement of the
entire germ on the closed cell and global smoothness. Proper discontinuity reduces
the nearby choices to finitely many; closedness excludes those missing the cell at
the base point. Applied to kappa, this preserves all its differential forcing.

The exact real linear coordinate identification `z ↦ (Re z, Im z)` transfers the
actual first and second derivatives to the original angular metric coordinates.
The full second chain rule gives

`Delta(f composed with g)=normSq(g')*(Delta f composed with g)`

for a holomorphic chart change g. Its second-derivative terms cancel because the
chart coordinates are harmonic. For the actual modular Mobius map, this Jacobian
factor cancels the squared-height factor in the hyperbolic Laplacian. Consequently
the original cutoff forcing identity extends from the closed cell to every point.
Adding it to the classical correction equation proves the full H equation.
Subtracting the original cutoff recovers the actual native Hilbert-space correction
almost everywhere.

## Actual covector and retained current

The constructed field is transferred back to the original two angular coordinates.
Its coexact derivative A is smooth and has zero actual covariant divergence. Set
`J=S*coexact(S)`, exactly the retained source pair `(S*Sy,-S*Sx)`.
Differentiating the full equation gives

`coexact(Delta H)=L*A+L*J`.

The actual covector intertwining formula retains its curvature term, hence

`roughLaplacian(A)+A=L*A+L*J`.

The two physical fundamental rates are `s=rho-2` and `s=-rho-1`. Their doubled-rate
parameter equals the parameter of the constructed angular inverse. The existing
two-factor mixed master identity has defect

`B²*(D-(2s+1)(2s+2)*A-2(s+1)(2s+1)*J)`.

Substituting the actual `D=roughLaplacian(A)+A`, the constructed A, the original J,
and the full gradient-source K makes this defect zero. The theorem holds for every
angular point, every real exterior radius r>1, both covector components and every
envelope value B. The radial factors and source current are the original formulas;
no source component is discarded.

## Lean surface and validation

All modules are under `GaloisForLFunctions.RHTower`.

| Module | New public theorems |
|---|---:|
| `ThetaCuspHawkingBMClassicalGreen` | 6 |
| `ThetaCuspHawkingBMClassicalResponse` | 4 |
| `ThetaCuspHawkingBMCellGermExtension` | 4 |
| `ThetaCuspHawkingBMGlobalCuspCutoff` | 5 |
| `ThetaCuspHawkingBMChartCoordinates` | 4 |
| `ThetaCuspHawkingBMConformalLaplacian` | 1 |
| `ThetaCuspHawkingBMModularLaplacian` | 2 |
| `ThetaCuspHawkingBMFullAngularAssembly` | 5 |
| `ThetaCuspHawkingBMFullAngularCovector` | 6 |
| `ThetaCuspHawkingBMFullAngularMasterCurrent` | 3 |

All ten development files passed individual `lake env lean` checks without
diagnostics. Each canonical leaf passed one `lake build <module>` final audit in
an exact-source cache-only package. Every invocation compiled exactly its one new
leaf and read existing dependencies from cache. Audited source bytes match all ten
canonical files. All 20 new olean/ilean artifacts are installed, and all ten modules
are wired once into the RHTower umbrella. No dependency, umbrella or full build ran.

One scratch `lake env lean` audit checked all 40 new public theorem axiom sets,
once. Each set contains only `propext`, `Classical.choice` and `Quot.sound`.
Earlier theorem batches were not re-audited. Scoped whitespace checks passed.
Source indexing and `lint --check-generated` passed. Existing large-file warnings
remain. No added axiom, proof gap, numerical experiment or computational certificate
was used.

## Metric reconstruction and remaining physical bridge

The differentiated literal J equation, the full actual angular and radial metric
jets, both master-current components and all sixteen forced mixed Einstein
components are now proved in
[actual mixed metric and endpoints](hb-actual-mixed-metric-and-endpoints.md).
That construction also proves the actual ingoing inverse-radius tensor pullback,
exact horizon and radial boundary values and the vanishing conformally rescaled
boundary limit. The unrescaled radial-angular boundary term is retained.

The actual modular tensor transformation laws and quotient Einstein equation are
proved in [modular tensor descent](hb-modular-tensor-descent.md). Physical gauge
conditions, original causal prescription and left-QNM pairing remain open. SS/VV sectors,
higher-return response and the independent fixed Hawking-clock extinction law
also remain open. These results do not establish causal admission, extinction or
RH. No numerical computation supplies proof evidence. The frontier map is read-only.
