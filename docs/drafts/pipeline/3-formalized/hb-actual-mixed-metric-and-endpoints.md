# HB actual mixed Einstein metric and physical endpoint values

Stage: formalized in Lean 4. Type: `[BRIDGE]`. RH remains open.

Chain: literal theta cusp → Xi occurrence → retained spin-two source → physical
causal response and left-QNM pairing → independent fixed Hawking-clock extinction → RH.

For both physical branches of every actual Xi occurrence, a constructed metric
field satisfies all sixteen original forced mixed Einstein equations at every
exterior point. Its complete angular and radial derivatives are actual field
jets. The actual ingoing and inverse-radius coordinate pullbacks give an explicit
metric extending holomorphically in inverse radius through the horizon and radial
boundary. Its exact endpoint values and vanishing conformally rescaled boundary
limit are proved. No angular inverse, source equation, regularity, metric
realization or critical-line premise is supplied to the final construction.

## Actual square-source differentiation

Write S for the literal completed theta cusp scalar and s for either physical
rate `rho-2` or `-rho-1`. Set `e=(s+1)(s+2)`, `L=(2s+1)(2s+2)` and
`P=S²/2`. The actual scalar equation and product rule give

`Delta P = 2e*P + G`, with `G=y²*(Sx²+Sy²)`.

The original retained square-source covector is exactly `J=coexact(P)`.
Differentiating the full G, using the scalar equation and commuting its actual
mixed derivatives, gives `coexact(G)=2K`, with the original gradient-source
covector K. The actual coexact intertwining identity therefore proves

`roughLaplacian(J)+J = 2e*J+2K`.

J is smooth and covariantly divergence-free. This identifies the previously
prescribed angular source slot with the differentiated literal field. The full
angular response A already satisfies `roughLaplacian(A)+A=L*A+L*J`.

## Actual metric and every forced Einstein component

The actual pullbacks of A and J to four coordinates have the complete required
angular jets. Their divergence constraints and differentiated constraints supply
the corresponding angular operator entries. The two radial stream fields have
profiles `B²` and `B²/r²`, where B is the original fundamental envelope.
Their full two-jets and the two-jets of their radial derivatives are proved,
including the third radial derivative required by the metric equation.

For a radial-angular stream Psi, the static mixed metric has blocks

`h_tk=(r²-1)*partial_r(Psi_k)`, `h_rk=(2s)/(r²-1)*Psi_k`.

Set `c=s(s-1)/4` and `Psi=B²*(A-c*J/r²)`. The resulting actual field is
`forcedMetricField`. Its complete metric two-jet agrees with the evaluated stream
jet, and every component has continuous second derivatives. The doubled envelope
identity is proved directly for the actual exponential field.

Both the master current and its radial derivative equal their full original
source expressions. Applying the already evaluated cosmological Einstein
linearization, then its proved linearity on actual metric-field jets, gives

`D(Einstein-3g)[forcedMetricField] + literalMixedSource = 0`

for all sixteen components. `literalMixedSource_eq` identifies this source with
the original quadratic mixed tensor evaluated on S and its actual first and second
coordinate derivatives. The source normalization, gradient terms, temporal
components and both radial stream factors are retained.

## Actual endpoint geometry

The static-to-ingoing map and the inverse-radius map `u=1/r` have proved actual
differentials. In particular, the latter tensor pullback retains `dr=-u^-2 du`.
In coordinates `(v,u,x,y)`, put

`E=a²*exp(2s*(v+log(1+u)))`.

The full pulled-back metric is symmetric with only mixed blocks

`h_vk = E*(2s*u*A_k + 2c*u*(1-(s+1)*u²)*J_k)`,

`h_uk = E*(-2s/(1+u)*A_k + 2c*u*(1+(s+1)*u)/(1+u)*J_k)`.

This is an equality with the coordinate pullback of the actual reconstructed
metric. Every entry is holomorphic where `1+u` lies in the complex slit plane,
which includes neighborhoods of both endpoints.

At the horizon `u=1`, the exact blocks are

`h_vk=E*2s*(A_k-c*J_k)`, `h_uk=E*(-s*A_k+c*(s+2)*J_k)`.

At the radial boundary `u=0`, they are

`h_vk=0`, `h_uk=-2s*a²*exp(2s*v)*A_k`.

The proof retains this exact radial-angular boundary term; it does not assert
that the unrescaled metric vanishes. Every component of `u²*h` tends to zero at
the boundary. These are metric endpoint statements, not an identification with
the original causal response or its left-QNM pairing.

## Lean surface and validation

All modules are under `GaloisForLFunctions.RHTower`; theorem namespace is
`RHTower.D4BMModularCore`.

| Module | New public theorems |
|---|---:|
| `ThetaCuspHawkingBMSquareSourceDifferential` | 5 |
| `ThetaCuspHawkingBMSquareSourceCovector` | 5 |
| `ThetaCuspHawkingBMStreamAngularJets` | 4 |
| `ThetaCuspHawkingBMStreamRadialProfiles` | 2 |
| `ThetaCuspHawkingBMStreamRadialFields` | 5 |
| `ThetaCuspHawkingBMStreamMetricField` | 2 |
| `ThetaCuspHawkingBMStreamForcedCurrent` | 3 |
| `ThetaCuspHawkingBMMetricLinearCombination` | 2 |
| `ThetaCuspHawkingBMStreamMetricEinstein` | 1 |
| `ThetaCuspHawkingBMForcedMetricTensor` | 2 |
| `ThetaCuspHawkingBMForcedMetricField` | 2 |
| `ThetaCuspHawkingBMInverseRadiusCoordinates` | 2 |
| `ThetaCuspHawkingBMForcedMetricCompact` | 2 |
| `ThetaCuspHawkingBMForcedMetricEndpoints` | 5 |

All fourteen final development files passed individual `lake env lean` checks
without diagnostics. Each canonical leaf passed one `lake build <module>` final
audit in an exact-source cache-only package. Each invocation compiled exactly its
one requested new leaf and read existing dependencies from cache. All fourteen
canonical source files match the audited bytes; all 28 new olean/ilean artifacts
are installed and byte-matched. Every new module is wired once into the RHTower
umbrella. No dependency, umbrella or full build ran.

One scratch `lake env lean` audit checked exactly these 42 new public theorem
axiom sets, once. Each set contains only `propext`, `Classical.choice` and
`Quot.sound`; earlier batches were not re-audited. Source indexing and
`lint --check-generated` passed, with existing large-file warnings. Scoped
whitespace checks passed. No added axiom, proof gap, numerical experiment or
computational certificate was used. Owned foreground checks completed, and the
owned scratch and isolated audit package were removed.

## Remaining physical bridge

The actual covector, metric, source and background transformation laws, tangent-pair
quotient and forced equation on that quotient are now proved in
[modular tensor descent](hb-modular-tensor-descent.md).
Identify the metric with the original causal prescription, establish its physical
gauge conditions and define and evaluate the original left-QNM pairing on it.
Smooth ingoing endpoint behavior and vanishing conformal boundary data alone do
not establish causal admission, uniqueness or finiteness of that pairing.

The SS/VV sectors, higher-return response and independent fixed Hawking-clock
extinction law remain open. The theorem solves the forced mixed linearized metric
equation; it does not prove a full nonlinear response or RH. The frontier map is
read-only. No numerical computation supplies proof evidence.
