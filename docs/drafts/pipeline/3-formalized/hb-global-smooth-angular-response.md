# HB globally smooth angular response

Stage: formalized in Lean 4; leaf, axiom and source-lint audits passed. Type: `[BRIDGE]`. RH remains open.

Chain: literal theta cusp → Xi occurrence → retained spin-two source → physical
causal response and left-QNM pairing → independent fixed Hawking-clock extinction → RH.

The actual response to the complete cusp-subtracted forcing has a globally smooth,
pointwise modular-invariant representative on the entire upper half-plane. It
represents the original solution in its native Hilbert space. Neither modular seam
nor elliptic fixed point is excluded. This closes global smooth reconstruction of
the forced angular correction; physical causal admission remains a separate obligation.

## Actual scalar lift and global equation

For an original quotient L² vector u, extend its specified representative by zero
from the open cell and periodize over the actual projective modular group:

`U(z) = sum_gamma (1_open-cell * u)(gamma*z)`.

The literal orbit-height bound and proper discontinuity imply that, on any compact
chart K, one finite set of group elements contains every translate meeting the
closed cell. Thus the complete periodization is a finite sum there. The zero
extension is full hyperbolic L²; measure-preserving translates and finite sums give
L² on every compact chart. The lift is invariant pointwise and equals u almost
everywhere in the native quotient measure.

Exact scalar test unfolding converts the already proved modular distribution
equation into the equation of this actual lift. Hyperbolic volume transports to
planar volume with density y^-2. Squared height cancels the density exactly; every
compact planar localization is L¹ and L². Writing V for the lifted original forcing,
the actual planar equation is

`integral (Delta g)*U - L*integral (g/y²)*U = integral (g/y²)*V`

for every smooth compact test supported in positive height.

Testing with g times an arbitrary Schwartz function gives the complete scalar
localization identity, where T(g,U) denotes the distribution of gU:

```
Delta T(g,U) = 2*sum_i partial_i T(partial_i g,U)
              - T(Delta g,U) + L*T(g/y²,U) + T(g/y²,V).
```

Every derivative of the cutoff is retained. The argument does not treat completed
hyperbolic-frame gradient components as invariant scalar functions. Local L² first
gives H¹ by elliptic gain from H^-1, then H² by repeating the identity. Consequently
every localization has an L² Laplacian and an integrable Fourier transform.

## Smooth forcing through all cell overlaps

The literal Xi scalar obeys inversion and translation identities already proved
from its actual series and continuation. Generation by S and T now proves invariance
under the entire modular group.

For an integral matrix A with nonzero lower-left entry, the denominator in the
actual height formula has squared norm at least y², hence

`height(A*z) <= 1/height(z)`.

Every point of the closed cell has height strictly greater than 1/2. If both z and
A*z belong to that cell, applying the bound to A and its inverse puts both heights
strictly below 2. These inequalities persist on a neighborhood. There the cutoff
and all its differential contributions vanish, so the original full forcing is
exactly `(L/2)*S²` in both charts. If the lower-left entry is zero, A acts as an
integer translation and the full forcing is periodic. Thus every closed-cell
overlap, including elliptic corner overlaps, carries equal forcing germs.

Choose a closed-cell representative of each orbit and evaluate the literal forcing
there. Equality of the overlap germs proves independence of that choice and
pointwise modular invariance. On a compact neighborhood only finitely many cell
pullbacks are possible. Those not meeting the cell at the base point are excluded
nearby by closedness; all others have equal forcing germs. The chosen extension
therefore agrees with one smooth original chart germ locally. Pulling back by a
modular element proves global chart smoothness.

This smooth field equals the actual lifted L² forcing almost everywhere in full
hyperbolic volume. Native almost-everywhere equality extends globally using the
countable group and measure-preserving pullbacks. The zero-extension periodization
itself need not be pointwise continuous on seam orbits; its smooth representative
is constructed and identified separately.

## All orders and smooth response

Every compact localization of the globally smooth original forcing has an explicit
Schwartz representative, hence every Sobolev order. In the scalar localization
identity, H^s control of all response localizations puts the right side in H^(s-1).
Elliptic gain gives H^(s+1). Induction establishes every nonnegative integer order.

The existing planar Fourier reconstruction then supplies a smooth representative
of each actual response localization. On overlaps, almost-everywhere equality
implies equality of the continuous cross-products `g*R_h = h*R_g`. Compact positive-
height tests are nonzero at every point, so local quotients R_g/g glue. A countable
subcover establishes planar almost-everywhere identification for the resulting
smooth field on the whole upper half-plane. Exact density transport identifies it
with the actual global lift in full hyperbolic volume and with the original solution
in native quotient measure. Smoothness and almost-everywhere modular invariance
imply pointwise modular invariance.

The resulting `globalResponse` has the proved properties
`globalResponse_smooth`, `globalResponse_ae_lift`, `globalResponse_invariant`, and
`globalResponse_native_ae`. These actual-response theorems require no additional
smoothness, boundary-trace, modularity or critical-line hypothesis.

## Lean surface and validation

All modules below are under `GaloisForLFunctions.RHTower`.

| Module | New public theorems |
|---|---:|
| `ThetaCuspHawkingBMGlobalScalarLift` | 8 |
| `ThetaCuspHawkingBMGlobalLiftedEquation` | 4 |
| `ThetaCuspHawkingBMGlobalPlanarLift` | 5 |
| `ThetaCuspHawkingBMGlobalPlanarEquation` | 3 |
| `ThetaCuspHawkingBMGlobalCutoffLaplacian` | 2 |
| `ThetaCuspHawkingBMGlobalH2Response` | 4 |
| `ThetaCuspHawkingBMFullSourceOverlap` | 5 |
| `ThetaCuspHawkingBMGlobalSmoothForcing` | 4 |
| `ThetaCuspHawkingBMGlobalForcingRegularity` | 3 |
| `ThetaCuspHawkingBMGlobalSobolevBootstrap` | 2 |
| `ThetaCuspHawkingBMGlobalSmoothResponse` | 5 |

All eleven development files passed individual `lake env lean` checks without
diagnostics. Each canonical leaf passed one `lake build <module>` final audit in
an exact-source cache-only package. Every invocation compiled exactly its one new
leaf; existing dependencies were read from cache. Audited source bytes match the
canonical files. All 22 new olean/ilean artifacts are installed, and all eleven
modules are wired once into the RHTower umbrella. No dependency, umbrella or full
build ran.

One scratch `lake env lean` audit checked all 45 new public theorem axiom sets,
once. Every set contains only `propext`, `Classical.choice` and `Quot.sound`. No
older theorem batch was re-audited. Source indexing and `lint --check-generated`
passed; existing large-file warnings remain. Scoped whitespace checks passed.
No added axiom, proof gap, numerical experiment or computational certificate was
used. The frontier map remains read-only.

## Remaining bridge

Transfer the exact distribution equation to the reconstructed smooth representative
and state its classical pointwise equation. Construct the global cusp-cutoff
extension and assemble the complete angular field `chi*H0+h`. Then establish physical
causal admission for the complete forced metric, including horizon and radial
boundary conditions, gauge conditions and the original left-QNM pairing. SS/VV
sectors and the independent fixed Hawking-clock extinction law remain open.
Global elliptic solvability and smoothness do not supply these physical laws or RH.
