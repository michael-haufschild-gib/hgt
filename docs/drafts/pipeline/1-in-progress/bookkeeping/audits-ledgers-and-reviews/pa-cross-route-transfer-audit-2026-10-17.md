# PA: cross-corpus transfers and the remaining source estimate

Status: AUDIT COMPLETE. Existing transfers below are not new contributions.
The subsequent fixed-scale inverse theorem is contribution 15; goal: 15/100.
User requested concrete help for PA from other routes and unrelated Lean.
The frontier map is read-only and was used solely for routing; mathematical
claims below come from Lean statements and proofs.

## Transfers already available

1. `HTGeometry/QuantumReplicaHausdorff` proves all complementary trace
   differences of a Hilbert--Schmidt channel's bounded positive effect are
   nonnegative. `RHTower/SoninCoupledQuantumHausdorff` instantiates this on the
   actual all-prime coupled Sonin channel, with its actual HS proof and norm
   radius. `SoninCoupledBernsteinCollarQuantumDischarge` removes every auxiliary
   Hausdorff-positivity premise from the endpoint/source comparison.
   What remains is the exact endpoint-minus-Sonin packet estimate, not a
   further abstract positive-operator theorem.
2. `PrimeArchHausdorffFixedOrderLargeShiftPositivity` imports Riemann--von
   Mangoldt, ordinate-band copies and mass-height transfer. For each order k,
   every sufficiently large shift r is unconditionally nonnegative. Its
   final RH criterion concerns only r below the order-dependent threshold.
   The proof actually constructs a threshold using K=10(k+1)+20 and a height
   at least max(T0,500,42(k+1)+44K); it does not prove an order-uniform cutoff.
3. `HTGeometry/HalfOrderMeromorphicObstruction` excludes single-valued
   meromorphic germs with a nonzero inverse-square-root boundary law, using
   integer-order parity. `PrimeArchBernsteinAbelMeromorphicCollarCriterion`
   needs only a meromorphic realization of the actual Abel susceptibility
   at each real R with 250000/251001<R<1, agreeing with the interior Abel germ.
   Poles are permitted. Constructing that realization remains unproved.
4. `PrimeArchThetaSingleGibbsGammaCoordinate` converts the first-atom Gibbs
   moments to one explicit positive incomplete-Gamma integral.
   `PrimeArchThetaSingleGibbsRationalEnclosureGate` reduces the two low-degree
   certificates to rational bounds on nine moments and exp(-pi).
   `PrimeArchThetaFirstAtomHighOrderQuadrature` already supplies exact Taylor
   lower/upper integrands. Certified completion is a concrete finite task,
   but it would not settle the unbounded-order PA obstruction or count here
   as a new significant cross-route theorem.

## Exact object on which further transfer must act

For one nondegenerate coupled aperture a, let

    d_a(k) = radiusNormalizedMoment(endpointRadius, normalizedPrimeArchMoment)(k)
             - soninCoupledNormalizedReplicaMoment(a)(k),
    D_a(n) = sum_i |L_(d_a)(B_(n,i))|^2.

`SoninCoupledNormalizedDeterminantCollar` identifies D_a(n) exactly with the
source mismatch and with the Bernstein purity of the relative determinant's
logarithmic coefficient defect. This is a coefficient/germ identity; it does
not assert a global nonvanishing Fredholm determinant or a susceptibility
continuation.

`BernsteinLegendreDoubleSourceKernel` supplies the exact bivariate polynomial
kernel S_n(x,y)=sum_i B_(n,i)(x) B_(n,i)(y). Its Legendre coefficient formula
has generating radical

    [1 - 2t(1-x-y+2xy) + t^2(1-x-y)^2]^(-1/2).

Two scratch examples passed Lean with an empty log:

    (L_(d_a) tensor L_(d_a))(S_n) = D_a(n),
    (n+2)D_a(n+1) = (n+1)D_a(n) + DirichletDissipation(d_a,n).

These are useful exact splices of existing theorems, not new contributions.
The second identity has a nonnegative INCREASE in scaled energy. Treating
degree elevation as forward dissipative evolution would reverse its arrow.

## Candidate machinery and attacks

`HTGeometry/AnalyticMarkovTransferMatrix` has actual holomorphic branch
matrices, geometric coefficient decay and an exact periodic-word trace
formula. `GeometricDecayFredholmDeterminant` proves locally uniform determinant
limits and holomorphy. These could support a continuation proof after an
exact source representation is constructed. They do not identify PA's
quadratic susceptibility. Diagonal extraction can create square-root branch
points even from meromorphic inputs; analyticity of Xi or of a relative
determinant is therefore insufficient.

The same analytic Markov class has a substantial restriction:
`RHTower/RuelleZetaNuclearZeroFree.not_riemannZeta_eq_ruelleZeta` rules out
identifying zeta with its entropy-at-most-one nuclear Ruelle zeta. This does
not directly rule out a representation of PA's different susceptibility,
but prevents a naive zeta/positive-transfer identification.

The completed Burnol Levy inverse result does not supply PA's missing sign:
physical cone preservation and injectivity are different from reflection
of positivity by the inverse. No such inverse-positivity claim was made.

## Audit and search limits

One /tmp Lean file checked ten principal transfer signatures and their axiom
lists. All ten pass; only `propext`, `Classical.choice`, `Quot.sound` occur.
The eight imported leaf objects were present and newer than their sources.
The first scratch attempt exposed and corrected a namespace mismatch:
`HTGeometry.quantumMasterEffectScaledDifference_nonneg` is in the root
HTGeometry namespace, not GaloisForLFunctions.HTGeometry.

Three documented deep corpus searches addressed PA/source positivity,
Bernstein mismatch, and Fredholm continuation. Inventory covered 61,576 Lean
files and over 1.08 million declarations. The first and third completed; the
second was partial after malformed final model JSON. Semantic coverage was
unmeasured, compiler snapshots mixed. Actual source inspection and targeted
Lean checks determine applicability. The first search mostly returned
irrelevant positive-matrix or arithmetic names; these were not promoted into
transfers. No web or old research prose was used as mathematical evidence.

## New transfer proved after this audit

The fixed-scale coefficient-index measure and exact dominant divisor recovery
are now formalized in contribution 15:
`../../../3-formalized/pa-bernstein-index-divisor-tomography-2026-10-17.md`.
The principal theorem is
`RHTower.primeArchEndpointBernstein_index_divisor_tomography`.
It states RH or weak index/probability laws with exact conjugate coordinate
fibres and reciprocal-square fibre multiplicities. All 15 leaves, 76 public
axiom lists, 63 theorem signatures and 13 definitions passed. The contribution
card records the global lint failures from concurrent work and all limits.

This provides a new growing-index observable for PA. It does not prove the
missing source sign or construct its Sonin susceptibility representation.
