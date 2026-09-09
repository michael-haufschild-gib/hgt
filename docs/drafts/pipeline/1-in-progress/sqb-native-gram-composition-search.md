# SQB: native Gram and residual composition

Status: corpus ingredients located and their statements inspected. The source-specific
composition described below is open. This is a search map for the mathematical gap,
not an additional RH criterion or a claimed occurrence proof.

Proof chain: actual theta source -> unit vectors with vanishing full native residual
at every full Xi target -> native occurrence -> real-preimage classification ->
critical line -> RH.

Hardest obstacle: obtain small residuals in the same norm that makes the actual
native vectors nonzero. The common-forcing graph theorem supplies

    (A-e_q) U_q = F_0,
    F_0 = -(1/4) centered(nativePositive),

with the unchanged native operator and true constant-mode centering. It supplies
neither nonvanishing of U_q nor a vanishing normalized residual.

## Located ingredients and their exact inputs

All paths below are relative to `formal/GaloisForLFunctions/`.

| Ingredient | Existing declaration | Inputs still needed for the SQB use |
|---|---|---|
| Unit vectors whose images tend to zero | `GaloisForLFunctions.hasApproximateUnitKernel_iff_not_isClosed_range`, `HTGeometry/SourceGaugeObservabilitySpectrum.lean` | An injective continuous linear map between complete spaces, with nonclosed range. Its domain norm must be the norm transported to native vectors. |
| A compact reporter produces such vectors on a source kernel | `GaloisForLFunctions.compact_sourceGaugeReporter_hasApproximateUnitKernel`, same module | Actual compactness, injectivity of the joint source/reporter map, and an infinite-dimensional source kernel. These are mathematical inputs, not consequences of naming a map a residual. |
| Norm-preserving inclusion into the native space | `HTGeometry.denseSourceFeatureGramIsometry`, `HTGeometry/OneSidedFeatureGramIsometry.lean` | Equality of every complex Gram entry and density of the source feature span. **No density of the target family in the whole native space is needed.** |
| Transport of operator compressions | `HTGeometry.canonicalCompressionEntry_eq_of_gram_eq`, `RHTower/KrylovGramPrefixTransfer.lean` | Bounded operator models, equal vector Gram and mixed vector/operator-image Gram entries, and linearly independent finite frames. Unbounded native action additionally needs graph/domain transport. |
| Exact native theta dilation norm | `RHTower.SelbergThetaDilationGram.vector_inner`, `RHTower/SelbergThetaDilationGram.lean` | Already proved for its literal family: `inner (vector rho L) (vector rho M) = K(M-L)+H(L+M)`. The reflected totient term H is included. |
| Actual native source graph | `RHTower.SelbergThetaCommonForcing.centeredDomain_equation`, `RHTower/SelbergThetaCommonForcingGraph.lean` | Already proved for every actual Xi copy. Both native graph limits and all primitive rows are retained. |
| A dual way to find range information | `HTGeometry.observableBy_iff_mem_range`, `HTGeometry/RangeObservabilityDuality.lean` | A bounded injective self-adjoint operator. Its pairing bound is equivalent to actual range membership. Self-adjointness cannot be assumed for a residual at a general complex target. |

Here `HTGeometry` abbreviates the namespace `GaloisForLFunctions.HTGeometry`.
The SourceGauge declarations instead live directly in `GaloisForLFunctions`.

## The useful join

The one-sided isometry removes a possible unnecessary task: showing that a theta
feature family spans the entire native Hilbert space. A source model only needs to
land isometrically in the native space, with the correct operator action on its image.

The next object to identify is therefore an **augmented Gram family**, containing
both each vector and its operator image. Its entries include

    <v_i,v_j>,  <v_i,T v_j>,  <T v_i,v_j>,  <T v_i,T v_j>.

Matching separate vector norms and image norms is insufficient. Matching the complete
complex augmented Gram gives one common isometry for vectors and images. Source
graph approximation and closedness of the native operator can then extend the
feature-level action. The existing SQB graph construction provides the native side
of this passage for the common-forcing family.

The two concrete joins still being sought are:

1. A source-side model with a proved mechanism producing small images in its own
   norm, together with an exact match to the full native augmented Gram.
2. Alternatively, a source-specific estimate for the same native kernel that
   directly supplies the nonclosed-range or small-image input.

The dilation Gram theorem uses the profile from `SelbergThetaDilationTransform`.
The common-forcing graph uses the reflected first-order pair from
`SelbergThetaCommonForcing`. An identity between these families, or a generalization
of the Gram calculation to the reflected pair, remains a required join. Neither is
silently identified with the other.

## Other exact constructions exposed by broad search

`HedenmalmThetaAnomalyBurnolMultiplicativeSyzygyQuotient` gives an unconditional
scalar unit synthesis at each Xi point from the 2, 3, and 6 Burnol multipliers.
This is a possible source identity to transport. A scalar Bezout row does not yet
identify a native vector or its operator image.

`DeningerTwoPrimeKummerDenseNonclosedRange` constructs an actual arithmetic
multiplier with dense nonclosed range. Its carrier is an arithmetic coefficient
`ell^2` space. It supplies a concrete model for the first ingredient above; an
equal-Gram and operator-action identification with SQB has not been found.

`CommonRadialSubunitHarmonicCompletion` supplies actual Hilbert--Schmidt prime
synthesis and the exact covariance `W W* = A` on its stated half-line/prime carriers.
It is a proved factorization to compare against native kernels, not an identification
with the native Selberg operator.

`PrimeArchKrylovResidualRH` contains a strong determinant producer, but its exact
reflected complex Gram realization is an input. The canonical realization in that
file takes RH as an argument. It is not an unconditional producer of the missing
SQB norm identity.

## Reproducible discovery method

Broad discovery uses separate concepts and OR queries, one result per module and
exploration hits, before following exact statements and their assumptions. Examples:

    python3 scripts/formal_tools.py research 'controllability observability reachability' --any --per-module 1 --explore 12 --limit 32
    python3 scripts/formal_tools.py research '"equal Gram" "kernel domination" "Toeplitz Hankel" "norming"' --any --per-module 1 --explore 8 --limit 30
    python3 scripts/formal_tools.py research '"Weyl sequence" "approximate eigenvector" "spectral inclusion"' --any --per-module 1 --explore 8 --limit 25
    python3 scripts/formal_tools.py research '"compact source" "compact residual" "compact synthesis"' --any --per-module 1 --explore 8 --limit 25

Follow-up searches use the remaining hypothesis, the actual carrier, or the displayed
kernel, not just the route name. A promising docstring is followed by its definition,
full theorem statement, and proof. Results are separated into actual constructions,
general transport theorems, and conclusions requiring the desired property as input.
This preserves useful theorems across route names without mistaking an interface for
its producer.

API check passed: `lake env lean /tmp/sqb37_corpus_interfaces.lean` imported the six
principal modules and checked all nine selected declarations, exit 0. The exact
types are in `/tmp/sqb37_corpus_interfaces.log`. This verifies the interfaces, not
the missing composition. No new Lean theorem, numerical computation, full build,
or frontier-map edit is part of this search.
