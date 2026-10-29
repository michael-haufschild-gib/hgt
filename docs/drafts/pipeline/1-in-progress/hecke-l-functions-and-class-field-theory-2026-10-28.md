# Hecke L-functions and class field theory

- **ID:** hecke-cft
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** user goal 2026-10-28; ArtinMertens S8 (non-rational Artin characters)
- **Statement:** for a number field `K` and a modulus `𝔪 = 𝔪₀ 𝔪∞`: the ray class group `Cl_𝔪` is finite;
  every character `ψ` of `Cl_𝔪` has an L-function `L(s, ψ) = Σ_𝔞 ψ(𝔞) N𝔞^{−s}` with Euler product,
  meromorphic continuation to the complex plane, the completed functional equation for primitive
  characters, a pole at `s = 1` exactly for `ψ = 1`, and `L(1, ψ) ≠ 0` for `ψ ≠ 1`;
  for every finite abelian `L/K` the Artin map gives `Cl_𝔪/H ≅ Gal(L/K)` (reciprocity), and
  every congruence subgroup `H` is the norm group of an abelian extension (existence).

## Goal
Programme folders `formal/GaloisForLFunctions/HeckeLFunctions/` (first) and
`formal/GaloisForLFunctions/ClassFieldTheory/` (second), each with its umbrella.

## Gates — Hecke L-functions
- [x] HL1 moduli; ideals coprime to `𝔪`; `K_𝔪` (elements prime to `𝔪`), the ray group `K^{𝔪,1}_+`;
      surjective reduction `K_𝔪 → (𝓞/𝔪)ˣ × {±1}^{𝔪∞}` with kernel `K^{𝔪,1}_+`; `Cl_𝔪 = I^𝔪/P_𝔪`; map to `Cl_K`
      surjective with finite kernel ⇒ `Cl_𝔪` finite — `finite_rayClassGroup`,
      `toClassGroup_surjective`, `range_rayResidueClass`, `rayHom_surjective`
- [x] HL2 ray class characters on integral ideals; multiplicativity; convergence for `Re s > 1` —
      `heckeValue_mul`, `lSeriesSummable_heckeCoeff`
- [x] HL3 `L(s, ψ)`: absolute convergence over ideals for `Re s > 1`, prime-ideal Euler product,
      nonvanishing there, and `ψ = 1` vs `ζ_K` — `summable_norm_heckeIdealTerm`,
      `heckeL_eq_tsum_ideals`, `heckeL_eulerProduct_hasProd`, `heckeL_ne_zero`,
      `heckeL_one_eq_dedekindZeta_mul`
- [x] HL4 ray-class ideal counts with power saving and equal densities —
      `exists_abs_ncard_rayClassIdeals_sub_le` (`#{𝔞 ∈ c : N𝔞 ≤ x} = κ_𝔪 x + O(x^{1−1/n})`, one
      `κ_𝔪` for all `c`); `rayDensity_pos`; `exists_norm_sum_heckeCoeff_le`
      (`Σ_{N𝔞≤x} ψ(𝔞) = O(x^{1−1/n})`, `ψ ≠ 1`)
- [x] HL5 continuation to `Re s > 1 − 1/n`; holomorphic at `1` for `ψ ≠ 1`; residue for `ψ = 1` —
      `differentiableOn_heckeLCont`, `exists_norm_heckeL_le`, `heckeL_one_eq`,
      `tendsto_sub_one_mul_heckeL_one` (via `HTGeometry.BoundedPartialSums.contLSeries`),
      `heckeDensity_eq_dedekindZeta_residue_mul`, `heckeDensity_pos`
- [ ] HL6 nonvanishing on `Re s ≥ 1` is proved for every character, away from the trivial pole —
      `heckeLFunction_ne_zero_of_one_le_re`, `heckeLCont_one_ne_zero`, `heckeLCont_ne_zero`;
      Mertens bounds for Hecke characters remain open
- [ ] HL7 Hecke's functional equation (theta series, Poisson summation, Mellin transform) —
      full-plane meromorphic continuation and exact pole classification are now proved;
      primitive Gauss/conductor normalization and dual-character identification remain open

## Gates — class field theory
- [ ] CFT1 Artin map on ideals prime to the ramification of an abelian `L/K`
- [ ] CFT2 norm groups `P_𝔪 N(I_L^𝔪)`; primes splitting completely; logarithmic densities
- [ ] CFT3 second inequality `[I^𝔪 : P_𝔪 N] ≤ [L : K]` (analytic, HL5)
- [ ] CFT4 first inequality for cyclic `L/K` (Herbrand quotients of units and local norm indices)
- [ ] CFT5 Artin reciprocity (Artin's cyclotomic crossing)
- [ ] CFT6 existence theorem (Kummer theory)
- [ ] CFT7 consequences: Chebotarev, `L(1, ψ) ≠ 0` for all `ψ ≠ 1`, abelian Artin `L` = Hecke `L`,
      Mertens for every Artin `L`-function (ArtinMertens S8)

## Building blocks (corpus/Mathlib)
- Mathlib: `FractionalIdeal.count`, `toPrincipalIdeal`, `ClassGroup`, adic valuations, `LSeries`,
  Euler products, Dedekind zeta and residue, Hilbert ramification theory, `IsArithFrobAt`.
- ArtinMertens: lattice counts in dilates of Lipschitz domains, `normLeOne` frontier, Weber's theorem,
  Abel summation, Frobenius counting in fixed fields.
- `RHTower/Artin`: Artin Euler products, Frobenius reciprocity, virtual characters.
- `HTGeometry/ABHN`: local Brauer invariants, cyclic algebras, unramified local reciprocity, norm
  quotients of cyclic Galois extensions.

## Log
- 2026-10-28 — created; corpus/Mathlib survey: no ray class groups, Hecke characters, idèle class
  group or reciprocity map.

## Completed Euler-product and residue batch

See [the formalized proof and declarations](../3-formalized/hecke-prime-ideal-euler-product-and-positive-residue.md).
Four modules identify ideals with prime exponent vectors, transfer the existing occupation
Euler product to the actual coefficient L-series, prove nonvanishing on `Re s > 1`, remove
the finite-modulus Euler factors from Dedekind zeta, and identify the positive residue and
positive ray-class densities. The prior residue limit alone did not establish positivity.

All nine audited results depend only on `propext`, `Classical.choice`, and `Quot.sound`.
All four modules passed final direct source checks with `lake --old env lean`.
The programme is wired into `MainTheorems.lean`;
no umbrella is compiled. HL6, HL7 and CFT remain open.

## Next analytic input

The nonquadratic part of HL6 is now formalized: see
[the proof and declarations](../3-formalized/nonquadratic-hecke-characters-have-no-zeros-on-re-ge-one.md).
Mathlib's Dirichlet-character three-four-one argument has been transferred to the actual
prime-ideal Euler product and combined with the existing continuation and residue limit.
The requested ordering is Hecke first, CFT second. Real-character nonvanishing therefore needs
the analytic route through HL7 and Landau positivity; it must not be postponed to reciprocity.

### Completed nonquadratic nonvanishing

The summable prime-ideal Euler logarithm and local `3–4–1` inequality are implemented in
`HeckeEulerLogarithmsGiveTheThreeFourOneInequality.lean` (source check and olean generation pass;
the two public analytic results have clean transitive axiom audits).
For real `σ > 1` and `t` this gives `|L(σ,1)^3 L(σ+it,ψ)^4 L(σ+2it,ψ²)| ≥ 1`.
If `ψ² ≠ 1` and `L(1+it,ψ) = 0`, the existing holomorphic continuation gives a finite
limit for `L(σ+it,ψ)/(σ-1)`, while `(σ-1)L(σ,1)` and `L(σ+2it,ψ²)` have finite limits.
Their product times `σ-1` is the displayed product and tends to zero, contradicting
the lower bound. Combining with the open-half-plane Euler product proves nonvanishing on
`Re s ≥ 1` for every nonquadratic character. The proof and all six transitive axiom checks
pass in `NonquadraticCharactersDoNotVanishOnTheLineReOne.lean`; both final direct source audits
pass without warnings. Both new modules are wired into the umbrella.
No full-plane continuation or reciprocity is needed for this case.

### Full-continuation dependency audit

Corpus leads inspected while formalizing HL6:

- `RHTower/EpsteinCharacterFunctionalEquation.lean` proves a binary-lattice theta
  transformation with a Dirichlet character modulo a prime. It is a concrete model,
  not the arbitrary-number-field theorem.
- `HTGeometry/DirichletCoefficientTheta.lean` supplies convergence and the Mellin transform
  of a theta series attached to any absolutely convergent coefficient series. It supplies
  no arithmetic theta inversion and therefore cannot by itself extend `heckeL` to all `ℂ`.
- `HTGeometry/FinitePiProductSummability.lean` has polynomial-Gaussian summability on `ℤ^n`.
- `HTGeometry/RemovableSingularity.lean` supplies the derivative quotient limit used for HL6.

HL7 must construct the ideal-lattice theta transformation, account for the unit action and
archimedean signs, and identify its Mellin transform with the actual Hecke ideal series.
These identities remain proof obligations; no functional-equation interface is assumed.

The original `rayResidueClass` has domain `(rayHom 𝔪).range`. Surjectivity, now proved below,
extends it to the full product `(𝓞 K / 𝔪.fin)ˣ × (𝔪.inf → ℤˣ)`. This permits a character to be
separated into its finite component and independent real-place parities. The earlier
finiteness argument did not need surjectivity.

A route using already-proved arithmetic counting avoids new approximation machinery:
`rayDensity_pos` and the definition of `rayDensity` force the common signed-norm-ball volume
to be positive. The translated lattice count then makes every residue/sign coset nonempty
for a sufficiently large norm bound. `conePoints_eq_image` is valid for arbitrary residue/sign
data, not only data in `rayHom.range`; use it with the unit ideal, extract the integral
representative, and apply `rayHom_algebraMap` and `signAtInf_eq_iff`.

`EveryRayResidueAndSignHasAnIntegralRepresentative.lean` now contains the positive-volume lemma,
existence of a lattice point in every signed coset, an integral representative with arbitrary
residue/sign data, and `rayHom_surjective`. The proof check and three transitive axiom audits
pass; its olean is built for the character-decomposition module, and its final direct
source audit passes without warnings. See
[the formalized proof](../3-formalized/finite-residues-and-real-signs-have-integral-representatives.md).
The missing positive-residue dependency olean was built.

After surjectivity, extend `rayResidueClass` from its range to the full residue/sign product
and compose with `ψ`. Its restrictions to `(ρ,1)` and `(1,σ)` give the finite and infinite
characters. For coordinate parities reuse Mathlib `MonoidHom.mulSingle` and
`Finset.univ_prod_mulSingle` (`Algebra/Group/Pi/Lemmas.lean`, `Algebra/BigOperators/Pi.lean`):
each coordinate sign has square one, so its complex character value is `±1`, and the whole
infinite character is the product of those coordinate characters. The principal-ideal
identity and triviality on global units must be proved for these actual characters.
`HeckeCharactersSplitIntoFiniteCharactersAndRealParities.lean` is complete: the decomposition
proofs, three transitive axiom audits, and final direct source audit pass without warnings.
It is wired into the umbrella. The source includes the global-unit inclusion, trivial
principal ray classes of units, and compatibility between the finite character and the
parity product on every global unit. See
[the formalized proof](../3-formalized/hecke-characters-split-into-finite-characters-and-real-parities.md).

### Arbitrary-dimensional Poisson summation

The corpus contains a complete three-dimensional normal-periodization argument in
`RHTower/ChiCompactLatticePoisson.lean`, and an unconditional Schwartz version in
`RHTower/ChiCubicSchwartzPoisson.lean`. Generalizing the coordinate type and the product
majorant supplies the analytic Poisson theorem required for arbitrary ideal lattices.
See [the formalized proof](../3-formalized/schwartz-poisson-summation-in-arbitrary-dimension.md).
The general periodization, Schwartz decay, Fourier identification, and twisted identity
now pass in `HTGeometry/IntegerLatticePoisson.lean` and
`HTGeometry/SchwartzPoissonSummation.lean`. Five transitive axiom audits are clean.
Both required oleans are built. Both new modules and the original three-dimensional
specialized wrappers pass final direct source audits without warnings. The Schwartz proof reuses
`HTGeometry.CombinationModeDiophantineDivisor.summable_prod_pi`.
`FinitePiProductSummability` has a private general product lemma with raised limits;
it is not needed for this route. `GL3EpsteinContinuation` is another concrete ternary
theta/Mellin model, not an arbitrary-number-field continuation theorem.

The [affine-lattice extension](../3-formalized/poisson-summation-on-affine-lattices.md) is
formalized in `HTGeometry/AffineLatticePoisson.lean`: pull back a translated Schwartz
function along an invertible linear map, prove the determinant/adjoint Fourier formula by
change of variables, and apply integer-lattice Poisson summation. Physical and dual absolute
convergence are explicit. Three transitive axiom checks and the final direct source audit
pass without warnings. It is wired into the umbrella; its olean has been built for the
written Gaussian-theta consumer.

[Gaussian theta inversion for full lattices](../3-formalized/gaussian-theta-inversion-for-full-lattices.md)
is formalized. `HTGeometry/GaussianLatticeTheta.lean` proves normal convergence, the exact
Gaussian Fourier formula, and normalized real theta inversion for every full lattice,
including dimension zero. Its final direct source audit and four exported-theorem axiom
audits pass; the olean is built for the characteristics consumer.

Additional primary-source leads: Mathlib's `Gaussian.FourierTransform` proves
`fourier_gaussian_innerProductSpace` in arbitrary finite-dimensional real inner-product
spaces. `DedekindDomain/Different` defines the trace dual of a fractional ideal and proves
`FractionalIdeal.mem_dual`. `CanonicalEmbedding/FundamentalCone` links its logarithmic map
to the unit embedding; `Units/Regulator` and `CanonicalEmbedding/NormLeOne` supply the
unit lattice and its fundamental domain. These require the actual number-field theta
construction and dual-ideal identification; none is a full Hecke functional equation.
Several Mathlib searches returned partial/interrupted text retrieval, so empty outputs
must not be treated as absence results.

For the eventual ideal-series Mellin identity, `exists_integral_rep` already supplies an
integral representative of each ordinary ideal class prime to the chosen modulus.
`IdealsOfARayClassAreConePoints.card_integerSet_eq` uses Mathlib `integerSetEquiv` to
identify cone generators with principal ideals times roots of unity, and
`ncard_rayClassIdeals_mul_torsionOrder` specializes this to ray-class ideals. The exact
equivalence can support weighted summation; the existing theorem is a cardinality identity,
not yet the required theta/Mellin unfolding.

The corpus supplies the one-dimensional `GaloisForLFunctions.gaussianSchwartz` in
`HTGeometry/GaussianSchwartz.lean`. No multidimensional Gaussian Schwartz object was
located in the completed short searches. The raw normal-periodization theorem and the
affine extension's unconditional Fourier covariance now apply directly to Gaussian
kernels using the proved normal-convergence bounds. No multidimensional Schwartz
representative is assumed.

### Gaussian theta with shifts and phases

[Theta with characteristics](../3-formalized/gaussian-theta-with-lattice-shifts-and-phases.md)
is formalized in `HTGeometry/GaussianThetaCharacteristics.lean`. It proves affine Gaussian
normal convergence, Fourier modulation/covariance, absolute convergence on both lattices,
and the exact shifted/phased theta identity. Three axiom audits and the final direct source
audit pass without warnings. It is wired into the umbrella; no olean is needed yet.
The completed characteristics scratch has been removed. Arithmetic ideal duality,
real parity factors, finite multiplicative-character transforms, and unit integration
remain open.

### Arithmetic trace-duality sources

The corpus already has `HTGeometry/NumberFieldMixedRealCoordinates.lean`, whose real
linear equivalence splits each complex place into real and imaginary coordinates.
It has no `√2` weighting; that must be added for the trace-compatible Euclidean metric.
`HTGeometry/DualZLatticeCovolume.lean` proves intrinsic dual lattices, dual bases,
`dual_rowLattice`, and inverse covolumes. `NumberFieldUnitPlaceLog.lean` proves
`numberFieldEmbeddingSum_eq_placeSum` by summing over fibers of `InfinitePlace.mk` and
using `card_filter_mk_eq`; the same fiber method can regroup real parts of embeddings.
Mathlib `trace_eq_sum_embeddings` (`RingTheory/Trace/Basic.lean`) identifies
field trace with a sum over algebra embeddings. `FractionalIdeal.mem_dual`
(`RingTheory/DedekindDomain/Different.lean`) characterizes nonzero fractional-ideal
trace duals by integral trace pairings. These are source-checked leads, not yet the
required theorem identifying Euclidean dual ideal lattices.

Mathlib already proves `mixedEmbedding.covolume_idealLattice` for every nonzero fractional
ideal: `absNorm(I) * 2^(−r₂) * sqrt(abs(discr K))`. Applying `√2` to both real coordinates
at each complex place multiplies volume by `2^r₂`, giving the desired trace-normalized
covolume. `FractionalIdeal.dual_eq_mul_inv`, `dual_mul_self`, and `dual_dual` identify the
trace dual algebraically as `dual(1) * I⁻¹` and prove involution. Its exact identification
with the Euclidean dual of the weighted mixed ideal lattice is now formalized below.

`InfinitePlace.embedding_mk_eq` states that the chosen embedding of a place represented
by `σ` is either `σ` or its complex conjugate. Hence real parts are constant on the
fibers used above. The completed search JSON scratch files have been removed after
preserving the useful declarations and source locations here and on the theta cards.

The precise weighted trace-pairing target is recorded on
[number-field trace pairing](../3-formalized/number-field-trace-pairing-in-weighted-real-coordinates.md).
The weighted trace-pairing theorem is formalized. `HTGeometry/NumberFieldTraceCoordinates.lean`
passes its final direct source audit and four axiom audits without warnings. It is wired
into the umbrella; its olean is built for the written ideal-duality consumer.
[Ideal-lattice trace duality](../3-formalized/weighted-ideal-lattices-have-the-arithmetic-trace-dual.md)
is formalized in `HTGeometry/NumberFieldIdealTraceDuality.lean`. The intrinsic integer
dual is exactly the conjugated weighted embedding of `FractionalIdeal.dual ℤ ℚ I`.
Its complete scratch, final direct source audit, and two transitive axiom audits pass
without warnings; it is wired into the umbrella. The olean is built for the
written covolume consumer. The [weighted covolume normalization](../3-formalized/weighted-ideal-lattice-covolume-is-norm-times-root-discriminant.md)
is formalized in `HTGeometry/NumberFieldIdealCovolume.lean`: the actual weighted ideal
lattice has covolume `absNorm(I) * sqrt(abs(discr K))`. Its complete scratch, final
direct source audit, and three transitive axiom checks pass without warnings.
It is wired into the umbrella; its olean is needed by the newly written arithmetic
theta consumer and is built.
[Intrinsic dual-lattice Gaussian summation](../3-formalized/gaussian-poisson-sums-over-intrinsic-dual-lattices.md)
is formalized in `HTGeometry/IntrinsicLatticeTheta.lean`. It identifies the inverse-adjoint
parametrization with the intrinsic integer dual, computes the actual covolume, and
reindexes theta over actual lattice subtypes. Its complete scratch, final direct source
audit, and three axiom checks pass without warnings; it is wired into the umbrella.
Its olean is built for the written arithmetic consumer.
The [actual fractional-ideal theta theorem](../3-formalized/fractional-ideal-theta-inversion-with-arithmetic-normalization.md)
is formalized in `HTGeometry/NumberFieldIdealTheta.lean`. It proves summability and
`θ_I(t) = (absNorm(I) sqrt(abs(discr K)))⁻¹ t^(-[K:ℚ]/2) θ_(dual I)(1/t)`
over actual ideal elements. The complete scratch, final direct source audit, and two
transitive axiom checks pass without warnings. It is wired into the umbrella; its
olean is built for the written archimedean-theta consumer. The next exact target is
[archimedean place scaling](../3-formalized/ideal-theta-under-archimedean-place-scaling.md), supported by
[positive diagonal lattice duality](../3-formalized/positive-diagonal-images-of-dual-lattices.md),
which now passes its complete scratch, final direct source audit, and both axiom checks.
`HTGeometry/NumberFieldScaledIdealTheta.lean` now proves scaled actual lattices,
determinant, duality, covolume, actual-ideal reindexing, summability, inversion, the
weighted place-norm formula, and global-unit log periodicity. Its complete scratch
and final direct source audit pass without warnings. The three main theta theorems
and both updated diagonal-helper theorems audit to standard axioms only. It is wired
into the umbrella; its olean is built for the written
[uniform exponential-tail consumer](../3-formalized/ideal-theta-tails-decay-uniformly-on-bounded-place-profiles.md).
`HTGeometry/NumberFieldIdealThetaDecay.lean` now proves a positive actual-ideal
minimum, the profile-dependent norm comparison, zero-term removal, and uniform
exponential decay for all upper-bounded place profiles. Its complete scratch and
final direct source audit pass without warnings, and its transitive axiom audit
is standard only. It is wired into the umbrella; no olean is needed yet.
The [parity Gaussian theorem](../3-formalized/parity-weighted-gaussian-poisson-summation.md)
is formalized. The supporting
[Euclidean coordinate-product Fourier identity](../3-formalized/coordinate-products-factor-under-euclidean-fourier-transform.md)
is formalized in `HTGeometry/CoordinateProductFourier.lean`, with clean complete
scratch, final source, and both axiom audits. It is wired into the umbrella; its
olean is built, as is the required `GaussianThetaCharacteristics` olean.
`HTGeometry/ParityGaussianPoisson.lean` proves the scalar and finite-coordinate
parity transforms, the half-rate Gaussian majorant, normal convergence, absolute
affine and dual summability, and the normalized shifted/phased Poisson identity.
Its complete scratch and final direct source audit pass without warnings; all five
transitive axiom audits are standard only. It is wired into the umbrella; its olean is built for the written arithmetic
Hecke-theta consumer. The completed scratch is removed.

The next arithmetic step is to extend the actual finite residue character by zero
on nonunits and combine it with the actual real parity profile. Mathlib
`MulChar.ofUnitHom` and `ofUnitHom_coe` are source-inspected. The existing
`finite_character_mul_parities_globalUnit` already proves the exact global-unit
compatibility of the two characters. `signAtInf_apply` identifies each sign with
the sign of the chosen real embedding.

The completed primitive-Gauss corpus query returned `ZMod` and prime-power local
formulas. Mathlib `gaussSum_mulShift_eq` is valid over every finite commutative ring,
but `gaussSum_mul_gaussSum_eq_card` in `NumberTheory/GaussSum.lean` assumes the source
ring is a field. The nonunit vanishing theorem found is for Dirichlet characters
over `ZMod`. These do not yet prove the needed primitive transform over arbitrary
number-ring residue rings. That arithmetic input, unit-domain integration, and
the exact Hecke Mellin unfolding remain open. HL6, HL7 and CFT remain open.


[Actual Hecke-weighted ideal theta](../3-formalized/finite-hecke-weights-give-unit-periodic-ideal-theta.md)
is now formalized in `HeckeLFunctions/HeckeIdealThetaIsUnitPeriodic.lean`.
It extends the actual finite residue character by zero on nonunits, identifies
its actual real parity profile, proves the finite/infinite global-unit
cancellation in the scaled kernel, proves absolute summability on every integral
ideal, and proves unit-log periodicity of the actual theta sum. The complete
scratch and four transitive axiom audits pass; the final direct source audit is
clean. The module is wired into the Hecke umbrella, and its completed scratches
are removed. Its olean is built for the written ideal-coset and affine-parity consumers. The character-splitting and parity-Poisson dependency oleans are built.

The next exact target is the
[finite residue-coset Poisson transform](../3-formalized/hecke-ideal-theta-as-finite-parity-poisson-sums.md).
The existing `residueRep`, `residueRep_mem`, and `mk_residueRep` already give
representatives in a coprime ideal for every residue. The intrinsic parity theorem and physical/dual absolute summability are now
formalized in `HTGeometry/IntrinsicParityPoisson.lean`; its complete scratch,
three transitive axiom audits, and final direct source check pass. It is wired
into the umbrella and its completed scratch is removed. Two current scratches
hold the actual affine ideal parity Poisson formula and the residue/ideal coset
equivalence. Their required dependency oleans are being built. These
inputs do not yet discharge primitive Gauss evaluation or Mellin unfolding.


The finite residue-coset transform is now formalized in
`HeckeLFunctions/HeckeThetaHasAFiniteFourierTransform.lean`. It proves the actual
coset equivalence, integral/fractional reindexing, affine parity transform with
arithmetic trace phases, the finite Fourier coefficient bound by `N(𝔪.fin)`,
and the full weighted ideal theta transformation with an absolutely convergent
dual series. The complete scratch and final direct source audit are clean;
nine transitive axiom checks are standard only. The module is wired into the
Hecke umbrella, no olean is needed yet, and its completed scratch is removed.
The intrinsic-parity and unit-periodic-Hecke dependency oleans are built.

Completed searches for unit-domain Mellin unfolding and Hecke conductors returned
scalar Mellin identities, unit-log definitions, and Dirichlet-character conductor
results, but no matching actual-number-field unfolding or ray-character conductor
in those returned results. This is not a claim of absence. Exact finite primitive
Gauss evaluation, unit-domain integration, completed continuation, and the primitive
functional equation remain open, as do HL6's real characters and CFT.


The next active analytic card is
[zero modes and uniform exponential tails](../3-formalized/hecke-theta-zero-modes-and-uniform-exponential-tails.md).
Its scratch already proves uniform exponential decay of the sum of nonzero
parity-Gaussian norms for every actual nonzero fractional ideal and bounded
place profiles. Physical/dual zero-mode classification and the actual weighted
applications are in progress. The finite-Fourier and unweighted-tail oleans
are now built for this written consumer. Unit-domain Mellin unfolding and
primitive arithmetic Gauss evaluation remain open.


Zero modes and actual physical/dual uniform exponential tails are now fully
formalized in `HeckeLFunctions/HeckeThetaTailsDecayExponentially.lean`. The
complete scratch, six transitive axiom audits, and final direct source check
pass without warnings. The source is wired into the umbrella and its completed
scratch is removed. Its olean is being built for the written measurability
consumer. The active next card is
[theta Mellin continuation and actual unit unfolding](hecke-theta-mellin-continuation-and-unit-unfolding.md),
which records the exact unresolved analytic and arithmetic inputs and a
normalization derivation explicitly marked unproved. The current scratch is
`/tmp/HeckeThetaMeasurabilityScratch.lean`.


[Actual theta Mellin continuation](../3-formalized/actual-hecke-theta-mellin-continuation.md)
is now formalized in `HeckeThetaHasMellinContinuation.lean`: actual local
integrability, fully discharged Mellin-pair construction, continuation,
functional equation, both residues, and entire continuation for nonzero
parity. Seven transitive axiom audits are standard only; the final direct
source audit passes without warnings. It is wired into the Hecke umbrella.
The tail dependency olean is built, and this module's olean is being built
for `/tmp/HeckeThetaJointContinuityScratch.lean`.

The active unfolding card now records Mathlib's actual unit-log quotient by
torsion, full unit lattice, and fundamental-cone ideal-element equivalences.
Its weighted logarithmic coordinates alter the proposed unfolding scalar;
the exact Jacobian and Gamma normalization remain explicitly unproved.
Next: joint theta continuity, actual unit-domain averaging and unfolding.
This closes neither full Hecke continuation nor HL6, HL7, or CFT.


[Joint continuity of actual Hecke theta](../3-formalized/hecke-theta-joint-continuity-on-positive-parameters.md)
is now formalized and source/axiom audited. Both physical and finite-Fourier
series have actual uniform summable Gaussian majorants on positive parameter
strips and bounded profile regions. Its consumer olean is built and scratch
removed. The next geometric unit-domain source is written and in final audit;
the actual unit-averaging/Mellin consumer is written but not yet compiled.


[The actual unit logarithm domain](../3-formalized/actual-unit-log-domain-and-regulator-volume.md)
is now formalized in `HTGeometry/NumberFieldUnitLogFundamentalDomain.lean`.
It identifies the weighted profile conversion, actual lattice tiling, exact
regulator volume, compact closure, and uniform coordinate bound. Five main
transitive axiom checks are standard only, and the final direct source audit
is clean. Its required olean is building for the written unit-average consumer;
the completed scratch is removed. The averaged Mellin construction itself
has not yet been checked. Full Hecke continuation, HL6, primitive FE, and CFT
remain open.


[Actual unit-averaged theta Mellin continuation](../3-formalized/actual-unit-averaged-hecke-theta-mellin-continuation.md)
is now formalized in `HeckeThetaAveragesOverTheUnitDomain.lean`. The actual
unit integrals are continuous, have regulator-scaled zero modes and exponential
tails, and satisfy a fully discharged Mellin functional-equation pair with
explicit residues. Six transitive checks are standard only; the complete
scratch and final direct source audit are clean. The umbrella is wired and
the scratch removed. No new olean is needed yet.

The next actual target is the unrestricted nonzero ideal-element/global-unit
bijection, followed by absolute Tonelli/Fubini and exact Gamma/ideal-series
unfolding. Full Hecke continuation, primitive FE, real-character HL6, and CFT
remain open.


### Exact ideal and unit indexing for HL7

`HeckeLFunctions/NonzeroIdealElementsAreGlobalUnitOrbits.lean` now identifies
nonzero elements of each actual nonzero integral ideal `b` with inverse-class
integral ideals times global units. Its inverse sends `(I,u)` to `u*g_I`,
with `(g_I)=I*b` and `|Norm(g_I)|=N(I)N(b)`. Four transitive axiom audits and
the final source check passed.

`HTGeometry/NumberFieldUnitsAreTorsionTimesLogLattice.lean` now identifies
actual global units with their torsion subgroup times the actual unit
logarithm lattice. It retains the exact fundamental-unit product and the
exact logarithm of both directions. Three transitive axiom audits and the
final source check passed. Both modules are wired into their umbrellas.

The weighted theta reindexing and absolutely integrable unit-domain
unfolding are written in separate scratch files, not yet claimed as proved.
HL7 still requires the exact Gamma/Mellin identification with the actual
Hecke ideal series, ordinary-class residue cancellation, and primitive
finite-Fourier/Gauss normalization. HL6 real-character nonvanishing and CFT
remain open; these algebraic indexing results do not close those gates.


The exact series unfolding is now formalized in
`HeckeThetaUnitOrbitsAreLogPeriodizations.lean`: the nonzero actual ideal
theta is a torsion-weighted sum over inverse-class ideals and actual
logarithmic-lattice translates. Unit-orbit, lattice, and full class/unit
families have proved absolute convergence. Three transitive axiom audits and
the final source check passed. Integral unfolding is the current scratch;
radial Mellin/Gamma identification and primitive functional-equation
normalization remain open.


The fixed-parameter unit-domain unfolding is now fully formalized in
`HeckeUnitOrbitsUnfoldOverTheLogSpace.lean`. The actual averaged theta minus
its regulator-weighted zero mode equals the exact torsion order times the
sum over inverse-class ideals of whole-log-space kernel integrals. Whole-space
integrability and both infinite exchanges follow from the actual summable
Gaussian majorant; no analytic premise is added. Three transitive axiom
checks are standard-only, and the final direct source audit passed without
warnings. The card is now
`3-formalized/hecke-unit-domain-unfolding-is-absolutely-integrable.md`.
Earlier scratch-status paragraphs are superseded. The next bridge is the
exact radial/logarithmic Jacobian and Gamma evaluation, followed by the
arithmetic coefficient identity and absolutely convergent ideal-series
Mellin exchange. Full Hecke continuation/primitive functional equation and
class field theory are still unfinished.

The exact radial/logarithmic measure conversion is now audited in
`HTGeometry/NumberFieldRadialLogarithmicJacobian.lean`. Its pushforward density
is `2^r₂/[K:Q]`, and it preserves absolute integrability, with exact complex
and nonnegative integral identities. Seven transitive axiom checks are
standard-only; final direct source audit passed without warnings. Card:
`3-formalized/hecke-radial-logarithmic-jacobian.md`.
The Gamma-factor and actual kernel/ideal-series identification remain active
on `hecke-archimedean-mellin-integrals.md`; full HL7 is not yet closed.

The Gamma and principal-ideal coefficient bridges are now complete:
`HeckeGammaFactorsAreArchimedeanMellinIntegrals.lean` proves the actual
Gamma product, convergence, exact normalization `1/(degree*2^unitRank)`,
nonvanishing on `Re s>0`, and entire reciprocal.
`HeckeThetaWeightsArePrincipalIdealCharacters.lean` identifies finite
weights times parity signs with principal-ideal Hecke values, including
noncoprime zeros, and gives the chosen inverse-class generator coefficient.
Both final source audits passed without warnings; eight main transitive
axiom checks are standard-only. Stage-3 cards record their exact statements.
The actual element Mellin identity is now written in
`/tmp/HeckeElementMellinScratch.lean`, awaiting its first check after the
Gamma dependency olean finishes. Absolute ideal-series exchange, ordinary
class residue cancellation, primitive Gauss/conductor normalization, HL6
real-character nonvanishing, and CFT remain open.


Actual element and ideal-class Mellin unfolding are now fully formalized in
`HeckeElementKernelsHaveExactMellinIntegrals.lean` and
`HeckeUnitAveragedMellinIsTheIdealClassSeries.lean`. Exact norm-integral
factorization gives summable absolute class masses and justifies the infinite
exchange. The continued unit-theta transform agrees with its inverse-class
ideal series on the full `Re s>1` domain. Both direct audits passed; nine
main transitive axiom checks are standard-only.

`UnramifiedHeckeCharactersDescendToIdealClasses.lean` is also finalized:
actual ordinary-class descent, nontrivial class-character orthogonality,
and entire unit theta transforms for nontrivial finite weight. Its three
axiom audits and direct source check passed. All modules are wired into the
Hecke umbrella. The new active global-continuation card records finite
class recombination and removable-pole construction. Primitive functional
equation normalization, real-character HL6, and CFT remain unfinished.

### Finite global class recombination

The actual absolutely convergent ideal series now partitions by ordinary
class using integral inverse-class representatives prime to the modulus.
`HeckeLSeriesAreFiniteSumsOfClassThetaTransforms.lean` identifies the
normalized finite theta sum with `GammaFactor * heckeL` on `Re s>1`.
Its entire reciprocal Gamma product gives the actual L-continuation;
nontrivial finite weight or nonzero parity makes it entire immediately.
The complete scratch and three axiom audits pass with standard axioms only;
the required consumer olean has been built. See
[the proof card](../3-formalized/hecke-l-series-as-finite-class-theta-sums.md).
The unramified removable-pole proof remains under verification.

For real-character nonvanishing, a positive occupation expansion of the
product with the trivial character is recorded on
[the Landau card](../3-formalized/real-hecke-characters-nonvanishing-by-positive-occupations.md).
It uses one doubled-frequency particle at a negative prime and two ordinary
particles at a positive prime, giving coefficient one for every occupation.
The general-frequency Landau theorem already supports arbitrary index types.

### Global continuation completed

[Full global continuation](../3-formalized/hecke-global-continuation-from-ordinary-classes.md)
is formalized in `HeckeLFunctionsHaveGlobalContinuation.lean`. The actual
`heckeLFunction` agrees with the original series on `Re s>1`, is meromorphic
on all of `C`, and is entire for every nontrivial character. The trivial
character has meromorphic order `-1` at one, exact residue `heckeDensity`,
and no other poles. Entire divided differences fill the removable theta
quotients; comparison with the older near-one continuation identifies the
residue without circularity. The identity theorem identifies both
continuations throughout the old half-plane and transfers nonquadratic
nonvanishing. Seven main transitive axiom audits are standard-only, and
the final direct source audit passes without warnings. The module is wired
into the umbrella. The remaining HL7 work is the primitive completed
functional equation, including finite Gauss and conductor normalization.
