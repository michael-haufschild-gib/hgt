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
- [ ] HL6 nonquadratic nonvanishing on `Re s ≥ 1` is proved —
      `heckeLCont_ne_zero_of_sq_ne_one`; still open: real nontrivial characters at `1`
      (full continuation and Landau positivity after HL7), and Mertens for Hecke characters
- [ ] HL7 Hecke's functional equation (theta series, Poisson summation, Mellin transform)

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

The ordinary Gaussian theta theorem is complete. The next exact target is
[theta with characteristics](gaussian-theta-with-lattice-shifts-and-phases.md).
`/tmp/HeckeGaussianCharacteristicsScratch.lean` contains normal convergence for affine
lattices, modulation, exact Fourier covariance, absolute convergence of both sums, and
the full shifted/phased Poisson identity. The scratch compiles cleanly and all three
axiom audits pass. `HTGeometry/GaussianThetaCharacteristics.lean` is wired into the umbrella
and undergoing its final direct source audit.
The exported ordinary-theta axiom audits all pass. Arithmetic ideal duality and
unit integration remain open.

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
trace dual algebraically as `dual(1) * I⁻¹` and prove involution. The remaining bridge is
its exact identification with the Euclidean dual of the weighted mixed ideal lattice.

`InfinitePlace.embedding_mk_eq` states that the chosen embedding of a place represented
by `σ` is either `σ` or its complex conjugate. Hence real parts are constant on the
fibers used above. The completed search JSON scratch files have been removed after
preserving the useful declarations and source locations here and on the theta cards.

The precise weighted trace-pairing target is recorded on
[number-field trace pairing](number-field-trace-pairing-in-weighted-real-coordinates.md).
`/tmp/HeckeWeightedTraceScratch.lean` contains drafted finite-fiber and field-trace
summation lemmas; it is uncompiled. The theta-characteristics final source audit is the current
Lean check. Completed search JSON scratch files have been removed.
