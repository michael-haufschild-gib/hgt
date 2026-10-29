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

The user paused the programme and authorized closing existing work only.
That closeout is complete: all seven Hecke gates are formalized, audited,
and wired. Existing proof drafts and paper proofs are closed; scratch
files are removed. The programme remains paused before CFT. No CFT work
was started during closeout.

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
- [x] HL6 nonvanishing on `Re s ≥ 1` for every character, away from the trivial pole —
      `heckeLFunction_ne_zero_of_one_le_re`, `heckeLCont_one_ne_zero`, `heckeLCont_ne_zero`;
      prime-power and prime-ideal Mertens sums are bounded for nontrivial characters and
      `log N+O(1)` for the trivial character — `exists_norm_heckePrimeMertensSum_le`,
      `exists_norm_heckePrimeMertensSum_one_sub_log_le`
- [x] HL7 global continuation, exact pole classification, actual ideal-lattice Poisson summation,
      primitive conductor/Gauss arithmetic, both actual Mellin identities, and completed functional
      equation — `heckeCompletedLFunction_reflection`,
      `heckeCompletedLFunction_reflection_entire`, `heckePoleClearedCompletion_reflection`,
      `norm_heckeRootNumber`; see
      [the completed equation](../3-formalized/primitive-hecke-l-functions-have-completed-functional-equation.md),
      [dual unfolding](../3-formalized/hecke-dual-theta-unfolding-over-fractional-ideal-classes.md), and
      [completed residues](../3-formalized/hecke-unramified-character-descent-and-residue-cancellation.md)

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

## Formalized proof cards

- [Hecke theta Mellin continuation and unit unfolding](../3-formalized/hecke-theta-mellin-continuation-and-unit-unfolding.md)
- [Unramified descent and completed Hecke residue cancellation](../3-formalized/hecke-unramified-character-descent-and-residue-cancellation.md)
- [Hecke prime-ideal Euler products and positive residues](../3-formalized/hecke-prime-ideal-euler-product-and-positive-residue.md)
- [Nonquadratic Hecke characters have no zeros on Re(s) ≥ 1](../3-formalized/nonquadratic-hecke-characters-have-no-zeros-on-re-ge-one.md)
- [Finite residues and real signs have integral representatives](../3-formalized/finite-residues-and-real-signs-have-integral-representatives.md)
- [Hecke characters split into finite characters and real parities](../3-formalized/hecke-characters-split-into-finite-characters-and-real-parities.md)
- [Schwartz Poisson summation in arbitrary dimension](../3-formalized/schwartz-poisson-summation-in-arbitrary-dimension.md)
- [Poisson summation on affine lattices](../3-formalized/poisson-summation-on-affine-lattices.md)
- [Gaussian theta inversion for full lattices](../3-formalized/gaussian-theta-inversion-for-full-lattices.md)
- [Gaussian theta with lattice shifts and phases](../3-formalized/gaussian-theta-with-lattice-shifts-and-phases.md)
- [Number-field trace pairing in weighted real coordinates](../3-formalized/number-field-trace-pairing-in-weighted-real-coordinates.md)
- [Weighted ideal lattices have the arithmetic trace dual](../3-formalized/weighted-ideal-lattices-have-the-arithmetic-trace-dual.md)
- [Weighted ideal-lattice covolume is norm times root discriminant](../3-formalized/weighted-ideal-lattice-covolume-is-norm-times-root-discriminant.md)
- [Gaussian Poisson sums over intrinsic dual lattices](../3-formalized/gaussian-poisson-sums-over-intrinsic-dual-lattices.md)
- [Fractional-ideal theta inversion with arithmetic normalization](../3-formalized/fractional-ideal-theta-inversion-with-arithmetic-normalization.md)
- [Ideal theta under archimedean place scaling](../3-formalized/ideal-theta-under-archimedean-place-scaling.md)
- [Positive diagonal images of dual lattices](../3-formalized/positive-diagonal-images-of-dual-lattices.md)
- [Uniform exponential decay of ideal theta tails](../3-formalized/ideal-theta-tails-decay-uniformly-on-bounded-place-profiles.md)
- [Parity-weighted Gaussian Poisson summation](../3-formalized/parity-weighted-gaussian-poisson-summation.md)
- [Coordinate products factor under the Euclidean Fourier transform](../3-formalized/coordinate-products-factor-under-euclidean-fourier-transform.md)
- [Finite Hecke weights give unit-periodic ideal theta](../3-formalized/finite-hecke-weights-give-unit-periodic-ideal-theta.md)
- [Hecke ideal theta as finite parity Poisson sums](../3-formalized/hecke-ideal-theta-as-finite-parity-poisson-sums.md)
- [Hecke theta zero modes and uniform exponential tails](../3-formalized/hecke-theta-zero-modes-and-uniform-exponential-tails.md)
- [Actual Hecke theta Mellin continuation](../3-formalized/actual-hecke-theta-mellin-continuation.md)
- [Joint continuity of actual Hecke theta](../3-formalized/hecke-theta-joint-continuity-on-positive-parameters.md)
- [Actual unit logarithm domain and regulator volume](../3-formalized/actual-unit-log-domain-and-regulator-volume.md)
- [Actual unit-averaged Hecke theta Mellin continuation](../3-formalized/actual-unit-averaged-hecke-theta-mellin-continuation.md)
- [Hecke L-series as finite sums of actual class theta transforms](../3-formalized/hecke-l-series-as-finite-class-theta-sums.md)
- [Every Hecke L-function is nonzero on the closed right half-plane](../3-formalized/real-hecke-characters-nonvanishing-by-positive-occupations.md)
- [Global Hecke continuation from actual ordinary-class theta transforms](../3-formalized/hecke-global-continuation-from-ordinary-classes.md)
- [Hecke character Mertens bounds from the ideal hyperbola identity](../3-formalized/hecke-character-mertens-via-ideal-hyperbola.md)
- [Finite Hecke characters have primitive conductors](../3-formalized/hecke-finite-characters-have-primitive-conductors.md)
- [Primitive finite-ring characters have exact Gauss transforms](../3-formalized/primitive-finite-ring-characters-have-gauss-transforms.md)
- [Actual Hecke Fourier coefficients are Gauss sums](../3-formalized/hecke-finite-fourier-coefficients-are-gauss-sums.md)
- [Hecke Fourier support is ideal coprimality](../3-formalized/hecke-fourier-support-is-ideal-coprimality.md)
- [Exact Mellin integrals for nonzero field elements](../3-formalized/hecke-field-element-kernels-have-exact-mellin-integrals.md)
- [Actual dual Hecke kernels are unit covariant](../3-formalized/hecke-dual-theta-kernels-are-unit-covariant.md)
- [Absolute unfolding of families over the unit-log lattice](../3-formalized/number-field-log-periodizations-have-absolute-unfolding.md)
- [Exact Mellin integrals of actual dual class kernels](../3-formalized/hecke-dual-class-kernels-have-exact-mellin-integrals.md)
- [Actual dual Hecke unit orbits unfold absolutely](../3-formalized/hecke-dual-unit-orbits-unfold-over-the-log-space.md)
- [The dual averaged Mellin transform is the inverse class series](../3-formalized/hecke-dual-averaged-mellin-is-the-inverse-class-series.md)
- [Primitive Gauss sums and the arithmetic dual Hecke character](../3-formalized/hecke-primitive-gauss-sums-and-arithmetic-dual-character.md)
- [Dual Hecke theta unfolding over fractional-ideal classes](../3-formalized/hecke-dual-theta-unfolding-over-fractional-ideal-classes.md)
- [Completed Hecke theta residues cancel for nontrivial characters](../3-formalized/hecke-completed-theta-residues-cancel.md)
- [Gamma-completed Hecke functions have their removable values](../3-formalized/hecke-gamma-completed-functions-have-removable-values.md)
- [Hecke completion factors have exact arithmetic normalization](../3-formalized/hecke-completion-factors-have-exact-arithmetic-normalization.md)
- [Primitive Hecke L-functions satisfy the completed functional equation](../3-formalized/primitive-hecke-l-functions-have-completed-functional-equation.md)

All final direct source checks use `lake --old env lean`; no umbrella or
full build was run. Recorded transitive axiom audits are standard only.
