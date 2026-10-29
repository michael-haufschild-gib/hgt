# Schwartz Poisson summation in arbitrary dimension

- **ID:** hecke-poisson
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Hecke L-functions and class field theory](../1-in-progress/hecke-l-functions-and-class-field-theory-2026-10-28.md), HL7
- **Statement:** For every finite coordinate type `ι`, complex Schwartz function `f` on `EuclideanSpace ℝ ι`, and real frequency `a`,
  `Σ_k f̂(k−a) = Σ_n exp(2πi⟨n,a⟩) f(n)`.
  Both lattice sums converge absolutely; the ordinary Poisson identity follows at `a = 0`.

## Paper proof

Write `d = #ι` and `W(n) = ∏_i (1+|n_i|)`. The reciprocal-square series in one integer
coordinate converges, so `Σ_n W(n)⁻²` converges by finite product summation.
For a Schwartz function, a seminorm supplies
`(1+‖y‖)^(2d) |f(y)| ≤ C`. If the coordinate sup norm of a translation `x` is at most
`R ≥ 0` and `y = x+n`, each coordinate satisfies
`1+|n_i| ≤ (1+R)(1+‖y‖)`. Therefore

`|f(x+n)| ≤ (1+R)^(2d) C / W(n)²`.

This gives a single summable majorant for all translations in a bounded set. In particular,
the integer lattice sum and each real translate converge absolutely.

For a continuous integrable function with this normal-convergence property, periodize by
integer translations. The sum is continuous and descends to the unit torus. Integrating
over the unit cube and unfolding its translates is justified by the preceding majorant.
The torus Fourier coefficient at `k` is consequently the full-space integral against
`exp(−2πi⟨k,x⟩)`. If these coefficients are absolutely summable, the existing torus Fourier
inversion theorem reconstructs the periodization at zero, proving Poisson summation.

Apply this to `exp(2πi⟨x,a⟩) f(x)`. Its norm is `|f(x)|`, so integrability and the same
normal-convergence bound hold. Its Fourier coefficient at `k` is `f̂(k−a)` by direct
combination of the exponential factors. The Fourier transform of a Schwartz function is
Schwartz; the translated lattice estimate therefore proves absolute summability of these
coefficients. This gives the claimed twisted identity and, at zero frequency, the ordinary
identity. The measure-preserving map from coordinate space to Euclidean space identifies
the coordinate torus integrals with the Euclidean Fourier transform.

The proof also covers the empty coordinate type. No dimension positivity, compact support,
or unproved summability assumption is used in the Schwartz theorems.

## Reused work

The periodization and Schwartz arguments extend the previously proved three-dimensional
results in `RHTower/ChiCompactLatticePoisson.lean` and `RHTower/ChiCubicSchwartzPoisson.lean`.
Those files now preserve their public APIs as specializations of the shared results.
Finite product summation reuses
`HTGeometry.CombinationModeDiophantineDivisor.summable_prod_pi`, transported through
`Fintype.equivFin`. Mathlib supplies torus Fourier inversion, fundamental-domain unfolding,
the Schwartz Fourier transform, and the measure-preserving Euclidean identification.

## Lean declarations

In [IntegerLatticePoisson.lean](../../../../formal/GaloisForLFunctions/HTGeometry/IntegerLatticePoisson.lean):

- `integerPoint`, `torusProjection`
- `poisson`
- `poisson_of_summable_translates`

In [SchwartzPoissonSummation.lean](../../../../formal/GaloisForLFunctions/HTGeometry/SchwartzPoissonSummation.lean):

- `euclideanIntegerPoint`
- `schwartz_summable_translates`
- `summable_norm_integerPoint`, `summable_norm_integerPoint_add`
- `schwartz_poisson_twisted`, `schwartz_poisson`

All declarations above lie in `GaloisForLFunctions.HTGeometry.IntegerLatticePoisson`.

## Validation

Both new modules and both specialized wrappers pass final direct source audits with
`lake --old env lean`, without warnings. The two periodization results, lattice summability,
twisted Schwartz identity, and ordinary Schwartz identity pass transitive axiom audits
using only `propext`, `Classical.choice`, and `Quot.sound`. Both new modules are wired into
`HTGeometry.lean`. Their oleans were built because the written consumers import them.
No existing olean was rebuilt and no umbrella was compiled.

## Remaining Hecke input

The [affine-lattice extension](poisson-summation-on-affine-lattices.md)
is formalized with its determinant and inverse-adjoint dual frequencies.
The arithmetic dual ideal, theta coefficients, unit integration, and Mellin identity
remain separate obligations before full Hecke continuation.

## Actual-function interface

`integer_character_eq_fourier_phase` and `integer_fourier_coefficient` identify the
Euclidean Fourier samples without Schwartz assumptions. The new
`euclidean_poisson_of_summable_translates` discharges reconstruction from explicit
continuity, integrability, normal translates, and dual summability. Gaussian kernels
satisfy these conditions directly. This avoids duplicating the torus phase argument.
The extended module passes its direct source audit without warnings; its olean has
been updated for the affine and Gaussian consumers.
