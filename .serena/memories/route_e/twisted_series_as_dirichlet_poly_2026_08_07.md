# The truncated twisted series IS a corpus dirPoly (2026-08-07)

`RHTower/Sieve/TwistedSeriesAsDirichletPoly.lean` — green (9071 jobs), axiom-clean, umbrella-wired.

`sum_range_twistedSummand_eq_dirPoly (hf0 : f 0 = 0) (σ t : ℝ) (L : ℕ) :
  ∑ n ∈ range (L+1), twistedSummand f (σ + t·I) n = dirPoly L (twistedTruncCoeff f σ L) (-t)`

with `twistedTruncCoeff f σ L k = f (k+1) · ((k+1 : ℝ)^(-σ) : ℂ)`, plus
`norm_twistedTruncCoeff_le` and `sum_norm_sq_twistedTruncCoeff_le : ∑ k, ‖a k‖² ≤ ∑' n, n^(-2σ)`
(uniform in L — the quantity `volume_largeValues_le` / `DirichletIntegralMeanValue` consume).

Mechanism: the polar split `natCast_cpow_neg_eq_mul` (from `DistanceAbscissaBridge`) puts the abscissa
in the coefficients; `dirPoly` uses `+it`, so the frequency is `-t`.

## Traps

- **`conj_charFn` already exists** in `Sieve/DistanceTriangle` — do not re-prove it (I did, and the
  compiler caught the duplicate).
- The identification NEEDS `f 0 = 0`: at `σ = t = 0` the `n = 0` term is `f 0 · 0^0 = f 0`, so the
  statement is false without it.
- `Fin.sum_univ_eq_sum_range g L` needs the summand written as a function of `(k : ℕ)`; give `g`
  explicitly.
- `Finset.sum_image`'s injectivity goal arrives unbeta-reduced: `simp only [] at h` then `omega`.
- mathlib's `ring` prints a "Try this: ring_nf" suggestion when `ring1` fails but `ring_nf` closes the
  goal; exit code is 0 but the noise is worth removing by writing `ring_nf`.

Remaining on the successor task: the optimisation — feed `integral_norm_dirPoly_halasz` the damped sup
bound from `HalaszUniformDistance` and choose `V`.
