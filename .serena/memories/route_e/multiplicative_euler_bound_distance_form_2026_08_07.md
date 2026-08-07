# Euler bound in distance form (2026-08-07)

Appended to `RHTower/Sieve/MultiplicativeEulerBound.lean` (green, 3379 jobs, axiom-clean):

- `primeAbscissaSum σ = ∑' p : Nat.Primes, (p:ℝ)^(-σ)`; `summable_primes_rpow_neg`.
- `mulDistSqTsum f s = ∑' p, ((p:ℝ)^(-s.re) - (twistedSummand f s p).re)` — the σ-weighted distance,
  defined as a DIFFERENCE so no polar split `p^{-s} = p^{-σ}·p^{-it}` is needed; nonnegativity is
  `Complex.re_le_norm` plus `norm_twistedSummand_le`.
- `tsum_re_twistedSummand_eq_sub` : `∑' p, Re(f p · p^(-s)) = primeAbscissaSum s.re - mulDistSqTsum f s`.
- `norm_tsum_twistedSummand_le_exp_sub_dist` : `‖F s‖ ≤ exp(primeAbscissaSum s.re - mulDistSqTsum f s + 5/2)`.

## Open next steps on this brick

1. **Bridge to the corpus's finite distance.** `Sieve/MultiplicativeDistance.mulDistSq f t P =
   ∑_{p∈P} (1 - Re(f p p^{-it}))/p` is weighted by `1/p` at `σ = 1`; mine is weighted by `p^{-σ}`.
   `Sieve/PrimeSigmaShift.abs_sum_weight_shift_le` is exactly the conversion (cost
   `(σ-1)(log z + log 4)`, free at `σ = 1 + 1/log z`). Proving
   `mulDistSqTsum f s ≥ mulDistSq f t (primesLE z) - 2(σ-1)(log z + log 4)` would let the corpus's
   PROVED uniform distance lower bounds feed the Euler bound. This needs the polar split after all
   (`Complex.cpow_add` + an `ofReal_cpow`-style cast).
2. **Quantify the main term.** `primeAbscissaSum σ ≤ log(1/(σ-1)) + C`. Route: `ZetaLogPrimeSum.
   abs_log_norm_riemannZeta_sub_tsum_re_le` at real `s = σ` gives `primeAbscissaSum σ ≤ log ζ(σ) + 2`;
   then an upper bound `ζ(σ) ≤ 1 + 1/(σ-1)` is needed. The corpus has
   `HTGeometry/ZetaGammaFieldHypertranscendence.norm_riemannZeta_le_halfPlane` with
   `zetaHalfPlaneBound c = ∑' i, 1/(i+1)^c` — so what is missing is the integral test
   `∑_{n≥1} n^{-σ} ≤ 1 + 1/(σ-1)`. NOT found in the corpus; check mathlib's
   `AntitoneOn.sum_le_integral` family before building.

See `mem:route_e/multiplicative_euler_bound_built_2026_08_07`.
