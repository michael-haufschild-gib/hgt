# A smooth profile carries both edge regimes

- **ID:** SMOOTH-PROFILE-BOTH-EDGE-REGIMES
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-3110/route-obstacles.md` (RH-regime row: "no profile transfer exists"; B6 profile transfer, Σ14); `walls-ledger.md` Σ1, Σ14.
- **Statement:** (i) For every `C²` profile on `[0, 1]` whose Fourier transform has no real zero, the detection edge tends to `∞` unconditionally. (ii) There is a `C^∞` nonnegative profile on `[0, 1]` with no real Fourier zero. Hence one `C^∞` profile has edge `→ ∞` unconditionally and RH ⇔ positivity on `v₁^⊥` at `2(log N)^α` for every `α > 0`; without RH its hyperplane edge tends to `∞` and is `≤ 2(log N)^β` infinitely often for every `β > 0`.

## Proof

**(i) Uniform bounded-overlap positivity.** Fix `K ≥ 1`. The tilted-spline argument uses the
profile only through three uniform inputs on `1 ≤ c ≤ K`, each available without real Fourier
zeros:
1. A Fourier floor `m > 0` on the compact band `[1, 101K]` (continuity of `φ̂` and no real zero).
   Every band `[c, 101c] ⊆ [1, 101K]`, so the high-band mass bound gives one Gamma reserve
   `(a log N − b)‖x‖²`, `a = 48m/(2πM)`. The ordered prefix/tail split at cutoff `N/L` with
   `L ≫ K/δ` converts it into a Gamma payment of the log counterterm at defect cost `1 − δ/2`;
   the arithmetic overlap energy bound then gives one complete defect reserve
   `a' D_N(x) − C‖x‖² ≤ W_{φ,c,N}(x)` for all `c ∈ [1, K]`.
2. Ramanujan quasimodes with residual `≤ ε` uniformly on `[1, K]` (already general).
3. The conductor floor `(2/M) ∫_{t>K} |φ̂|² > 0`, a common lower bound for every completed
   conductor energy at every `c ≤ K`.
A unit vector of energy `≤ b` has bounded defect, so it has mass `≥ 1/18` on one finite conductor
family; a low eigenvector is orthogonal to the upper spectrum, so its coordinates on that family
are `≤ ε/δ` each, a contradiction for small `ε`. So eventually every eigenvalue on `[1, K]` is at
least half the conductor floor. Applying this with `K = n + 1` puts `edge ≥ n + 1` eventually.

**(ii) Tilting a bump off its zeros.** Let `b` be the smooth bump on `[0, 1]`. Then
`∫ e^{λu} b(u) e^{iru} du = b̂(r − iλ)`. `b̂` is entire and `b̂(0) = ∫ b > 0`, so its zero set is
codiscrete-complement, finite on each closed disc, hence countable; its imaginary parts form a
countable subset of `ℝ`. Choose `μ` outside it and `λ = −μ`: `e^{λu} b(u)` is `C^∞`, nonnegative,
supported in `[0, 1]`, with positive mass and no real Fourier zero.

**Both regimes.** Apply (i) to this profile, the every-power hyperplane receivers for smooth
nonnegative profiles, and `edge ≤ hyperplaneEdge`.

## Lean

- `CriticalArithmeticCorrelationTheory/EveryProfileWithoutRealFourierZerosIsUniformlyPositiveOnBoundedOverlap.lean`:
  `exists_noRealZero_common_fourier_floor`, `exists_noRealZero_archForm_uniform_overlap_reserve`,
  `exists_noRealZero_gamma_uniform_overlap_payment`, `exists_noRealZero_complete_uniform_overlap_reserve`,
  `exists_noRealZero_completeWeilEnergy_uniform_overlap_reserve`,
  `noRealZero_completedConductorEnergy_ge_boundedOverlapTail`,
  `eventually_noRealZero_eigenvalues_ge_uniformly_above_touching`,
  `eventually_noRealZero_completeWeilMatrix_posDef_uniform_overlap`.
- `EdgeHodgeTheory/ASmoothProfileCarriesBothEdgeRegimes.lean`: `tendsto_edge_of_noRealZero`,
  `tendsto_hyperplaneEdge_of_noRealZero`, `exists_horizontal_line_free_of_zeros`,
  `paperFT_exp_tilt`, `exists_smooth_profile_noRealZero`,
  `exists_smooth_profile_with_both_edge_regimes`.

Both modules pass `lake --old env lean`; `#print axioms` for `tendsto_edge_of_noRealZero` and
`exists_smooth_profile_with_both_edge_regimes`: `propext`, `Classical.choice`, `Quot.sound`.
Wired into `CriticalArithmeticCorrelationTheory.lean` and `EdgeHodgeTheory.lean`.

## Scope

The universal regime here is qualitative (`edge → ∞`); the explicit `(log N)^{1/144}` rate remains
tilted-spline specific. The full-space every-power receiver for smooth profiles is not claimed.

## Gates

- [x] Uniform bounded-overlap positivity for every profile without real Fourier zeros.
- [x] Existence of a `C^∞` nonnegative profile without real Fourier zeros.
- [x] Both regimes on one profile; direct checks and standard axiom closures.
