# Estermann lane — working log

Route-level record for the twisted divisor sum. Object-level facts extracted from this work are
MUST-382 / CANNOT-383 / CANNOT-384 in `universal-law-field/STATUS.md`; nothing else from here
belongs there.

## Built (all axiom-clean, wired into `GaloisForLFunctions.RHTower`)

| module | content |
|---|---|
| `EstermannMeanZeroTwist` | main term `(γ − log x − 2 log q)/(qx)` is independent of the twist; `exists_bound_norm_estermann_meanZero`, `exists_bound_norm_estermann_character` |
| `EstermannProgressionOrthogonality` | `summable_estermannSmoothedTerm`; `sum_twist_eq_progression` : `∑_{a mod q} e(−ab/q) S_a = q ∑_{N≡b(q)} d(N)e^{−Nx}`, exact, every modulus |
| `EstermannPrimeProgression` | `exists_bound_norm_estermann_weighted` (main term retained); `estermannSmoothedSum_zero`; `sum_zmod_eq_add_sum_units`; `exists_bound_norm_estermann_prime_progression` |
| `EstermannScaledTwist` | `stdAddChar_scale`, `estermannCoeff_scale`, `estermannSmoothedSum_scale` : `S_{q}(d·m) = S_{q/d}(m)` |
| `EstermannGeneralProgression` | `exists_reducedMain`; `exists_bound_norm_estermann_general_progression` |
| `EstermannRightEdgeExplicit` | `divisorSquareMass`; `norm_estermannZeta_le_divisorSquareMass` (`Re s ≥ 2`, modulus-free) |
| `EstermannLeftEdgeExplicit` | `norm_estermannZeta_left_edge_le` : `≤ K q³ e^{π|t|}` |
| `EstermannLeftEdgePolynomial` | `norm_estermannZeta_left_edge_poly_le` : `≤ K q³|t|³`, `|t| ≥ 1` |
| `EstermannConvexityExplicit` | `norm_estermannZeta_left_edge_uniform_le`; `modulusNormalizer`; `norm_estermannPLTest_edge`, `norm_estermannPLTest_strip`; `norm_estermannZeta_critical_line_le` : `≤ C q^{3/2}(1+|t|)³`, every `t` |
| `EstermannSmoothedErrorExplicit` | `estermannGammaWeight`; `norm_estermannMellinIntegrand_one_le`; `norm_estermann_smoothed_error_le` : `≤ C q^{3/2} x^{−1/2}` |
| `EstermannProgressionUniform` | `reducedModulus`; `norm_estermannSmoothedSum_sub_reducedMain_le`; `norm_progression_sub_main_le` : `≤ C q^{5/2} x^{−1/2}`, every modulus and residue |

## The chain

1. Main term twist-independent (character-sum collapse `∑_{c mod q} expZeta(c/q,s) = q^{1−s}ζ(s)`,
   giving `D = q^{1−2s}ζ² + q^{−s}R_a` with an `a`-free double pole), so mean-zero unit weights
   annihilate it.
2. Additive orthogonality turns the twists into the progression `N ≡ b (q)`.
3. `gcd(a,q)` sends every residue twist to a unit twist of `q/gcd`, carrying that modulus's main
   term; the prime case is the instance `c_q(b) = −1`.
4. Right edge `q⁰` (Dirichlet series, unimodular twist); left edge `q³` (functional equation, with
   the explicit `‖Γ(2+it)‖ ≤ √(2π|t|/(1−e^{−2}))·3|t|·e^{−π|t|/2}` cancelling the cosine growth).
5. Normalising by `q^{s−2}` (modulus `q^{σ−2}`, so `1` and `q^{−3}` on the two edges) makes both
   edge constants `q`-free; `‖s+2‖ ≥ (1+|t|)/2` absorbs the height. Phragmén–Lindelöf uses only the
   edge constants, so the propagated bound has no modulus in it; unwinding restores `q^{2−σ}`.
   On the critical line `‖s−1‖² = 1/4 + t²` exactly, and `(1+|t|)² ≤ 8(1/4+t²)`, so no height
   restriction is needed.
6. The error integral meets that with `‖Γ(1/2+iv)‖ ≤ √(2π)e^{−π|v|/2}`; the product is integrable
   with an absolute integral and the `x`-dependence is `‖x^{−(1/2+iv)}‖ = x^{−1/2}`.
7. `q' ∣ q` gives one constant for all twists; the `q`-fold average costs `card (ZMod q) = q`.

## Open core

Not more uniformity — see CANNOT-384. The modulus sum needs cancellation between moduli
(Kloosterman / spectral shifted-convolution input). Per CANNOT-371 the lane bounds the proportion
of zeros on the critical line, not RH.
