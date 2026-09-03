# Ground energies of the restricted Weil form on the pole-vanishing subspace — numerical study

- **Date:** 2026-09-03
- **Parent cards:** `1-in-progress/weil-positivity-soft-prime-entry.md` (`WEIL-ENTRY-001`),
  `3-formalized/weil-polar-ground-energy-continuity-lean.md`,
  `3-formalized/weil-polar-degeneracy-threshold-lean.md`
- **Machine:** RunPod, 16 CPU cores, Python 3.8, numpy 1.24 / scipy 1.10 / mpmath 1.3
- **Status of the numbers:** high-precision numerics with convergence control in the basis size
  and in the working precision. They are **not** interval-certified. Every Galerkin ground energy
  is an *upper bound* for the true infimum of the Rayleigh quotient (a minimum over a subspace),
  decreasing monotonically in the basis size `N`; a *positive* computed value therefore does not
  by itself certify positivity of the true infimum, while a *negative* computed value does certify
  that the true infimum is negative (up to rounding).

## 1. What was computed

Weil's quadratic form for a real test function `f` supported in `[-a, a]` of the logarithmic
variable (multiplicative support `[λ⁻¹, λ]`, `λ = e^a`), with `g(x) = ∫ f(y) f(y − x) dy` its
autocorrelation and `c_± = ∫ e^{±x/2} f(x) dx` its two pole coefficients:

```
Q(f) = 2 c_+ c_-                                        (pole terms ĥ(0) + ĥ(1))
     - 2 Σ_{n ≥ 2} Λ(n) n^{-1/2} g(log n)                (primes; only n < e^{2a} contribute)
     + (-γ - log π) g(0) + 2 ∫_0^∞ [g(0)e^{-2u} - g(u)e^{-u/2}] / (1 - e^{-2u}) du   (archimedean)
```

The archimedean term equals `∫_ℝ 2θ'(2πξ) |f̂(ξ)|² dξ` with `2θ'(t) = Re ψ(1/4 + it/2) − log π`,
which is the exact Connes–Consani–Moscovici archimedean weight used in the corpus's
`ccmRestrictedWeilSourceQuadratic`. By the explicit formula `Q(f) = Σ_ρ F(ρ) F(1 − ρ)` with
`F(s) = ∫ f(x) e^{(s − 1/2)x} dx`, so `RH ⟺ Q ≥ 0` for all `f` and all apertures.

Four ground energies (lowest Rayleigh quotient `Q(f)/‖f‖²`) were computed as functions of `a`:

| symbol | meaning |
|---|---|
| `mu_full` | `Q` on all of `L²(−a, a)` — Suzuki's lowest eigenvalue `λ_a`, Connes–Consani's minuscule eigenvalue |
| `mu0_full` | `Q` on the pole-vanishing subspace `V₀ = {c_+ = c_- = 0}` — the corpus's `ccmRestrictedWeilPolarGroundEnergy` |
| `mu0_arch` | the archimedean term alone on `V₀` (no primes) |
| `mu0_primes_le_P` | archimedean minus the primes powers `n ≤ P` only, on `V₀` |

**Method.** Galerkin on the orthonormal Legendre basis of `L²(−a, a)` (`N = 24 … 80`). The shifted
overlaps `∫ P̃_j(x) P̃_k(x − u) dx` are exact Gauss–Legendre integrals of polynomials; the
`u`-integral of the archimedean term is a Gauss–Legendre quadrature of an analytic integrand
(time-domain form, no Fourier tails); the pole vectors are Gauss quadratures of `e^{±x/2} P̃_j`.
The constrained problem projects onto the orthogonal complement of the two pole vectors. Double
precision (`weil_polar_galerkin.py`) for the sweeps and bisections; mpmath at 60–80 digits
(`weil_polar_mp.py`) for the small values.

**Checks performed** (`python3 weil_polar_galerkin.py checks`):
- time-domain versus Fourier-side assembly of the archimedean matrix (products of spherical Bessel
  functions against `2θ'`): agreement to `4·10⁻⁷`, the Fourier truncation error;
- double precision versus mpmath (30 digits) on individual matrix entries: agreement to `10⁻¹⁴`;
- indicator test function with closed-form autocorrelation: agreement to the Fourier truncation;
- convergence in `N` (see `table_convergence_in_N.csv`): `mu0_full(0.35)` = 0.53318 (N=24),
  0.53306 (36), 0.53305 (48), 0.53304 (64); mpmath 60 digits: 0.533070 (32), 0.533056 (44);
- a quadrature-exactness failure was caught and fixed: with 48 Gauss nodes the overlaps are exact
  only up to `N = 48`; `N = 56` produced garbage (`sqrt2_bad_N56.log` is kept as the record), and
  the node count now scales with `N`.

## 2. Results

### 2.1 The pole-vanishing form at √2 has a large margin

At `a = (log 2)/2 = 0.34657` (`λ = √2`, the Connes–Consani / Yoshida aperture):

| quantity | value (mpmath, 60 digits) | convergence |
|---|---|---|
| `mu0_full(√2)` | **0.547036** (N = 64) | N = 24: 0.5470582, 32: 0.5470457, 40: 0.5470408, 48: 0.5470385, 56: 0.5470372, 64: 0.5470364 (decreasing, differences shrinking geometrically; limit ≈ 0.54703) |
| `mu_full(√2)` (unconstrained) | **1.32932·10⁻³** (N = 64) | N = 24 … 64: 1.32952, 1.32941, 1.32936, 1.32934, 1.32933, 1.32932 (·10⁻³) |

So the ground energy of the pole-vanishing form at √2 is about **0.547**, with the second
constrained eigenvalue about 0.84. This is the quantity `μ₀(√2)` that Theorem C–D of the parent
card need to be positive: numerically it is positive by a margin of order one, not by the
0.3 % margin of Connes–Consani's operator comparison. (Their minuscule eigenvalue is the
*unconstrained* `mu_full ≈ 1.3·10⁻³`, which the pole term nearly cancels.)

### 2.2 The pole-vanishing full form stays positive but decays super-exponentially

`mu0_full(a)` from the 80-digit run (`mp_hp.json`, `table_hp_dps80.csv`), `N = 56`, with the
ratio of the `N = 40` value to the `N = 56` value as the convergence indicator (a ratio near 1
means the Galerkin minimum has converged; a large ratio means only an upper bound is known):

| a | λ | mu0_full (N=56) | ratio N40/N56 | mu_full (N=56) |
|---|---|---|---|---|
| 0.30 | 1.35 | 0.6920 | 1.00 | 7.57·10⁻³ |
| 0.35 | 1.42 | 0.5331 | 1.00 | 1.19·10⁻³ |
| 0.40 | 1.49 | 0.2253 | 1.00 | 1.81·10⁻⁴ |
| 0.45 | 1.57 | 6.615·10⁻² | 1.00 | 1.62·10⁻⁵ |
| 0.50 | 1.65 | 1.188·10⁻² | 1.00 | 9.36·10⁻⁷ |
| 0.55 | 1.73 | 9.207·10⁻⁴ | 1.00 | 5.33·10⁻⁸ |
| 0.60 | 1.82 | 6.658·10⁻⁵ | 1.01 | 1.62·10⁻⁹ |
| 0.65 | 1.92 | 2.326·10⁻⁶ | 1.01 | 3.99·10⁻¹¹ |
| 0.70 | 2.01 | 5.621·10⁻⁸ | 1.05 | 4.27·10⁻¹³ |
| 0.75 | 2.12 | 7.612·10⁻¹⁰ | 1.01 | 3.77·10⁻¹⁵ |
| 0.80 | 2.23 | 5.567·10⁻¹² | 1.19 | 1.72·10⁻¹⁷ |
| 0.85 | 2.34 | 2.17·10⁻¹⁴ | 3.7 | 4.4·10⁻²⁰ |
| 0.90 | 2.46 | 5.8·10⁻¹⁷ | 19 | 7.4·10⁻²³ |
| 1.00 | 2.72 | 4.5·10⁻²¹ | 760 | 1.7·10⁻²⁶ |
| 1.20 | 3.32 | 4.6·10⁻²⁷ | 2·10⁵ | 1.0·10⁻³² |
| 1.40 | 4.06 | 4.1·10⁻³³ | 1·10⁸ | 2.0·10⁻³⁷ |
| 1.60 | 4.95 | 1.3·10⁻³⁵ | 7·10⁸ | 6.4·10⁻⁴¹ |

Every computed value is positive, at every `N` and every precision. The values are converged
(ratio ≤ 1.05) up to `a = 0.75` (`λ = 2.12`), marginal at `a = 0.80`, and beyond `a ≈ 0.85`
they are still decreasing steeply with `N`, so only upper bounds for the true infimum are known
there; the decay is the "exponential of exponential" decay Connes–Consani describe. Consequence
for the parent card: **no threshold aperture `a*` is visible up to `λ ≈ 5`**, positivity of the
pole-vanishing form is confirmed with a resolved margin up to `λ ≈ 2.1` (`mu0_full(0.75) =
7.6·10⁻¹⁰`, stable in `N`), and an explicit `λ₁` beyond which positivity could fail cannot be
located numerically because the ground energy tends to zero without changing sign.

### 2.3 The archimedean term alone is indefinite beyond λ ≈ 1.81 (prime necessity)

Bisection (`thresholds.json`, `N = 48, 64, 80` agree to `10⁻⁵`):

| form on `V₀` | sign change at `a` | `λ = e^a` | autocorrelation support `S = 2a` | first excluded prime power and its entry `a = (log n)/2` |
|---|---|---|---|---|
| archimedean only | **0.595815** | **1.81451** | 1.19163 | — |
| archimedean − prime 2 | 0.565803 | 1.76086 | 1.13161 | `n = 3` enters at 0.549306 |
| archimedean − primes 2, 3 | 0.702542 | 2.01888 | 1.40508 | `n = 4` enters at 0.693147 |
| archimedean − primes 2, 3, 4, 5 | between 0.95 and 1.00 (80-digit scan) | ≈ 2.7 | | `n = 7` enters at 0.972955 |
| archimedean − primes ≤ 7 | between 1.00 and 1.05 (80-digit scan: −7.6·10⁻⁵ at 1.05) | ≈ 2.8 | | `n = 8` enters at 1.039721 |

Readings.

1. The archimedean form alone is positive on the pole-vanishing subspace up to `λ_arch = 1.8145`
   and negative beyond. Yoshida's and Connes–Consani's archimedean positivity at `λ = √2 = 1.414`
   is therefore not sharp for the archimedean term: it survives to 1.81 without any prime. Beyond
   1.81 Weil positivity needs the primes.
2. A truncated form (primes up to `P`) fails shortly after the first excluded prime power enters:
   the form without the prime 3 fails at `a = 0.5658`, which is `0.0165` past the entry of 3;
   the form without the prime power 4 fails at `a = 0.7025`, which is `0.0094` past the entry
   of 4; the form without 7 fails between 0.95 and 1.00 (7 enters at 0.973), the form without 8
   fails between 1.00 and 1.05 (8 enters at 1.040). Each prime power is needed almost immediately
   once it enters. This is the quantitative face of the log-soft entry law of the parent card: at
   the entry point the new term is harmless, and within about `0.01`–`0.02` of aperture it
   becomes decisive.
3. Adding the prime 2 *lowers* the constrained ground energy (at `a = 0.35`, 0.5372 without the
   prime 2 versus 0.5331 with it), while the later primes raise the truncated ground energies back
   to the full-form value: at `a = 0.8`, `mu0_primes_le_2 = −0.25`, `mu0_primes_le_3 = −0.10`,
   `mu0_primes_le_5 = +5·10⁻¹² = mu0_full`. The prime terms do not have a fixed sign; they
   conspire.

### 2.5 Fourier zeros of the ground states versus the zeta zeros (`spectral_zeros.json`)

Connes–Consani–Moscovici observed that the Fourier transform of the lowest eigenvector of the
full restricted Weil form has real zeros that approach the ordinates of the zeta zeros as the
aperture grows (their spectral realization of the ultraviolet regime). Here the same is done for
the ground state of the pole-vanishing form (`spectral_zeros.py`; `F(1/2 + it)` of the eigenvector
evaluated through spherical Bessel functions, real zeros by bisection on `[0, 80]`). Both ground
states are even at every aperture computed. First four Fourier zeros against `γ₁…γ₄ =
14.1347, 21.0220, 25.0109, 30.4249`:

| a | λ | full form: zeros | pole-vanishing form: zeros |
|---|---|---|---|
| 0.35 | 1.42 | 14.332, 22.616, 31.032, 39.540 | 19.486, 28.290, 37.127, 45.987 |
| 0.50 | 1.65 | 14.135, 21.055, 25.196, 31.356 | 14.251, 21.716, 26.984, 32.668 |
| 0.70 | 2.01 | 14.1347, 21.0220, 25.0109, 30.4249 (next: 32.937, 37.603, 41.054) | 14.1347, 21.0220, 25.0116, 30.441 (next: 32.986, 37.750, 41.626) |
| 0.90 | 2.46 | first eight zeta zeros to `< 10⁻³` | first eight zeta zeros to `< 10⁻³` |
| 1.10 | 3.00 | first eight zeta zeros to `< 10⁻³` | first eight zeta zeros to `< 10⁻³` |
| ≥ 1.30 | ≥ 3.7 | zeta zeros retained, extra zeros appear between them (e.g. 32.41 at a = 1.3) | same, with fewer extras at a = 2.1 |

Readings.

1. The pole-vanishing ground state also converges to the spectral realization: by `a = 0.9`
   its Fourier zeros reproduce the first eight zeta ordinates to three decimals, exactly as the
   full ground state does. The pole terms are therefore not what drives the CCM phenomenon; the
   zeros are encoded in the archimedean-plus-prime part of the form.
2. The full form locks on earlier (`a = 0.5`: 14.135 versus 14.251 for the first zero; `a = 0.7`:
   the fourth zero exact versus off by 0.016). The two pole directions help the unconstrained
   minimizer, they do not contaminate it. At `√2` the pole-vanishing ground state is still
   generic: zeros spaced by about `π/a`, no relation to zeta.
3. Beyond `a ≈ 1.3` extra real zeros interleave with the zeta ordinates in both cases. This is
   expected from counting: an entire function of exponential type `a` has about `aT/π` real zeros
   up to `T`, more than `N(T)` once `a` is large. The ground states themselves are well separated
   (`gaps.json`: the second eigenvalue exceeds the first by a factor 20 to 1300 for the full form
   and 10 to 300 for the pole-vanishing form at every aperture from 0.7 to 2.1, so the lowest
   eigenvector is well defined at the working precision), but their Galerkin convergence in `N`
   is not established beyond `a ≈ 0.8` (Section 2.2), so the zero lists for `a ≥ 1.3` are
   qualitative. The regime where everything is converged is `a ≤ 0.8`, and the agreement with the
   zeta ordinates at `a = 0.9` and `1.1` is stable between `N = 56` and the smaller runs.

### 2.4 What this says about the parent card's theorems

- Theorem D (propagation past √2 on the pole-vanishing subspace) needs `μ₀(√2) > 0`: numerically
  `μ₀(√2) ≈ 0.547`. The soft `λ₁` of the theorem is numerically at least `λ ≈ 2` with a resolved
  margin, and no failure is visible up to `λ ≈ 5`.
- The degeneracy law (a threshold with an attained null vector) shows no threshold in the
  computed range; the ground energy approaches zero super-exponentially without changing sign,
  which is exactly what RH predicts.
- The prime-necessity observation of the parent card is now quantified: `λ_arch = 1.8145`.

## 3. Files

| file | content |
|---|---|
| `weil_polar_galerkin.py` | double-precision solver; `checks`, `sweep`, `fine` modes |
| `weil_polar_mp.py` | mpmath solver (60–80 digits); `probe`, `sqrt2`, `hp` modes |
| `bisect_thresholds.py` | bisection of the sign-change apertures |
| `sweep_results.json`, `sweep.log` | 47 apertures `0.05 ≤ a ≤ 2.0`, `N = 24, 36, 48, 64` |
| `fine_results.json`, `fine.log` | 130 apertures `0.30 ≤ a ≤ 1.59` step 0.01, `N = 48, 64` |
| `table_sweep_N64.csv`, `table_fine_N64.csv`, `table_convergence_in_N.csv` | flat tables |
| `thresholds.json` | bisection results and the prime-entry apertures |
| `mp_probe.json`, `probe.log` | mpmath 60 digits, `a ∈ {0.35, 0.5, 0.7, 0.9, 1.1, 1.3, 1.5}`, `N = 32, 44` |
| `mp_sqrt2.json`, `sqrt2.log` | mpmath 60 digits at `a = (log 2)/2`, `N = 24 … 64` |
| `mp_hp.json`, `hp.log`, `table_hp_dps80.csv` | mpmath 80 digits, `0.30 ≤ a ≤ 1.60` step 0.05, `N = 40, 56` |
| `table_sqrt2_dps60.csv` | the √2 convergence table |
| `sqrt2_bad_N56.log` | the invalid run before the quadrature-degree fix (kept as a record) |
| `spectral_zeros.py`, `spectral_zeros.json`, `spectral.log` | Fourier zeros of the full and pole-vanishing ground states, `a = 0.35 … 2.1` |
| `gaps.py`, `gaps.json`, `gaps.log` | two lowest eigenvalues of both forms at the larger apertures (eigenvector reliability) |

## 4. How to interpret and reuse

- To certify positivity at an aperture one would need a *lower* bound for the Rayleigh infimum,
  not a Galerkin minimum; the corpus's Birman–Schwinger finite block
  (`CCMRestrictedWeilOneSidedFiniteBlock`) is the right object for that, and interval arithmetic
  (`arb`, python-flint) would be needed. python-flint did not build on this pod's Python 3.8.
- Negative computed values are trustworthy statements about the true infimum (they are upper
  bounds), so the archimedean-only indefiniteness beyond `λ_arch` and the failure of the
  truncated forms are numerically solid facts, limited only by floating-point rounding
  (`10⁻¹³` relative to the matrix norms).
- The conventions match the corpus's Lean definitions (`ccmRestrictedWeilSourceQuadratic`,
  `ccmPolarApertureVector`, `logTranslationCLM`) and the parent card's elementary
  `K`-kernel form; see the docstring of `weil_polar_galerkin.py`.
