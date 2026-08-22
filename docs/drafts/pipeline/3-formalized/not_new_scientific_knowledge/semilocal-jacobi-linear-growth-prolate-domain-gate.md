# Semilocal Jacobi linear growth and the prolate domain gate

- **ID:** semilocal-jacobi-linear-growth-prolate-domain-gate
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) + THEOREM (Lean)
- **Scientific status:** BRIDGE / NOT NEW SCIENTIFIC KNOWLEDGE
- **Parent sources:** Connes--Consani--Moscovici, *Zeta zeros and prolate wave operators*,
  arXiv:2310.18423v2, Sections 2 and 4.3; Connes--Consani--Moscovici,
  *On q-series and the moment problem associated to local factors*, arXiv:2403.01247

## Statement

Let `P` be a finite set of primes and let `nu_P` be the normalized semilocal cyclic spectral measure

`dnu_P(s)=Z_P^(-1) prod_(p in P)|1-p^(-1/2)exp(i log(p)s)|^(-2) dmu_infinity(s)`.

Write `a_n(P)>0` for its Jacobi coefficients, with `P=empty` denoting the archimedean measure. Put

`K_P=prod_(p in P) ((1+p^(-1/2))/(1-p^(-1/2)))^2`.

Then for every `n>=0`,

`K_P^(-1) a_n(empty) <= a_n(P) <= K_P a_n(empty)`,

where

`a_n(empty)=sqrt((2n+1)(2n+2))/2`.

Consequently `a_n(P)` has uniform linear upper and lower growth for each fixed finite `P`. The
off-diagonal coefficients of each parity block of the formal prolate Jacobi matrix,

`b_n^+(P)=a_(2n)(P)a_(2n+1)(P)`,

`b_n^-(P)=a_(2n+1)(P)a_(2n+2)(P)`,

have quadratic upper and lower growth. In particular

`sum_n 1/b_n^+(P)<infinity`, `sum_n 1/b_n^-(P)<infinity`.

Thus the elementary Carleman divergence criterion for essential self-adjointness of these prolate
Jacobi matrices is unavailable. The formal source expression does not by itself select a resolvent.

## Proof

For `r_p=p^(-1/2)`, the triangle inequality gives

`(1+r_p)^(-2) <= |1-r_p exp(i log(p)s)|^(-2) <= (1-r_p)^(-2)`.

Multiplying over `P` and using the same bounds for the normalization integral `Z_P` gives the
Radon--Nikodym estimate

`K_P^(-1) <= dnu_P/dmu_infinity <= K_P` almost everywhere.                 (1)

For a probability measure `rho` with all moments, let

`H_n(rho)=inf {int |Q|^2 drho : Q monic of degree n}`.

The infimum is attained by the monic orthogonal polynomial. Equation (1) gives, for every monic
`Q`,

`K_P^(-1) int |Q|^2 dmu_infinity
 <= int |Q|^2 dnu_P
 <= K_P int |Q|^2 dmu_infinity`.

Taking infima yields

`K_P^(-1)H_n(mu_infinity) <= H_n(nu_P) <= K_P H_n(mu_infinity)`.           (2)

For monic orthogonal polynomials,

`a_n(rho)^2=H_(n+1)(rho)/H_n(rho)`.

Applying the opposite sides of (2) to numerator and denominator gives

`K_P^(-2)a_n(empty)^2 <= a_n(P)^2 <= K_P^2 a_n(empty)^2`.

Taking positive square roots proves the comparison. The parent archimedean calculation gives the
displayed exact formula for `a_n(empty)`, hence linear growth. Products of consecutive coefficients
then have quadratic growth, so their reciprocal sums are dominated by a constant multiple of
`sum_(n>=1)n^(-2)`.

## Route consequence

- `[PROVED]` Every finite semilocal formal prolate matrix has the same coefficient order as the
  archimedean prolate matrix; Euler factors neither collapse nor superinflate the Jacobi scale.
- `[PROVED]` The normalized low-mode contraction is compatible with this global comparison but is
  strictly sharper at `n=0`.
- `[CLOSED SHORTCUT]` The usual Jacobi Carleman criterion cannot prove essential self-adjointness,
  because its required reciprocal off-diagonal series converges.
- `[OPEN CORE]` One must construct a source-selected self-adjoint/closed realization by a sharper
  limit-circle/boundary analysis or another semilocal principle, then establish Schatten estimates
  for its resolvent.

## Novelty audit

Uniform equivalence of measures, the monic extremal characterization, and the Jacobi norm-ratio
formula are standard. Their application gives an explicit source bound and removes an easy domain
shortcut, but it is a direct bridge rather than new scientific knowledge.

## Lean formalization

Unconditional; every declaration below depends only on `propext`, `Classical.choice`, `Quot.sound`.

New reusable layer — `formal/GaloisForLFunctions/HTGeometry/MonicOrthoExtremalComparison.lean`:

| paper step | Lean declaration |
|---|---|
| monic Pythagoras `L(Q²) = H_n + L(R²)` | `HTGeometry.momentInner_self_eq_monicOrthoNormSq_add` |
| `H_n = inf{L(Q²) : Q monic of degree n}` | `HTGeometry.monicOrthoNormSq_le_momentInner_of_monic` |
| uniqueness of the monic orthogonal polynomial | `HTGeometry.eq_monicOrtho_of_monic_of_orthogonal` |
| triangular families span by degree | `HTGeometry.mem_span_of_degree_lt` |
| any orthogonal family of exact degrees is `monicOrtho`, renormalized | `HTGeometry.monicOrtho_eq_of_orthogonal_family` |
| `H_n` through a concrete orthogonal family | `HTGeometry.monicOrthoNormSq_of_orthogonal_family` |
| `(2)`: `K⁻¹H_n(μ) ≤ H_n(ν) ≤ K H_n(μ)` | `HTGeometry.monicOrthoNormSq_le_of_momentInner_le` |
| `a_n(ρ)² = H_{n+1}/H_n` and its `K²` comparison | `HTGeometry.monicOrthoBeta_le_of_momentInner_le` |

Card layer — `formal/GaloisForLFunctions/RHTower/SemilocalJacobiLinearGrowthProlateDomainGate.lean`:

| paper step | Lean declaration |
|---|---|
| the archimedean Gamma measure charges every cofinite set | `RHTower.semilocalArchimedeanGammaMeasure_compl_finset_pos` |
| its moment form is positive definite | `RHTower.positiveMomentForm_ccmMetaplecticGammaMoment` |
| leading-coefficient step of the orthonormal Gamma--Jacobi family | `RHTower.semilocalArchimedeanJacobiPolynomial_leadingCoeff_succ` |
| `H_n(∅) = lc_n⁻²` | `RHTower.monicOrthoNormSq_ccmMetaplecticGammaMoment` |
| `a_n(∅)² = (n+1/2)(n+1)` | `RHTower.monicOrthoBeta_ccmMetaplecticGammaMoment` |
| `a_n(∅) = √((2n+1)(2n+2))/2` | `RHTower.semilocalArchimedeanJacobiCoefficient_eq_sqrt_div_two` |
| one-factor bound `(1+r)⁻² ≤ \|1−re^{iθ}\|⁻² ≤ (1−r)⁻²` | `RHTower.semilocalPrimeEulerFactor_bounds` |
| `(1)`: `K_P⁻¹ ≤ dν_P/dμ_∞ ≤ K_P` | `RHTower.semilocalFinitePrimeEulerDensity_bounds`, `RHTower.semilocalEulerDensityUpper_eq` |
| positivity of the normalizing mass `Z_P` | `RHTower.semilocalFinitePrimeMass_pos` |
| the normalized semilocal moment functional | `RHTower.momentFunctional_semilocalFinitePrimeCyclicMoment`, `RHTower.momentInner_semilocalFinitePrimeCyclicMoment_self` |
| uniform equivalence of the two moment forms | `RHTower.momentInner_semilocalFinitePrimeCyclicMoment_le`, `RHTower.momentInner_ccmMetaplecticGammaMoment_le` |
| positive definiteness of the semilocal moment form | `RHTower.positiveMomentForm_semilocalFinitePrimeCyclicMoment` |
| `a_n(P) ≤ K_P a_n(∅)` | `RHTower.semilocalFinitePrimeJacobiCoefficient_le` |
| `a_n(∅) ≤ K_P a_n(P)` | `RHTower.semilocalArchimedeanJacobiCoefficient_le` |
| linear lower growth `a_n(P) ≥ (n+1/2)/K_P` | `RHTower.semilocalFinitePrimeJacobiCoefficient_lower` |
| linear upper growth `a_n(P) ≤ K_P(n+1)` | `RHTower.semilocalFinitePrimeJacobiCoefficient_upper` |
| `b_n^±(P)` quadratic lower growth | `RHTower.semilocalProlate_offDiagonal_lower` |
| `b_n^±(P)` quadratic upper growth | `RHTower.semilocalProlate_offDiagonal_upper` |
| `∑ 1/b_n^±(P) < ∞`: Carleman unavailable | `RHTower.summable_inv_semilocalProlateOffDiagonal` |

Corpus assets reused without duplication: `RHTower.semilocalArchimedeanGammaMeasure`,
`RHTower.ccmMetaplecticGammaMoment`, `RHTower.integrable_pow_semilocalArchimedeanGammaMeasure`,
`RHTower.semilocalArchimedeanJacobiPolynomial` with `…_natDegree`, `…_leadingCoeff_pos`,
`semilocalArchimedeanJacobiGram_eq_ite`, `RHTower.semilocalArchimedeanJacobiCoefficient` and
`…_sq`, `RHTower.semilocalFinitePrimeEulerDensity` with `…_pos`, `…_le_poissonBound`,
`integrable_eval_mul_semilocalFinitePrimeEulerDensity`, `RHTower.semilocalPrimePoissonRatio`
(`…_pos`, `…_lt_one`), `RHTower.semilocalPrimePhase` and `norm_semilocalPrimePhase`, and the
whole `HTGeometry` moment/orthogonal-polynomial layer.

`scripts/formal_tools.py lint` → `formal lint passed`.
