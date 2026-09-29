# Cofinal prime deletion exposes the oscillatory rate kernel of zero division — Lean certificate

- **Paper card:** `theta-sieve-zero-division-rate-tomography.md`
- **Lean modules:**
  - `GaloisForLFunctions.HTGeometry.QuasiPolynomialLaplaceCalculus` covers quasi-polynomials `Σ_μ p_μ(s) e^{μs}`:
    - convolution with an exponential and the Laplace transform as an explicit rational function;
    - pole order `deg p_μ + 1` at each exponent;
    - uniqueness from a real ray; reality and conjugation symmetry;
    - the top-term asymptotics; non-decay of trigonometric polynomials (Cesàro means);
    - `limsup log‖E(s)‖/s = max Re μ`; the real growth law.
  - `GaloisForLFunctions.RHTower.ThetaZeroDivisionCausalKernel` covers the causal kernel of a zero division:
    - sine kernels and their convolutions; the kernel `K = combKernel L e` of the partial-fraction combination;
    - the Green formula `u = c k + ∫ K(s) k(·+s) ds`;
    - the Laplace identity `c + ℒK(q) = r(−q²)` and its extension off the exponents;
    - poles ↔ kernel exponents; evenness; reality.
  - `GaloisForLFunctions.RHTower.ThetaZeroDivisionRateTomography` covers:
    - Landau's no-eventual-sign theorem for kernels with a genuine non-real pole;
    - both signs arbitrarily late;
    - deletion of the causal representation; the deleted flux; the cofinal limit;
    - the signed seed measure and the failure of complete monotonicity;
    - the rate density; exponential type; the leading oscillation; the single quartet; the critical line.
  - `GaloisForLFunctions.RHTower.ThetaZeroDivisionRateDerivativeWitness` covers:
    - Gaussian-rate derivative towers and differentiation under the rate integral;
    - derivative convergence along every exhaustion;
    - the single derivative-order witness.
- **Umbrellas:** `GaloisForLFunctions.HTGeometry` (the quasi-polynomial layer), `GaloisForLFunctions.RHTower` (the three RH-side modules)
- **Verification:**
  - Targeted `lake build` of every module.
  - `lake env lean` audit clean (no errors, no warnings) on all four modules.
  - `#print axioms` = `propext`, `Classical.choice`, `Quot.sound` for all 245 declarations of the four modules.
  - No `sorry`; lint reports nothing for these modules.
  - The only hypotheses are the card's own quantified objects:
    - a conjugation-closed list `L` of zeros of `XiC` with multiplicities and `Re β > 0`;
    - a nonzero real numerator `N` with `N(0) = 0`, `deg N ≤ |L|`;
    - `ε ≠ 0`; an exhaustion of the primes;
    - for the quartet, `Im α ≠ 0`; for the critical line, `Im β = 0`.

Dictionary:
- `F = XiC` in the Fourier coordinate; `k = thetaCuspFullSource`.
- `P(z²) = listDivisor L z = ∏_{β∈L}(1 − z²/β²)`; `r(−q²) = rateSymbol L e q` with `e = N` over `ℂ`.
- `u = divisionSource L N` (the real part of `listComb thetaListDivision L e`, equal to it on `x ≥ 0`).
- `c = causalRateConst L N`, `K = causalRateKernel L N` (the real part of the quasi-polynomial `combKernel L e`).
- `f_ε = perturbedSource L N ε`; `D_S = thetaPrimeDeletion S`; `b_f = thetaNormalizedFlux f`.
- `B_ε = cofinalFlux L N ε`; the rate density `2πK(s)e^{5s/2}` is `rateDensity L N`.
- The signed seed parts are `seedPart L N ε (±1)`; complete monotonicity is `CompletelyMonotoneOn`.
- An increasing cofinal exhaustion is `PrimeExhaustion S`.
- Poles of the reduced rational function are points with `meromorphicOrderAt (rateSymbol L e) μ < 0`; this automatically cancels common factors.
- A pole of order `m + 1` is the card's multiplicity `m + 1`.

| Card item | Lean theorem |
|-|-|
| causal representation (1) on `x ≥ 0`, with integrability; `u` is real there | `divisionSource_eq`, `listComb_thetaListDivision_eq_ofReal`, `listComb_eq_kernel`, `halfListDivision_eq_kernel` |
| `K` is a real exponential polynomial, the inverse Laplace transform of `r(−q²) − c`; `c` is the constant part of `r` | `combKernel_real`, `combKernel_eval_eq_ofReal`, `integral_causalRateKernel_mul_exp`, `combConst_add_laplace_combKernel`, `rateSymbol_eq_add_laplace`, `tendsto_rateSymbol_atTop` |
| poles of `r(−q²)` are exactly the exponents of `K`, of order `deg + 1`, symmetric under `q ↦ −q`, non-real | `meromorphicOrderAt_rateSymbol`, `meromorphicOrderAt_rateSymbol_nonneg`, `rateSymbol_pole_iff`, `meromorphicOrderAt_rateSymbol_at_neg`, `neg_mem_support_combKernel`, `ofReal_not_mem_kernelExponents`, `combKernel_ne_zero` |
| Landau: a nonnegative tail has a singular transform at its real abscissa, so no eventual sign | `not_eventually_nonneg_of_pole`, `causalRateKernel_not_eventually_signed` |
| **1. `K` takes both signs arbitrarily far out** | `causalRateKernel_sign_changes` |
| rate density (2) `dν = 2πK(s)e^{5s/2}ds` at `λ = πe^{2s}`: `B_ε` is its Laplace transform plus the atom | `rateDensity`, `cofinalFlux_eq_rate` |
| **both signs on arbitrarily large rates** (critical-line divisions included) | `rateDensity_sign_changes` |
| deletion formula (3) and shift law (4) (corpus) | `thetaNormalizedFlux_thetaPrimeDeletion_eq`, `thetaNormalizedFlux_comp_add` |
| positive shifts commute with (1): `D_S f_ε = (1+εc)D_S k + ε∫K D_S k(·+s)` | `thetaPrimeDeletion_perturbedSource` |
| deleted flux (5) for `t > 1` | `thetaNormalizedFlux_perturbedSource`, `integrable_flux_kernel` |
| cofinal limit (6) along every exhaustion | `cofinalFlux`, `tendsto_flux_perturbedSource` |
| `B_ε(t₀+·)` is the Laplace transform of a finite signed measure; the atom cannot mask the negative density | `seedPart`, `isFiniteMeasure_seedPart`, `cofinalFlux_eq_seedFlux_sub`, `thetaSeedFlux_seedPart` |
| **`B_ε` is not completely monotone for `ε ≠ 0`** | `not_completelyMonotoneOn_cofinalFlux` |
| **2. along every exhaustion the deleted fluxes of `f_ε` are eventually not completely monotone** | `eventually_not_completelyMonotoneOn_flux` (also a single difference witness: `exists_allSieve_failure_witness`) |
| derivatives of `b_{D_S f_ε}` and of `B_ε` differentiate (5) and (6) under the integral; derivative convergence along every exhaustion | `iteratedDeriv_flux_perturbedSource`, `iteratedDeriv_cofinalFlux`, `tendsto_iteratedDeriv_flux_perturbedSource` (Gaussian-rate towers: `GaussianRateTower.hasDerivAt_rateFluxTower`, `tendsto_rateFluxTower`, `abs_deletedRateTower_le`, `tendsto_deletedRateTower`) |
| **a single derivative order and a single `t > 1` witness the failure eventually** | `exists_iteratedDeriv_cofinalFlux_neg`, `exists_allSieve_derivative_witness` |
| **3. exponential type**: `limsup log|K(s)|/s = a = max Re` of a pole, `a ≥ 0`; an off-line pole gives `a > 0` | `causalRateKernel_exponential_type`, `causalRateKernel_positive_type` |
| leading oscillation with the evident sum of frequencies: `K(s) = s^m e^{as}(Σ_top (A_μ cos(Im μ s) + B_μ sin(Im μ s)) + o(1))`, `(A_μ,B_μ) ≠ 0`, the sum does not tend to `0` | `causalRateKernel_top_asymptotics` (quasi-polynomial layer: `QuasiPolynomial.exists_real_top_asymptotics`, `QuasiPolynomial.limsup_log_norm_eval`) |
| **single quartet**: maximal pole order `m+1`, `limsup log|K|/s = |β|`, `K(s) = s^m e^{|β|s}(A cos(γs) + B sin(γs) + o(1))`, `(A,B) ≠ 0` | `causalRateKernel_single_quartet` |
| **critical-line zero division has exponential type zero** | `causalRateKernel_exponential_type_critical` |
| growth `e^{|β|s} = (λ/π)^{|β|/2}` in the rate variable | `exp_mul_eq_rate_rpow` |
