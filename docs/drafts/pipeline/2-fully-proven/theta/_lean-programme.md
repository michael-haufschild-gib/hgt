# Theta folder → stage 3: Lean programme ledger

Goal: formalize, unconditionally, every paper theorem of every card in this folder; move each
card to `3-formalized/theta/` when all its displayed results have closed Lean theorems
(`lake env lean` clean, `#print axioms` = propext/Classical.choice/Quot.sound only, wired into
`RHTower.lean`). Delete this file when the folder is empty.

## Shared layers (build once, reuse)

| Layer | Content | Module | Status |
|-|-|-|-|
| L1 deletion | finite prime deletion `D_S`, atom Mellin for complex `w`, `L_w k_S = XiC(iw)∏(1-p^{-1/2-w})`, coprime atom sum | `ThetaPrimeDeletionMellin` (+ `ThetaPrimeDeletionSpectralEscape`: `PrimeExhaustion`, real Mellin laws, positivity) | done |
| L2 flux | normalized flux `b_f`, `b_k = 2π∑n²e^{-πn²t}`, shift law, CM ⇔ positive rate measure, dominated representation | `ThetaCriticalFluxBernstein` (+ `ThetaFluxSource`, linearity, deletion flux, rate lattice in `ThetaPrimeDeletionBernsteinPureRay`) | done |
| L2b gauges | real-shift gauges `∑ c_i k(·+s_i)`: flux atom expansion, grouped Bernstein criterion, rate-coefficient cone, `L_w g = M(w) XiC(iw)`, zero-order transfer | `ThetaTranslationGaugeFlux` | done |
| L2c measure gauges | `∫ k(·+s) dν`, Fubini flux, Laplace laws, CM under integrals/limits, seed limit, signed Laplace positivity, all-sieve theorem | `ThetaTranslationMeasureGauge` | done |
| L3 zero division | outward sine Green operator `T_α`, relative bounds, ODE, Fourier division | `ThetaZeroDivisionSource` | done (single division; iterates/partial fractions pending) |
| L4 renewal | `P,ν,Q,D`, renewal log series, `Xi(2iλ)=(a+λ)D(λ)+(a-λ)D(-λ)` | `ThetaRenewalFactorization` | todo |
| L5 quantile | CDF/quantile/`B,D,T,A` on `L²(0,1)` (partly in corpus) | existing Hedenmalm modules | audit |
| L6 complex analysis | Rouché/Hurwitz, Jensen+RvM capacity, indicator/PL | search corpus | audit |

## Cards (status: todo / partial / done)

| Card | Needs | Status |
|-|-|-|
| prime-deletion-spectral-escape | L1 | done → 3-formalized |
| euler-two-port-jet-pole-renormalization | L1 | done → 3-formalized |
| sieve-bidirectional-cusp-variation | L1 | done → 3-formalized |
| prime-square-two-level-normal-jet-rigidity | L1 (algebra in corpus) | done → 3-formalized |
| prime-deletion-graded-terminal-admission | first-atom asymptotic | todo |
| euler-critical-boundary-mass-escape | L1, flux potential | todo |
| one-sided-bernstein-two-anchor-offline-zero | L1, L2 | done → 3-formalized |
| prime-power-bernstein-gauge-rigidity | L2, gauge layer `ThetaTranslationGaugeFlux` | done → 3-formalized |
| divisor-bernstein-gauge-rigidity | L2b, Möbius/totient | done → 3-formalized |
| prime-deletion-bernstein-pure-ray | L2 | done → 3-formalized |
| all-sieve-seed-projector-translation-cone | L1, L2, measure gauges `ThetaTranslationMeasureGauge` | done → 3-formalized |
| all-sieve-mobius-rate-reconstruction | L2 | todo |
| sieve-zero-division-rate-tomography | L2, L3, Landau | todo |
| positive-real-zero-division | L3 | done → 3-formalized (`ThetaZeroDivisionSource`) |
| euler-zero-division-seed-transfer | L3 | todo |
| endpoint-harmonic-completeness | L3, tail-capacity | todo |
| tail-divisor-capacity-threshold | L6 | todo |
| derivative-dark-divisor-packets | partial corpus, L6 | todo |
| compact-critical-strip-zero-engineering | bumps, Riemann–Lebesgue | todo |
| global-riccati-order-one-offline-countermodel | Riccati Gaussian family `ThetaRiccatiGaussianCountermodel` | done → 3-formalized |
| riccati-three-charge-offline-countermodel | L6 | done → 3-formalized (`ThetaRiccatiThreeChargeCountermodel`) |
| euler-logcell-residue-highpass | ℓ² operators, Hardy separation | todo |
| cdf-crossfrequency-rvm-capacity | L5, compact operators | todo |
| cdf-no-finite-range-symmetrizer | L5 | todo |
| quantile-critical-one-port-rigging | L5 | todo |
| quantile-resistance-network | L5, Fourier series | todo |
| compact-inverse-zero-jordan-history | L5 | todo |
| deletion-cutoff-commutator-collapse | L1, PNT | todo |
| chronological-boundary-positive-transfer | L1, Laplace | todo |
| prime-deletion-moving-cusp-dual-source | L1, Landau | todo |
| rational-cusp-boundary-law | Poisson/Gauss sums | done → 3-formalized (`ThetaRationalCuspBoundary`, `ThetaCuspOneSidedConnection`, `ThetaCuspAbelBoundaryPairing`, `QuadraticGaussSumFourthPower`) |
| prime-modular-commutator-crossing | Jacobi, Hardy sign, PNT | todo |
| renewal-phase-cosh-factorization | L4 | todo |
| renewal-complex-resonance-stieltjes-obstruction | L4, Hadamard | todo |
| renewal-reflection-preserving-zero-surgery | L4 | todo |
| renewal-seam-critical-coupling | L4, Rouché | todo |
| half-line-port-alternating-orientation | two-thirds theorem | todo |
| half-port-stieltjes-spectral-bridge | L4 | todo |
| levy-spherical-dispersion-duality | L4 | todo |
| causal-germ-translation-ideal-phase-selection | zero-radius theorem | todo |
| causal-mobius-theta-boundary-criterion | Möbius–theta tail ⇔ RH criterion | todo |
| causal-mobius-theta-primorial-transition | primorial innovation bounds | todo |
