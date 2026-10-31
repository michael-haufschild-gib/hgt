# Arithmetic Counting Positivity (ACountP)

Namespace `GaloisForLFunctions.ArithmeticCountingPositivity`; umbrella `ArithmeticCountingPositivity.lean`; 35 modules.
All results are unconditional. No module carries `#print axioms` lines.

## 1. Motivation

SelectiveMultiscaleArithmeticPositivity identified the pole-hyperplane gap of the prime form as the place where `Λ` differs
from its twins: `ζ` has gap `2 log 2`, Liouville has `0`. ACountP asks what an arithmetic **count** can prove about this gap
for every completely multiplicative sign twin `ωΛ`, and whether the gap, possibly with extra counted data, selects `Λ`. The
programme computes the exact gap of every prime-flip twin from divisibility counts, through Ramanujan conductor coordinates,
actual eigenlines of the finite prime matrix, and an arithmetic secular equation.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Harmonic correlation | `harmonicCorrelation` | `c_N(ω) = S_N(ω)/H_N`, `S_N = Σ_{n≤N} ω(n)/n` |
| Prime flips | `finiteFlip`, `cofiniteFlip`, `primeSetFlip`, `primeFlipWeight` | `ω_F(n) = Π_{p∈F}(−1)^{v_p(n)}`; `λ·ω_F`; arbitrary prime set `P`; `ω_pΛ` |
| Densities | `finiteFlipHarmonicDensity`, `primeSetHarmonicDensity` | `Π_{p∈F}(p−1)/(p+1)`; decreasing Euler-product limit |
| Parity counts | `parityMass`, `primeParityRamanujanSum`, `finiteFlipRamanujanSum`, `primeSetRamanujanSum` | `Σ(1 ± ω_p)/n`; mixed counts with conductor `m` |
| Horizon vectors | `primeParityHorizonVector`, `finiteFlipHorizonVector`, `primeSetHorizonVector`, `harmonicRamanujanHorizonVector` | unit constraint vectors and harmonic-normalized Ramanujan modes |
| Parity tower | `primeParityTowerProfile`, `primeParityTowerVector`, `primeParityTowerCoefficient`, `primeParityTowerEnergy` | Ramanujan expansion through conductors `p^k`; coefficients and energies `E_{p^k} − γ` |
| Conductor data | `finiteFlipMobius`, `finiteFlipSpectralWeight`, `finiteFlipConductorCoefficient`, `primeSetMobius`, `primeSetSpectralWeight`, `primeSetConductorCoefficient` | `μ * ω`, `mobius²/φ`, `density·mobius/√φ` |
| Secular functions | `primeParitySecularRoot`, `finiteFlipSecular`, `primeSetSecular` | `−1/s + Σ_{m≥2} weight(m)/(E_m − γ − s)` and its root |
| Resolvents | `primeParityFiniteResolvent`, `finiteFlipFiniteResolvent`, `primeSetFiniteResolvent`, `primeSetConductorResolvent` | `Σ_i ⟨v, e_i⟩²/(E_i − γ − s)` on the actual prime matrix; arithmetic limit |
| Greatest gaps | `finiteFlipGreatestGap`, `primeSetGreatestGap` | attained supremum of hyperplane gaps |
| Prime tails | `primeTailCutoff`, `primeSetCutoff`, `primeSetReciprocalSum` | primes in `(B,Q]`; `P ∩ [1,N]`; `Σ 1/p` |
| Costs | `finitePrimeStrippingCost`, `finiteFlipConductorEnergyMoment` | `Σ 2(1+log p)/(p+1)`; `Σ 4p log p/(p²−1)` |
| Bounded spectral mass | `primeSetBoundedSpectralMass` | squared constraint mass below energy `T` |

External: `HasHyperplaneGap`, `gaugeHarmonicSum`, `gaugeWitness`, `poleCoord`, `poleResidual`, `atomicWeilForm`
(SelectiveMultiscaleArithmeticPositivity); `poleDefect`, `fullPrimeMatrix`, `ramanujanAdjunctionEnergy`, `IsSignGauge`,
`liouvilleSign`, `harmonicVar` (RenormalizedArithmeticPotentialTheory); `ramanujanLagCoefficient`, `moebiusReal`
(BezoutValuationIncidence); `infiniteSecular`, `WeilPositiveFull` (RHTower).

## 3. Language

- **Gap** `g` of `ω`: on `Σx_n/√n = 0`, `P_N(ωx) ≤ (log N − γ − g + ε)|x|²` eventually; greatest gap `≤ 2 log 2` for sign gauges.
- **Density** of a flip pattern: Euler product `Π(p−1)/(p+1)`, the limit of `c_N`.
- **Conductor coordinate**: limit of the inner product of the constraint vector with the conductor-`m` Ramanujan mode.
- **Secular function**: reciprocal series whose sign decides the constrained gap.
- **Counting producer**: an identity proved from divisibility alone that pays an inequality.

## 4. Mechanisms

**A. Counts pay gaps**

1. **Angle transfer.** On the hyperplane, `Var(ωx) ≥ c_N²|x|²`; with the sharp Poincaré constant, uniformly over all sign
   gauges: `P_N(ωx) ≤ (log N − γ − 2 log 2·c_N² + ε)|x|²`.
2. **Parity pairing.** Multiplication by `p` maps positive to negative fibres: `H_N − S_N = (H + S)_{⌊N/p⌋}/p`; so
   `c_N → (p−1)/(p+1)` with boundary error `≤ 2(1 + log p)/((p+1)H_N)`.
3. **Finite sets.** Adding a prime gives `pS_N(new) + S_{N/p}(new) = pS_N(old) − S_{N/p}(old)`; contraction under `N ↦ N/p` keeps
   the error bounded: `c_N → Π(p−1)/(p+1)`.
4. **Stripping.** Each prime costs two harmonic shells: `|S(ω_F ω) − dens(F)S(ω)| ≤ Σ 2(1 + log p)/(p+1)`, uniform in `N` and
   the residual pattern. Every infinite pattern then has `c_N →` Euler product.

**B. Counts give spectral coordinates**

5. **Möbius transform.** Mixed count `= Σ_{d|m}μ(m/d)ω(d)S_{⌊N/d⌋}`; normalized limit `density·(μ * ω)(m)`. `(μ * ω_F)(p^k) = 2(−1)^k`
   for `p ∈ F`, `0` otherwise; squared weights `4^{ω(m)}/φ(m)` on `F`-supported `m`.
6. **Unit mass.** Finite Euler product `Π(1 + 4p/(p−1)²) = dens⁻²`, so squared conductor coefficients sum to `1`; for infinite `P`
   the sum is `1` if density `> 0` and `0` otherwise.
7. **Eigenline transfer.** Ramanujan quasimodes have vanishing residual; isolated energy windows contain one eigenvalue; the squared
   coordinate on that eigenline tends to the counted coefficient².
8. **Exact count.** Bounded spectral sublevels are filled by conductor eigenlines (distinct energies, exact eigenvalue count).

**C. Secular classification**

9. **Reciprocal criterion.** One negative diagonal direction is removed by a constraint iff `b·Σa_i²/w_i ≤ c²`; for the prime
   matrix: constrained bound at `s` ⇔ finite resolvent `≤ 0`.
10. **Resolvent limit.** For `0 < s < 2 log 2` only the ground lies below `γ + s`; unit mass and a fixed denominator gap make the
    full resolvent converge to the arithmetic series (zero density: mass escape makes it vanish).
11. **Gap = secular sign.** `g` is a gap ⇔ `g ≤ 2 log 2` and the secular function `≤ 0` on `(0,g)`; the greatest gap is attained and
    is the interior root when below `2 log 2`.

**D. Quantitative structure**

12. **Inclusion.** More flipped primes add weight: gaps decrease, strictly below the plateau; loss
    `(δ_F − δ_G)² ≤ (2 log 2)²(dens_G⁻² − dens_F⁻²)`; one prime `p` changes a gap by `O(p^{−1/2})`.
13. **Moment bound.** Dual-number Euler product gives `Σ coeff²(E − γ) = Σ 4p log p/(p²−1)`; Cauchy–Schwarz gives
    `δ_F ≤ dens²/(1 − dens²)·moment`.
14. **Tail collapse.** Conductors `B!(n+2)+1` are supported above `B` and have divergent `Σ 1/(m log m)`, forcing tail gaps to `0`;
    Mertens gives `δ ≤ (64/3)D_B²/(log Q)³`.
15. **Large single primes.** Two-scale (smooth box × rough fibres) Efron–Stein with separate `p`-ladders: excess `log p − 2 log 2`
    pays the pole rotation `(1 − c_p²)/c_p²` from `p = 11` on; ground + conductor-`p` plane bounds gaps by `p log p/(p+3)`.

## 5. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| Uniform squared-correlation gap | `eventually_prime_gap_ge_squared_correlation` | proved |
| Parity pairing and density `(p−1)/(p+1)` | `prime_parity_pairing`, `primeFlip_harmonicCorrelation_tendsto` | proved |
| Maximal gap `2 log 2` ⇔ `p ≥ 11` | `primeFlip_hasHyperplaneGap_two_mul_log_two_iff` | proved |
| Maximal gap does not select `Λ` | `maximal_gap_does_not_select_the_source` | proved |
| Near-maximal gap, `|weight| = Λ`, matching, yet not Weil positive | `near_maximal_gaps_do_not_force_weil_positivity` | proved |
| Uniform Ramanujan-tower exhaustion of parity | `primeParityTower_uniform_exhaustion` | proved |
| Exact single-prime gap `min(2 log 2, α_p)` | `isGreatest_primeFlip_hyperplaneGap_min_secularRoot` | proved |
| Unit conductor mass | `hasSum_finiteFlipConductorCoefficient_sq`, `hasSum_primeSetConductorCoefficient_sq` | proved |
| Counts determine eigenline coordinates | `exists_primeSet_conductor_eigenline` | proved |
| Full resolvent limit for every pattern | `tendsto_primeSetFiniteResolvent` | proved |
| Secular gap classification | `finiteFlip_hasHyperplaneGap_iff_secular`, `primeSetFlip_hasHyperplaneGap_iff_secular` | proved |
| Strict inclusion law | `finiteFlipGreatestGap_lt_iff_of_ssubset` | proved |
| Tail gaps `O((log Q)^{−3})` | `eventually_primeTailGreatestGap_le_inverse_log_cube` | proved |
| Dyadic probe selects finite flips | `finiteFlip_two_gap_selection` | proved |
| No fixed probe tolerance | `exists_maximal_flip_with_almost_unchanged_dyadic_gap` | proved |
| Every pattern's harmonic mean is its Euler product | `primeSetFlip_harmonicCorrelation_tendsto` | proved |
| Positive density ⇔ cutoff completeness ⇔ bounded mass retained | `primeSetFlip_harmonic_cutoffs_complete_iff`, `primeSet_bounded_spectral_mass_vanishes_iff` | proved |
| Cofinite flips have gap `0`; exhaustion is non-uniform | `isGreatest_cofiniteFlip_hyperplaneGap`, `finitePrimeExhaustion_no_uniform_positive_gap` | proved |

## 6. Tools

**Developed**
- Divisibility recurrences and harmonic shell bounds for multiplicative sign gauges.
- Möbius/Ramanujan coordinate calculus with dual-number Euler products for mass and moments.
- Eigenline transfer from quasimodes to actual prime-matrix spectra; exact sublevel counting.
- Reciprocal-mass criterion for constrained forms; packet sandwich limits.
- Arithmetic secular functions with continuity, monotonicity and root characterization.
- Two-scale smooth/rough Efron–Stein with separated prime ladders.

**To build**
- A count that selects `Λ` among arbitrary bounded weights, not only prime-sign patterns.
- Transfer of the discrete gap to continuous overlapping sources with Gamma and both poles.
- Optimal-gap transfer at zero density.

## 7. Open questions

1. Which counted invariant, beyond the gap and one dyadic probe, selects `Λ` with a fixed positive tolerance?
2. What is the exact greatest gap of a zero-density infinite prime pattern?
3. What is the sharp decay rate of tail-flip gaps in `Q`?
4. Can the gap classification be lifted from atomic prime forms to the complete Weil form?
5. Why does the prime two fix both the dyadic generator and the sharp gap value?

## 8. Traps

| Trap | Fact |
|---|---|
| Multiplicativity breaks parity | Liouville is completely multiplicative |
| A maximal selective gap identifies the source | Single-prime flips with `p ≥ 11` have gap `2 log 2`, polar matching, `|weight| = Λ` |
| Finite-prime selection survives a tolerance | Remote flips change the dyadic response by `O(1/p)` |
| Positive gaps at each cutoff survive exhaustion | No uniform horizon; prime cutoffs below `Q` equal Liouville on `n < Q` |
| Pointwise convergence controls the gap | Zero-gap cofinite flips converge pointwise to `1` |
| Individually maximal primes stay maximal jointly | Joint flips above any cutoff have gaps tending to `0` |
| A fixed mode controls the spectrum | Only with unit mass and denominator gap for all omitted lines |
| A gap implies Weil positivity | Full-cone uniqueness rules out every flip |

## 9. Context

**Uses**

| Programme | Imports | For |
|---|---|---|
| RenormalizedArithmeticPotentialTheory | 9 | prime matrix, quasimodes, eigenlines, polar matching, adjunction spectrum, horizon laws |
| SelectiveMultiscaleArithmeticPositivity | 6 | hyperplane gap, margin `2 log 2`, conductor-two excitation, correlation lemmas |
| RHTower | 6 | Weil cone uniqueness, infinite secular roots, Mertens, divisor harmonic means |
| TransHorizonIncidenceMechanics | 2 | Möbius transforms at prime powers |
| BezoutValuationIncidence | 2 | Ramanujan lag coefficients, prime-power revival |
| HTGeometry | 1 | Hermitian spectral windows |

**Used by**

| Programme | Modules | For |
|---|---|---|
| TransMetzlerWeilPositivity | 3 | sign twins above the Robin–Euler ratio, prime-flip complete form |
| HeckeKreinToeplitz | 1 | flips on the finite stratum |
| `MainTheorems.lean` | 1 | aggregation |

| Neighbour | Relation |
|---|---|
| SelectiveMultiscaleArithmeticPositivity | defines the gap; ACountP computes it for every prime-sign twin |
| RenormalizedArithmeticPotentialTheory | supplies the prime matrix spectrum used for the transfer |
| HeckeKreinToeplitz | uses flips to test tower Toeplitz indices |

## 10. Big picture

ACountP turns a qualitative separation into a complete calculation. For every completely multiplicative prime-sign twin, its
selective gap is now determined by divisibility counts: an Euler-product density, Ramanujan conductor weights, and one
arithmetic secular equation that matches the actual finite prime matrices exactly. Counting is powerful enough to compute
the discrete margin to the last constant.

The finding for RH research is negative but sharp. The discrete margin, even at its exact maximum and combined with
multiplicativity, polar matching and the true size of every Weil coefficient, does not identify `Λ`: infinitely many twins
match it and still fail Weil positivity. Exhaustion through prime cutoffs is non-uniform, and any fixed tolerance in a
selecting probe is defeated by remote primes. A proof of positivity cannot come from the hyperplane gap alone; it must use
continuous overlap, Gamma and the poles, or an invariant finer than any finite count of prime signs.
