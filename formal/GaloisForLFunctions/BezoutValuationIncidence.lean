import GaloisForLFunctions.BezoutValuationIncidence.PronicBezoutSplitAndPrimePowerIndecomposability
import GaloisForLFunctions.BezoutValuationIncidence.QuotientDualOctaveReciprocityAndValuationSwitching
import GaloisForLFunctions.BezoutValuationIncidence.BezoutSuccessorQuadraticFormAndDirichletEnergySplit

/-!
# Bézout–Valuation Incidence Mechanics (`GaloisForLFunctions.BezoutValuationIncidence`)

Umbrella module for **Bézout–Valuation Incidence Mechanics**, the mathematical discipline coupling
the infinite-dimensional prime valuation lattice $\mathbb{N}_0^{(\mathcal{P})}$ to the
1-dimensional additive successor line $(\mathbb{N}, T_+ : k \mapsto k + 1)$ via pronic Bézout
successor splitting ($d_1 \mid k \wedge d_2 \mid (k + 1) \iff d_1 d_2 \mid k(k + 1)$ with
$\gcd(d_1, d_2) = 1$) and quotient-dual octave reciprocity ($d \leftrightarrow m = k / d$ across
trans-horizon octaves $R = \lfloor (k - 1)/N \rfloor$).

See [`BezoutValuationIncidence/README.md`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/README.md)
for the complete field guide, core objects, five core mechanisms, and six structural traps.

## Pillars

1. **Pillar I (`PronicBezoutSplitAndPrimePowerIndecomposability`):**
   - Mixed multiplicative difference annihilation $\Delta_{d_1, d_2}^\times \log(m) = 0$ vs. 1D
     prime-axis gradient $\Delta_d^\times \log(m) = \log d$ (`wall11_mixed_difference_log4_vs_log6`).
   - Pronic successor coprimality $\gcd(k, k + 1) = 1$, unique factor recovery
     $d_1 = \gcd(d_1 d_2, k), d_2 = \gcd(d_1 d_2, k + 1)$, and exact pronic divisor bijection
     (`image_mul_bezoutSuccessorPairSet_eq_divisors`, `sum_divisors_pronicSeq_eq_sieveSeq_mul_succ`).
   - Prime-power indecomposability under coprime factorization (`not_isPrimePow_mul_of_coprime`),
     total annihilation of prime powers on `centeredBezoutSuccessorPairSet`
     (`vonMangoldt_mul_eq_zero_of_mem_centeredBezoutSuccessorPairSet`), concrete Wall 11 separation
     excluding $4 = 2^2$ while attaining $6 = 2 \cdot 3$ (`wall11_four_excluded_six_attained`), and
     universal vanishing $\Lambda(k(k + 1)) = 0$ for all $k \ge 2$ (`vonMangoldt_pronicSeq_eq_zero`).

2. **Pillar II (`QuotientDualOctaveReciprocityAndValuationSwitching`):**
   - High-divisor complement formula and first trans-horizon octave reciprocity ($N + 1 \le k \le 2N$):
     $s_{N,\mu}(k) = -\mu(k)$, $s_{N,\mu}(k)^2 = \mu(k)^2$, and
     $s_{N,\mu}(k)s_{N,\mu}(k + 1) = \mu(k)\mu(k + 1)$.
   - Trans-horizon LCM fibre parity collapse $F_{N,\mu}(L) = \mu(L) + \mu(L)^2 \ge 0$ on
     $N + 1 \le L \le 2N$ (`sievedLcmFibre_moebius_first_octave`), vanishing identically on all
     primes $p \in [N + 1, 2N]$ (`sievedLcmFibre_moebius_prime_first_octave_eq_zero`).
   - Logarithmic von Mangoldt first-octave split $\Lambda_N(k) = \Lambda(k) + \mu(k)\log k$ and
     prime annihilation (`truncLogMoebiusSum_first_octave`, `truncLogMoebiusSum_prime_first_octave_eq_zero`).
   - Second trans-horizon octave ($2N + 1 \le k \le 3N$) and $2$-adic valuation switching:
     $s_{N,\mu}(2u) = 0$ for odd $u$ ($\log 6$ sector annihilated) vs. $s_{N,\mu}(4u) = \mu(u)$
     for odd $u$ ($\log 4$ sector activated).

3. **Pillar III (`BezoutSuccessorQuadraticFormAndDirichletEnergySplit`):**
   - Exact discrete Dirichlet energy polarization coupling Same-Node squares to Successor-Node
     Bézout correlations (`sum_addDiff_sieveSeq_sq_eq`).
   - Coprime bilinear expansion of `sieveSeq` and `centeredSieveSeq` successor correlations into
     `bezoutIncidenceCount` (`sum_sieveSeq_mul_succ_eq_sum_bezoutIncidenceCount`,
     `sum_centeredSieveSeq_mul_succ_eq_sum_bezoutIncidenceCount`).
   - Chinese Remainder separation law $d_1 d_2 \mid (k_2 - k_1)$, super-horizon uniqueness
     $\mathcal{I}_{\mathrm{Bez}}(M; d_1, d_2) \le 1$ ($M \le d_1 d_2$), and super-horizon reach up
     to $\theta = 2$ (`bezoutIncidence_super_horizon_reach`).
   - Master Four-Requirement Synthesis (`bezout_valuation_incidence_four_requirement_synthesis`).
-/
