# Arithmetic Counting Positivity (ACountP)

Namespace `GaloisForLFunctions.ArithmeticCountingPositivity`; umbrella `ArithmeticCountingPositivity.lean`.

**Question.** Produce positivity from arithmetic **counts**, with multiplicativity selecting the untwisted source. A positive
representation assumed at the outset does not solve this; neither does an identity transferring an unproved sign. Over $\mathbb F_q$ an
independently proved point count supplies the Hodge inequality. Over $\mathbb Z$ the complete Weil form has an exact arithmetic
description but no proved sign. What must a count retain to produce it — arithmetic incidence, signed correlations, the
archimedean term, the two poles?

---

## 1. Place in the research

The explicit formula splits the complete form into Gamma, poles and prime source. Majorants discard what distinguishes $\Lambda$ from
its Liouville twist; multiplicativity alone permits that twist. A successful count must use a compatibility that changes under
twisting and prove an inequality from it. Starting point: the discrete multiplicative walk has sharp harmonic-hyperplane gap
$2\log2$, the Liouville twin gap $0$ (RAPT/SMAP). Open passage: discrete energy → continuous overlapping sources → source-complete exhaustion.

ACountP owns **independent counting constructions** and exact tests of what information their positivity preserves.

| Programme | Interface |
|---|---|
| ArithmeticCastelnuovoSeveri | Intersection theory, effectivity, section counts, finite-field calibration |
| ArithmeticOrientationGeometry | Orbit correlation, Toeplitz index, finite-support receivers |
| ArithmeticCorrespondencePositivity | Sparse annihilators; lattice requirement of Stepanov's mechanism |
| SelectiveMultiscaleArithmeticPositivity | Selective discrete margin; multiscale transfer |
| RenormalizedArithmeticPotentialTheory | Sharp multiplicative Poincaré inequality, prime-defect identity, finite-prime gauges |
| MultiplicativePositivityGeometry | Arithmetic positive definiteness on the boundary and its interior limits |
| ArithmeticIncidencePositivity | Prime incidence, atomic forms, surplus allocation |
| SignedArithmeticHodgeTheory, ArithmeticIndexDescent | Complete source coordinates; uniform index bounds for prime layers; first-layer obstruction |
| BezoutValuationIncidence | Divisor incidence and correlations unavailable in Beurling systems |
| ArithmeticEffectivityTheory | Counting as effectivity; Stepanov over $\mathbb Z$ reaches only the base |

---

## 2. Objects and language

| Object | Information retained |
|---|---|
| Complete Weil form $W=\Gamma+\text{poles}-P$ | Both poles, every prime power, all mixed entries, multiplicities |
| Twisted forms $W_\lambda$ | Which steps distinguish the actual source from bounded twins |
| Multiplicative incidence, walk energy | Divisibility, prime-power edges, harmonic mass, signed edge correlations |
| Sign gauge $\omega$, harmonic count $S_N=\sum\omega(n)/n$, $H_N=\sum1/n$, angle $c_N=S_N/H_N$ | Correlation of a gauge with the pole |
| Prime parity gauge $\omega_p(n)=(-1)^{v_p(n)}$ | The simplest non-Liouville completely multiplicative flip |
| Auxiliary sections | Explicit construction, vanishing orders, dimension, complexity |
| Orbit Toeplitz forms; signature counts | Every index difference; positive/negative indices, trace, Frobenius energy |
| Exhaustions | Source maps, domains, growing parameters, topology, uniform errors |

A **selective inequality** fails for a specified bounded twin; a **parity-breaking input** changes under Liouville twisting (necessary,
not sufficient). A **counting producer** constructs what it counts and proves its bound independently of the output sign; a
**receiver** translates a supplied bound into a sign. An **arithmetic Herglotz theorem** would produce Toeplitz positivity for a
prime-generated form from arithmetic. Finite incidence counts are exact; a count supplying the Weil sign must reach square-root
precision — do not conflate the two.

---

## 3. Mechanisms

1. **Pole-angle transfer.** On the harmonic hyperplane $\operatorname{Var}_{1/n}(\sqrt n\,\omega(n)x_n)\ge c_N^2\sum x_n^2$ (attained by the gauged pole's projection); with the
   sharp multiplicative Poincaré inequality, eventually and **uniformly over all sign gauges** (even $N$-dependent ones):
   $P_N(\omega x)\le(\log N-\gamma-(2\log2)c_N^2+\varepsilon)\sum x_n^2$. A signed harmonic count pays a prime gap.
2. **Prime parity pairing (exact counting producer).** Negative coordinates of $\omega_p$ are $p$ times positive ones:
   $p(H_N-S_N)=H_{\lfloor N/p\rfloor}+S_{\lfloor N/p\rfloor}$; hence $S_N/H_N\ge(p-1)/(p+1)$, with excess $(p+1)S_N-(p-1)H_N=\sum_{N/p<n\le N}(1+\omega_p(n))/n\in[0,2(1+\log p)]$, so
   $c_N\to(p-1)/(p+1)$ and the unconditional gap is $2\log2((p-1)/(p+1))^2$ (at $p=2$: $2\log2/9$; Liouville: 0).
3. **Sparse flips keep near-maximal gaps.** $\sum_{p\mid n,n\le N}1/n=H_{\lfloor N/p\rfloor}/p$: a single flip at a large prime has gap $\ge a$ for any $a<2\log2$, is completely
   multiplicative and keeps polar matching.
4. **Full-cone uniqueness kills them.** A full-Weil-positive weight equals $\Lambda$ on $n\ge2$; $\omega_p\Lambda$ has $-\log p$ at $p$, so each has a compact $C^2$ test with
   negative complete Weil functional (Gamma, poles, all prime powers retained).
5. **Ramanujan coordinates of prime parity.** Divisibility incidence writes the conductor-$m$ harmonic count as a finite Möbius sum of
   decimated parity counts $S_{\lfloor N/d\rfloor}$ with bounded boundary errors; normalized by $H_N$ it tends to
   $\frac{p-1}{p+1}\sum_{d\mid m}\mu(m/d)\,\omega_p(d)$, hence to 0 for every conductor $m\ge2$ coprime to $p$. A prime flip is visible only at
   conductors divisible by $p$.
6. **Counts determine actual eigenline coordinates.** Normalize both the parity constraint and the conductor-$m$ Ramanujan mode by
   $\sqrt{H_N}$. The mixed count is their exact inner product. The Ramanujan residual tends to zero, so projection onto its isolated
   prime eigenline changes that inner product by $o(1)$. The squared coordinate of the unit parity constraint therefore tends to
   $\left(\frac{p-1}{p+1}\frac{\sum_{d\mid m}\mu(m/d)\omega_p(d)}{\sqrt{\varphi(m)}}\right)^2$.
   This identifies a multiplicative constraint inside the actual finite spectrum; it does not bound its full orthogonal complement.
7. **Finite-prime density.** For any finite set $F$ of primes,
   $S_F(N)=c_FH_N+O_F(1)$ with $c_F=\prod_{p\in F}(p-1)/(p+1)>0$. Adding a prime gives an exact divisibility recurrence;
   the bounded harmonic shell and contraction under $N\mapsto\lfloor N/p\rfloor$ control its error. The resulting prime gap is
   $(2\log2)c_F^2$. Both the error constant and the eventual horizon retain their dependence on $F$.
8. **Finite-prime exhaustion separates quantifiers.** Flipping all primes below $Q$ agrees exactly with Liouville at every integer
   below $Q$. Each fixed cutoff is multiplicative, polar matched and positively gapped. Yet no positive gap holds with one horizon
   bound uniform in all sufficiently large cutoffs: choosing $Q>N$ would give the forbidden positive Liouville gap at horizon $N$.
9. **Large prime flips attain the maximal gap.** For every prime $p\ge11$ the flip $\omega_p$ has hyperplane gap exactly $2\log2$,
   the maximum over all sign gauges. In the two-scale decomposition of $[1,N]$ (smooth parts below a horizon $X$, rough fibres),
   the flipped pole $\omega_p(n)/\sqrt n$ differs from the pole only inside the $p$-ladders of the smooth box. Efron–Stein on the box,
   keeping the $p$-ladders separate, pays the within-$p$-fibre variance with the ladder constant $\log p\,W_p(X)\ge\log p(1+1/p)$
   rather than $2\log2$; the pairing of $\omega_p$ with a mean-zero function is controlled by that variance with constant
   $(1-c_p^2)W_p(X)$, $c_p=(p-1)/(p+1)$. The rotation of the pole therefore costs $2\log2(1-c_p^2)$ against an excess
   $c_p^2(\log p-2\log2)$, and $4p\cdot2\log2<(p-1)^2(\log p-2\log2)$ holds from $p=11$ on. The halo above $X$ and the variation of
   the rough masses below $X$ are paid by the walk energy and vanish with the horizon. Consequence: the exact discrete margin, even at
   its maximum and together with complete multiplicativity and polar matching, does not select $\Lambda$.
10. **Eleven is the exact single-prime cutoff.** Every hyperplane gap of $\omega_p$ is at most
   $p\log p/(p+3)$. The ground and conductor-$p$ eigenlines have limiting squared parity coordinates
   $c_p^2$ and $4c_p^2/(p-1)$; their exactly constrained plane gives this upper bound. For $p<11$ it is
   strictly below $2\log2$, since $p\le7$ and $7^7<2^{20}$. Together with the large-prime lower bound,
   $\omega_p$ attains the maximal gap if and only if $p\ge11$.
11. **A complete parity expansion with uniform error.** Let $c_p=(p-1)/(p+1)$ and truncate the Ramanujan tower at $p^K$:
   $z_{K,N}=c_pu_{1,N}+\sum_{k=1}^K(2c_p(-1)^k/\sqrt{\varphi(p^k)})u_{p^k,N}$.
   Its arithmetic profile equals $\omega_p(n)$ outside $p^K\mid n$, and equals $c_p(-1)^K$ on that fibre. Therefore
   $\|v_{p,N}-z_{K,N}\|^2=((1+c_p^2)H_{\lfloor N/p^K\rfloor}-2c_pS_p(\lfloor N/p^K\rfloor))/(p^KH_N)
   \le4p/((p+1)^2p^K)$ for every $N\ge1$. The bound is attained as $N\to\infty$;
   the squared coefficients sum to $1-4p/((p+1)^2p^K)$ and exhaust mass one. Individual spectral coordinates now assemble
   into a finite arithmetic approximation with an error uniform over the integer horizon.
12. **Cofinite flips expose the exhaustion topology.** Put $\eta_F=\lambda\omega_F$. Removing one prime sign gives
   $pS_{\eta_{F\cup\{p\}}}(N)-S_{\eta_{F\cup\{p\}}}(\lfloor N/p\rfloor)
   =pS_{\eta_F}(N)+S_{\eta_F}(\lfloor N/p\rfloor)$. The elementary Liouville square count and induction give
   $|S_{\eta_F}(N)|\le2/c_F$ for every horizon. Consequently every cofinite flip has greatest hyperplane gap zero.
   The harmonic squared distance $D_F(N)=H_N^{-1}\sum_{n\le N}(\omega_F(n)-\lambda(n))^2/n$ satisfies
   $D_F(N)=2-2S_{\eta_F}(N)/H_N$ and $|D_F(N)-2|\le4/(c_FH_N)$. Thus its horizon limit is two at every
   fixed prime cutoff, while its prime-cutoff limit is zero at every fixed horizon. Conversely, the zero-gap cofinite flips
   stabilize pointwise to the untwisted sign, whose greatest gap is $2\log2$.
13. **The counted tower has an exact secular root.** Its coefficients $a_0=c_p$ and
   $a_k=2c_p(-1)^k/\sqrt{\varphi(p^k)}$ have squared sum one. With $D_0=0$ and
   $D_k=k\log p+\log p/(p-1)$, the series $\sum_{k\ge0}a_k^2/(D_k-s)$ has a unique zero
   $\alpha_p$ in $(0,D_1)$. The higher tower has positive mass, so
   $\alpha_p<p\log p/(p+3)$. Identification with the actual constrained prime-matrix gap uses
   the finite constraint criterion and control of all omitted eigenlines.
14. **Reciprocal mass decides the finite constraint.** For a diagonal form with one negative weight
   $-b$ and positive weights $w_i$, the constraint $cx_0+\sum a_ix_i=0$, $c\ne0$, removes the
   negative direction exactly when $b\sum a_i^2/w_i\le c^2$. Weighted Cauchy–Schwarz proves
   sufficiency; $x_i=a_i/w_i$ proves necessity. A packet omitting only weights at least $\eta>0$
   loses at most its omitted squared coordinate mass divided by $\eta$. Orthonormal expansion gives
   the same exact criterion for the actual Hermitian form. Eventual packet bounds with convergent
   lower and upper limits pass to the whole scalar expression without a uniform packet horizon.
15. **The tower determines the full actual resolvent.** Let $E_{i,N}=\log N-\lambda_{i,N}-\gamma$,
   and $b_{i,N}=\langle v_{p,N},e_{i,N}\rangle$ for an actual orthonormal prime eigenbasis.
   For every $0<s<2\log2$, $\sum_i b_{i,N}^2/(E_{i,N}-s)$ converges to
   $\sum_{k\ge0}a_k^2/(D_k-s)$. A threshold between $s$ and $2\log2$ contains only the ground
   eventually. Every omitted reciprocal denominator is therefore bounded below by one fixed
   positive number. The selected tower mass exhausts one, controlling all remaining actual
   eigenlines, including those whose energies diverge. This transfers the whole scalar reading
   from counted arithmetic coordinates to the finite prime matrix.

---

## 4. Pillar theorems

1. **Pole-angle transfer** (`harmonicCorrelation_sq_mul_mass_le_variance`, `gaugeWitness_attains_variance_bound`,
   `eventually_prime_gap_ge_squared_correlation`).
2. **Prime parity pairing and its paid gap** (`prime_parity_pairing`, `prime_parity_boundary_bounds`, `primeFlip_harmonicCorrelation_tendsto`,
   `primeFlip_hasHyperplaneGap`, `two_adic_parity_has_gap_but_liouville_does_not`).
3. **A positive gap is weaker than selection** (`harmonicMass_multiples`, `every_submaximal_gap_has_a_nontrivial_multiplicative_twin`).
4. **Near-maximal gaps do not force Weil positivity**: no fixed gap threshold below $2\log2$, even with multiplicativity and polar
   matching, forces complete positivity (`primeFlip_exists_negative_complete_test`, `near_maximal_gaps_do_not_force_weil_positivity`).
5. **Harmonic Ramanujan coordinates of prime parity** (`gaugeHarmonicSum_divisibility`, `primeParityRamanujanSum_tendsto`,
   `primeParityRamanujanSum_tendsto_zero`).
6. **Counting-to-eigenline bridge** (`primeParityHorizonVector_inner`, `tendsto_primeParityWindowCoordinateSq`,
   `exists_primeParity_eigenline_coordinates`): exact harmonic counts determine orientation-independent coordinates on actual simple
   prime eigenlines.
7. **Positive density for every finite set of flips** (`finiteFlip_harmonic_recurrence`, `finiteFlip_harmonic_error_bounded`,
   `finiteFlip_harmonicCorrelation_tendsto`, `finiteFlip_hasHyperplaneGap`).
8. **Exact exhaustion obstruction with positive finite stages** (`finitePrimeExhaustion_eventually_eq_liouville`,
   `finitePrimeExhaustion_each_stage_matched_positive`, `finitePrimeExhaustion_no_uniform_positive_gap`).
9. **The maximal gap is not rigid** (`boxGap_mul_boxVar_add_le`, `sum_flip_mul_sq_le`, `eventually_primeFlip_poleDefect_ge`,
   `primeFlip_hasHyperplaneGap_two_mul_log_two`, `isGreatest_primeFlip_hyperplaneGap`, `maximal_gap_does_not_select_the_source`):
   every prime $p\ge11$ gives a completely multiplicative, polar-matched sign twin with the greatest hyperplane gap $2\log2$,
   Weil coefficients of the size of $\Lambda$, and a negative complete Weil test.
10. **Exact threshold and small-prime obstruction** (`primeFlip_hyperplaneGap_le_prime_log_div`,
   `smallPrimeFlip_has_positive_but_not_maximal_gap`, `primeFlip_hasHyperplaneGap_two_mul_log_two_iff`):
   every single-prime flip has gap at most $p\log p/(p+3)$, and maximal-gap attainment is equivalent to $p\ge11$.
11. **Uniform Ramanujan tower exhaustion** (`primeParityTowerProfile_value`, `primeParityTowerVector_eq_ramanujan`,
   `primeParityTower_error_sq_eq`, `primeParityTower_error_sq_le`, `tendsto_primeParityTower_error_sq`,
   `primeParityTower_coefficient_mass`, `tendsto_primeParityTower_coefficient_mass`, `primeParityTower_uniform_exhaustion`).
   Exact divisibility counts supply the uniform norm bound and its sharp constant.
12. **Cofinite zero gaps and distinct harmonic limits** (`cofiniteFlip_harmonic_recurrence`,
   `cofiniteFlip_harmonicSum_abs_le`, `isGreatest_cofiniteFlip_hyperplaneGap`,
   `finiteFlipLiouvilleDistanceSq_error_le`, `finitePrimeExhaustion_two_harmonic_limits`,
   `cofinitePrimeExhaustion_eventually_eq_one`). A bounded arithmetic count gives an exact gap classification
   and identifies the harmonic distance discarded by pointwise convergence.
13. **Exact arithmetic secular data** (`primeParityTowerEnergy_eq`,
   `primeParityTowerCoefficient_sq_succ`, `hasSum_primeParityTowerCoefficient_sq`,
   `primeParitySecularRoot_spec`, `primeParitySecularRoot_unique`). The existing infinite secular
   theory applies to the counted parity tower and gives a strictly improved candidate gap.
14. **Finite constraint and exhaustion tools** (`diagonal_hyperplane_nonneg_iff`,
   `reciprocal_mass_le_packet_add_tail`, `exists_negative_diagonal_on_hyperplane`,
   `one_negative_diagonal_nonneg_iff`, `hermitian_hyperplane_bound_iff`,
   `tendsto_of_eventual_packet_bounds`). These classical criteria retain every spectral direction
   and expose the precise tail estimate needed for arithmetic transfer.
15. **Actual resolvent convergence** (`primeParityTowerCoefficient_eq_moebius`,
   `exists_primeParity_tower_eigenline`, `eventually_fullPrime_ground_count_one`,
   `primeParityTowerEnergy_strictMono`, `primeParityTowerEnergy_ge_excitation`,
   `tendsto_primeParityFiniteResolvent`). Every unselected eigenline is included in the remainder bound.

**Pillar obligations** (targets, not theorems): count before sign (an integer-side construction with square-root error);
arithmetic selection on overlapping complete sources; uniform mixed-term control through exhaustion; a displacement-sensitive
signature bound or uniform complete-source index ceiling; obstructions with positive content.

---

## 5. Traps

| Temptation | Correction |
|---|---|
| A Gram representation settles the sign | Prove equality with the literal complete form |
| Multiplicativity breaks parity | Liouville is completely multiplicative |
| A positive, even maximal, selective gap identifies the source | Single-prime flips at $p\ge11$ have the maximal gap $2\log2$ and keep polar matching |
| Positive arithmetic weights select $\zeta$ | Test scalings, mixtures, golden data, Beurling systems |
| Finite counts or ranks retain signs | Record exact correlations and what reweighting loses |
| A fixed arithmetic mode controls a full spectrum | Bound its orthogonal complement uniformly |
| Finite-horizon positivity passes to the limit | State the topology, error currency, uniformity |
| Positive gaps at every finite prime cutoff give a gap after exhaustion | Their horizon bounds need not be uniform; finite flips stabilize to Liouville |
| Pointwise arithmetic convergence controls the optimal gap | Zero-gap cofinite flips converge pointwise to the untwisted maximal-gap sign |
| Positive measures explain arithmetic Herglotz | Positivity must come from arithmetic, not zeros |
| A no-go completes a route | Extract its positive survivor |

Battery: Liouville twin, scaled $\Lambda$, quadratic mixtures, golden curve, over-regular Beurling systems, Davenport–Heilbronn.

---

## 6. Open problems

1. **Exact gap values** for the flips at $p\le7$, between the counted lower bound
   $(2\log2)((p-1)/(p+1))^2$ and the upper bound $p\log p/(p+3)$; classification for multiple-prime flips;
   the information beyond a maximal gap needed to select the source. The single-prime cutoff for maximal-gap attainment is settled.
2. **Selective overlap transfer**: carry the discrete hyperplane gap into continuous atomic families beyond the Robin–Euler threshold, paying the
   affine pole direction separately.
3. **Arithmetic Herglotz theory**: Toeplitz positivity from prime-side data with Gamma and poles.
4. **Integer-side auxiliary vanishing**: arithmetic sections replacing the Frobenius lattice annihilator with controlled complexity and
   vanishing; parity-sensitive input exposed before any sieve count.
5. **Finite-rank renormalization**: a uniform index ceiling for the complete source, retaining the first prime layer (endpoint: finite
   off-line support ⇒ a fixed zero-free strip).
6. **Exact inertia counting**: an observable separating a reflected pair from two critical points at depth $\asymp1/\log T$.
7. **Structural questions**: why the smallest prime fixes both the dyadic generator and the sharp gap; what survives the parity barrier;
   the heat-flow reality horizon $\exp((27/40+\varepsilon)/t)$ as $t\to0$; a topology preserving complete inequalities under exhaustion.

## 7. Tools to build

Signed incidence counts with exact mixed entries; selective overlap transfer; arithmetic Herglotz constructions; integer-side
auxiliary sections; displacement-sensitive inertia counts.

## 8. Contribution standard

A new unconditional count, paid sign, energy bound, index ceiling or sharp classification, with its arithmetic construction,
domain, growing-parameter dependence, battery behaviour and relation to an open mechanism. First decisive success: selective
positivity past the Robin–Euler point, a new displacement-sensitive census bound, or a uniform finite-index bound for the complete
source.
