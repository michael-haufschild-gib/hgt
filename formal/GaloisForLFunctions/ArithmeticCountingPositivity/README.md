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

**Pillar obligations** (targets, not theorems): count before sign (an integer-side construction with square-root error);
arithmetic selection on overlapping complete sources; uniform mixed-term control through exhaustion; a displacement-sensitive
signature bound or uniform complete-source index ceiling; obstructions with positive content.

---

## 5. Traps

| Temptation | Correction |
|---|---|
| A Gram representation settles the sign | Prove equality with the literal complete form |
| Multiplicativity breaks parity | Liouville is completely multiplicative |
| A positive selective gap identifies the source | Single-prime flips have gaps arbitrarily close to $2\log2$ and keep polar matching |
| Positive arithmetic weights select $\zeta$ | Test scalings, mixtures, golden data, Beurling systems |
| Finite counts or ranks retain signs | Record exact correlations and what reweighting loses |
| A fixed arithmetic mode controls a full spectrum | Bound its orthogonal complement uniformly |
| Finite-horizon positivity passes to the limit | State the topology, error currency, uniformity |
| Positive measures explain arithmetic Herglotz | Positivity must come from arithmetic, not zeros |
| A no-go completes a route | Extract its positive survivor |

Battery: Liouville twin, scaled $\Lambda$, quadratic mixtures, golden curve, over-regular Beurling systems, Davenport–Heilbronn.

---

## 6. Open problems

1. **Exact gap classification** among completely multiplicative gauges: determine the gaps of small-prime and multiple-prime flips,
   and the information beyond a maximal gap needed to select the source.
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
