# Bézout–Valuation Incidence Mechanics (`GaloisForLFunctions.BezoutValuationIncidence`)

## 1. What This Field Is & Why It Exists

Every classical tool in analytic number theory—and every pure scale-correlation tool in
[`BiScaleUncertainty`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BiScaleUncertainty/README.md)—operates
inside a single group or monoid geometry at a time:
- **Additive / Fourier / Dispersion Theory** on $(\mathbb{Z}, +)$ (Poisson summation, large sieve,
  Bombieri–Vinogradov, Kuznetsov trace formulas) uses the additive group structure of $\mathbb{Z}$,
  so it fails for Beurling generalized integers, **but** it generates orthogonality only by averaging
  over external character families $\chi \pmod q$ or spectral shifts $t$. At the degenerate point of
  **one character, modulus one, shift zero**, its off-diagonal control collapses (**Wall 7**), and
  its frequency-space norms treat $\{\log n\}$ as generic frequencies, unable to distinguish
  $\log 4 = 2\log 2$ from $\log 6 = \log 2 + \log 3$ (**Wall 11**).
- **Multiplicative / Dirichlet-Convolution / Sieve Theory** on $(\mathbb{N}_{\ge 1}, \times)$
  (Euler products, Selberg $\Lambda^2$ diagonalization, Vaughan/Heath-Brown identities, Barban–Vehov
  weights) survives the single-character degenerate point and distinguishes prime powers $p^a$
  ($\Lambda(4) = \log 2$) from multi-prime composites ($\Lambda(6) = 0$) via $\Lambda = \mu * \log$,
  **but** its identities hold verbatim in Beurling generalized number systems where the Riemann
  Hypothesis is false (**Wall 9**), and its polynomial length is capped at the archimedean Nyquist /
  parity horizon $\theta = 1$ (**Wall 1 / Wall 10**).
- **Bi-Scale / Logarithmic-Grid Uncertainty Theory (`BiScaleUncertainty`)** studies translation
  autocorrelations $h_f(u) = (f \star \tilde{f})(u)$ sampled on $\Lambda_{\log} = \{\log n\}$ against
  hyperbolic weights $\cosh(u/2)$ and $e^{u/2}/\sinh u$. Because continuous additive translation in
  $u = \log x$ is **multiplicative dilation** $x \mapsto e^u x$ on $\mathbb{R}_+^\times$ rather than
  integer addition $n \mapsto n + 1$ on $\mathbb{N}$, `BiScaleUncertainty` treats $\{\log n\}$ as a
  1-dimensional point process on $\mathbb{R}_u$, where $\log 4 \approx 1.386$ and
  $\log 6 \approx 1.792$ are merely two sample locations.

As established in [`docs/reports/wall1.md`](file:///Users/michael/Documents/code/hgt/docs/reports/wall1.md),
any mechanism capable of breaking **Wall 1** must simultaneously satisfy **four structural requirements**:
1. **Fail for Beurling systems** (by using the additive ring structure of $\mathbb{N}$: $n \mapsto n + 1$,
   distributivity $d(q + 1) = dq + d$, and $\gcd(k, k + 1) = 1$).
2. **Survive the degenerate point** (operating on a single arithmetic sequence at **one character,
   modulus one, shift zero**, without external character or spectral averaging).
3. **Carry information beyond polynomial length equal to height ($\theta > 1$)** at square-root
   precision (reaching across the $N = M$ horizon up to $N^2 \asymp M^2$, $\theta = 2$).
4. **Distinguish $\log 4$ from $\log 6$ (Wall 11)** (separating prime-power nodes $p^a$ with
   $\omega(p^a) = 1, \Lambda(p^a) = \log p \ne 0$ from multi-prime composite nodes with
   $\omega(n) \ge 2, \Lambda(n) = 0$).

**Bézout–Valuation Incidence Mechanics (`GaloisForLFunctions.BezoutValuationIncidence`)** is the
foundational mathematical field built to satisfy all four requirements simultaneously. Instead of
starting on the 1D logarithmic line $\mathbb{R}_u$, its primitive state space couples:
- the **infinite-dimensional prime valuation lattice** $\mathbb{N}_0^{(\mathcal{P})}$
  ($n = \prod_p p^{v_p(n)}$, governed by mixed multiplicative difference operators
  $\Delta_{\mathcal{P}}^\times = \prod_p \Delta_p^\times$), and
- the **1-dimensional archimedean successor line** $(\mathbb{N}, T_+ : k \mapsto k + 1)$,
intertwined by **Pronic Bézout Successor Splitting** ($d_1 \mid k \wedge d_2 \mid (k + 1) \iff d_1 d_2 \mid k(k + 1)$
with $\gcd(d_1, d_2) = 1$) and **Quotient-Dual Octave Reciprocity** ($d \leftrightarrow m = k / d$
across trans-horizon octaves $R = \lfloor (k - 1)/N \rfloor$).

---

## 2. Core Mathematical Objects & Language

| Concept | Mathematical Definition & Role |
| :--- | :--- |
| **1D Multiplicative Axis Difference (`mulAxisDiff`)** | $\Delta_d^\times F(m) = F(d m) - F(m)$; along any single scale $d \ge 1$, $\Delta_d^\times \log(m) = \log d > 0$ ($d \ge 2$), preserving prime-power gradients such as $\Delta_2^\times \log(2) = \log 4 - \log 2 = \log 2$. |
| **2D Mixed Multiplicative Difference (`mixedMulDiff`)** | $\Delta_{d_1, d_2}^\times F(m) = F(d_1 d_2 m) - F(d_1 m) - F(d_2 m) + F(m)$; annihilates $n \mapsto \log n$ identically ($\Delta_{d_1, d_2}^\times \log(m) = 0$), killing composite 2-cells such as $6 = 2 \cdot 3$. |
| **Pronic Successor Sequence (`pronicSeq`)** | $P(k) = k(k + 1)$; the product of consecutive integers under $T_+$, satisfying $\gcd(k, k + 1) = 1$, $\Lambda(k(k + 1)) = 0$ for all $k \ge 2$, and reaching scale $M(M + 1) > M^2$ ($\theta = 2$) for $k \in [1, M]$. |
| **Sieve & Centered Sieve Responses (`sieveSeq`, `centeredSieveSeq`)** | $s_{N,c}(k) = \sum_{d \in [1, N], d \mid k} c(d)$ and $\widetilde{s}_{N,c}(k) = \sum_{d \in [2, N], d \mid k} c(d)$, related by $s_{N,c}(k) = c(1) + \widetilde{s}_{N,c}(k)$ for $N \ge 1$. |
| **Bézout Successor Pair Sets (`bezoutSuccessorPairSet`, `centeredBezoutSuccessorPairSet`)** | Pairs $(d_1, d_2) \in [1, N]^2$ (resp. $[2, N]^2$) with $d_1 \mid k$ and $d_2 \mid (k + 1)$; every such pair is automatically coprime ($\gcd(d_1, d_2) = 1$) and maps injectively to $n = d_1 d_2 \mid k(k + 1)$. |
| **$R$-Octave Dual Möbius Operator (`dualMoebiusOctaveSum`)** | $\mathcal{M}_R(k) = -\sum_{m \in [1, R], m \mid k} \mu(k / m)$; equals $s_{N,\mu}(k)$ identically on the $R$-th trans-horizon octave $R N < k \le (R + 1)N$, compressing length-$N$ divisor sums to length-$R$ quotient sums. |
| **Truncated Logarithmic Möbius Sieve (`truncLogMoebiusSum`)** | $\Lambda_N(k) = -\sum_{d \in [1, N], d \mid k} \mu(d)\log d$; equals $\Lambda(k)$ for $1 \le k \le N$ and $\Lambda(k) + \mu(k)\log k$ on the first trans-horizon octave $N < k \le 2N$. |
| **Bézout Successor Incidence Count (`bezoutIncidenceCount`)** | $\mathcal{I}_{\mathrm{Bez}}(M; d_1, d_2) = \#\{k \in [1, M] : d_1 \mid k \wedge d_2 \mid (k + 1)\}$; counts Chinese Remainder idempotent hits modulo $d_1 d_2$ across $[1, M]$, satisfying $\mathcal{I}_{\mathrm{Bez}}(M + d_1 d_2; d_1, d_2) = \mathcal{I}_{\mathrm{Bez}}(M; d_1, d_2) + 1$ for $\gcd(d_1, d_2) = 1$ and remaining non-zero up to $d_1 d_2 \le M(M + 1)$ ($\theta = 2$). |
| **Bézout Unitary Coprime Form (`bezoutCoprimeQuadraticForm`)** | $\mathcal{Q}_{\mathrm{Bez}}(N, c) = \sum_{\substack{d_1, d_2 \in [1, N] \\ \gcd(d_1, d_2) = 1}} \frac{c(d_1)c(d_2)}{d_1 d_2} = \sum_{e=1}^N \mu(e)\,Y_{N,c}(e)^2$; the asymptotic density of $\sum_{k=1}^M s_{N,c}(k)s_{N,c}(k+1)$, simultaneously diagonalized in Selberg's coordinates $Y_{N,c}(e) = \sum_{d \le N, e \mid d} c(d)/d$ with eigenvalue $\mu(e)$ in place of $\varphi(e)$. |
| **Bézout Sawtooth Defect & Remainder (`bezoutSawtoothDefect`, `bezoutSawtoothRemainderForm`)** | $\delta_{\mathrm{Bez}}(M; d_1, d_2) = \mathcal{I}_{\mathrm{Bez}}(M; d_1, d_2) - \mathbf{1}_{\gcd(d_1, d_2)=1}\frac{M}{d_1 d_2} \in [-1, 1]$ and $\mathcal{R}_{\mathrm{Bez}}(M, N, c) = \sum_{d_1, d_2 \le N} c(d_1)c(d_2)\,\delta_{\mathrm{Bez}}(M; d_1, d_2)$. |
| **GCD–LCM Modular Valuation Functions (`IsGcdLcmModular`)** | Functions $F : \mathbb{N} \to \mathbb{R}$ satisfying $F(1) = 1$ and $F(j)\,F(k) = F(\operatorname{lcm}(j, k))\,F(\gcd(j, k))$; automatically coprime-multiplicative, pronic-multiplicative ($F(k)F(k+1) = F(k(k+1))$), and obeying exact pronic–diagonal–gradient conservation $(\nabla_+ F(k))^2 + 2 F(\operatorname{pronicSeq}(k)) = F(k)^2 + F(k+1)^2$. |
| **Radical Prime-Factor Product (`radicalPrimeProd`)** | $\tau_w(n) = \prod_{p \in n.\mathrm{primeFactors}} (1 - w(p))$ for an arbitrary prime-valuation weight $w : \mathbb{N} \to \mathbb{R}$; satisfies `IsGcdLcmModular`, radical/power invariance $\tau_w(n^k) = \tau_w(n)$, divisor absorption $\tau_w(d m) = \tau_w(m)$ ($d \mid m$), divisor-ordering antitonicity ($d \mid m \implies \tau_w(m) \le \tau_w(d)$ for $w \in [0, 1]$), submultiplicativity $\tau_w(a)\tau_w(b) \le \tau_w(ab)$, and specializes to `pmPowerDampedDivisorCoeff ε` at $w(p) = p^{-\varepsilon}$. |
| **Three-Way Sawtooth Partition (`weightedCenteredSawtoothSum`, `activeCenteredSawtoothSum`, `inactiveCenteredSawtoothSum`, `bezoutInteriorSawtoothSum`)** | Decomposition $W_{N,c}(n) = A_{N,c}(n, n) + A_{N,c}(n+1, n) + I^{\mathrm{Bez}}_{N,c}(n)$ into the post-jump active peak ($d \mid n$), the pre-jump active trough ($d \mid (n+1)$), and the doubly-inactive Bézout interior sum ($d \nmid n \wedge d \nmid (n+1)$); the active pair equals $-\frac{1}{2}\nabla_+(s_{N,c} - s_{N, c/d})(n)$ and telescopes identically over finite intervals. |
| **Five Canonical Spectral Quadratic Forms (`sieveVariance`, `sieveSuccessorCovariance`, `sieveSuccessorReserve`, `successorPhaseLoss`, `sievePrimitiveEnergy`)** | Simultaneously diagonalized in the Selberg multiples basis $Y_{N,c}(q) = \sum_{d \le N, q \mid d} c(d)/d$ with modal weights $\varphi(q)$, $\mu(q)$, $\varphi(q) - \mu(q)$, $\varphi(q) - \mu(q)^2/\varphi(q)$, and $\frac{1}{12} J_2(q) = \frac{1}{12}\psi(q)\varphi(q)$. |
| **Second Jordan Totient & Dedekind Psi Ratio (`jordanTotient2`, `dedekindPsiReal`)** | $J_2(n) = \sum_{d \mid n} \mu(n/d) d^2$ and $\psi(n) = J_2(n)/\varphi(n)$ with $\psi(p^{k+1}) = p^k(p+1)$, $\psi(p) = p + 1 = \varphi(p) - 2\mu(p)$, $J_2(p) = (\varphi(p) - \mu(p))^2 - 1$, and sharp prime-attained lower bound $(q + 1)\varphi(q) \le J_2(q)$ for all $q \ge 2$. |
| **Gcd-Orbit Projection & Coprimality Predictor (`sieveGcdProjection`, `sieveSuccessorPredictor`)** | $\Gamma_h c$ orthogonally projects all five spectral quadratic forms onto resonant modes $q \mid h$ (bounding primitive energy by $\frac{1}{16} h^2 \operatorname{sieveVariance}$ independent of $N$), while `sieveSuccessorPredictor` achieves the unique minimum one-step prediction error `successorPhaseLoss`. |
| **Renormalized Prefix Defect (`sieveRenormalizedPrefixDefect`)** | $\mathcal{D}^{\mathrm{ren}}_{N,M}(c) = \mathcal{D}_{N,M}(c) - M \cdot \operatorname{sieveSuccessorReserve}(N, c) = \sum_{k=1}^M s_{N,c}(k)\bigl(s_{N,c}(k+1) - s_{N,c}(k)\bigr)$; eliminates the linear reserve drift and is non-positive on sub-horizon prefixes $M + 1 \le N$ for all radical weights. |

---

## 3. How the Theory Works: Core Mechanisms

### 3.1 Mixed-Difference Calculus on the Prime Valuation Complex vs. 1D Prime Fibers (Wall 11)
On the prime valuation lattice $\mathbb{N}_0^{(\mathcal{P})}$ ($n = \prod_p p^{v_p(n)}$), Dirichlet
convolution with $\mu$ is the global mixed backward difference $\Delta_{\mathcal{P}}^\times = \prod_p \Delta_p^\times$.
Because the archimedean scale embedding $\log n = \sum_p v_p(n)\log p$ is **additively separable
across prime axes**, every 2D mixed multiplicative difference vanishes identically
(`mixedMulDiff_log_eq_zero`):
$$\Delta_{d_1, d_2}^\times \log(m) = \log(d_1 d_2 m) - \log(d_1 m) - \log(d_2 m) + \log m = 0 \qquad (\forall d_1, d_2, m \ge 1).$$
At $n = 6 = 2^1 \cdot 3^1$ (a 2-dimensional cell with $\omega(6) = 2$),
$\Delta_{2, 3}^\times \log(1) = \log 6 - \log 2 - \log 3 + \log 1 = 0$. By contrast, along any
1-dimensional prime fiber $n = p^a$ ($\omega(p^a) = 1$, such as $n = 4 = 2^2$), only a single prime
difference acts (`mulAxisDiff_log_eq_log`):
$$\Delta_2^\times \log(2) = \log 4 - \log 2 = \log 2 > 0.$$
This is the exact geometric reason why composite nodes ($\log 6$) lie in the flat kernel of
$\Delta_{\mathcal{P}}^\times \log = \Lambda$, whereas prime-power nodes ($\log 4$) carry persistent
non-zero gradient (`wall11_mixed_difference_log4_vs_log6`).

### 3.2 Pronic Bézout Successor Splitting & Total Annihilation of Prime Powers
In $\mathbb{N}$, stepping by the additive successor $T_+ : k \mapsto k + 1$ orthogonalizes prime
supports: $\gcd(k, k + 1) = 1$ (`coprime_self_succ`). Consequently, for any pair of divisors
$d_1 \mid k$ and $d_2 \mid (k + 1)$:
1. **Automatic Coprimality & Unique Factor Recovery (`coprime_of_dvd_self_succ`, `gcd_mul_self_succ_eq`):**
   $\gcd(d_1, d_2) = 1$, and the individual factors are uniquely recovered from their product
   $n = d_1 d_2 \mid k(k + 1)$ via $d_1 = \gcd(n, k)$ and $d_2 = \gcd(n, k + 1)$.
2. **Exact Pronic Divisor Bijection (`image_mul_bezoutSuccessorPairSet_eq_divisors`):**
   At every fixed $k \ge 1$ and $N \ge k + 1$, the map $(d_1, d_2) \mapsto d_1 d_2$ is a strict
   1-to-1 bijection from `bezoutSuccessorPairSet N k` onto `Nat.divisors (k(k + 1))`, factoring
   $\sum_{n \mid k(k + 1)} F(n) = s_{N,F}(k)\,s_{N,F}(k + 1)$ for every coprime-multiplicative $F$
   (`sum_divisors_pronicSeq_eq_sieveSeq_mul_succ`).
3. **Total Prime-Power Annihilation on Centered Successor Pairs
   (`not_isPrimePow_mul_of_coprime`, `vonMangoldt_mul_eq_zero_of_mem_centeredBezoutSuccessorPairSet`):**
   In the centered successor correlation $\widetilde{s}_{N,c}(k)\,\widetilde{s}_{N,c}(k + 1)$
   (where $d_1, d_2 \ge 2$), because $\gcd(d_1, d_2) = 1$ and $d_1, d_2 \ge 2$, the product
   $n = d_1 d_2$ has at least two distinct prime factors ($\omega(n) \ge 2$). Thus **every prime and
   every prime power $p^a$ (including $4 = 2^2$) is 100% annihilated** ($\neg\operatorname{IsPrimePow}(d_1 d_2)$
   and $\Lambda(d_1 d_2) = 0$), while composite products starting at $6 = 2 \cdot 3$ are attained
   (`wall11_four_excluded_six_attained`). In particular, $\Lambda(k(k + 1)) = 0$ for every $k \ge 2$
   (`vonMangoldt_pronicSeq_eq_zero`).

### 3.3 Quotient-Dual Octave Reciprocity & $2$-Adic Valuation Switching ($\theta > 1$)
For any $k \ge 2$, $\sum_{d \mid k} \mu(d) = 0$, so the length-$N$ truncated Möbius sieve sum equals
the negative of the high-divisor sum (`sieveSeq_moebiusReal_eq_neg_sum_gt`):
$$s_{N,\mu}(k) = \sum_{\substack{d \mid k \\ d \le N}} \mu(d) = -\sum_{\substack{d \mid k \\ d > N}} \mu(d)
  = -\sum_{\substack{1 \le m < k/N \\ m \mid k}} \mu(k / m).$$
On the $R$-th trans-horizon octave $R N < k \le (R + 1)N$, the dual quotient $m = k / d$ is restricted
to $1 \le m \le R$, compressing a length-$N$ divisor sum into the $R$-term operator $\mathcal{M}_R(k)$:
- **First Trans-Horizon Octave ($N < k \le 2N$, $R = 1$):**
  Only $m = 1$ ($d = k$) exceeds $N$, so $s_{N,\mu}(k) = -\mu(k)$, $s_{N,\mu}(k)^2 = \mu(k)^2$, and
  $s_{N,\mu}(k)s_{N,\mu}(k + 1) = \mu(k)\mu(k + 1)$ (`sieveSeq_moebiusReal_first_octave`).
- **Second Trans-Horizon Octave ($2N < k \le 3N$, $R = 2$) — $2$-Adic Valuation Switching:**
  Only $m \in \{1, 2\}$ contribute (`sieveSeq_moebiusReal_second_octave`):
  $$s_{N,\mu}(k) = -\mu(k) - \mathbf{1}_{2 \mid k}\,\mu(k / 2).$$
  - **Total Annihilation of $v_2(k) = 1$ ($\log 6$ Sector, `sieveSeq_moebiusReal_second_octave_two_mul_odd_eq_zero`):**
    For every odd $u$ with $2u \in (2N, 3N]$, $\mu(2u) = -\mu(u)$, so
    $s_{N,\mu}(2u) = -\mu(2u) - \mu(u) = 0$ identically!
  - **Activation of $v_2(k) = 2$ ($\log 4$ Sector, `sieveSeq_moebiusReal_second_octave_four_mul_odd`):**
    For every odd $u$ with $4u \in (2N, 3N]$, $\mu(4u) = 0$ while $\mu(2u) = -\mu(u)$, so
    $s_{N,\mu}(4u) = 0 - (-\mu(u)) = \mu(u)$!

### 3.4 Trans-Horizon LCM Fibre Parity Collapse & Logarithmic Octave Splitting
1. **LCM Fibre Parity Collapse on $(N, 2N]$ (`sievedLcmFibre_moebius_first_octave`):**
   Combining the Möbius LCM fibre inversion $F_{N,\mu}(L) = \mu(L) + \sum_{d \mid L, d > N} \mu(L/d) s_{N,\mu}(d)^2$
   with $s_{N,\mu}(L)^2 = \mu(L)^2$ on $N < L \le 2N$ proves that for every $L \in [N + 1, 2N]$:
   $$F_{N,\mu}(L) = \mu(L) + \mu(L)^2 = \begin{cases} 0 & \text{if } \mu(L) = -1 \text{ (odd number of prime factors, e.g. primes } p\text{)}, \\ 2 & \text{if } \mu(L) = +1 \text{ (even number of prime factors, e.g. } 6 = 2\cdot 3\text{)}, \\ 0 & \text{if } \mu(L) = 0 \text{ (non-squarefree, e.g. } 4 \mid L\text{)}. \end{cases}$$
   In particular, $F_{N,\mu}(L) \ge 0$ across the entire first post-horizon octave, and
   $F_{N,\mu}(p) = 0$ for every prime $p \in [N + 1, 2N]$ (`sievedLcmFibre_moebius_prime_first_octave_eq_zero`).
2. **Logarithmic / Von Mangoldt First-Octave Split (`truncLogMoebiusSum_first_octave`):**
   On $N < k \le 2N$, $\Lambda_N(k) = -\sum_{d \mid k, d \le N} \mu(d)\log d = \Lambda(k) + \mu(k)\log k$,
   which vanishes identically on all primes $p \in (N, 2N]$, equals $\log p$ on prime powers
   $p^a \in (N, 2N]$ ($a \ge 2$), and equals $\mu(k)\log k$ on multi-prime composites.

### 3.5 Discrete Dirichlet Energy Polarization, CRT Bézout Periodicity & Super-Horizon Reach ($\theta = 2$)
1. **Discrete Dirichlet Energy Polarization (`sum_addDiff_sieveSeq_sq_eq`):**
   The unit additive difference energy $\sum_{k=1}^M (s_{N,c}(k + 1) - s_{N,c}(k))^2$ couples the
   Same-Node Selberg/LCM second moment $\sum_{k=1}^M s_{N,c}(k)^2$ directly to the Successor-Node
   Bézout quadratic form $\sum_{k=1}^M s_{N,c}(k)s_{N,c}(k + 1)$.
2. **CRT Bijection, One-Per-Period Recurrence & Super-Horizon Reach up to $\theta = 2$
   (`image_bezoutResidueMap_Icc_eq`, `card_bezoutIntervalSet_period_eq_one`, `bezoutIncidenceCount_eq_div_add_rem`, `bezoutIncidence_super_horizon_reach`):**
   In a Same-Node Sieve ($L = \operatorname{lcm}(d_1, d_2) \mid k$), any modulus $L > M$ has
   $\lfloor M / L \rfloor = 0$ hits in $k \in [1, M]$, rendering the sieve completely blind beyond
   $\theta = 1$. In the Bézout Successor Sieve ($d_1 \mid k \wedge d_2 \mid (k + 1)$), the residue
   map $k \mapsto (k \bmod d_1, (k + 1) \bmod d_2)$ is a bijection on every contiguous period
   $[A + 1, A + d_1 d_2]$ (`image_bezoutResidueMap_Icc_eq`), so every period of length $d_1 d_2$
   contains **exactly one** solution (`card_bezoutIntervalSet_period_eq_one`), giving
   $$\mathcal{I}_{\mathrm{Bez}}(M; d_1, d_2) = \left\lfloor \frac{M}{d_1 d_2} \right\rfloor + \mathcal{I}_{\mathrm{Bez}}\bigl(M \bmod (d_1 d_2);\ d_1, d_2\bigr), \qquad \mathcal{I}_{\mathrm{Bez}}\bigl(M \bmod (d_1 d_2);\ d_1, d_2\bigr) \in \{0, 1\},$$
   while attaining non-zero hits inside $k \in [1, M]$ for moduli $d_1 d_2 = d(d + 1)$ all the way up
   to **$M(M + 1) > M^2$ ($\theta = 2$)** (`bezoutIncidence_super_horizon_reach`).

### 3.6 Simultaneous Selberg–Möbius Diagonalization, Wall 11 Spectral Separation, & the Universal $1/2$-Decorrelation Law on $\ker P$
Expanding $\mathbf{1}_{\gcd(d_1, d_2) = 1} = \sum_{e \mid \gcd(d_1, d_2)} \mu(e)$ proves that the
Bézout unitary coprime quadratic form $\mathcal{Q}_{\mathrm{Bez}}(N, c)$ is **simultaneously
diagonalized** in the exact same Selberg coordinates $Y_{N,c}(e) = \sum_{d \le N, e \mid d} c(d)/d$
as $\mathcal{Q}_{\mathrm{Sel}}(N, c) = \sum_{e=1}^N \varphi(e)\,Y_{N,c}(e)^2$, with diagonal
eigenvalue $\mu(e)$ in place of Euler's totient $\varphi(e)$
(`bezoutCoprimeQuadraticForm_eq_moebius_diagonal`):
$$\mathcal{Q}_{\mathrm{Bez}}(N, c) = \sum_{e=1}^N \mu(e)\,Y_{N,c}(e)^2.$$
This simultaneous diagonalization exposes three structural phenomena:
1. **Universal Pole Cancellation (`selbergSubBezoutQuadraticForm_eq_Icc_two`) & Prime Weight Recovery (`totient_sub_moebiusReal_prime`):**
   Because $\varphi(1) = \mu(1) = 1$, the $e = 1$ harmonic-pole mode $Y_{N,c}(1)^2$ cancels out of
   $\mathcal{Q}_{\mathrm{Sel}}(N, c) - \mathcal{Q}_{\mathrm{Bez}}(N, c) = \sum_{e=2}^N (\varphi(e) - \mu(e)) Y_{N,c}(e)^2$
   for **every** weight $c$ (even off $\ker P$!), and at every prime $p$, the totient $-1$ defect in
   $\varphi(p) = p - 1$ is repaired by $-\mu(p) = +1$: $\varphi(p) - \mu(p) = p$.
2. **Breaking Euler's Totient Degeneracy at Wall 11 (`wall11_totient_degeneracy_broken_by_bezout`):**
   In the classical Selberg sieve, Euler's totient is degenerate at Wall 11:
   $\varphi(4) = \varphi(6) = 2$. Subtracting the Bézout eigenvalue $\mu(e)$ breaks this degeneracy:
   $$\varphi(4) - \mu(4) = 2 - 0 = 2 \;\ne\; 1 = 2 - 1 = \varphi(6) - \mu(6).$$
3. **The Universal $1/2$-Decorrelation & Coercivity Law on $\ker P$ (`two_mul_moebiusReal_le_totient`,
   `two_mul_bezoutCoprimeQuadraticForm_le_selberg_of_harmonic_eq_zero`,
   `selberg_and_mean_square_le_dirichlet_energy_of_harmonic_eq_zero`):**
   For every integer $e \ge 2$, $\varphi(e) \ge 2\mu(e)$ (with **unique sharp equality at the Wall 11
   node $e = 6 = 2 \cdot 3$**, where $\varphi(6) = 2 = 2\mu(6)$!). Consequently, on $\ker P$
   ($Y_{N,c}(1) = 0$), the Bézout successor form is universally bounded by **one-half** of the
   Selberg form:
   $$2\,\mathcal{Q}_{\mathrm{Bez}}(N, c) \le \mathcal{Q}_{\mathrm{Sel}}(N, c) \le 2\bigl(\mathcal{Q}_{\mathrm{Sel}}(N, c) - \mathcal{Q}_{\mathrm{Bez}}(N, c)\bigr),$$
   and at every finite horizon $M \ge 1$, both $M\,\mathcal{Q}_{\mathrm{Sel}}(N, c)$ and
   $\sum_{k=1}^M s_{N,c}(k)^2$ are coerced by the additive Dirichlet energy plus the signed sawtooth
   defects (`selberg_and_mean_square_le_dirichlet_energy_of_harmonic_eq_zero`).

### 3.7 Fermi–Nyman Cellular Jump Reciprocity & First-Octave Pronic Tail Bridge
On each reciprocal cell $I_n = (\frac{1}{n+1}, \frac{1}{n}]$ (of Lebesgue measure
$\frac{1}{n(n+1)} = \frac{1}{\operatorname{pronicSeq}(n)}$), the cellular Fermi–Nyman response
$\operatorname{fermiCellResponse}(N, c, n) = \sum_{d=1}^N c(d)\operatorname{fermiCellMatrix}(d, n)$
decomposes into dyadic prefix sums of `sieveSeq N c` (`fermiCellResponse_eq_two_prefix_half_sub_prefix`):
$$\operatorname{fermiCellResponse}(N, c, n) = 2 \sum_{k=1}^{\lfloor n/2 \rfloor} s_{N,c}(k) - \sum_{k=1}^n s_{N,c}(k).$$
Its inter-cell jump across $t = \frac{1}{n+1}$ is
$2\,\mathbf{1}_{2 \mid (n+1)}\,s_{N,c}\!\bigl(\frac{n+1}{2}\bigr) - s_{N,c}(n+1)$
(`fermiCellResponse_succ_sub_eq`), where no two consecutive boundaries can both activate $2 \mid m$
(`not_two_dvd_self_and_succ`). Across the entire first trans-horizon tail octave $N + 1 \le n \le 2N$,
$\lfloor n / 2 \rfloor \le N$ freezes the half-scale prefix sum of $s_{N,\mu}$ at $1$, so:
- $\operatorname{fermiCellResponse}(N, \mu, n) = 1 + \sum_{k=N+1}^n \mu(k)$
  (`fermiCellResponse_moebiusReal_first_octave`),
- every inter-cell jump is purely $\mu(m) = -s_{N,\mu}(m)$ (`fermiCellResponse_moebiusReal_jump_first_octave`),
- consecutive jump products equal the Bézout successor correlation $s_{N,\mu}(m)s_{N,\mu}(m+1) = \mu(m)\mu(m+1)$
  (`fermiCellResponse_moebiusReal_jump_mul_succ_first_octave`), and
- on $I_n$, `dilatedMobiusFermiCombinator 1 N` has cell $L^2$ energy
  $(1 + \sum_{k=N+1}^n \mu(k))^2 / \operatorname{pronicSeq}(n)$
  (`setIntegral_cell_normSq_dilatedMobiusFermiCombinator_one_first_octave`).

Uniform strict-half-power bounds for these response increments are exactly RH:
`mobiusFirstOctavePowerSaving_iff_riemannHypothesis` quantifies every `δ > 0` and one
constant independent of `N,n` on `1 ≤ N < n ≤ 2N`. The proof passes through the proved
Mertens–Littlewood equivalence; no classical-converse hypothesis remains. Establishing
the increment bound from arithmetic is still open. The raw combined prefix defect has
a different normalization and retains its proved sublinear-bound obstruction.

### 3.8 Autonomous GCD–LCM Valuation-Lattice Algebra, Radical Prime-Factor Products & Exact Three-Step Primorial Bézout Hierarchy
Every arithmetic function $F : \mathbb{N} \to \mathbb{R}$ satisfying `IsGcdLcmModular F`
($F(1) = 1$ and $F(j)\,F(k) = F(\operatorname{lcm}(j, k))\,F(\gcd(j, k))$) obeys an autonomous
valuation-successor calculus (`GeneralRadicalMultiplicativeAndGcdLcmValuationAlgebra`):
- **Coprime & Pronic Multiplicativity (`IsGcdLcmModular.mul_succ_eq_pronicSeq`):**
  $F(k)\,F(k + 1) = F(\operatorname{pronicSeq}\,k)$ and $F(d k)\,F(d k + 1) = F(d k (d k + 1))$.
- **Exact Pronic–Diagonal–Gradient Conservation (`IsGcdLcmModular.addDiff_sq_add_two_mul_pronicSeq`, `IsGcdLcmModular.sum_Icc_pronicSeq_add_addDiff_sq_eq`):**
  Pointwise, $(\nabla_+ F(k))^2 + 2 F(\operatorname{pronicSeq}\,k) = F(k)^2 + F(k + 1)^2$, so over
  every interval $[1, M]$, $\sum_{k=1}^M F(\operatorname{pronicSeq}\,k) + \frac{1}{2}\sum_{k=1}^M (\nabla_+ F(k))^2 = \sum_{m=1}^M F(m)^2 + \frac{1}{2}(F(M+1)^2 - F(1)^2)$.
- **General Radical Prime-Factor Products (`radicalPrimeProd`):**
  For any prime weight $w : \mathbb{N} \to \mathbb{R}$, $\tau_w(n) = \prod_{p \in n.\mathrm{primeFactors}} (1 - w(p))$
  satisfies `isGcdLcmModular_radicalPrimeProd`, radical/power invariance (`radicalPrimeProd_pow`),
  divisor absorption (`radicalPrimeProd_mul_of_dvd`), divisor-ordering antitonicity
  (`radicalPrimeProd_le_of_dvd`), and universal submultiplicativity (`radicalPrimeProd_mul_le`).
- **Exact Three-Step Primorial Bézout Factorization & Even-Start Cubic Ceiling (`ThreeStepPrimorialBezoutAndEvenCubicCeiling`):**
  Because $\gcd(k, k + 2) = \gcd(k, 2) \in \{1, 2\}$ (`gcd_self_add_two_eq_gcd_two`) and
  $\gcd(k(k + 2), k + 1) = 1$ (`coprime_mul_add_two_succ`), every three-step product satisfies the
  **exact 3-step Bézout factorization law** (`radicalPrimeProd_three_step_mul_eq`):
  $$\tau_w(k)\,\tau_w(k + 1)\,\tau_w(k + 2) = \bigl(\text{if } 2 \mid k \text{ then } 1 - w(2) \text{ else } 1\bigr)\,\tau_w\bigl(k(k + 1)(k + 2)\bigr).$$
  Consequently, on odd-start triples ($2 \nmid k$), $\tau_w(k)\tau_w(k+1)\tau_w(k+2) = \tau_w(k(k+1)(k+2)) \le (1 - w(2))(1 - w(3))$
  (attained at $k = 1$), whereas on even-start triples ($2 \mid k$, where $24 \mid k(k+1)(k+2)$,
  `twenty_four_dvd_mul_succ_mul_add_two_of_two_dvd`), the product obeys the **sharp cubic ceiling**
  $(1 - w(2))^2(1 - w(3))$ (`radicalPrimeProd_three_step_mul_le_cubic_of_two_dvd`, attained at $k = 2$).

### 3.9 Sawtooth Midpoint Annihilation, Active-Divisor Square Invariance, & Shifted-Exponent Totient Suppression (`ε ↦ 1 + ε`)
Across each additive step $n \mapsto n + 1$, partitioning `weightedCenteredSawtoothSum N c k` into
`activeCenteredSawtoothSum N c (n + 1) k` ($d \mid (n + 1)$) and `inactiveCenteredSawtoothSum N c (n + 1) k`
($d \nmid (n + 1)$) reveals (`SawtoothMidpointAnnihilationAndActiveDivisorSquareInvariance`,
`ActiveSawtoothClosedFormAndShiftedExponentTotientBridge`, `ActiveDeletedMartingaleAndShiftedEulerConvergence`):
- **Active Sign Flip & Square Cancellation (`activeCenteredSawtoothSum_succ_eq_neg`, `activeCenteredSawtoothSum_succ_sq_eq_sq`):**
  Every dividing modulus flips from $+(d-1)/(2d)$ at $n$ to $-(d-1)/(2d)$ at $n + 1$, so its square
  cancels 100% identically in $W_{N,c}(n + 1)^2 - W_{N,c}(n)^2$.
- **Exact Sieve Closed Form & Active-Deleted Martingale Identity (`active_diagonal_reduction`):**
  Because $A_{N,c}(n + 1, n) = -\frac{1}{2}(s_{N,c}(n + 1) - s_{N, c/d}(n + 1))$, absorbing
  $2 \Delta W_{N,c}(n)\,A_{N,c}(n + 1, n)$ into the diagonal square $(\Delta W_{N,c}(n))^2$ replaces
  $(s_{N,c}(n + 1) - Y(1))^2$ by the **active-deleted product**
  $(s_{N,c}(n + 1) - Y(1))(s_{N, c/d}(n + 1) - Y(1))$. For Route PM ($c_\varepsilon(d) = \mu(d)d^{-\varepsilon}$),
  dividing by $d$ shifts the damping exponent from $\varepsilon$ to $1 + \varepsilon$, suppressing
  the local prime Euler factor gap by an extra factor of $1/p$ (`pmShiftedExponentFactor_gap_eq_div_p`).

### 3.10 Universal Bézout Interior Sawtooth Martingale Identity, Two-Point Post-Step Smoothing & Boundary-Free Active-Pair Dissipation
Because $\gcd(n, n + 1) = 1$, the inactive set $\{d \le N : d \nmid (n + 1)\}$ at step $n$ contains
the **predecessor post-jump active divisors** $\{d \le N : d \mid n, d \ge 2\}$ at their positive
peak $A_{N,c}(n, n) = +\frac{1}{2}(s_{N,c}(n) - s_{N, c/d}(n))$. Extracting both $A_{N,c}(n + 1, n)$
and $A_{N,c}(n, n)$ leaves the **doubly-inactive Bézout interior sawtooth sum**
`bezoutInteriorSawtoothSum N c n` (`BezoutPronicInteriorSawtoothAndPredecessorPeakSplit`,
`UniversalSawtoothInteriorMartingaleAndPostStepCalculus`):
- **Universal Bézout Interior Martingale Identity (`weightedCenteredSawtoothSum_succ_sq_sub_sq_eq_bezout_interior`):**
  For **every** cutoff $N : \mathbb{N}$, weight $c : \mathbb{N} \to \mathbb{R}$, and step $n : \mathbb{N}$,
  the diagonal square is eliminated 100% identically in favor of the **Bézout successor covariance**
  plus the harmonic-divided forward difference:
  $$W_{N,c}(n + 1)^2 - W_{N,c}(n)^2 =
    \bigl(s_{N,c}(n) - Y_{N,c}(1)\bigr)\bigl(s_{N,c}(n + 1) - Y_{N,c}(1)\bigr) +
    \bigl(s_{N,c}(n + 1) - Y_{N,c}(1)\bigr)\,\nabla_+ s_{N, c/d}(n) +
    2\bigl(s_{N,c}(n + 1) - Y_{N,c}(1)\bigr)\,\operatorname{bezoutInteriorSawtoothSum}\,N\,c\,n.$$
- **Universal Two-Point Bézout Smoothing (`addDiff_inactiveCenteredSawtoothSum_at_self`):**
  The forward difference of the post-step inactive sawtooth sum $n \mapsto I_{N,c}(n, n)$ replaces
  the raw impulse $s_{N,c}(n + 1) - Y(1)$ by the **two-point Bézout average**
  $\frac{1}{2}\bigl((s_{N,c}(n) - Y(1)) + (s_{N,c}(n + 1) - Y(1))\bigr) + \frac{1}{2}\nabla_+ s_{N, c/d}(n)$.
- **Universal Boundary-Free Active-Pair Dissipation (`sum_bezout_active_pair_martingale_compensated_eq`):**
  Because $A_{N,c}(1, 1) = 0$ for every weight $c$, the self-interaction of the Bézout active pair
  in the compensated Pronic Abel sum has zero boundary term at $n = 1$ and is purely non-positively
  dissipative (`sum_bezout_active_pair_martingale_compensated_le`).

### 3.11 Optimal Successor Prediction, Irreducible $3/4$ Phase-Loss Floor, & Gcd-Orbit Projection
On the complete factorial period $N!$, the optimal linear divisor-sieve predictor of $s_{N,c}(k + 1)$
from divisor indicators at $k$ is the explicit **coprimality predictor** `sieveSuccessorPredictor N c`
with Selberg coordinates $Y_{N, b_*}(q) = \frac{\mu(q)}{\varphi(q)} Y_{N,c}(q)$
(`OptimalSuccessorPredictionAndExactPhaseLoss`, `SharpSuccessorPhaseLossAndClosureClassification`,
`IteratedSuccessorPredictionAndReservePhaseLossSplit`):
- **Exact Pythagorean Error Decomposition (`successorPredictionError_pythagoras`):**
  Every candidate weight $b$ has squared prediction error
  $\operatorname{successorPhaseLoss}(N, c) + \mathcal{Q}_{\mathrm{Sel}}(N, b - b_*)$, where
  $$\operatorname{successorPhaseLoss}(N, c) = \sum_{q=3}^N \left(\varphi(q) - \frac{\mu(q)^2}{\varphi(q)}\right) Y_{N,c}(q)^2.$$
- **Sharp Universal $[3/4, 1]$ Phase-Loss Sandwich (`successorPhaseLoss_bounds`):**
  At every sieve level $N$, $\frac{3}{4}\operatorname{sieveVarianceAboveParity}(N, c) \le \operatorname{successorPhaseLoss}(N, c) \le \operatorname{sieveVarianceAboveParity}(N, c)$,
  with lower equality iff $Y_{N,c}$ is supported on $\{3, 6\}$ (`successorPhaseLoss_lower_eq_iff`)
  and zero phase loss iff $c(d) = 0$ for all $d \in [3, N]$ (`sieve_successor_representable_iff`).
  Iterating the optimal predictor contracts variance above parity by $4^{-m}$
  (`sieveVarianceAboveParity_iterated_successorPredictor_le`).

### 3.12 The Five-Form Spectral Triad, Dedekind's Psi Ratio $\psi(n) = J_2(n)/\varphi(n)$, & Renormalized Prefix Defect Duality
The discrete mean square of `weightedCenteredSawtoothSum N c` over its factorial period is governed
by the second Jordan totient $J_2(q) = \psi(q)\varphi(q)$ (`DiscretePrimitiveEnergyAndJordanComparison`,
`JordanUpperBoundAndGcdOrbitPrimitiveEnergy`, `DedekindPsiJordanTotientAndFiveFormSpectralSynthesis`):
- **Prime Algebraic Bridge & Sharp $(q + 1)\varphi(q) \le J_2(q)$ Bound (`jordanTotient2_prime_eq_totient_moebius`, `add_one_mul_totient_le_jordanTotient2`):**
  At every prime $p$, $\psi(p) = p + 1 = \varphi(p) - 2\mu(p)$ and
  $J_2(p) = \varphi(p)(\varphi(p) - 2\mu(p)) = (\varphi(p) - \mu(p))^2 - 1$. For all $q \ge 2$,
  $(q + 1)\varphi(q) \le J_2(q) \le \frac{3}{4} q^2 \varphi(q)$ (sharp at every prime $p$ on the left
  and at $q = 2$ on the right), yielding the parity-split energy chain
  (`three_mul_sieveVariance_add_above_parity_le_twelve_mul_sievePrimitiveEnergy`):
  $$3\,\operatorname{sieveVariance}(N, c) + \operatorname{successorPhaseLoss}(N, c) \le
    3\,\operatorname{sieveVariance}(N, c) + \operatorname{sieveVarianceAboveParity}(N, c) \le
    12\,\operatorname{sievePrimitiveEnergy}(N, c) \le
    \frac{3}{4} N^2\,\operatorname{sieveVariance}(N, c).$$
- **Simultaneous Gcd-Orbit Projection of All Five Quadratic Forms (`bezoutValuationIncidence_master_five_form_synthesis`):**
  For every stride $h \ge 1$, `sieveGcdProjection N h c` simultaneously restricts the Selberg
  diagonals of all five canonical forms to resonant divisors $q \mid h$ and satisfies
  $16\,\operatorname{sievePrimitiveEnergy}(N, \Gamma_h c) \le h^2 \operatorname{sieveVariance}(N, c)$
  completely independent of $N$ (`sixteen_mul_sievePrimitiveEnergy_gcdProjection_le_stride_sq`).
- **Renormalized Prefix Defect Non-Positivity (`sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_nonpos`):**
  Subtracting the linear drift $M \cdot \operatorname{sieveSuccessorReserve}(N, c)$ from the combined
  prefix defect yields $\mathcal{D}^{\mathrm{ren}}_{N,M}(c) = \sum_{k=1}^M s_{N,c}(k)\nabla_+ s_{N,c}(k)$,
  which is unconditionally $\le 0$ for all sub-horizon prefixes $M + 1 \le N$ and all $\varepsilon \ge 0$.

### 3.13 Non-Markovian Compressed Translation Operator Algebra, Valuation Visibility Clock, & Prime-Power Revival
On the native finite-dimensional Hilbert space `SieveCoefficientSpace N` (equipped with the exact
full-period mean-square norm and diagonalized by the isometric Selberg–Ramanujan transform
`weightedSelbergIsometry N`, see `SelbergHilbertCoordinateEquivalence`), compressing true integer
translation $k \mapsto k + h$ to the divisor-sieve subspace yields the commuting self-adjoint
operator family $\mathcal{C}_h = \operatorname{nativeSieveTranslationPredictor}\,N\,h$ with
eigenvalue (`TrueTranslationPredictionAndExactCompression`, `ValuationVisibilityClockAndRamanujanSupport`,
`NonMarkovianLagOperatorAlgebraAndPrimePowerRevival`):
$$\lambda_q(h) = \operatorname{sieveLagMultiplier}\,q\,h = \frac{\mu\bigl(q / \gcd(q, h)\bigr)}{\varphi\bigl(q / \gcd(q, h)\bigr)}.$$
- **The Valuation Visibility Clock (`lagVisibilityClock`, `sieveLagMultiplier_ne_zero_iff`):**
  Mode $q \ge 1$ is non-zero under $\mathcal{C}_h$ if and only if its **visibility clock**
  $$\operatorname{lagVisibilityClock}(q) = \frac{q}{\operatorname{rad}(q)} = \prod_{p \mid q} p^{v_p(q) - 1}$$
  divides $h$. Thus squarefree modes ($\operatorname{lagVisibilityClock}(q) = 1$) are visible at
  every lag $h \ge 1$, whereas non-squarefree modes are completely erased at lag $1$ and first become
  visible at $h = q / \operatorname{rad}(q)$ (`sieveLagScheduleRecovers_iff`,
  `sieveLagScheduleRecovers_initial_iff`).
- **Coprime Multiplicativity & Three-Regime Prime-Power Law (`sieveLagMultiplier_mul_of_coprime`, `sieveLagMultiplier_prime_pow_trichotomy`):**
  For coprime $q_1, q_2$ and every lag $h$, $\lambda_{q_1 q_2}(h) = \lambda_{q_1}(h)\,\lambda_{q_2}(h)$.
  At prime powers $q = p^{a+1}$ ($a \ge 0$):
  $$\lambda_{p^{a+1}}(h) = \begin{cases} 1 & \text{if } p^{a+1} \mid h, \\ -\frac{1}{p - 1} & \text{if } p^a \mid h \text{ and } p^{a+1} \nmid h, \\ 0 & \text{if } p^a \nmid h. \end{cases}$$
- **Failure of the Markov Semigroup Law & Non-Markovian Prime-Power Revival (`nonMarkovianLagDefect_prime_pow_revival`, `norm_nativeNonMarkovianDefect_sq`):**
  Unlike true translation on the ambient sequence space, compressed translation is **non-Markovian**:
  $\mathcal{C}_{h_1 + h_2} - \mathcal{C}_{h_1}\mathcal{C}_{h_2}$ acts on mode $q$ by
  $\operatorname{nonMarkovianLagDefect}(q, h_1, h_2) = \lambda_q(h_1 + h_2) - \lambda_q(h_1)\lambda_q(h_2)$.
  For every non-squarefree prime power $p^{a+1}$ ($a \ge 1$, starting at Wall 11's $q = 4 = 2^2$),
  every sub-clock lag $1 \le h < p^a$ is completely erased ($\lambda_{p^{a+1}}(h) = 0$), yet any
  two positive sub-clock lags $h_1, h_2 \ge 1$ with $h_1 + h_2 = p^a$ (such as $h_1 = 1$ and
  $h_2 = p^a - 1$) combine to **revive** mode $p^{a+1}$ at the visibility clock $p^a$ with
  non-Markovian semigroup defect $-1/(p - 1) \ne 0$.

### 3.14 Period-Free Pronic Discrepancy Von Mangoldt Duality, Multi-Scale Prime-Dilation Gram Dichotomy, & Short-Horizon Bounds
The finite-prefix discrepancy
$\operatorname{sievePrefixDiscrepancy}(N, M, c) = \sum_{k=1}^M s_{N,c}(k) - M \cdot \operatorname{finiteHarmonicSum}(N, c)$
admits an exact period-free representation in terms of the individual $e$-periodic Ramanujan
primitives $R_e(M) = \operatorname{pmRamanujanPrimitive}\,e\,M$ ($2 \le e \le N$)
(`ExactFinitePrefixDiscrepancyDualityAndReturnTimes`, `ShortHorizonPronicDiscrepancyAndVonMangoldtDuality`):
$$\operatorname{sievePrefixDiscrepancy}(N, M, c) = \sum_{e=2}^N \operatorname{Re} R_e(M)\,Y_{N,c}(e).$$
1. **The Pronic-Weighted Discrepancy Von Mangoldt Duality Theorem (`hasSum_sievePrefixDiscrepancy_div_pronicSeq`, `tsum_sievePrefixDiscrepancy_mode_probe_div_pronicSeq`):**
   Integrating the finite-prefix discrepancy against the Bézout pronic measure
   $1 / \operatorname{pronicSeq}(M) = 1 / (M(M + 1))$ over all natural horizons $M \ge 1$ (with **no
   reference to $N!$**) projects the Selberg multiples coordinates directly onto **minus the von Mangoldt
   function**:
   $$\sum_{M=1}^\infty \frac{\operatorname{sievePrefixDiscrepancy}(N, M, c)}{\operatorname{pronicSeq}(M)}
     = -\sum_{e=2}^N \Lambda(e)\,Y_{N,c}(e).$$
   In particular, probing with a pure Selberg mode `sieveModeWeight N q` ($2 \le q \le N$) yields
   $-\Lambda(q)$, which **annihilates every composite non-prime-power mode** (such as $q = 6$)
   identically (`tsum_sievePrefixDiscrepancy_mode_probe_eq_zero_of_not_isPrimePow`) while extracting
   $-\log p \ne 0$ on every prime power $q = p^a$.
2. **Period-Free Uniform Dual-Energy Ceiling & Short-Horizon $L^2$ Bounds (`sievePrefixDualEnergy_le_periodFreeDualCeiling`, `sum_Icc_sievePrefixDiscrepancy_sq_le`, `sum_Icc_sievePrefixDiscrepancy_sq_div_pronicSeq_le`):**
   Because each $R_e(M)$ is periodic with period $e \le N$, the dual energy
   $\operatorname{sievePrefixDualEnergy}(N, M) = \sum_{e=2}^N (\operatorname{Re} R_e(M))^2 / \varphi(e)$
   is bounded uniformly in $M$ (without $N!$) by `sievePeriodFreeDualCeiling N`, and at prime modes
   $p$ satisfies $(\operatorname{Re} R_p(M))^2 / \varphi(p) = (M \bmod p)^2 / (p - 1) \le \varphi(p)$.
   Consequently, over any short horizon $H \ge 1$, the cumulative squared discrepancy on $[1, H]$ is
   bounded by $H \cdot \operatorname{sieveVariance}(N, c) \cdot \operatorname{sievePeriodFreeDualCeiling}(N)$,
   and the pronic-weighted squared discrepancy sum is bounded uniformly for all $H \ge 1$ by
   $(1 - \frac{1}{H + 1})\operatorname{sieveVariance}(N, c)\operatorname{sievePeriodFreeDualCeiling}(N)$.
3. **Non-Periodic Pronic Discrepancy Gram Form & Multi-Scale Prime-Dilation Dichotomy (`hasSum_sievePrefixDiscrepancy_sq_div_pronicSeq`, `pmRamanujanPrimitiveGram_two_mode_dilation_identity`, `tendsto_pmRamanujanPrimitiveGram_prime_mul_not_isPrimePow`):**
   The infinite pronic-weighted squared discrepancy series converges unconditionally to the quadratic
   form $\operatorname{sievePronicDiscrepancyGramForm}(N, c) = \sum_{p, q \in [2, N]} Y_{N,c}(p) Y_{N,c}(q) \mathcal{G}(p, q)$
   where $\mathcal{G}(p, q) = \operatorname{pmRamanujanPrimitiveGram}\,p\,q$. Under prime dilation
   $q \mapsto p q$ ($p \nmid q$), $\mathcal{G}(p q, p q) = (p - 1)\mathcal{G}(q, q) - 2\mathcal{G}(p q, q)$,
   decomposing the two-mode Gram form on $\{q, p q\}$ into:
   $$u^2\mathcal{G}(q, q) + 2uv\mathcal{G}(p q, q) + v^2\mathcal{G}(p q, p q) = \bigl(u^2 + (p - 1)v^2\bigr)\mathcal{G}(q, q) - 2v(v - u)\mathcal{G}(p q, q),$$
   while as $p \to \infty$ through primes, $\mathcal{G}(p q, q) \to \frac{1}{2}\varphi(q)\Lambda(q) - \mathcal{G}(q, q)$,
   which is strictly negative ($-\mathcal{G}(q, q) < 0$) for every non-prime-power $q$ and shifted by
   $+\frac{1}{2}\varphi(q)\log p_0$ for every prime power $q = p_0^a$.

### 3.15 Sharp Initial-Prefix Observability ($H = N - 1$), Unimodular Smith Normal Form, Prime-Power Legendre Obstructions, & the $2N - 3$ Return-Window Theorem
1. **Sharp Initial-Prefix Observability & Exact Gram Determinants (`SharpInitialPrefixObservabilityAndExactGramDeterminants`):**
   At level $N = n + 1$, the first $n = N - 1$ prefix discrepancies uniquely determine all
   non-constant divisor weights $c(2), \dots, c(N)$ (`sievePrefix_initial_zero_iff_variance_zero`).
   The $(n \times n)$ initial floor-discrepancy observation matrix has exact determinant
   $(-1)^n / (n + 1)$, the initial Ramanujan primitive matrix has determinant $(-1)^n n!$, and the
   positive-definite variance-dual Gram matrix has exact determinant
   $(n!)^2 / \prod_{e=2}^{n+1} \varphi(e)$.
2. **Unimodular Smith Normal Form & Prime-Power Legendre Valuation Obstructions (`IntegralPrefixLatticeAndPrimePowerObstructions`):**
   After clearing denominators by $(n + 1)!$, the integer initial-prefix observation matrix is
   unimodularly equivalent over $\mathbb{Z}$ (via explicit unit-determinant triangular divisor
   reduction and column rotation) to the diagonal matrix $\operatorname{diag}(1, 2, \dots, n)$
   (`sievePrefixScaledIntegerObservationMatrix_smith`). Consequently, over $\mathbb{Z}/p^a\mathbb{Z}$,
   the kernel cardinality is $p^{\sum_{r=1}^a \lfloor n / p^r \rfloor}$ (Legendre's factorial
   valuation!), and any integer weight vector invisible mod $p^a$ on $[1, n]$ has Euclidean norm at
   least $p^a / \sqrt{n(n + 1)(2n + 1)/6}$.
3. **The $2N - 3$ Return-Window Reflection Symmetry & Two-Moment Kernel (`ReturnWindowTwoMomentKernelsAndSharpZeroBlocks`):**
   Every Ramanujan primitive $R_e$ ($e \ge 2$) satisfies the reflection symmetry
   $R_e(L - 1 - r) = R_e(r) - \varphi(e)$ around any common return multiple $L$ of
   $\operatorname{lcm}(1, \dots, N)$, so the centered discrepancy is odd around $L - 1/2$ and
   carries **zero new linear information** on $[L - N, L - 1]$. Conversely, any contiguous zero block
   of length $2N - 3$ forces $c(2) = \dots = c(N) = 0$ (and $2N - 4$ is sharp!). Adding the single
   quadratic observable $\sum_{M=1}^{N-1} \operatorname{sievePrefixDiscrepancy}(N, M, c) = -\frac{1}{2}\sum_{e=2}^N \varphi(e) Y_{N,c}(e) + \text{prefix sum}$
   extends observability across return boundaries.

### 3.16 Three-Step Bézout Interior Sawtooth Calculus & Second-Order Outer-Pair Smoothing
In `ThreeStepBezoutInteriorSawtoothAndSecondOrderSmoothing`, the doubly-inactive Bézout interior
sawtooth sum `bezoutInteriorSawtoothSum N c n` (and its horizon-free Route PM counterpart
`pmBezoutInteriorPrefix ε n`) is shown to obey an exact second-order smoothing law:
- **Outer-Pair Two-Step Bézout Smoothing (`addDiff_bezoutInteriorSawtoothSum_eq_outer_pair_avg`, `addDiff_pmBezoutInteriorPrefix_eq_outer_pair_avg`):**
  Because $\operatorname{bezoutInteriorSawtoothSum}(N, c, n) = W_{N,c}(n) + \frac{1}{2}\nabla_+(s_{N,c} - s_{N, c/d})(n)$,
  taking the forward difference $\nabla_+$ cancels the middle impulse $s_{N,c}(n + 1)$ identically against
  $-\frac{2}{2} s_{N,c}(n + 1)$ from the second difference, leaving the **outer-pair two-step average**
  of the impulses at $n$ and $n + 2$ minus half the second-order difference of the harmonic-divided
  sieve $s_{N, c/d}$:
  $$\nabla_+\bigl(\operatorname{bezoutInteriorSawtoothSum}\,N\,c\bigr)(n) =
    \frac{1}{2}\Bigl(\bigl(s_{N,c}(n) - Y_{N,c}(1)\bigr) + \bigl(s_{N,c}(n + 2) - Y_{N,c}(1)\bigr)\Bigr)
    - \frac{1}{2}\,\nabla_+^2 s_{N, c/d}(n).$$
- **Pure Lag-1 Pronic Covariance Reduction (`sieveSeq_sub_mul_addDiff_bezoutInteriorSawtoothSum_eq_pronic_avg`):**
  When multiplied by the middle impulse $s_{N,c}(n + 1) - Y_{N,c}(1)$, both outer-pair endpoints $n$
  and $n + 2$ lie at unit distance $|(n + 1) - n| = |(n + 2) - (n + 1)| = 1$ from $n + 1$, reducing
  the product to the symmetric average of two consecutive **lag-1 coprime pronic covariances** with
  zero diagonal square and zero lag-2 cross-term.

---

## 4. Classical Foundations vs. Autonomous Theorems of `BezoutValuationIncidence`

To evaluate `BezoutValuationIncidence` by the standards of modern mathematics, it is essential to
distinguish the **classical coordinates** it uses as input from the **new structural theorems** it
establishes:
- **Classical Coordinates Used:** Selberg's multiples coordinate change $Y_{N,c}(e) = \sum_{d \le N, e \mid d} c(d)/d$
  (Selberg 1947), Ramanujan sums $c_q(h)$ and their Möbius–totient evaluation (Ramanujan 1918,
  Kluyver 1906), and the complete-period Bernoulli sawtooth covariance $\frac{1}{12}\frac{\gcd(a,b)^2}{ab}$
  (Franel–Landau 1924).
- **What Makes `BezoutValuationIncidence` an Independent Mathematical Field:**
  Classical sieve theory studies single-node divisibility $d \mid k$ (the LCM lattice), while
  classical Fourier/circle-method analysis studies additive characters $e(\alpha k)$. Neither studies
  the **joint algebraic, operator-theoretic, lattice-theoretic, and martingale geometry of consecutive
  and multi-step divisibility $d_1 \mid k,\, d_2 \mid (k + 1),\dots$ coupled to the prime valuation
  lattice**. Specifically, `BezoutValuationIncidence` discovers and proves:
  1. **The Non-Markovian Compressed Translation Algebra & Prime-Power Revival (`NonMarkovianLagOperatorAlgebraAndPrimePowerRevival`, `ValuationVisibilityClockAndRamanujanSupport`, `ArithmeticLagSchedulesAndSharpRecoveryHorizon`):**
     Compressing additive translation $T_h$ to the divisor-sieve Hilbert space breaks the Markov
     semigroup law ($T_{h_1 + h_2} \ne T_{h_1} T_{h_2}$): non-squarefree prime powers $p^{a+1}$ ($a \ge 1$)
     are completely erased at all sub-clock lags $1 \le h < p^a$ (`lagVisibilityClock(p^{a+1}) = p^a`),
     then **spontaneously revive** at $h = p^a$ with eigenvalue $-1/(p - 1)$.
  2. **Pronic-Weighted Discrepancy Von Mangoldt Duality & Multi-Scale Gram Recurrence (`ShortHorizonPronicDiscrepancyAndVonMangoldtDuality`):**
     Without any $N!$ period, integrating the finite-prefix discrepancy against the Bézout pronic
     measure $1 / (M(M + 1))$ maps Selberg coordinates $Y_{N,c}(e)$ to the **von Mangoldt functional**
     $-\sum_{e=2}^N \Lambda(e) Y_{N,c}(e)$, annihilating all composite non-prime-power modes while
     generating a non-periodic Gram matrix $\mathcal{G}(p, q)$ governed by the exact prime-dilation
     law $\mathcal{G}(p q, p r) + \mathcal{G}(p q, r) + \mathcal{G}(q, p r) = (p - 1)\mathcal{G}(q, r)$.
  3. **Unimodular Smith Normal Form & Prime-Power Legendre Obstructions for Initial Discrepancy Prefixes (`SharpInitialPrefixObservabilityAndExactGramDeterminants`, `IntegralPrefixLatticeAndPrimePowerObstructions`, `ReturnWindowTwoMomentKernelsAndSharpZeroBlocks`):**
     Exact determinant formulas $(-1)^n / (n + 1)$, $(-1)^n n!$, and $(n!)^2 / \prod_{e=2}^{n+1} \varphi(e)$,
     explicit unimodular reduction of the scaled integer prefix observation matrix to
     $\operatorname{diag}(1, 2, \dots, n)$, exact mod-$p^a$ Legendre kernel dimension $\sum_{r=1}^a \lfloor n/p^r \rfloor$,
     and the sharp $2N - 3$ return-window zero-block theorem.
  4. **The Five-Form Spectral Geometry & $\{2, 3, 4, 6\}$ Extreme-Ray Polytope (`OptimalSuccessorPredictionAndExactPhaseLoss`, `SharpSuccessorPhaseLossAndClosureClassification`, `SharpPrimitiveEnergySuccessorFrontier`, `DedekindPsiJordanTotientAndFiveFormSpectralSynthesis`):**
     The joint spectral geometry of the five canonical forms ($\varphi$, $\mu$, $\varphi - \mu$,
     $\varphi - \mu^2/\varphi$, $\frac{1}{12}\psi\varphi$), the sharp $3/4$ phase-loss floor attained
     uniquely on $\{3, 6\}$, and the exact 3D convex hull of normalized `(covariance, reserve, primitive energy)`
     spanned by the four arithmetic modes $\{2, 3, 4, 6\}$.
  5. **Universal Sawtooth Active-Deleted & Bézout Interior Martingale Renormalization (`ActiveDeletedMartingaleAndShiftedEulerConvergence`, `UniversalSawtoothInteriorMartingaleAndPostStepCalculus`, `ThreeStepBezoutInteriorSawtoothAndSecondOrderSmoothing`, `GeneralRadicalMultiplicativeAndGcdLcmValuationAlgebra`, `ThreeStepPrimorialBezoutAndEvenCubicCeiling`):**
     The exact elimination of the divergent diagonal square $(s_{N,c}(n + 1) - Y(1))^2$ across
     $n \mapsto n + 1$ by absorbing the pre-jump trough ($d \mid (n + 1)$) and predecessor post-jump
     peak ($d \mid n$), reducing the square increment to the coprime pronic covariance, the
     harmonic-divided first difference, and the second-order outer-pair smoothed Bézout interior sum.

---

## 5. The Ten Structural Traps (Obstructions & Design Laws)

1. **Trap 1 — The Same-Node Dirichlet-Convolution / Floor-Sum Tautology Trap ($\mathbf{1} * \mu * f = f$):**
   Expanding $\sum_{k=1}^M s_{N,c}(k)^2 = \sum_{L=1}^M F_{N,c}(L)\lfloor M / L \rfloor$ via
   $F_{N,c} = \mu * (s_{N,c}^2)$ and $\lfloor M / L \rfloor = \sum_{k \le M, L \mid k} 1$ is the
   purely multiplicative tautology $\mathbf{1} * \mu * (s_{N,c}^2) = s_{N,c}^2$, which holds in any
   Beurling system and reduces to $0 = 0$ when inverted on $[N + 1, M]$.
   - *Rule:* Always couple Same-Node squares $s_{N,c}(k)^2$ to Successor-Node Bézout products
     $s_{N,c}(k)s_{N,c}(k + 1)$ or additive differences $\nabla_+ s_{N,c}(k)$ across $k \mapsto k + 1$.
2. **Trap 2 — The 1D Logarithmic-Line Sampling & Totient Degeneracy Trap (Wall 11):**
   Treating $\{\log n\}$ as points on $\mathbb{R}_u$ or relying on the Same-Node Selberg weight
   $\varphi(e)$ alone is blind to Wall 11 ($\varphi(4) = \varphi(6) = 2$), whereas the mixed
   multiplicative difference $\Delta_{2, 3}^\times \log = 0$ vs. $\Delta_2^\times \log(2) = \log 2$,
   all four non-Selberg BVI modal weights ($\mu$, $\varphi - \mu$, $\varphi - \mu^2/\varphi$, and
   $J_2$), the non-Markovian revival defect (`nonMarkovianLagDefect 4 1 1 = -1` vs. `-3/4` at $6$),
   and the pronic discrepancy von Mangoldt weight ($-\Lambda(4) = -\log 2$ vs. $-\Lambda(6) = 0$)
   strictly separate $4 = 2^2$ from $6 = 2 \cdot 3$.
3. **Trap 3 — The Pure Monoid / Beurling Semigroup Trap (Wall 9):**
   Any identity proved solely from Dirichlet convolution, Euler products, or same-node divisibility
   $d \mid k$ holds in Beurling generalized number systems with off-line zeros.
   - *Rule:* Every mechanism must explicitly invoke $\gcd(k, k + 1) = 1$, pronic factor injectivity
     $d_1 d_2 \mid k(k + 1)$, or the Euclidean floor-step law $\lfloor (k + 1)/d \rfloor - \lfloor k/d \rfloor = \mathbf{1}_{d \mid (k+1)}$.
4. **Trap 4 — The External-Family Dispersion Trap (Wall 7):**
   Relying on character orthogonality $\sum_{\chi \pmod q}$ or spectral $t$-integrals collapses at
   the degenerate point of a single $L$-function ($Q = 1, q = 1, t = 0$).
   - *Rule:* Use internal scale-quotient correspondence $k = q_d d + r_d$ and pronic Bézout incidence
     at modulus $1$ and shift $0$.
5. **Trap 5 — The Uncentered $d = 1$ Boundary Leakage Trap:**
   In the uncentered product $s_{N,c}(k)s_{N,c}(k + 1)$, the trivial factor $d_1 = 1$ or $d_2 = 1$
   allows prime powers $(p^a, 1)$ and $(1, p^a)$ to leak into the successor product.
   - *Rule:* Split $s_{N,c}(k) = c(1) + \widetilde{s}_{N,c}(k)$ (`sieveSeq_eq_c_one_add_centeredSieveSeq`)
     so that $\widetilde{s}_{N,c}(k)\widetilde{s}_{N,c}(k + 1)$ is supported 100% on multi-prime
     composites $d_1 d_2$ with $d_1, d_2 \ge 2$ and $\Lambda(d_1 d_2) = 0$.
6. **Trap 6 — The Unsigned Remainder / Triangle-Inequality Sieve Trap (Wall 10):**
   Bounding trans-horizon LCM fibres $|F_{N,\mu}(L)|$ by $\tau_3(L)$ ignores both the exact
   sub-horizon collapse $F_{N,\mu}(L) = \mu(L)$ ($L \le N$) and the first-octave parity collapse
   $F_{N,\mu}(L) = \mu(L) + \mu(L)^2 \in \{0, 2\}$ ($N < L \le 2N$).
7. **Trap 7 — The Diagonal-Square / Harmonic-Divergence Martingale Trap:**
   In the naive square-increment identity $W_{N,c}(n + 1)^2 - W_{N,c}(n)^2 = (\Delta W_{N,c}(n))^2 + 2\Delta W_{N,c}(n)W_{N,c}(n)$,
   treating the diagonal square $(\Delta W_{N,c}(n))^2 = (s_{N,c}(n + 1) - Y(1))^2$ and the
   predictable martingale term separately creates a $1/(2\varepsilon)$ prime-sum divergence as
   $\varepsilon \to 0^+$ that must be cancelled against an equal and opposite divergence in the
   active sawtooth component.
   - *Rule:* Always absorb the active pre-jump component $A_{N,c}(n + 1, n)$ or the full Bézout
     active pair $A_{N,c}(n, n) + A_{N,c}(n + 1, n)$ into the diagonal square first, eliminating the
     diagonal square identically.
8. **Trap 8 — The Single-Step Active Boundary / Centering-Drift Trap:**
   Extracting only the pre-jump active divisor sum $d \mid (n + 1)$ leaves behind the predecessor
   post-jump peak $d \mid n$ inside the inactive sum, together with a linear dependence on the
   centering density $Y_{N,c}(1)$.
   - *Rule:* Pair the pre-jump trough at $n + 1$ with the post-jump peak at $n$ via
     `weightedCenteredSawtoothSum_eq_bezout_active_pair_add_interior`, which cancels centering drift
     and has zero boundary term at $n = 1$ (`activeCenteredSawtoothSum_one`).
9. **Trap 9 — The One-Step Markovian / Linear Successor Closure Trap:**
   Attempting to approximate $s_{N,c}(k + 1)$ by a single linear divisor sieve $s_{N,b}(k)$ at lag $1$
   loses at least $3/4$ of all Selberg variance above parity (`successorPhaseLoss_bounds`), erases
   all non-squarefree modes (`sieveModeWeight_iterated_successor_erased_iff`), and fails the Markov
   semigroup law ($\mathcal{C}_2 \ne \mathcal{C}_1^2$, `nonMarkovianLagDefect_first_octave_table`).
   - *Rule:* Use true-lag compression schedules covering all visibility clocks $q/\operatorname{rad}(q)$
     (`ArithmeticLagSchedulesAndSharpRecoveryHorizon`, `NonMarkovianLagOperatorAlgebraAndPrimePowerRevival`).
10. **Trap 10 — The Unrenormalized Prefix Defect / Sub-Horizon Linear Drift Trap:**
    The raw combined prefix defect $\mathcal{D}_{N,M}(c) = \mathcal{R}_{\mathrm{Sel}}(M, N, c) - \mathcal{R}_{\mathrm{Bez}}(M, N, c)$
    grows linearly like $M \cdot \operatorname{sieveSuccessorReserve}(N, c)$ across sub-horizon
    prefixes $M \le N$ (`PrimeTailCalibrationAndMobiusDefect`).
    - *Rule:* Always work with the renormalized prefix defect $\mathcal{D}^{\mathrm{ren}}_{N,M}(c) = \mathcal{D}_{N,M}(c) - M \cdot \operatorname{sieveSuccessorReserve}(N, c)$
      (`RenormalizedMobiusDefectAndFirstOctaveCancellation`, `PowerDampedRenormalizedDefectAndPronicCeiling`).

---

## 6. How to Navigate & Extend the Codebase (Complete 58-Module Architecture)

Use the repository search tool to locate declarations and proof patterns:
```bash
scripts/formal_tools.py research "bezoutSuccessorPairSet pronicSeq"
scripts/formal_tools.py research "sieveLagMultiplier lagVisibilityClock"
scripts/formal_tools.py research "hasSum_sievePrefixDiscrepancy_div_pronicSeq"
```

### Complete Module Inventory (`formal/GaloisForLFunctions/BezoutValuationIncidence/`)

#### I. Foundational Bézout–Valuation Incidence, Trans-Horizon Octaves, & Simultaneous Diagonalization
1. [`PronicBezoutSplitAndPrimePowerIndecomposability.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/PronicBezoutSplitAndPrimePowerIndecomposability.lean) —
   Mixed multiplicative differences vs. 1D prime-axis gradients (`log 4` vs. `log 6`), pronic factor
   recovery and divisor bijection, prime-power indecomposability under coprime factorization, total
   annihilation of prime powers on `centeredBezoutSuccessorPairSet`, and universal vanishing
   $\Lambda(k(k + 1)) = 0$ ($k \ge 2$).
2. [`QuotientDualOctaveReciprocityAndValuationSwitching.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/QuotientDualOctaveReciprocityAndValuationSwitching.lean) —
   High-divisor complement formula, first-octave reciprocity ($s_{N,\mu}(k) = -\mu(k)$,
   $F_{N,\mu}(L) = \mu(L) + \mu(L)^2 \ge 0$, prime annihilation), second-octave $2$-adic valuation
   switching ($s_{N,\mu}(2u) = 0$ vs. $s_{N,\mu}(4u) = \mu(u)$ for odd $u$), and logarithmic von
   Mangoldt first-octave splitting.
3. [`BezoutSuccessorQuadraticFormAndDirichletEnergySplit.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/BezoutSuccessorQuadraticFormAndDirichletEnergySplit.lean) —
   Discrete Dirichlet energy polarization coupling Same-Node squares to Successor-Node Bézout
   correlations, CRT separation law, super-horizon uniqueness $\mathcal{I}_{\mathrm{Bez}}(M; d_1, d_2) \le 1$
   ($M \le d_1 d_2$), and super-horizon reach up to $d(d + 1) \le M(M + 1)$ ($\theta = 2$).
4. [`BezoutSelbergDiagonalCoercivityAndHalfDecorrelation.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/BezoutSelbergDiagonalCoercivityAndHalfDecorrelation.lean) —
   Simultaneous Selberg–Möbius diagonalization $\mathcal{Q}_{\mathrm{Bez}}(N, c) = \sum_{e=1}^N \mu(e) Y_{N,c}(e)^2$,
   universal $e = 1$ pole cancellation, prime weight recovery $\varphi(p) - \mu(p) = p$, Wall 11
   spectral separation $\varphi(4) - \mu(4) = 2 \ne 1 = \varphi(6) - \mu(6)$, and the universal
   $1/2$-decorrelation & coercivity law on $\ker P$ (sharp at $e = 6 = 2 \cdot 3$).
5. [`ChineseRemainderBezoutPeriodicityAndSawtoothDefect.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/ChineseRemainderBezoutPeriodicityAndSawtoothDefect.lean) —
   Exact Chinese Remainder bijection on contiguous periods $[A + 1, A + d_1 d_2]$, one-per-period
   recurrence and Euclidean division formula for `bezoutIncidenceCount`, universal unit-interval
   bound on `bezoutSawtoothDefect`, and finite-prefix Dirichlet energy decomposition.
6. [`FermiCellJumpReciprocityAndPronicTailBridge.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/FermiCellJumpReciprocityAndPronicTailBridge.lean) —
   Dyadic prefix decomposition and inter-cell jump law for `fermiCellResponse`, pronic successor
   parity orthogonalization of consecutive jumps, exact first-octave evaluation of
   `dilatedMobiusFermiCombinator 1 N`, and pronic-weighted cell $L^2$ tail energy.
7. [`PowerSavingIncrementCriterion.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/PowerSavingIncrementCriterion.lean) —
   Unconditional equivalence between uniform strict-half-power bounds on first-octave Möbius
   Fermi–Nyman cell responses (`mobiusFirstOctavePowerSaving_iff_riemannHypothesis`), Mertens bounds,
   and `RiemannHypothesis`.
8. [`DilatedCellScalingAndSecondOctaveFermiJumpBridge.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/DilatedCellScalingAndSecondOctaveFermiJumpBridge.lean) —
   Dilated cell-matrix scaling `fermiCellMatrix (k * d) n = fermiCellMatrix d (n / k)`, universal
   cell evaluation of `dilatedMobiusFermiCombinator k N`, the Four-Way $2$-Adic Jump Table in the
   second trans-horizon octave ($v_2(m) = 0, 1, 2, \ge 3$), and `fermiCellResponse_moebiusReal_first_and_second_octave`.
9. [`EndpointHaarCellDecompositionAndWitnessPronicTransfer.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/EndpointHaarCellDecompositionAndWitnessPronicTransfer.lean) —
   Cellular evaluation and pronic cell energy of `pmPowerDampedEndpointHaarPrefix` and
   `pmPowerDampedRepairedHaarPrefix`, dyadic resolvent recursion, and exact first-tail-cell Möbius
   evaluation `singleCellFermiCombinator 1 (2 * M) t = -μ(2M + 1)`.
10. [`AllOctaveFermiJumpReciprocityAndDyadicSiblingPolarization.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/AllOctaveFermiJumpReciprocityAndDyadicSiblingPolarization.lean) —
    Universal all-octave dyadic sibling step `fermiCellResponse N c (2m + 1) - fermiCellResponse N c (2m) = -sieveSeq N c (2m + 1)`,
    dyadic sibling polarization `two_mul_add_sq_fermiCellResponse_siblings`, and telescoping dyadic
    wavelet resolvent reconstruction `pmPowerDampedCenteredDivisorPrefix_eq_neg_sum_dyadicPrefixWavelet`.

#### II. Spectral Extremal Theory, Five-Form Polytope Geometry, & Non-Markovian Lag Operator Algebra
11. [`SuccessorEnergyRigidityAndParityStability.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/SuccessorEnergyRigidityAndParityStability.lean) —
    Descending inversion of the truncated multiples transform (`selbergMultiplesCoord_tail_zero_iff`),
    kernel rigidity (`selberg_eq_bezout_iff_weight_tail_zero`), universal two-sided successor
    covariance bounds (`successor_covariance_bounds`), and parity-mode stability
    (`variance_above_parity_le_anticorrelation_defect`).
12. [`ExactSuccessorMomentRegionAndUniversalInequalities.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/ExactSuccessorMomentRegionAndUniversalInequalities.lean) —
    Exact three-mode Ramanujan realization on divisors $\{1, 2, 6\}$ (`successorThreeModeWeight_moments`),
    necessary and sufficient joint moment realizability (`exists_sieve_weight_with_moments_iff`),
    and complete classification of universal quadratic inequalities (`universal_successor_quadratic_inequality_iff`).
13. [`SixModeStabilityAndSharpQuarterDecorrelation.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/SixModeStabilityAndSharpQuarterDecorrelation.lean) —
    Quantitative $e = 6$ mode stability and the sharp $1/4$-decorrelation bound once $Y_{N,c}(6) = 0$.
14. [`GcdOrbitProjectionAndExactTranslationPeriods.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/GcdOrbitProjectionAndExactTranslationPeriods.lean) —
    Gcd-orbit projection `sieveGcdProjection N h c` onto Selberg modes $q \mid h$, exact translation
    invariance at lag $h$, and Pythagorean variance decomposition.
15. [`DiscretePrimitiveEnergyAndJordanComparison.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/DiscretePrimitiveEnergyAndJordanComparison.lean) —
    Exact diagonalization of the centered sawtooth primitive energy `sievePrimitiveEnergy N c` by the
    second Jordan totient $\frac{1}{12} J_2(q) Y_{N,c}(q)^2$ and sharp lower bound
    $\frac{1}{4}\operatorname{sieveVariance}(N, c) \le \operatorname{sievePrimitiveEnergy}(N, c)$.
16. [`SharpPrimitiveEnergySuccessorFrontier.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/SharpPrimitiveEnergySuccessorFrontier.lean) —
    Exact 3D convex hull of normalized `(covariance, reserve, primitive energy)` at modes $q \ge 2$:
    the four arithmetic modes $\{2, 3, 4, 6\}$ form the extreme rays of the facet polytope
    (`primitiveEnergy_successor_polytope`), with universal lower frontier
    $4 E + C \ge V$ attained strictly on $\operatorname{span}\{e_2, e_3, e_6\}$.
17. [`CoprimalitySuccessorPredictorAndSquarefreeInformation.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/CoprimalitySuccessorPredictorAndSquarefreeInformation.lean) —
    Explicit divisor-level coprimality predictor `sieveSuccessorPredictor N c` with Selberg multiplier
    $\mu(q)/\varphi(q)$, retaining precisely the squarefree Selberg coordinates (`sieveSuccessorPredictor_eq_iff`).
18. [`OptimalSuccessorPredictionAndExactPhaseLoss.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/OptimalSuccessorPredictionAndExactPhaseLoss.lean) —
    Exact Pythagorean optimality `successorPredictionError_pythagoras` of `sieveSuccessorPredictor N c`
    for predicting $s_{N,c}(k + 1)$ from $s_{N,b}(k)$, with minimum error `successorPhaseLoss N c`.
19. [`SharpSuccessorPhaseLossAndClosureClassification.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/SharpSuccessorPhaseLossAndClosureClassification.lean) —
    Sharp $[3/4, 1]$ phase-loss sandwich `successorPhaseLoss_bounds` above parity ($q \ge 3$),
    characterization of lower equality on $\{3, 6\}$ (`successorPhaseLoss_lower_eq_iff`), and exact
    successor closure iff $c(d) = 0$ for all $d \in [3, N]$ (`sieve_successor_representable_iff`).
20. [`IteratedSuccessorPredictionAndReservePhaseLossSplit.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/IteratedSuccessorPredictionAndReservePhaseLossSplit.lean) —
    Variance–phase-loss conservation (`sieveVariance_successorPredictor_add_phaseLoss`), geometric
    $4^{-m}$ contraction of iterated prediction above parity, and splitting of the $\{3, 6\}$
    phase-loss degeneracy via `sieveSuccessorReserveAboveParity`.
21. [`JordanUpperBoundAndGcdOrbitPrimitiveEnergy.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/JordanUpperBoundAndGcdOrbitPrimitiveEnergy.lean) —
    Sharp multiplicative upper bound $4 J_2(n) \le 3 n^2 \varphi(n)$ ($n \ge 2$), simultaneous
    diagonalization under `sieveGcdProjection N h c`, and the cutoff-independent stride bound
    $16\,\operatorname{sievePrimitiveEnergy}(N, \Gamma_h c) \le h^2 \operatorname{sieveVariance}(N, c)$.
22. [`DedekindPsiJordanTotientAndFiveFormSpectralSynthesis.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/DedekindPsiJordanTotientAndFiveFormSpectralSynthesis.lean) —
    Dedekind's psi ratio $\psi(n) = J_2(n)/\varphi(n)$, prime identities $\psi(p) = \varphi(p) - 2\mu(p)$
    and $J_2(p) = (\varphi(p) - \mu(p))^2 - 1$, sharp prime-attained bound $(q + 1)\varphi(q) \le J_2(q)$
    ($q \ge 2$), Wall 11 five-weight separation (`wall11_five_modal_weights_separation`), and the
    master five-form spectral synthesis (`bezoutValuationIncidence_master_five_form_synthesis`).
23. [`RamanujanLagCoefficientAndTotientQuotient.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/RamanujanLagCoefficientAndTotientQuotient.lean) —
    Möbius inversion of the CRT compatibility kernel at lag $h$ (`ramanujanLagCoefficient q h`) and
    its exact evaluation `sieveLagMultiplier_eq_moebius_totient_quotient` as
    $\mu(q/\gcd(q, h)) / \varphi(q/\gcd(q, h))$.
24. [`ValuationVisibilityClockAndRamanujanSupport.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/ValuationVisibilityClockAndRamanujanSupport.lean) —
    The valuation visibility clock `lagVisibilityClock q = q / rad(q)` with prime valuations
    $v_p(q) - 1$ (`lagVisibilityClock_factorization`), exact non-vanishing characterization
    `sieveLagMultiplier_ne_zero_iff` ($\iff q \ne 0 \wedge \operatorname{lagVisibilityClock}(q) \mid h$),
    and prime-power clock evaluation `lagVisibilityClock_prime_power` ($\operatorname{lagVisibilityClock}(p^{a+1}) = p^a$).
25. [`TrueTranslationPredictionAndExactCompression.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/TrueTranslationPredictionAndExactCompression.lean) —
    Exact Ramanujan diagonalization of literal lag-$h$ pairings (`sieveLagPair_eq_ramanujan_diagonal`),
    the optimal lag-$h$ predictor `sieveTranslationPredictor N h c`, and Pythagorean error
    minimization (`translationPredictionError_pythagoras`).
26. [`ArithmeticLagSchedulesAndSharpRecoveryHorizon.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/ArithmeticLagSchedulesAndSharpRecoveryHorizon.lean) —
    Complete classification of finite lag schedules $H \subset \mathbb{N}$ that recover all active
    divisor weights (`sieveLagScheduleRecovers_iff`), sharp consecutive recovery horizon
    `sieveLagRecoveryHorizon N = sup_{q ≤ N} lagVisibilityClock q`, single-lag recovery modulus
    `sieveLagRecoveryModulus N = lcm_{q ≤ N} lagVisibilityClock q`, and contrast between one-step
    iterated erasure and true-shift recovery.
27. [`SelbergHilbertCoordinateEquivalence.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/SelbergHilbertCoordinateEquivalence.lean) —
    Native finite-dimensional Hilbert space `SieveCoefficientSpace N`, the explicit isometric
    isomorphism `weightedSelbergIsometry N` onto `EuclideanSpace ℝ (SieveActiveIndex N)`, and exact
    intertwining `weightedSelbergIsometry_translation` of `nativeSieveTranslationPredictor N h`.
28. [`WittSelbergReceiverCoordinates.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/WittSelbergReceiverCoordinates.lean) —
    Transport of Deninger Big-Witt ghost coordinates into `SieveCoefficientSpace N` via
    `weightedSelbergIsometry N` (`wittSieveReceiver`), exact Frobenius-2 and arbitrary Verschiebung
    coordinate formulas, and native lag compression (`wittSieveReceiver_lag_prediction`).
29. [`NonMarkovianLagOperatorAlgebraAndPrimePowerRevival.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/NonMarkovianLagOperatorAlgebraAndPrimePowerRevival.lean) —
    Exact three-regime prime-power formula `sieveLagMultiplier_prime_pow_trichotomy`, coprime
    multiplicativity `sieveLagMultiplier_mul_of_coprime` and `ramanujanLagCoefficient_mul_of_coprime`,
    the Non-Markovian Prime-Power Revival Theorem `nonMarkovianLagDefect_prime_pow_revival` and
    `nonMarkovianLagDefect_prime_pow_one_pred`, first-octave semigroup defect table
    `nonMarkovianLagDefect_first_octave_table`, and self-adjointness, commutativity, and Hilbert-space
    defect norm `norm_nativeNonMarkovianDefect_sq` on `SieveCoefficientSpace N`.

#### III. Finite-Prefix Discrepancy Duality, Unimodular Prefix Lattices, & Short-Horizon Pronic Calculus
30. [`ExactFinitePrefixDiscrepancyDualityAndReturnTimes.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/ExactFinitePrefixDiscrepancyDualityAndReturnTimes.lean) —
    Exact dual representation `sievePrefixDiscrepancy_eq_ramanujan_diagonal` in terms of
    `pmRamanujanPrimitive e M`, sharp Cauchy–Schwarz inequality
    `(sievePrefixDiscrepancy N M c)² ≤ sieveVariance N c * sievePrefixDualEnergy N M` with explicit
    attaining weight `sievePrefixExtremizer N M`, and common return-time characterization
    `sievePrefixDualEnergy_eq_zero_iff` ($\iff \forall d \in [1, N],\, d \mid M$).
31. [`SharpInitialPrefixObservabilityAndExactGramDeterminants.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/SharpInitialPrefixObservabilityAndExactGramDeterminants.lean) —
    Exact initial-prefix kernel characterization `sievePrefix_initial_kernel_iff`, sharp $N - 1$
    observability horizon `sievePrefix_initial_zero_iff_variance_zero`, explicit Möbius–harmonic
    interpolation of arbitrary initial prefix data, and exact determinant formulas $(-1)^n / (n + 1)$,
    $(-1)^n n!$, and $(n!)^2 / \prod_{e=2}^{n+1} \varphi(e)$ for the floor, Ramanujan primitive, and
    variance-dual Gram matrices.
32. [`IntegralPrefixLatticeAndPrimePowerObstructions.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/IntegralPrefixLatticeAndPrimePowerObstructions.lean) —
    Explicit unimodular Smith Normal Form `sievePrefixScaledIntegerObservationMatrix_smith` reducing
    the scaled integer prefix observation matrix to $\operatorname{diag}(1, 2, \dots, n)$, exact
    invariant-factor product formulas, mod-$p^a$ kernel cardinality $p^{\sum_{r=1}^a \lfloor n / p^r \rfloor}$,
    and prime-power Euclidean norm lower bounds for integer prefix-invisible weights.
33. [`ReturnWindowTwoMomentKernelsAndSharpZeroBlocks.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/ReturnWindowTwoMomentKernelsAndSharpZeroBlocks.lean) —
    Return-window reflection symmetry $R_e(L - 1 - r) = R_e(r) - \varphi(e)$, oddness of the centered
    discrepancy around $L - 1/2$, the sharp $2N - 3$ contiguous zero-block observability theorem
    (with $2N - 4$ counterexamples), and exact two-moment kernel classification.
34. [`PrimeTailCalibrationAndMobiusDefect.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/PrimeTailCalibrationAndMobiusDefect.lean) —
    Prime-tail calibration on $(N/2, N]$, exact formula for the unrenormalized combined prefix
    defect, and proof of its linear sub-horizon drift $M \cdot \operatorname{sieveSuccessorReserve}(N, c)$.
35. [`RenormalizedMobiusDefectAndFirstOctaveCancellation.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/RenormalizedMobiusDefectAndFirstOctaveCancellation.lean) —
    Universal renormalized prefix defect `sieveRenormalizedPrefixDefect N M c = ∑_{k=1}^M s_{N,c}(k)(s_{N,c}(k+1) - s_{N,c}(k))`,
    Dirichlet polarization `two_mul_sieveRenormalizedPrefixDefect_eq_neg_dirichlet_add_boundary`, and
    exact first-octave law and squarefree-count bounds for `moebiusCombinedPrefixDefect`.
36. [`PowerDampedRenormalizedDefectAndPronicCeiling.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/PowerDampedRenormalizedDefectAndPronicCeiling.lean) —
    Universal pronic ceiling `0 ≤ pmPowerDampedDivisorCoeff ε (pronicSeq k) ≤ 1 - 2^{-ε}`, exact
    sub-horizon pronic formula, and unconditional non-positivity
    `sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_nonpos`.
37. [`ShortHorizonPronicDiscrepancyAndVonMangoldtDuality.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/ShortHorizonPronicDiscrepancyAndVonMangoldtDuality.lean) —
    The Pronic-Weighted Discrepancy Von Mangoldt Duality Theorem `hasSum_sievePrefixDiscrepancy_div_pronicSeq`
    and `tsum_sievePrefixDiscrepancy_mode_probe_div_pronicSeq`, composite non-prime-power cancellation
    `tsum_sievePrefixDiscrepancy_mode_probe_eq_zero_of_not_isPrimePow`, period-free uniform dual-energy
    ceiling `sievePrefixDualEnergy_le_periodFreeDualCeiling`, short-horizon cumulative and
    pronic-weighted $L^2$ discrepancy bounds (`sum_Icc_sievePrefixDiscrepancy_sq_le`,
    `sum_Icc_sievePrefixDiscrepancy_sq_div_pronicSeq_le`), non-periodic pronic Gram quadratic form
    `hasSum_sievePrefixDiscrepancy_sq_div_pronicSeq`, two-mode prime-dilation decomposition
    `pmRamanujanPrimitiveGram_two_mode_dilation_identity`, and asymptotic negative self-energy limit
    `tendsto_pmRamanujanPrimitiveGram_prime_mul_not_isPrimePow`.

#### IV. Autonomous GCD–LCM Valuation Algebra, Primorial Bézout Hierarchy, & Sawtooth Martingale Calculus
38. [`PowerDampedPronicMultiplicativityAndRoutePMBridge.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/PowerDampedPronicMultiplicativityAndRoutePMBridge.lean) —
    Identification of `pmPowerDampedDivisorCoeff ε` with `sieveSeq N (pmPowerDampedRealWeight ε)`,
    Pronic Bézout Multiplicativity `pmPowerDampedDivisorCoeff ε k * pmPowerDampedDivisorCoeff ε (k + 1) = pmPowerDampedDivisorCoeff ε (pronicSeq k)`,
    and Pronic Abel Summation for `pmPowerDampedDivisorDiscreteEnergy ε T`.
39. [`SawtoothBezoutSuccessorGradientAndRouteFZZPBridge.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/SawtoothBezoutSuccessorGradientAndRouteFZZPBridge.lean) —
    Additive successor step law `centeredDiscreteSawtooth d (k + 1) - centeredDiscreteSawtooth d k = 1 / d - 1_{d ∣ (k + 1)}`,
    sieve gradient law `weightedCenteredSawtoothSum N c (k + 1) - weightedCenteredSawtoothSum N c k = sieveSeq N c (k + 1) - selbergMultiplesCoord N c 1`,
    and Bézout successor phase-locking (`centeredDiscreteSawtooth_bezoutSuccessorPair_extremal`).
40. [`PredictableMartingaleDecompositionAndCovarianceCancellationBridge.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/PredictableMartingaleDecompositionAndCovarianceCancellationBridge.lean) —
    Pointwise and telescoping square-increment martingale identities, predictable martingale
    identification `pmPowerDampedDivisorCovarianceOffDiagonal ε T = 2 * pmPredictableMartingaleSum ε T`,
    and logarithmic asymptotic drift `pmPredictableMartingaleSum ε N / log N → -pmPowerDampedDivisorVariance ε / 2`.
41. [`RadicalInvariancePrimePowerAbsorptionAndSubHorizonFermiEvaluation.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/RadicalInvariancePrimePowerAbsorptionAndSubHorizonFermiEvaluation.lean) —
    Radical invariance, power invariance, divisor-multiplication absorption, and sub-horizon
    odd-to-even Fermi–Nyman jump dichotomy for `pmPowerDampedDivisorCoeff ε`.
42. [`ModularGcdLcmMultiplicativityAndCenteredSuccessorCovariance.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/ModularGcdLcmMultiplicativityAndCenteredSuccessorCovariance.lean) —
    Modular GCD–LCM multiplicativity `pmPowerDampedDivisorCoeff ε j * pmPowerDampedDivisorCoeff ε k = pmPowerDampedDivisorCoeff ε (Nat.lcm j k) * pmPowerDampedDivisorCoeff ε (Nat.gcd j k)`
    and successor centered covariance linearization `pmPowerDampedCenteredDivisorCoeff_mul_succ_eq_pronicSeq`.
43. [`SawtoothMidpointAnnihilationAndActiveDivisorSquareInvariance.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/SawtoothMidpointAnnihilationAndActiveDivisorSquareInvariance.lean) —
    Active-divisor sign flip `centeredDiscreteSawtooth d (n + 1) = -centeredDiscreteSawtooth d n`
    for $d \mid (n + 1)$, square invariance, and active-square cancellation in Pronic Abel sums.
44. [`ActiveSawtoothClosedFormAndShiftedExponentTotientBridge.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/ActiveSawtoothClosedFormAndShiftedExponentTotientBridge.lean) —
    Closed form `activeCenteredSawtoothSum N c (n + 1) n = -(1 / 2) * (sieveSeq N c (n + 1) - sieveSeq N (c / d) (n + 1))`
    and shifted-exponent totient identity `pmPowerDampedRealWeight ε d / d = pmPowerDampedRealWeight (1 + ε) d`.
45. [`ActiveDeletedMartingaleAndShiftedEulerConvergence.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/ActiveDeletedMartingaleAndShiftedEulerConvergence.lean) —
    Active-Deleted Martingale Identity `weightedCenteredSawtoothSum_succ_sq_sub_sq_eq_shifted_diagonal_add_inactive_martingale`,
    one-$p$-th suppression of the shifted-exponent local Euler factor gap `pmShiftedExponentFactor_gap_eq_div_p`,
    and uniform $O(1/p^2)$ convergence of `pmShiftedExponentPrimeDeficit`.
46. [`ShiftedExponentAsymptoticDensityAndActiveMartingaleRate.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/ShiftedExponentAsymptoticDensityAndActiveMartingaleRate.lean) —
    Euler product and Cesàro mean convergence of $\tau_\varepsilon(n)\tau_{1+\varepsilon}(n)$ to
    `pmShiftedExponentSecondDensity ε`, unit small-damping rate, and $+1/2$ variance equipartition of
    `pmActiveSawtoothMartingaleDensity`.
47. [`HorizonFreeActiveDeletedEnergyAndShiftedCovariance.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/HorizonFreeActiveDeletedEnergyAndShiftedCovariance.lean) —
    Horizon-free decomposition `pmPowerDampedDivisorDiscreteEnergy_eq_activeDeletedDiagonal_add_two_mul_inactive`,
    strict positivity of `pmShiftedExponentCovariance`, and asymptotic drift of
    `pmInactivePredictableMartingaleSum`.
48. [`ShiftedExponentSmallDampingCovarianceRateAndActiveDrift.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/ShiftedExponentSmallDampingCovarianceRateAndActiveDrift.lean) —
    Unconditional logarithmic drift `tendsto_pmActivePredictableMartingaleSum_div_log` and exact
    small-damping rate `tendsto_pmShiftedExponentCovariance_div_parameter`.
49. [`BezoutPronicInteriorSawtoothAndPredecessorPeakSplit.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/BezoutPronicInteriorSawtoothAndPredecessorPeakSplit.lean) —
    Three-way Bézout sawtooth partition `weightedCenteredSawtoothSum_eq_bezout_active_pair_add_interior`,
    forward-difference representation `bezout_active_pair_eq_neg_half_addDiff`, telescoping sum
    `sum_Icc_bezout_active_pair_eq_terminal`, and centering-drift cancellation
    `pmActiveSawtoothComponent_pre_add_post_martingale_eq`.
50. [`BezoutPronicTotientInteriorMartingaleSynthesis.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/BezoutPronicTotientInteriorMartingaleSynthesis.lean) —
    Diagonal-free Bézout pronic–totient–interior square-increment identity
    `pmPowerDampedCenteredDivisorPrefix_sq_succ_sub_sq_eq_pronic_add_shiftedAddDiff_add_interior` and
    two-step symmetric midpoint duality `pmBezoutInteriorPrefix_add_half_shiftedAddDiff_eq_two_step_midpoint`.
51. [`PostStepInactivePrefixAndSixDivisibilityPronicDefect.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/PostStepInactivePrefixAndSixDivisibilityPronicDefect.lean) —
    Post-step inactive prefix `pmPostStepInactivePrefix`, two-point Bézout smoothing
    `addDiff_pmPostStepInactivePrefix`, divisor-ordering antitonicity `pmPowerDampedDivisorCoeff_le_of_dvd`,
    and $6$-adic Bézout product ceilings.
52. [`PostStepInactiveEnergyAndPronicGradientConservation.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/PostStepInactiveEnergyAndPronicGradientConservation.lean) —
    General linear Pronic Abel summation `sum_div_pronicSeq_eq_compensated_abel`, pronic reciprocal
    telescoping `sum_one_div_pronicSeq_eq`, and pointwise/finite pronic–diagonal–gradient
    conservation laws (`sum_Icc_pronicSeq_add_addDiff_sq_eq`).
53. [`ActivePairMartingaleDissipationAndShiftedTotientReduction.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/ActivePairMartingaleDissipationAndShiftedTotientReduction.lean) —
    Compensated Abel dissipation identity `sum_neg_succ_mul_addDiff_compensated_eq`, purely
    dissipative sawtooth self-interaction, and compensated pronic–gradient decomposition of
    `pmPowerDampedDivisorCovarianceDiagonal`.
54. [`SummationByPartsActivePairAndUncenteredShiftedReduction.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/SummationByPartsActivePairAndUncenteredShiftedReduction.lean) —
    Compensated summation by parts `sum_succ_mul_addDiff_compensated_eq_pronic_sub`, sharp $1/8$
    active-sawtooth envelope `sum_centered_mul_pmActiveSawtoothComponent_div_pronicSeq_le_eighth`,
    and complete centering elimination `pmActive_add_pmPredecessorPeak_eq_sbp_uncentered`.
55. [`GeneralRadicalMultiplicativeAndGcdLcmValuationAlgebra.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/GeneralRadicalMultiplicativeAndGcdLcmValuationAlgebra.lean) —
    Autonomous class `IsGcdLcmModular F` and general radical prime-factor functional
    `radicalPrimeProd w`, with universal pronic–gradient conservation, divisor absorption,
    antitonicity, submultiplicativity, and primorial Bézout ceilings.
56. [`ThreeStepPrimorialBezoutAndEvenCubicCeiling.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/ThreeStepPrimorialBezoutAndEvenCubicCeiling.lean) —
    Three-step Bézout GCD laws ($\gcd(k, k + 2) = \gcd(k, 2)$, $\gcd(k(k + 2), k + 1) = 1$),
    $24$-divisibility of even-start triples, exact three-step factorization
    `radicalPrimeProd_three_step_mul_eq`, and sharp cubic $(1 - w(2))^2(1 - w(3))$ ceiling on
    even-start triples.
57. [`UniversalSawtoothInteriorMartingaleAndPostStepCalculus.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/UniversalSawtoothInteriorMartingaleAndPostStepCalculus.lean) —
    Universal all-horizon, arbitrary-weight Bézout interior martingale identity
    `weightedCenteredSawtoothSum_succ_sq_sub_sq_eq_bezout_interior`, boundary-free active-pair
    dissipation `sum_bezout_active_pair_martingale_compensated_eq`, and general post-step two-point
    smoothing `addDiff_postStepInactiveSawtoothSum`.
58. [`ThreeStepBezoutInteriorSawtoothAndSecondOrderSmoothing.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/ThreeStepBezoutInteriorSawtoothAndSecondOrderSmoothing.lean) —
    Second-order outer-pair smoothing `addDiff_bezoutInteriorSawtoothSum_eq_outer_pair_avg` and
    `addDiff_pmBezoutInteriorPrefix_eq_outer_pair_avg`, pure lag-1 pronic covariance reduction
    `sieveSeq_sub_mul_addDiff_bezoutInteriorSawtoothSum_eq_pronic_avg` and
    `mul_addDiff_pmBezoutInteriorPrefix_eq_pronic_avg`, and the three-step Bézout interior sawtooth
    partition `bezoutInteriorSawtoothSum_eq_threeStep_add_two_step_prejump`.

