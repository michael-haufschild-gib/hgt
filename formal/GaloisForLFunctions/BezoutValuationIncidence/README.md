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

---

## 3. How the Theory Works: The Six Core Mechanisms

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

---

## 4. The Six Structural Traps (Obstructions & Design Laws)

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
   multiplicative difference $\Delta_{2, 3}^\times \log = 0$ vs. $\Delta_2^\times \log(2) = \log 2$
   and the Bézout–Dirichlet eigenvalue $\varphi(4) - \mu(4) = 2 \ne 1 = \varphi(6) - \mu(6)$
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

---

## 5. How to Navigate & Extend the Codebase

Use the repository search tool to locate declarations and proof patterns:
```bash
scripts/formal_tools.py research "bezoutSuccessorPairSet pronicSeq"
scripts/formal_tools.py research "sieveSeq_moebiusReal_second_octave"
scripts/formal_tools.py research "bezoutCoprimeQuadraticForm"
```

### Architecture of `GaloisForLFunctions.BezoutValuationIncidence`
- [`PronicBezoutSplitAndPrimePowerIndecomposability.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/PronicBezoutSplitAndPrimePowerIndecomposability.lean) —
  **Pillar I:** Mixed multiplicative differences vs. 1D prime-axis gradients (`log 4` vs. `log 6`),
  pronic factor recovery and divisor bijection, prime-power indecomposability under coprime
  factorization, total annihilation of prime powers on `centeredBezoutSuccessorPairSet`, and
  universal vanishing $\Lambda(k(k + 1)) = 0$ ($k \ge 2$).
- [`QuotientDualOctaveReciprocityAndValuationSwitching.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/QuotientDualOctaveReciprocityAndValuationSwitching.lean) —
  **Pillar II:** High-divisor complement formula, first-octave reciprocity ($s_{N,\mu}(k) = -\mu(k)$,
  $F_{N,\mu}(L) = \mu(L) + \mu(L)^2 \ge 0$, prime annihilation), second-octave $2$-adic valuation
  switching ($s_{N,\mu}(2u) = 0$ vs. $s_{N,\mu}(4u) = \mu(u)$ for odd $u$), and logarithmic
  von Mangoldt first-octave splitting.
- [`BezoutSuccessorQuadraticFormAndDirichletEnergySplit.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/BezoutSuccessorQuadraticFormAndDirichletEnergySplit.lean) —
  **Pillar III:** Discrete Dirichlet energy polarization coupling Same-Node squares to Successor-Node
  Bézout correlations, CRT separation law, super-horizon uniqueness $\mathcal{I}_{\mathrm{Bez}}(M; d_1, d_2) \le 1$
  ($M \le d_1 d_2$), super-horizon reach up to $d(d + 1) \le M(M + 1)$ ($\theta = 2$), and the
  Master Four-Requirement Synthesis (`bezout_valuation_incidence_four_requirement_synthesis`).
- [`BezoutSelbergDiagonalCoercivityAndHalfDecorrelation.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/BezoutSelbergDiagonalCoercivityAndHalfDecorrelation.lean) —
  **Pillar IV:** Simultaneous Selberg–Möbius diagonalization $\mathcal{Q}_{\mathrm{Bez}}(N, c) = \sum_{e=1}^N \mu(e) Y_{N,c}(e)^2$,
  universal $e = 1$ pole cancellation, prime weight recovery $\varphi(p) - \mu(p) = p$, Wall 11
  spectral separation $\varphi(4) - \mu(4) = 2 \ne 1 = \varphi(6) - \mu(6)$, and the universal
  $1/2$-decorrelation & coercivity law on $\ker P$ (sharp at $e = 6 = 2 \cdot 3$).
- [`ChineseRemainderBezoutPeriodicityAndSawtoothDefect.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/ChineseRemainderBezoutPeriodicityAndSawtoothDefect.lean) —
  **Pillar V:** Exact Chinese Remainder bijection on contiguous periods $[A + 1, A + d_1 d_2]$,
  one-per-period recurrence and Euclidean division formula for `bezoutIncidenceCount`, universal
  unit-interval bound on `bezoutSawtoothDefect`, and the Master Finite-Prefix Dirichlet Energy
  Decomposition & $\ker P$ Coercivity Law.
- [`FermiCellJumpReciprocityAndPronicTailBridge.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/FermiCellJumpReciprocityAndPronicTailBridge.lean) —
  **Pillar VI:** Dyadic prefix decomposition and inter-cell jump law for `fermiCellResponse`,
  pronic successor parity orthogonalization of consecutive jumps, exact first-octave evaluation of
  `dilatedMobiusFermiCombinator 1 N`, and pronic-weighted cell $L^2$ tail energy.
- [`SuccessorEnergyRigidityAndParityStability.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/SuccessorEnergyRigidityAndParityStability.lean) —
  **Pillar VII:** Descending inversion of the truncated multiples transform (`selbergMultiplesCoord_tail_zero_iff`),
  kernel rigidity of the successor Dirichlet energy (`selberg_eq_bezout_iff_weight_tail_zero`),
  universal two-sided successor covariance and variance bounds (`successor_covariance_bounds`,
  `successor_energy_variance_bounds`), and quantitative parity-mode stability
  (`successor_anticorrelation_iff_weight_tail_zero`, `variance_above_parity_le_anticorrelation_defect`).
- [`ExactSuccessorMomentRegionAndUniversalInequalities.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/ExactSuccessorMomentRegionAndUniversalInequalities.lean) —
  **Pillar VIII:** Exact three-mode Ramanujan realization on divisors $\{1, 2, 6\}$ (`successorThreeModeWeight_moments`),
  necessary and sufficient joint moment realizability (`exists_sieve_weight_with_moments_iff`), and
  complete classification of all universal quadratic inequalities in sieve variance and successor
  covariance (`universal_successor_quadratic_inequality_iff`).
- [`SixModeStabilityAndSharpQuarterDecorrelation.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/SixModeStabilityAndSharpQuarterDecorrelation.lean) —
  Quantitative $e = 6$ mode stability and the sharp $1/4$-decorrelation bound once $Y_{N,c}(6) = 0$.
- [`ExactFinitePrefixDiscrepancyDualityAndReturnTimes.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/ExactFinitePrefixDiscrepancyDualityAndReturnTimes.lean) —
  Exact finite-prefix discrepancy duality (`sieveWindowEnergy_eq_divisorDiscrepancy`) and simultaneous
  return times at $M = \operatorname{lcm}(1, \dots, N)$.
- [`SharpInitialPrefixObservabilityAndExactGramDeterminants.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/SharpInitialPrefixObservabilityAndExactGramDeterminants.lean) —
  Triangular observability of initial prefixes $M = N$ and exact Gram determinants.
- [`IntegralPrefixLatticeAndPrimePowerObstructions.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/IntegralPrefixLatticeAndPrimePowerObstructions.lean) —
  Unimodular equivalence of the initial prefix lattice and prime-power lower bounds.
- [`ReturnWindowTwoMomentKernelsAndSharpZeroBlocks.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/ReturnWindowTwoMomentKernelsAndSharpZeroBlocks.lean) —
  Return-window two-moment kernels and sharp zero blocks.
- [`PrimeTailCalibrationAndMobiusDefect.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/PrimeTailCalibrationAndMobiusDefect.lean) —
  Sharp prime-tail calibration on $(N/2, N]$ and exact evaluation of the literal Möbius combined
  prefix defect `moebiusCombinedPrefixDefect`.
- [`DilatedCellScalingAndSecondOctaveFermiJumpBridge.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/DilatedCellScalingAndSecondOctaveFermiJumpBridge.lean) —
  **Pillar IX:** Dilated cell-matrix scaling `fermiCellMatrix (k * d) n = fermiCellMatrix d (n / k)`,
  universal cell evaluation of `dilatedMobiusFermiCombinator k N`, two-octave threshold + discrepancy
  decomposition of `dyadicResolventCellThreshold k N`, the Four-Way $2$-Adic Jump Table in the second
  trans-horizon octave ($v_2(m) = 0, 1, 2, \ge 3$), and the unified two-octave cumulative formula
  `fermiCellResponse_moebiusReal_first_and_second_octave`.
- [`PowerDampedPronicMultiplicativityAndRoutePMBridge.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/PowerDampedPronicMultiplicativityAndRoutePMBridge.lean) —
  **Pillar X:** Identification of `pmPowerDampedDivisorCoeff ε` with `sieveSeq N (pmPowerDampedRealWeight ε)`,
  scale-invariant unit response `sieveSeq N (pmPowerDampedRealWeight ε) p = 1` on first-octave primes,
  cellular evaluation of `pmPowerDampedFermiSource ε`, the Pronic Bézout Multiplicativity Law
  `pmPowerDampedDivisorCoeff ε k * pmPowerDampedDivisorCoeff ε (k + 1) = pmPowerDampedDivisorCoeff ε (pronicSeq k)`,
  Wall 11 separation between $4 = 2^2$ and $6 = 2 \cdot 3$, and Pronic Abel Summation for
  `pmPowerDampedDivisorDiscreteEnergy ε T` (`riemannHypothesis_of_pmPowerDamped_pronic_abel_budget`).
- [`EndpointHaarCellDecompositionAndWitnessPronicTransfer.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/EndpointHaarCellDecompositionAndWitnessPronicTransfer.lean) —
  **Pillar XI:** Cellular evaluation and pronic cell energy of `pmPowerDampedEndpointHaarPrefix` and
  `pmPowerDampedRepairedHaarPrefix`, global pointwise recursion
  `dyadicResolventCellThreshold k N t = dilatedMobiusFermiCombinator k N t + 2 * dyadicResolventCellThreshold (2 * k) N t`,
  global decomposition `singleCellFermiCombinator 1 N t = dilatedMobiusFermiCombinator 1 N t + dyadicResolventCellThreshold 2 N t`,
  and exact first-tail-cell Möbius evaluation `singleCellFermiCombinator 1 (2 * M) t = -μ(2M + 1)` on
  $I_{2M+1} = (1 / (2M + 2), 1 / (2M + 1)]$.
- [`SawtoothBezoutSuccessorGradientAndRouteFZZPBridge.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/SawtoothBezoutSuccessorGradientAndRouteFZZPBridge.lean) —
  **Pillar XII:** Exact additive successor step law `centeredDiscreteSawtooth d (k + 1) - centeredDiscreteSawtooth d k = 1 / d - 1_{d ∣ (k + 1)}`,
  the BVI sieve gradient law `weightedCenteredSawtoothSum N c (k + 1) - weightedCenteredSawtoothSum N c k = sieveSeq N c (k + 1) - selbergMultiplesCoord N c 1`,
  exact Dirichlet energy identity on $\ker P$, Bézout successor phase-locking and two-step sign-flip
  orthogonality (`centeredDiscreteSawtooth_bezoutSuccessorPair_extremal`), identification and pronic
  Abel variance decomposition of `pmPowerDampedRamanujanCenteredSawtoothPrefix`, and the master
  Route PM + Route FZZ-P + Route PW-B synthesis (`bezoutValuationIncidence_routePM_and_routeFZZP_master_synthesis`).
- [`PredictableMartingaleDecompositionAndCovarianceCancellationBridge.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/PredictableMartingaleDecompositionAndCovarianceCancellationBridge.lean) —
  **Pillar XIII:** Pointwise and telescoping square-increment martingale identities
  `A(n + 1)² - A(n)² = (addDiff A n)² + 2 * addDiff A n * A(n)`, general pronic-to-martingale and
  terminal-compensated decompositions, exact 1D predictable martingale identification of
  `pmPowerDampedDivisorCovarianceOffDiagonal ε T = 2 * pmPredictableMartingaleSum ε T`, logarithmic
  asymptotic drift `pmPredictableMartingaleSum ε N / log N → -pmPowerDampedDivisorVariance ε / 2`
  with small-damping rate `(-pmPowerDampedDivisorVariance ε / 2) / ε → -1 / 4`, and Route PM
  predictable/harmonic martingale cancellation criteria for `RiemannHypothesis`.
- [`AllOctaveFermiJumpReciprocityAndDyadicSiblingPolarization.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/AllOctaveFermiJumpReciprocityAndDyadicSiblingPolarization.lean) —
  **Pillar XIV:** Universal all-octave dyadic sibling step `fermiCellResponse N c (2m + 1) - fermiCellResponse N c (2m) = -sieveSeq N c (2m + 1)`,
  second-order odd-cell difference `2 * sieveSeq N c (m + 1) - addDiff (sieveSeq N c) (2m + 1)`,
  dyadic sibling polarization `two_mul_add_sq_fermiCellResponse_siblings`, exact sub-horizon
  centered-prefix wavelet formula `fermiCellResponse N (pmPowerDampedRealWeight ε) n = 2 A_ε(n / 2) - A_ε(n) - (n % 2) α_ε`
  with 100% density-drift cancellation on even cells `2m ≤ N`, and telescoping dyadic wavelet
  resolvent reconstruction `pmPowerDampedCenteredDivisorPrefix_eq_neg_sum_dyadicPrefixWavelet`.
- [`RadicalInvariancePrimePowerAbsorptionAndSubHorizonFermiEvaluation.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/RadicalInvariancePrimePowerAbsorptionAndSubHorizonFermiEvaluation.lean) —
  **Pillar XV:** Radical invariance `pmPowerDampedDivisorCoeff_eq_of_primeFactors_eq`, power/square
  invariance `pmPowerDampedDivisorCoeff_pow`, divisor-multiplication absorption
  `pmPowerDampedDivisorCoeff ε (d * m) = pmPowerDampedDivisorCoeff ε m` for `d ∣ m`, prime-multiplication
  and dyadic doubling dichotomy `pmPowerDampedDivisorCoeff_two_mul`, and the sub-horizon odd-to-even
  Fermi–Nyman jump dichotomy `(if 2 ∣ (m + 1) then 1 else 1 + 2^{-ε}) * τ_ε(m + 1)` with Wall 11
  jump contrast between `4 = 2²` and `6 = 2 · 3`.
- [`ModularGcdLcmMultiplicativityAndCenteredSuccessorCovariance.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/ModularGcdLcmMultiplicativityAndCenteredSuccessorCovariance.lean) —
  **Pillar XVI:** Universal modular GCD–LCM multiplicativity law
  `pmPowerDampedDivisorCoeff ε j * pmPowerDampedDivisorCoeff ε k = pmPowerDampedDivisorCoeff ε (Nat.lcm j k) * pmPowerDampedDivisorCoeff ε (Nat.gcd j k)`,
  scaled Bézout successor multiplicativity `pmPowerDampedDivisorCoeff_scaled_bezout_succ`, odd/even
  two-step shift autocorrelation laws, coprime and successor centered covariance linearizations
  `pmPowerDampedCenteredDivisorCoeff_mul_succ_eq_pronicSeq`, and the predecessor-isolated split of
  the Route PM predictable martingale increment `pmPredictableMartingaleIncrement_split_predecessor`.
- [`SawtoothMidpointAnnihilationAndActiveDivisorSquareInvariance.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/SawtoothMidpointAnnihilationAndActiveDivisorSquareInvariance.lean) —
  **Pillar XVII:** Pointwise active-divisor sign flip `centeredDiscreteSawtooth d (n + 1) = -centeredDiscreteSawtooth d n`
  for `d ∣ (n + 1)`, midpoint annihilation `centeredDiscreteSawtooth d n + centeredDiscreteSawtooth d (n + 1) = 0`,
  square invariance and 100% pointwise cancellation between the squared jump and predictable
  martingale product (`centeredDiscreteSawtooth_addDiff_sq_add_two_mul_eq_zero_of_dvd`), active-square
  cancellation in Pronic Abel sums (`weightedCenteredSawtoothSum_succ_sq_sub_sq_active_sq_cancelled`),
  and the zero-oscillation affine equivalence between Route PM's `pmPowerDampedCenteredDivisorPrefix`
  and `weightedCenteredSawtoothSum N (pmPowerDampedRealWeight ε)` (`pmPowerDampedCenteredDivisorPrefix_sub_weightedCenteredSawtoothSum_eq_affine`).
- [`ActiveSawtoothClosedFormAndShiftedExponentTotientBridge.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/ActiveSawtoothClosedFormAndShiftedExponentTotientBridge.lean) —
  **Pillar XVIII:** Exact closed-form evaluation of `activeCenteredSawtoothSum` (`activeCenteredSawtoothSum_at_pred_eq_half_sieveSeq_sub`)
  and `inactiveCenteredSawtoothSum` forward drift (`inactiveCenteredSawtoothSum_succ_sub_eq`), the
  shifted-exponent totient identity `pmPowerDampedRealWeight ε d / d = pmPowerDampedRealWeight (1 + ε) d`,
  sub-horizon closed forms `activeCenteredSawtoothSum N c_ε (n + 1) n = -(1 / 2) * (τ_ε(n + 1) - τ_{1+ε}(n + 1))`
  and `inactiveCenteredSawtoothSum N c_ε (n + 1) (n + 1) - inactiveCenteredSawtoothSum N c_ε (n + 1) n = τ_{1+ε}(n + 1) - selbergMultiplesCoord N c_ε 1`,
  and Euler totient ratio evaluations at exponent `1` (`pmPowerDampedDivisorCoeff_one_four_and_six`).
- [`ActiveDeletedMartingaleAndShiftedEulerConvergence.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/ActiveDeletedMartingaleAndShiftedEulerConvergence.lean) —
  **Pillar XIX (Active-Deleted Martingale & Shifted-Exponent Euler Convergence):** Active-martingale
  diagonal reduction `active_diagonal_reduction`, the Active-Deleted Martingale Identity
  `weightedCenteredSawtoothSum_succ_sq_sub_sq_eq_shifted_diagonal_add_inactive_martingale` and its
  Pronic Abel summation form `sum_weightedCenteredSawtoothSum_sq_div_pronicSeq_add_terminal_eq_active_deleted`,
  shifted-exponent totient dominance `pmPowerDampedDivisorCoeff_le_add_one` and divisor-sum
  representation `pmPowerDampedDivisorCoeff_mul_add_one`, one-`$p$-th` suppression of the
  shifted-exponent local Euler factor gap `pmShiftedExponentFactor_gap_eq_div_p`
  (`((p : ℝ)^{-ε})² (p - 1) / p³`), and uniform $O(1/p^2)$ convergence of
  `pmShiftedExponentPrimeDeficit` (`tendsto_tsum_pmShiftedExponentPrimeDeficit`).
- [`ShiftedExponentAsymptoticDensityAndActiveMartingaleRate.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/ShiftedExponentAsymptoticDensityAndActiveMartingaleRate.lean) —
  **Pillar XX (Shifted-Exponent Asymptotic Density & Active Martingale Equipartition):** Infinite
  Euler product `pmShiftedExponentSecondDensity_hasProd` and Cesàro mean convergence
  `tendsto_pmPowerDampedDivisorCoeff_mul_add_one_mean` for $\tau_\varepsilon(n)\,\tau_{1+\varepsilon}(n)$,
  universal density sandwich `pmPowerDampedSecondDensity ε ≤ pmShiftedExponentSecondDensity ε ≤ (pmPowerDampedDivisorDensity ε).re`,
  unit small-damping limit `tendsto_pmShiftedExponentDensityRatio` and unit small-damping rate
  `tendsto_pmShiftedExponentSecondDensity_div_parameter` ($\lim_{\varepsilon \to 0^+} \operatorname{pmShiftedExponentSecondDensity}\,\varepsilon / \varepsilon = 1$),
  and the exact $+1/2$ small-damping rate and variance equipartition of
  `pmActiveSawtoothMartingaleDensity` (`tendsto_pmActiveSawtoothMartingaleDensity_div_parameter`,
  `tendsto_pmActiveSawtoothMartingaleDensity_sub_divisorVariance_div_parameter`).
- [`HorizonFreeActiveDeletedEnergyAndShiftedCovariance.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/HorizonFreeActiveDeletedEnergyAndShiftedCovariance.lean) —
  **Pillar XXI (Horizon-Free Active-Deleted Energy & Shifted-Exponent Covariance):** Horizon-free
  active pre-jump component `pmActiveSawtoothComponent`, inactive residual prefix
  `pmInactiveResidualPrefix`, and active-deleted diagonal coefficient `pmActiveDeletedDiagonalCoeff`;
  exact horizon-free discrete energy decomposition
  `pmPowerDampedDivisorDiscreteEnergy_eq_activeDeletedDiagonal_add_two_mul_inactive`; strict
  positivity `pmShiftedExponentCovariance_pos` and harmonic asymptotics
  `tendsto_pmActiveDeletedCovarianceDiagonal_div_log` of `pmShiftedExponentCovariance`; asymptotic
  drift `tendsto_pmInactivePredictableMartingaleSum_div_log` of the inactive predictable martingale;
  and the Route PM cancellation criterion `riemannHypothesis_of_pmInactivePredictableMartingale_cancellation`.
- [`ShiftedExponentSmallDampingCovarianceRateAndActiveDrift.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/ShiftedExponentSmallDampingCovarianceRateAndActiveDrift.lean) —
  **Pillar XXII (Unconditional Active Martingale Drift & Small-Damping Covariance Rate):**
  Unconditional logarithmic drift `tendsto_pmActivePredictableMartingaleSum_div_log` of
  `pmActivePredictableMartingaleSum ε N / log N` for **all** $\varepsilon > 0$ (without `MemLp`),
  two-adic Euler bound `pmPowerDampedDivisorDensity_one_re_le_three_quarters`
  ($0 < (\operatorname{pmPowerDampedDivisorDensity}\,1).\text{re} \le 3/4$), and exact small-damping
  rates `tendsto_pmShiftedExponentCovariance_div_parameter`
  ($\lim_{\varepsilon \to 0^+} \operatorname{pmShiftedExponentCovariance}\,\varepsilon / \varepsilon = 1 - (\operatorname{pmPowerDampedDivisorDensity}\,1).\text{re} \ge 1/4$),
  `tendsto_pmActivePredictableMartingaleDrift_div_parameter`, and
  `tendsto_neg_half_pmShiftedExponentCovariance_div_parameter`.
- [`BezoutPronicInteriorSawtoothAndPredecessorPeakSplit.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/BezoutPronicInteriorSawtoothAndPredecessorPeakSplit.lean) —
  **Pillar XXIII (Bézout Interior Sawtooth Partition & Predecessor-Peak Telescoping):** Bézout
  divisor disjointness `eq_one_of_dvd_and_dvd_succ`, exact three-way partition
  `weightedCenteredSawtoothSum_eq_bezout_active_pair_add_interior` into predecessor post-jump peak +
  successor pre-jump trough + `bezoutInteriorSawtoothSum`, forward-difference representation
  `bezout_active_pair_eq_neg_half_addDiff` and telescoping sum `sum_Icc_bezout_active_pair_eq_terminal`,
  and complete centering-drift cancellation with pronic reduction when pairing pre-jump and
  post-jump active martingale terms (`pmActiveSawtoothComponent_pre_add_post_martingale_eq`).
- [`BezoutPronicTotientInteriorMartingaleSynthesis.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/BezoutPronicTotientInteriorMartingaleSynthesis.lean) —
  **Pillar XXIV (Bézout Pronic–Totient–Interior Martingale Synthesis):** Exact diagonal-free
  Bézout pronic–totient–interior square-increment identity
  `pmPowerDampedCenteredDivisorPrefix_sq_succ_sub_sq_eq_pronic_add_shiftedAddDiff_add_interior`
  ($A_\varepsilon(n + 1)^2 - A_\varepsilon(n)^2 = \widetilde{\tau}_\varepsilon(n)\,\widetilde{\tau}_\varepsilon(n + 1) + \widetilde{\tau}_\varepsilon(n + 1)\,\operatorname{addDiff}(\tau_{1+\varepsilon})\,n + 2\,\widetilde{\tau}_\varepsilon(n + 1)\,\operatorname{pmBezoutInteriorPrefix}\,\varepsilon\,n$),
  two-step symmetric midpoint duality `pmBezoutInteriorPrefix_add_half_shiftedAddDiff_eq_two_step_midpoint`,
  sub-horizon affine equivalence `pmBezoutInteriorPrefix_sub_bezoutInteriorSawtoothSum_eq_affine`,
  and global Bézout interior martingale decomposition
  `pmPowerDampedDivisorDiscreteEnergy_eq_activeDeleted_add_predecessorPeak_add_bezoutInterior`
  with RH cancellation criterion `riemannHypothesis_of_pmBezoutInteriorMartingale_cancellation`.
- [`RenormalizedMobiusDefectAndFirstOctaveCancellation.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/RenormalizedMobiusDefectAndFirstOctaveCancellation.lean) —
  **Pillar XIX:** Universal renormalized prefix defect `sieveRenormalizedPrefixDefect N M c = sieveCombinedPrefixDefect N M c - M * sieveSuccessorReserve N c`,
  its exact source-space evaluation `sieveRenormalizedPrefixDefect_eq_succ_sub_sq`, Dirichlet
  polarization `two_mul_sieveRenormalizedPrefixDefect_eq_neg_dirichlet_add_boundary`, complete
  common-return annihilation `sieveCombinedPrefixDefect_eq_zero_of_common_return`, and the exact
  first trans-horizon octave law and squarefree-count envelope for `moebiusCombinedPrefixDefect`
  (`moebiusCombinedPrefixDefect_first_octave_eq`, `moebiusCombinedPrefixDefect_first_octave_bounds`,
  `moebiusCombinedPrefixDefect_le_sub_horizon_linear_of_le_two_mul_sub_one`).
- [`JordanUpperBoundAndGcdOrbitPrimitiveEnergy.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/JordanUpperBoundAndGcdOrbitPrimitiveEnergy.lean) —
  **Pillar XX:** Sharp `3/4` multiplicative upper bound `four_mul_jordanTotient2_le_three_mul_sq_mul_totient`
  (`4 * J₂(n) ≤ 3 * n² * φ(n)` for `n ≥ 2`), sharp finite-level primitive energy bound
  `sixteen_mul_sievePrimitiveEnergy_le_sq_mul_sieveVariance` (`16 * sievePrimitiveEnergy N c ≤ N² * sieveVariance N c`),
  simultaneous diagonalization and Pythagorean split of `sieveVariance`, `sieveSuccessorCovariance`,
  `sieveSuccessorReserve`, and `12 * sievePrimitiveEnergy` under `sieveGcdProjection N h c`, and the
  cutoff-independent GCD-orbit stride bound `sixteen_mul_sievePrimitiveEnergy_gcdProjection_le_stride_sq`
  (`16 * sievePrimitiveEnergy N (sieveGcdProjection N h c) ≤ h² * sieveVariance N c`).
- [`PowerDampedRenormalizedDefectAndPronicCeiling.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/PowerDampedRenormalizedDefectAndPronicCeiling.lean) —
  **Pillar XXI:** Exact `2`-adic Euler factorization `pmPowerDampedDivisorCoeff_pronicSeq_eq_mul_erase_two`
  and universal pronic ceiling `pmPowerDampedDivisorCoeff_pronicSeq_le_one_sub_two_rpow`
  (`0 ≤ pmPowerDampedDivisorCoeff ε (pronicSeq k) ≤ 1 - 2^{-ε}` for all `k ≥ 1`, `ε ≥ 0`), exact
  sub-horizon pronic formula and unconditional non-positivity of `sieveRenormalizedPrefixDefect N M (pmPowerDampedRealWeight ε)`
  (`sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_nonpos`,
  `sieveCombinedPrefixDefect_pmPowerDampedRealWeight_le_linear_reserve`), and the master BVI
  frontier synthesis (`bezoutValuationIncidence_renormalized_defect_and_jordan_gcd_synthesis`).
- [`IteratedSuccessorPredictionAndReservePhaseLossSplit.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/IteratedSuccessorPredictionAndReservePhaseLossSplit.lean) —
  **Pillar XXII:** Exact variance–phase-loss conservation laws (`sieveVarianceAboveParity_successorPredictor_add_phaseLoss`,
  `sieveVariance_successorPredictor_add_phaseLoss`, `selbergTotientDiagonalForm_successorPredictor_add_phaseLoss`),
  two-step parity involution (`selbergMultiplesCoord_two_step_successorPredictor_one_and_two`),
  geometric $4^{-m}$ contraction of iterated successor prediction (`sieveVarianceAboveParity_iterated_successorPredictor_le`),
  and exact splitting of the $\{3, 6\}$ phase-loss degeneracy via `sieveSuccessorReserveAboveParity`
  (`successorPhaseLoss_reserveAboveParity_bounds`, `successorPhaseLoss_eq_half_reserveAboveParity_iff`,
  `successorPhaseLoss_eq_three_halves_reserveAboveParity_iff`).
- [`PostStepInactivePrefixAndSixDivisibilityPronicDefect.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/PostStepInactivePrefixAndSixDivisibilityPronicDefect.lean) —
  **Pillar XXV (Post-Step Inactive Prefix Smoothing, Divisor-Ordering Antitonicity & Universal `6`-Adic Bézout Ceilings):**
  Post-step inactive residual prefix `pmPostStepInactivePrefix`, intra-step shifted-exponent drift
  `pmPostStepInactivePrefix_sub_pmInactiveResidualPrefix` and square increment
  `pmPostStepInactivePrefix_sq_sub_pmInactiveResidualPrefix_sq`, two-point Bézout smoothing
  `addDiff_pmPostStepInactivePrefix` ($\frac{1}{2}(\widetilde{\tau}_\varepsilon(n) + \widetilde{\tau}_\varepsilon(n+1)) + \frac{1}{2}\operatorname{addDiff}(\tau_{1+\varepsilon})\,n$),
  universal divisor-ordering antitonicity `pmPowerDampedDivisorCoeff_le_of_dvd` and
  submultiplicativity `pmPowerDampedDivisorCoeff_mul_le`, and two-step / universal three-step
  `6`-adic Bézout product ceilings `pmPowerDampedDivisorCoeff_pronicSeq_le_six_of_three_dvd` and
  `pmPowerDampedDivisorCoeff_three_step_mul_le_six` ($\le (1 - 2^{-\varepsilon})(1 - 3^{-\varepsilon})$).
- [`PostStepInactiveEnergyAndPronicGradientConservation.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/PostStepInactiveEnergyAndPronicGradientConservation.lean) —
  **Pillar XXVI (General Linear Pronic Abel Summation, Post-Step Inactive Energy Equivalence & Exact Pronic–Gradient Conservation):**
  General linear Pronic Abel summation `sum_div_pronicSeq_add_terminal_eq_abel` and
  `sum_div_pronicSeq_eq_compensated_abel`, exact pronic reciprocal telescoping
  `sum_one_div_pronicSeq_eq` ($\sum_{n=1}^T 1/\operatorname{pronicSeq}\,n = 1 - 1/(T+1) \le 1$) and
  uniform $1/4$ bound `sum_pmActiveSawtoothComponent_sq_div_pronicSeq_bounds`, post-step inactive
  discrete energy `pmPostStepInactiveDiscreteEnergy` with two-sided equivalence to
  `pmPowerDampedDivisorDiscreteEnergy` and RH criterion
  `riemannHypothesis_of_pmPostStepInactive_cofinal_discrete_budget`, and exact pointwise and finite
  pronic–diagonal–gradient conservation laws
  `addDiff_pmPowerDampedDivisorCoeff_sq_add_two_mul_pronicSeq`,
  `two_point_bezout_average_sq_add_quarter_addDiff_sq`, `sum_Icc_pronicSeq_add_addDiff_sq_eq`, and
  boundary-free finite inequalities `sum_Icc_pronicSeq_add_addDiff_sq_le_two_mul_sum_sq` and
  `sum_Icc_pronicSeq_and_addDiff_sq_le_sum_sq`.
