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
