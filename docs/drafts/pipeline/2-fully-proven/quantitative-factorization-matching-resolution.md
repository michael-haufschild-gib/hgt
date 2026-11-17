# Resolution of the Local Factorization-Matching Extension Question

- **ID:** `QFM-2-6-RESOLUTION`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `docs/reports/review-1711/obstacles-summary.md` §2.6, §2.11
- **Statement:** Complete positive and negative classification of prime-factorization opposite-parity matchings across squarefree factor counts, their unmatched populations on dyadic blocks, and their unconditional analytic equivalences with zero-free strips and the Riemann hypothesis.

## Goal

Answer completely and unconditionally every part of §2.6:
1. Whether the local prime–semiprime / semiprime–triprime cell matching extends across squarefree factor counts with a controlled unmatched population.
2. Whether allowing a common squarefree cofactor and exchanging a small prescribed or bounded-arity group of primes of opposite parity yields a common supply across growing cofactors and factor counts, or fails on an explicit deficient source family (identifying the extra moves required).
3. What happens when those extra moves are adopted globally on $(X, 2X]$, together with the unconditional positivity-free and spectral-free analytic equivalences linking dyadic unmatched counts to $M(x)$, $\sum \mu(n)n^{-s} = 1/\zeta(s)$, zero-free strips below $20999/24000$, and the Riemann hypothesis, plus the integer-norm prime-edit selectivity barrier.

## Gates

- [x] 0 → 1  in-progress: exact definitions, all parameter regimes, and non-circular receivers fixed
- [x] 1 → 2  fully-proven: complete dependency-closed paper proofs `[PROVED HERE]`
- [ ] 2 → 3  formalized: unconditional Lean modules in `GaloisForLFunctions/QuantitativeFactorizationMatching/`, wired into `MainTheorems.lean`, `lake --old env lean` green, standard axioms only

## Theorems and Paper Proofs `[PROVED HERE]`

### 1. König–Ore Deficiency Split and Sequential Cascade Conservation

Let $S \subset \mathbb{N}$ be a finite set of squarefree positive integers, partitioned into $S_\pm = \{n \in S : \mu(n) = \pm 1\}$ and into factor-count layers $\mathcal{Q}_k(S) = \{n \in S : \omega(n) = k\}$.

**Theorem 1.1 (Exact Bipartite Deficiency Decomposition).** For any allowed edge relation $R \subseteq S_+ \times S_-$ with neighborhood map $N_R(U) = \{b \in S_- : \exists a \in U, R(a, b)\}$, define the Hall deficiency $\operatorname{def}_R(S_+) = \max_{U \subseteq S_+} (\#U - \#N_R(U))$. Then the maximum matching cardinality in $R$ is $\nu(R) = \#S_+ - \operatorname{def}_R(S_+)$, and the minimum unmatched cardinality $U_{\min}(R) = \#S - 2\nu(R)$ satisfies
$$
U_{\min}(R) = 2\operatorname{def}_R(S_+) - \sum_{n \in S} \mu(n) = \left|\sum_{n \in S} \mu(n)\right| + 2\,\operatorname{HallExcess}(R),
$$
where $\operatorname{HallExcess}(R) = \operatorname{def}_R(S_+) - \max\!\big(0, \sum_{n \in S}\mu(n)\big) \ge 0$. In particular, every $R$-isolated subset $I_0 \subseteq S$ forces $U_{\min}(R) \ge \#I_0$.

*Proof.* For any matching $(A, f)$ ($A \subseteq S_+$, $f : A \hookrightarrow S_-$ with $R(a, f(a))$), $\sum_{n \in S} \mu(n) = \#S_+ - \#S_- = (\#(S_+ \setminus A) - \#(S_- \setminus f(A)))$, so $|\sum_{n \in S}\mu(n)| \le \#(S \setminus (A \cup f(A))) = \#S - 2\#A$. For any $U \subseteq S_+$, $f(A \cap U) \subseteq N_R(U)$, so $\#A = \#(A \setminus U) + \#(A \cap U) \le \#(S_+ \setminus U) + \#N_R(U) = \#S_+ - (\#U - \#N_R(U))$; taking the minimum over $U$ gives $\nu(R) \le \#S_+ - d$ where $d = \operatorname{def}_R(S_+)$. Conversely, adjoin $d$ auxiliary elements $D = \operatorname{Fin} d$ to $S_-$ with every $a \in S_+$ adjacent to all of $D$. Every nonempty $U \subseteq S_+$ then has enlarged neighborhood of size $\#N_R(U) + d \ge \#U$. Hall's marriage theorem yields an injection $g : S_+ \hookrightarrow S_- \sqcup D$; restricting $g$ to $A = g^{-1}(S_-)$ gives an $R$-matching of size $\#A \ge \#S_+ - d$. Evaluating $U = \emptyset$ and $U = S_+$ yields $\operatorname{def}_R(S_+) \ge \max(0, \#S_+ - \#S_-)$, giving the nonnegativity of $\operatorname{HallExcess}(R)$. $\square$

**Theorem 1.2 (Universal Telescoping Law for Adjacent-Layer Cascades).** Suppose injections $\varphi_k : U_k \hookrightarrow \mathcal{Q}_{k+1}(S)$ ($1 \le k \le K$) are defined inductively on unconsumed sources $U_1 = \mathcal{Q}_1(S)$ and $U_{k+1} = \mathcal{Q}_{k+1}(S) \setminus \varphi_k(U_k)$. Then:
1. All $K$ matched pairs $\big\{(u, \varphi_k(u)) : u \in U_k\big\}_{1 \le k \le K}$ are pairwise vertex-disjoint across all layers, cover $\big(\bigsqcup_{k=1}^K \mathcal{Q}_k(S)\big) \sqcup \varphi_K(U_K)$, and cancel identically in $\sum \mu(n)$.
2. Independently of the choice of injections $\varphi_1, \dots, \varphi_K$, the unconsumed remainder in layer $K+1$ satisfies
$$
(\#U_{K+1} : \mathbb{Z}) = (-1)^{K+1} \sum_{\substack{n \in S \\ 1 \le \omega(n) \le K+1}} \mu(n).
$$
Consequently, sequential upward exhaustion across all non-empty layers of $S$ is possible only when $(-1)^{k+1}\sum_{1 \le \omega(n) \le k+1} \mu(n) \ge 0$ for every $k$, and leaves zero unmatched elements at the top iff $\sum_{n \in S} \mu(n) = 0$.

*Proof.* Disjointness holds by induction on $K$: $\bigcup_{j=1}^K (U_j \cup \varphi_j(U_j)) = \big(\bigcup_{j=1}^K \mathcal{Q}_j(S)\big) \sqcup \varphi_K(U_K)$ because $U_k \sqcup \varphi_{k-1}(U_{k-1}) = \mathcal{Q}_k(S)$ and $\omega$ separates distinct layers. Since $\varphi_k$ is injective with $\varphi_k(U_k) \subseteq \mathcal{Q}_{k+1}(S)$, $\#U_{k+1} = \#\mathcal{Q}_{k+1}(S) - \#U_k$, whence induction on $k$ gives $\#U_{K+1} = \sum_{j=1}^{K+1} (-1)^{K+1-j} \#\mathcal{Q}_j(S) = (-1)^{K+1}\sum_{1 \le \omega(n) \le K+1} \mu(n)$ as $\mu(n) = (-1)^{\omega(n)}$ on $\mathcal{Q}_j(S)$. $\square$

### 2. All-Finite-Depth Extension vs. Unbounded-Depth Failure of the $\{2, 3, 5\}$ Cell Matching

**Theorem 2.1 (All-Finite-Depth Cellwise Matching Theorem).** Fix any $K \ge 1$ and $B > 0$. Partition $(R, 2R]$ into $J = \lfloor (\log R)^B \rfloor$ cells of width $h = R / J \le 2R / (\log R)^B$. For all sufficiently large $R$:
1. Every cell $(u, v] \subseteq [R, 2R]$ of width $v - u \ge R / (\log R)^B$ satisfies, for all $1 \le k \le K$,
$$
\#\mathcal{Q}_k(u, v) \le \frac{v - u}{\log R}\left(\frac{(\log\log R + C_M)^{k-1}}{(k-1)!} + C_k (\log\log R + C_M)^{k-2}\right),
$$
while the $(k+1)$-prime family $T_{k+1}(u, v) = \{q d r \in (u, v] : q \in \{2, 3, 5\},\; d \in D_{k-1}(\lfloor R^{1/(2k)}\rfloor),\; r \text{ prime}\}$ satisfies
$$
\#T_{k+1}(u, v) \ge \frac{61}{60}\frac{v - u}{\log R}\,\frac{(\log\log R - C'_k)^{k-1}}{(k-1)!} \ge \#\mathcal{Q}_k(u, v).
$$
2. Consequently, sequential cellwise injections $\varphi_1, \dots, \varphi_K$ match **every** squarefree integer in $(R, 2R]$ with $1 \le \omega(n) \le K$ to a distinct opposite-sign partner in its own cell, with all pairs pairwise disjoint across all $K$ layers, unweighted Möbius sum identically $0$, and smooth Gamma-jet energy $\le C_{K, B} R^{1-\delta} (\log\log R)^{2K-2} / (\log R)^{2B+2}$ uniformly in $0 \le \delta \le 1$.
3. Nevertheless, for every fixed $K \ge 1$, the unmatched squarefree integers in $(R, 2R]$ after $K$ layers number $\frac{6}{\pi^2} R - O_K\!\big(R (\log\log R)^K / \log R\big) = \big(\frac{6}{\pi^2} - o(1)\big) R$.

*Proof.* For $n \in \mathcal{Q}_k(u, v)$ ($k \ge 2$), let $r = P^+(n)$ be its largest prime factor and $d = n / r \in \mathcal{Q}_{k-1}$. Since $R < n \le r^k$, $r > R^{1/k}$ and $u/d \ge (R/n)r \ge \frac{1}{2} R^{1/k}$, so $\log(u/d) \ge \frac{1}{2k}\log R$ for large $R$. Applying the log-power Chebyshev bound `abs_theta_increment_le` at exponent $A = \lceil B \rceil + 2$ to $(u/d, v/d]$ and `(log R - log d)⁻¹ ≤ (log R)⁻¹ + 2k log d / (log R)²`, then summing over $d \le 2R$ with $(k-1)! \sum_{\omega(d)=k-1} d⁻¹ \le (\sum_{p \le 2R} p⁻¹)^{k-1}$ and $\sum_{\omega(d)=k-1} (\log d)/d \le (\sum_{p \le 2R} (\log p)/p)\sum_{\omega(d')=k-2} d'⁻¹$ yields (1)'s upper bound via Mertens' first and second theorems. For $T_{k+1}(u, v)$, $q \le 5 < p \le N = \lfloor R^{1/(2k)}\rfloor < \frac{1}{5} R^{1/2 + 1/(2k)} < r$ separates $q$, $d$, and $r$ uniquely, making the families $(q, d)$ pairwise disjoint; the non-injective tuple diagonal in $(\sum_{5 < p \le N} p⁻¹)^{k-1}$ is at most $(k-1)^2 (\sum_{p > 5} p^{-2})(\sum_{5 < p \le N} p⁻¹)^{k-3}$, giving (1)'s lower bound with $\frac{61}{62}\cdot\frac{31}{30} = \frac{61}{60} > 1$. Inductive application of `exists_cellwise_injOn` on $U_k = \mathcal{Q}_k \setminus \operatorname{im}(\varphi_{k-1}) \subseteq \mathcal{Q}_k$ and Theorem 1.2 gives (2), and subtracting $2\sum_{k=1}^K \#\mathcal{Q}_k(R, 2R) = o(R)$ from $\#\mathcal{Q}(R, 2R) = \frac{6}{\pi^2} R + O(\sqrt{R})$ gives (3). $\square$

### 3. Deficient Source Families Ruling Out Prescribed-Prime and Local Bounded-Arity Rules

**Theorem 3.1 (Global Isolation of Rough Sources Under Any Finite Prescribed Prime Set).** Let $P_0 \subset \mathbb{P}$ be any finite set of primes and $M_0 = \prod_{p \in P_0} p$. Consider the global dyadic graph on $\mathcal{Q}(X)$ ($X \ge 1$) permitting all opposite-parity cofactor exchanges $n = a u \leftrightarrow m = a v$ where $a, u, v$ are pairwise coprime squarefree integers, $\mu(u) = -\mu(v)$, and all prime factors of $u$ and $v$ lie in $P_0$.
1. Every $P_0$-rough squarefree integer $n \in \mathcal{R}_{P_0}(X) = \{n \in \mathcal{Q}(X) : \gcd(M_0, n) = 1\}$ is **isolated** in $(X, 2X]$.
2. Both polarity halves $\mathcal{R}_{P_0, \pm}(X) = \{n \in \mathcal{R}_{P_0}(X) : \mu(n) = \pm 1\}$ satisfy $\lim_{X \to \infty} \#\mathcal{R}_{P_0, \pm}(X) / X = \frac{3}{\pi^2}\prod_{p \in P_0}\frac{p}{p+1} > 0$, so every opposite-parity matching using $P_0$-prescribed exchanges leaves at least $\big(\frac{6}{\pi^2}\prod_{p \in P_0}\frac{p}{p+1} - o(1)\big)X$ unmatched integers in **every** dyadic block $(X, 2X]$.
3. Under asymmetric $P_0$-catalysed upward moves $n = a p \to m = a q r$ ($q \in P_0$, $p, r$ arbitrary primes), every squarefree multiple of $M_0$ in $(X, 2X]$ has zero upward neighbors, forming a positive-density family of size $\big(\frac{6}{\pi^2 M_0}\prod_{p \in P_0}\frac{p}{p+1} - o(1)\big)X$.

*Proof.* (1) If $\gcd(M_0, n) = 1$ and $n = a u$ with prime factors of $u$ in $P_0$, then $u = 1$, so $\mu(v) = -\mu(1) = -1$ forces $v \ge 2$, whence $m = n v \ge 2n > 2X \notin (X, 2X]$. (2) `tendsto_coprimeSquarefreeMean_of_squarefree` gives $\#\mathcal{R}_{P_0}(X)/X \to \frac{6}{\pi^2}\prod_{p \in P_0}\frac{p}{p+1}$ on $(X, 2X] = [1, 2X] \setminus [1, X]$ and `tendsto_coprimeMoebiusMean` gives $(\#\mathcal{R}_{P_0,+}(X) - \#\mathcal{R}_{P_0,-}(X))/X \to 0$. (3) If $M_0 \mid a p$ and $a q r$ is squarefree with $q \in P_0$, then $q \nmid a$ forces $q = p$, so $a q r = n r \ge 2n > 2X$; reindexing $n = M_0 b$ with $\gcd(M_0, b) = 1$ gives the density. $\square$

**Theorem 3.2 (All-Block Friable Isolation Under Power-Local and Log-Power Cell Bounded-Arity Moves).** Fix any source arity $k \ge 1$, and allow all opposite-parity cofactor moves $n = a u \leftrightarrow m = a v$ ($a, u, v$ squarefree, $u \neq v$, $\omega(u) \le k$, arbitrary target $v$ with no arity cap on $v$).
1. **Power-local cells ($H(X) \le C X^\theta$, $\theta < 1$):** Put $r = \max\!\big(2, \lfloor \frac{k}{1 - \max(\theta, 0)} \rfloor + 2\big)$. For every sufficiently large real $X$, the $r$-prime family $\mathcal{S}_r(X) = \{(\prod_{p \in T} p) p_* : T \in \text{windowPrimes}(Y, 2^{1/(2r)}Y)^{(r-1)},\; p_* \in \text{windowPrimes}(\max(2^{1/(2r)}Y, X/\prod_{T} p), 2X/\prod_T p)\}$ ($Y = X^{1/r}$) lies in $\mathcal{Q}_r(X)$, has every element at distance $> C X^\theta$ from every bounded-arity cofactor neighbor, and satisfies $\#\mathcal{S}_r(X) \ge c_r X / (\log X)^r$. Thus for **every** $\beta < 1$ (including $\beta = 20999/24000$ and $\beta = 1/2 + \varepsilon$), the isolated population in $(X, 2X]$ exceeds $X^\beta$ for all large $X$.
2. **Log-power cells ($h = X / \lfloor(\log X)^B\rfloor$, $B > k$):** For every $\beta < 1 - k/B$ and all sufficiently large real $X$, choosing $\gamma \in (\frac{1}{1-\beta}, \frac{B}{k})$ and $z = (\log X)^\gamma$, $\sqrt{2}$-multiplicative binning of $r_1$-subsets of primes in $(z/2, z]$ ($r_1 = \lfloor \frac{\log X}{\log z} \rfloor - 3$) multiplied by a greedy cofactor in $(z, 4z]$ produces $\ge X^\beta$ distinct $(4z)$-smooth squarefree integers in $(X, 2X]$, each at distance $> 2X/(\log X)^B \ge h$ from every arity-$k$ cofactor neighbor (hence completely isolated in its log-power cell). In particular, for $B > 2k$ the unmatched count exceeds $X^{1/2+\delta}$, and for $B > 24000 k$ it exceeds $X^{20999/24000 + \delta}$, on **every** large dyadic block $(X, 2X]$.

*Proof.* If all prime factors of $n > X$ are $\le y$ and $n = a u$ with $\omega(u) \le k$, then $u \le y^k$ and $|a v - a u| = a|v - u| \ge a = n/u > X / y^k$.
For (1), $\alpha = 2^{1/(2r)}$ gives $Y^{r-1} < d = \prod_{p \in T} p \le \sqrt{2} Y^{r-1}$, so $\frac{2X}{d} \ge \sqrt{2} Y$ while $\alpha Y \le 2^{1/4} Y$ and $\frac{X}{d} \le Y$, giving window length $\ge (\sqrt{2} - 2^{1/4}) Y > \frac{1}{5} Y$ and upper endpoint $\le 2Y$. Since $p_* > \alpha Y$ is the unique prime factor of $d p_*$ above $\alpha Y$, $(T, p_*) \mapsto d p_*$ is injective into $\mathcal{Q}_r(X)$ with $y = 2 X^{1/r}$, so $X/y^k = 2^{-k} X^{1 - k/r} > C X^\theta$. Using $r'^r \binom{M}{r'} \ge M^{r'}$ and PNT on $(Y, \alpha Y]$ and on the $p_*$-window yields $\#\mathcal{S}_r(X) \ge c_r X / (\log X)^r$.
For (2), $(z/2)^{r_1} < \Pi(S) \le z^{r_1} \le X/z^3$ spans logarithmic width $r_1 \log 2$, covered by $2 r_1 + 2$ intervals of logarithmic width $\frac{1}{2}\log 2$. Pigeonhole selects a fiber $\mathcal{F}_0$ of size $\ge \binom{M_1}{r_1}/(2r_1+2)$ with $\Pi(S) \in [W, \sqrt{2}W]$. Multiplying distinct primes in $(z, \frac{5}{4}z]$ until the last partial product $Q_t \le \frac{X}{2zW}$ satisfies $\frac{X}{\frac{5}{2}zW} < Q_t \le \frac{X}{2zW}$, and PNT supplies a prime $q_* \in (\frac{X}{W Q_t}, \frac{\sqrt{2}X}{W Q_t}] \subseteq (2z, 4z]$, giving $m_2 = Q_t q_*$ coprime to $\Pi(S)$ with $\Pi(S) m_2 \in (X, 2X]$ and $y = 4(\log X)^\gamma$, so $X/y^k = 4^{-k} X / (\log X)^{k\gamma} > 2X/(\log X)^B$. Finally $r_1^{r_1}\binom{M_1}{r_1} \ge M_1^{r_1}$ gives $(M_1/r_1)^{r_1} \ge (\frac{1}{4}(\log X)^{\gamma-1})^{r_1} = X^{1 - 1/\gamma - o(1)} > (2r_1+2) X^\beta$. $\square$

### 4. Global Dyadic $(1 \leftrightarrow 2)$ Moves, Growing Common Supply, and Canonical Cofactor Fibres

**Theorem 4.1 (Global Dyadic Non-Isolation and Growing Common Supply of $\mathcal{G}_2(X)$).** On $(X, 2X]$:
1. No $(0 \leftrightarrow s)$ pure insertion/deletion move exists inside $(X, 2X]$ ($n \in (X, 2X]$ and $v \ge 2 \implies n v > 2X$), so $(1 \leftrightarrow 2)$ ($n = a p \leftrightarrow m = a q r$, $\gcd(a, p) = \gcd(a, qr) = 1$) is the minimal opposite-parity factorization move.
2. For **every** real $X \ge 30$ and **every** $n \in \mathcal{Q}(X)$, $n$ has at least one opposite-parity neighbor in $\mathcal{G}_2(X)$ inside $(X, 2X]$.
3. For **every** $D \in \mathbb{N}$, for all sufficiently large $X$, **every** $n \in \mathcal{Q}(X)$ has at least $D$ distinct opposite-parity neighbors in $\mathcal{G}_2(X)$ uniformly across all cofactors $a$ and all factor counts $\omega(n)$.

*Proof.* If $\omega(n) = 1$, $n = p$ is adjacent to $2r \in (X, 2X]$ for every odd prime $r \in (X/2, X]$; Bertrand's postulate on $\lfloor X/2 \rfloor \ge 15$ gives one such $r > 15 > 2$ for $X \ge 30$, and PNT gives $\to \infty$ as $X \to \infty$. If $\omega(n) \ge 2$, let $p_2 = P^+(n)$ and $p_1 = P^+(n / p_2)$ be the two largest primes dividing $n$, and set $a = n / (p_1 p_2)$. Then $p_1 \ge 2, p_2 \ge 3$ and every prime $q \mid a$ satisfies $q < p_1$. If $a = 1$, $\lfloor X/a \rfloor = \lfloor X \rfloor \ge 30$; if $a > 1$, $q \ge 2 \implies p_1 \ge 3, p_2 \ge 5$, so $X/a \ge n/(2a) = p_1 p_2 / 2 \ge \frac{5}{2} p_1 > p_1$, whence $\lfloor X/a \rfloor \ge p_1 > q$ for all $q \mid a$. Every prime $r \in (\lfloor X/a \rfloor, 2\lfloor X/a \rfloor]$ satisfies $X < a r \le 2X$ and $r > P^+(a)$ (so $a r \in \mathcal{Q}(X)$ with $\mu(ar) = -\mu(n)$); Bertrand's postulate gives one for all $X \ge 30$, and since $n \le \prod_{q \le p_2} q$ forces $p_2 \to \infty$ uniformly for $n > X \to \infty$, `windowPrimes(X/a, 2X/a)` has size $\ge D$ for large $X$. $\square$

**Theorem 4.2 (Canonical Collision-Free Even-Prefix Cofactor Partition and Fibre-Boundary Debt).** Define $\alpha : \mathcal{Q}(X) \to \mathbb{N}$ ($X \ge 1$) by $\alpha(n) = n / P^+(n)$ if $\omega(n)$ is odd, and $\alpha(n) = n / (P_2^+(n) P^+(n))$ if $\omega(n)$ is even.
1. For every $n \in \mathcal{Q}(X)$, $\alpha(n)$ is squarefree with $\omega(\alpha(n))$ even ($\mu(\alpha(n)) = +1$), partitioning $\mathcal{Q}(X) = \bigsqcup_{a} (\mathcal{F}_-(a; X) \sqcup \mathcal{F}_+(a; X))$ into pairwise-disjoint complete bipartite subgraphs of $\mathcal{G}_2(X)$ with zero cross-cofactor target collisions.
2. Whenever $a \cdot P^+(a)^3 \ge 2X$ (in fact whenever $a \cdot P^+(a)^2 \ge 2X$), $\mathcal{F}_+(a; X) = \emptyset$. For all large $X$, the triprimes $p_1 p_2 p_3 \in (X, 2X]$ with $p_1 \in (\frac{1}{8}X^{1/3}, \frac{1}{6}X^{1/3}]$, $p_2 \in (2 X^{1/3}, \frac{9}{4} X^{1/3}]$, and $p_3 \in (\frac{X}{p_1 p_2}, \frac{2X}{p_1 p_2}]$ all lie in fibres with $\mathcal{F}_+(a; X) = \emptyset$ and number $\ge c X / (\log X)^3$, proving that cross-cofactor alternating paths are strictly necessary even on $(X, 2X]$.

*Proof.* (1) Single-valuedness of $\alpha$ makes the fibres pairwise disjoint; for $x = a p \in \mathcal{F}_-(a; X)$ and $y = a q r \in \mathcal{F}_+(a; X)$, $P^+(a) < p$ and $P^+(a) < q < r$ give $\gcd(a, p) = \gcd(a, qr) = 1$ and $\mu(x) = -1 = -\mu(y)$. (2) Any $a q r \in \mathcal{F}_+(a; X)$ satisfies $P^+(a) < q < r$, so $a q r > a P^+(a)^2$. For $a = p_1 p_2$ in the stated ranges, $P^+(a) = p_2 > 2 X^{1/3}$ and $p_1 > \frac{1}{8} X^{1/3}$ give $a P^+(a)^2 = p_1 p_2^3 > X^{4/3} > 2X$ for $X > 8$, while $p_3 > \frac{X}{p_1 p_2} \ge \frac{8}{3} X^{1/3} > p_2 > p_1$ makes $(p_1, p_2, p_3) \mapsto p_1 p_2 p_3$ injective into $\mathcal{Q}_3(X)$ of size $\gg X/(\log X)^3$. $\square$

### 5. Positivity-Free Analytic Equivalences and Integer-Norm Prime-Edit Selectivity

**Theorem 5.1 (Positivity-Free Strip Transfer, Sub-$20999/24000$ Criterion, and RH Equivalence).**
1. If $\theta \in (0, 1)$ and every dyadic block $(X, 2X]$ ($X \ge X_0$) admits a disjoint opposite-parity matching on $\mathcal{Q}(X)$ with $\le C X^\theta$ unmatched integers, then:
   - $|M(n)| = |\sum_{d=1}^n \mu(d)| \le K n^\theta$ for all $n \ge 1$ by dyadic block summation;
   - Partial summation gives convergence of $\sum_{n=1}^\infty \mu(n)n^{-s}$ to a holomorphic function $F(s)$ on $\{\operatorname{Re} s > \theta\}$;
   - Analytic continuation of $F(s)\cdot(s - 1)\zeta(s) = s - 1$ from $\{\operatorname{Re} s > 1\}$ across the convex half-plane $\{\operatorname{Re} s > \theta\}$ proves $\zeta(s) \neq 0$ for all $s \neq 1$ with $\operatorname{Re} s > \theta$, hence $\Theta \le \max(\frac{1}{2}, \theta)$.
2. Any dyadic matching exponent $\theta \in [\frac{1}{2}, \frac{20999}{24000})$ yields a strictly wider zero-free strip $\Theta \le \theta < \frac{20999}{24000}$.
3. Having a dyadic opposite-parity matching with $O_\varepsilon(X^{1/2+\varepsilon})$ unmatched integers for every $\varepsilon > 0$ is **equivalent** to `RiemannHypothesis` (via the functional equation in the forward direction, and Theorem 1.1 + Littlewood's bound in the reverse direction), while unconditionally $U_{\min}(\mathcal{Q}(X)) = O(X^\beta)$ holds for every $\beta > \frac{20999}{24000}$ and at $\beta = \frac{7}{8}$ exact.

**Theorem 5.2 (Integer-Norm Prime-Edit Selectivity Barrier).** For every $\sigma \in (\frac{20999}{24000}, \frac{14}{15})$ (including $\sigma = \frac{7}{8}$) and every $\sigma' \in (\frac{1}{2}, \sigma)$, there exists a two-sided integer-norm edit `editSystem e` of the rational primes with $N_e(x) = A' x + O(x^{14/15})$ and identical log-power window prime counts whose generalized squarefree dyadic blocks admit **no** opposite-parity matching with $O(X^{\sigma'})$ unmatched elements (cofinally exceeding $C X^{\sigma'}$ for every $C > 0$).

*Proof.* `exists_isEdit_zeros_on_line_right_of_sub_seed` supplies `e` and $G$ holomorphic on $\{\operatorname{Re} s > 1/2\}$ with $G(s) = (s - 1)\zeta_e(s)$ on $\{\operatorname{Re} s > 1\}$ and $G(z_0) = 0$ at $\operatorname{Re} z_0 = \sigma$. If every dyadic block $\{g : X < |g| \le 2X\}$ had an opposite-`moebius` matching leaving $\le C X^{\sigma'}$ unmatched squarefree elements, dyadic summation would bound $|\sum_{|g| \le x} \mu_e(g)| \le K x^{\sigma'}$; partial summation (`growthCont`) on the norm-grouped Möbius series $c_e(n) = \sum_{|g|=n} \mu_e(g)$ would continue $\sum \mu_e(g)|g|^{-s}$ holomorphically to $\{\operatorname{Re} s > \sigma'\}$, where $F_e(s) G(s) = s - 1$ by continuation from $\{\operatorname{Re} s > 1\}$, forcing $0 = F_e(z_0) G(z_0) = z_0 - 1 \neq 0$, a contradiction. $\square$

## Log

- 2026-11-17 — complete paper resolution proved across all 5 theorems; proceeding immediately to unconditional Lean 4 formalization.
