# E-Q5: Subexponential growth of $F(u)e^{-8u}$ on a thick tail implies AAL

- **ID:** ecs-q5-thick-tail-aal
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Source:** docs/reports/review-1611/route-ecs.md §6 (E-Q5)
- **Lean Module:** `GaloisForLFunctions.ExclusionOfTheCriticalState.Decay.SubexponentialThickTailGivesTheAbscissaLaw`
- **Statement:** If the confined critical state $F$ has $F(u)e^{-8u}$ growing subexponentially along a thick set of $u \to -\infty$ (in local $L^1$, a.e. pointwise on a continuous thick set, or via its heated zero series), then `RHTower.AsymptoticAbscissaLaw` holds unconditionally.

## Goal
Settle E-Q5 unconditionally with zero tail-pollution loss, together with the general weighted-tower transfer theorem, the heated-state receiver, the contrapositive syndetic excursion law under $\neg\text{AAL}$, and the sharp $a = 0$ exclusion under `ZerosApproachLine` / `FiniteOffLine`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven: complete dependency-closed paper proof below `[PROVED HERE]`
- [x] 2 → 3  formalized: `GaloisForLFunctions.ExclusionOfTheCriticalState.Decay.SubexponentialThickTailGivesTheAbscissaLaw`

## Dependency-Closed Paper Proof `[PROVED HERE]`

### 1. Smooth interpolation on $(-\ell, 0)$
Let $\ell > 0$, $n \in \mathbb{N}$, $z : \operatorname{Fin} n \to \mathbb{C}$ injective, and $b : \operatorname{Fin} n \to \mathbb{C}$. Set
$$\delta := \min\!\left(\frac{\ell}{4},\, \frac{1}{4(1 + \sum_k \|z_k\|)}\right) > 0, \qquad \tau := \min\!\left(\frac{\ell}{4(n+1)},\, \frac{1}{1 + \sum_{k,l} \|z_k - z_l\|}\right) > 0,$$
and $t_j := -(2\delta + j\tau)$ for $j \in \operatorname{Fin} n$. Using the Mathlib $C^\infty$ bump $\varphi_\delta = \text{smallBump}\,\delta$ supported in $(-\delta, \delta)$, each $\psi^{(j)}(u) := \varphi_\delta(u - t_j)$ lies in $C_c^\infty(\mathbb{R})$ and vanishes outside $(-\ell, 0)$ since $|u - t_j| < \delta \implies -\ell < -3\delta - n\tau \le u < -\delta < 0$.
Its two-sided Laplace transform satisfies $\widehat{\psi^{(j)}}(z_k) = e^{2\delta z_k} h_0(z_k) (e^{\tau z_k})^j$, where $h_0(z_k) = \int \varphi_\delta(u) e^{-z_k u}\,du = \text{paperFT}(\varphi_\delta)(i z_k) \ne 0$ because $\|i z_k\|\delta \le 1/4$ (`paperFT_bumpTest_zero_ne_zero`). Moreover $k \mapsto e^{\tau z_k}$ is injective: if $e^{\tau z_k} = e^{\tau z_l}$, then $\tau(z_k - z_l) = 2\pi i m$ for $m \in \mathbb{Z}$, and $\tau\|z_k - z_l\| < 1 < 2\pi$ forces $m = 0$, hence $k = l$. Thus $M = \operatorname{diag}(e^{2\delta z_k} h_0(z_k)) \cdot V(e^{\tau z_k})$ is invertible, and $\psi_0 := \sum_j (M^{-1}b)_j \psi^{(j)} \in C_c^\infty((-\ell, 0))$ satisfies $\widehat{\psi_0}(z_k) = b_k$ for all $k$.

### 2. Exact shifted-test tower identity (avoiding Gaussian tail pollution)
For $\psi_0 \in C_c^\infty((-\ell, 0))$ and $\nu \in \mathbb{N}$, define $\psi_\nu(u) := \psi_0(u + \nu\ell)$. Then $\psi_\nu \in C_c^\infty(\mathbb{R})$ vanishes outside $(-(\nu+1)\ell, -\nu\ell) \subset (-\infty, 0)$ and satisfies $\widehat{\psi_\nu}(p) = \widehat{\psi_0}(p) e^{\nu\ell p}$. At $p = z_q = \rho_q - 1/2$, $e^{\nu\ell z_q} = (\text{frobTower}\,\ell\,\text{zetaConfig}\,q)^\nu$.
Applying `criticalState_hasSum_zeroSeries_test_left` to $\psi_\nu$ yields the exact identity (with zero boundary or tail error):
$$\text{levelSum}(\text{frobTower}\,\ell\,\text{zetaConfig})\,b\,\nu = -a(W_0) \int_{-(\nu+1)\ell}^{-\nu\ell} \psi_0(u + \nu\ell) e^{-8u} F(u)\,du,$$
where $b_q := \mathcal{L}F(z_q)\widehat{\psi_0}(z_q)$ satisfies $\sum_q \|b_q\| < \infty$ by `(criticalState_hasSum_zeroSeries_test_left ... (ν := 0)).summable.norm`. Since $\psi_0$ is continuous and compactly supported, $\|\psi_0\|_\infty \le B < \infty$, giving
$$\|\text{levelSum}(\text{frobTower}\,\ell\,\text{zetaConfig})\,b\,\nu\| \le a(W_0) B \int_{-(\nu+1)\ell}^{-\nu\ell} |F(u)| e^{-8u}\,du.$$

### 3. Elimination of an isolated top (`E-Q5` local $L^1$ and `ThickLeft` theorems)
Suppose `¬ RHTower.AsymptoticAbscissaLaw`. By `not_asymptoticAbscissaLaw_iff_hasIsolatedTop`, there exist a finite nonempty set $F_{\text{top}}$ of `XiZeroCopy` and $\Theta_2 < \Theta$ with $\Theta > 1/2$, $\operatorname{Re}\rho_q = \Theta$ on $F_{\text{top}}$, and $\operatorname{Re}\rho_q \le \Theta_2$ outside $F_{\text{top}}$. Pick $q_0 \in F_{\text{top}}$. Enumerate the distinct values of $z_j = \text{centredZero}\,j$ ($j \in F_{\text{top}}$) and construct $\psi_0 \in C_c^\infty((-\ell, 0))$ via §1 with $\widehat{\psi_0}(z_{q_0}) = 1$ and $\widehat{\psi_0}(z) = 0$ on all other distinct points in $F_{\text{top}}$.
Every copy $j \in F_{\text{top}}$ with $z_j = z_{q_0}$ has $e^{\ell z_j} = e^{\ell z_{q_0}}$, while every other $j \in F_{\text{top}}$ in the fiber $\{j \in F_{\text{top}} : e^{\ell z_j} = e^{\ell z_{q_0}}\}$ has $z_j \ne z_{q_0}$, hence $\widehat{\psi_0}(z_j) = 0$. Thus the merged weight of $q_0$ is
$$\sum_{\substack{j \in F_{\text{top}} \\ e^{\ell z_j} = e^{\ell z_{q_0}}}} b_j = \#\{j \in F_{\text{top}} : z_j = z_{q_0}\} \cdot \mathcal{L}F(z_{q_0}) \ne 0,$$
since $\#\{j \in F_{\text{top}} : z_j = z_{q_0}\} \ge 1$ and $\operatorname{Re} z_{q_0} = \Theta - 1/2 > 0 \implies \mathcal{L}F(z_{q_0}) \ne 0$ (`criticalHalfLineGroundState_closedRightHalfPlaneLaplace_ne_zero`).
Taking $a := (\Theta - 1/2)/2 > 0$, a bound $\int_{-(\nu+1)\ell}^{-\nu\ell} |F(u)| e^{-8u}\,du \le C e^{a\nu\ell}$ on a thick set $G \subseteq \mathbb{N}$ contradicts `not_forall_mem_thick_norm_levelSum_le`.

If $E \subseteq \mathbb{R}$ is thick toward $-\infty$ (`∀ L M, 0 < L → ∃ T ≥ M, [-T - L, -T] ⊆ E`), then $G := \{\nu \in \mathbb{N} : [-(\nu+1)\ell, -\nu\ell] ⊆ E\}$ is `Thick` in $\mathbb{N}$ (taking $T \ge \max(0, (N+1)\ell)$ for length $(K+2)\ell$ and $M := \lceil T/\ell \rceil$). On $[-(\nu+1)\ell, -\nu\ell] \subseteq E$, $|F(u)e^{-8u}| \le C e^{-au}$ a.e. gives $\int_{-(\nu+1)\ell}^{-\nu\ell} |F(u)| e^{-8u}\,du \le (\ell C e^{a\ell}) e^{a\nu\ell}$, yielding AAL.

### 4. Heated zero series / weighted lag transfer
For general summable weights $b : \text{XiZeroCopy} \to \mathbb{C}$, if every isolated top has a point with nonzero merged weight at base $\ell > 0$, subexponential growth of `levelSum (frobTower ℓ zetaConfig) b` along a thick set implies AAL (`asymptoticAbscissaLaw_of_thick_weighted_tower_bound`).
For the heated zero weights $b_q(\varepsilon) := \mathcal{L}F(z_q) e^{\varepsilon z_q^2}$ at **any** base $\ell > 0$: in the fiber $S := \{j \in F_{\text{top}} : e^{\ell z_j} = e^{\ell z_{q_0}}\}$, choose $q_* \in S$ minimizing $|\operatorname{Im} z_j|$ and set $\sigma := \Theta - 1/2 > 0$, $\gamma := |\operatorname{Im} z_{q_*}|$.
- If $\gamma = 0$, every $j \in S$ with $|\operatorname{Im} z_j| = 0$ has $z_j = \sigma$; as $\varepsilon \to +\infty$, terms with $|\operatorname{Im} z_j| > 0$ decay like $e^{-\varepsilon (\operatorname{Im} z_j)^2}$ relative to $e^{\varepsilon \sigma^2}$, so the merged weight is nonzero for large $\varepsilon$.
- If $\gamma > 0$, let $A_\pm := \#\{j \in S : z_j = \sigma \pm i\gamma\} \cdot \mathcal{L}F(\sigma \pm i\gamma)$. Since at least one count is $\ge 1$ and $\mathcal{L}F(\sigma \pm i\gamma) \ne 0$, $(A_+, A_-) \ne (0,0)$, so $\max(\|A_+ + A_-\|, \|A_+ - A_-\|) > 0$. Evaluating at $2\varepsilon\sigma\gamma = 2\pi k$ (where $e^{\pm 2i\varepsilon\sigma\gamma} = 1$) or $2\varepsilon\sigma\gamma = 2\pi k + \pi/2$ (where $e^{\pm 2i\varepsilon\sigma\gamma} = \pm i$) for $k \in \mathbb{N}$ sufficiently large dominates all $|\operatorname{Im} z_j| > \gamma$ terms and produces $\varepsilon > 0$ with nonzero merged weight.
Combined with `criticalState_heatedState_add_zeroSeries_le` ($|\text{heatedState}\,\varepsilon\,F\,(-\nu\ell) + a^{-1}\text{levelSum}\,b(\varepsilon)\,\nu| \le \|F^+ e^{-x}\|_2 k_\varepsilon(-\nu\ell) = O(1)$ for $\nu\ell \ge 4\varepsilon$), subexponential bounds on `heatedState ε F (-ν * ℓ)` along thick sets for all $\varepsilon > 0$ imply AAL.

### 5. Corollaries
1. **Syndetic excursion law under $\neg\text{AAL}$:** Unconditionally, $\neg\text{AAL}$ implies $\neg\text{RH}$, hence a critical state $(W_0, F)$ exists and there exist $k \ge 1$ and $a > 0$ such that at every $\ell > 0$, $\int_{-(\nu+1)\ell}^{-\nu\ell} |F(u)|e^{-8u}\,du > C e^{a\nu\ell}$ syndetically in windows of length $k$.
2. **Boundedness exclusion under ZAL / `FiniteOffLine`:** If `ZerosApproachLine` (or `FiniteOffLine`) holds, no critical state can have $\int_{-(\nu+1)\ell}^{-\nu\ell} |F(u)|e^{-8u}\,du \le C$ on a thick set (at $a = 0$ the same tower argument eliminates every right zero, giving `RiemannHypothesis`, contradicting `windowThreshold < ⊤`).
