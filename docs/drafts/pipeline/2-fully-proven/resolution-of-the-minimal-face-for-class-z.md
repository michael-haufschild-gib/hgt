# Resolution of the minimal face for the class `𝒵`

## Metadata
- **Date**: 2026-11-10
- **Status**: 2-fully-proven
- **Author**: Agent
- **Target**: `formal/GaloisForLFunctions/SurfaceOfSpecZ/ScaleLocality/`
- **Obstacle Reference**: B143 (`docs/reports/review-1011/obstacles-summary.md`, §3)

## Mathematical Statement

Let $\mathcal{Z}(\gamma_{\min}, C)$ be the class of tempered reflection-symmetric zero configurations $Z$ in $0 < \operatorname{Re} s < 1$ without real zeros, with lowest ordinate $|\operatorname{Im} \rho| \ge \gamma_{\min} > 0$ for all $\rho \in Z$ and unit-window local counts $N_Z(t, t+1] \le C \log(|t| + 3)$ for all $t \in \mathbb{R}$.

1. **Unbounded sub-logarithmic windows do not decide $\mathcal{Z}$ (Resolution of Question B143.2).**
   For every $\gamma_{\min} > 0$, $C > 0$, and $0 < \Theta \le 1/2$, there exist a zero configuration $Z \in \mathcal{Z}(\gamma_{\min}, C)$ of simple zeros ($\text{mult} \equiv 1$) with unattained accumulating top $\sup_{\rho \in Z} \operatorname{Re} \rho = 1/2 + \Theta$ ($\operatorname{Re} \rho < 1/2 + \Theta$ for all $\rho \in Z$) and a monotone window radius function $R : \mathbb{R} \to \mathbb{R}$ satisfying
   $$\lim_{T \to \infty} R(T) = +\infty, \qquad \lim_{T \to \infty} \frac{R(T)}{\log T} = 0$$
   such that $2 \operatorname{Re} S_Z(u)$ is bounded below beyond every bound on arbitrarily late windows of radius $R(T)$:
   $$\forall K, U \in \mathbb{R}, \quad \exists T \ge U, \quad \forall u \in [T - R(T), T + R(T)], \quad 2 \operatorname{Re} S_Z(u) \ge K.$$

2. **Bounded windows do not decide $\mathcal{Z}$ (Resolution of Question B143.1).**
   For every $\gamma_{\min} > 0$, $C > 0$, $0 < \Theta \le 1/2$, and $L > 0$, the same configuration $Z \in \mathcal{Z}(\gamma_{\min}, C)$ satisfies
   $$\forall K, U \in \mathbb{R}, \quad \exists u_0 \ge U, \quad \forall u \in [u_0, u_0 + L], \quad 2 \operatorname{Re} S_Z(u) \ge K.$$
   In particular, no bounded window length $L = L(\gamma_{\min}, C)$ decides $\mathcal{Z}(\gamma_{\min}, C)$.

3. **Prime-window corollaries and positive logarithmic-square detection for $\mathcal{Z}$.**
   - Restricting $u = \log p$ to primes $p$, the configuration $Z \in \mathcal{Z}(\gamma_{\min}, C)$ satisfies $2 \operatorname{Re} S_Z(\log p) \ge K$ on arbitrarily late prime windows $|\log p - T| \le R(T)$ of unbounded sub-logarithmic radius $R(T) = o(\log T)$, and on arbitrarily late bounded prime windows $\log p \in [u_0, u_0 + L]$, while having off-line zeros accumulating at $1/2 + \Theta$ (and at $\operatorname{Re} s = 1$ when $\Theta = 1/2$).
   - Conversely, for every $\gamma_{\min} > 0$ and $C > 0$, there is an explicit constant $R_0(\gamma_{\min}, C) > 0$ such that windows of radius $R_0(\gamma_{\min}, C) (\log(T+2))^2$ (and prime windows of radius $2 R_0(\gamma_{\min}, C) (\log(T+2))^2$) decide every configuration $Z \in \mathcal{Z}(\gamma_{\min}, C)$ in full width form.

## Proof

### 1. High-frequency binomial polynomials on a short arc

For any integer $m_0 \ge 1$ and $z \in \mathbb{C}$, expanding $1 = (z + (1 - z))^{2 m_0}$ by the binomial theorem and splitting at $m_0$ gives
$$P_{m_0}(z) := \sum_{m = m_0}^{2 m_0} \binom{2 m_0}{m} z^m (1 - z)^{2 m_0 - m} = 1 - \sum_{m = 0}^{m_0 - 1} \binom{2 m_0}{m} z^m (1 - z)^{2 m_0 - m}.$$
When $\|z\| = 1$ and $\|1 - z\| \le 1/4$, each term in the remainder has $2 m_0 - m \ge m_0 + 1$, so $\|1 - z\|^{2 m_0 - m} \le (1/4)^{m_0 + 1}$. Using $\sum_{m=0}^{m_0 - 1} \binom{2 m_0}{m} \le 2^{2 m_0} = 4^{m_0}$, we obtain
$$\left\|1 - P_{m_0}(z)\right\| \le 4^{m_0} \left(\frac{1}{4}\right)^{m_0 + 1} = \frac{1}{4}, \qquad \operatorname{Re} P_{m_0}(z) \ge \frac{3}{4}.$$
Expanding $(1 - z)^{2 m_0 - m} = \sum_{d = m}^{2 m_0} (-1)^{d - m} \binom{2 m_0 - m}{d - m} z^{d - m}$ and exchanging the finite triangular sum over $m_0 \le m \le d \le 2 m_0$ yields the monomial representation
$$P_{m_0}(z) = \sum_{d = m_0}^{2 m_0} a(m_0, d) z^d, \qquad a(m_0, d) := \sum_{m = m_0}^d (-1)^{d - m} \binom{2 m_0}{m} \binom{2 m_0 - m}{d - m} \in \mathbb{Z},$$
with coefficient bound $|a(m_0, d)| \le 64^{m_0}$ for all $d \in [m_0, 2 m_0]$. For $v \in [-R, R]$ and step $\delta = 1/(4R)$, the angle $\theta = \delta v$ satisfies $|\theta| \le 1/4$, hence $\|1 - e^{i \delta v}\| \le |\delta v| \le 1/4$ and
$$\sum_{d = m_0}^{2 m_0} a(m_0, d) \cos(d \delta v) = \operatorname{Re} P_{m_0}(e^{i \delta v}) \ge \frac{3}{4}.$$

### 2. Phase-split simple-zero clusters at prescribed window centers

At tower level $k \in \mathbb{N}$, set the depth $x_k = \Theta(1 - 2^{-k-1}) \in (0, \Theta)$ and window radius $R_k = k + 1 \ge 1$, with step $\delta_k = 1 / (4(k + 1))$. For an integer base ordinate $\Gamma_k \ge 4$, set $m_0(k) = 4(k + 1)\Gamma_k \in \mathbb{N}$. For each harmonic $d \in [m_0(k), 2 m_0(k)]$, the unperturbed ordinate $\gamma_d = d \delta_k$ lies in $[\Gamma_k, 2 \Gamma_k]$.

At $\gamma_d - i x_k$, the cubic-spline Fourier weight is $w_{k, d} = \operatorname{sinc}(\gamma_d - i x_k)^8 = r_{k, d} e^{i \phi_{k, d}}$, where $\phi_{k, d} = \arg w_{k, d}$ and
$$\left(\frac{x_k}{7 \Gamma_k}\right)^8 =: r_{\min}(k) \le r_{k, d} \le \frac{1}{\Gamma_k^8}.$$
Define the normalized amplitude ratio
$$b_{k, d} := \frac{|a(m_0(k), d)|}{64^{m_0(k)}} \cdot \frac{r_{\min}(k)}{r_{k, d}} \in [0, 1], \qquad \alpha_{k, d} := \arccos(b_{k, d}) \in [0, \pi/2],$$
and sign angle $\theta_{k, d} = 0$ if $a(m_0(k), d) \ge 0$ and $\theta_{k, d} = \pi$ if $a(m_0(k), d) < 0$. Then
$$w_{k, d} \left(e^{i(\theta_{k, d} - \phi_{k, d} + \alpha_{k, d})} + e^{i(\theta_{k, d} - \phi_{k, d} - \alpha_{k, d})}\right) = r_{k, d} \cdot 2 \cos(\alpha_{k, d}) e^{i \theta_{k, d}} = \frac{2 r_{\min}(k)}{64^{m_0(k)}} a(m_0(k), d).$$

Given a window center $T_k > 0$, for any frequency $\gamma$, target phase $\psi$, and slot $s \in \{1, 3\}$, the perturbed ordinate
$$\tilde{\gamma}(\gamma, \psi, s, T_k) := \gamma + \eta(\gamma, \psi, s, T_k), \qquad \eta(\gamma, \psi, s, T_k) := \frac{2\pi \left(\lfloor (\gamma T_k - \psi)/(2\pi) \rfloor + s + 1\right) + \psi - \gamma T_k}{T_k}$$
satisfies $\frac{2\pi s}{T_k} < \eta \le \frac{2\pi(s + 1)}{T_k} \le \frac{26}{T_k}$ and $e^{i \tilde{\gamma} T_k} = e^{i \psi}$ identically. Placing two simple zeros at $\gamma_{k, d}^+ = \tilde{\gamma}(\gamma_d, \theta_{k, d} - \phi_{k, d} + \alpha_{k, d}, 1, T_k)$ and $\gamma_{k, d}^- = \tilde{\gamma}(\gamma_d, \theta_{k, d} - \phi_{k, d} - \alpha_{k, d}, 3, T_k)$ (together with their functional-equation reflections at $1/2 - x_k$) keeps $\gamma_d < \gamma_{k, d}^+ < \gamma_{k, d}^- < \gamma_d + \delta_k$ whenever $T_k > 26 / \delta_k$.

For $u = T_k + v$ with $|v| \le R_k$, the trigonometric identity $\sin z_1 - \sin z_2 = 2 \sin(\eta/2) \cos((z_1 + z_2)/2)$ gives $\|\operatorname{sinc}(\tilde{\gamma} - i x_k)^8 - \operatorname{sinc}(\gamma_d - i x_k)^8\| \le 16 \eta$ and $\|e^{i \tilde{\gamma} v} - e^{i \gamma_d v}\| \le \eta R_k$, so each perturbed mode differs from its ideal term by at most $(R_k + 16)\eta \le 26(R_k + 16)/T_k$. Summing over $d \in [m_0(k), 2 m_0(k)]$ shows that once $T_k \ge 104 (m_0(k) + 1)(R_k + 16) 64^{m_0(k)} / r_{\min}(k)$, the level-$k$ main trace on $[T_k - R_k, T_k + R_k]$ satisfies
$$\text{clusterMain}_k(u) \ge \frac{2 r_{\min}(k)}{64^{m_0(k)}} > 0.$$

### 3. Mutual tower recursion, local zero counts, and sub-logarithmic radius

Choose $(\Gamma_k, T_k)$ recursively:
- $\Gamma_k \ge \max(\lceil \gamma_{\min} \rceil + 4, 2 \Gamma_{k-1} + 10, \lceil \exp((16 k + 24)/C) \rceil)$ and $\Gamma_k$ large enough that the level-$k$ weight ceiling $w_k := 8(m_0(k) + 1) / \Gamma_k^8 = 8(4(k+1)\Gamma_k + 1)/\Gamma_k^8$ satisfies $w_k \le 2^{-k} \exp(-\Theta(T_{k-1} + R_{k-1}))$.
- $T_k$ large enough that $T_k \ge T_{k-1} + R_{k-1} + R_k + 4$, $T_k \ge \exp((k + 1)^2)$, the perturbation error bound holds, and $\frac{2 r_{\min}(k)}{64^{m_0(k)}} e^{(x_k - x_{k-1})(T_k - R_k)} \ge k + 10 + 8 e^{2 \Theta R_k}$.

Then:
- Every zero has multiplicity $1$ and ordinate $\ge \Gamma_0 \ge \gamma_{\min} > 0$.
- The ordinate bands $(\Gamma_k, 2 \Gamma_k + 1)$ of distinct levels are separated by at least $9 > 1$. Any unit window $(t, t + 1]$ meets at most one level $k$ (forcing $|t| + 3 > \Gamma_k + 2$) and at most $4(k + 1) + 2$ values of $d$, hence contains at most $4(4(k + 1) + 2) = 16 k + 24 \le C \log(\Gamma_k + 2) \le C \log(|t| + 3)$ zeros.
- On $[T_k - R_k, T_k + R_k]$, levels $j < k$ have total magnitude at most $4 e^{x_{k-1}(T_k + R_k)}$, the reflected sum and levels $j > k$ have total magnitude at most $5$, and level $k$ contributes at least $\frac{2 r_{\min}(k)}{64^{m_0(k)}} e^{x_k(T_k - R_k)}$, giving $2 \operatorname{Re} S_Z(u) \ge k$.
- Defining $R(T) := k + 1$ for $T \in [T_k, T_{k+1})$ (and $R(T) = 1$ for $T < T_1$) gives a monotone function with $R(T_k) = R_k = k + 1 \to \infty$ and $0 < R(T) \le \sqrt{\log T}$ for $T \ge T_1$, so $R(T) / \log T \to 0$.
