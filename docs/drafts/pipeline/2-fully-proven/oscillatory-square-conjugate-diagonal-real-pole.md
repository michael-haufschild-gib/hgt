# Exponential-Floor Real-Pole Shielding and Conjugate-Diagonal Real-Pole Creation for Oscillatory Waves

- **Status:** `2-fully-proven`
- **Target subfolder:** `formal/GaloisForLFunctions/ConjugateDiagonalGeometry/OscillatorySquareConjugateDiagonalRealPole.lean`

## Theorem Statements

1. **Exponential-Floor Real-Pole Shielding (`expBufferedWave_nonneg`, `laplace_expBufferedWave_eq`):**
   Let $F$ be a finite index set, $c : F \to \mathbb{C}$, $\gamma : F \to \mathbb{R}$, $\beta, \alpha, C \in \mathbb{R}$ with $\beta \le \alpha$ and $2 \sum_{j \in F} \|c_j\| \le C$. Then the real oscillatory wave
   $$W(u) := \sum_{j \in F} 2\,\operatorname{Re}\!\left(c_j e^{(\beta + i\gamma_j)u}\right)$$
   satisfies $C e^{\alpha u} + W(u) \ge 0$ for all $u \ge 0$, and for every $s \in \mathbb{C}$ with $\operatorname{Re} s > \alpha$,
   $$\int_0^\infty e^{-su}\left(C e^{\alpha u} + W(u)\right) du = \frac{C}{s - \alpha} + \sum_{j \in F} \left(\frac{c_j}{s - (\beta + i\gamma_j)} + \frac{\bar{c}_j}{s - (\beta - i\gamma_j)}\right).$$
   In particular, when $C > 0$, $(s - \alpha) \int_0^\infty e^{-su}(C e^{\alpha u} + W(u))\,du \to C > 0$ as $s \to \alpha$ ($\operatorname{Re} s > \alpha$) provided $\gamma_j \ne 0$ whenever $\beta = \alpha$, shielding the off-axis poles $\beta \pm i\gamma_j$ behind a strictly positive real pole at $s = \alpha$.

2. **Conjugate-Diagonal Real-Pole Creation under Squaring (`oscillatoryWave_laplace_analytic_at_real`, `oscillatoryWave_sq_decomposition`, `laplace_oscillatoryWave_sq_eq`, `tendsto_sub_mul_laplace_oscillatoryWave_sq`):**
   Let $F$ be a finite set, $c : F \to \mathbb{C}$, $\beta_* \in \mathbb{R}$, and $\gamma : F \to \mathbb{R}$ injective with $0 < \gamma_j$ for all $j \in F$. For $W(u) := \sum_{j \in F} (c_j e^{(\beta_* + i\gamma_j)u} + \bar{c}_j e^{(\beta_* - i\gamma_j)u})$:
   - The rational Laplace continuation $L_W(s) := \sum_{j \in F} \left(\frac{c_j}{s - (\beta_* + i\gamma_j)} + \frac{\bar{c}_j}{s - (\beta_* - i\gamma_j)}\right)$ is analytic at the real abscissa $s = \beta_*$, with $(s - \beta_*) L_W(s) \to 0$ as $s \to \beta_*$;
   - Squaring $W(u)$ creates an exact conjugate-diagonal DC exponential plus purely nonreal off-diagonal frequencies:
     $$W(u)^2 = 2\left(\sum_{j \in F} \|c_j\|^2\right) e^{2\beta_* u} + \sum_{j \in F} \sum_{k \in F} \left(c_j c_k e^{(2\beta_* + i(\gamma_j + \gamma_k))u} + \bar{c}_j \bar{c}_k e^{(2\beta_* - i(\gamma_j + \gamma_k))u}\right) + \sum_{j \in F} \sum_{k \in F \setminus \{j\}} 2\,\operatorname{Re}\!\left(c_j \bar{c}_k e^{(2\beta_* + i(\gamma_j - \gamma_k))u}\right);$$
   - Every off-diagonal frequency $\pm(\gamma_j + \gamma_k)$ and $\pm(\gamma_j - \gamma_k)$ ($j \ne k$) is strictly nonzero, and for every $s \in \mathbb{C}$ with $\operatorname{Re} s > 2\beta_*$, the Laplace transform $\int_0^\infty e^{-su} W(u)^2\,du$ has a real simple pole at $s = 2\beta_*$ of exact residue
     $$\lim_{\substack{s \to 2\beta_* \\ \operatorname{Re} s > 2\beta_*}} (s - 2\beta_*) \int_0^\infty e^{-su} W(u)^2\,du = 2 \sum_{j \in F} \|c_j\|^2,$$
     which is strictly positive whenever $\exists j \in F,\ c_j \ne 0$.

## Proof Outline

1. For $u \ge 0$ and $\beta \le \alpha$, $|2\operatorname{Re}(c_j e^{(\beta + i\gamma_j)u})| \le 2\|c_j\| e^{\beta u} \le 2\|c_j\| e^{\alpha u}$, so $W(u) \ge -(2\sum \|c_j\|) e^{\alpha u} \ge -C e^{\alpha u}$. Each exponential $e^{(z - s)u}$ with $\operatorname{Re}(z - s) < 0$ integrates on $(0, \infty)$ to $\frac{1}{s - z}$.
2. Expanding $(\sum_{j \in F} (a_j + \bar{a}_j))^2 = \sum_{j, k} (a_j a_k + \bar{a}_j \bar{a}_k + a_j \bar{a}_k + \bar{a}_j a_k)$ with $a_j = c_j e^{(\beta_* + i\gamma_j)u}$ splits the $a_j \bar{a}_k + \bar{a}_j a_k$ sum into the diagonal $j = k$ ($2\|c_j\|^2 e^{2\beta_* u}$) and $j \ne k$ ($\gamma_j - \gamma_k \ne 0$ by injectivity of $\gamma$), while $\gamma_j + \gamma_k > 0$ for all $j, k$. Multiplying the rational Laplace sum by $(s - 2\beta_*)$ sends the diagonal term to $2\sum \|c_j\|^2$ and every nonreal pole term $\frac{s - 2\beta_*}{s - 2\beta_* \mp i\omega}$ ($\omega \ne 0$) to $0$ as $s \to 2\beta_*$.
