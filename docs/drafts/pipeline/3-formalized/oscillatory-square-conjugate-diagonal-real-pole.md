# Exponential-floor real-pole shielding and conjugate-diagonal real-pole creation for oscillatory waves

- **ID:** oscillatory-square-conjugate-diagonal-real-pole
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For a finite conjugate-symmetric oscillatory wave $W(u) = \sum_{j \in F} (c_j e^{(\beta + i\gamma_j)u} + \bar{c}_j e^{(\beta - i\gamma_j)u})$, adding an exponential floor $C e^{\alpha u}$ ($\beta \le \alpha$, $2\sum_{j \in F} \|c_j\| \le C$) ensures $C e^{\alpha u} + \operatorname{Re} W(u) \ge 0$ on $[0, \infty)$ and creates a real simple pole $C/(s - \alpha)$ of residue $C$ shielding $\beta \pm i\gamma_j$; while $L_W(s)$ itself has residue $0$ at $s = \beta$ when $\gamma_j \ne 0$, squaring $W(u)$ for distinct positive ordinates $\gamma_j > 0$ isolates the conjugate-diagonal term $2(\sum_{j \in F} \|c_j\|^2) e^{2\beta u}$ from purely nonreal off-diagonal frequencies $\pm(\gamma_j + \gamma_k)$ and $\pm(\gamma_j - \gamma_k)$ ($j \ne k$), giving $\int_0^\infty e^{-su} W(u)^2\,du$ a real simple pole at $s = 2\beta$ of residue $2\sum_{j \in F} \|c_j\|^2 > 0$.

## Paper proof

1. **Exponential-floor real-pole shielding.** For $u \ge 0$ and $\beta \le \alpha$, $|\operatorname{Re} W(u)| \le (2\sum_{j \in F} \|c_j\|) e^{\beta u} \le C e^{\alpha u}$, so $C e^{\alpha u} + \operatorname{Re} W(u) \ge 0$. Integrating against $e^{-su}$ on $(0, \infty)$ for $\operatorname{Re} s > \alpha$ gives $\frac{C}{s - \alpha} + L_W(s)$. When $\gamma_j \ne 0$ for $\beta = \alpha$, $L_W(s)$ is continuous at $s = \alpha$, so $(s - \alpha)(\frac{C}{s - \alpha} + L_W(s)) \to C$ as $s \to \alpha$ ($\operatorname{Re} s > \alpha$).

2. **Conjugate-diagonal real-pole creation under squaring.** Writing $W(u) = \sum_{j \in F} (a_j + b_j)$ with $a_j = c_j e^{(\beta + i\gamma_j)u}$ and $b_j = \bar{c}_j e^{(\beta - i\gamma_j)u}$, expanding $W(u)^2$ splits $\sum_{j,k} (a_j b_k + b_j a_k)$ into the diagonal $j = k$, equal to $2(\sum_{j \in F} \|c_j\|^2) e^{2\beta u}$, and $j \ne k$ with imaginary frequencies $\pm(\gamma_j - \gamma_k) \ne 0$ (by injectivity of $\gamma$ on $F$), while $\sum_{j,k} (a_j a_k + b_j b_k)$ has imaginary frequencies $\pm(\gamma_j + \gamma_k) \ne 0$ (since $\gamma_j > 0$). Hence the off-diagonal Laplace sum is continuous at $s = 2\beta$, and $(s - 2\beta)\int_0^\infty e^{-su} W(u)^2\,du \to 2\sum_{j \in F} \|c_j\|^2 > 0$ whenever $\exists j \in F,\ c_j \ne 0$.

## Lean

Module `formal/GaloisForLFunctions/ConjugateDiagonalGeometry/OscillatorySquareConjugateDiagonalRealPole.lean` (wired in `ConjugateDiagonalGeometry.lean`):
- `conjSymWave`, `conjSymWaveLaplace`, `conjSymWaveSqOffDiagLaplace`
- `expBufferedWave_nonneg`
- `laplace_conjSymWave_eq`
- `laplace_expBufferedWave_eq`
- `tendsto_sub_mul_laplace_expBufferedWave`
- `conjSymWaveLaplace_residue_zero`
- `conjSymWave_sq_eq`
- `laplace_conjSymWave_sq_eq`
- `tendsto_sub_mul_laplace_conjSymWave_sq`
- `conjDiagResidue_pos_of_exists_ne_zero`

## Gates
- [x] 0 → 1
- [x] 1 → 2
- [x] 2 → 3  compiles with `lake --old env lean`
