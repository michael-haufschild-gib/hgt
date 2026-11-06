# Asymptotic zero abscissa, bilateral spectral-gap structure of one-off zeros, and single-base top-layer annihilators

- **ID:** asymptotic-abscissa-spectral-gap-and-top-annihilator
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Define the asymptotic zero abscissa $\Theta_\infty := \inf\{\sigma \ge \frac{1}{2} : \{q \in \mathrm{XiZeroCopy} : \sigma < \operatorname{Re} q\}.\mathrm{Finite}\}$. Unconditionally $\frac{1}{2} \le \Theta_\infty \le \Theta \le 1$, `ZerosApproachLine ↔ Θ_∞ = 1/2`, and `AsymptoticAbscissaLaw ↔ Θ_∞ = Θ`; `¬ AsymptoticAbscissaLaw` holds iff $\zeta$ has nonempty finite conjugate-symmetric top and reflected bottom zero layers at $\beta_* \in (\frac{1}{2}, 1)$ and $1 - \beta_*$ isolated by global zero-free strips $(\beta_1, \beta_*)$ and $(1 - \beta_*, 1 - \beta_1)$; any finite off-line layer $F \subset \{\operatorname{Re}\rho > \frac{1}{2}\}$ is annihilated by a single-base Euler polynomial $D_{b,F,m}(s)$ strictly bounded away from $0$ on $\operatorname{Re} s \le \frac{1}{2}$, while dividing by its unimodular right-half-plane Blaschke product $B_{F,m}(s)$ twists $s \leftrightarrow 1 - s$ symmetry by $B_{F,m}(s)^2$.

## Paper proof

1. **Asymptotic abscissa and `limsup = sup`.** The cofinite-finiteness set $S_\infty = \{\sigma \ge \frac{1}{2} : \{q \in \mathrm{XiZeroCopy} : \sigma < \operatorname{Re} q\}.\mathrm{Finite}\}$ contains $1$ and is bounded below by $\frac{1}{2}$. By bounded-ordinate finiteness (`xiZeroBall`), $\sigma \in S_\infty$ iff $\sigma \ge \frac{1}{2}$ and $\exists T > 0$ above which $\operatorname{Re} q \le \sigma$. Under `AsymptoticAbscissaLaw`, every $\sigma = \frac{1}{2} + h \in S_\infty$ bounds all zeros ($\Theta \le \sigma$), giving $\Theta_\infty = \Theta$; conversely $\Theta_\infty = \Theta$ directly gives `AsymptoticAbscissaLaw`.

2. **Bilateral isolated spectral-gap characterization.** If `AsymptoticAbscissaLaw` fails, $\Theta_\infty < \Theta$, so choosing $\sigma_0 \in S_\infty$ with $\sigma_0 < \Theta$ makes $E_0 = \{q : \sigma_0 < \operatorname{Re} q\}$ finite and nonempty. Taking its maximum $\beta_* = \Theta < 1$ and next-largest abscissa $\beta_1 < \beta_*$ ($\beta_1 \ge \frac{1}{2}$), functional-equation and conjugation symmetries of $\zeta$ isolate the finite nonempty layers at $\beta_*$ and $1 - \beta_*$ behind the zero-free vertical strips $(\beta_1, \beta_*)$ and $(1 - \beta_*, 1 - \beta_1)$. Conversely, any such triple $(\beta_1, \beta_*, T_*)$ places $\{q : \frac{1}{2} + (\beta_1 - \frac{1}{2}) < \operatorname{Re} q\}$ inside `xiZeroBall ⌈T_* + 1⌉₊` while the nonempty top layer violates $\operatorname{Re} q \le \beta_1$.

3. **Single-base top-layer annihilator and Blaschke twist.** For $b > 1$, $\rho \in F$ ($\operatorname{Re}\rho > \frac{1}{2}$), and $\operatorname{Re} s \le \frac{1}{2}$, $\|1 - b^{\rho - s}\| \ge b^{\operatorname{Re}\rho - \operatorname{Re} s} - 1 > 0$. On $\operatorname{Re} s = \frac{1}{2}$, $s - (1 - \bar{\rho}) = -\overline{(s - \rho)}$, so $|B_{F,m}(s)| = 1$; for conjugate-symmetric $(F, m)$, reindexing $\rho \mapsto \bar{\rho}$ gives $B_{F,m}(1 - s) B_{F,m}(s) = 1$ and $\Xi(1 - s)/B_{F,m}(1 - s) = B_{F,m}(s)^2 (\Xi(s)/B_{F,m}(s))$.

## Lean

Module `formal/GaloisForLFunctions/ZeroConfigurationGeometry/AsymptoticAbscissaSpectralGapAndTopAnnihilator.lean` (wired in `ZeroConfigurationGeometry.lean`):
- `zetaAsymptoticAbscissaSet`, `zetaAsymptoticAbscissa`
- `mem_zetaAsymptoticAbscissaSet_iff_eventually_height`
- `half_le_zetaAsymptoticAbscissa`
- `zetaAsymptoticAbscissa_le_zetaZeroAbscissa`
- `zetaAsymptoticAbscissa_le_one`
- `zerosApproachLine_iff_zetaAsymptoticAbscissa_eq_half`
- `asymptoticAbscissaLaw_iff_zetaAsymptoticAbscissa_eq_zetaZeroAbscissa`
- `asymptoticAbscissaLaw_iff_zetaAsymptoticAbscissa_sub_half_eq`
- `zetaVerticalZeroLayer`
- `not_asymptoticAbscissaLaw_iff_bilateral_spectralGap`
- `singleBaseTopAnnihilator`
- `singleBaseTopAnnihilator_eq_zero_of_mem`
- `norm_singleBaseTopAnnihilator_ge_of_re_le_half`
- `singleBaseTopAnnihilator_ne_zero_of_re_le_half`
- `singleBaseTopAnnihilator_reflected_ne_zero`
- `finiteRightBlaschke`
- `norm_finiteRightBlaschke_criticalLine`
- `finiteRightBlaschke_one_sub_mul_conjSymm`
- `twisted_functionalEquation_div_finiteRightBlaschke`

## Gates
- [x] 0 → 1
- [x] 1 → 2
- [x] 2 → 3  compiles with `lake --old env lean`
