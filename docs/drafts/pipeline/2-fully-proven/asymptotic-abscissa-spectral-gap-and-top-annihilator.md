# Asymptotic Zero Abscissa, Bilateral Spectral-Gap Structure of One-Off Zeros, and Single-Prime Top-Layer Annihilators

- **Status:** `2-fully-proven`
- **Target subfolder:** `formal/GaloisForLFunctions/ZeroConfigurationGeometry/AsymptoticAbscissaSpectralGapAndTopAnnihilator.lean`

## Theorem Statements

1. **Asymptotic Zero Abscissa and `limsup = sup` Equivalence (`zetaAsymptoticAbscissa`, `asymptoticAbscissaLaw_iff_zetaAsymptoticAbscissa_eq_zetaZeroAbscissa`):**
   Define the asymptotic zero abscissa
   $$\Theta_\infty := \inf_{T > 0} \sup \left\{ \operatorname{Re}\rho \;\middle|\; \rho \in \Xi,\; |\operatorname{Im}\rho| \ge T \right\} = \inf \left\{ \sigma \ge \tfrac{1}{2} \;\middle|\; \{q \in \text{XiZeroCopy} : \sigma < \operatorname{Re} q\}. \text{Finite} \right\}.$$
   Unconditionally:
   - $\frac{1}{2} \le \Theta_\infty \le \Theta \le 1$, where $\Theta = \text{zetaZeroAbscissa}$;
   - $\text{ZerosApproachLine} \iff \Theta_\infty = \frac{1}{2}$;
   - $\text{AsymptoticAbscissaLaw} \iff \Theta_\infty = \Theta \iff \Theta_\infty - \frac{1}{2} = \Theta - \frac{1}{2}$.

2. **Exact Bilateral Isolated Spectral-Gap Characterization of `¬ AsymptoticAbscissaLaw` (`not_asymptoticAbscissaLaw_iff_bilateral_spectralGap`):**
   `¬ AsymptoticAbscissaLaw` holds if and only if there exist $\beta_1, \beta_*, T_* \in \mathbb{R}$ with $\frac{1}{2} \le \beta_1 < \beta_* < 1$ and $T_* > 0$ such that:
   - $\zeta(s) \ne 0$ for all $\operatorname{Re} s > \beta_*$ and for all $0 < \operatorname{Re} s < 1 - \beta_*$;
   - the top zero layer $F_* = \{\rho \in \mathbb{C} : \zeta(\rho) = 0,\ \operatorname{Re}\rho = \beta_*\}$ and reflected bottom layer $\widetilde{F}_* = \{\rho \in \mathbb{C} : \zeta(\rho) = 0,\ \operatorname{Re}\rho = 1 - \beta_*\}$ are finite, nonempty, conjugate-symmetric, mapped bijectively onto one another by $s \mapsto 1 - s$ and $s \mapsto 1 - \bar{s}$, and satisfy $|\operatorname{Im}\rho| \le T_*$;
   - $\zeta(s) \ne 0$ everywhere on both global open vertical spectral-gap strips $\beta_1 < \operatorname{Re} s < \beta_*$ and $1 - \beta_* < \operatorname{Re} s < 1 - \beta_1$;
   - every strip zero $\rho \in \{0 < \operatorname{Re} s < 1\} \setminus (F_* \cup \widetilde{F}_*)$ (in particular every strip zero with $|\operatorname{Im}\rho| > T_*$) satisfies $1 - \beta_1 \le \operatorname{Re}\rho \le \beta_1$.

3. **Single-Base Euler Top-Layer Annihilator Separating $F_*$ from $\operatorname{Re} s \le \frac{1}{2}$ (`singleBaseTopAnnihilator`, `singleBaseTopAnnihilator_eq_zero_of_mem`, `norm_singleBaseTopAnnihilator_ge_of_re_le_half`, `singleBaseTopAnnihilator_ne_zero_of_re_le_half`):**
   For any real base $b > 1$, finite set $F \subset \{\rho \in \mathbb{C} : \frac{1}{2} < \operatorname{Re}\rho\}$, and multiplicity map $m : \mathbb{C} \to \mathbb{N}$, the finite single-base Euler-type Dirichlet polynomial
   $$D_{b, F, m}(s) := \prod_{\rho \in F} \left(1 - b^{\rho - s}\right)^{m(\rho)}$$
   vanishes at every $\rho \in F$ with $m(\rho) \ge 1$, while for every $s \in \mathbb{C}$ with $\operatorname{Re} s \le \frac{1}{2}$ (in particular at every reflected zero $1 - \rho$ and $1 - \bar{\rho}$ for $\rho \in F$),
   $$\left|D_{b, F, m}(s)\right| \ge \prod_{\rho \in F} \left(b^{\operatorname{Re}\rho - \operatorname{Re} s} - 1\right)^{m(\rho)} > 0.$$

4. **Finite-Blaschke Twisted Functional Equation (`finiteRightBlaschke`, `norm_finiteRightBlaschke_criticalLine`, `finiteRightBlaschke_one_sub_mul_conjSymm`):**
   For any conjugate-symmetric finite set $F \subset \{\rho \in \mathbb{C} : \frac{1}{2} < \operatorname{Re}\rho\}$ and multiplicity map $m : \mathbb{C} \to \mathbb{N}$ with $m(\bar{\rho}) = m(\rho)$, the right-half-plane Blaschke product
   $$B_{F, m}(s) := \prod_{\rho \in F} \left(\frac{s - \rho}{s - (1 - \bar{\rho})}\right)^{m(\rho)}$$
   satisfies $|B_{F, m}(\frac{1}{2} + it)| = 1$ for all $t \in \mathbb{R}$ and the reflection reciprocity $B_{F, m}(1 - s) \cdot B_{F, m}(s) = 1$ off $F \cup (1 - F)$, so dividing any $s \leftrightarrow 1 - s$ symmetric function $\Xi(s)$ by $B_{F, m}(s)$ twists its functional equation by the nonconstant phase $B_{F, m}(s)^2$ on $\operatorname{Re} s = \frac{1}{2}$.

## Proof Outline

1. The cofinite-finiteness set $S_\infty = \{\sigma \in \mathbb{R} : \frac{1}{2} \le \sigma \wedge \{q \in \text{XiZeroCopy} : \sigma < \operatorname{Re} q\}.\text{Finite}\}$ contains $1$ (empty set) and is bounded below by $\frac{1}{2}$. Since bounded-ordinate subsets of `XiZeroCopy` are finite (`xiZeroBall`), $\{q : \sigma < \operatorname{Re} q\}$ is finite iff $\exists T > 0$ above which $\operatorname{Re} q \le \sigma$. Under `AsymptoticAbscissaLaw`, every $\sigma = \frac{1}{2} + h \in S_\infty$ bounds all zeros (`\Theta \le \sigma`), giving $\Theta \le \Theta_\infty \le \Theta$. Conversely, if $\Theta_\infty = \Theta$ and $\{q : \frac{1}{2} + h < \operatorname{Re} q\}$ is finite ($h \ge 0$), then $\Theta = \Theta_\infty \le \frac{1}{2} + h$, bounding all zeros.
2. If `AsymptoticAbscissaLaw` fails, $\Theta_\infty < \Theta$. Taking $h_0 = (\Theta + \Theta_\infty)/2 - \frac{1}{2} > 0$, $\{q : \frac{1}{2} + h_0 < \operatorname{Re} q\}$ is finite and nonempty, so it attains both its maximum $\beta_* = \Theta > \frac{1}{2} + h_0$ on a nonempty finite top layer $F_*$ and a strict gap above $\beta_1 := \max(\frac{1}{2} + h_0, \max\{\operatorname{Re} q : \frac{1}{2} + h_0 < \operatorname{Re} q,\ \operatorname{Re} q < \beta_*\}) < \beta_*$. Functional-equation and conjugation symmetries of $\zeta$ produce the reflected bottom layer $\widetilde{F}_*$ at $1 - \beta_*$ and the symmetric gap strip $(1 - \beta_*, 1 - \beta_1)$. Conversely, the existence of such $(\beta_1, \beta_*)$ gives finiteness of $\{q : \frac{1}{2} + (\beta_1 - \frac{1}{2}) < \operatorname{Re} q\}$ while $F_* \ne \emptyset$ violates $\operatorname{Re} q \le \beta_1$.
3. For $\rho \in F$ and $\operatorname{Re} s \le \frac{1}{2} < \operatorname{Re}\rho$, $\|b^{\rho - s}\| = b^{\operatorname{Re}\rho - \operatorname{Re} s} > 1$, so $\|1 - b^{\rho - s}\| \ge \|b^{\rho - s}\| - 1 = b^{\operatorname{Re}\rho - \operatorname{Re} s} - 1 > 0$.
4. On $s = \frac{1}{2} + it$, $s - (1 - \bar{\rho}) = -(\overline{s - \rho})$, so $|s - \rho| = |s - (1 - \bar{\rho})| > 0$. Under $s \mapsto 1 - s$ and the involution $\rho \mapsto \bar{\rho}$ on $F$, $(1 - s - \rho) / (1 - s - (1 - \bar{\rho})) = (s - (1 - \rho)) / (s - \bar{\rho})$, whose product over conjugate pairs cancels $(s - \rho)/(s - (1 - \bar{\rho}))$ to $1$.
