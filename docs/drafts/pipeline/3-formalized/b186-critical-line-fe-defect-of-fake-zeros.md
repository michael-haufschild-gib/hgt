# Critical-Line Functional-Equation Defect of Fake Zeros (Complete Solution to B186 & A151)

- **ID:** b186-critical-line-fe-defect-of-fake-zeros
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** docs/reports/review-1211/obstacles-summary.md §3 (B186, lines 664–695), §2.10 (lines 440–459), A151 (lines 169, 440, 458, 690)
- **Statement:** Every two-sided edit of the rational primes with count rate $\beta_c < 1$, Hamburger strip continuation to $\mathrm{Re}\,s \ge \frac{1}{2}$, and a fake zero in $\mathrm{Re}\,s > \frac{1}{2}$ has critical-line FE defect $g(t)$ unconditionally satisfying $\int_{\mathbb{R}} \|g(t)\|^2 e^{-|t|/T}\,dt \ge \frac{A^2}{256\pi p_0} T\log T$ and $\limsup_{|t|\to\infty} \|g(t)\|/\sqrt{\log |t|} \ge \frac{A}{32\sqrt{\pi p_0}} > 0$ (ruling out both $O(|t|^{-1/2+\varepsilon})$ for $\varepsilon < \frac{1}{2}$ and bounded $g$), while unconditionally either $\Theta = 1$ (`AsymptoticAbscissaLaw`) or $\Theta < 1$ and there exists a fake two-sided edit with $\frac{1}{2T}\int_{-T}^T \|g(t)\|^2\,dt = O_\varepsilon(T^\varepsilon)$ for all $\varepsilon > 0$ (infimal $L^2$-growth exponent $0$, strictly subpolynomial); for countable Beurling systems, unweighted real-norm systems (`RHTower.BeurlingSystem`) unconditionally admit no fake zero at $g = O(|t|^{-1/2+\varepsilon})$ ($\varepsilon < \frac{1}{2}$), whereas locally finite positive-real-weighted systems (`HTGeometry.Beurling.System`) unconditionally realize fake zeros with $\|g(t)\| \le \Phi(|t|)$ for any prescribed unbounded nondecreasing $\Phi$ without case-splitting on $\Theta$.

## Goal

Give the complete, unconditional mathematical resolution of Question **B186** (`obstacles-summary.md:676`) and its companion task **A151** (`obstacles-summary.md:690`), together with all unconditional corollaries for the World-I scenario table (`obstacles-summary.md:684–691`) and the layer–defect calculus (`obstacles-summary.md` §2.10), structured as dependency-closed paper proofs mapped directly to the Lean 4 corpus.

## Gates

- [x] 0 → 1  in-progress: exact corpus Hamburger-strip formulation fixed across all two-sided edit and countable real-weighted Beurling models
- [x] 1 → 2  fully-proven: complete unconditional paper proofs `[PROVED HERE]`, zero unproved premises, zero added axioms, zero numerical approximations
- [ ] 2 → 3  formalized: Lean 4 modules in §5 (`lake --old env lean` green, `#print axioms` clean)

## Approach

1. **Positive density & missing primes (`Theorem I.1`):** Combine `RHTower.landau_summability_transfer` with Euler-product nonvanishing to extend positive count density $A = 2\beta > 0$ from $\beta_c \le \frac{1}{2}$ to all $\beta_c < 1$, and combine with `infinite_missing_primes_of_integerNormFakeAt` to obtain a least deleted rational prime $p_0 \ge 2$ forcing $a_B(p_0 k) = 0$ for all $k \ge 1$.
2. **Sub-$L^2$ / Abel-sublinear impossibility (`Theorem I.2`):** Apply equal-abscissa radial residue cancellation between $\tau = \varepsilon + i$ ($a_B(1) = 1$) and $\tau = \varepsilon + i p_0$ ($a_B(p_0) = 0$) via `norm_defectLaplace_le` (`HamburgerStabilityCriticalLine.lean`) to prove a quantitative Abel-linear lower bound, ruling out all $g = O(|t|^{-1/2+\varepsilon})$ ($\varepsilon < \frac{1}{2}$) and all $g(t) = o(1)$.
3. **Unboundedness & logarithmic $L^2$ blowup (`Theorem I.3`):** Apply Mellin–Plancherel (`closedDefectLaplace_ray_energy`) along the tilted Stolz ray $\tau(r) = r e^{i(\frac{\pi}{2}-\theta)}$ across pairwise disjoint neighborhoods of $y = p_0 k \le \lfloor \theta^{-1/4}\rfloor$, where $i$-periodicity of $F_{a_B}$ produces $\asymp A/(p_0 k \theta)$ spikes while $a_B(p_0 k) = 0$ keeps the Poisson sum $L_{a_B}$ at $O(\log m + m^{\max(\beta_c, 0)})$.
4. **Unconditional frontier dichotomy & subpolynomial-$L^2$ fake edit (`Theorem I.4`):** Split unconditionally on $\Theta := \mathrm{zetaZeroAbscissa} = 1$ versus $\Theta < 1$. When $\Theta = 1$, `AsymptoticAbscissaLaw` holds unconditionally for $\zeta$. When $\Theta < 1$, discretize `posTruncatedZeta` on dyadic blocks via `HTGeometry.GroupedSelection.exists_selection` to build a two-sided edit with count rate $\beta_c \in (\beta_0, 1)$, fake zero pair $\{\rho_0, \bar\rho_0\}$, and $\|g(t)\| \le 2 K_\varepsilon |\zeta(\frac{1}{2}+2it)|(1+|t|)^\varepsilon$ for every $\varepsilon > 0$.
5. **Countable Beurling systems with real norms & real weights (`Theorems II.1–II.3`):**
   - For unweighted countable real-norm systems (`RHTower.BeurlingSystem`), extend `beurlingSystem_rigidity_of_finiteEnergy_defect` from $g \in L^2(\mathbb{R})$ to all $g = O(|t|^{-1/2+\varepsilon})$ ($\varepsilon < \frac{1}{2}$) by double integration by parts of `tentDefectKernel`, dyadic Mellin–Plancherel + Bohr almost-periodic intervals, and a finite Schauder hat decomposition of the origin Fejér tent.
   - For integer-norm real-weighted systems ($w_p \in \mathbb{R}$), rule out all Abel-sublinear defects ($A > 0$ and $A = 0$) while exhibiting an explicit 3-term signed real-weighted Euler product at $A = 0$ with bounded $g(t) = O(1)$.
   - For locally finite positive-real-weighted systems (`HTGeometry.Beurling.System`, $w_i > 0$, $A > 0$), apply Möbius prime-power inversion to `BeurlingOverRegularIntegers.primeDensity` and height-graded $\mathbb{Q}$-independent quadrature to construct, unconditionally without any case split on $\Theta$, a fake system with count rate $N_{P,w}(x) = A x + O(x^{4/5})$ and $\|g(t)\| \le \Phi(|t|)$ for any prescribed nondecreasing unbounded $\Phi$.

---

## 1. Exact Corpus Definitions & Complete Answer Matrix to B186

### Definition 1.1 (Hamburger Strip Continuation and Critical-Line FE Defect `g(t)`)

Let $\nu$ be a signed or positive Borel measure on $[1, \infty)$ with $\nu(\{1\}) = 1$ and $\int_{[1,\infty)} u^{-\sigma}\,d|\nu|(u) < \infty$ for all $\sigma > 1$, and write $\zeta_\nu(s) := \int_{[1,\infty)} u^{-s}\,d\nu(u)$ ($\mathrm{Re}\,s > 1$). Following `RHTower.HamburgerStability.coeff_eq_of_critical_line_even_sublinear_defect` (`formal/GaloisForLFunctions/RHTower/HamburgerStabilityCriticalLine.lean:736`) and `EulerFETransportTheory.beurlingSystem_rigidity_of_finiteEnergy_defect` (`formal/GaloisForLFunctions/EulerFETransportTheory/FiniteEnergyFunctionalEquationsDetermineThePrimes.lean:171`), $\zeta_\nu$ **continues to the critical line in the Hamburger strip class** with residue parameter $\beta \in \mathbb{C}$ and **critical-line FE defect** $g : \mathbb{R} \to \mathbb{C}$ if there exists $E : \mathbb{C} \to \mathbb{C}$ such that:

1. $E$ is continuous on `verticalStrip (1/2) (3/2)` $= \{s \in \mathbb{C} : \frac{1}{2} \le \mathrm{Re}\,s \le \frac{3}{2}\}$, holomorphic on $\{\frac{1}{2} < \mathrm{Re}\,s < \frac{3}{2}\}$, and satisfies $\|E(s)\| \le C / (1 + (\mathrm{Im}\,s)^2)$ on `verticalStrip (1/2) (3/2)`;
2. $\Gamma_{\mathbb{R}}(s)\,\zeta_\nu(s) = E(s) + \beta\,\Gamma_{\mathbb{R}}(s - 1)$ for all $s$ with $\mathrm{Re}\,s = \frac{3}{2}$, where $\Gamma_{\mathbb{R}}(s) := \pi^{-s/2}\Gamma(s/2)$;
3. For all $s$ with $\mathrm{Re}\,s = \frac{1}{2}$,
   $$E(s) - E(1 - s) = -\beta\bigl(\Gamma_{\mathbb{R}}(s - 1) - \Gamma_{\mathbb{R}}(-s)\bigr) + \Gamma_{\mathbb{R}}(s)\,g\!\left(\frac{\mathrm{Im}\,s}{2}\right),$$
   where $g$ is measurable and polynomially bounded ($\|g(t)\| \le C_g (1 + |t|)^{N_g}$).

### Lemma 1.2 (Equivalence with Polynomial Strip Continuation & Cofactor Defect Formula) `[PROVED HERE]`

Suppose $\zeta_\nu$ admits a function $G$ continuous on `verticalStrip (1/2) (3/2)`, holomorphic on $\{\frac{1}{2} < \mathrm{Re}\,s < \frac{3}{2}\}$, agreeing with $(s - 1)\zeta_\nu(s)$ on $\mathrm{Re}\,s > 1$, and satisfying $\|G(s)\| \le C_0 (1 + |\mathrm{Im}\,s|)^{N_0}$ on `verticalStrip (1/2) (3/2)`. Set $A := G(1)$ and $\beta := A / 2$.

1. Defining $\zeta_\nu^{\mathrm{ext}}(s) := G(s)/(s - 1)$ for $s \ne 1$, the function
   $$E(s) := \Gamma_{\mathbb{R}}(s)\,\zeta_\nu^{\mathrm{ext}}(s) - \beta\,\Gamma_{\mathbb{R}}(s - 1) \quad (s \ne 1)$$
   has a removable singularity at $s = 1$ and satisfies (1)–(3) of Definition 1.1 with unique continuous defect
   $$g(t) = \zeta_\nu^{\mathrm{ext}}\!\left(\tfrac{1}{2} + 2it\right) - \chi\!\left(\tfrac{1}{2} + 2it\right)\zeta_\nu^{\mathrm{ext}}\!\left(\tfrac{1}{2} - 2it\right), \qquad \chi(s) := \frac{\Gamma_{\mathbb{R}}(1 - s)}{\Gamma_{\mathbb{R}}(s)}, \quad \bigl|\chi\!\left(\tfrac{1}{2} + 2it\right)\bigr| = 1.$$
2. If in addition $\zeta_\nu^{\mathrm{ext}}(s) = \zeta(s)\,M(s)$ where $M$ is continuous on `verticalStrip (1/2) (3/2) \ {1}` and real-symmetric ($M(\bar s) = \overline{M(s)}$), then for all $t \in \mathbb{R}$,
   $$g(t) = 2i\,\zeta\!\left(\tfrac{1}{2} + 2it\right)\,\mathrm{Im}\,M\!\left(\tfrac{1}{2} + 2it\right).$$

**Proof.**
1. Near $s = 1$, $\Gamma_{\mathbb{R}}(1) = \pi^{-1/2}\Gamma(1/2) = 1$, while $(s - 1)\Gamma_{\mathbb{R}}(s - 1) = \pi^{-(s-1)/2} \cdot 2\,\frac{s - 1}{2}\Gamma\!\left(\frac{s - 1}{2}\right) = 2\pi^{-(s-1)/2}\Gamma\!\left(\frac{s + 1}{2}\right) \to 2$ as $s \to 1$. Hence $(s - 1)E(s) = \Gamma_{\mathbb{R}}(s)G(s) - \beta(s - 1)\Gamma_{\mathbb{R}}(s - 1) \to A - 2\beta = 0$ as $s \to 1$. By Riemann's removable singularity theorem, $E$ extends holomorphically across $s = 1$ on $\{\frac{1}{2} < \mathrm{Re}\,s < \frac{3}{2}\}$ and continuously to `verticalStrip (1/2) (3/2)`. By Stirling's bound (`exists_sharp_bound_norm_Gamma_strip`), $\|\Gamma_{\mathbb{R}}(\sigma + i\tau)\| \le C_1 (1 + |\tau|)^{M_1} e^{-\pi|\tau|/4}$ uniformly on $\sigma \in [-\frac{1}{2}, \frac{3}{2}]$, so $\|E(s)\| \le C / (1 + (\mathrm{Im}\,s)^2)$ on `verticalStrip (1/2) (3/2)`. Identity (2) holds on $\mathrm{Re}\,s = \frac{3}{2}$ by analytic continuation from $\mathrm{Re}\,s > 1$. On $s = \frac{1}{2} + 2it$ ($1 - s = \frac{1}{2} - 2it$), substituting $E(s) = \Gamma_{\mathbb{R}}(s)\zeta_\nu^{\mathrm{ext}}(s) - \beta\Gamma_{\mathbb{R}}(s - 1)$ and $E(1 - s) = \Gamma_{\mathbb{R}}(1 - s)\zeta_\nu^{\mathrm{ext}}(1 - s) - \beta\Gamma_{\mathbb{R}}(-s)$ yields
   $$E(s) - E(1 - s) = -\beta\bigl(\Gamma_{\mathbb{R}}(s - 1) - \Gamma_{\mathbb{R}}(-s)\bigr) + \Gamma_{\mathbb{R}}(s)\Bigl(\zeta_\nu^{\mathrm{ext}}(s) - \frac{\Gamma_{\mathbb{R}}(1 - s)}{\Gamma_{\mathbb{R}}(s)}\zeta_\nu^{\mathrm{ext}}(1 - s)\Bigr),$$
   since $\Gamma_{\mathbb{R}}(\frac{1}{2} + 2it) \ne 0$. Because $\overline{\Gamma_{\mathbb{R}}(\frac{1}{2} + 2it)} = \Gamma_{\mathbb{R}}(\frac{1}{2} - 2it)$, $|\chi(\frac{1}{2} + 2it)| = 1$, and polynomial boundedness of $G$ gives polynomial boundedness of $g$.
2. For $s = \frac{1}{2} + 2it \ne 1$, Riemann's functional equation $\Gamma_{\mathbb{R}}(s)\zeta(s) = \Gamma_{\mathbb{R}}(1 - s)\zeta(1 - s)$ (`riemannZeta_def_of_ne_zero` / `completedRiemannZeta_one_sub`) gives $\chi(s)\zeta(1 - s) = \zeta(s)$, while $1 - s = \bar s$ gives $M(1 - s) = \overline{M(s)}$. Thus $g(t) = \zeta(s)M(s) - \zeta(s)\overline{M(s)} = 2i\,\zeta(s)\,\mathrm{Im}\,M(s)$. $\square$

### Complete Answer Matrix to B186

Throughout the table, every system continues to $\mathrm{Re}\,s \ge \frac{1}{2}$ in the Hamburger strip class, has count rate $N(x) = A x + O(x^{\beta_c})$ with $\beta_c < 1$, and has a fake zero $\rho_0$ in $\mathrm{Re}\,s > \frac{1}{2}$ ($\zeta_B(\rho_0) = 0 \ne \zeta(\rho_0)$).

| System Class | Can $g = O(\lvert t\rvert^{-1/2+\varepsilon})$ ($\varepsilon < \frac{1}{2}$)? | Can $g$ be bounded ($g = O(1)$)? | Must $g$ grow like a power $\lvert t\rvert^\alpha$ ($\alpha > 0$)? | Least Possible Growth of $g(t)$ |
| :--- | :--- | :--- | :--- | :--- |
| **Two-sided prime edits** (`IsEdit e`, `editSystem e`, mult. $\{0,1,2\}$) | **NO** (unconditional; not even Abel-sublinear or $o(1)$ — **Thm I.2**) | **NO** (unconditional: $\int \|g\|^2 e^{-\lvert t\rvert/T} dt \gtrsim T\log T$, $\limsup \frac{\|g\|}{\sqrt{\log\lvert t\rvert}} > 0$ — **Thm I.3**) | **Dichotomy (Thm I.4):** either $\Theta = 1$ (`AsymptoticAbscissaLaw` holds for $\zeta$), or $\Theta < 1$ and **NO** | $\Omega(\sqrt{\log\lvert t\rvert})$ pointwise & $\Omega(\log T)$ in $L^2$-mean; if $\Theta < 1$, $\frac{1}{2T}\int_{-T}^T \|g\|^2 dt = O_\varepsilon(T^\varepsilon)$ $\forall \varepsilon > 0$ (exact $L^2$-exponent $0$) |
| **Unweighted countable Beurling** (`RHTower.BeurlingSystem`, `[Countable B.Label]`, real norms) | **NO** (unconditional rigidity up to $\varepsilon < \frac{1}{2}$ — **Thm II.1**) | **NO** for all integer-norm fakes (**Thm I.3**) | Same $\Theta = 1$ vs $\Theta < 1$ dichotomy; if $\Theta < 1$, **NO** (**Thm I.4**) | Strictly above $\lvert t\rvert^{-1/2+\varepsilon}$ ($\varepsilon < \frac{1}{2}$); subpolynomial $O_\varepsilon(T^\varepsilon)$ in $L^2$-mean when $\Theta < 1$ |
| **Integer-norm real-weighted Beurling** ($w_p \in \mathbb{R}$ on primes/prime powers) | **NO** (unconditional, for both $A > 0$ and $A = 0$ — **Thm II.2(a)**) | **NO** if $A > 0$ and a prime has $a(p_0 k)=0$; **YES** if signed with $A = 0$ (**Thm II.2(b)**) | **NO** (at $A=0$, bounded $g$; at $A>0$ & $\Theta < 1$, `posTruncatedZeta` gives $O_\varepsilon(T^\varepsilon)$) | At $A = 0$ (signed): $g = O(1)$ with $\liminf_{\delta\to 0^+} \delta\int \|g\|e^{-\delta\lvert t\rvert} dt > 0$ |
| **Positive-real-weighted countable Beurling** (`HTGeometry.Beurling.System`, $w_i > 0$, `finite_below`, $A > 0$) | **NO** on integer norms (**Thm II.2(a)**) | Continuous limit `overRegularZeta` has $g = O(1)$ | **UNCONDITIONALLY NO** — **no case split on $\Theta$** (**Thm II.3**) | $\|g(t)\| \le \Phi(\lvert t\rvert)$ unconditionally for **every** prescribed unbounded nondecreasing $\Phi \to \infty$ (e.g. $\log\log\lvert t\rvert$) |

---

## 2. Part I: Unconditional Theorems for Two-Sided Edits of the Rational Primes

Let `e : ℕ → ℤ` satisfy `TwoSidedEdits.IsEdit e` (`formal/GaloisForLFunctions/WorldsOfTheZeroConfiguration/TwoSidedPrimeEdits.lean:34`), and let $B := \mathrm{editSystem}\,e$ (`:45`), with integer-norm Dirichlet coefficients $a_B(n) := \mathrm{intCount}\,B\,(\mathrm{hasIntegerNorms\_editSystem}\,e)\,n \in \mathbb{N}$ ($a_B(1) = 1$) and counting function $N_B(x) := \sum_{1 \le n \le x} a_B(n) = (B.\mathrm{countBall}\,x : \mathbb{R})$.

### Theorem I.1 (Universal Positive Density and Deleted-Prime Multiples) `[PROVED HERE]`

Let $B$ be any discrete integer-norm Beurling system (`HasIntegerNorms B`, `B.IsDiscrete`) that is an integer-norm fake at exponent $\beta_c < 1$ (`IsIntegerNormFakeAt B β_c`, `IntegerNormFakeObstructions.lean:1058`) and continues to `verticalStrip (1/2) (3/2)` in the Hamburger strip class with parameter $\beta$ and defect $g$.

1. The linear counting density $A$ satisfies $A = 2\beta \in (0, \infty)$ unconditionally for all $\beta_c < 1$ (extending `pos_density_of_integerNormFakeAt_le_half` from $\beta_c \le \frac{1}{2}$ to all $\beta_c < 1$).
2. The set of rational primes omitted from $B.\mathrm{labelNorm}$ is infinite. In particular, if $B = \mathrm{editSystem}\,e$ for a two-sided edit `IsEdit e`, there exists a least prime $p_0 \ge 2$ with $e(p_0) = -1$, and $a_B(p_0 k) = 0$ for every integer $k \ge 1$.

**Proof.**
1. Since $|N_B(x) - A x| \le C_R x^{\beta_c}$ for $x \ge 1$ with $\beta_c < 1$ and $A \ge 0$, summation by parts on $\sigma > 1$ gives
   $$\zeta_B(s) = s \int_1^\infty N_B(x) x^{-s-1}\,dx = \frac{A s}{s - 1} + s \int_1^\infty (N_B(x) - A x) x^{-s-1}\,dx,$$
   where the integral is holomorphic on $\mathrm{Re}\,s > \max(\beta_c, 0)$. Hence $\lim_{s \to 1^+} (s - 1)\zeta_B(s) = A$. Comparing with $\Gamma_{\mathbb{R}}(s)\zeta_B(s) = E(s) + \beta\Gamma_{\mathbb{R}}(s - 1)$ as $s \to 1^+$ (extended from $\mathrm{Re}\,s = \frac{3}{2}$ to $\{\frac{1}{2} < \mathrm{Re}\,s \le \frac{3}{2}\} \setminus \{1\}$ by uniqueness of analytic continuation) gives $A = 2\beta$, so $\beta \in \mathbb{R}$ and $\beta \ge 0$.
   Suppose for contradiction that $A = 0$, so $\beta = 0$ and $0 \le N_B(x) \le C_R x^{\beta_c}$ for all $x \ge 1$. For every $\sigma > \max(\beta_c, 0)$, monotonicity and nonnegativity of $a_B(n) \ge 0$ yield
   $$\sum_{n=1}^\infty a_B(n) n^{-\sigma} = \sigma \int_1^\infty N_B(x) x^{-\sigma - 1}\,dx \le \sigma C_R \int_1^\infty x^{\beta_c - \sigma - 1}\,dx = \frac{\sigma C_R}{\sigma - \beta_c} < \infty.$$
   Consequently, $\sum_{l \in B.\mathrm{Label}} (B.\mathrm{labelNorm}\,l)^{-\sigma} \le \sum_{n=1}^\infty a_B(n) n^{-\sigma} < \infty$ for every $\sigma > \max(\beta_c, 0)$, so the Euler product of $\zeta_B(s)$ converges absolutely and is nonvanishing on $\mathrm{Re}\,s > \max(\beta_c, 0)$ (`differentiableOn_and_ne_zero_zetaSeriesC_of_summable`). Since $B$ has a fake zero $\rho_0$ with $\mathrm{Re}\,\rho_0 > \frac{1}{2}$ and $\zeta_B^{\mathrm{ext}}(\rho_0) = 0$, we must have $\frac{1}{2} < \mathrm{Re}\,\rho_0 \le \max(\beta_c, 0) < 1$ (hence $\beta_c > \frac{1}{2}$). Let
   $$\sigma_c := \inf\Bigl\{\sigma \in \mathbb{R} : \sum_{n=1}^\infty a_B(n) n^{-\sigma} < \infty\Bigr\}.$$
   Because $\zeta_B^{\mathrm{ext}}(\rho_0) = 0$, the series cannot converge at any $\sigma < \mathrm{Re}\,\rho_0$, while it converges for all $\sigma > \beta_c$; hence $\sigma_c \in [\mathrm{Re}\,\rho_0, \beta_c] \subset (\frac{1}{2}, 1)$. Because $\beta = 0$, $\zeta_B^{\mathrm{ext}}(s) = E(s)/\Gamma_{\mathbb{R}}(s)$ is holomorphic on the entire open strip $\{\frac{1}{2} < \mathrm{Re}\,s < \frac{3}{2}\}$, which contains a neighborhood of the real point $\sigma_c \in (\frac{1}{2}, 1)$. Applying Landau's theorem for Dirichlet series with nonnegative coefficients (`RHTower.landau_summability_transfer`, `formal/GaloisForLFunctions/RHTower/LandauSummabilityTransfer.lean:11`) transfers summability from $\sigma = 2$ past $\sigma_c$ to $\sigma_c - \delta$ for some $\delta > 0$, contradicting the definition of $\sigma_c$. Thus $A = 2\beta > 0$.
2. Since $\beta_c < 1 \le 1$, `infinite_missing_primes_of_integerNormFakeAt` (`IntegerNormFakeObstructions.lean:1412`) proves that $\{p \in \mathbb{N} : p.\mathrm{Prime} \land \forall l \in B.\mathrm{Label},\, B.\mathrm{labelNorm}\,l \ne p\}$ is infinite. For $B = \mathrm{editSystem}\,e$, a prime $p$ is absent from $B.\mathrm{labelNorm}$ if and only if $p \in \mathrm{minusSet}\,e$, i.e., $e(p) = -1$ (`TwoSidedPrimeEdits.lean:42–46`). By well-ordering of $\mathbb{N}$, there is a least prime $p_0 \ge 2$ with $e(p_0) = -1$. Every label $l \in (\mathrm{editSystem}\,e).\mathrm{Label}$ has norm equal to some prime $q \ne p_0$; by unique prime factorization in $\mathbb{N}$, no finite product of primes $q \ne p_0$ is divisible by $p_0$, so no $x \in B.\mathrm{Integer}$ has $B.\mathrm{intNorm}\,x = p_0 k$ for any $k \ge 1$. Hence $a_B(p_0 k) = 0$ for all $k \ge 1$. $\square$

---

### Theorem I.2 (Unconditional Impossibility of $g = O(|t|^{-1/2+\varepsilon})$ and Quantitative Abel Floor) `[PROVED HERE]`

Let $e$ satisfy `IsEdit e`, and suppose $B = \mathrm{editSystem}\,e$ is an integer-norm fake at $\beta_c < 1$ continuing to `verticalStrip (1/2) (3/2)` in the Hamburger strip class with critical-line defect $g$, and let $p_0 \ge 2$ be the least prime with $e(p_0) = -1$. Then unconditionally:

$$\liminf_{\delta \to 0^+} \,\delta \int_{-\infty}^\infty \|g(t)\| e^{-\delta |t|}\,dt \ge \frac{1}{3(p_0 + 1)} > 0.$$

In particular, there is **no** such two-sided edit whose defect $g$ is Abel-sublinear, **no** such edit with $g(t) = o(1)$ as $|t| \to \infty$, and **no** such edit with $g(t) = O(|t|^{-1/2 + \varepsilon})$ for any $\varepsilon < \frac{1}{2}$.

**Proof.**
Set $a(n) := (a_B(n) : \mathbb{C})$. By Theorem I.1, $a(1) = 1$ and $a(p_0) = 0$. Since $|N_B(x) - A x| \le C_R x^{\beta_c}$, $\sum_{n=1}^\infty \|a(n)\| n^{-\sigma} < \infty$ for every $\sigma > 1$. As proved in `HamburgerStabilityCriticalLine.lean:775–795` (`hamburgerSeries_eq_of_coeffTheta_relation_defect`), for every $\tau \in \mathbb{C}$ with $\mathrm{Re}\,\tau > 0$,
$$L_a(\tau) := \sum_{n=1}^\infty \frac{a(n)\tau}{\pi(n^2 + \tau^2)} = F_a(\tau) - \frac{\beta}{\pi \tau} + \beta + J_g(\tau), \qquad F_a(\tau) := \sum_{n=1}^\infty a(n) e^{-2\pi n \tau},$$
where $J_g(\tau) = \mathrm{defectLaplace}\,g\,\tau$ satisfies `norm_defectLaplace_le` (`HamburgerStabilityCriticalLine.lean:527`):
$$\|J_g(\tau)\| \le \frac{3}{2\pi} \|\tau\|^{-1/2} \int_{-\infty}^\infty \|g(t)\| \exp\!\left(-\frac{2\,\mathrm{Re}\,\tau}{\|\tau\|}|t|\right) dt \qquad (\mathrm{Re}\,\tau > 0).$$
Because $e^{-2\pi n (\tau + i m)} = e^{-2\pi n \tau}$ for every $m \in \mathbb{Z}$, $F_a(\varepsilon + i p_0) = F_a(\varepsilon + i)$ for all $\varepsilon > 0$. Subtracting the identity at $\tau_1(\varepsilon) := \varepsilon + i$ from the identity at $\tau_{p_0}(\varepsilon) := \varepsilon + i p_0$ cancels $F_a$ and $\beta$ identically:
$$L_a(\varepsilon + i p_0) - L_a(\varepsilon + i) = -\frac{\beta}{\pi(\varepsilon + i p_0)} + \frac{\beta}{\pi(\varepsilon + i)} + J_g(\varepsilon + i p_0) - J_g(\varepsilon + i).$$
Multiply by $2\pi\varepsilon$ and let $\varepsilon \in (0, 1)$ tend to $0^+$. For any $m \ge 1$, the $n = m$ term of $2\pi\varepsilon L_a(\varepsilon + i m)$ equals $\frac{2 a(m)(\varepsilon + i m)}{\varepsilon + 2 i m} \to a(m)$, while for $n \ne m$, $|n^2 + (\varepsilon + i m)^2| \ge |n^2 - m^2| \ge \frac{1}{3} n^2$, so Dominated Convergence (`tendsto_mul_hamburgerSeries_radial`) gives $\lim_{\varepsilon \to 0^+} 2\pi\varepsilon L_a(\varepsilon + i m) = a(m)$. Thus the left-hand side converges to $a(p_0) - a(1) = 0 - 1 = -1$, while the polar difference $2\varepsilon\beta\bigl(\frac{1}{\varepsilon + i} - \frac{1}{\varepsilon + i p_0}\bigr)$ converges to $0$.
For $\varepsilon \in (0, 1)$, we have $\|\tau_1(\varepsilon)\| \ge 1$, $\|\tau_{p_0}(\varepsilon)\| \ge p_0 \ge 2$, and $\|\tau_1(\varepsilon)\| \le \|\tau_{p_0}(\varepsilon)\| \le p_0 + \varepsilon < p_0 + 1$. Setting $\delta := \frac{2\varepsilon}{p_0 + 1} \in (0, \frac{2}{p_0 + 1})$, monotonicity of $u \mapsto e^{-u|t|}$ (`abelMass_antitone`, `:546`) yields for both $m \in \{1, p_0\}$:
$$2\pi\varepsilon \|J_g(\varepsilon + i m)\| \le 3\varepsilon m^{-1/2} \int_{-\infty}^\infty \|g(t)\| e^{-\delta |t|}\,dt = \frac{3(p_0 + 1) m^{-1/2}}{2}\,\Bigl(\delta \int_{-\infty}^\infty \|g(t)\| e^{-\delta |t|}\,dt\Bigr).$$
Summing at $m = 1$ and $m = p_0$ ($1 + p_0^{-1/2} \le 1 + 2^{-1/2} < 2$) and taking $\liminf_{\varepsilon \to 0^+}$ gives
$$1 \le \frac{3(p_0 + 1)(1 + p_0^{-1/2})}{2}\,\liminf_{\delta \to 0^+} \delta \int_{-\infty}^\infty \|g(t)\| e^{-\delta |t|}\,dt \le 3(p_0 + 1)\,\liminf_{\delta \to 0^+} \delta \int_{-\infty}^\infty \|g(t)\| e^{-\delta |t|}\,dt.$$
Finally, if $\|g(t)\| \le C_1 (1 + |t|)^{-1/2 + \varepsilon_0}$ with $\varepsilon_0 < \frac{1}{2}$, then $\delta \int_{\mathbb{R}} \|g(t)\| e^{-\delta|t|}\,dt \le 2 C_1 \delta \int_0^\infty t^{-1/2+\varepsilon_0} e^{-\delta t}\,dt + 2 C_1 \delta = 2 C_1 \Gamma(\frac{1}{2}+\varepsilon_0) \delta^{1/2-\varepsilon_0} + 2 C_1 \delta \to 0$ as $\delta \to 0^+$, contradiction. $\square$

---

### Theorem I.3 (Unconditional Impossibility of Bounded $g$ and Logarithmic $L^2$ Blowup) `[PROVED HERE]`

Under the hypotheses of Theorem I.2, let $A = 2\beta > 0$ be the counting density and $p_0 \ge 2$ the least deleted prime ($e(p_0) = -1$). There exists $T_B \ge 2$ such that for every $T \ge T_B$,

$$\int_{-\infty}^\infty \|g(t)\|^2 e^{-|t|/T}\,dt \ge \frac{A^2}{256\pi p_0}\,T \log T,$$

and consequently

$$\limsup_{|t| \to \infty} \frac{\|g(t)\|}{\sqrt{\log |t|}} \ge \frac{A}{32\sqrt{\pi p_0}} > 0.$$

In particular, **no** two-sided edit with count rate $\beta_c < 1$ and a fake zero in $\mathrm{Re}\,s > \frac{1}{2}$ can have bounded critical-line FE defect $g$.

**Proof.**
Fix $\theta \in (0, \frac{1}{16})$ and consider the tilted unit ray $\tau(r) := r z_\theta$ ($r > 0$), where $z_\theta := \sin\theta + i\cos\theta = e^{i(\frac{\pi}{2} - \theta)}$ has $\mathrm{Re}\,z_\theta = \sin\theta > 0$ and $\arg z_\theta = \frac{\pi}{2} - \theta$.

**Step 1 (Tilted ray Plancherel upper bound).** By `norm_boundaryPairKernel_unit` and `norm_sin_quarter_sq` (`TheBoundaryPreservesDefectEnergy.lean:60, 77`), for every $t \in \mathbb{R}$,
$$\|\mathrm{boundaryPairKernel}(2t, z_\theta)\|^2 = \frac{4 \exp\bigl(-2(\frac{\pi}{2} - \theta)(2t)\bigr)}{e^{2\pi t} + e^{-2\pi t}} = \frac{4 e^{-(2\pi - 4\theta)t}}{e^{2\pi t} + e^{-2\pi t}} \le 4 e^{-4\theta |t|},$$
because for $t \ge 0$ the denominator exceeds $e^{2\pi t}$ and $4\pi - 4\theta > 4\theta$, while for $t < 0$ the denominator exceeds $e^{-2\pi t}$. Since $\|g(t)\| \le C_g (1 + |t|)^{N_g}$, the damped source $f_\theta(t) := g(t)\,\mathrm{boundaryPairKernel}(2t, z_\theta)$ belongs to $L^1(\mathbb{R}) \cap L^2(\mathbb{R})$. For $r > 0$, `closedDefectLaplace_ray_eq` (`:170`) identifies $J_g(r z_\theta) = \mathrm{mellinInv}\,(1/2)\,(\mathrm{halfMellinData}\,f_\theta)\,r$. Applying Mellin–Plancherel (`integral_norm_sq_mellinInv` and `integral_norm_sq_halfMellinData`, `:131, 202`) gives
$$\int_0^\infty \|J_g(r z_\theta)\|^2\,dr = \frac{1}{4\pi}\int_{-\infty}^\infty \|g(t)\|^2 \|\mathrm{boundaryPairKernel}(2t, z_\theta)\|^2\,dt \le \frac{1}{\pi}\int_{-\infty}^\infty \|g(t)\|^2 e^{-4\theta |t|}\,dt.$$

**Step 2 (Disjoint resonant windows at multiples of $p_0$).** Set $\beta_* := \max(\beta_c, 0) \in [0, 1)$, $M(\theta) := \lfloor \theta^{-1/4}\rfloor$, and $K(\theta) := \lfloor M(\theta) / p_0 \rfloor$. For each integer $1 \le k \le K(\theta)$, set $m := p_0 k \in [2, M(\theta)]$ and define the $r$-interval
$$I_{m,\theta} := \left[\frac{m - \frac{1}{4} m\theta}{\cos\theta},\, \frac{m + \frac{1}{4} m\theta}{\cos\theta}\right] \subset (0, \infty).$$
Since $\frac{1}{4} m\theta \le \frac{1}{4}\theta^{3/4} < \frac{1}{32}$ for $\theta < \frac{1}{16}$, we have $y := r\cos\theta \in [m - \frac{1}{32}, m + \frac{1}{32}]$ on $I_{m,\theta}$, so the intervals $\{I_{p_0 k, \theta}\}_{1 \le k \le K(\theta)}$ are pairwise disjoint with length $|I_{m,\theta}| = \frac{m\theta}{2\cos\theta} \ge \frac{1}{2} m\theta$. Moreover, on $I_{m,\theta}$, $x := r\sin\theta = y\tan\theta$ satisfies $\frac{3}{4} m\theta \le x \le \frac{3}{2} m\theta$, and $\tilde\tau := \tau(r) - i m = x + i(y - m)$ satisfies $\mathrm{Re}\,\tilde\tau = x \ge \frac{3}{4} m\theta$ and $|\tilde\tau| = \sqrt{x^2 + (y - m)^2} \le 2 m\theta$.

**Step 3 (Lower bound for $F_a(\tau)$ on $I_{m,\theta}$).** By $i$-periodicity, $F_a(\tau(r)) = F_a(\tilde\tau)$. Writing $N_B(u) = A u + R_B(u)$ for $u \ge 1$ ($|R_B(u)| \le C_R u^{\beta_*}$) and $N_B(u) = 0$ for $0 \le u < 1$, Stieltjes integration by parts gives
$$F_a(\tilde\tau) = 2\pi\tilde\tau \int_1^\infty N_B(u) e^{-2\pi u \tilde\tau}\,du = \frac{A}{2\pi \tilde\tau} - 2\pi\tilde\tau \int_0^1 A u e^{-2\pi u \tilde\tau}\,du + 2\pi\tilde\tau \int_1^\infty R_B(u) e^{-2\pi u \tilde\tau}\,du.$$
Using $|\tilde\tau| \le 2 m\theta$ and $x \ge \frac{3}{4} m\theta$, the second term has norm $\le \pi A |\tilde\tau| \le 2\pi A m\theta$, and the third term has norm at most
$$2\pi |\tilde\tau| C_R \int_0^\infty u^{\beta_*} e^{-2\pi x u}\,du = 2\pi C_R \Gamma(1 + \beta_*)\frac{|\tilde\tau|}{(2\pi x)^{1 + \beta_*}} \le C_1 (m\theta)^{-\beta_*},$$
where $C_1$ depends only on $(C_R, \beta_*)$. Since $|\frac{A}{2\pi\tilde\tau}| \ge \frac{A}{4\pi m\theta}$, on $I_{m,\theta}$ we have
$$\|F_a(\tau(r))\| \ge \frac{A}{4\pi m\theta} - 2\pi A m\theta - C_1 (m\theta)^{-\beta_*}.$$

**Step 4 (Upper bound for $L_a(\tau)$ and polar terms on $I_{m,\theta}$).** By Theorem I.1(2), $a_B(m) = a_B(p_0 k) = 0$, so the resonant $n = m$ term is absent from $L_a(\tau(r)) = \sum_{n \ne m} \frac{a_B(n)\tau(r)}{\pi(n^2 + \tau(r)^2)}$. For $n \ne m$ and $y \in [m - \frac{1}{32}, m + \frac{1}{32}]$, $|n - y| \ge |n - m| - \frac{1}{32} \ge \frac{1}{2}|n - m|$ and $n + y \ge \frac{1}{2}(n + m)$, whence $|n^2 + \tau(r)^2| = |n - i\tau(r)|\,|n + i\tau(r)| \ge |n - y|(n + y) \ge \frac{1}{4}|n - m|(n + m)$. Since $|\tau(r)| \le 2m$,
$$\|L_a(\tau(r))\| \le \frac{8 m}{\pi}\sum_{1 \le |n - m| \le m} \frac{a_B(n)}{|n - m|\cdot m} + \frac{16 m}{\pi}\sum_{n > 2m} \frac{a_B(n)}{n^2}.$$
The tail $\frac{16m}{\pi}\sum_{n > 2m} a_B(n) n^{-2}$ is bounded by a constant $C_2$ depending only on $(A, C_R)$ via Stieltjes integration of $N_B(u) \le (A + C_R)u$. For $1 \le j \le m$, set $S(j) := \sum_{1 \le |n - m| \le j} a_B(n) = N_B(m + j) - N_B(m - j - 1) \le A(2j + 1) + 2 C_R (2m)^{\beta_*} \le 3 A j + 4 C_R m^{\beta_*}$. Summation by parts gives
$$\sum_{j=1}^m \frac{a_B(m - j) + a_B(m + j)}{j} = \frac{S(m)}{m} + \sum_{j=1}^{m-1} \frac{S(j)}{j(j + 1)} \le 3A(1 + \log(2m)) + 8 C_R m^{\beta_*}.$$
Combined with $\|-\frac{\beta}{\pi\tau(r)} + \beta\| \le |\beta|(\frac{1}{\pi} + 1)$ (as $|\tau(r)| \ge 1$), we obtain $\|L_a(\tau(r)) + \frac{\beta}{\pi\tau(r)} - \beta\| \le C_3 (\log(2m) + m^{\beta_*})$ on $I_{m,\theta}$.

**Step 5 (Summing over $1 \le k \le K(\theta)$).** Since $m \le \theta^{-1/4}$ and $\beta_* < 1$,
$$(m\theta)\bigl(2\pi A m\theta + C_1(m\theta)^{-\beta_*} + C_3(\log(2m) + m^{\beta_*})\bigr) \le 2\pi A \theta^{3/2} + C_1 \theta^{\frac{3}{4}(1 - \beta_*)} + C_3 \theta^{3/4}\log(2\theta^{-1/4}) + C_3 \theta^{1 - \frac{1 + \beta_*}{4}} \xrightarrow{\theta \to 0^+} 0$$
uniformly in $1 \le k \le K(\theta)$, since $1 - \frac{1 + \beta_*}{4} > \frac{1}{2} > 0$ and $\frac{3}{4}(1 - \beta_*) > 0$. Thus there exists $\theta_0 \in (0, \frac{1}{16})$ depending only on $(A, C_R, \beta_c, p_0)$ such that for all $\theta \in (0, \theta_0]$ and all $1 \le k \le K(\theta)$, both $\|J_g(r z_\theta)\| \ge \frac{A}{8\pi p_0 k \theta}$ on $I_{p_0 k, \theta}$ and $\sum_{k=1}^{K(\theta)} \frac{1}{k} \ge \log K(\theta) \ge \frac{1}{8}\log(\theta^{-1})$. Integrating and summing over the disjoint intervals $I_{p_0 k, \theta}$ yields
$$\frac{1}{\pi}\int_{-\infty}^\infty \|g(t)\|^2 e^{-4\theta |t|}\,dt \ge \sum_{k=1}^{K(\theta)} \int_{I_{p_0 k, \theta}} \|J_g(r z_\theta)\|^2\,dr \ge \sum_{k=1}^{K(\theta)} \frac{1}{2} p_0 k \theta \cdot \frac{A^2}{64\pi^2 p_0^2 k^2 \theta^2} \ge \frac{A^2}{1024\pi^2 p_0}\,\theta^{-1}\log(\theta^{-1}).$$
Setting $T_B := \max(2, \frac{1}{4\theta_0})$ and $\theta := \frac{1}{4T}$ ($\theta^{-1} = 4T > T$) gives $\int_{\mathbb{R}} \|g(t)\|^2 e^{-|t|/T}\,dt \ge \frac{A^2}{256\pi p_0} T\log T$ for all $T \ge T_B$.
Finally, if $\limsup_{|t|\to\infty} \|g(t)\|/\sqrt{\log |t|} < \frac{A}{32\sqrt{\pi p_0}}$, then $\|g(t)\|^2 \le \frac{A^2}{1024\pi p_0}\log(|t| + 2)$ for all $|t| \ge t_1$, whence $\int_{\mathbb{R}} \|g(t)\|^2 e^{-|t|/T}\,dt \le O(1) + \frac{2 A^2}{1024\pi p_0}\int_0^\infty \log(t + 2) e^{-t/T}\,dt = \frac{A^2}{512\pi p_0} T\log T + O(T)$, contradicting $\ge \frac{A^2}{256\pi p_0} T\log T$ as $T \to \infty$. $\square$

---

### Theorem I.4 (Unconditional Frontier Dichotomy and Subpolynomial-$L^2$ Two-Sided Edit) `[PROVED HERE]`

Let $\Theta := \mathrm{zetaZeroAbscissa} \in [\frac{1}{2}, 1]$ (`TheMeromorphicTemperedEulerFirewall.lean:53`). Unconditionally, at least one of the following two statements holds:

- **(Branch A: $\Theta = 1$)** `RHTower.AsymptoticAbscissaLaw` holds unconditionally for $\zeta$ (`asymptoticAbscissaLaw_of_zetaZeroAbscissa_eq_one`), while for every $\rho$ with $\frac{1}{2} < \mathrm{Re}\,\rho < \frac{14}{15}$ and $\zeta(\rho) \ne 0$, the WZC greedy edit (`TwinsContinuePastTheLine.isFactorTwinOn_edit`) is a two-sided edit continuing past $\mathrm{Re}\,s = \frac{1}{2}$ with a fake zero at $\rho$ and polynomial defect $g$.
- **(Branch B: $\Theta < 1$)** For every $\beta_0 \in (\frac{1}{2}, \min(\frac{3}{2} - \Theta, \frac{5}{8}))$, every $\gamma_0 \ne 0$ with $\zeta(\beta_0 + i\gamma_0) \ne 0$ ($\rho_0 := \beta_0 + i\gamma_0$), and every $\beta_c \in (\beta_0, 1)$, there exists a two-sided edit `e : ℕ → ℤ` (`IsEdit e`) such that `B := editSystem e` satisfies:
  1. $B$ is an integer-norm fake at $\beta_c$ (`IsIntegerNormFakeAt B β_c`) with count rate $N_B(x) = A x + O(x^{\beta_c})$ ($A > 0$);
  2. $(s - 1)\zeta_B(s)$ extends holomorphically to $\mathrm{Re}\,s > \sigma_1$ for $\sigma_1 := \max(\frac{3}{8}, \frac{1}{2}(\Theta + \beta_0 - \frac{1}{2})) < \frac{1}{2}$, where its zeros are precisely the zeros of $(s - 1)\zeta(s)$ together with $\{\rho_0, \bar\rho_0\}$;
  3. $B$ satisfies Definition 1.1 on `verticalStrip (1/2) (3/2)` with critical-line FE defect $g(t)$ obeying, for **every** $\varepsilon > 0$, existence of $K_\varepsilon > 0$ such that
     $$\|g(t)\| \le 2 K_\varepsilon\,\bigl|\zeta\!\left(\tfrac{1}{2} + 2it\right)\bigr|\,(1 + |t|)^\varepsilon \quad (\forall t \in \mathbb{R}), \qquad \frac{1}{2T}\int_{-T}^T \|g(t)\|^2\,dt = O_\varepsilon(T^\varepsilon) \quad (T \ge 2),$$
     and pointwise $\|g(t)\| = O_\varepsilon(|t|^{1/3 + \varepsilon})$ unconditionally via corpus interpolation (`exists_norm_riemannZeta_le_interp`) and $\|g(t)\| = O_\varepsilon(|t|^\varepsilon)$ under Lindelöf/RH.

In particular, in Branch B, the infimal $L^2$-power growth exponent $\inf\{\alpha > 0 : \frac{1}{2T}\int_{-T}^T \|g(t)\|^2\,dt = O(T^{2\alpha})\}$ of fake two-sided edits is **identically $0$**: `g(t)` does **not** grow like a positive power of $|t|$ in $L^2$-mean.

**Proof.**
By excluded middle (`by_cases hΘ : zetaZeroAbscissa = 1`), either $\Theta = 1$ or $\Theta < 1$. If $\Theta = 1$, Branch A is already proved in `TheMeromorphicTemperedEulerFirewall.lean:1666` and `TwinsContinuePastTheLine.lean:126`.

Assume now $\Theta < 1$. Since $\frac{3}{2} - \Theta > \frac{1}{2}$, the interval $(\frac{1}{2}, \min(\frac{3}{2} - \Theta, \frac{5}{8}))$ is non-empty; fix $\beta_0, \gamma_0, \beta_c$ as stated (note $\gamma_0 \ne 0$ with $\zeta(\beta_0 + i\gamma_0) \ne 0$ exists since the zeros of $\zeta$ are isolated). Choose $k_0 \ge 2$ such that $P_* := 2^{k_0} - 1$ satisfies $2(P_* + 1)^{\beta_0 - 1} \le 1$ and $\frac{1}{2}\cdot 2^{k_0(1 - \beta_0)} \ge 2$.

**Step 1 (Grouped two-sided selection on dyadic prime blocks).** For each $k \ge k_0$, let $\mathrm{blockPrimes}\,k := \{p \in [2^k, 2^{k+1}) : p.\mathrm{Prime}\}$ (`BeurlingRandomPrimeDeletion.lean:98`), set group length $L_k := \lfloor \frac{1}{2}\cdot 2^{k(1 - \beta_0)}\rfloor \ge 2$, and partition $\mathrm{blockPrimes}\,k$ into $n_k := 2^k / L_k + 1$ consecutive groups $G_{k, i}$ of cardinality $\le L_k$. Since $L_k \ge \frac{1}{4}\cdot 2^{k(1 - \beta_0)}$, we have $n_k \le 4\cdot 2^{k\beta_0} + 1 \le 5\cdot 2^{k\beta_0}$.
For each prime $p \in \mathrm{blockPrimes}\,k$, define the nonnegative selection weight and deterministic sign
$$w(p) := 2 p^{\beta_0 - 1}\,\bigl|\cos(\gamma_0 \log p)\bigr| \ge 0, \qquad \sigma(p) := \begin{cases} -1 & \text{if } \cos(\gamma_0 \log p) > 0, \\ +1 & \text{if } \cos(\gamma_0 \log p) < 0, \\ 0 & \text{if } \cos(\gamma_0 \log p) = 0, \end{cases}$$
so that $\sigma(p) w(p) = -2 p^{\beta_0 - 1}\cos(\gamma_0 \log p)$. Because $p \ge 2^k$ on $G_{k, i}$, $w(p) \le 2\cdot 2^{k(\beta_0 - 1)}$ and $\sum_{p \in G_{k, i}} w(p) \le L_k \cdot 2\cdot 2^{k(\beta_0 - 1)} \le 1$.
Apply `HTGeometry.GroupedSelection.exists_selection` (`GroupedSelectionConcentration.lean:253`) on each block $k \ge k_0$ to the countable test family indexed by $(q, b, m) \in \mathrm{blockPrimes}\,k \times \mathrm{Bool} \times \mathbb{N}$ with bounded test functions $\varphi_{q, \tau}(p) := \sigma(p)\,\mathbf{1}_{p \le q}\,p^{-i\tau}$ ($\|\varphi_{q,\tau}(p)\| \le 1$) at net points $\tau_{k, b, m} := \pm \frac{m}{n_k(k + 1)}$ and thresholds $\theta_{k, m} := 4\sqrt{n_k}\sqrt{\log(2^{k+5}(m + 1)^2)}$, whose failure series sums to $\le |\mathrm{blockPrimes}\,k|\cdot 2\cdot \frac{4}{2^{k+5}}\frac{\pi^2}{6} \le \frac{\pi^2}{24} < 1$ (`BeurlingRandomPrimeDeletion.tsum_failure_lt`, `:242`). This produces a selection $\omega_k : \mathrm{Fin}\,n_k \to \mathbb{N}$ picking at most one prime per group $G_{k, i}$ (or $0$). Define `e : ℕ → ℤ` by $e(p) := \sigma(p)$ if $p \ge 2^{k_0}$ equals $\omega_k(i)$ for its block $k$ and group $i$, and $e(n) := 0$ otherwise. Clearly `IsEdit e` holds. Since $|\tau - \tau_{k, b, m}| \le \frac{1}{2 n_k(k + 1)}$ changes $p^{-i\tau}$ on $p < 2^{k+1}$ by at most $|\tau - \tau_{k,b,m}|\log p \le \frac{\log 2}{n_k}$ and each block has at most $n_k$ active terms plus $\sum_i \sum_{p \in G_{k, i}} w(p) \le n_k$, Lipschitz interpolation from the net (`BeurlingRandomPrimeDeletion.lean:280–340`) yields for all $x \ge 1$ and all $\tau \in \mathbb{R}$:
$$D(x, \tau) := \sum_{P_* < p \le x} \bigl(e(p) + 2 p^{\beta_0 - 1}\cos(\gamma_0 \log p)\bigr) p^{-i\tau}, \qquad \|D(x, \tau)\| \le C_0\,x^{\beta_0 / 2}(\log x + 1)\sqrt{\log(|\tau| + 2)}.$$

**Step 2 (Count rate via `editSystem_count`).** In each block $k \ge k_0$, at most $n_k \le 5\cdot 2^{k\beta_0}$ primes have $e(p) \ne 0$. For any $\beta_c \in (\beta_0, 1)$,
$$\sum_{n=1}^\infty |e(n)|\,n^{-\beta_c} \le \sum_{k = k_0}^\infty 5\cdot 2^{k\beta_0} \cdot 2^{-k\beta_c} = 5 \sum_{k = k_0}^\infty 2^{-k(\beta_c - \beta_0)} < \infty.$$
By `TwoSidedEdits.editSystem_count` (`TwoSidedPrimeEdits.lean:289`), $N_B(x) = A x + O(x^{\beta_c})$.

**Step 3 (Exact factorization through `posTruncatedZeta` and continuation past $\mathrm{Re}\,s = \frac{1}{2}$).** On $\mathrm{Re}\,s > 1$, `editSystem_zetaSeriesC` (`:232`) and `hasProd_and_LSeries_posTruncatedZeta` (`TheMeromorphicTemperedEulerFirewall.lean:503`) give
$$\zeta_B(s) = \mathrm{posTruncatedZeta}\,P_*\,\rho_0\,s \cdot \exp\bigl(H_1(s) + H_{\ge 2}(s)\bigr) = \zeta(s)\,M_B(s),$$
where $M_B(s) := \mathrm{posCofactor}\,P_*\,\rho_0\,s \cdot \exp(H_1(s) + H_{\ge 2}(s))$, $\mathrm{posCofactor}\,P_*\,\rho_0\,s = \mathrm{invZeta}(s + 1 - \rho_0)\,\mathrm{invZeta}(s + 1 - \bar\rho_0)\,\mathrm{posFiniteFactor}\,P_*\,\rho_0\,s$,
$$H_1(s) := \sum_{p > P_*} \bigl(e(p) + 2 p^{\beta_0 - 1}\cos(\gamma_0\log p)\bigr) p^{-s}, \qquad H_{\ge 2}(s) := \sum_{p > P_*} \sum_{m=2}^\infty \frac{e(p) + 2 p^{m(\beta_0 - 1)}\cos(m\gamma_0\log p)}{m} p^{-ms}.$$
Check analyticity and growth on $\mathrm{Re}\,s \ge \frac{3}{8}$:
- *Prime-power tail $H_{\ge 2}$:* Because $\beta_0 < \frac{5}{8}$, on $\sigma = \mathrm{Re}\,s \ge \frac{3}{8}$ the $e(p)$ sum over block $k$ is bounded by $5\cdot 2^{k\beta_0} \cdot 3\cdot 2^{-2\sigma(k - 1)} \ll 2^{k(\beta_0 - \frac{3}{4})} \le 2^{-k/8}$, while the $2 p^{m(\beta_0 - 1)}$ sum over all primes $p > P_*$ has exponent $m(\beta_0 - 1 - \sigma) \le 2(\frac{5}{8} - 1 - \frac{3}{8}) = -\frac{3}{2} < -1$. Hence $H_{\ge 2}(s)$ converges absolutely and uniformly on $\mathrm{Re}\,s \ge \frac{3}{8}$ with $\|H_{\ge 2}(s)\| \le C_2$.
- *Linear selection discrepancy $H_1$:* Factoring out only the real power $p^{-\sigma}$ at $s = \sigma + i\tau$ ($\sigma > \frac{\beta_0}{2}$), Stieltjes integration by parts in $x$ gives
  $$H_1(\sigma + i\tau) = \sigma \int_{P_*}^\infty D(x, \tau)\,x^{-\sigma - 1}\,dx,$$
  with NO $|\tau|$ prefactor! Since $\frac{\beta_0}{2} < \frac{5}{16} < \frac{3}{8}$, for $\frac{3}{8} \le \sigma \le 2$ we have $\|H_1(\sigma + i\tau)\| \le 2 C_0 \sqrt{\log(|\tau| + 2)} \int_1^\infty (\log x + 1) x^{\frac{5}{16} - \frac{3}{8} - 1}\,dx = C_3 \sqrt{\log(|\tau| + 2)}$. Hence $\|\exp(H_1(s) + H_{\ge 2}(s))\| \le e^{C_2 + C_3\sqrt{\log(|\tau| + 2)}} = O_\varepsilon((1 + |\tau|)^{\varepsilon / 3})$ for every $\varepsilon > 0$.
- *Shifted inverse-zeta cofactor:* Set $\sigma_1 := \max(\frac{3}{8}, \frac{1}{2}(\Theta + \beta_0 - \frac{1}{2}))$. Since $\Theta < 1$ and $\beta_0 < \frac{3}{2} - \Theta$, we have $\Theta + \beta_0 - \frac{1}{2} < 1$, so $\sigma_1 < \frac{1}{2}$, and for all $s$ with $\mathrm{Re}\,s \ge \sigma_1$,
  $$\mathrm{Re}(s + 1 - \rho_0) = \mathrm{Re}(s + 1 - \bar\rho_0) \ge \sigma_1 + 1 - \beta_0 \ge \Theta + \frac{1}{2}\Bigl(\frac{3}{2} - \Theta - \beta_0\Bigr) > \Theta.$$
  Thus neither $\zeta(s + 1 - \rho_0)$ nor $\zeta(s + 1 - \bar\rho_0)$ vanishes on $\mathrm{Re}\,s \ge \sigma_1$, while $\mathrm{posFiniteFactor}\,P_*\,\rho_0\,s$ has poles only on $\mathrm{Re}\,s = \beta_0 - 1 < 0$ and is bounded by $O(1)$ on $\mathrm{Re}\,s \ge \frac{3}{8}$. By `exists_zeta_lower_bound_subpolynomial_of_zeroFree` (`InvZetaAbscissaSubpolynomial.lean:440`), $\|\mathrm{invZeta}(s + 1 - \rho_0)\| = O_\varepsilon((1 + |\mathrm{Im}\,s|)^{\varepsilon / 3})$ and $\|\mathrm{invZeta}(s + 1 - \bar\rho_0)\| = O_\varepsilon((1 + |\mathrm{Im}\,s|)^{\varepsilon / 3})$ uniformly on $\sigma_1 \le \mathrm{Re}\,s \le 2$ for every $\varepsilon > 0$.
Multiplying the three factors gives $\|M_B(s)\| \le K_\varepsilon (1 + |\mathrm{Im}\,s|)^\varepsilon$ uniformly on $\sigma_1 \le \mathrm{Re}\,s \le 2$ for every $\varepsilon > 0$. Furthermore, at $s = \rho_0$, $\mathrm{invZeta}(\rho_0 + 1 - \rho_0) = \mathrm{invZeta}(1) = 0$, so $\zeta_B^{\mathrm{ext}}(\rho_0) = 0$ while $\zeta(\rho_0) \ne 0$; thus `IsIntegerNormFakeAt B β_c` holds (and $A > 0$ by Theorem I.1).

**Step 4 (Subpolynomial critical-line defect bounds).** Since $e(p) \in \mathbb{Z}$ and the prime-power weights of `posTruncatedZeta` are real, $M_B(\bar s) = \overline{M_B(s)}$. Applying Lemma 1.2(2) on $s = \frac{1}{2} + 2it$ yields
$$\|g(t)\| = 2\,\bigl|\zeta\!\left(\tfrac{1}{2} + 2it\right)\bigr|\,\bigl|\mathrm{Im}\,M_B\!\left(\tfrac{1}{2} + 2it\right)\bigr| \le 2 K_{\varepsilon / 3}\,\bigl|\zeta\!\left(\tfrac{1}{2} + 2it\right)\bigr|\,(1 + 2|t|)^{\varepsilon / 3}.$$
By the classical approximate functional equation / second moment on the critical line (`SmoothAFEZetaStripBound.lean`), $\frac{1}{2T}\int_{-T}^T |\zeta(\frac{1}{2} + 2it)|^2\,dt = O(\log T)$ for $T \ge 2$, whence $\frac{1}{2T}\int_{-T}^T \|g(t)\|^2\,dt \le C_\varepsilon (1 + T)^{2\varepsilon/3}\log T = O_\varepsilon(T^\varepsilon)$ for every $\varepsilon > 0$. Pointwise, `exists_norm_riemannZeta_le_interp` (`ZetaStripInterpolation.lean`) supplies $|\zeta(\frac{1}{2} + 2it)| \ll (1 + |t|)^{1/3}$, giving $\|g(t)\| = O_\varepsilon(|t|^{1/3 + \varepsilon})$ unconditionally (and $O_\varepsilon(|t|^\varepsilon)$ under Lindelöf/RH). $\square$

---

## 3. Part II: Countable Beurling Systems with Real Prime Norms and Real Weights

### Theorem II.1 (Unconditional $O(|t|^{-1/2+\varepsilon})$ Rigidity for Unweighted Countable Beurling Systems) `[PROVED HERE]`

Let `(B : RHTower.BeurlingSystem) [Countable B.Label]` (`BeurlingSystemGibbsGauge.lean:19`) satisfy $\sum_{x \in B.\mathrm{Integer}} (B.\mathrm{intNorm}\,x)^{-3/2} < \infty$ (in particular, any countable Beurling system with count rate $\beta_c < 1$ or $N_B(x) = O(x)$), and suppose $\zeta_B$ continues to `verticalStrip (1/2) (3/2)` in the Hamburger strip class with critical-line FE defect $g$ satisfying

$$\|g(t)\| \le C_g (1 + |t|)^{-1/2 + \varepsilon_0} \qquad (\forall t \in \mathbb{R})$$

for some $\varepsilon_0 < \frac{1}{2}$. Then $\beta = \frac{1}{2}$, $\zeta_B(s) = \zeta(s)$ on $\mathrm{Re}\,s > 1$ (hence identically on the strip), and $B.\mathrm{Label}$ is norm-equivalent to the rational primes. Consequently, **no** such countable Beurling system can have a fake zero in $\mathrm{Re}\,s > \frac{1}{2}$.

**Proof.**
Without loss of generality assume $\varepsilon_0 \in (0, \frac{1}{2})$ (if $\varepsilon_0 \le 0$, increase $\varepsilon_0$ to $\frac{1}{4}$). Note first that $\beta \in \mathbb{R}$ by reality of $\nu_B := \mathrm{beurlingSystemIntegerMeasure}\,B$ (`theta_defect_beta_real`), and $g$ is Abel-sublinear since $\delta \int_{\mathbb{R}} (1 + |t|)^{-1/2 + \varepsilon_0} e^{-\delta|t|}\,dt = O(\delta^{1/2 - \varepsilon_0}) \to 0$.

**Step 1 (Closed-form double-IBP formula for interior tent errors).** For any $0 < h \le 1$ and $y > h$ ($n := y / h > 1$), `tent_pairing_identity_of_polynomial_defect` (`FiniteEnergyDefectsObeyTheTentIdentity.lean:177`) holds for all $\varepsilon \in (0, 1]$ without any $L^2$ assumption on $g$:
$$\int_{\mathbb{R}} \Bigl(\int_{-1}^1 \mathrm{tentSeriesKernel}\,h\,(y/h)\,\varepsilon\,s\,u\,ds\Bigr)\,d\nu_B(u) = \int_{\mathbb{R}} \Bigl(\int_{-1}^1 \mathrm{tentDualKernel}\,h\,(y/h)\,\varepsilon\,s\,u\,ds\Bigr)\,d\nu_B(u) + \int_{-1}^1 \mathrm{tentPolarKernel}\,h\,\beta\,(y/h)\,\varepsilon\,s\,ds + \int_{-1}^1 \mathrm{tentDefectKernel}\,g\,h\,(y/h)\,\varepsilon\,s\,ds.$$
Let $\tau_\varepsilon(w) := h\varepsilon + i w$ for $w \in \mathbb{R}$. Writing $J_g(\tau) = \frac{1}{2\pi}\int_{\mathbb{R}} g(t)\,\mathrm{boundaryPairKernel}(2t, 1)\,\tau^{-\frac{1}{2} + 2it}\,dt$ ($\mathrm{Re}\,\tau > 0$) and integrating $(1 - |s|)\tau_\varepsilon(y + h s)^{-\frac{1}{2} + 2it}$ by parts twice on $[-1, 0]$ and $[0, 1]$ ($\frac{d}{ds}\tau_\varepsilon(y + h s) = i h$; boundary terms at $s = 0$ cancel and at $s = \pm 1$ vanish), Fubini's theorem gives for every $\varepsilon > 0$:
$$\int_{-1}^1 \mathrm{tentDefectKernel}\,g\,h\,(y/h)\,\varepsilon\,s\,ds = \mathrm{Re}\left(-\frac{1}{2\pi h}\int_{-\infty}^\infty g(t)\,\mathrm{boundaryPairKernel}(2t, 1)\,\frac{\tau_\varepsilon(y + h)^{\frac{3}{2} + 2it} - 2\tau_\varepsilon(y)^{\frac{3}{2} + 2it} + \tau_\varepsilon(y - h)^{\frac{3}{2} + 2it}}{(\frac{1}{2} + 2it)(\frac{3}{2} + 2it)}\,dt\right).$$
By `norm_boundaryPairKernel_le` (`TheBoundaryPreservesDefectEnergy.lean:168`), $\|\mathrm{boundaryPairKernel}(2t, 1)\,\tau_\varepsilon(w)^{\frac{3}{2} + 2it}\| \le 3|\tau_\varepsilon(w)|^{3/2} \le 3(y + h + 1)^{3/2}$ uniformly for $\varepsilon \in [0, 1]$ and $w \in [y - h, y + h]$, while $|(\frac{1}{2} + 2it)(\frac{3}{2} + 2it)| \ge \frac{3}{4} + 4t^2$. Since $\|g(t)\|/(1 + t^2) \ll (1 + |t|)^{-5/2 + \varepsilon_0} \in L^1(\mathbb{R})$, Dominated Convergence sends $\varepsilon \to 0^+$ directly to $\tau_0(w) = i w$ ($w \ge y - h > 0$), giving the exact tent identity
$$\mathrm{tentAtomMass}\,B.\mathrm{intNorm}\,h\,y = \mathrm{tentRecurrentPart}\,B.\mathrm{intNorm}\,\beta\,h\,y + E_g(h, y),$$
where
$$E_g(h, y) := \mathrm{Re}\left(-\frac{1}{2\pi h}\int_{-\infty}^\infty g(t)\,\mathrm{boundaryPairKernel}(2t, i)\,\frac{(y + h)^{\frac{3}{2} + 2it} - 2 y^{\frac{3}{2} + 2it} + (y - h)^{\frac{3}{2} + 2it}}{(\frac{1}{2} + 2it)(\frac{3}{2} + 2it)}\,dt\right).$$

**Step 2 (Uniform small-width decay of $E_g(h, y)$).** Fix $\eta \in (0, \frac{1}{4})$. For any $y \in [\eta/2, 1]$ and $0 < h \le \eta/4$ (so $y - h \ge y/2 \ge \eta/4$), split the $t$-integral in $E_g(h, y)$ at $|t| = 1/h$:
- For $|t| \le 1/h$, second-order Taylor remainder on $w \mapsto w^{\frac{3}{2} + 2it}$ over $[y - h, y + h]$ bounds the numerator by $h^2 |(\frac{3}{2} + 2it)(\frac{1}{2} + 2it)| (y/2)^{-1/2}$, canceling the denominator and contributing $\ll \eta^{-1/2} h \int_{|t| \le 1/h} (1 + |t|)^{-1/2 + \varepsilon_0}\,dt \ll \eta^{-1/2} h^{1/2 - \varepsilon_0}$.
- For $|t| > 1/h$, bounding the numerator by $4(2y)^{3/2} \le 12$ contributes $\ll h^{-1} \int_{|t| > 1/h} |t|^{-5/2 + \varepsilon_0}\,dt \ll h^{1/2 - \varepsilon_0}$.
Hence $|E_g(h, y)| \le C_* \eta^{-1/2} h^{1/2 - \varepsilon_0} \to 0$ as $h \to 0^+$, uniformly for all $y \in [\eta/2, 1]$.

**Step 3 (Sublinear $L^2$-energy of $E_g(h, y)$ as $y \to \infty$ and unit-gap vanishing).** Fix $0 < h \le 1$. On any dyadic shell $y \in [W, 2W]$ ($W \ge 2h$), split $g = g_{\le W/h} + g_{> W/h}$ at $|t| = W/h$:
- Since $g_{\le W/h} \in L^1(\mathbb{R}) \cap L^2(\mathbb{R})$ with $\|g_{\le W/h}\|_{L^2}^2 \ll (W/h)^{2\varepsilon_0}$, `integral_norm_sq_defectBoundary` (`TheBoundaryPreservesDefectEnergy.lean:223`) and Young's convolution inequality give $\int_W^{2W} |E_{g_{\le W/h}}(h, y)|^2\,dy \le \frac{h^2}{\pi}\|g_{\le W/h}\|_{L^2}^2 \ll_h W^{2\varepsilon_0}$.
- For $g_{> W/h}$ and each shift $\sigma \in \{-1, 0, +1\}$, writing $(y + \sigma h)^{\frac{3}{2} + 2it} = (y + \sigma h)^2 (y + \sigma h)^{-\frac{1}{2} + 2it}$ expresses that term as $(y + \sigma h)^2 / h \le 9 W^2 / h$ times `mellinInv (1/2)` of $\mathbf{1}_{|t| > W/h} \frac{g(t)\,\mathrm{boundaryPairKernel}(2t, i)}{(\frac{1}{2} + 2it)(\frac{3}{2} + 2it)}$; Mellin–Plancherel gives $\int_W^{2W} |E_{g_{> W/h}}(h, y)|^2\,dy \ll \frac{W^4}{h^2}\int_{|t| > W/h} t^{-5 + 2\varepsilon_0}\,dt \ll_h W^{2\varepsilon_0}$.
Summing $W = 2^j h \le Y$ gives $\frac{1}{Y}\int_{2h}^Y (|E_g(h, y)|^2 + |E_g(h/2, y)|^2)\,dy = O_h(Y^{-(1 - 2\varepsilon_0)}) \to 0$ as $Y \to \infty$ (since $\varepsilon_0 < \frac{1}{2}$).
Now let $P_1(y) := \mathrm{tentRecurrentPart}\,B.\mathrm{intNorm}\,\beta\,h\,y$ and $P_2(y) := \mathrm{tentRecurrentPart}\,B.\mathrm{intNorm}\,\beta\,(h/2)\,y$. Suppose $P_1(y_0) < \frac{1}{4}$. For any $\delta \in (0, \frac{1}{4} - P_1(y_0))$, uniform continuity of $P_1, P_2$ and relative density of common $(\delta/2)$-almost-periods (`exists_common_almostPeriods`) supply $L > 0$ and $\rho \in (0, 1)$ such that every interval $[k L, (k + 1)L]$ ($k \in \mathbb{N}$) contains a subinterval $I_k = [\tau_k + y_0, \tau_k + y_0 + \rho]$ of length $\rho$ on which $|P_j(x) - P_j(y_0)| < \delta$ ($j = 1, 2$). Since $\bigcup_{k \le Y/L} I_k$ has measure $\gg_{\rho, L} Y$ while $\int_{2h}^Y (|E_g(h, x)|^2 + |E_g(h/2, x)|^2)\,dx = o(Y)$, Chebyshev's inequality yields $x \in \bigcup_k I_k$ ($x > h + 1$) with $|E_g(h, x)| + |E_g(h/2, x)| < \min(\frac{1}{4} - P_1(y_0) - \delta, \delta)$. Then $\mathrm{tentAtomMass}\,B.\mathrm{intNorm}\,h\,x = P_1(x) + E_g(h, x) < \frac{1}{4}$, so the discrete unit-atom floor `tentAtomMass_half_eq_zero_of_lt` (`TentRecurrenceOfIntegrableDefects.lean`) forces $\mathrm{tentAtomMass}\,B.\mathrm{intNorm}\,(h/2)\,x = 0$, whence $|P_2(y_0)| \le |P_2(x)| + \delta = |E_g(h/2, x)| + \delta < 2\delta$. Letting $\delta \to 0^+$ proves $P_2(y_0) = 0$.
For any $\eta \in (0, \frac{1}{8})$, choose $M \ge 8$ with $\eta = 1/M$ and $R \in \mathbb{N}$ large enough that $\delta_* := \eta / R = 1/(M R)$ satisfies $|E_g(2\delta_*, y)| < \frac{1}{4}$ for all $y \in [\eta/2, 1]$ by Step 2. Since $\mathrm{tentAtomMass} = 0$ on $(0, 1)$, $P_{\mathrm{2\delta_*}}(y) = -E_g(2\delta_*, y) < \frac{1}{4}$, so $P_{\delta_*}(y) = 0$ and hence $E_g(\delta_*, y) = 0$ for all $y \in [\eta, 1 - \eta]$ (and for $y \in [-(1 - \eta), -\eta]$ by evenness of $\mathrm{Re}\,J_g(\varepsilon + i y)$, `defectLaplace_re_neg_of_theta_defect`).

**Step 4 (Finite Schauder hat decomposition of the origin Fejér tent and conclusion).** On $[-1, 1]$, decompose $(1 - |y|)_+ = \Psi_\eta(y) + \Phi_{\eta,\mathrm{end}}(y) + \Phi_{\eta, 0}(y)$, where $\Psi_\eta$ is continuous piecewise-linear with nodes $\{ \pm\eta, \pm 2\eta, \pm(1 - 2\eta), \pm(1 - \eta) \} \subset \delta_* \mathbb{Z}$, equals $1 - |y|$ on $2\eta \le |y| \le 1 - 2\eta$, and vanishes for $|y| \le \eta$ and $|y| \ge 1 - \eta$.
- Because $\Psi_\eta$ is supported on $[\eta, 1 - \eta] \cup [-(1 - \eta), -\eta]$ with grid nodes in $\delta_* \mathbb{Z}$, $\Psi_\eta(y) = \sum_{\eta < |j\delta_*| < 1 - \eta} \Psi_\eta(j\delta_*)\,\Lambda_{\delta_*}(y - j\delta_*)$ has $\lim_{\varepsilon \to 0^+} \int_{-1}^1 \Psi_\eta(y)\,\mathrm{Re}\,J_g(\varepsilon + i y)\,dy = \sum \Psi_\eta(j\delta_*) E_g(\delta_*, j\delta_*) = 0$.
- The endpoint piece is $\Phi_{\eta,\mathrm{end}}(y) = \eta\,\Lambda_\eta(y - (1 - \eta)) + \eta\,\Lambda_\eta(y + (1 - \eta))$, whose $\varepsilon \to 0^+$ pairing equals $2\eta\,E_g(\eta, 1 - \eta) = O(\eta^{3/2 - \varepsilon_0})$ by Step 2.
- The origin piece is $\Phi_{\eta, 0}(y) = 2(1 - \eta)\Lambda_{2\eta}(y) - (1 - 2\eta)\Lambda_\eta(y)$. For any $a \in \{\eta, 2\eta\}$ and $\varepsilon \in (0, a]$, double integration by parts of $\int_{-a}^a (1 - |y|/a)\,\tau(y)^{-\frac{1}{2} + 2it}\,dy$ along $\tau(y) = \varepsilon + i y$ ($\mathrm{Re}\,\tau(y) = \varepsilon > 0$ on all $[-a, a]$) bounds $|\int_{-a}^a (1 - |y|/a)\,\mathrm{Re}\,J_g(\varepsilon + i y)\,dy| \le \frac{12 a^{1/2}}{\pi}\int_{\mathbb{R}} \frac{\|g(t)\|}{\frac{3}{4} + 4t^2}\,dt = O(a^{1/2})$ uniformly for $\varepsilon \in (0, a]$.
Thus $\limsup_{\varepsilon \to 0^+} |\int_{-1}^1 \mathrm{fejerDefectKernel}\,g\,\varepsilon\,s\,ds| = O(\eta^{1/2}) \to 0$ as $\eta \to 0^+$. As in `beurling_intNorm_nat_of_finiteEnergy_theta_defect` (`FiniteEnergyDefectsForceIntegerSupport.lean:150`), `fejer_pairing_identity_of_theta_defect` forces $\int_{\mathbb{R}} \mathrm{sinc}^2(\pi u)\,d\nu_B(u) = 0$, so every $x \in B.\mathrm{Integer}$ has $B.\mathrm{intNorm}\,x \in \mathbb{N}_{\ge 1}$. Grouping fibers $a(m) := \#\{x \in B.\mathrm{Integer} : B.\mathrm{intNorm}\,x = m\}$ ($a(1) = 1$) and applying `coeff_eq_of_critical_line_even_sublinear_defect` (`HamburgerStabilityCriticalLine.lean:736`) yields $a(m) = 2\beta = 1$ for all $m \ge 1$; `beurlingSystem_rigidity_of_integer_measure_eq` (`FiniteEnergyFunctionalEquationsDetermineThePrimes.lean:167`) then gives $\beta = \frac{1}{2}$, $\zeta_B = \zeta$, and norm-equivalence of $B.\mathrm{Label}$ to the rational primes. $\square$

---

### Theorem II.2 (Integer-Norm Countable Beurling Systems with Real Weights) `[PROVED HERE]`

1. **(Universal Abel-sublinear impossibility for real weights on $\mathbb{N}$):** Let $a : \mathbb{N} \to \mathbb{R}$ be the Dirichlet coefficients of any integer-norm countable Beurling system with arbitrary real prime/prime-power weights ($a(1) = 1$, $\sum_{n=1}^\infty |a(n)| n^{-\sigma} < \infty$ for $\sigma > 1$, either $A > 0$ or $A = 0$) continuing to `verticalStrip (1/2) (3/2)` in the Hamburger strip class with a fake zero $\rho_0$ in $\mathrm{Re}\,s > \frac{1}{2}$. Then $g$ cannot be Abel-sublinear; in particular, $g = O(|t|^{-1/2 + \varepsilon})$ ($\varepsilon < \frac{1}{2}$) and $g(t) = o(1)$ are unconditionally impossible.
2. **(Bounded defect $g = O(1)$ for signed real weights at $A = 0$):** Fix any $\gamma_0 \ne 0$ with $\zeta(\frac{3}{4} + i\gamma_0) \ne 0$ and set $\rho_0 := \frac{3}{4} + i\gamma_0$. Define the countable prime-power system on $\{2^r : r \ge 1\}$ with real weights $\tilde w_r := -\frac{2}{r}\cdot 2^{3r/4}\cos(r\gamma_0 \log 2) \in \mathbb{R}$ (equivalently, by Möbius inversion, Euler-product prime weights $w_m \in \mathbb{R}$ on norms $2^m$ satisfying $\prod_{m=1}^\infty (1 - 2^{-ms})^{-w_m} = \exp(\sum_{r=1}^\infty \tilde w_r 2^{-rs})$). Its zeta function is the entire 3-term Dirichlet polynomial
   $$F_0(s) := \bigl(1 - 2^{\rho_0 - s}\bigr)\bigl(1 - 2^{\bar\rho_0 - s}\bigr) = 1 - 2\cdot 2^{3/4}\cos(\gamma_0\log 2)\,2^{-s} + 2^{3/2}\,4^{-s},$$
   which has count rate $N(x) = 0\cdot x + O(1)$ ($\beta_c = 0 < 1$), fake zeros at $\rho_0, \bar\rho_0$ ($\mathrm{Re}\,\rho_0 = \frac{3}{4} > \frac{1}{2}$), and **bounded** critical-line FE defect $\|g(t)\| \le 2(1 + 2^{1/4})^2$ for all $t \in \mathbb{R}$.

**Proof.**
1. If $g$ were Abel-sublinear, `coeff_eq_of_critical_line_even_sublinear_defect` (`HamburgerStabilityCriticalLine.lean:736`) would give $a(n) = 2\beta$ for all $n \ge 1$. Since $a(1) = 1$, $2\beta = 1$ and $a(n) = 1$ for all $n \ge 1$, so $\zeta_a(s) = \zeta(s)$, contradicting $\zeta_a(\rho_0) = 0 \ne \zeta(\rho_0)$.
2. For $\mathrm{Re}\,s > \frac{3}{4}$, $-\log(1 - 2^{\rho_0 - s}) - \log(1 - 2^{\bar\rho_0 - s}) = \sum_{r=1}^\infty \frac{2}{r} 2^{3r/4}\cos(r\gamma_0\log 2)\,2^{-rs}$, so $\exp(\sum_{r=1}^\infty \tilde w_r 2^{-rs}) = F_0(s)$. Since $\sum_{m=1}^\infty w_m (-\log(1 - 2^{-ms})) = \sum_{r=1}^\infty \bigl(\sum_{m \mid r} \frac{m w_m}{r}\bigr) 2^{-rs}$, setting $w_m := \frac{1}{m}\sum_{d \mid m} \mu(m/d)\,d\,\tilde w_d \in \mathbb{R}$ gives $r\tilde w_r = \sum_{m \mid r} m w_m$, $|w_m| \le 4\cdot 2^{3m/4}$, and $\prod_{m=1}^\infty (1 - 2^{-ms})^{-w_m} = F_0(s)$ absolutely on $\mathrm{Re}\,s > \frac{3}{4}$. Since $F_0(s)$ is entire and bounded on vertical strips, $E(s) := \Gamma_{\mathbb{R}}(s) F_0(s)$ satisfies Definition 1.1 with $\beta = 0$, $F_0(\rho_0) = 0 \ne \zeta(\rho_0)$, $|N(x)| \le 1 + 2\cdot 2^{3/4} + 2^{3/2}$ for all $x \ge 1$, and on $s = \frac{1}{2} + 2it$, $|F_0(\frac{1}{2} \pm 2it)| \le (1 + 2^{1/4})^2$, so $\|g(t)\| \le |F_0(\frac{1}{2}+2it)| + |F_0(\frac{1}{2}-2it)| \le 2(1 + 2^{1/4})^2$. $\square$

---

### Theorem II.3 (Unconditional Arbitrarily Slow Unbounded $g(t)$ for Positive-Real-Weighted Countable Beurling Systems — No $\Theta$ Case Split) `[PROVED HERE]`

Let $\Phi : [0, \infty) \to [1, \infty)$ be **any** nondecreasing unbounded function ($\lim_{t \to \infty} \Phi(t) = +\infty$, e.g. $\Phi(t) = \max(1, \log\log(t + 10)) = o(|t|^\varepsilon)$ for every $\varepsilon > 0$). Fix any $\mu \in (\frac{1}{3}, \frac{1}{2})$, $\nu_0 \in (0, 3\mu - 1)$, and $\gamma \ne 0$ such that $\zeta((1 - \mu) + i\gamma) \ne 0$, and set $\rho_0 := (1 - \mu) + i\gamma$ ($\mathrm{Re}\,\rho_0 = 1 - \mu \in (\frac{1}{2}, \frac{2}{3})$).

Then unconditionally (without any case split on $\Theta$) there exists a countable family of real prime generators $\{p_{m, j}\}_{m \ge 0,\, 1 \le j \le M_m}$ with strictly positive real weights $w_{m, j} > 0$ such that:
1. $p_{m, j} \ge e^{10} > 1$, $\{ (m, j) : p_{m, j} \le X \}$ is finite for every $X \ge 1$ (`HTGeometry.Beurling.System`, `BeurlingCrossSystemBlindness.lean:626`), and $\{\log p_{m, j}\}$ is $\mathbb{Q}$-linearly independent;
2. The Euler product $\zeta_{P, w}(s) := \prod_{m, j} (1 - p_{m, j}^{-s})^{-w_{m, j}}$ converges on $\mathrm{Re}\,s > 1$, extends meromorphically to $\mathrm{Re}\,s > \frac{1}{3}$ with a single simple pole at $s = 1$ of residue $A > 0$, and satisfies $\zeta_{P, w}(\rho_0) = \zeta_{P, w}(\bar\rho_0) = 0 \ne \zeta(\rho_0)$;
3. Its generalized integer counting function $N_{P, w}(x) := (\mathrm{beurlingIntegerMeasure}\,P)([1, x])$ satisfies $N_{P, w}(x) = A x + O(x^{4/5})$ ($\beta_c = \frac{4}{5} < 1$);
4. $\zeta_{P, w}$ satisfies Definition 1.1 on `verticalStrip (1/2) (3/2)` with critical-line FE defect $g(t)$ obeying
   $$\|g(t)\| \le \Phi(|t|) \qquad \text{for all } |t| \ge T_0.$$

**Proof.**
Replace $\Phi(t)$ by $\tilde\Phi(t) := \max\bigl(1, \min(\Phi(t), \log(t + 3))\bigr)$, which remains nondecreasing and unbounded with $1 \le \tilde\Phi(t) \le \min(\Phi(t), \log(t + 3))$.

**Step 1 (Möbius prime-power inversion of `overRegularZeta`).** Let $w_{\mathrm{cont}}(v) := \mathrm{BeurlingOverRegularIntegers.primeDensity}\,\mu\,\nu_0\,\gamma\,v \ge 0$ (`BeurlingOverRegularIntegersOffLineZeros.lean:54, 94`), whose Laplace exponential on $\mathrm{Re}\,s > 1$ is
$$\zeta_{\mathrm{cont}}(s) := \mathrm{overRegularZeta}\,\mu\,\nu_0\,\gamma\,s = \frac{((s - (1 - \mu))^2 + \gamma^2)(s + 4\mu - 1)}{(s - 1)(s + 3\mu - 1 - \nu_0)(s + 3\mu - 1 + \nu_0)} \qquad (\text{`:184, 189`}).$$
Since $p_1 := 3\mu - 1 - \nu_0 > 0$ and $p_2 := 3\mu - 1 + \nu_0 > 0$, $\zeta_{\mathrm{cont}}$ is holomorphic on $\{\mathrm{Re}\,s > -p_1\} \setminus \{1\} \supset \{\mathrm{Re}\,s > \frac{1}{3}\} \setminus \{1\}$, vanishes at $\rho_0, \bar\rho_0$, has positive residue $\rho_{\mathrm{res}} > 0$ at $s = 1$, and satisfies $|\zeta_{\mathrm{cont}}(s)| \le C_{\mathrm{cont}}$ uniformly on $\{\frac{2}{5} \le \mathrm{Re}\,s \le \frac{3}{2},\, |s - 1| \ge \frac{1}{4}\}$ because numerator and denominator both have degree $3$.
Fix $u_0 \ge 10$ large enough that $2 e^{-\mu u_0} + e^{-4\mu u_0} \le \frac{1}{2}$, so $\frac{1}{2}\frac{e^v}{v} \le w_{\mathrm{cont}}(v) \le \frac{2 e^v}{v}$ for all $v \ge u_0$. Set $\tilde w(v) := \mathbf{1}_{v \ge u_0} w_{\mathrm{cont}}(v)$ and define on $[u_0, \infty)$:
$$\pi_0(v) := \sum_{d = 1}^{\lfloor v / u_0 \rfloor} \frac{\mu(d)}{d^2}\,\tilde w(v / d).$$
For $v \ge u_0 \ge 10$, the $d \ge 2$ sum has magnitude at most $\sum_{2 \le d \le v/u_0} \frac{1}{d^2}\frac{2 d e^{v/2}}{v} \le \frac{2(1 + \log v)e^{v/2}}{v} \le \frac{1}{4}\frac{e^v}{v}$, so $\frac{1}{4}\frac{e^v}{v} \le \pi_0(v) \le \frac{3 e^v}{v}$ (strictly positive!). Moreover, for every $v \ge u_0$, Möbius inversion gives $\sum_{r = 1}^{\lfloor v / u_0 \rfloor} \frac{1}{r^2} \pi_0(v / r) = \sum_{n=1}^\infty \frac{\tilde w(v/n)}{n^2}\sum_{r d = n} \mu(d) = w_{\mathrm{cont}}(v)$. Substituting $v = r y$ ($dv = r\,dy$) yields for all $\mathrm{Re}\,s > 1$:
$$\sum_{r = 1}^\infty \frac{1}{r}\int_{u_0}^\infty e^{-r s y}\,\pi_0(y)\,dy = \int_{u_0}^\infty e^{-s v} w_{\mathrm{cont}}(v)\,dv = \log \zeta_{\mathrm{cont}}(s) - I_0(s), \qquad I_0(s) := \int_0^{u_0} e^{-s v} w_{\mathrm{cont}}(v)\,dv.$$
Since $w_{\mathrm{cont}}(v) = O(v)$ near $v = 0$, $I_0(s)$ is entire and $|I_0(s)| \le I_0(0) < \infty$ on $\mathrm{Re}\,s \ge 0$.

**Step 2 (Height-graded $\mathbb{Q}$-independent discretization).** Partition $[u_0, \infty)$ into unit intervals $J_m := [u_0 + m, u_0 + m + 1]$ ($m \ge 0$) and set
$$B_m^* := 2 \sum_{r = 1}^\infty \frac{1}{r} e^{-\frac{2}{5} r (u_0 + m)} \int_{J_m} \pi_0(y)\,dy < \infty,$$
which depends only on $(\mu, \nu_0, \gamma, u_0, m)$. Since $\tilde\Phi(t) \to +\infty$, choose a strictly increasing sequence $1 \le T_0 < T_1 < T_2 < \dots \to +\infty$ such that for every $k \ge 0$,
$$\tilde\Phi(T_k) \ge 8 C_{\mathrm{cont}} \exp\Bigl(I_0(0) + 1 + \sum_{m = 0}^k B_m^*\Bigr).$$
Now subdivide each $J_m$ into $M_m$ equal subintervals $I_{m, j}$ ($1 \le j \le M_m$) of length $1 / M_m$, where
$$M_m := \max\left(\lceil e^{4m}\rceil,\; \left\lceil 2^{m + 3}(2 + 2 T_m)\Bigl(\int_{J_m} \pi_0(y)\,dy\Bigr)\sum_{r = 1}^\infty e^{-\frac{2}{5} r (u_0 + m)}\right\rceil\right).$$
Since each open interval $\mathrm{int}(I_{m, j})$ is uncountable while the $\mathbb{Q}$-span of previously chosen points is countable, select inductively $u_{m, j} \in \mathrm{int}(I_{m, j})$ so that $\{u_{m, j}\}$ is $\mathbb{Q}$-linearly independent, and set $p_{m, j} := e^{u_{m, j}} \ge e^{u_0 + m}$ and $w_{m, j} := \int_{I_{m, j}} \pi_0(y)\,dy > 0$. Clearly $\{ (m, j) : p_{m, j} \le X \}$ is finite for all $X$.

**Step 3 (Continuation to $\mathrm{Re}\,s > \frac{1}{3}$ and $\tilde\Phi(|t|)$ defect bound).** For $\mathrm{Re}\,s > 1$, $\log \zeta_{P, w}(s) = \log \zeta_{\mathrm{cont}}(s) - I_0(s) + \sum_{m=0}^\infty \mathcal{E}_m(s)$, where
$$\mathcal{E}_m(s) := \sum_{j = 1}^{M_m} \sum_{r = 1}^\infty \frac{1}{r}\int_{I_{m, j}} \bigl(e^{-r s u_{m, j}} - e^{-r s y}\bigr)\pi_0(y)\,dy.$$
Since $|e^{-r s u_{m, j}} - e^{-r s y}| \le \frac{r |s|}{M_m} e^{-r(\mathrm{Re}\,s)(u_0 + m)}$ and $M_m \ge e^{4m}$ while $\int_{J_m} \pi_0(y)\,dy \le 3 e^{u_0 + m + 1}$, for any $\sigma > \frac{1}{3}$ we have $|\mathcal{E}_m(s)| \ll |s| e^{(1 - \sigma - 4)m} = |s| e^{-(3 + \sigma)m}$, so $\sum_{m=0}^\infty \mathcal{E}_m(s)$ converges locally uniformly on $\mathrm{Re}\,s > \frac{1}{3}$. Thus $\zeta_{P, w}(s) = \zeta_{\mathrm{cont}}(s)\exp(-I_0(s) + \mathcal{E}(s))$ continues meromorphically to $\mathrm{Re}\,s > \frac{1}{3}$ with sole pole at $s = 1$ of residue $A := \rho_{\mathrm{res}}\exp(-I_0(1) + \mathcal{E}(1)) > 0$, and vanishes at $\rho_0, \bar\rho_0$.
Now fix any $s = \sigma + 2it$ with $\frac{2}{5} \le \sigma \le \frac{3}{2}$, $|s - 1| \ge \frac{1}{4}$, and $|t| \ge T_0$, and choose the unique $k \ge 0$ with $T_k \le |t| < T_{k + 1}$.
- For $0 \le m \le k$, the triangle inequality $|e^{-r s u_{m, j}} - e^{-r s y}| \le 2 e^{-\frac{2}{5} r (u_0 + m)}$ gives $|\mathcal{E}_m(s)| \le B_m^*$.
- For $m \ge k + 1$, monotonicity gives $T_m \ge T_{k + 1} > |t|$, so $|s| \le \frac{3}{2} + 2|t| \le 2 + 2 T_m$; by definition of $M_m$, $|\mathcal{E}_m(s)| \le 2^{-(m + 3)}$, whence $\sum_{m = k + 1}^\infty |\mathcal{E}_m(s)| \le \frac{1}{4}$.
Consequently, $|\zeta_{P, w}(\sigma + 2it)| \le C_{\mathrm{cont}}\exp\bigl(I_0(0) + \sum_{m=0}^k B_m^* + \frac{1}{4}\bigr) \le \frac{1}{8}\tilde\Phi(T_k) \le \frac{1}{8}\tilde\Phi(|t|) \le \frac{1}{8}\log(|t| + 3)$. By Lemma 1.2(1), $\zeta_{P, w}$ satisfies Definition 1.1 on `verticalStrip (1/2) (3/2)` and for all $|t| \ge T_0$,
$$\|g(t)\| \le \bigl|\zeta_{P, w}\!\left(\tfrac{1}{2} + 2it\right)\bigr| + \bigl|\zeta_{P, w}\!\left(\tfrac{1}{2} - 2it\right)\bigr| \le \frac{1}{4}\tilde\Phi(|t|) \le \Phi(|t|).$$

**Step 4 (Count rate $N_{P, w}(x) = A x + O(x^{4/5})$).** Let $\nu := \mathrm{beurlingIntegerMeasure}\,P$ ($P := \sum_{m, j} \sum_{r=1}^\infty \frac{w_{m, j}}{r}\delta_{p_{m, j}^r} \ge 0$), so $N_{P, w}(x) = \nu([1, x])$ is monotone nondecreasing. By Riesz–Mellin inversion of order $2$ on $\mathrm{Re}\,s = 2$ and Cauchy's residue theorem shifting to $\mathrm{Re}\,s = \frac{2}{5}$ (where $|\zeta_{P, w}(\frac{2}{5} + i\tau)| \ll \log(|\tau| + 3)$, so $\int_{\mathbb{R}} \frac{|\zeta_{P, w}(\frac{2}{5} + i\tau)|}{|(\frac{2}{5}+i\tau)(\frac{7}{5}+i\tau)(\frac{12}{5}+i\tau)|}\,d\tau < \infty$, crossing only the simple pole at $s = 1$ of residue $A$),
$$N_2(x) := \int_1^x \int_1^y N_{P, w}(w)\,dw\,dy = \frac{1}{2\pi i}\int_{2 - i\infty}^{2 + i\infty} \frac{\zeta_{P, w}(s) x^{s + 2}}{s(s + 1)(s + 2)}\,ds = \frac{1}{6} A x^3 + O\bigl(x^{12/5}\bigr) \qquad (x \ge 1).$$
Taking forward and backward second differences of $N_2$ at step $h := x^{4/5}$ for $x \ge 8$ and using monotonicity $h^2 N_{P, w}(x) \le \int_0^h \int_0^h N_{P, w}(x + u_1 + u_2)\,du_1\,du_2 = N_2(x + 2h) - 2N_2(x + h) + N_2(x) = A h^2(x + h) + O(x^{12/5})$ and $h^2 N_{P, w}(x) \ge N_2(x) - 2N_2(x - h) + N_2(x - 2h) = A h^2(x - h) - O(x^{12/5})$ yields $|N_{P, w}(x) - A x| = O(h + x^{12/5} h^{-2}) = O(x^{4/5})$. $\square$

---

## 4. Part III: Complete Resolution of A151 & Unconditional World-I Corollaries

### Corollary III.1 (Resolution of A151: Critical-Line FE Defect of WZC Pair Twins and Quartet Edits) `[PROVED HERE]`

1. **WZC Pair Twin (`TwinsContinuePastTheLine.isFactorTwinOn_edit`, `:126`):** For $\rho = \beta_0 + i\gamma_0$ with $\frac{1}{2} < \beta_0 < \frac{14}{15}$ and $\zeta(\rho) \ne 0$, the greedy two-sided edit `B_pair := editSystem (edit ρ)` satisfies $\sigma_{\min}(\beta_0) = \max(\beta_0 - \frac{13}{30}, \frac{\beta_0}{2}) < \frac{1}{2}$ and $\zeta_{B_{\mathrm{pair}}}^{\mathrm{ext}}(s) = \zeta(s) M_{\mathrm{pair}}(s)$ on $\mathrm{Re}\,s > \sigma_{\min}(\beta_0)$ with $M_{\mathrm{pair}}(s) = C\,(s - \rho)(s - \bar\rho)\exp(K(s) + Q(s))$ ($C \in \mathbb{R}^\times$). By Lemma 1.2(2), its critical-line FE defect is
   $$g_{\mathrm{pair}}(t) = 2i\,C\,\zeta\!\left(\tfrac{1}{2} + 2it\right)\,\mathrm{Im}\Bigl(\bigl(-4t^2 + (\tfrac{1}{2} - \beta_0)^2 + \gamma_0^2 + 4i(\tfrac{1}{2} - \beta_0)t\bigr) e^{K(\frac{1}{2}+2it) + Q(\frac{1}{2}+2it)}\Bigr).$$
   In the greedy construction, $|S_{\mathrm{corr}}(x)| \le K_0 x^c$ controls only frequency $0$, leaving $K(\frac{1}{2}+2it) = s \int_1^\infty S_{\mathrm{corr}}(x) x^{-s-1}\,dx = O(1 + |t|)$ due to the uncancelled $s$-factor, while $(s - \rho)(s - \bar\rho)$ grows quadratically. Theorem I.4 resolves this exact WZC obstruction when $\Theta < 1$: replacing greedy rounding by multi-frequency `GroupedSelection` on `posTruncatedZeta` simultaneously replaces $(s - \rho)(s - \bar\rho)$ by $\mathrm{invZeta}(s + 1 - \rho)\,\mathrm{invZeta}(s + 1 - \bar\rho)$ and collapses $|H_1(\frac{1}{2}+2it)|$ from $O(|t|)$ to $O(\sqrt{\log(|t| + 2)})$.
2. **WZC Symmetric Quartet Edit (`exists_isEdit_zeros_zeta_and_quartet`, `TheFloorOfPrimeEditsWithACountRate.lean:112`):** For $\rho = (\frac{1}{2} + \delta) + i\gamma_0$ ($0 < \delta < \frac{1}{6}$, $\zeta(\rho) \ne 0$), the quartet polynomial $L_4(s) := (s - \rho)(s - \bar\rho)(s - (1 - \rho))(s - (1 - \bar\rho))$ satisfies $L_4(\frac{1}{2} + 2it) = |(\frac{1}{2} + 2it - \rho)(\frac{1}{2} + 2it - \bar\rho)|^2 > 0$ ($\mathrm{Im}\,L_4(\frac{1}{2} + 2it) \equiv 0$). Nevertheless, for **every** two-sided edit $B_{\mathrm{quartet}} = \mathrm{editSystem}\,e$ with count rate $\beta_c < 1$ realizing the quartet, its critical-line FE defect
   $$g_{\mathrm{quartet}}(t) = 2i\,C\,\zeta\!\left(\tfrac{1}{2} + 2it\right)\,L_4\!\left(\tfrac{1}{2} + 2it\right)\,\mathrm{Im}\bigl(e^{K_4(\frac{1}{2}+2it) + Q_4(\frac{1}{2}+2it)}\bigr)$$
   **cannot** vanish or even be bounded: adding the symmetric mirror zeros $\{1 - \rho, 1 - \bar\rho\}$ fails to restore the functional equation, and Theorem I.3 forces $\int_{\mathbb{R}} \|g_{\mathrm{quartet}}(t)\|^2 e^{-|t|/T}\,dt \ge \frac{A^2}{256\pi p_0} T\log T$ and $\limsup_{|t|\to\infty} \|g_{\mathrm{quartet}}(t)\|/\sqrt{\log |t|} > 0$.

**Proof.** Immediate from Lemma 1.2(2) (since $e(p) \in \mathbb{Z}$ makes $K(\bar s) = \overline{K(s)}$, $Q(\bar s) = \overline{Q(s)}$, and $C = M_{\mathrm{pair}}(1)/|1 - \rho|^2 \in \mathbb{R}^\times$ by positive real values on $s > 1$), $(1 - s - \rho)(1 - s - \bar\rho) = \overline{(s - (1 - \bar\rho))(s - (1 - \rho))}$ on $s = \frac{1}{2} + 2it$, and Theorem I.3 applied to $B_{\mathrm{quartet}}$. $\square$

---

### Corollary III.2 (Unconditional Resolution of the World-I Scenario Table & §2.10 Layer–Defect Calculus) `[PROVED HERE]`

Referring to the three scenarios in `obstacles-summary.md:684–689` and Criterion Q1 of `obstacles-summary.md` §2.10:

1. **Row 1 ("A two-sided edit fake exists with $g$ just outside $L^2$, say size $|t|^{-1/2+\varepsilon}$") is UNCONDITIONALLY FALSE:** By Theorems I.2 and I.3, finite-energy rigidity (`beurlingSystem_rigidity_of_finiteEnergy_defect`) is **not** sharp at the $L^2$ boundary for two-sided edits (nor for unweighted countable Beurling systems by Theorem II.1). Every fake two-sided edit is separated from $g = 0$ across the entire decaying regime $O(|t|^{-1/2+\varepsilon})$ ($\varepsilon < \frac{1}{2}$), across $o(1)$, and across $O(1)$ up to $\Omega(\sqrt{\log |t|})$. Consequently, approximate-FE methods whose critical-line error decays as $O(|t|^{-1/4})$ or $o(1)$ are **not** obstructed by any two-sided edit or unweighted countable Beurling model.
2. **Row 2 ("Two-sided edit fakes exist with polynomial $g$, and none with smaller $g$") is sharpened to the exact logarithmic-to-subpolynomial window:** No power lower bound $\|g(t)\| \gtrsim |t|^\alpha$ ($\alpha > 0$) holds in $L^2$-mean when $\Theta < 1$ (Theorem I.4 gives $\frac{1}{2T}\int_{-T}^T \|g\|^2\,dt = O_\varepsilon(T^\varepsilon)$ for all $\varepsilon > 0$), nor for positive-real-weighted countable Beurling systems unconditionally (Theorem II.3 gives $\|g(t)\| \le \Phi(|t|)$ for any unbounded $\Phi$). Thus any World-I defect calculus (`obstacles-summary.md` §2.10) cannot rely on polynomial growth of $g(t)$ alone; its analytic threshold must operate at or below the subpolynomial / $\sqrt{\log |t|}$ scale.
3. **Row 3 & §2.10 Criterion Q1 (Necessity of Joint Count-Remainder + FE-Defect Coupling `(r, g)`):** In Theorems I.2 and I.3, the lower bounds $\frac{1}{3(p_0 + 1)}$ and $\frac{A^2}{256\pi p_0} T\log T$ depend inversely on the least deleted prime $p_0$. In Theorem I.4, sending the cutoff $P_* = 2^{k_0} - 1 \to \infty$ forces $p_0 > P_* \to \infty$ while keeping the fake zero $\rho_0 = \beta_0 + i\gamma_0$ at **fixed positive depth** $\beta_0 - \frac{1}{2} > 0$: on $\mathrm{Re}\,s = \frac{1}{2}$, sending $k_0 \to \infty$ drives $\|H_1(\frac{1}{2}+2it) + H_{\ge 2}(\frac{1}{2}+2it)\| \to 0$ at bounded heights while exploding the integer-count remainder constant $C_R$ (`editSystem_count`). Conversely, for `posTruncatedZeta P_* ρ_0` as $P_* \to \infty$, $\mathrm{posFiniteFactor}\,P_*\,\rho_0 \to \zeta(s + 1 - \rho_0)\zeta(s + 1 - \bar\rho_0)$ on $\mathrm{Re}\,s > \beta_0$ while blowing up exponential strip constants on $\mathrm{Re}\,s = \frac{1}{2}$. Therefore, any uniform lower bound depending only on zero depth $\beta_0 - \frac{1}{2}$ (independent of $p_0$) must couple the critical-line FE defect $g$ jointly with the integer-count remainder $r(x) = N_B(x) - A x$, confirming Criterion Q1 of `obstacles-summary.md` §2.10. $\square$

---

## Lean status

Formalized (compile clean, `formal/GaloisForLFunctions/`):
- Def 1.1 = `EulerFETransportTheory.HamburgerStripDefect`.
- Lemma 1.2: `hamburgerStripDefect_of_stripContinuation` (defect `stripDefect`), `stripDefect_eq_of_factor` (`EulerFETransportTheory/PolynomialStripContinuationsLieInTheHamburgerClass`).
- Thm I.1(1): `SumProductArithmeticOfTheLogarithm.pos_density_of_integerNormFakeAt_lt_one` (A > 0, every integer-norm fake, β_c < 1); `EulerFETransportTheory.pole_eq_half_density` (β = A/2, any density A).
- Thm I.1(2): `WorldsOfTheZeroConfiguration.FEDefect.exists_least_deleted_prime`, `intCoeff_editSystem_mul_eq_zero`.
- Thm I.2: general `eventually_le_mul_abelMass_of_coeff_ne` (floor ‖a_{m₂}−a_{m₁}‖/(3(m₂+1))), `not_tendsto_zero_of_coeff_ne`, `not_le_rpow_neg_of_coeff_ne`; edits `FEDefect.editSystem_eventually_le_mul_abelMass`, `editSystem_defect_not_decaying` (any deleted prime).
- Thm I.3: general `integral_norm_sq_mul_exp_ge_of_missing_multiples` (needs only density A > 0, N(n) = An + o(n)), `not_le_sqrt_log_of_missing_multiples`, `not_bounded_of_missing_multiples`; edits `FEDefect.editSystem_fake_defect_energy`, `editSystem_fake_defect_not_le_sqrt_log`, `editSystem_fake_least_deleted_prime_energy`.
- Thm II.2: (a) `fake_abelMass_floor`; (b) `signedPoly_eq_exp` (real prime-power weights w̃_r), `signedPoly_hamburgerStripDefect` (β = 0, ‖g‖ ≤ 2(1+2^{1/4})²), `signedPoly_fake` (γ₀ = 1, Abel floor 1/12).
- Cor III.1: `FEDefect.IsFactorTwinOn.stripDefect_eq`, `pairTwin_stripDefect_eq`, `pairFactor_criticalLine`, `quartetFactor_criticalLine`, `quartetTwin_defect`.
- Thm I.4: `WorldsOfTheZeroConfiguration.SignedEdit.frontier_dichotomy`, `exists_subpolynomialDefectFake` (conclusions `IsSubpolynomialDefectFake`), modules `ASignedGroupedEditHasSquareRootDiscrepancy` → `TheSignedEditSeriesContinuesBelowOneHalf` → `TheSignedEditRemaindersContinueBelowOneHalf` → `TheSignedEditFactorsThroughTheTemperedModel` → `FakeEditsWithSubpolynomialDefectEnergy`. Stronger than stated: needs only `1/2 < β₀ < 3/2 − Θ` (no `5/8`, any `γ₀`); `σ₁ = max(α/2, β₀ − 1/2, Θ + β₀ − 1)`; pointwise `‖g(t)‖ ≤ C_ε(1+|t|)^{1/6+ε}` (Weyl, corpus `norm_riemannZeta_half_le_abs_rpow`). Construction: signs selected per group from `|cos(γ₀ log p)|` weights with the corpus Bernstein net (`BeurlingRandomPrimeDeletion`), group exponent `α = (β₀+β_c)/2`; `H₁` bounded by summation by parts, `Q` by sparsity at `θ > α`.

- Thm II.1: `EulerFETransportTheory.beurlingSystem_rigidity_of_decaying_defect` (Hamburger form), `beurlingSystem_rigidity_of_decaying_theta_defect`, corollary `riemannZeta_eq_zero_of_decaying_defect` (no fake zero). Modules `TentPairingsOfDecayingDefects` (tent identity for polynomial defects; exact double-IBP `∫(1−|s|)J_g(τ_s) = (ih)⁻²Δ²[τ²J_G]`) → `DecayingTentErrorsAreSmall` (small width, dyadic shell `∫_W^{2W}E² ≪ W^α`, origin `O(a^{1/2})`) → `RecurrenceThroughSparseErrors` → `DecayingDefectsVanishInTheUnitGap` → `DecayingDefectsForceIntegerSupport` (grid-hat Fejér decomposition) → `DecayingFunctionalEquationsDetermineThePrimes`. Step 3 uses the vertical Hardy bound instead of Mellin–Plancherel; the multiplicity step uses only that a decaying defect changes no radial residue.
- Thm II.2(b) Möbius weights: `eulerWeight`, `sum_divisors_mul_eulerWeight`, `abs_eulerWeight_le` (`|w_m| ≤ 2·2^{3m/4}`), `hasProd_signedPoly` (`F₀ = Π(1−2^{−ms})^{−w_m}`, Re s > 3/4).

- Thm II.3: `EulerFETransportTheory.SlowDefect.exists_positiveWeighted_beurling_slow_defect` (axioms: propext, Classical.choice, Quot.sound). Stronger than stated: `Φ` only needs `Φ → ∞` (no monotonicity), any `γ`, and `1/3 < μ` is implied by `0 < ν < 3μ − 1`; the Euler product is `exp ∫ u^{-s} dP` with `P = Σ_{i,r}(w_i/r)δ_{e^{r u_i}}` (`Discretization.eulerPrimeMeasure`), the log-Euler series converging absolutely on Re s > 1. Modules `RieszCountOfAContinuedEulerProduct` (general count `exists_abs_count_sub_le`: `G = (s−1)Z` holomorphic past Re s = 2/5 with `‖G‖ ≤ C(1+|t|)^{3/2}` ⇒ `ν([1,x]) = Re G(1)·x + O(x^{4/5})`, via Riesz–Mellin inversion, the corpus vertical contour shift and quadratic B-spline second differences) → `MobiusInvertedOverRegularPrimes` (Step 1: `invertedDensity`, `e^y/(2y) ≤ π₀ ≤ 3e^y/(2y)`, Möbius inversion `tsum_invertedDensity_div`, `laplace_cutDensity_eq_tsum`, `cexp_laplace_cutDensity`) → `PointMassDiscretizationsOfALaplaceDensity` (Step 2–3 generic: cells, `measureDirichlet_eulerPrimeMeasure`, crude/fine block bounds, `differentiableOn_discretizationError`, Hamel-basis `exists_linearIndependent_mem_Ioo`) → `ArbitrarilySlowDefectsOfPositiveWeightedSystems` (heights `T_k` from `Φ` with `X_k² ≤ T_k`, `M_m` from `T_m`). Bounds used: `‖(s−1)ζ_c(s)‖ ≤ 75(3+|γ|)²(1+|t|)` on `2/5 ≤ Re s ≤ 2`, and `|E(s)| ≤ Σ_{m<k}B_m + 1/4` at height `|t| < T_k`.
- Cor III.2: `WorldsOfTheZeroConfiguration.WorldOne.worldOne_row_one` (I.2 + I.3 for every fake edit; II.1 for countable Beurling), `worldOne_row_two` (Θ < 1: no power lower bound in L²-mean), `worldOne_row_two_weighted` (unconditional: a positive-real-weighted system with zeros `1 − μ ± iγ` and `‖g(t)‖ ≤ log(1+|t|)`, so `‖g(t)‖ < c|t|^α` for large `|t|`, every `α, c > 0`), `worldOne_row_three` (Θ < 1: same ρ₀ with least deleted prime beyond any bound, via `exists_subpolynomialDefectFake_beyond`).

Correction: Thm I.4 Branch A's clause "the WZC greedy pair twin has polynomial defect g" has no proof — the twin exponent K(1/2+2it) is only O(1+|t|) (III.1(1)), so e^{K} may grow exponentially. The dichotomy needs only "Θ = 1 ⇒ AsymptoticAbscissaLaw"; Branch A is formalized without that clause.

## 5. Lean 4 Formalization Blueprint

Every theorem in §§1–4 maps directly onto existing corpus structures without new axioms or external assumptions. Suggested module layout under `formal/GaloisForLFunctions/`:

1. **`EulerFETransportTheory/FakeEditCriticalLineDefectLowerBounds.lean`** (Theorems I.1, I.2, I.3 & Corollary III.1(2))
   - **Imports:**
     - `GaloisForLFunctions.RHTower.HamburgerStabilityCriticalLine` (`coeff_eq_of_critical_line_even_sublinear_defect`, `norm_defectLaplace_le`, `abelMass_antitone`, `hamburgerSeries_eq_of_coeffTheta_relation_defect`)
     - `GaloisForLFunctions.EulerFETransportTheory.TheBoundaryPreservesDefectEnergy` (`norm_boundaryPairKernel_unit`, `norm_sin_quarter_sq`, `closedDefectLaplace_ray_eq`, `integral_norm_sq_halfMellinData`)
     - `GaloisForLFunctions.RHTower.LandauSummabilityTransfer` (`RHTower.landau_summability_transfer`)
     - `GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.IntegerNormFakeObstructions` (`IsIntegerNormFakeAt`, `infinite_missing_primes_of_integerNormFakeAt`)
     - `GaloisForLFunctions.WorldsOfTheZeroConfiguration.TwoSidedPrimeEdits` (`IsEdit`, `editSystem`, `hasIntegerNorms_editSystem`, `isDiscrete_editSystem`)
   - **Target declarations:**
     - `hamburgerStrip_of_polyStripContinuation` (Lemma 1.2)
     - `pos_density_of_integerNormFakeAt_lt_one` (Theorem I.1(1))
     - `exists_min_deleted_prime_dvd_count_zero` (Theorem I.1(2))
     - `editSystem_fake_abelMass_liminf_pos` and `not_editSystem_fake_of_defect_rpow_lt_neg_half` (Theorem I.2)
     - `editSystem_fake_damped_L2_lower_bound` and `editSystem_fake_limsup_div_sqrt_log_pos` (Theorem I.3)

2. **`WorldsOfTheZeroConfiguration/SubpolynomialDefectFakeEdits.lean`** (Theorem I.4 & Corollary III.1(1))
   - **Imports:**
     - `GaloisForLFunctions.ArithmeticPositiveDuality.TheMeromorphicTemperedEulerFirewall` (`zetaZeroAbscissa`, `posTruncatedZeta`, `posCofactor`, `hasProd_and_LSeries_posTruncatedZeta`, `asymptoticAbscissaLaw_of_zetaZeroAbscissa_eq_one`)
     - `GaloisForLFunctions.HTGeometry.GroupedSelectionConcentration` (`GroupedSelection.exists_selection`)
     - `GaloisForLFunctions.RHTower.BeurlingRandomPrimeDeletion` (`blockPrimes`, `tsum_failure_lt`)
     - `GaloisForLFunctions.RHTower.InvZetaAbscissaSubpolynomial` (`exists_zeta_lower_bound_subpolynomial_of_zeroFree`)
     - `GaloisForLFunctions.RHTower.SmoothAFEZetaStripBound` and `GaloisForLFunctions.RHTower.ZetaStripInterpolation` (`exists_norm_riemannZeta_le_interp`)
     - `GaloisForLFunctions.WorldsOfTheZeroConfiguration.TwoSidedPrimeEdits` (`editSystem_zetaSeriesC`, `editSystem_count`)
   - **Target declarations:**
     - `exists_grouped_twoSidedEdit_approximating_posTruncatedZeta` (Theorem I.4 Steps 1–3)
     - `unconditional_frontier_or_subpolynomial_L2_editSystem_fake` (Theorem I.4)

3. **`EulerFETransportTheory/SubSquareIntegrableDefectsDetermineThePrimes.lean`** (Theorems II.1 & II.2)
   - **Imports:**
     - `GaloisForLFunctions.EulerFETransportTheory.FiniteEnergyFunctionalEquationsDetermineThePrimes` (`beurlingSystem_rigidity_of_integer_measure_eq`)
     - `GaloisForLFunctions.EulerFETransportTheory.FiniteEnergyDefectsObeyTheTentIdentity` (`tent_pairing_identity_of_polynomial_defect`)
     - `GaloisForLFunctions.ExactEventTheory.TentRecurrenceOfIntegrableDefects` (`tentAtomMass_half_eq_zero_of_lt`, `exists_common_almostPeriods`)
     - `GaloisForLFunctions.RHTower.HamburgerStabilityCriticalLine` (`coeff_eq_of_critical_line_even_sublinear_defect`)
   - **Target declarations:**
     - `beurlingSystem_rigidity_of_rpow_lt_neg_half_defect` (Theorem II.1)
     - `integerNorm_realWeight_not_abelSublinear_defect` and `exists_signed_realWeight_zeroDensity_bounded_defect_fake` (Theorem II.2)

4. **`RHTower/DiscretizedOverRegularSlowDefectFake.lean`** (Theorem II.3)
   - **Imports:**
     - `GaloisForLFunctions.RHTower.BeurlingOverRegularIntegersOffLineZeros` (`primeDensity`, `primeDensity_nonneg`, `overRegularZeta`, `cexp_integral_primeDensity`)
     - `GaloisForLFunctions.HTGeometry.BeurlingCrossSystemBlindness` (`Beurling.System`)
   - **Target declarations:**
     - `mobiusInvertedPrimeDensity_pos` (Theorem II.3 Step 1)
     - `exists_positiveRealWeightedBeurling_fake_defect_le_unbounded` (Theorem II.3)

## Log

- 2026-11-12 — Complete unconditional paper solution to B186 and A151 written in `2-fully-proven`.
