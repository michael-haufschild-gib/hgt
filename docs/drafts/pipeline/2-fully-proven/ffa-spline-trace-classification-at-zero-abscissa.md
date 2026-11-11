# Four-Sector Classification of the Normalized Spline Trace at the Zero Abscissa and Strict Separation of the Top-Line Laws

- **ID:** ffa-spline-trace-classification-at-zero-abscissa
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** docs/reports/review-1011/fable.md §5.3 `[D]`
- **Statement:** For the normalized cubic-spline trace $G(u) = \operatorname{normTrace}(\mathcal{Z}_\zeta, \Theta - \frac{1}{2}, u)$ at the zeta zero abscissa $\Theta = \operatorname{zetaZeroAbscissa}$, $G(u)$ splits unconditionally into four mutually exclusive regimes (`RH`, unattained off-line top $G \to 0$, finite nonempty off-line top $G - T \to 0$ with $T \not\equiv 0$ trigonometric polynomial, infinite off-line top where $G - T \not\to 0$ for every finite trigonometric polynomial $T$), and the three laws (`StrongOffLineTopNonAttainment` $\implies$ `NoFiniteOffLineTopLine` $\implies$ `AsymptoticAbscissaLaw`) are strictly separated on tempered conjugation-symmetric nonreal zero configurations.

## Goal
Resolve the exact relation between `RHTower.AsymptoticAbscissaLaw`, the trigonometric-polynomial exclusion in `fable.md` §5.3 `[D]`, and strong $o(1)$ decay of $G(u) = e^{-(\Theta - 1/2)u} c_B(u)$ at the canonical top depth $b_* = \Theta - \frac{1}{2}$.

## Gates
- [x] 0 → 1  in-progress: exact Bohr-spectrum formulation of real trigonometric polynomials and canonical depth $b_* = \Theta - \frac{1}{2}$
- [x] 1 → 2  fully-proven: complete dependency-closed paper proof `[PROVED HERE]`
- [ ] 2 → 3  formalized: Lean module `GaloisForLFunctions.FloorFreeArithmetic.TheSplineTraceClassificationAtTheZeroAbscissa`, `lake --old env lean` green, `#print axioms` clean

## Paper Proof `[PROVED HERE]`

### 1. Real finite trigonometric polynomials and Bohr-spectrum finiteness
Define `IsRealTrigPoly(T)` for $T : \mathbb{R} \to \mathbb{R}$ by the existence of a finite set $S \subset \mathbb{R}$ and coefficients $c : \mathbb{R} \to \mathbb{C}$ such that
$$
T(u) = \operatorname{Re}\sum_{\omega \in S} c(\omega) e^{i\omega u} \qquad (u \in \mathbb{R}).
$$
Using $\operatorname{Re} w = \frac{1}{2}(w + \overline{w})$ and $\overline{e^{i\omega u}} = e^{-i\omega u}$, the complexification $T_{\mathbb{C}}(u) = (T(u) : \mathbb{C})$ equals
$$
T_{\mathbb{C}}(u) = \sum_{\omega \in S} \frac{c(\omega)}{2} e^{i\omega u} + \sum_{\omega \in S} \frac{\overline{c(\omega)}}{2} e^{-i\omega u}.
$$
Each summand is continuous and Bohr almost periodic, so $T_{\mathbb{C}}$ is continuous and Bohr almost periodic. By linearity of `bohrCoefficient` and `bohrCoefficient (bohrExp μ) λ = δ_{μ,λ}`, $\operatorname{bohrCoefficient}(T_{\mathbb{C}}, \lambda) = 0$ whenever $\lambda \notin S \cup (-S)$. In particular, $\{\lambda \in \mathbb{R} \mid \operatorname{bohrCoefficient}(T_{\mathbb{C}}, \lambda) \ne 0\}$ is finite.

### 2. Characterization of trigonometric-polynomial limits at a bounding depth
Let $Z$ be a tempered zero configuration (`TemperedConfig Z`) and $b \in \mathbb{R}$ satisfy `TopDepth Z b`. Let
$$
\mathcal{A}(Z, b) := \{z \in \mathbb{C} \mid \operatorname{Re} z = b \text{ and } e_Z(z) \ne 0\}, \qquad e_Z := \operatorname{evenCoeff}(Z, B_{1,3}).
$$
By `tendsto_normTrace_sub_topTrace`, $\operatorname{normTrace}(Z, b, u) - \operatorname{topTrace}(Z, b, u) \to 0$ as $u \to +\infty$.

- **(Necessity of finite active top line):** Suppose $T$ satisfies `IsRealTrigPoly T` and $\operatorname{normTrace}(Z, b, u) - T(u) \to 0$ as $u \to +\infty$. Subtracting gives $\operatorname{topTrace}(Z, b, u) - T(u) \to 0$, hence $\operatorname{topTraceC}(Z, b, u) - T_{\mathbb{C}}(u) \to 0$. Since both $\operatorname{topTraceC}(Z, b)$ and $T_{\mathbb{C}}$ are continuous and Bohr almost periodic, Bohr uniqueness (`eq_zero_of_isBohrAlmostPeriodic_of_tendsto_zero`) yields $\operatorname{topTraceC}(Z, b) = T_{\mathbb{C}}$ identically on $\mathbb{R}$, hence $T = \operatorname{topTrace}(Z, b)$. By `bohrCoefficient_topTraceC`, for every $z \in \mathcal{A}(Z, b)$,
  $$
  \operatorname{bohrCoefficient}(T_{\mathbb{C}}, \operatorname{Im} z) = \operatorname{bohrCoefficient}(\operatorname{topTraceC}(Z, b), \operatorname{Im} z) = e_Z(z) \ne 0,
  $$
  so $\operatorname{Im} z \in S \cup (-S)$. Since $z \mapsto \operatorname{Im} z$ is injective on $\{z \in \mathbb{C} \mid \operatorname{Re} z = b\}$, $\mathcal{A}(Z, b)$ is finite. Moreover, $T \not\equiv 0 \iff \mathcal{A}(Z, b) \ne \emptyset$ by `topCoeff_eq_zero_of_topTraceC_eq_zero` and `topTrace_eq_zero_of_topCoeff_eq_zero`.

- **(Sufficiency of finite active top line):** Conversely, if $\mathcal{A}(Z, b)$ is finite with `Finset` representative $F$, let $S = \operatorname{Im}(F)$ and $c(\omega) = e_Z(b + i\omega)$. Every term `topTerm Z b z u` with $z \notin F$ vanishes identically, so $\operatorname{topTraceC}(Z, b, u) = \sum_{z \in F} e_Z(z) e^{i(\operatorname{Im} z) u} = \sum_{\omega \in S} c(\omega) e^{i\omega u}$ (by injectivity of $\operatorname{Im}$ on $\{ \operatorname{Re} z = b \}$). Taking real parts gives `IsRealTrigPoly (topTrace Z b)`, and `tendsto_normTrace_sub_topTrace` gives $\operatorname{normTrace}(Z, b, u) - \operatorname{topTrace}(Z, b, u) \to 0$. If $\mathcal{A}(Z, b)$ is nonempty with $z_0 \in \mathcal{A}(Z, b)$, then $\operatorname{bohrCoefficient}(\operatorname{topTraceC}(Z, b), \operatorname{Im} z_0) = e_Z(z_0) \ne 0$, so $\operatorname{topTrace}(Z, b)$ is not identically zero.

### 3. Four-sector classification at $b_* = \Theta - \frac{1}{2}$ for $\zeta(s)$
Set $b_* = \Theta - \frac{1}{2}$ where $\Theta = \operatorname{zetaZeroAbscissa} \in [\frac{1}{2}, 1]$. Unconditionally $b_* \ge 0$, and $b_* = 0 \iff \Theta = \frac{1}{2} \iff \operatorname{RiemannHypothesis}$. For any $z \in \mathbb{C}$ with $e_{\mathcal{Z}_\zeta}(z) \ne 0$, `add_half_mem_zetaZeroConfig_of_evenCoeff_ne_zero` gives $\frac{1}{2} + z \in \mathcal{Z}_\zeta$, hence $\zeta(\frac{1}{2} + z) = 0$, so $\frac{1}{2} + \operatorname{Re} z \le \Theta$, proving `TopDepth zetaZeroConfig b_*`. When $b_* > 0$, the map $z \mapsto \frac{1}{2} + z$ restricts to a bijection between $\mathcal{A}(\mathcal{Z}_\zeta, b_*)$ and $\mathcal{L}_{\mathrm{top}}(\zeta) := \{\rho \in \mathcal{Z}_\zeta \mid \operatorname{Re}\rho = \Theta\}$ by `evenCoeff_spline_sees` and `add_half_mem_zetaZeroConfig_of_evenCoeff_ne_zero`.

Partitioning into $b_* = 0$ (`RiemannHypothesis`) and $b_* > 0$ with $\mathcal{L}_{\mathrm{top}}(\zeta)$ empty, finite nonempty, or infinite yields the four mutually exclusive regimes for $G(u) = \operatorname{normTrace}(\mathcal{Z}_\zeta, b_*, u)$:
1. $\Theta = \frac{1}{2}$ (`RiemannHypothesis`): $G = \operatorname{topTrace}(\mathcal{Z}_\zeta, 0)$ identically on $\mathbb{R}$, hence $(G(u) : \mathbb{C})$ is Bohr almost periodic;
2. $\Theta > \frac{1}{2}$ and $\mathcal{L}_{\mathrm{top}}(\zeta) = \emptyset$: $G(u) \to 0$ as $u \to +\infty$;
3. $\Theta > \frac{1}{2}$ and $\mathcal{L}_{\mathrm{top}}(\zeta)$ finite nonempty: $G(u) - T(u) \to 0$ for a nonzero real trigonometric polynomial $T = \operatorname{topTrace}(\mathcal{Z}_\zeta, b_*)$;
4. $\Theta > \frac{1}{2}$ and $\mathcal{L}_{\mathrm{top}}(\zeta)$ infinite: for every real trigonometric polynomial $T$, $G(u) - T(u) \not\to 0$ as $u \to +\infty$ (in particular $G(u) \not\to 0$).

Consequently, for $\zeta(s)$:
- $(\Theta > \frac{1}{2} \implies G(u) \to 0) \iff (\Theta > \frac{1}{2} \implies \mathcal{L}_{\mathrm{top}}(\zeta) = \emptyset)$;
- $(\Theta > \frac{1}{2} \implies \forall T \not\equiv 0 \text{ trig.\ poly.}, \, G - T \not\to 0) \iff (\Theta > \frac{1}{2} \implies \mathcal{L}_{\mathrm{top}}(\zeta) = \emptyset \text{ or } \mathcal{L}_{\mathrm{top}}(\zeta) \text{ infinite})$;
- $(\Theta > \frac{1}{2} \implies G(u) \to 0) \implies (\Theta > \frac{1}{2} \implies \forall T \not\equiv 0 \text{ trig.\ poly.}, \, G - T \not\to 0) \implies \operatorname{AsymptoticAbscissaLaw}$ (since `¬ AsymptoticAbscissaLaw` yields a spectral gap $h < \Theta - \frac{1}{2}$ with `rightOf zetaZeroConfig h` finite and containing $\mathcal{L}_{\mathrm{top}}(\zeta) \ne \emptyset$).

### 4. Strict separation of the three laws on tempered configurations
Fix any $b \in (0, \frac{1}{2}]$.
1. **Infinite top line (`AbscissaLaw` and `NoFiniteTopLine` hold, `normTrace → 0` fails):** Let $Z_{\mathrm{col}}$ be the disjoint superposition of `column one_pos 1 hb hb' 1 le_rfl` and `column one_pos (-1) hb hb' 1 le_rfl`, whose carrier consists of $\frac{1}{2} \pm b + i(6j \pm 1)(2\pi)$ for $j \in \mathbb{Z}$. Since $6j \pm 1 \ne 0$ for all $j \in \mathbb{Z}$, $Z_{\mathrm{col}}$ has no real zeros; since $-(6j + 1) = 6(-j) - 1$, $Z_{\mathrm{col}}$ is conjugation-symmetric; by `temperedConfig_superpose` and `temperedConfig_column`, $Z_{\mathrm{col}}$ is tempered of exact top depth $b$. It has infinitely many points on $\operatorname{Re} \rho = \frac{1}{2} + b$, so `AbscissaLaw Z_col` holds, no finite trigonometric polynomial approximates $\operatorname{normTrace}(Z_{\mathrm{col}}, b)$ at $+\infty$, and $\operatorname{normTrace}(Z_{\mathrm{col}}, b) \not\to 0$.
2. **Sub-top accumulation (`AbscissaLaw` holds, yet `normTrace` tends to a nonzero finite trigonometric polynomial — refuting the converse in `[D]`):** Define `subTopConfig hb hb'` with carrier $\{\rho \in \mathbb{C} \mid \exists k \in \mathbb{N},\; |\operatorname{Re}\rho - \frac{1}{2}| = b(1 - \frac{1}{k+2}) \wedge |\operatorname{Im}\rho| = k + 2\}$ and multiplicity $1$. Since $|\operatorname{Im}\rho| = k + 2$ uniquely determines $k$ and grows linearly, `subTopConfig` is locally finite, reflection- and conjugation-symmetric, free of real zeros, and tempered (`∑ (1 + (k+2)^2)⁻¹ < ∞`). Let $Z_{\mathrm{mix}} = \operatorname{superpose}(\operatorname{layerConfig}\; hb'\; \{1\}\; 1,\; \operatorname{subTopConfig}\; hb\; hb')$. The two carriers are disjoint (ordinates $1$ vs.\ $k + 2 \ge 2$, and depths $b$ vs.\ $b(1 - \frac{1}{k+2}) < b$). Because $b(1 - \frac{1}{k+2}) \to b$ as $k \to \infty$ along distinct ordinates $k + 2$, `rightOf Z_mix h` is infinite for every $h < b$ and empty for every $h \ge b$, proving `AbscissaLaw Z_mix`. Yet `{ρ ∈ Z_mix.carrier | Re ρ = 1/2 + b} = {1/2 + b ± i}` is finite and nonempty, so $\operatorname{normTrace}(Z_{\mathrm{mix}}, b, u)$ converges as $u \to +\infty$ to a nonzero finite trigonometric polynomial.

## Log
- 2026-11-11 — created and proved in `2-fully-proven`
