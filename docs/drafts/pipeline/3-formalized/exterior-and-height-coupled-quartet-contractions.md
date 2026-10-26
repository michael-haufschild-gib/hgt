# Exterior and Height-Coupled Zero-Tax Quartet Contractions

- **ID:** acp-exterior-and-height-coupled-quartet-contractions
- **Stage:** 3-formalized
- **Type:** THEOREM (formalized in Lean 4)
- **Source:** `formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/ExteriorAndHeightCoupledQuartetContractions.lean` · `formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/SymmetricSquareContractionsAndExteriorCounts.lean` · `formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/TheSpectrumOfSymmetricSquaresIsTheSign.lean` · `formal/GaloisForLFunctions/StripBochnerWeilForcing/PositiveDefiniteSectionsAreCompletelyMonotone.lean` · `formal/GaloisForLFunctions/StripBochnerWeilForcing/CollectivePoleRepulsion.lean`
- **Statement:** Eliminating the $\Delta\kappa \ge 1$ boundary pole tax on complex off-critical quartets $\{1/2 \pm a \pm i\gamma\}$ ($0 < a < 1/2, \gamma \neq 0$) obeys an exact real-anchor law and is constructively achieved by two phase-colliding couplings: (1) any conjugation-symmetric finite polar sum $G(s) = \sum_{z \in S} c(z)/(s - z)$ whose vertical real-part sections are positive definite on $\sigma > \sigma_1$ has nonnegative Laplace scale weight $\sum_{z \in S} c(z) e^{\operatorname{Re} z \cdot t}\cos(\operatorname{Im} z \cdot t) \ge 0$ for all $t > 0$, forcing any $\Delta\kappa = 0$ cancellation of a rightmost non-real pole $\sigma_{\max} + i\gamma_1$ ($c(\sigma_{\max} + i\gamma_1) > 0$) to simultaneously cancel a real pole at $\sigma_{\max}$ of weight $c(\sigma_{\max}) \ge c(\sigma_{\max} + i\gamma_1)$ (and $c(\sigma_{\max}) \ge 2 c(\sigma_{\max} + i\gamma_1)$ in the single-ordinate case); (2) over $\mathbb{F}_q$ and on archimedean scale divisors, the functorial exterior square `CurveDatum.exterior D 2` and the centered exterior-square divisor polynomial $P_{\Lambda^2}(\rho; s)$ convert every complex quartet into a single real off-critical pair plus four unitary/critical-line zeros at $\Delta\kappa = 0$; (3) over $\mathbb{Z}$, the correspondence height-coupled system $F_\gamma(s) = F(s)^2 F(s + i\gamma) F(s - i\gamma)$, $\Lambda_\gamma(s) = \Lambda(s)^2 \Lambda(s + i\gamma) \Lambda(s - i\gamma)$ (`HeightCoupledSystem (2κ) κ d γ`) collides $(\rho_0, \bar{\rho}_0)$ onto $1/2 + a \in \mathbb{R}$ with multiplicity $2$ and contracts both the collided real pairs and the complex quartet onto $\{1/2, 1/2 \pm i\gamma\}$ across the entire strip $0 < a < 1/2$ via `coupledQuartetSymSquare` at zero marginal pole tax ($\Delta\kappa_0 = 0, \Delta\kappa_\gamma = 0$), terminating in finitely many steps across arbitrarily many quartets on $\operatorname{Im} s = \gamma$ under a fixed contraction-invariant archimedean budget.

## Goal
In `SymmetricSquareContractionsAndExteriorCounts` (Pillar P17), real off-critical pairs $\{\beta, 1 - \beta\}$ of a `CompletedPositiveSystem κ d` contract onto $s = 1/2$ at zero pole cost ($\Delta\kappa = 0$), so iterated contraction terminates in finitely many steps, whereas single-system contractions of complex quartets $\{1/2 \pm a \pm i\gamma\}$ ($\gamma \neq 0$) paid a boundary pole tax $\Delta\kappa = 1$ ($a \le 1/4$) or $\Delta\kappa = 2$ ($a < 1/2$), causing the archimedean budget $9\kappa$ to grow faster than the central order gain under iteration.

This card proves why single-system isolated quartet contractions must pay $\Delta\kappa \ge 1$ and constructs the exterior and multi-system couplings that eliminate the $\Delta\kappa \ge 1$ pole tax by colliding conjugate phases $(\pm i\gamma) \mapsto 0$ onto the real axis — attaining the sharp real-anchor bound $c(1/2 + a) = 2 c(1/2 + a + i\gamma)$ across the entire strip $0 < a < 1/2$ with zero marginal pole cost and finite-step contraction termination.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, literature and corpus audited
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean module `GaloisForLFunctions.ArithmeticCorrespondencePositivity.ExteriorAndHeightCoupledQuartetContractions`

## Lean 4 Declarations (`GaloisForLFunctions.ArithmeticCorrespondencePositivity`)
- **Post–Widder polar scale weights & real-anchor law:**
  - `polarSum`, `polarScaleWeight`
  - `posDef_polarSum_laplaceWeight_nonneg`
  - `real_anchor_of_posDef_polarSum`
  - `two_mul_le_real_anchor_of_single_ordinate`
  - `not_isEvenPosDef_quartetPureRatio`
- **Functorial exterior-power curve data & quartet phase elimination:**
  - `ExteriorIndex`, `CurveDatum.exterior`, `CurveDatum.sqrtq_exterior`, `eigenvalue_exterior`, `detDeg_exterior_eq_exteriorDetDeg`
  - `quartetCurveDatum`, `quartetCurveDatum_detDeg_linear_pos`, `quartetCurveDatum_exterior_two_spectrum`
- **Archimedean exterior-square divisors & zero-tax contraction:**
  - `centeredScaleTrace`, `exteriorTwoScaleTrace`, `exteriorTwoScaleTrace_eq_newton`
  - `exteriorTwoDivisorPoly`, `quartetPoints`, `exteriorTwoDivisorPoly_quartet`, `exteriorTwoDivisorPoly_quartet_contract`
- **Full-strip coupled symmetric-square contractions (`Δκ = 0`):**
  - `coupledQuartetSymSquare`, `deepRealQuartetSymSquare`
  - `isEvenPosDef_coupledQuartetSymSquare`, `isEvenPosDef_deepRealQuartetSymSquare`
  - `CompletedPositiveSystem.contractComplexQuartet_of_doubleRealAnchor`
  - `CompletedPositiveSystem.contractComplexQuartet_of_singleDeepRealAnchor`
- **Height-coupled positive systems, zero-tax quartet elimination & archimedean budget:**
  - `shiftedPolePoly`, `coupledGamma`, `HeightCoupledSystem`, `heightCoupledF`, `heightCoupledΛ`
  - `CompletedPositiveSystem.heightCouple`, `CompletedPositiveSystem.orderAt_heightCoupledΛ`, `CompletedPositiveSystem.orderAt_heightCoupledΛ_real`
  - `HeightCoupledSystem.contractRealPair`, `HeightCoupledSystem.contractCollidedQuartet`
  - `CompletedPositiveSystem.contractComplexQuartet_heightCoupled`
  - `HeightCoupledSystem.archimedean_budget`
  - `CompletedPositiveSystem.contractOrdinateQuartets_heightCoupled`
  - `CompletedPositiveSystem.ordinateQuartet_multiplicity_archimedean_bound`
  - `HeightCoupledSystem.exists_real_offCritical_free`

## Complete Paper Proof (`[PROVED HERE]`)

### Theorem 1 (`[PROVED HERE]` — Post–Widder Polar Weight Positivity and the Real-Anchor Law)
Let $S \subset \mathbb{C}$ be a finite set stable under conjugation ($\bar{z} \in S$ for $z \in S$) and let $c : \mathbb{C} \to \mathbb{R}$ satisfy $c(\bar{z}) = c(z)$ for all $z \in S$. Define $G(s) := \sum_{z \in S} \frac{c(z)}{s - z}$. Suppose there exists $\sigma_1 \in \mathbb{R}$ such that $\operatorname{Re} z \le \sigma_1$ for all $z \in S$ and for every $\sigma > \sigma_1$, the vertical section $u \mapsto \operatorname{Re} G(\sigma + iu)$ is positive definite (`IsPosDef`).

1. **Nonnegative scale weight (`posDef_polarSum_laplaceWeight_nonneg`):** For every $t > 0$,
   $$w_G(t) := \sum_{z \in S} c(z)\, e^{\operatorname{Re} z \cdot t} \cos(\operatorname{Im} z \cdot t) \ge 0.$$
   *Proof.* Set $a := \max(\sigma_1, 1)$. On $U := \{s \in \mathbb{C} : \operatorname{Re} s > a\}$, every $z \in S$ satisfies $\operatorname{Re}(s - z) > a - \sigma_1 \ge 0$, so $s - z \neq 0$ and $G$ is holomorphic on $U$. For real $x > a$, conjugation invariance of $(S, c)$ gives $\overline{G(x)} = \sum_{z \in S} \frac{c(\bar{z})}{x - \bar{z}} = G(x)$, so $\operatorname{Im} G(x) = 0$. For $x \ge a + 1$, $|x - z| \ge x - \operatorname{Re} z \ge 1$, whence $\operatorname{Re} G(x) \le |G(x)| \le \sum_{z \in S} |c(z)| \le \bigl(\sum_{z \in S} |c(z)|\bigr)\sqrt{x}$ (as $\sqrt{x} \ge \sqrt{2} \ge 1$). By `re_iterate_deriv_two_mul_nonneg`, `hasDerivAt_re_iterate_deriv`, and `tower_odd_nonpos` (`PositiveDefiniteSectionsAreCompletelyMonotone`), $(-1)^n \operatorname{Re}(G^{(n)}(x)) \ge 0$ for every $n \in \mathbb{N}$ and $x > a$. By induction on $n$ on the open set $U$,
   $$G^{(n)}(s) = (-1)^n n! \sum_{z \in S} \frac{c(z)}{(s - z)^{n + 1}} \qquad (s \in U).$$
   Fix $t > 0$. For every integer $n > a t$, $x_n := n / t > a$, and multiplying $(-1)^n \operatorname{Re}(G^{(n)}(x_n)) \ge 0$ by $x_n^{n+1} / n! > 0$ yields
   $$0 \le \operatorname{Re} \sum_{z \in S} c(z) \bigl((1 - z t / n)^{-1}\bigr)^{n+1}.$$
   Since $(1 - z t / n)^n \to e^{-z t} \neq 0$ and $(1 - z t / n) \to 1$ as $n \to \infty$, $\bigl((1 - z t / n)^{-1}\bigr)^{n+1} \to e^{z t}$, and $\operatorname{Re}(c(z) e^{z t}) = c(z) e^{\operatorname{Re} z \cdot t}\cos(\operatorname{Im} z \cdot t)$. Passing to the limit $n \to \infty$ gives $w_G(t) \ge 0$. $\square$

2. **Multi-ordinate and single-ordinate real-anchor bounds (`real_anchor_of_posDef_polarSum`, `two_mul_le_real_anchor_of_single_ordinate`):** Suppose $\sigma_{\max} \in \mathbb{R}$ satisfies $\operatorname{Re} z \le \sigma_{\max}$ whenever $z \in S$ and $c(z) \neq 0$, and suppose $z_1 = \sigma_{\max} + i\gamma_1 \in S$ has $\gamma_1 \neq 0$ and $c(z_1) > 0$.
   - *(General multi-ordinate case)* Integrating $e^{-\sigma_{\max} t} w_G(t)(1 - \cos(\gamma_1 t)) \ge 0$ over $[T, 2T]$ and dividing by $T \to \infty$ kills all subdominant modes ($\operatorname{Re} z < \sigma_{\max}$) exponentially and all non-resonant top frequencies by `tendsto_avg_cos_zero`, leaving $(\sigma_{\max} \in S \text{ ? } c(\sigma_{\max}) : 0) - c(z_1) \ge 0$, whence $\sigma_{\max} \in S$ and $c(\sigma_{\max}) \ge c(z_1) > 0$.
   - *(Single-ordinate case)* If additionally every $z \in S$ with $c(z) \neq 0$ and $\operatorname{Re} z = \sigma_{\max}$ has $\operatorname{Im} z \in \{0, \gamma_1, -\gamma_1\}$, sampling $e^{-\sigma_{\max} t_k} w_G(t_k) \ge 0$ along $t_k := \frac{(2k + 1)\pi}{|\gamma_1|} \to +\infty$ yields $\sigma_{\max} \in S$ and $c(\sigma_{\max}) \ge 2 c(z_1)$.
   - *(Corollary `not_isEvenPosDef_quartetPureRatio`)* No pure quartet ratio `quartetCritPoly γ s / quartetOffPoly a γ s` ($0 < a < 1/2, \gamma \neq 0$) can have `IsEvenPosDef` vertical $-\logDeriv$ sections on $\sigma > 1$. $\square$

### Theorem 2 (`[PROVED HERE]` — Functorial Exterior-Square Curve Datum and Quartet Phase Elimination)
For any `CurveDatum ι` and $k \ge 1$, `CurveDatum.exterior D k` on $k$-element subsets of $\iota$ at base $q^k$ ($\Delta\kappa = 0$) satisfies $\operatorname{detDeg}(D.\text{exterior}\,k, P) = \operatorname{exteriorDetDeg}_D(k, P)$. On any genus-$2$ complex quartet `quartetCurveDatum q hq r hr θ`, all $4$ degree-one linear counts are strictly positive when $\sin\theta \neq 0$, whereas `exterior 2` converts the $6$ exterior eigenvalues into one real off-critical pair $\{q r^2, q r^{-2}\}$ plus four unitary eigenvalues $\{e^{2i\theta}, e^{-2i\theta}, 1, 1\}$. $\square$

### Theorem 3 (`[PROVED HERE]` — Archimedean Exterior-Square Divisor and Zero-Tax Midpoint Contraction)
For $\rho : \iota \to \mathbb{C}$, $2 \Lambda^2 z_\rho(t) = z_\rho(t)^2 - z_\rho(2t)$ (`exteriorTwoScaleTrace_eq_newton`) cancels the diagonal $2\rho_i - 1/2$ and factors `exteriorTwoDivisorPoly (quartetPoints a γ) s` into `realPairPoly (1/2 + 2a) s * (s - 1/2)^2 * ((s - 1/2)^2 + 4γ^2)`, which contracts onto $\operatorname{Re} s = 1/2$ via `midpointSymSquare (1/2 + 2a)` at $\Delta\kappa = 0$ for $0 < a < 1/4$. $\square$

### Theorem 4 (`[PROVED HERE]` — Full-Strip Coupled Symmetric-Square Quartet Contraction Attaining the Sharp Real-Anchor Bound)
`coupledQuartetSymSquare b a γ` ($0 < a \le b < 1/2$) has nonnegative Laplace density $2 e^{t/2}((e^{bt/2} - e^{-bt/2})^2 + \cos(\gamma t)(e^{at/2} - e^{-at/2})^2) \ge 0$ (`4 e^{t/2}\cos^2(\gamma t/2)(e^{at/2} - e^{-at/2})^2$ at $b = a$, attaining $c(1/2 + a) = 2 c(1/2 + a + i\gamma)$), giving `IsEvenPosDef` vertical $-\logDeriv$ sections for all $\sigma > 1$ at $\Delta\kappa = 0$. Similarly, a single deeper real pair ($2a \le b < 1/2$) contracts a quartet at $\Delta\kappa = 0$ via `deepRealQuartetSymSquare b a γ`. $\square$

### Theorem 5 (`[PROVED HERE]` — Height-Coupled Positive Systems, Zero-Tax Collided Quartet Contraction, Archimedean Budget, and Finite-Step Elimination)
Lifting $(F, \Lambda) \in \operatorname{CompletedPositiveSystem}\;\kappa\;d$ to $F_\gamma(s) = F(s)^2 F(s + i\gamma) F(s - i\gamma)$, $\Lambda_\gamma(s) = \Lambda(s)^2 \Lambda(s + i\gamma) \Lambda(s - i\gamma)$ produces `HeightCoupledSystem (2κ) κ d γ F_γ Λ_γ` (`CompletedPositiveSystem.heightCouple`), colliding $(\rho_0, \bar{\rho}_0)$ onto $1/2 + a \in \mathbb{R}$ with multiplicity $2$. Inside `HeightCoupledSystem κ₀ κγ d γ`, `contractCollidedQuartet` contracts both collided real pairs and the complex quartet onto $\{1/2, 1/2 \pm i\gamma\}$ across all $0 < a < 1/2$ at $\Delta\kappa_0 = 0, \Delta\kappa_\gamma = 0$. Against the contraction-invariant Hadamard–digamma budget (`HeightCoupledSystem.archimedean_budget`), simultaneous contraction of all quartets on $\operatorname{Im} s = \gamma$ proves `ordinateQuartet_multiplicity_archimedean_bound`, and iterated `contractRealPair` terminates in finitely many $\Delta\kappa = 0$ steps (`HeightCoupledSystem.exists_real_offCritical_free`). $\square$

## Log
- Complete paper proof written and unconditionally formalized in `formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/ExteriorAndHeightCoupledQuartetContractions.lean` (3,712 lines, zero `sorry`, `#print axioms` clean `[propext, Classical.choice, Quot.sound]`, audited via `lake --old env lean`).
