# E-Q3: Curve critical states and exclusion by Castelnuovo–Severi and native Stepanov

- **ID:** ecs-q3-curve-critical-states-stepanov
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Source:** docs/reports/review-1611/route-ecs.md §6 (E-Q3)
- **Lean Module:** `GaloisForLFunctions.ExclusionOfTheCriticalState.Models.CurveCriticalStatesAndStepanovExclusion`
- **Lean Declarations:**
  - `GaloisForLFunctions.ExclusionOfTheCriticalState.CurveModels.exists_curveGroundState_of_not_unitary`
  - `GaloisForLFunctions.ExclusionOfTheCriticalState.CurveModels.curveCriticalState_iff_not_unitary`
  - `GaloisForLFunctions.ExclusionOfTheCriticalState.CurveModels.curveCriticalState_eq_sum`
  - `GaloisForLFunctions.ExclusionOfTheCriticalState.CurveModels.curveCriticalState_laplace_eq_rational`
  - `GaloisForLFunctions.ExclusionOfTheCriticalState.CurveModels.curveCriticalState_star_identity`
  - `GaloisForLFunctions.ExclusionOfTheCriticalState.CurveModels.curveCriticalState_zeroParseval`
  - `GaloisForLFunctions.ExclusionOfTheCriticalState.CurveModels.curveCriticalState_sees_outer_and_inner_root`
  - `GaloisForLFunctions.ExclusionOfTheCriticalState.CurveModels.curveBeyondWallBalance_eq_rational`
  - `GaloisForLFunctions.ExclusionOfTheCriticalState.CurveModels.curveCriticalState_not_beyondWallContinuation`
  - `GaloisForLFunctions.ExclusionOfTheCriticalState.CurveModels.hodgeIndex_violates_negative_bareForm`
  - `GaloisForLFunctions.ExclusionOfTheCriticalState.CurveModels.goldenDatum_exists_criticalState_and_collar_blind`
  - `GaloisForLFunctions.ExclusionOfTheCriticalState.CurveModels.cubicStepanov_even_bound_excludes_outer_root`
  - `GaloisForLFunctions.ExclusionOfTheCriticalState.CurveModels.cubicKummerDatum_beyondWallContinuation_and_no_criticalState`
- **Statement:** For any curve datum $D$ in the strip ($q > 1$, $\|\beta_i\| < q^4$, in particular $\|\beta_i\| \le \sqrt{q}$): (1) a confined half-line critical state exists iff $D$ has a non-unitary Frobenius root, and every critical state $f \in \mathcal{H}_D$ at $a > 0$ has the exact closed form $f(m) = -\frac{1}{a}\sum_{i \in \iota} \mathcal{L}_D f(\beta_i)(\beta_i q^{-8})^m$, rational transform $\mathcal{L}_D f(Z) = -\frac{1}{a}\sum_{i \in \iota} \frac{Z\,\mathcal{L}_D f(\beta_i)}{Z - \beta_i q^{-8}}$, curve $(\star)$, negative zero Parseval identity, and a simultaneously seen outer/inner Frobenius pair $(\beta_{i_0}, \beta_{\text{fe } i_0})$ obstructing beyond-the-wall continuation to $\{|Z| < 1\}$; (2) Castelnuovo–Severi (`curve_hodgeIndex_tfae`) excludes the critical state by violating its negative bare-energy / negative zero-norm identity $B_D(f, f) = -a W_8(f) < 0$; (3) native Stepanov (`riemannHypothesis_cubicCharacter`) excludes the critical state at Stage 5: its even-degree bound forces $|\omega_i/\sqrt{q}| \le 1$ (excluding any outer root), and together with the Gauss-sum determinant $|\prod \omega_i| = q^{(m-1)/2}$ it forces $|D.\text{trace}(n)| \le 2(\deg P - 1)$ for all $n \ge 1$ on `cubicKummerDatum`, giving holomorphic continuation of `curveBeyondWallBalance` across $\{|Z| < 1\}$ for every $h \in \mathcal{H}_D$.

## Goal
Answer E-Q3 completely and unconditionally: construct the confined critical state (and explicit golden-curve ground state) for curve configurations with non-unitary Frobenius roots, prove all of its ECS identities, and pinpoint the exact ECS identities violated by `curve_hodgeIndex_tfae` and by `riemannHypothesis_cubicCharacter`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven: complete dependency-closed paper proof below `[PROVED HERE]`
- [x] 2 → 3  formalized: `GaloisForLFunctions.ExclusionOfTheCriticalState.Models.CurveCriticalStatesAndStepanovExclusion`

## Dependency-Closed Paper Proof `[PROVED HERE]`

### 1. The confined Frobenius half-line domain and bare form
Let $D$ be a `CurveDatum ι` ($q > 1$, $\beta : \iota \to \mathbb{C}$ closed under `conjPerm` and `fePerm` with $\beta_{\text{fe } i}\beta_i = 1$) satisfying `InFourStrip D` ($\forall i,\, \|\beta_i\| < q^4$, implied by $\forall i,\, \|\beta_i\| \le \sqrt{q}$). Then $q^{-4} < \|\beta_i\| < q^4$ for all $i \in \iota$.

In discrete half-line coordinates $u_m = -m \log q \le 0$ ($m \in \mathbb{N}$) and multiplicative spectral variable $z = q^p$:
- Confined energy domain: $\mathcal{H}_D := \{ f : \mathbb{N} \to \mathbb{R} \mid \operatorname{Summable}(m \mapsto f(m)^2 q^{8m}) \}$, with confinement pairing $W_8(f, g) := \sum_{m=0}^\infty f(m) g(m) q^{8m}$.
- Half-line Laplace transform: $\mathcal{L}_D f(z) := \sum_{m=0}^\infty f(m) z^{-m}$, converging absolutely on $\{|z| > q^{-4}\}$.
- Bare Weil / Castelnuovo–Severi form:
  $$B_D(f, g) := \operatorname{Re} \sum_{i \in \iota} \mathcal{L}_D f(\beta_i) \mathcal{L}_D g(\beta_i^{-1}) = \sum_{k=0}^\infty \sum_{l=0}^\infty f(k) g(l) D.\text{trace}(|k - l|),$$
  agreeing on finite windows $[0, n)$ with $D.\text{toeplitz}(\operatorname{range} n)\,f = \operatorname{hermQuad}(D.\text{spanGram}\,n)\,f$.

### 2. Existence, dichotomy, and exact closed form of curve critical states
Orthogonal projection with respect to $W_8$ onto the finite-dimensional subspace $V_0 = \operatorname{span}_{\mathbb{R}}\{\operatorname{Re}(\beta_i^m)q^{-8m}, \operatorname{Im}(\beta_i^m)q^{-8m} : i \in \iota\}$ preserves $B_D$ and contracts $W_8$.
- **Unitary case ($\forall i,\, \|\beta_i\| = 1$):** $B_D(f, f) = \sum_{i \in \iota} \|\mathcal{L}_D f(\beta_i)\|^2 \ge 0$, so no critical state exists at any $a > 0$.
- **Non-unitary case ($\exists i,\, \|\beta_i\| \ne 1$):** By `unitary_iff_negIndex_spanGram_eq_zero`, $\operatorname{hermNegIndex}(D.\text{spanGram}(\#\iota)) > 0$, producing a real window vector $f_0 \in \mathcal{H}_D$ with $B_D(f_0, f_0) < 0$. Compact Rayleigh minimization on $V_0$ produces $a^* > 0$ and a unit profile $f^* \in \mathcal{H}_D$ ($W_8(f^*) = 1$) minimizing $B_D$ globally ($\forall h \in \mathcal{H}_D,\, B_D(h, h) + a^* W_8(h) \ge 0$) and solving $\forall g \in \mathcal{H}_D,\, B_D(f^*, g) + a^* W_8(f^*, g) = 0$.

Testing against Kronecker deltas $\delta_m$ gives the exact closed form $f(m) = -\frac{1}{a}\sum_{i \in \iota} \mathcal{L}_D f(\beta_i)(\beta_i q^{-8})^m$, rational transform $\mathcal{L}_D f(z) = -\frac{1}{a}\sum_{i \in \iota} \frac{z\,\mathcal{L}_D f(\beta_i)}{z - \beta_i q^{-8}}$, curve $(\star)$ ($-a\,\mathcal{L}_D f(z q^{-8}) = \sum_{i \in \iota} \frac{z\,\mathcal{L}_D f(\beta_i)}{z - \beta_i}$), negative zero Parseval identity, and a simultaneously seen outer/inner Frobenius pair $(\beta_{i_0}, \beta_{\text{fe } i_0})$ ($\|\beta_{i_0}\| > 1$, $\|\beta_{\text{fe } i_0}\| < 1$).

### 3. Curve beyond-the-wall prime-head identity and pole obstruction
For $h \in \mathcal{H}_D$ and $\|z\| < \min_j \|\beta_j\|$,
$$\Phi_D(h, z) := -\sum_{n=0}^\infty D.\text{trace}(n)\,z^n \sum_{m < n} h(m) z^{-m} = \sum_{j \in \iota} \frac{z\,\mathcal{L}_D h(\beta_j)}{z - \beta_j}.$$
Clearing denominators with $Q(z) = \prod_{w \in D.\text{spectrum}} (z - w)$ on the convex unit ball `Metric.ball 0 1` shows no curve critical state admits holomorphic continuation of $\Phi_D(f, \cdot)$ across $\{|z| < 1\}$ because evaluating $Q(z) H(z) = R_f(z)$ at the seen inner root $z_* = \beta_{\text{fe } i_0} \in \text{Metric.ball } 0\,1$ yields $0 = m_{z_*} z_* \mathcal{L}_D f(z_*) Q_{z_*}(z_*) \ne 0$.

### 4. Exact ECS identities violated by `curve_hodgeIndex_tfae` vs. `riemannHypothesis_cubicCharacter`
- **Castelnuovo–Severi (`curve_hodgeIndex_tfae`):** Violates the critical state's negative bare-energy / negative zero-norm identity $B_D(f, f) = -a W_8(f) < 0$ (`hodgeIndex_violates_negative_bareForm`).
- **Native Stepanov (`riemannHypothesis_cubicCharacter`):** Has no intersection form; instead its even-degree bound (`norm_rootEnumC_le`) excludes any outer root (`cubicStepanov_even_bound_excludes_outer_root`), and together with `norm_prod_lRootsC` yields $|D.\text{trace}(n)| \le 2(\deg P - 1)$ on `cubicKummerDatum`, forcing Stage-5 beyond-the-wall prime continuation throughout $\{|z| < 1\}$ for all $h \in \mathcal{H}_D$ (`cubicKummerDatum_beyondWallContinuation_and_no_criticalState`).
