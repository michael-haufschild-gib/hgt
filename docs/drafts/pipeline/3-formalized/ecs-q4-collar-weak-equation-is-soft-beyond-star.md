# E-Q4: The Collar Weak Equation is Soft Beyond $(\star)$

- **ID:** ecs-q4-collar-soft-beyond-star
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Source:** docs/reports/review-1611/route-ecs.md §6 (E-Q4)
- **Lean Module:** `GaloisForLFunctions.ExclusionOfTheCriticalState.Collar.TheCollarWeakEquationIsSoftBeyondStar`
- **Statement:** Restricting the confined weak equation to collar tests supported in $(-\log 2, 0)$ — where Weil's form is coercive ($\ge \frac{1}{8000}\int G^2$) and only backward prime translates enter — imposes zero additional constraints on the zero values $(\mathcal{L}F(z_q))_q$ beyond the left-normalised Cauchy system $(\star)$: every profile $F \in \mathcal{H}$ satisfying normalised $(\star)$ automatically satisfies the smooth half-line weak equation and the collar weak equation, together with the collar Cauchy–Schwarz bound on its zero pairings.

## Goal
Answer E-Q4 unconditionally and completely: establish the collar explicit formula in both zero and prime coordinates (both for the critical state on all collar domain profiles and unconditionally on $\mathcal{H} \times C_c^\infty((-\infty, 0))$), prove complete subsumption of the collar weak equation by normalised $(\star)$, and record the quantitative collar zero-pairing inequality, collar uniqueness from the tail, and nonvanishing deep-tail mass of the critical state.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven: complete dependency-closed paper proof below `[PROVED HERE]`
- [x] 2 → 3  formalized: `GaloisForLFunctions.ExclusionOfTheCriticalState.Collar.TheCollarWeakEquationIsSoftBeyondStar`

## Dependency-Closed Paper Proof `[PROVED HERE]`

### 1. Prime coordinates and zero side on the collar $(-\log 2, 0)$
Let $F : \mathbb{R} \to \mathbb{R}$ vanish on $[0, \infty)$ and let $G : \mathbb{R} \to \mathbb{R}$ vanish on $(-\infty, -\log 2]$ and on $[0, \infty)$.
- **Vanishing of forward prime translates:** For every $n \ge 2$, $\log 2 \le \log n$. If $t < 0$, then $t - \log n < -\log n \le -\log 2$, so $G(t - \log n) = 0$; if $t \ge 0$, $F(t) = 0$. Hence $\int_{\mathbb{R}} F(t) G(t - \log n)\,dt = 0$. Similarly, in `primePairTerm G F n`, if $t \le -\log 2$ then $G(t) = 0$, while if $t > -\log 2$ then $t + \log n > 0$, so $F(t + \log n) = 0$, and $\int G(t) F(t - \log n)\,dt = \int F(u) G(u + \log n)\,du = \int_{-\log 2}^0 F(u - \log n) G(u)\,du$. For $n < 2$, `vonMangoldtAtom n = 0`. Thus for every $n \in \mathbb{N}$:
  $$\operatorname{primePairTerm}(F, G, n) = \operatorname{primePairTerm}(G, F, n) = \frac{\Lambda(n)}{\sqrt{n}} \int_{-\infty}^0 F(t) G(t + \log n)\,dt,$$
  and `bareMixedEnergy F G` reduces to Gamma + pole minus pure backward translates sampling $F$ strictly on $(-\infty, -\log 2)$:
  $$B(F, G) = \Gamma(F, G) - \sum_{n=0}^\infty \frac{\Lambda(n)}{\sqrt{n}} \int_{-\infty}^0 F(t) G(t + \log n)\,dt + 2 C(F) C(G) - 2 S(F) S(G).$$
  If $F$ also vanishes on $(-\infty, -\log 2]$, then $F(t) G(t + \log n) = 0$ identically for $n \ge 2$, so `primeMixedForm F G = 0`.
- **Collar zero side at the state:** Combining this prime-coordinate formula with `criticalState_tendsto_zeroPairing` (for any $G \in \mathcal{H}$ vanishing on $(-\infty, -\log 2]$) and `criticalState_hasSum_bareMixedEnergy` (for any $G \in C_c^\infty((-\log 2, 0))$) expresses $B(F, G) = -a(W_0)\int_{-\log 2}^0 F(u)G(u)e^{-8u}\,du$ simultaneously by its zero side $\sum_q \mathcal{L}F(z_q)\mathcal{L}G(-z_q)$ and by its backward-prime collar coordinates.

### 2. Unconditional smooth-test explicit formula on the entire energy domain $\mathcal{H}$
Let $F \in \mathcal{H}$ (`CriticalHalfLineEnergyDomain F`) be **any** profile and let $G \in C_c^\infty(\mathbb{R})$ have compact support and vanish on $[0, \infty)$. Set $\psi = \operatorname{cx} G$ and $H = \operatorname{laplaceTest}\,\psi$. Applying `hasSum_zeroValues_two_lines` to $F$ and $H$ between $a = -2$ and $b = 5$ gives
$$\sum_{q : \text{XiZeroCopy}} \mathcal{L}F(z_q)\,\mathcal{L}G(-z_q) = \frac{1}{2\pi}\left(\int_{\mathbb{R}} H(5 + it)\,B_F(5 + it)\,dt - \int_{\mathbb{R}} H(-2 + it)\,B_F(-2 + it)\,dt\right).$$
- **Left line ($a = -2$):** Since $B_F(-2 + it) = -a(1)\,\operatorname{stateMeromorphic}\,1\,F\,(-10 + it)$, `integral_laplaceTest_mul_stateMeromorphic_left` equates the left integral to $-2\pi a(1)\int_{x > 0} G(x) F^+(x)\,dx = 0$ because $G = 0$ on $[0, \infty)$.
- **Right line ($b = 5$):** On $\operatorname{Re} p = 5$, $B_F(p) = \operatorname{levyRemainder}\,F\,p = \operatorname{stateRemainder}\,F\,p = \operatorname{stateGamma}\,F\,p + \mathcal{L}F(p)\frac{\zeta'}{\zeta}(\frac{1}{2}+p) - \operatorname{stateTail}\,F\,p + C(F)((p+\frac{1}{2})^{-1} + (p-\frac{1}{2})^{-1}) - S(F)((p+\frac{1}{2})^{-1} - (p-\frac{1}{2})^{-1})$. Evaluating $\frac{1}{2\pi}\int H(5+it)(\cdots)\,dt$ term-by-term via `integral_laplaceTest_mul_laplace` on $\sigma = 5$ proves $\sum_q \mathcal{L}F(z_q)\mathcal{L}G(-z_q) = B(F, G)$ unconditionally on $\mathcal{H} \times C_c^\infty((-\infty, 0))$.

### 3. Complete subsumption of the collar by $(\star)$ (Answer to E-Q4: NO)
For $R \in \mathbb{R}$ and $F \in \mathcal{H}$, if $F$ satisfies `SatisfiesNormalisedStar R F`, comparing with `tendsto_tsum_sub_left` along `comap Complex.re atBot` forces $B_F(w + 8) = -a(R)\,\mathcal{L}F(w)$ for all $\operatorname{Re} w > -4$. Plugging this into `hasSum_zeroValues_two_lines` between $a = -2$ and $b = 5$ gives $\sum_q \mathcal{L}F(z_q)\mathcal{L}G(-z_q) = -a(R)\int_{-\infty}^0 F(u)G(u)e^{-8u}\,du$ for all $G \in C_c^\infty((-\infty, 0))$ (and Gaussian-summed for all $G \in \mathcal{H}$). Uniqueness of sums against §2 (`hasSum_bareMixedEnergy_of_domain`) gives `criticalHalfLineMixedEnergy R F G = 0` for all $G \in C_c^\infty((-\infty, 0))$, hence on all smooth collar tests: `(SatisfiesNormalisedStar R F ∧ SmoothCollarWeakEquation R F) ↔ SatisfiesNormalisedStar R F`.

### 4. Collar coercivity corollaries: zero-pairing bound, collar uniqueness, and deep-tail mass
1. **Collar bare-form floor & Cauchy–Schwarz on zero values:** For any `IsWindowTest A G` with $A \le 2\cdot\text{enlargedWeilFloorAperture}$ (in particular $A = \log 2$), $B(G, G) = \operatorname{weilQuad}(G) \ge \frac{1}{8000}\int G^2 \ge 0$, and under `SatisfiesNormalisedStar R F`, $\|\sum_q \mathcal{L}F(z_q)\mathcal{L}G(-z_q)\|^2 \le 2048000\,a(R)^2 (\int_{-\log 2}^0 F^2 e^{-8u}) B(G, G)$ for all $G \in C_c^\infty((-\log 2, 0))$.
2. **Collar uniqueness from the tail:** If $F_1, F_2 \in \mathcal{H}$ satisfy the collar weak equation at $R > 0$ on `IsWindowTest (Real.log 2)` and $F_1 - F_2$ is a `C²` collar test, then $F_1 = F_2$ everywhere.
3. **Nonvanishing deep tail (`criticalState_deepTail_sq_pos`):** By `criticalState_changes_sign_on_every_ray`, $\int_{u < -T} F(u)^2\,du > 0$ for every $T \in \mathbb{R}$ (in particular $T = \log 2$).
