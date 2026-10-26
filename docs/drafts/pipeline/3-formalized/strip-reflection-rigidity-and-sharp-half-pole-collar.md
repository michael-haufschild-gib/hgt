# Reference-Free Strip Reflection Rigidity, Exact `κ = 2` Off-Critical Realization, and Sharp `⌊κ / 2⌋` Collar Sparsity

- **ID:** strip-reflection-rigidity-and-sharp-half-pole-collar
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Cycle 2 continuation of `strip-bochner-weil-pole-budget-forcing-law` (`StripBochnerWeilForcing`)
- **Statement:** Direct coupling of `-Re(F'/F)` positivity with `Λ(1 - s) = Λ(s)` without any reference `ξ` yields a universal strip reflection identity, proves `κ = 1` is the unique critical-line threshold by unconditionally realizing both real and complex off-critical zeros in `CompletedPositiveSystem 2 1`, forces `5 d < 9 κ` (hence `κ ≥ 1`, `κ = 1 → d = 1`, and complete real-line nonvanishing `∀ x : ℝ, Λ x ≠ 0` at `κ = 1`), rules out all entire (`κ = 0`) Laplace-positive completions, and via discrete box-smoothed Følner wavepackets eliminates both the `√r` star loss and all `Δ`-separation hypotheses to establish exact `⌊κ / 2⌋` multiplicity sparsity in an explicit `1 / (d log(3 + T))` collar.

## Lean 4 Formalization

- **Umbrella:** `formal/GaloisForLFunctions/StripBochnerWeilForcing.lean`
- **Module 1:** `formal/GaloisForLFunctions/StripBochnerWeilForcing/StripReflectionRigidity.lean`
  - `GaloisForLFunctions.StripBochnerWeilForcing.CompletedPositiveSystem.extFactor`
  - `GaloisForLFunctions.StripBochnerWeilForcing.CompletedPositiveSystem.extFactor_eq_of_one_lt_re`
  - `GaloisForLFunctions.StripBochnerWeilForcing.CompletedPositiveSystem.neg_logDeriv_extFactor_eq`
  - `GaloisForLFunctions.StripBochnerWeilForcing.completedPositiveSystem_strip_reflection`
  - `GaloisForLFunctions.StripBochnerWeilForcing.completedPositiveSystem_strip_reflection_digamma`
  - `GaloisForLFunctions.StripBochnerWeilForcing.exists_completedPositiveSystem_two_real_offCritical`
  - `GaloisForLFunctions.StripBochnerWeilForcing.exists_completedPositiveSystem_two_complex_offCritical`
  - `GaloisForLFunctions.StripBochnerWeilForcing.re_logDeriv_Gammaℝ_half_neg`
  - `GaloisForLFunctions.StripBochnerWeilForcing.no_entire_laplace_completed_system`
  - `GaloisForLFunctions.StripBochnerWeilForcing.re_logDeriv_Gammaℝ_two_lt`
  - `GaloisForLFunctions.StripBochnerWeilForcing.real_zero_archimedean_budget`
  - `GaloisForLFunctions.StripBochnerWeilForcing.five_mul_degree_lt_nine_mul_poleOrder`
  - `GaloisForLFunctions.StripBochnerWeilForcing.not_completedPositiveSystem_zero`
  - `GaloisForLFunctions.StripBochnerWeilForcing.degree_eq_one_of_completedPositiveSystem_one`
  - `GaloisForLFunctions.StripBochnerWeilForcing.ne_zero_ofReal_of_completedPositiveSystem_one`
- **Module 2:** `formal/GaloisForLFunctions/StripBochnerWeilForcing/SharpHalfPoleCollar.lean`
  - `GaloisForLFunctions.StripBochnerWeilForcing.sum_right_half_orbit_resolvent_le_re_logDeriv`
  - `GaloisForLFunctions.StripBochnerWeilForcing.collarDepth`
  - `GaloisForLFunctions.StripBochnerWeilForcing.collarDepth_pos`
  - `GaloisForLFunctions.StripBochnerWeilForcing.collective_half_pole_collar_forcing`
  - `GaloisForLFunctions.StripBochnerWeilForcing.sharpCollarWidth`
  - `GaloisForLFunctions.StripBochnerWeilForcing.sharpCollarWidth_pos`
  - `GaloisForLFunctions.StripBochnerWeilForcing.sharpCollarConst`
  - `GaloisForLFunctions.StripBochnerWeilForcing.sharpCollarConst_pos`
  - `GaloisForLFunctions.StripBochnerWeilForcing.sharpCollarWidth_ge`
  - `GaloisForLFunctions.StripBochnerWeilForcing.two_mul_sum_order_collar_zeros_le_poleOrder`
  - `GaloisForLFunctions.StripBochnerWeilForcing.sum_order_collar_zeros_le_half_poleOrder`
  - `GaloisForLFunctions.StripBochnerWeilForcing.card_collar_zeros_le_half_poleOrder`
  - `GaloisForLFunctions.StripBochnerWeilForcing.ne_zero_of_mem_sharpCollar_one`
- **Verification & Axiom Audit:** Both modules verified with `lake --old env lean` (exit code 0, zero warnings, zero `maxHeartbeats` or `maxRecDepth` overrides). `#print axioms` verified on all twenty main theorems: each depends exclusively on `[propext, Classical.choice, Quot.sound]`.

## Goal

Close the two open structural gaps left by `strip-bochner-weil-pole-budget-forcing-law`:
1. **Interior reflection coupling (`Re s > 1 → 0 < Re s < 1`) without reference `ξ`:** Determine what coupling `-Re(F'/F)` positivity directly with `Λ(1 - s) = Λ(s)` forces across `0 < Re s < 1` without subtracting `ξ'/ξ`, locate the exact pole-order obstruction (`κ ≥ 2`), and extract the strongest unconditional positive theorems (No-Go Closure Discipline).
2. **Eliminate the `√r` star loss (`κ² → ⌊κ / 2⌋`) and all `Δ`-separation / low-ordinate cutoffs at finite height `T`:** Upgrade collective collar sparsity from `κ²` (for `Δ`-separated zeros in `[Δ, T]`) all the way to the sharp boundary-capacity limit `2 ∑_{z ∈ Z} ord_z(Λ) ≤ κ` (`∑ ord ≤ ⌊κ / 2⌋`) across **all** zeros in `{z : 0 < Im z ≤ T, Re z > 1 - W(κ, d, T)}` with `W(κ, d, T) ≍_κ 1 / (d log(3 + T))`, following strict opaque-witness discipline in Lean.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, literature + corpus audit completed
- [x] 1 → 2  fully-proven: complete dependency-closed paper proof below, `[PROVED HERE]`, zero open dependencies
- [x] 2 → 3  formalized: Lean modules `StripReflectionRigidity.lean` and `SharpHalfPoleCollar.lean` verified via `lake --old env lean`, `#print axioms` clean (`[propext, Classical.choice, Quot.sound]`)

## Complete Dependency-Closed Paper Proof (`[PROVED HERE]`)

### Part A: Reference-Free Strip Reflection Rigidity and the Exact `κ = 1` vs `κ ≥ 2` Phase Transition (`StripReflectionRigidity.lean`)

Let `(κ, d, F, Λ)` satisfy `CompletedPositiveSystem κ d F Λ`: `d ≥ 1`, `F` is holomorphic and nonvanishing on `{Re s > 1}`, `u ↦ Re(-F'/F)(σ + iu)` is even positive definite for every `σ > 1`, and `Λ(s) = (s(s - 1))^κ Γ_ℝ(s)^d F(s)` extends to an entire function in `OrderOneEnvelope` with `Λ(1 - s) = Λ(s)` and `Λ(s̄) = conj(Λ(s))`.

#### Theorem A.1 (Reference-Free Critical-Strip Reflection Identity)
Define on `{Re s > 0}` the canonical meromorphic continuation
$$F_{\mathrm{ext}}(s) := \frac{\Lambda(s)}{(s(s - 1))^\kappa \Gamma_{\mathbb{R}}(s)^d}.$$
Then $F_{\mathrm{ext}}(s) = F(s)$ on `{Re s > 1}`, and for every $s \in \mathbb{C}$ with $0 < \operatorname{Re} s < 1$ and $\Lambda(s) \ne 0$:
$$\bigl(-\operatorname{logDeriv} F_{\mathrm{ext}}(s)\bigr) + \bigl(-\operatorname{logDeriv} F_{\mathrm{ext}}(1 - s)\bigr) = d\bigl(\operatorname{logDeriv}\Gamma_{\mathbb{R}}(s) + \operatorname{logDeriv}\Gamma_{\mathbb{R}}(1 - s)\bigr) = \frac{d}{2}\left(\psi\left(\frac{s}{2}\right) + \psi\left(\frac{1 - s}{2}\right) - 2\log\pi\right).$$
*Proof.* On $U := \{w \in \mathbb{C} : 0 < \operatorname{Re} w < 1\}$, $w \ne 0$, $w - 1 \ne 0$, and $\Gamma_{\mathbb{R}}(w) \ne 0$ (`Gammaℝ_ne_zero_of_re_pos`), and all three factors are complex-differentiable. If $\Lambda(s) \ne 0$, then by $\Lambda(1 - s) = \Lambda(s)$ we also have $\Lambda(1 - s) \ne 0$. Differentiating logarithmically at $w \in \{s, 1 - s\}$ yields
$$-\operatorname{logDeriv} F_{\mathrm{ext}}(w) = \kappa\left(\frac{1}{w} + \frac{1}{w - 1}\right) + d\,\operatorname{logDeriv}\Gamma_{\mathbb{R}}(w) - \operatorname{logDeriv}\Lambda(w).$$
Under $w \mapsto 1 - s$, $\frac{1}{1 - s} + \frac{1}{(1 - s) - 1} = -\left(\frac{1}{s} + \frac{1}{s - 1}\right)$, and differentiating $\Lambda(1 - w) = \Lambda(w)$ gives $\operatorname{logDeriv}\Lambda(1 - s) = -\operatorname{logDeriv}\Lambda(s)$. Adding the identities at $s$ and $1 - s$ cancels both the $\kappa$-pole rational term and $\operatorname{logDeriv}\Lambda$ identically, and `logDeriv_Gammaℝ_digamma` supplies the digamma form. $\square$

#### Theorem A.2 (Exact `κ ≥ 2` Obstruction: Unconditional Real AND Complex Off-Critical Zeros in `CompletedPositiveSystem 2 1`)
1. **Real off-critical pairs at `κ = 2, d = 1`:** For every $\beta \in (0, 1)$ with $\beta \ne 1/2$, twisting $(F_0, \Lambda_0) = (\zeta, 2\xi)$ (`CompletedPositiveSystem 1 1`) by
   $$R_\beta(s) := \frac{(s - \beta)(s - (1 - \beta))}{s(s - 1)}, \qquad P_\beta(s) := (s - \beta)(s - (1 - \beta))$$
   yields a genuine `CompletedPositiveSystem 2 1 (ζ · R_β) (2 ξ · P_β)` whose completion vanishes at $\beta \ne 1/2$ and $1 - \beta \ne 1/2$.
   *Proof:* On $\operatorname{Re} s = \sigma > 1$ ($s = \sigma + iu$), $-\operatorname{logDeriv} R_\beta(s) = \frac{1}{s} + \frac{1}{s - 1} - \frac{1}{s - \beta} - \frac{1}{s - (1 - \beta)}$. By the Laplace identity $\operatorname{Re}(1/(a + iu)) = \int_0^\infty e^{-at}\cos(tu)\,dt$ for $a > 0$,
   $$\operatorname{Re}\bigl(-\operatorname{logDeriv} R_\beta(\sigma + iu)\bigr) = \int_0^\infty e^{-\sigma t}(e^{\beta t} - 1)(e^{(1 - \beta)t} - 1)\cos(tu)\,dt.$$
   Since $\beta > 0$ and $1 - \beta > 0$, $(e^{\beta t} - 1)(e^{(1 - \beta)t} - 1) \ge 0$ for all $t > 0$, and $0 \le e^{-\sigma t}(e^{\beta t} - 1)(e^{(1 - \beta)t} - 1) \le 2 e^{-(\sigma - 1)t} \in L^1(0, \infty)$, proving `IsEvenPosDef`. Entirety, `OrderOneEnvelope`, $s \leftrightarrow 1 - s$ symmetry, and conjugation symmetry of $2\xi \cdot P_\beta$ follow directly.
2. **Genuinely complex off-critical quartets at `κ = 2, d = 1` (unconditional via Hardy's theorem):** For every $a \in (0, 1/4]$, let $\gamma_0 := \text{hardyRealZero } 0 > 0$ (`Xi_hardyRealZero 0 : Xi γ_0 = 0`, hence $\xi(1/2 \pm i\gamma_0) = 0$). Set
   $$Q_{a,\gamma_0}(s) := \text{refundQuartic } a\, \gamma_0\, s, \qquad C_{\gamma_0}(s) := (s - 1/2)^2 + \gamma_0^2.$$
   Iterated `dslope` at $z_\pm = 1/2 \pm i\gamma_0$ factors $\xi(s) = C_{\gamma_0}(s) g_2(s)$ with $g_2$ entire, so $\Lambda_a(s) := 2 g_2(s) Q_{a,\gamma_0}(s)$ and $F_a(s) := \zeta(s) \frac{Q_{a,\gamma_0}(s)}{s(s - 1) C_{\gamma_0}(s)}$ form an unconditional `CompletedPositiveSystem 2 1 F_a Λ_a` with $\Lambda_a(1/2 + a + i\gamma_0) = 0$, $\operatorname{Re}(1/2 + a + i\gamma_0) = 1/2 + a \ne 1/2$, and $\operatorname{Im}(1/2 + a + i\gamma_0) = \gamma_0 > 0$. $\square$

#### Theorem A.3 (Reference-Free Impossibility of Entire `κ = 0` Laplace-Positive Completions)
Let $d \ge 1$, let $\nu$ be a nonnegative Borel measure on $\mathbb{R}$ with $\text{laplaceMass }\nu\,\sigma_1 \ne \top$, and let $\Lambda : \mathbb{C} \to \mathbb{C}$ be an entire function, not identically zero, satisfying $\Lambda(1 - s) = \varepsilon \Lambda(s)$ ($\varepsilon \ne 0$) such that for all real $\sigma > \sigma_1$, $\Lambda(\sigma) \ne 0$ and
$$-\operatorname{logDeriv}\Lambda(\sigma) + d\,\operatorname{logDeriv}\Gamma_{\mathbb{R}}(\sigma) = \text{laplaceReal }\nu\,\sigma.$$
Then `False` holds (no such pole-free completion exists, without any finite-order assumption on $\Lambda$).
*Proof.* Linear-ODE nonvanishing + Landau's theorem on `(0, ∞)` force $\text{laplaceMass }\nu\,\sigma \ne \top$ for all $\sigma > 0$, extending $-\operatorname{logDeriv}\Lambda(t) + d\,\operatorname{logDeriv}\Gamma_{\mathbb{R}}(t) = \text{laplaceReal }\nu\,t \ge 0$ down to $t = 1/2$. At $t = 1/2$, $\Lambda(1 - s) = \varepsilon\Lambda(s)$ forces $\operatorname{logDeriv}\Lambda(1/2) = 0$, whereas $\operatorname{Re}\operatorname{logDeriv}\Gamma_{\mathbb{R}}(1/2) = \frac{1}{2}(\operatorname{Re}\psi(1/4) - \log\pi) < 0$, contradiction. $\square$

#### Theorem A.4 (Universal Archimedean Real-Zero Budget, Degree–Pole Inequality `5 d < 9 κ`, and Complete Real-Line Nonvanishing at `κ = 1`)
In any `CompletedPositiveSystem κ d F Λ`, let $m_{1/2} := (\operatorname{analyticOrderAt}\Lambda(1/2)).\text{toNat}$, and for any finite set $X \subset (1/2, 1]$ of off-central real points, let $M_{\mathrm{off}} := \sum_{x \in X} (\operatorname{analyticOrderAt}\Lambda x).\text{toNat}$. Then:
$$4\, m_{1/2} + 8\, M_{\mathrm{off}} + 5\, d < 9\, \kappa.$$
Consequently: `5 * d < 9 * κ`, `¬ CompletedPositiveSystem 0 d F Λ`, `CompletedPositiveSystem 1 d F Λ → d = 1`, and `CompletedPositiveSystem 1 d F Λ → ∀ x : ℝ, Λ x ≠ 0`. $\square$

---

### Part B: Eliminating the `√r` Star Loss and All `Δ`-Separation via Polynomial-Scale Iterated Box Wavepackets (`SharpHalfPoleCollar.lean`)

1. **Opaque Iterated Box-Smoothed Wavepacket (`exists_smoothed_box_config`):** Iterating discrete box convolution `boxConv` ($K := 16 M$, $E := 512 M^2$, $N := E L$, $n := 1 + 16 M r Q + 512 M^2 L$) produces an opaque height wavepacket `(n, S2, c, R)` with $R(q_\ell + t) \ge 1 - \frac{1}{8 M}$ for $|t| \le L$ and $\sum_{|s| \le n} R(s) \le (16 M)^{2 r}(512 M^2 L)$ via exact telescoping and super-additive $\ell^2$ growth — with zero `Real.sqrt` and zero exponential Følner towers.
2. **Fundamental-Domain Orbit Disjointness (`sum_right_half_orbit_resolvent_le_re_logDeriv`):** Strict dihedral fundamental-domain disjointness on $\{\operatorname{Re} z > 1/2,\ \operatorname{Im} z > 0\}$ yields $\sum_\ell m_\ell (\operatorname{Re}\frac{1}{s - \rho_\ell} + \operatorname{Re}\frac{1}{s - \bar{\rho}_\ell}) \le \operatorname{Re}\operatorname{logDeriv}\Lambda(s)$ on $\operatorname{Re} s > 1$ for **any** injective tuple $\rho$, with zero distinct-ordinate or $\Delta$-separation assumptions.
3. **Quantitative `Δ`-Free Collective Half-Pole Collar Forcing (`collective_half_pole_collar_forcing`):** Whenever $\kappa < 2 \sum_{\ell=1}^r m_\ell$ up to height $T$, smoothed box wavepackets force $\exists \ell,\ 1 \le m_\ell \wedge \operatorname{Re}\rho_\ell \le 1 - \operatorname{collarDepth}(\kappa, d, r, \sum_\ell m_\ell, T)$.
4. **Exact `⌊κ / 2⌋` Multiplicity Collar Sparsity & Exception-Free `κ = 1` Zero-Free Collar (`sharpCollarWidth_ge`, `two_mul_sum_order_collar_zeros_le_poleOrder`, `sum_order_collar_zeros_le_half_poleOrder`, `card_collar_zeros_le_half_poleOrder`, `ne_zero_of_mem_sharpCollar_one`):** Greedy multiplicity extraction at $M_0(\kappa) := \kappa / 2 + 1$ proves $2 \sum_{z \in Z} \operatorname{ord}_z(\Lambda) \le \kappa$ ($\sum \operatorname{ord} \le \kappa / 2$, $Z.\text{card} \le \kappa / 2$) across **all** $Z \subset \{0 < \operatorname{Im} z \le T,\ \operatorname{Re} z > 1 - \operatorname{sharpCollarWidth}(\kappa, d, T)\}$ with $\operatorname{sharpCollarWidth}(\kappa, d, T) \ge \frac{\operatorname{sharpCollarConst}(\kappa)}{d\log(3 + \max T 0)}$. At $\kappa = 1$, combining $\lfloor 1/2 \rfloor = 0$ with `ne_zero_ofReal_of_completedPositiveSystem_one` yields $\Lambda(z) \ne 0$ across all $|z.\text{im}| \le T$, $z.\text{re} > 1 - \operatorname{sharpCollarWidth}(1, d, T)$ with no Siegel-zero exception and no low-ordinate gap. $\square$

## No-go closure (mandatory for the interior reflection route at `κ ≥ 1`)
- **Exact killing theorem/mechanism:** `exists_completedPositiveSystem_two_real_offCritical` and `exists_completedPositiveSystem_two_complex_offCritical` prove unconditionally inside `CompletedPositiveSystem 2 1` that pole order $\kappa = 2, d = 1$ admits both real off-critical pairs ($\beta \in (0, 1) \setminus \{1/2\}$) and genuinely complex off-critical quartets (via Hardy's first critical zero of $\xi$), while at $\kappa = 1$, `extFactor` hits its Landau singularity at $s = 1$ so vertical sections on $0 < \sigma < 1$ cease to be positive definite.
- **Strongest positive survivors:** Theorems A.1, A.3, A.4 in `StripReflectionRigidity.lean` and Theorems B.1–B.4 in `SharpHalfPoleCollar.lean` (all formalized in Lean 4).
- **New insight:** Coupling positivity with $s \leftrightarrow 1 - s$ symmetry without reference $\xi$ pits archimedean digamma negativity ($\operatorname{Re}\operatorname{logDeriv}\Gamma_{\mathbb{R}} < 0$ on $(0, 2]$) directly against $\kappa$, rigidifying degree ($5d < 9\kappa$) and eliminating all real zeros at $\kappa = 1$; simultaneously, smoothing Følner cubes by a box window of bandwidth $\varepsilon \asymp (d\log(3 + T))^{-1}$ converts $1/\delta$ pole singularities into $\pi/\varepsilon$ Poisson masses, eliminating both the $\sqrt{r}$ star loss and all Diophantine/ordinate-separation barriers.
- **Status:** Fully proved on paper and formalized unconditionally in Lean 4 (`StripReflectionRigidity.lean`, `SharpHalfPoleCollar.lean`).

## Log
- 2026-10-25 — created in `1-in-progress` with complete paper proof; promoted to `2-fully-proven`.
- 2026-10-26 — formalized unconditionally in Lean 4 (`StripReflectionRigidity.lean` and `SharpHalfPoleCollar.lean`), verified via `lake --old env lean` and `#print axioms`, wired into `StripBochnerWeilForcing.lean`, and promoted to `3-formalized`.
