# Beyond-the-wall prime-pole continuation excludes the critical state

- **ID:** ecs-q8-beyond-the-wall-prime-continuation
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `formal/GaloisForLFunctions/ExclusionOfTheCriticalState/README.md` · Q8
- **Statement:** Every critical half-line ground state sees at least one left off-critical zero of $\zeta$ ($-\tfrac12 < \operatorname{Re}z_0 < 0$, $\mathcal LF(z_0)\ne 0$), while the positive-charge-cancelled archimedean resolvent tail $J_{\ge 1}F$ is holomorphic on $\operatorname{Re}p < \tfrac52$; consequently holomorphic continuation across $-\tfrac12 \le \operatorname{Re}p < 0$ of the beyond-the-wall prime-pole balance $\Phi_F(p) = \hat SF(p) + \mathcal LF(-\tfrac12)/(p+\tfrac12)$ (equivalently of the bare prime head $\hat SG(p)$ on $\mathcal LG(-\tfrac12)=0$, or damped $L^2(0,\infty)$ membership of the right-of-wall prime wave throughout $0 < \delta \le \tfrac12$) excludes the critical state directly, is unconditionally sharp at $\operatorname{Re}p = 0$, and fails unconditionally on both the prime-two deformations ($\tfrac12 < \theta < 1$) and the positive passive real-axis-positive Euler twins beyond every finite prefix.

## Goal

Answer ECS Q8 completely and unconditionally in Lean: isolate the exact arithmetic property of the prime-power distribution beyond the wall $x > 0$ that directly excludes the critical state (`property ⇒ no state`), prove its equivalence to pure prime-head continuation on $\mathcal LG(-\tfrac12)=0$ and boundary sharpness at $\operatorname{Re}p = 0$, and refute it unconditionally on both named model families in `ExclusionOfTheCriticalState/README.md`.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean modules checked with `lake --old env lean`, umbrella-wired in `formal/GaloisForLFunctions/ExclusionOfTheCriticalState.lean`

## Formalized Lean modules and declarations

1. **`formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Zeros/TheCriticalStateSeesALeftZero.lean`**
   - `criticalState_exists_seen_left_centredZero`
   - `criticalState_exists_seen_left_zetaZero`
   - `criticalState_has_left_strip_pole`
   - `criticalState_exists_left_stateXiProduct_order_drop`
   - `riemannHypothesis_or_criticalState_sees_left_zero`
2. **`formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheBeyondTheWallPrimeBalanceExcludesTheState.lean`**
   - `archimedeanWallTail`, `wallPrimeBalance`, `wallPrimeWaveDatumLp`
   - `HasBeyondTheWallPrimeContinuation`, `ZetaBeyondTheWallPrimeContinuation`, `PurePrimeHeadContinuation`, `HasSubstripPrimeHardyWave`
   - `differentiableOn_archimedeanWallTail`
   - `globalRemainder_eq_archimedeanWallTail_add_wallPrimeBalance`
   - `laplaceRay_wallPrimeWaveDatumLp`, `polarWallTerm_eq_continuumMainTerm`
   - `not_wallPrimeBalance_continues_of_seen_zero`
   - `criticalState_not_hasBeyondTheWallPrimeContinuation`
   - `criticalState_not_hasSubstripPrimeHardyWave`
   - `no_criticalState_of_beyondTheWallPrimeContinuation`
   - `riemannHypothesis_of_beyondTheWallPrimeContinuation`, `beyondTheWallPrimeContinuation_of_riemannHypothesis`
   - `zetaBeyondTheWallPrimeContinuation_iff_riemannHypothesis`, `zetaBeyondTheWallPrimeContinuation_iff_no_criticalState`
   - `no_criticalState_of_purePrimeHeadContinuation`, `purePrimeHeadContinuation_iff_zetaBeyondTheWallPrimeContinuation`
   - `not_forall_wallPrimeBalance_continues_past_zero`
3. **`formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Models/BeyondTheWallContinuationFailsOnTheModels.lean`**
   - `modelAtom`, `modelPrimeHead`, `modelWallPrimeBalance`, `ModelBeyondTheWallPrimeContinuation`
   - `modelBeyondTheWallPrimeContinuation_zeta_iff`
   - `not_modelBeyondTheWallPrimeContinuation_eulerLogCoeff`
   - `primeTwo_not_modelBeyondTheWallPrimeContinuation`
   - `exists_positive_euler_twin_failing_beyondTheWallContinuation`

## Proof summary

1. **Strip-wide archimedean holomorphy (`differentiableOn_archimedeanWallTail`).** For $F \in \mathcal H$ and $r > 0$, $|\mathcal LF(r)| \le (2\int F^2 + 1)/(4\sqrt r)$, so each summand of $J_{\ge 1}F(p) = \sum_{k\ge 0} \mathcal LF(2(k+1)+\tfrac12)/(2(k+1)+\tfrac12 - p)$ is uniformly $O((k+1)^{-3/2})$ on every half-plane $\operatorname{Re}p < \sigma$ ($\sigma < \tfrac52$). Hence $J_{\ge 1}F$ is holomorphic on $\operatorname{Re}p < \tfrac52$, while `leftRemainder_eq_resolvents` gives $\text{globalRemainder }F\,p = J_{\ge 1}F(p) + \Phi_F(p)$ on $\operatorname{Re}p < -\tfrac12$.
2. **Every critical state sees a left zero (`criticalState_exists_seen_left_centredZero`).** For a critical state $(W_0,F)$, pairing $\text{globalRemainder }F\,(4+it) - \text{globalRemainder }F\,(-4+it)$ against $\mathcal LF(-4-it)$ and the quartic bi-Cauchy kernel $W_N(it) = \frac{4N^4}{(N^2+t^2)(4N^2+t^2)}$ ($N \ge 20$), interchanging the absolutely convergent `(XiZeroCopy × ℝ)` integral, and shifting the pole-subtracted `dslope` remainders on vertical strips to $\operatorname{Re}s = -M \to -\infty$ yields an exact residue evaluation whose boundary terms are $O(\|\text{globalRemainder }F\,(\cdot)\|) = o(1)$ as $N \to +\infty$ because $N|\mathcal LF(N-4)| \le C_1$. On $\operatorname{Re}p = 4$, $\text{globalRemainder }F\,(4+it) = -a(W_0)\mathcal LF(-4+it)$ and $\int W_N(it)|\mathcal LF(-4+it)|^2\,dt > 0$ (since $F$ has unit $L^2$ norm and cannot vanish a.e.), whereas on-line zeros $z_c = i\gamma$ contribute $\operatorname{Re}W_N(4 - i\gamma)|\mathcal LF(i\gamma)|^2 \ge 0$ for $N \ge 20$. Therefore some off-line zero $z_c$ ($\operatorname{Re}z_c \ne 0$) satisfies $\mathcal LF(z_c)\mathcal LF(-z_c) \ne 0$; reflecting into $\operatorname{Re}z < 0$ if $\operatorname{Re}z_c > 0$ gives a seen left zero $-\tfrac12 < \operatorname{Re}z_0 < 0$ with $\mathcal LF(z_0) \ne 0$.
3. **Direct state exclusion, pole-neutral reduction, and boundary sharpness.** Any holomorphic continuation $H$ of $\Phi_F$ to $\operatorname{Re}p < 0$ makes $\xi(\tfrac12+p)(J_{\ge 1}F(p)+H(p))$ analytic on $\operatorname{Re}p < 0$ and equal to `clearedRemainder F` on $\operatorname{Re}p < -\tfrac12$, hence near $z_0$, giving analytic order $\ge \operatorname{ord}_{\frac12+z_0}(\xi)$ at $z_0$ and contradicting `analyticOrderAt_clearedRemainder_add_one`. Applying pure prime-head continuation to $G = F$ when $\mathcal LF(-\tfrac12)=0$ or to the pole-neutral causal difference $G(u) = F(u+1) - e^{1/2}F(u) \in \mathcal H$ (for which $(e^{-z_0}-e^{1/2})\mathcal LF(z_0)\ne 0$) excludes the critical state from `primeHead` alone. Evaluating on `probe 5` at a zero of $\xi$ with $\operatorname{Re}z \le 0$ proves sharpness at $\operatorname{Re}p = 0$.
4. **Unconditional model refutations (`not_modelBeyondTheWallPrimeContinuation_eulerLogCoeff`).** Whenever $p$ is prime and $\|\beta\| < \sqrt p < \|\alpha\| < p$, the $\beta$-series is holomorphic throughout $\operatorname{Re}q < 0$, while clearing $F_{12}(q) = \xi(\tfrac12+q)(1 - \alpha p^{q-1/2})$ on `probe 5` produces the Leibniz derivative term $F_{12}'(q)/(5+q)$ at $q_* = \tfrac12 - \frac{\log\alpha}{\log p} \in \{-\tfrac12 < \operatorname{Re}q < 0\}$, forcing analytic order $\operatorname{ord}_{q_*}(F_{12}) - 1$ unconditionally (regardless of whether $\zeta(\tfrac12-q_*)=0$). Specializing to $(p,\alpha,\beta) = (2,2^\theta,2^{1-\theta})$ ($\tfrac12 < \theta < 1$) and $(p,-p^\sigma,-p^{1-\sigma})$ ($p > N$, $\tfrac12 < \sigma < 1$) refutes both model families unconditionally.
