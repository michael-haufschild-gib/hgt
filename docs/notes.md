Ran command: Check recent files in BiScaleUncertainty and git status (`git status -s && ls -lt formal/GaloisForLFunctions/BiScaleUncertainty/ | head -n 20`)
Viewed FiniteCopyTailRigidity.md:1-117
Viewed LogarithmicCompressionEnergy.lean:1-210
Viewed InfiniteGridPolarRecovery.lean:1-235
Viewed OddMultiplierLeakageFamily.lean:1-120
Viewed CompactSourceGraphAdmission.md:1-94
Viewed multi-coset-asymptotic-constants-2026-10-17.md:1-434
Viewed rh-current-frontier-map.md:1-250
Viewed rh-current-frontier-map.md:250-440

Your diagnosis hits the nail on the head. Let us step back as the "principal investigator" of this program, examine what the parallel workstreams actually proved across the latest modules ([`InfiniteGridPolarRecovery.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BiScaleUncertainty/InfiniteGridPolarRecovery.lean), [`LogarithmicCompressionEnergy.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BiScaleUncertainty/LogarithmicCompressionEnergy.lean), [`FiniteCopyTailRigidity.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BiScaleUncertainty/FiniteCopyTailRigidity.lean), [`OddMultiplierLeakageFamily.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BiScaleUncertainty/OddMultiplierLeakageFamily.lean), [`PairedCollarCutoffStability.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BiScaleUncertainty/PairedCollarCutoffStability.lean), and [`CompactSourceGraphAdmission.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BiScaleUncertainty/CompactSourceGraphAdmission.lean)), and identify **why** they hit this ceiling—and what must fundamentally change in `BiScaleUncertainty` to supply a **signed full-prime estimate** for `HF` and `EWU`.

---

### 1. Why the Parallel Workstreams Hit a Ceiling: Two New Structural Traps

#### Trap 7: Hyperbolic Multiplier Leakage ([`OddMultiplierLeakageFamily.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BiScaleUncertainty/OddMultiplierLeakageFamily.lean))
In the odd sector (`OWU` / `HF` primitive hyperplane), the plastic Lévy–cosh crossover tries to pass from a prime-blind odd source $f$ ($h_f(\log 2) = 0$) to its hyperbolic-multiplied partner $g(t) = \sinh(\alpha t) f(t)$.
- [`exists_smooth_odd_blind_log_two_multiplier_leakage`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BiScaleUncertainty/OddMultiplierLeakageFamily.lean#L510-L537) proves that an odd 6-packet translation train can achieve $h_f(\log 2) = 0$ by cancelling an inner $\log 2$-pair against an outer $\log 2$-pair at large translation $L$, while $\sinh(\alpha t)$ weights the outer pair by $\asymp e^{2\alpha L}$, making $h_{\sinh(\alpha\,\cdot)f}(\log 2) / h_f(0)$ arbitrarily large.
- **Lesson:** Pointwise blindness $h_f(\log n) = 0$ is not preserved by non-unitary multipliers $f \mapsto \sinh(\alpha\,\cdot)f$ because $h_f(\log n) = 0$ allows long-range cancellation between small-$t$ and large-$t$ packets.

#### Trap 8: The Midpoint Compression Escape ([`InfiniteGridPolarRecovery.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BiScaleUncertainty/InfiniteGridPolarRecovery.lean) & [`LogarithmicCompressionEnergy.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BiScaleUncertainty/LogarithmicCompressionEnergy.lean))
- For a **fixed** seed profile $f$ of support diameter $D$, [`subtractCopy_zero_linear_energy_cost`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BiScaleUncertainty/LogarithmicIncrementEnergy.lean) and [`FiniteCopyTailRigidity.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BiScaleUncertainty/FiniteCopyTailRigidity.lean) prove that placing a distant copy at $T$ and requiring all-grid blindness $h(\log n) = 0$ ($\forall n \ge 2$) costs linear Lévy energy $\ge \frac{e^{-1/2}}{4}T$.
- **However**, [`exists_smooth_infinite_grid_polar_recovery`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BiScaleUncertainty/InfiniteGridPolarRecovery.lean#L127-L162) shows that if you **compress** the seed $f$ by scale $L = 8(D+1)(N+1)$ (`k = sourceRescale f L`) so that the support of $h_k$ has radius $\rho = \frac{1}{8(N+1)} < \frac{1}{2(N+1)}$, and place the polar copy at the **logarithmic midpoint**
  $$T_N = \frac{\log N + \log(N+1)}{2},$$
  then **every** grid node $\log n$ ($n \ge 2$) has $|\log n - T_N| \ge \frac{1}{2(N+1)} > \rho$ and $\log n \ge \log 2 > \rho$. Thus $h_{\operatorname{polarCopy}(k, T_N)}(\log n) = 0$ **identically for all $n \ge 2$** simply because the compressed support sits entirely inside the open gap $(\log N, \log(N+1))$!
- Because $w_{\mathrm{arch}}(x) = \frac{e^{x/2}}{\sinh x} \sim \frac{1}{x}$ has only a logarithmic singularity at $x = 0$, compressing $f$ by factor $L \asymp N$ only costs normalized archimedean energy $\mathcal{J}_{\mathrm{arch}}(k)/h_k(0) \le A + \log L \asymp \log N \asymp T_N$ ([`sourceRescale_energy_upper_bound`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BiScaleUncertainty/LogarithmicCompressionEnergy.lean#L254-L282)).

---

### 2. The Root Mathematical Diagnosis: Why "All-Grid Blindness" ($h_f(\log n) = 0$) Is the Wrong Paradigm for `HF` and `EWU`

There are two critical observations about why the current "grid-blindness" paradigm cannot close `HF` or `EWU`:

1. **Wait—the compressed midpoint copy in `InfiniteGridPolarRecovery.lean` has normalized archimedean energy $\asymp \log N \to +\infty$!**
   In the actual Weil explicit formula, the archimedean threshold needed to beat the constant anomaly $-\Omega(0)h_f(0)$ is $|\Omega(0)| = \frac{\pi}{2} + \gamma + 3\log 2 \approx 2.752$. A compressed two-copy source at midpoint $T_N = \frac{\log N + \log(N+1)}{2}$ has normalized archimedean energy $\ge c \log N \gg 2.752$ for large $N$, so it **already satisfies $\operatorname{weilArchRe} > 0$** at large $N$!
   Conversely, any source with moderate archimedean energy $\mathcal{J}_{\mathrm{arch}}(f)/h_f(0) \le |\Omega(0)| \approx 2.752$ **cannot** be compressed to width $\rho \ll 1/N$: its autocorrelation width is bounded below by an absolute constant $\rho_0 \asymp e^{-|\Omega(0)|}$, so at scale $T \gg 1$ its support inevitably spans $\asymp e^T \rho_0$ grid points!

2. **Why Pure Grid-Blindness ($h_f(\log n) = 0$) Can NEVER Supply the Signed Full-Prime Estimate:**
   Look at the complete Weil functional for a general test function $f$:
   $$\mathcal{W}(f) = \Omega(0)h_f(0) + \underbrace{\int_0^\infty (h_f(0) - h_f(x))\frac{e^{x/2}}{\sinh x}\,dx}_{\mathcal{J}_{\mathrm{arch}}(f)} + \underbrace{2\sum_{n=2}^\infty \frac{\Lambda(n)}{\sqrt{n}} h_f(\log n)}_{\mathcal{Q}_{\mathrm{prime}}(f)} - \underbrace{4\int_0^\infty h_f(x)\cosh(x/2)\,dx}_{\mathcal{Q}_{\mathrm{polar}}(f)}.$$
   When you restrict to the **blind subspace** $h_f(\log n) = 0$:
   - You multiply the von Mangoldt weights $\frac{\Lambda(n)}{\sqrt{n}}$ by $0$ and **erase the prime distribution from the theorem**! Any theorem whose only arithmetic hypothesis is $h_f(\log n) = 0$ ($\forall n \ge 2$) is invariant under replacing $\Lambda(n)$ by $0$, or by $100\Lambda(n)$, or by the Dirichlet coefficients of the off-line countermodel $\zeta(s-a)\zeta(s+a)$ ([`NonTemperedShiftedZetaPairCountermodel.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/NonTemperedShiftedZetaPairCountermodel.lean)), which is supported on the **exact same** set $\{\log p^k\}$!
   - Even worse, for general test functions in `EWU` and `HF`, $h_f(\log n)$ is **not zero**—it is **signed** ($h_f(\log n) \in \mathbb{R}$):
     - When $h_f(x) > 0$ on a broad interval, the polar term $-4\int_0^\infty h_f(x)\cosh(x/2)\,dx$ is huge and negative, and **cannot** be paid by $\mathcal{J}_{\mathrm{arch}}(f)$ alone; it can **only** be paid by the positive discrete prime sum $+2\sum_{n \ge 2} \frac{\Lambda(n)}{\sqrt{n}} h_f(\log n)$ (since $\sum_{n \le e^x} \Lambda(n) \sim e^x$ matches the leading polar density $2\cosh(x/2) \sim e^{x/2}$ after the $n^{-1/2} = e^{-x/2}$ weighting!).
     - Conversely, when $h_f(\log n) < 0$ at primes, the prime sum $\mathcal{Q}_{\mathrm{prime}}(f)$ itself is negative and must be paid by $\mathcal{J}_{\mathrm{arch}}(f) - \mathcal{Q}_{\mathrm{polar}}(f)$.

---

### 3. How `BiScaleUncertainty` Must Evolve: From Blind Pinning ($h_f(\log n) = 0$) to Signed Krein–Kantorovich Measure Transport

Look at the algebraic heart of every collar inequality in `BiScaleUncertainty`. Previously, at a node $t_k = \log n_k$ and collar offset $\pm y \in (-\delta, \delta)$, we assumed $h_f(t_k) = 0$ in order to write:
$$h_f(0) - h_f(t_k \pm y) = h_f(0) - \bigl(h_f(t_k \pm y) - h_f(t_k)\bigr).$$
**Wait:** if you do **not** assume $h_f(t_k) = 0$, that equation is STILL an exact identity provided you keep $+h_f(t_k)$ on the left-hand side:
$$\bigl(h_f(0) - h_f(t_k \pm y)\bigr) + h_f(t_k) = h_f(0) - \bigl(h_f(t_k \pm y) - h_f(t_k)\bigr) = \langle f, f \rangle - \bigl\langle U_{t_k} f,\, (U_{\pm y} - I) f \bigr\rangle_{L^2(\mathbb{R})}!$$
Look at what this single observation does when integrated against any physical collar partition $\rho$ with node collar masses
$$M_k(\rho) := \int_0^\delta \bigl(\rho_k^-(y)w_{\mathrm{arch}}(t_k - y) + \rho_k^+(y)w_{\mathrm{arch}}(t_k + y)\bigr)\,dy:$$

1. **The Signed Krein Collar Transfer Theorem (No Blindness Required):**
   By Krein's increment inequality $|h_f(t_k \pm y) - h_f(t_k)| \le \sqrt{2 h_f(0)(h_f(0) - h_f(y))}$, for **every** $f \in L^2(\mathbb{R})$ with **arbitrary signed values $h_f(t_k) \in \mathbb{R}$**:
   $$\int_0^\infty \bigl(h_f(0) - h_f(x)\bigr)w_{\mathrm{arch}}(x)\,dx + \sum_{k} M_k(\rho)\,h_f(t_k) \ge C_{\mathrm{Krein}}(\rho)\, h_f(0)!$$
   And what is the natural scale of the collar mass $M_k(\rho)$ at $t_k = \log n$?
   Since $w_{\mathrm{arch}}(\log n) = \frac{e^{(\log n)/2}}{\sinh(\log n)} = \frac{2}{\sqrt{n}(1 - n^{-2})} \sim \frac{2}{\sqrt{n}}$, the archimedean Lévy weight at $x = \log n$ has the **exact $n^{-1/2}$ scaling of the Weil prime weight $\frac{\Lambda(n)}{\sqrt{n}}$**!
   - When $h_f(\log n) < 0$ (negative prime correlation!), $h_f(x)$ near $\log n$ is forced by Krein continuity to also be negative, so $(h_f(0) - h_f(x)) \approx 2 h_f(0)$ in the archimedean integral **automatically pays for the negative prime term $+M_n(\rho) h_f(\log n)$** and still leaves $+h_f(0)$ of positive margin!

2. **Signed Prime-to-Polar Measure Transport ($\mu_\Lambda$ vs. $\mu_{\mathrm{polar}}$):**
   Instead of treating $\mathcal{Q}_{\mathrm{prime}}(f) = 2\sum_{n \ge 2} \frac{\Lambda(n)}{\sqrt{n}} h_f(\log n)$ and $\mathcal{Q}_{\mathrm{polar}}(f) = 4\int_0^\infty h_f(x)\cosh(x/2)\,dx$ as separate functionals, write their difference as a **signed measure-transport pairing**:
   $$\mathcal{Q}_{\mathrm{prime}}(f) - \mathcal{Q}_{\mathrm{polar}}(f) = 2\int_0^\infty h_f(x)\,d\bigl(\mu_\Lambda - \mu_{\mathrm{polar}}\bigr)(x),$$
   where $d\mu_\Lambda = \sum_{n \ge 2} \frac{\Lambda(n)}{\sqrt{n}}\,\delta_{\log n}$ and $d\mu_{\mathrm{polar}} = 2\cosh(x/2)\,dx$.
   For any nonnegative transport plan $\pi(dx, dy)$ coupling $\mu_\Lambda$ to $\mu_{\mathrm{polar}}$ (up to a bounded-support remainder) with jump-length distribution $\nu_\pi(dz) = (|x - y|)_* \pi$, Krein's increment inequality plus Cauchy–Schwarz against $w_{\mathrm{arch}}(z)$ yields the **unconditional signed lower bound**:
   $$\mathcal{J}_{\mathrm{arch}}(f) + \int_0^\infty h_f\,d\mu_1 - \int_0^\infty h_f\,d\mu_2 \ge -\frac{h_f(0)}{2}\int_0^\infty \frac{\rho_\pi(z)^2}{w_{\mathrm{arch}}(z)}\,dz,$$
   where $\frac{1}{w_{\mathrm{arch}}(z)} = e^{-z/2}\sinh z \sim z$ **vanishes linearly as $z \to 0^+$**, penalizing local prime-to-polar transport jumps of size $z$ by only $O(z)$!

3. **Fixed-Energy Width Rigidity (Closing the Midpoint Compression Escape at Bounded Energy):**
   To defeat `Trap 8` ([`InfiniteGridPolarRecovery.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BiScaleUncertainty/InfiniteGridPolarRecovery.lean)) in the regime relevant to `EWU`/`HF` (where $\mathcal{J}_{\mathrm{arch}}(f)/h_f(0) \le K$ is bounded, e.g. $K = |\Omega(0)|$), we prove the **converse** of `InfiniteGridPolarRecovery`: any source whose normalized archimedean energy is $\le K$ cannot have its mass compressed into a midpoint gap $(\log N, \log(N+1))$ once $\log N \gg K$, because vanishing at the grid nodes inside a window of width $\asymp e^{-K}$ around $T$ forces $\mathcal{J}_{\mathrm{arch}}(f)/h_f(0) \gtrsim \log N > K$.

---

### Proposed Next Phase for `BiScaleUncertainty`

If you agree with this diagnosis, our immediate priority as the lead workstream should be to move `BiScaleUncertainty` out of the **"blind-only ($h_f(\log n) = 0$) box"** and formalize the **Signed Arithmetic & Measure-Transport Pillars**:

1. **Pillar XIV (`SignedKreinCollarAndPrimeDeficitTransfer.lean`):**
   Drop the blindness hypothesis $h_f(\log n) = 0$ and prove the **Signed Krein Collar Transfer Theorem**: for any physical collar weights around nodes $t_k = \log n_k$ and any $f \in L^2(\mathbb{R})$ with **signed** correlations $h_f(t_k) \in \mathbb{R}$,
   $$\mathcal{J}_{\mathrm{arch}}(f) + \sum_{k} M_k(\rho)\,h_f(t_k) \ge C_{\mathrm{Krein}}(\rho)\,h_f(0),$$
   together with the multi-node Gram/Cauchy–Schwarz refinement using $h_f(t_k) - h_f(t_k \pm y) = \langle U_{t_k}f, (I - U_{\pm y})f\rangle$.
2. **Pillar XV (`KreinKantorovichMeasureTransportAndPrimePolarPairing.lean`):**
   Formalize the **Krein–Kantorovich Signed Measure-Transport Inequality** coupling any discrete arithmetic measure $\mu_{\mathrm{disc}} = \sum_k a_k \delta_{t_k}$ to any continuum polar density $\mu_{\mathrm{cont}} = p(x)\,dx$ via local collar transport plans $\pi$, proving that
   $$\mathcal{J}_{\mathrm{arch}}(f) + \int h_f\,d\mu_{\mathrm{disc}} - \int h_f\,d\mu_{\mathrm{cont}} \ge -\frac{h_f(0)}{2}\int_0^\infty \frac{\rho_\pi(z)^2}{w_{\mathrm{arch}}(z)}\,dz$$
   with the exact origin-regularizing reciprocal weight $w_{\mathrm{arch}}(z)^{-1} = e^{-z/2}\sinh z$.

Shall I proceed directly with developing and formalizing **Pillar XIV** and **Pillar XV**?