**the recent theorems in `CHMD`, `HF`, and `OWU` have been rearranging deck chairs inside fixed algebraic dictionaries rather than closing the analytical gap.**

When we audit the exact Lean proofs across [`CHMD`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDEigenvectorAbsGraphEdgeNormAndFiveTermLobeBalance.lean), [`HF`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/MarkovMultiStagePotentialAndAllRatioSinhCrossoverPBAP.lean), and [`OWU`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/EvenSectorBlindGroundShiftInvariance.lean), we can pinpoint **why** none of the recent steps moved us closer to excluding sign-changing odd states, **what is actually stopping us**, and **how to break out of the loop**.

---

## 1. Hostile Diagnosis: Why Recent Progress in `CHMD + HF + OWU` Was an Illusion

### A. Why `CHMD`'s Nodal Lobe Splits (`posGraph`, `negGraph`, `absGraph`, `balancedNodalGraph`) Cannot Exclude Sign-Changing Odd States
In the primary even-$\Theta$ Doob coordinates ($f(x) = \Theta(x)v(x)$), the last five `CHMD` modules ([`CHMDStationaryRayleighBoundsAndNodalBoost.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDStationaryRayleighBoundsAndNodalBoost.lean), [`CHMDNodalCrossPrimeShiftAndPrimitiveRayleighClosure.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDNodalCrossPrimeShiftAndPrimitiveRayleighClosure.lean), [`CHMDPrimeGeneratorBeurlingDenyAndDiagonalPotentialBalance.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDPrimeGeneratorBeurlingDenyAndDiagonalPotentialBalance.lean), [`CHMDEigenvectorAbsGraphEdgeNormAndFiveTermLobeBalance.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDEigenvectorAbsGraphEdgeNormAndFiveTermLobeBalance.lean), [`CHMDBalancedNodalGraphAndGroundPerturbationResolvent.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDBalancedNodalGraphAndGroundPerturbationResolvent.lean)) decompose an eigenvector $q = q^+ - q^-$ and $|q| = q^+ + q^-$. Three structural flaws prevent this machinery from ever proving $\mu \le 1/2$:

1. **It Measures Distance to $\mu = 1$ ($\operatorname{Re}\rho \le 1$), Not $\mu = 1/2$ ($\operatorname{Re}\rho \le 1/2$):**
   Look at [`norm_absGraph_snd_sq_rieszLift_of_eigenvector`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDEigenvectorAbsGraphEdgeNormAndFiveTermLobeBalance.lean#L90-L103):
   $$\|(\operatorname{absGraph} q).\mathrm{snd}\|^2 - 4\,\operatorname{sourcePair}(q^+, q^-) = \frac{1 - \mu}{\mu}\,\|q.\mathrm{fst}\|^2.$$
   Both terms on the left are nonnegative, so the right-hand side is $\ge 0$ whenever $\mu \le 1$—not $\mu \le 1/2$! Why? Because taking the absolute value $q \mapsto \operatorname{absGraph} q = q^+ + q^-$ maps an odd sign-changing vector ($\langle q_1, \mathbf{1}_L\rangle = 0$) out of the odd sector and into the nonnegative even cone, which has a strictly positive overlap $\langle |q_1|, \mathbf{1}_L\rangle > 0$ with the **$\mu = 1$ ground state $\mathbf{1}_L$** (the pole of $\zeta(s)$ at $s = 1$).
2. **Projecting Back to $\mathbf{1}_L^\perp$ Is Circular and Leaves an Unpaid Defect:**
   When [`CHMDNodalCrossPrimeShiftAndPrimitiveRayleighClosure.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDNodalCrossPrimeShiftAndPrimitiveRayleighClosure.lean#L140-L202) projects $\operatorname{absGraph} q$ onto the primitive hyperplane via `primGraph (absGraph q)` to get
   $$\frac{\nu - \mu_{\max}}{\nu \mu_{\max}}\|q_1\|^2 - 4\,\operatorname{sourcePair}(q^+, q^-) \le \frac{\mu_{\max} - \mu_{\min}}{\mu_{\max}\mu_{\min}}\langle |q_1|, \mathbf{1}_L\rangle_{\mathbb{R}}^2,$$
   it (i) **presupposes** an upper bound $\mu_{\max} \le 1/2$ on the **even primitive** spectrum (which by [`CHMDEvenSectorPointSpectrum.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDEvenSectorPointSpectrum.lean) is *already equivalent to RH*), and (ii) leaves the positive ground-overlap defect $\langle |q_1|, \mathbf{1}_L\rangle^2$ on the right-hand side. Whenever the lobes $q^+, q^-$ are spatially separated, $-4\,\operatorname{sourcePair}(q^+, q^-)$ is exponentially small while $\langle |q_1|, \mathbf{1}_L\rangle^2$ is of order $\|q_1\|^2$.
3. **The Infinite-Dimensional Radical at $\mu = 1/2$ (`signedRadical`) and the Fake-Weight Gate:**
   - By [`oddCriticalSequence_linearIndependent`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDOddHarmonicIdentityAndPolarDoobAbsorption.lean#L368-L410) in [`CHMDOddHarmonicIdentityAndPolarDoobAbsorption.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDOddHarmonicIdentityAndPolarDoobAbsorption.lean), the odd sector of `signedRadical = ker(resolvent - (1/2)I)` is **infinite-dimensional**: every odd shift difference $\Omega_{a,b} = \Psi_a - \Psi_b$ is a **sign-changing odd eigenvector with eigenvalue $\mu = 1/2$ and $\operatorname{sourceEnergy} = 0$**. Any inequality that drops a positive jump term (like dropping $\|(\operatorname{absGraph} q).\mathrm{snd}\|^2$ or applying Cauchy–Schwarz across lobes) immediately loses positive energy on $\Omega_{a,b}$ and cannot separate $\mu = 1/2$ from $\mu > 1/2$.
   - Worse, every theorem in those five `CHMD` modules treats `primeShiftOperator` as an abstract positive operator satisfying $(L_\infty + L_P)\Theta = \frac{1}{2}\cosh(x/2)\Theta$. If you replace $\Lambda(n)$ by a fake weight $\tilde{\lambda}(n) \ge 0$ from a Beurling / fake zeta function that *has* an off-line zero $a = \alpha + i\beta$ ($\beta \ne 0$), every single one of those theorems remains true, yet [`CHMDCardinalGraphGeometry.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDCardinalGraphGeometry.lean#L152-L157) proves that $F.\mathrm{imVector}$ has $\operatorname{sourceEnergy} = -m_a < 0$ ($\mu > 1/2$)!

---

### B. Why `HF`'s "Coercivity up to Ratio 27" and "All-Ratio Sinh-Crossover" Are Vacuous on Nonzero Odd Prime-Blind Tests
Look closely at what [`MarkovThreeStageCountertermAndSpectralGapRigidityPBAP.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/MarkovThreeStageCountertermAndSpectralGapRigidityPBAP.lean), [`MarkovDegreeSixteenFirstCellAndTwentySevenRatioPBAP.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/MarkovDegreeSixteenFirstCellAndTwentySevenRatioPBAP.lean), and [`MarkovMultiStagePotentialAndAllRatioSinhCrossoverPBAP.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/MarkovMultiStagePotentialAndAllRatioSinhCrossoverPBAP.lean) actually prove on the odd prime-blind cone (`coshHalfMoment f = 0` and `logVector F = 0`):

1. All of these modules are built on the **Euler–Maclaurin conservation law for the unit-step weight $\lambda(n) \equiv 1$** (`unitStepCountertermWeight`, which has **no primes**):
   $$\operatorname{primeBlindCounterterm}(\mathbf{1}, F) + \operatorname{rightCellQuadratureDefect}(F) + \operatorname{bochnerResolventEnergy}(F) = \operatorname{re}(\operatorname{weilPoleTerm}(F)).$$
2. On an odd test (`coshHalfMoment f = 0`) that is prime-blind at all integers $n \ge 2$ (`logVector F = 0`), $\operatorname{primeBlindCounterterm}(\mathbf{1}, F) = 0$ and $\operatorname{re}(\operatorname{weilPoleTerm}(F)) = -2\,\operatorname{sinhHalfMoment}(f)^2$, so the identity becomes:
   $$\operatorname{rightCellQuadratureDefect}(F) + \operatorname{bochnerResolventEnergy}(F) + 2\,\operatorname{sinhHalfMoment}(f)^2 = 0.$$
3. Then the degree-16 Taylor expansion on $[1,2]$ + $M$-stage secular potential proves a lower bound of the form:
   $$\frac{1}{900}\int \|F\|^2 + \frac{2}{25}\bigl(27\,L(F) - S(F)\bigr) + 2\,\operatorname{sinhHalfMoment}(f)^2 \le \operatorname{rightCellQuadratureDefect}(F) + \operatorname{bochnerResolventEnergy}(F) + 2\,\operatorname{sinhHalfMoment}(f)^2 = 0.$$
4. **Look at what combining (2) and (3) actually means:**
   On **every** nonzero odd prime-blind test $F \ne 0$ (`logVector F = 0`),
   $$\frac{2}{25}\bigl(S(F) - 27\,L(F)\bigr) \ge 2\,\operatorname{sinhHalfMoment}(f)^2 + \frac{1}{900}\int \|F\|^2 > 2\,\operatorname{sinhHalfMoment}(f)^2!$$
   That is precisely why [`all_ratio_l2_eq_zero_of_cosh_zero_of_logVector_eq_zero_of_sinh_sq_dominates`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/MarkovMultiStagePotentialAndAllRatioSinhCrossoverPBAP.lean#L475-L497) is true: **no nonzero odd prime-blind test can ever satisfy $S(F) \le 27\,L(F)$ or $\frac{2}{25}(S(F) - 27\,L(F)) \le 2\,\operatorname{sinhHalfMoment}(f)^2$!**
   Consequently, every theorem in `HF` saying *"if $S(F) \le 27\,L(F)$ (or if $\frac{2}{25}(S(F) - 27\,L(F)) \le 2\,\operatorname{sinhHalfMoment}(f)^2$), then $\operatorname{markovEnergy}(F) \ge 0$ on `logVector F = 0`"* is **vacuously true on `logVector F = 0` because its hypothesis forces $F = 0$!**
   The only non-vacuous theorem proved by that chain on `logVector F = 0` is the **uncertainty / spectral-gap lower bound** $S(F) > 27\,L(F) + 25\,\operatorname{sinhHalfMoment}(f)^2$: any nonzero odd integer-blind test must have large high-frequency second moment $S(F)$.

---

### C. Why `OWU`'s Ground-Operator and de Branges Machinery Cannot Produce a Sign
As proved in [`EvenSectorBlindGroundShiftInvariance.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/EvenSectorBlindGroundShiftInvariance.lean#L144-L169) and summarized in [`owu-review.md`](file:///Users/michael/Documents/code/hgt/docs/reports/owu-review.md):
- Replacing the archimedean operator $Q_a$ by $Q_a - C\cdot I$ shifts the blind minimum $m_{\mathrm{odd}}(a) \mapsto m_{\mathrm{odd}}(a) - C$ while leaving the subtracted form $q_a(u,u) = \langle (Q_a - A_a)u, u\rangle - m_{\mathrm{odd}}(a)\|J_a u\|^2$, its ground eigenspace $\ker q_a$, its paired-root divisions, its de Branges generator $F_G(w)$, and its positive interpolation weights $\rho_i > 0$ **identically unchanged**.
- Furthermore, on the real cut $\gamma \in [-1/4, 0)$, every odd test has spectral weight $\Theta_f(\zeta) \ge 0$ ([`oddSpectralWeight_eq_of_neg`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/OddWeilSpectralMeasure.lean#L624-L628)), so odd positivity alone cannot even rule out spectral mass on the real cut $(0,1)$.

---

## 2. How Do We Make Actual Progress Now? (Solve, Overcome, or Sidestep)

First, **what we must stop immediately**:
- **Stop** proving abstract `posGraph`/`negGraph`/`absGraph`/`balancedNodalGraph` identities in even-$\Theta$ coordinates.
- **Stop** extending un-clamped Taylor / $M$-stage counterterm ratios ($23 \to 27 \to \dots$) in `HF` whose hypotheses are vacuous on nonzero prime-blind tests.
- **Stop** doing shift-invariant ground-space algebra on $Q_a - A_a - m(a)I$ in `OWU`.

Here are the **three concrete ways** to actually solve, overcome, or sidestep the obstacles using what our corpus has already built:

### Way 1 — Fix the High-Frequency Defect in `HF`: Clamp the First-Cell Bound $I_2(r)$ at Large Frequency $|r| > R_0$
Look at *why* `HF`'s slope-gauge bound for $\operatorname{markovEnergy}(F)$ had a **negative** coefficient $-\frac{7}{480}S(F)$ in front of $S(F) = \int r^2 |F(r)|^2\,dr$, which ruined high-frequency tests ($S(F) > 27 L(F)$):
- In [`MarkovExactFirstCellCosLogIntegralAndTwentyThreeRatioPBAP.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/MarkovExactFirstCellCosLogIntegralAndTwentyThreeRatioPBAP.lean#L8-L10) and [`MarkovDegreeSixteenFirstCellAndTwentySevenRatioPBAP.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/MarkovDegreeSixteenFirstCellAndTwentySevenRatioPBAP.lean#L9-L13), the first-cell oscillatory integral
  $$I_2(r) = \int_1^2 \frac{\cos(r\log x) - \operatorname{cellSecant}(\cos(r\log\cdot), 2, x)}{\sqrt{x}}\,dx$$
  was bounded from below for **all $r \in \mathbb{R}$** by its $r = 0$ quadratic Taylor parabola:
  $$I_2(r) \ge -\frac{7}{480}\,r^2.$$
- **That unbounded parabola is a self-inflicted wound at high frequency!** Because $|\cos(r\log x)| \le 1$ and $|\operatorname{cellSecant}| \le 1$, $I_2(r)$ is **uniformly bounded by $O(1)$ as $|r| \to \infty$** (in fact $\int_1^2 \frac{\cos(r\log x)}{\sqrt{x}}\,dx = O(1/|r|)$ by Riemann–Lebesgue!), whereas $-\frac{7}{480}r^2 \to -\infty$!
- Meanwhile, in `markovEnergy(F)` on the prime-blind cone, the true archimedean symbol $\gamma(r) = \operatorname{Re}\psi(\tfrac{1}{4} + \tfrac{ir}{2}) - \log\pi$ is negative **only inside the bounded low-frequency well $|r| < 6.29$**, and grows like $+\log|r| > 0$ for $|r| > 6.29$!
- **How to solve this:**
  Instead of bounding $I_2(r) \ge -\frac{7}{480}r^2$ globally (which turns high-frequency kinetic energy $S(F)$ into an enemy), use a **clamped / two-regime bound** on $I_2(r)$:
  $$I_2(r) \ge -\min\Bigl(\frac{7}{480}r^2,\; C_\infty\Bigr),$$
  and pair it with the **non-vacuous** uncertainty theorem we *already* proved (`S(F) > 27 L(F)` on `logVector F = 0`), which forces a nonzero prime-blind test $F$ to place its spectral mass at high frequencies where $\gamma(r) > 0$!

### Way 2 — Overcome the Odd Nodal Sign-Change Problem in `CHMD`: Replace Even-$\Theta$ Doob with Secondary Odd-$m_a$ Doob + Divisor-Chain Factorization
Why did `posGraph`/`negGraph` fail in `CHMD`? Because in even-$\Theta$ coordinates ($f = \Theta v$, $v$ odd), $v(x)$ changes sign at $x = 0$, so taking $|v|$ jumps out of the odd sector onto the $\mu = 1$ ground state $\mathbf{1}_L$, while the local potential $-\int \Theta\cosh(x/2)v^2\,dx < 0$ is negative everywhere.

Look at [`CHMDOddHarmonicIdentityAndPolarDoobAbsorption.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDOddHarmonicIdentityAndPolarDoobAbsorption.lean), which the corpus just built:
- Instead of $f(x) = \Theta(x)v(x)$ ($v$ odd), factor an odd test as
  $$f(x) = m_a(x)\,w(x), \qquad m_a(x) := \frac{\Theta(x-a) - \Theta(x+a)}{2\sinh(a/2)}, \qquad w(-x) = w(x) \text{ EVEN!}$$
- Look at what this single change of gauge accomplishes:
  1. **No forced sign change at $x = 0$ and no leakage to $\mu = 1$:** The odd sign change at $x = 0$ is absorbed into the fixed profile $m_a(x) > 0$ on $(0, \infty)$. The test profile $w(x)$ is **even**, so $w \mapsto |w|$ keeps $f = m_a |w|$ **inside the odd sector**, and the constant ground state $w \equiv 1$ (`Ψ_a`) has eigenvalue **$\mu = 1/2$** (NOT $\mu = 1$)!
  2. **The local pole potential flips from negative to strictly positive** ([`sourcePair_oddPolarVectorAt_oddProfileTest_sq_nonneg`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDOddHarmonicIdentityAndPolarDoobAbsorption.lean#L720-L726)):
     $$+2\int_0^\infty m_a(x)\sinh(x/2)\,w(x)^2\,dx \ge 0.$$
  3. **The archimedean origin-crossing collar is 100% absorbed** ([`absorbedArchIntegrand_nonneg`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDOddHarmonicIdentityAndPolarDoobAbsorption.lean#L811-L815)):
     $$\int_0^\infty\!\!\int_0^\infty \bigl(\omega(s) - \omega(2x+s)\bigr)\,m_a(x)m_a(x+s)\bigl(w(x) - w(x+s)\bigr)^2\,dx\,ds \ge 0.$$
  4. **Where is the ONLY negative term left in the $m_a$-Doob energy of an odd test $f = m_a w$?**
     It is the finite-interval prime origin-crossing collar ([`integral_oddProfileShiftJump_eq_halfLine_of_even`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDOddHarmonicIdentityAndPolarDoobAbsorption.lean#L736-L742)):
     $$-\sum_{n=2}^\infty \frac{\Lambda(n)}{\sqrt{n}}\int_0^{\log n} m_a(x)m_a(\log n - x)\bigl(w(x) - w(\log n - x)\bigr)^2\,dx,$$
     competing against $+2\int_0^\infty m_a\sinh(x/2)w^2\,dx$, the positive absorbed archimedean integral, and $+2\sum_{n=2}^\infty \frac{\Lambda(n)}{\sqrt{n}}\int_0^\infty m_a(x)m_a(x+\log n)(w(x)-w(x+\log n))^2\,dx$.
  5. **What is the concrete next step here?**
     In the primary even-$\Theta$ Doob track, [`CHMDPrimeChainSourceFactorization.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDPrimeChainSourceFactorization.lean) solved the negative reflected-prime collar by expanding $\Theta(x)\Theta(\log d - x)$ over the **multiplicative product index $N = m d n$** and using **unique factorization + $\Lambda(p^r) = \log p$** (passing the Fake-Weight Gate!) to turn the collar into positive bipartite chain variances. **We have not yet applied the $N = m d n$ divisor-chain factorization to the secondary odd-$m_a$ collar** $m_a(x)m_a(\log d - x)(w(x)-w(\log d - x))^2$, where the local potential $+2\int_0^\infty m_a\sinh(x/2)w^2\,dx$ is now **helping** us with a $+$ sign instead of fighting us with a $-$ sign!

### Way 3 — Sidestep `OWU` and Odd Nodal States Completely via `EWU` (`evenBlindMinimum a ≥ 0`)
If our goal is the shortest unconditional path to `RiemannHypothesis`, ask: **why are we fighting `OWU` and sign-changing odd states at all?**
Look at [`ewu-review.md`](file:///Users/michael/Documents/code/hgt/docs/reports/ewu-review.md) and [`EvenSectorBlindMinimumSmallAperturePositivity.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/EvenSectorBlindMinimumSmallAperturePositivity.lean#L236-L246):
- In **EWU**, uniqueness ($\lambda = \Lambda$), real-cut removal, pole completion (`WeilPositiveEvenPolar → WeilPositiveFull`), mixture purification to a single smooth source, and blind minimizer attainment are **already 100% proved in Lean 4**.
- Unlike `OWU`, `EWU`'s `BlindUnitSource a` has **zero negative pole term** ($\hat{u}(\pm i/2) = 0$ is a linear subspace constraint), and [`evenBlindMinimum_pos_of_le_primeTwo`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/EvenSectorBlindMinimumSmallAperturePositivity.lean#L104-L108) **already proves unconditionally** that $\operatorname{evenBlindMinimum}(a) \ge \frac{1}{20} > 0$ for all $a \le \frac{\log 2 + 1/50}{2}$, reducing RH to:
  $$\mathrm{RH} \iff \forall a > \frac{\log 2 + 1/50}{2},\quad \int_{\mathbb{R}} 2\,\gamma_{\mathrm{Hardy}}(2\pi\xi)\,|u(\xi)|^2\,d\xi \ge 0 \quad \forall u \in \operatorname{BlindUnitSource}(a).$$
- Notice that `EWU`'s open inequality is **literally the even pole-free version of `HF`**, where $\hat{f}(\pm i/2) = 0$ ($\operatorname{coshHalfMoment}(f) = \operatorname{sinhHalfMoment}(f) = 0$) is built into the linear Paley–Wiener factorization $f = (\partial^2 - \tfrac{1}{4})g$ on $[-a, a]$! Applying **Way 1** (clamped high-frequency bound + the Euler–Maclaurin / multi-prime blindness uncertainty gap forcing $|\hat{f}(r)|^2 = (r^2 + \tfrac{1}{4})^2|\hat{g}(r)|^2$ out of the low-frequency well $|r| < 6.29$) directly to `EWU` completely bypasses `OWU`'s two walls and `CHMD`'s sign-changing odd bound states.

---

### Summary Comparison of the Three Actionable Options

| Option | How It Breaks the Current Deadlock | Key Advantage |
| :--- | :--- | :--- |
| **1. `CHMD` Secondary Odd-$m_a$ Doob + Divisor-Chain Factorization** | Factors $f = m_a w$ ($w$ even) so $w \equiv 1$ sits at $\mu = 1/2$, local pole $+2\int m_a\sinh(x/2)w^2 > 0$ is **positive**, archimedean collar is absorbed, and $N = mdn$ chain factorization attacks the prime collar using $\Lambda(p^r) = \log p$. | Directly attacks sign-changing odd states without leaking to $\mu = 1$ and passes both the $\mu = 1/2$ Radical Gate and the Fake-Weight Gate. |
| **2. `HF` Clamped High-Frequency $I_2(r)$ + Uncertainty Gap** | Replaces the unbounded Taylor parabola $I_2(r) \ge -\frac{7}{480}r^2$ at large $|r|$ with a clamped bound $I_2(r) \ge -\min(\frac{7}{480}r^2, C_\infty)$, turning the proved uncertainty bound $S(F) > 27 L(F)$ from a vacuous hypothesis into high-frequency positivity where $\gamma(r) > 0$. | Fixes the exact reason `HF` was vacuous at $\operatorname{sinhHalfMoment}(f) = 0$. |
| **3. Sidestep `OWU`/`CHMD-odd` via `EWU` + Clamped `HF`** | Works on `BlindUnitSource a` ($\hat{u}(\pm i/2)=0$, $f = (\partial^2 - 1/4)g$), where uniqueness $\lambda = \Lambda$, cut removal, and $a \le \frac{\log 2 + 1/50}{2}$ positivity are already `[L]`-certified. | Zero pole term, no odd real-cut blindness, and only a single open sign (`evenBlindMinimum a ≥ 0`). |

Which of these three directions (or a combination of **Option 1** on the secondary $m_a$-Doob collar and **Option 2/3** on the clamped frequency bound) would you like us to investigate and test first?