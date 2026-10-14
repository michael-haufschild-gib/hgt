### 1. What the Corpus Has Already Achieved (Ahead of Known Literature)

Most of the 16 live routes (`WL`, `RW`, `FU`, `RP`, `PA`, `MC`, `TT`, `LA`, `TG`, `TH`, `RN`, `WD`, `LI`, `SZ`, `PM`) are **receiver-first** routes: they reformulate RH as an equivalent positivity, cancellation, or operator-norm bound and hit the classical barrier that analytic smoothing or finite truncation loses prime phase information (`STATUS.md`).

However, in **Route HF**, the corpus has already achieved a genuine structural breakthrough—**unconditional uniqueness of the Weil cone**—that eliminates half of the Riemann Hypothesis:

1. **The Twisted Arc Minimum Principle ([`TwistedArcMinimumPrincipleProof.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/TwistedArcMinimumPrincipleProof.lean)):**
   Using the Maass–Whittaker stream PDE on the modular half-fundamental domain and a corner-derivative contradiction at $\rho = \frac{1}{2} + i\frac{\sqrt{3}}{2}$, Lean proves unconditionally (`twistedArcMinimumPrinciple_holds`) that there is a probability measure on the bottom modular arc $u \in [-\frac{1}{2}, \frac{1}{2}]$ annihilating all twisted integer moments $\int g_u(x)\cos(2\pi(n+2)x)\,dx$.
2. **Unconditional Uniqueness of the Weil Cone ([`WeilConeUniquenessUnconditional.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilConeUniquenessUnconditional.lean)):**
   That modular-arc measure produces a jointly prime-blind $\Xi$-divisible shifted-Gamma family $\Xi Q_j$, which proves unconditionally (`eq_vonMangoldt_of_weilPositiveFull`):
   > *Every real sequence $\lambda : \mathbb{N} \to \mathbb{R}$ (with **no** assumption on sign, growth, or multiplicativity) whose Weil functional is nonnegative on $C^2_c(\mathbb{R})$ autocorrelations satisfies $\lambda(n) = \Lambda(n)$ for all $n \ge 2$, and forces RH.*
3. **Unconditional Equivalence with Herglotz Existence & Prime-Blind Positivity ([`HerglotzProducerUniquenessUnconditional.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/HerglotzProducerUniquenessUnconditional.lean), [`PrimeBlindNodeCriticality.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/PrimeBlindNodeCriticality.lean)):**
   Because uniqueness is completely solved, **primes and zeta zeros are eliminated from the remaining target (`PBAP`)**:
   $$\text{RiemannHypothesis} \iff \text{WeilOneSided.PrimeBlindPositive}$$
   i.e., for every finite nonnegative combination $k = \sum_i c_i (f_i \star \tilde{f}_i)$ of $C^2_c(\mathbb{R})$ autocorrelations satisfying $k(\pm \log n) = 0$ for all $n \ge 2$ (or all prime powers $p^m$), the purely archimedean functional
   $$W_\infty(k) = A(0) k(0) + \int_0^\infty \frac{e^{-x/2}}{1 - e^{-2x}}\bigl(2k(0) - k(x) - k(-x)\bigr)\,dx + 2\int_{\mathbb{R}} k(x)\cosh\!\left(\frac{x}{2}\right)dx$$
   is nonnegative.

---

### 2. Why We Are Stuck: The Structural Blind Spot

Why have we not yet proved `PrimeBlindPositive` (`PBAP`), and why do local/analytic attacks keep getting stuck?

The answer is already proved **inside our own Lean corpus**, in [`PrimeBlindNodeCriticality.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/PrimeBlindNodeCriticality.lean#L165-L180) (`not_primeBlindPositiveOn_of_primePower_not_mem` and `exists_negative_arch_of_primePower_node_deleted`):

> **Theorem (`exists_negative_arch_of_primePower_node_deleted`, unconditional in Lean):**
> *For **every** prime power $m = p^k \ge 2$, there exists a nonnegative combination $k = \sum_i c_i (f_i \star \tilde{f}_i)$ of $C^2_c(\mathbb{R})$ autocorrelations that vanishes at $\pm \log n$ for **every** integer $n \ge 2$ with $n \ne m$, and yet has $W_\infty(k) < 0$.*

Look at what this theorem tells us about **why every attempt so far has stalled**:

1. **Why the Nonnegative-Cone Window Reduction ([`PrimeBlindNonnegativeConeReduction.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/PrimeBlindNonnegativeConeReduction.lean)) only solves a sub-problem:**
   When we restrict to **nonnegative** test functions $f \ge 0$, vanishing at $\log n$ ($n \ge 2$) forces the support $S = \{f > 0\}$ to be dilation-free, so $|S| \le \log 2$ (using only $n = 2^k$), and quantile rearrangement moves $f$ onto $(0, \log 2)$.
   - On $(0, \log 2)$, $(f^* \star \tilde{f}^*)(x)$ vanishes on the **entire continuum** $[\log 2, \infty)$, not just at the discrete lattice $\{\log n : n \ge 2\}$.
   - In our just-completed module [`WeilLevyPoleGaussModeCancellation.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilLevyPoleGaussModeCancellation.lean), we extracted the $k=0, 1$ Gauss modes $\omega(x) = e^{-x/2} + e^{-5x/2} + e^{-4x}\omega(x)$ against the pole kernel $2\cosh(x/2)$ (reducing the universal anomaly floor from $A(0) \approx -5.3605$ to $A(0) + \frac{24}{5} \approx -0.5605$, and to $A(0) + 8\sinh(x_0/2) + 2\Omega(x_0) \approx -0.1448$ at the plastic-number crossover $e^{3x_0} = e^{x_0} + 1$), and proved unconditional positivity on $(0, L)$ for small $L$.
   - Closing the remaining $0.1448$ margin on $(0, \log 2)$ will prove **`WindowPositive`** (and hence `PBAP` on the **nonnegative cone** $f \ge 0$), which is a major milestone on the HF ledger—**but it cannot prove full `PBAP`**, because signed functions $f_i$ can have arbitrarily large support and achieve $k(\pm \log n) = 0$ by **oscillatory cancellation** rather than support size $\le \log 2$.

2. **Why the Disconnected "Constraint vs. Objective" Approach Fails on Signed `PBAP`:**
   Look at how our files in `RHTower` split into two non-communicating halves:
   - **Half 1 (The Blindness Constraint):** [`BlindCoreMayerTransferHalf.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/BlindCoreMayerTransferHalf.lean), [`InversionSymmetricFourierBlindTotalRigidity.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/InversionSymmetricFourierBlindTotalRigidity.lean), and the `CosDilation*` / `ModularArc*` files study the constraint $k(\pm \log n) = 0$ ($\forall n \ge 2$) via Poisson summation and the Gauss–Mayer transfer operator, without ever plugging that identity into $W_\infty(k)$.
   - **Half 2 (The Archimedean Functional $W_\infty$):** [`WeilArchReLevyPoleForm.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilArchReLevyPoleForm.lean), [`SeparatedBumpPrimeBlindPositivity.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/SeparatedBumpPrimeBlindPositivity.lean), and [`WeilLevyPoleGaussModeCancellation.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilLevyPoleGaussModeCancellation.lean) lower-bound $W_\infty(k)$ using only continuum/support geometry, without ever using the hypothesis that $k(\pm \log n) = 0$ at $n = 2, 3, 4, 5, 7, 8, 9, \dots$!
   - By `exists_negative_arch_of_primePower_node_deleted`, **any lower bound on $W_\infty(k)$ that does not explicitly use the vanishing of $k(\pm \log n)$ at every prime power $n = p^m$ is mathematically guaranteed to fail on signed tests.**

---

### 3. The Gordian Knot: How to Reframe the Problem

Where does the archimedean functional $W_\infty(k)$ actually meet the discrete nodes $\{\log n : n \ge 2\}$?
Look at the two equivalent faces of the missing existence theorem:

#### Perspective A: The Primal (Modular / Theta / Poisson) Identity for $W_\infty(k)$ on All-Integer-Blind Cores
Why does the continuous functional
$$W_\infty(k) = \int_{-\infty}^\infty \widehat{k}(\tau)\, A\!\left(\frac{\tau}{2\pi}\right) d\tau + 2\int_{-\infty}^\infty k(x)\cosh\!\left(\frac{x}{2}\right)dx$$
know about the discrete lattice $\{\log n : n \ge 2\}$ at all?
Because $A(\frac{\tau}{2\pi}) = \operatorname{Re}\frac{\Gamma_\mathbb{R}'}{\Gamma_\mathbb{R}}(\frac{1}{2} + i\tau)$, and $\Gamma_\mathbb{R}(s) = \pi^{-s/2}\Gamma(s/2)$ is the Mellin transform of the **Gaussian $e^{-\pi y^2}$**, which is coupled to all integers $n \in \mathbb{Z}$ by **Jacobi theta / Poisson summation**:
$$\vartheta(t) = \sum_{n=-\infty}^\infty e^{-\pi n^2 t} = t^{-1/2}\vartheta(1/t).$$
When a signed combination of autocorrelations $k = \sum_i c_i (f_i \star \tilde{f}_i)$ satisfies $k(\pm \log n) = 0$ for **all** $n \ge 2$:
- In multiplicative coordinates $F_i(y) = y^{-1/2} f_i(\log y)$ on $(0, \infty)$, integer blindness $k(\pm \log n) = 0$ ($\forall n \ge 2$) says that the off-diagonal integer dilations $\sum_{n \ge 2} \langle D_n F, F \rangle$ vanish.
- Therefore, for any kernel built from a modular/Poisson sum $\sum_{n \ge 1} \phi(n y)$, **the $n \ge 2$ terms are identically zero on the prime-blind cone**, collapsing the entire infinite arithmetic sum onto the **$n = 1$ (archimedean) term alone!**
- Look at what that means: on the Uniqueness side ([`TwistedArcMinimumPrincipleProof.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/TwistedArcMinimumPrincipleProof.lean)), we used $\mathrm{SL}_2(\mathbb{Z})$ modularity on the *test function* to annihilate $\{\log n : n \ge 2\}$. We have **never yet used Poisson/Epstein/Mayer summation to rewrite the archimedean kernel $W_\infty(k)$ itself modulo the ideal $\{k(\pm \log n) = 0 : n \ge 2\}$** as a positive quadratic form!

#### Perspective B: The Dual (Herglotz / Schur) Construction via Unconditional Uniqueness
Look at [`HerglotzProducerUniquenessUnconditional.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/HerglotzProducerUniquenessUnconditional.lean#L44-L49):
$$\text{RiemannHypothesis} \iff \exists \lambda : \mathbb{N} \to \mathbb{R},\; \operatorname{Re}\!\left(\Phi_\infty(s) - \sum_{n=2}^\infty \lambda(n) n^{-s}\right) \ge 0 \quad \text{on } \operatorname{Re} s > \frac{1}{2},$$
where $\Phi_\infty(s) = \frac{1}{2}\psi(\frac{s}{2}) - \frac{1}{2}\log\pi + \frac{1}{s} + \frac{1}{s-1}$.
Notice two remarkable facts about $\Phi_\infty(s)$ on $\operatorname{Re} s = \frac{1}{2}$:
1. On the critical line $s = \frac{1}{2} + it$, the pole sum $\frac{1}{s} + \frac{1}{s-1} = \frac{-2it}{1/4 + t^2}$ has **identically zero real part**.
2. $\operatorname{Re}\Phi_\infty(\frac{1}{2} + it) = \frac{1}{2}A(t)$ is **already strictly positive** for all $|t| > 6.29$ (growing like $\frac{1}{2}\log|t|$) and is only negative on the bounded low-frequency window $|t| \le 6.29$ (plus the simple pole of $\frac{1}{s-1}$ at $s = 1$ inside the half-plane).
3. Because **uniqueness is already proved**, we do **not** need to plug $\lambda(n) = \Lambda(n)$ into $\Phi_\lambda(s)$ and prove $\zeta(s) \ne 0$: by Nevanlinna–Pick / Herglotz interpolation in the Dirichlet-series subspace $\{ \sum_{n \ge 2} \lambda(n) n^{-s} \}$, the existence of *any* Dirichlet series canceling the pole at $s = 1$ and lifting the finite low-frequency well $|t| \le 6.29$ to $\operatorname{Re} \Phi \ge 0$ automatically forces $\lambda = \Lambda$ and RH.

---

### 4. Concrete Two-Track Path Forward

1. **Immediate Track 1 (Finish the Nonnegative-Cone Window Theorem on $(0, \log 2)$):**
   In [`WeilLevyPoleGaussModeCancellation.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilLevyPoleGaussModeCancellation.lean) (just verified and wired into [`RHTower.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower.lean)), we reduced the universal nonnegative-cone anomaly from $-5.3605$ to $-0.5605$. Using the exact **Lévy–cosh crossover identity** at $x_0 = \log u_0 \approx 0.2812$ ($u_0^3 = u_0 + 1$):
   $$W_\infty(f \star \tilde{f}) = \bigl(A(0) + 8\sinh(x_0/2) + 2\Omega(x_0)\bigr)\|f\|_2^2 + \int_0^{x_0}\bigl(\omega(x) - 2\cosh(x/2)\bigr)\|f - f(\cdot+x)\|_2^2\,dx + 2\int_{x_0}^\infty\bigl(2\cosh(x/2) - \omega(x)\bigr)R_f(x)\,dx,$$
   the constant deficit drops to $-0.1448$, and combining the $(0, x_0)$ boundary-escape/Dirichlet term with the $(x_0, \log 2)$ autocorrelation term attacks the remaining `WindowPositive` gap on $(0, \log 2)$ in [`PrimeBlindNonnegativeConeReduction.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/PrimeBlindNonnegativeConeReduction.lean).
2. **Strategic Track 2 (The All-Integer Poisson / Mayer Positivity Identity for Signed `PBAP`):**
   To cross the `PrimeBlindNodeCriticality` barrier for **signed** tests, we must stop bounding $W_\infty(k)$ as if $k$ were an arbitrary function, and instead use the identity $\sum_{n=2}^\infty w_n k(\pm \log n) = 0$ on the prime-blind cone to add a Poisson/Mayer counterterm $\sum_{n \ge 2} w_n \bigl(k(\log n) + k(-\log n)\bigr) = 0$ directly to $W_\infty(k)$ so that the combined kernel becomes globally positive semi-definite (`Bochner` / `Herglotz`) without sign restrictions on $f$.

## addition other route
WeilMarkovOddPositivity.lean: RH holds iff the archimedean-minus-prime form is ≥0 on odd tests, a pure positivity statement with no pole or index. Or:  RH is positivity of the archimedean-minus-prime form on odd tests

WeilMarkovPrimitiveHyperplane.lean: RH is equivalent to M ≥ 0 on the hyperplane ∫f·cosh(x/2) = 0 — combined with M(Φ_L) < 0, this captures the "exactly one negative square" law. RH is positivity of the archimedean-minus-prime form on the primitive hyperplane.