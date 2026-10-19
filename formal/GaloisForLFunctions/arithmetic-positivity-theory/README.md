# Arithmetic Positivity Theory (`GaloisForLFunctions.ArithmeticPositivityTheory`)

We study when exact arithmetic structure forces positivity and cancellation at the critical scale, and how that structure governs the sign, stability, and negative index of explicit-formula spectral energies.

See [docs/reports/arithmetic-positivity-theory/README.md](../../../docs/reports/arithmetic-positivity-theory/README.md) and [research-foundational.md](../../../docs/reports/arithmetic-positivity-theory/research-foundational.md) for the full research programme.

---

## 1. Motivation

Explicit-formula and Weil-positivity reductions for L-functions split a complete spectral energy $\mathcal{W}(f, f)$ into competing archimedean, prime-power, and polar contributions, or equate global positivity to a one-sided critical-scale cancellation bound on the integrated prime deficit
$$D(T) = \int_0^T \bigl(e^t - \psi(e^t)\bigr)\,dt.$$
However, **exact identities and self-adjoint operator realizations do not supply the arithmetic estimates needed to determine the sign of the form**:
- A self-adjoint operator or Krein-space involution does not exclude a negative ground state.
- Positivity of one piece (such as the archimedean jump integral or a Markovian Dirichlet form $\mathcal{M}_N(g)$) does not determine the sign of the complete form $\mathcal{W}(g, g) = \mathcal{M}_N(g) + \frac{1}{2}C(g)^2 - \frac{1}{2}S(g)^2$.
- Without already knowing that $\mathcal{W}$ is positive semidefinite, one **cannot** apply Cauchy–Schwarz to $\mathcal{W}(f, g)$ itself to bound mixed interaction terms.

Arithmetic Positivity Theory (APT) addresses this gap directly: **which independently checkable features of an arithmetic source control mixed couplings, preserve positivity under perturbation, or force negative directions?**

---

## 2. Objects and Language

Every object in APT carries its exact normalization, domain of holomorphy/integrability, and dependence on arithmetic scale:

| Object | Mathematical Definition & Role |
| :--- | :--- |
| **Exact arithmetic source** | A test family built from literal prime-power weights $\Lambda(n)$, divisor identities $\sum_{d \mid k} \Lambda(d) = \log k$, or factorial/Bernoulli sawtooth remainders, retaining all endpoint jumps and collar shifts. |
| **Completed source data** | The arithmetic source paired with its archimedean Gamma factor, polar residues at $s = 0, 1$, boundary corrections, and smoothing kernel $\eta_k$. |
| **Test and Mellin readout** | A physical source $f : \mathbb{R} \to \mathbb{C}$ and its transform $F_f(s) = \int_{\mathbb{R}} f(x)e^{(s - 1/2)x}\,dx$. Compactly supported tests have entire readouts; noncompact tails require explicit half-plane holomorphy ($\operatorname{Re} s > -1$). |
| **Complete Weil form $\mathcal{W}(f, g)$** | The reflection-paired spectral energy $\sum_\rho m_\rho F_f(\rho)\overline{F_g(1 - \overline{\rho})}$ on the nontrivial zero divisor (with multiplicity $m_\rho$), identified with the physical explicit-formula functional on admitted tests. Positivity is a target to prove, never part of the definition. |
| **Positive comparison form $\mathcal{Z}(f)$** | An independently nonnegative majorant $\mathcal{Z}(f) = \sum_\rho m_\rho |F_f(\rho)|^2$ (or a physical Riesz window norm) used to bound indefinite mixed pairings via $\|\mathcal{W}(f, g)\| \le \sqrt{\mathcal{Z}(f)\mathcal{Z}(g)}$ without assuming $\mathcal{W} \ge 0$. |
| **Correction and defect** | The exact decomposition $r = H - U$ relating a target physical source $r$ (such as a compact ramp) to a pole-corrected source $H$ and a tractable tail $U$. Both the diagonal $\mathcal{W}(H, H)$ and mixed terms $\mathcal{W}(H, U)$ must be controlled. |
| **Scale and residual form** | Support aperture, arithmetic cutoff $N$, frequency band, or smoothing index $k$, together with the Schur complement $A - M^2/(4D)$ remaining after eliminating an invertible positive block. |
| **Sign and stability data** | Relative margin $\operatorname{Re}\mathcal{W}(u, u) \ge \delta\mathcal{Z}(u)$, perturbation ratio $\mathcal{Z}(h) \le \varepsilon\mathcal{Z}(u)$, Riesz frame bounds on coefficient space, or sharp sign-flip thresholds. |

---

## 3. Core Mechanisms

1. **Exact Arithmetic Compression:**
   Use divisor and Bernoulli identities to eliminate leading polynomial drifts before estimating.
   - *Divisor-log resummation:* $\sum_{d \mid k} \Lambda(d) = \log k$ collapses finite prime-shift rectangles into logarithmic sums when support conditions hold.
   - *Divisor-stencil Bernoulli filters:* Combining dilated copies of the periodic clamped Bernoulli kernel $K_1(x) = \{x\}^2/2 - \{x\}/3$ across a finite divisor stencil (such as the dyadic stencil $(4, -2, 1/4)$ on $\{1, 2, 4\}$) annihilates both parabolic and linear collar drifts while keeping the fundamental $k = 1$ Fourier harmonic strictly dominant over the $k \ge 2$ tail.

2. **Independent Control of Mixed Terms via Zero-Divisor Sampling:**
   Because $\rho \mapsto 1 - \overline{\rho}$ is a multiplicity-preserving involution on the zero divisor, Cauchy–Schwarz in $\ell^2(m_\rho)$ gives the unconditional bound $|\mathcal{W}(f, g)| \le \sqrt{\mathcal{Z}(f)\mathcal{Z}(g)}$.
   - To bound $\mathcal{Z}(f)$ without assuming zero locations, combine the subharmonic disk mean-value inequality on the half-plane of holomorphy with unconditional unit-height zero counts $O(\log(2 + |t|))$ and weighted $L^2$ translation regularity $D(h) \le C\min(N^{-1}, h)$ integrated against $dh/h$.
   - When a decomposition $r = H - U$ exhibits a **scale separation** between the correction budget $\mathcal{Z}(H) = O(1/N)$ and the tail diagonal $\operatorname{Re}\mathcal{W}(U, U) \gtrsim \log N / N$ (with $\mathcal{Z}(U) = O(\log N / N)$), the mixed pairing $|\mathcal{W}(H, U)| = O(\sqrt{\log N}/N)$ is strictly lower order and positivity transfers from $U$ to $r$.

3. **Exact Block and Parity Elimination with Controlled Residuals:**
   - *Schur complement elimination:* In a 2-block system $Q(c, d) = A c^2 + M c d + D d^2$ with $D > 0$, completing the square isolates the residual $A - M^2/(4D)$. Positivity holds if and only if the coupling cost $M^2/(4D)$ is strictly smaller than the diagonal margin $A$.
   - *Hyperbolic pole parity decoupling:* In the Markov–pole decomposition $\mathcal{W}(g) = \mathcal{M}_N(g) + \frac{1}{2}C(g)^2 - \frac{1}{2}S(g)^2$, reflection parity $u \mapsto -u$ orthogonally decouples the stabilizing $\cosh$ functional (supported purely on even tests) from the destabilizing $\sinh$ functional (supported purely on odd tests).
   - *Codimension-one pole nullspace:* When boundary-corrected sources $H_n$ have rank-one zero readout $c_n/\rho$, restricting coefficients to the hyperplane $\Lambda_{\text{pole}}(a) = \sum a_n c_n = 0$ annihilates the corrected readout identically and identifies the compact-ramp combination with the negated tail combination on the zero divisor.

4. **Relative Stability and Nonstationary Mellin Exclusion:**
   - *Relative Krein perturbation:* A relative margin $\operatorname{Re}\mathcal{W}(u, u) \ge \delta\mathcal{Z}(u)$ survives any perturbation $u - h$ with $\mathcal{Z}(h) \le \varepsilon\mathcal{Z}(u)$ below the sharp threshold $\varepsilon < (\sqrt{1+\delta} - 1)^2$.
   - *Low-frequency exclusion vs. dilation envelopes:* On multi-scale spans $\sum_{N \ge M} b_N \Phi_N$, irrational collar shifts $\lambda_N = N(1+\varepsilon_N)$ provide uniform frequency separation (giving physical $L^2$ Riesz sequence bounds via Montgomery–Vaughan) and nonstationary Mellin phase derivatives on $|\xi| \le 1/2$ (forcing logarithmic archimedean Gamma growth $\gtrsim (\log M)\sum |b_N|^2$), while envelopes decaying faster than the critical exponent $\beta = 1/2$ keep the prime-shift and polar quadratic forms uniformly bounded on $\ell^2$.

---

## 4. Traps and Boundaries

| Trap / Invalid Shortcut | Why It Fails |
| :--- | :--- |
| **Applying Cauchy–Schwarz to $\mathcal{W}(f, g)$ directly** | $|\mathcal{W}(f, g)|^2 \le \mathcal{W}(f, f)\mathcal{W}(g, g)$ is valid **only** after $\mathcal{W}$ is known to be positive semidefinite on $\operatorname{span}(f, g)$. Use the unconditionally positive majorant $\mathcal{Z}(f)$ instead. |
| **Inferring positivity from self-adjointness or finite negative index** | A self-adjoint operator or Krein involution $J$ ($J^2 = I$) has eigenvalues $\pm 1$; neither self-adjointness nor a finite negative index excludes negative directions. |
| **Replacing a test $g$ by $|g|$ and keeping only the Markov improvement** | Normal contraction lowers the Markovian jump form ($\mathcal{M}_N(|g|) \le \mathcal{M}_N(g)$), but simultaneously alters the anti-Markovian hyperbolic pole term $\frac{1}{2}C(g)^2 - \frac{1}{2}S(g)^2$. |
| **Absorbing the factorial polar loss into the Gram coupling error** | Their asymptotic scales are incompatible: the polar loss has leading order $\log N / N$, whereas the ramp–tent Gram coupling correction $M_n^2/(4 D_n)$ is $O(\log^2 N / N^2)$. |
| **Inferring derivative/Sobolev bounds from smoothing-uniform value bounds** | Noncompact arithmetic tails have endpoint jumps at $x = 0$; an unqualified $H^1$ bound fails uniformly as smoothing is removed, whereas fractional/logarithmic translation integrals $\int_0^1 D(h)\,dh/h$ remain uniform. |
| **Using diagonal sampling bounds alone to control cross-scale Gram matrices** | After normalizing diagonals to unit order, Cauchy–Schwarz via $\sqrt{\mathcal{Z}(f_N)\mathcal{Z}(f_M)}$ leaves off-diagonal entries of order $1$; cross-scale control requires oscillation (Montgomery–Vaughan / nonstationary phase) or prime-dilation decay $\beta > 1/2$. |
| **Renaming an RH-equivalent cone, metric, or contraction as a hypothesis** | Assuming a global positive cone, $L^2$ contraction, or fixed-side $O((1+T)e^{T/2})$ integrated prime deficit merely restates RH; the arithmetic work consists in proving such a bound from literal source data. |
| **Replacing exact completion data by functional-equation symmetry alone** | Symmetry $\xi(s) = \xi(1-s)$ without Euler-product and Gamma-pole completion permits off-line zeros and negative Weil directions at large support aperture. |

---

## 5. Main Research Topics

**Current frontier (19 October 2026).** These topics include established tools
and open extensions. Subcritical tail-span coercivity is already available in
[`FactorialTailSpanWeilCoercivity.lean`](FactorialTailSpanWeilCoercivity.lean).
At the critical envelope, the whole-span affine comparison
[`FactorialCriticalAffineComparison.lean`](FactorialCriticalAffineComparison.lean)
is also proved; a generic Gram-matrix obstruction must not be used to erase that
source-specific result. The translated prime limit, harmonic diagonalization
and continuous kernel are established in
[`FactorialCriticalTranslatedPrimeHarmonicDiagonal.lean`](FactorialCriticalTranslatedPrimeHarmonicDiagonal.lean)
and [`FactorialCriticalPrimeContinuousKernel.lean`](FactorialCriticalPrimeContinuousKernel.lean).
The exact half-line kernel-weight mass for a finite pattern is now
$(\pi^2/12)\sum_j b_j^2$ in
[`FactorialCriticalPrimeKernelMass.lean`](FactorialCriticalPrimeKernelMass.lean).

What remains is a sign estimate for the relevant critical prime form, assembly
with the archimedean and polar terms of the **complete** Weil form, and a
finite-scale error bound strong enough for the intended growing patterns.
The negative $m=2$ harmonic and positive higher harmonics identify a concrete
comparison to investigate; they do not determine the sum's sign. A fixed-pattern
limit does not justify inserting a growing pattern. No new sign theorem is
claimed by these README corrections.

1. **Zero-Divisor Sampling vs. Signed Diagonal Growth (Local Source Calibration):**
   Establishing sharp two-sided logarithmic budgets $\mathcal{Z}(U_{n,k}) \asymp \frac{\log N}{N}$ and $\operatorname{Re}\mathcal{W}(U_{n,k}, U_{n,k}) \gtrsim \frac{\log N}{N}$ from literal phase Lipschitz regularity and endpoint jump control, proving that physical $L^2$ mass $O(1/N)$ underestimates zero-divisor sampling by an essential factor of $\log N$.

2. **Compact Source Transfer, Smoothing Continuity, and Finite-Block Schur Margins:**
   Transferring positive tail margins across $r_{n,k} = H_{n,k} - U_{n,k}$ using the smaller $O(1/N)$ zero-sampling budget of the rank-one pole-corrected source $H_{n,k}$, removing the mollifier $k \to \infty$ across the singular archimedean jump integral via translation-square contraction, and closing the two-dimensional ramp–tent Schur margin $Q_n(c, d) \ge \frac{\log N}{8192 N}c^2 + \frac{N}{2}d^2$.

3. **Divisor-Stencil Filters, Collar Irrationality, and Multi-Scale Riesz Coercivity:**
   Classifying finite divisor-dilation stencils that cancel polynomial collar drifts while preserving first-harmonic dominance, characterizing the cubic Diophantine resonances of the shifted frequencies $\lambda_N = N(1+\varepsilon_N)$, and proving uniform Bohr and finite-window physical $L^2(\mathbb{R})$ Riesz sequence bounds across arbitrary finite coefficient families.

4. **High-Scale Signed Span Coercivity and the Critical Envelope Boundary $\beta \downarrow 1/2$:**
   Use the established subcritical coercivity bound as a baseline. At $\beta=1/2$, estimate the complete signed form on a specified pole-free family, with the finite-scale error and all growing support parameters controlled. Absolute prime summation $\sum\Lambda(k)/k^{\beta+1/2}$ diverges at this boundary; the existing critical affine and prime-kernel formulas specify where cancellation must be retained.

5. **All-Aperture Extension, Pole-Free Nullspace Geometry, and Odd-Mode Sinh Capacity:**
   Extending positivity from restricted high-scale or single-scale families toward larger subspaces by exploiting the codimension-one pole-free nullspace $\Lambda_{\text{pole}}(S, a) = 0$ (where compact-ramp combinations and negated tail combinations share identical zero-side readouts) and controlling the odd-mode hyperbolic capacity ratio $\operatorname{sinhPairing}(g)^2 / (2\mathcal{M}_N(g))$ as the support aperture grows.
