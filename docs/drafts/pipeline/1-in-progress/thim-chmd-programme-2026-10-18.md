# Trans-Horizon Incidence Mechanics: CHMD Closure Programme

- **ID:** thim-chmd-programme-2026-10-18
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/TransHorizonIncidenceMechanics/CHMD-programme.md
- **Statement:** Execute the 5-step CHMD programme in `TransHorizonIncidenceMechanics`: (1) multi-shell prime-power valuation sums, arbitrary-cut $p$-rough chain base coercivity, and quadratic $\beta^2$ convexity floor; (2) continuous shift pullback from discrete `chainVariance` to `chainIntegral` and `chainDensity` with origin-crossing collar duality; (3) nodal-lobe / prime-clock / multi-band $L^2$ sieve conservation laws; (4) scale-uniform cofinal estimates; (5) spine receiver integration.

## Goal
Systematic unconditional Lean 4 formalization of the mathematical steps in `docs/reports/TransHorizonIncidenceMechanics/CHMD-programme.md` connecting `TransHorizonIncidenceMechanics` to the CHMD spine (`CHMDPrimeChain`, `CHMDPrimeChainSource`, `CHMDPolar`, `CHMDChebyshevTransport`).

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean modules in `formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/`, `lake --old env lean` green, axiom-clean
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach
1. **Step 1 (All-Cut & Multi-Shell Discrete `chainVariance` Coercivity + Quadratic $\beta^2$ Floor):**
   - Prove the universal hyperbolic convexity floor $(e^x - 1)^2 + (e^{-x} - 1)^2 = 2(\cosh x - 1)^2 + 2\sinh^2 x \ge 2 x^2$ (and single-branch symmetrized floor $(e^x - 1)^2 + (e^{-x} - 1)^2 \ge 2 x^2$), yielding an explicit quadratic $\beta^2 (\log p)^3$ lower bound on the symmetrized off-line `chainVariance` excess.
   - Extend the ground-cut ($b = 1$) prime-factor sum to arbitrary cuts $u > 0$ by summing over all $p$-rough chain bases $b \in N.\text{divisors}$ with $\text{ordCompl}[p]\,b = b$ and $\log b \le u < \log(p^r b)$, and summing over all active valuation shells $r \in [1, v_p(N)]$ along a single chain.
2. **Step 2 (Continuous Logarithmic Pullback to `chainDensity` & `chainIntegral`):**
   - Connect `CHMDPrimeChainSource.chainDensity N p b v u` and `chainIntegral v q` directly to our discrete `varianceEnergy` and `chainVariance` lower bounds via the evaluation map $m \mapsto v(u - \log m)$.
   - Prove the continuous off-line hyperbolic excess for shifted logarithmic profiles $v_{\pm\beta,\gamma}(x) = e^{\pm\beta x}\cos(\gamma x)$ inside `chainDensity N p b v u` at every cut $u$, showing that the $u$-dependence factors as $e^{\pm 2\beta u}$ times the exact discrete `chainVariance` at shift phase $\gamma u$.
3. **Step 3 (Nodal-Lobe, Prime-Clock, and Multi-Band Sieve Conservation):**
   - Formalize the odd-eigenvector nodal-lobe prime-shift vs. `oneL`-defect balance and the fourth/fifth-band composite Buchstab $L^2$ step bounds using the sharp $5N$ unit envelope (`abs_sieveSeq_moebiusReal_le_one_of_le_five_mul`).

## Log
- 2026-10-18 — created in 1-in-progress
