# L7 Critical Audit of the RH Research Program (`argon`)

**Date:** 2026-10-19 (Revised after documentation & Lean ground-truth verification)  
**Scope:**
- Route ledger: [`docs/reports/rh-current-frontier-map.md`](file:///Users/michael/Documents/code/hgt/docs/reports/rh-current-frontier-map.md)
- Corrected obstacle summary: [`docs/reports/hard-obstacles-summary-1810.md`](file:///Users/michael/Documents/code/hgt/docs/reports/hard-obstacles-summary-1810.md)
- Four research programs:
  1. [`formal/GaloisForLFunctions/arithmetic-positivity-theory/README.md`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/arithmetic-positivity-theory/README.md) ([`ArithmeticPositivityTheory.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticPositivityTheory.lean), 50 modules)
  2. [`formal/GaloisForLFunctions/BiScaleUncertainty/README.md`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BiScaleUncertainty/README.md) ([`BiScaleUncertainty.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BiScaleUncertainty.lean), 536 modules)
  3. [`formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/README.md`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/README.md) ([`TransHorizonIncidenceMechanics.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/TransHorizonIncidenceMechanics.lean), 90 modules)
  4. [`formal/GaloisForLFunctions/BezoutValuationIncidence/README.md`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/README.md) ([`BezoutValuationIncidence.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence.lean), 128 modules)

---

## Initial Analysis

### 1. Ground-Truth Audit: Documentation Errors, Vacuous Hypotheses, and Overclaims

Before diagnosing why no route has closed, we must separate what is **actually proved in the Lean 4 source files** from what is claimed in the program `README.md` files and route ledger. Alongside the seven corrections recorded in [`docs/reports/hard-obstacles-summary-1810.md` §1](file:///Users/michael/Documents/code/hgt/docs/reports/hard-obstacles-summary-1810.md#L9-L82), direct comparison against the `.lean` modules exposes five concrete discrepancies across the four program READMEs and frontier modules:

#### 1.1 Unfixed Mathematical Errors Still Present in `TransHorizonIncidenceMechanics/README.md`
1. **Invalid Nyman–Beurling Tail Measure ([`THIM/README.md:28, 50, 111, 130, 170`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/README.md#L28)):**
   `THIM/README.md` repeatedly states the target for `CTF`, `BVI`, and `PM` as bounding the Báez–Duarte tail in "$L^2((0, 1/N), dx/x^2)$". As documented in [`hard-obstacles-summary-1810.md` §1.1](file:///Users/michael/Documents/code/hgt/docs/reports/hard-obstacles-summary-1810.md#L11-L28), for the fractional-part functions $\rho_k(x) = \{1/(kx)\}$, the Nyman–Beurling Hilbert space is $L^2((0, \infty), dx)$; the change of variables $u = 1/x$ turns $\int_0^{1/N} |\sum_{k \le N} a_{N,k}\{1/(kx)\}|^2\,dx$ into $\int_N^\infty |\sum_{k \le N} a_{N,k}\{u/k\}|^2\,\frac{du}{u^2}$. Writing $dx/x^2$ on $(0, 1/N)$ applies the Jacobian twice and produces $\int_N^\infty |\sum a_{N,k}\{u/k\}|^2\,du$, which is the integral of a periodic function on $[N, \infty)$ and diverges unless the function is zero a.e. Furthermore, a tail bound alone does not yield weak convergence $q_N \rightharpoonup \chi$: weak closure requires $\sup_N \|q_N\|_{L^2((0,\infty), dx)} < \infty$ together with local $L^2([a,b])$ convergence on all compact intervals $0 < a < b < \infty$.
2. **False Unguarded Von Mangoldt Clock Identity ([`THIM/README.md:46, 87`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/README.md#L46)):**
   `THIM/README.md` asserts that $\tau_{\mathrm{vis}}(q) = q/\operatorname{rad}(q)$ satisfies "$\Lambda(d) = \log(d/\tau_{\mathrm{vis}}(d))$". Since $d/\tau_{\mathrm{vis}}(d) = \operatorname{rad}(d)$, this states $\Lambda(d) = \log(\operatorname{rad}(d))$, which is false for every composite $d$ with at least two distinct prime factors (e.g., $d = 6 \implies \log(\operatorname{rad}(6)) = \log 6 \ne 0 = \Lambda(6)$). In the actual Lean file [`ValuationClockChainBridge.lean:144-162`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/ValuationClockChainBridge.lean#L144-L162), [`vonMangoldt_eq_log_div_lagVisibilityClock`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/ValuationClockChainBridge.lean#L144-L148) has an explicit primality guard:
   ```lean
   ArithmeticFunction.vonMangoldt d =
     if Nat.Prime (d / lagVisibilityClock d) then Real.log ((d / lagVisibilityClock d : ℕ) : ℝ) else 0
   ```
   Dropping the `if Nat.Prime` guard in the documentation creates the false impression that additive visibility clocks algebraically detect prime powers without primality testing of the radical.
3. **Outdated Characterization of `BezoutValuationIncidence` ([`THIM/README.md:21`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/README.md#L21)):**
   `THIM/README.md` claims BVI only proved non-positivity sub-horizon ($M + 1 \le N$). In fact, [`QuotientDualOctaveReciprocityAndValuationSwitching.lean:125-249`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/QuotientDualOctaveReciprocityAndValuationSwitching.lean#L125-L249) already proves exact first-octave ($s_{N,\mu}(k) = -\mu(k)$ on $N < k \le 2N$) and second-octave ($2N < k \le 3N$) reciprocity inside BVI.

#### 1.2 Vacuous Anchor Hypothesis in `BiScaleUncertainty`'s Flagship Visibility Classification
- In [`SieveLocalVisibilityClassification.lean:150-168`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BiScaleUncertainty/SieveLocalVisibilityClassification.lean#L150-L168), [`highest_stratum_sharp_exponent`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BiScaleUncertainty/SieveLocalVisibilityClassification.lean#L150-L155) classifies local Hölder recovery exponents ($\alpha = 1$ vs. $\alpha = 1/3$) under the hypothesis:
  ```lean
  hb : selbergMultiplesCoord N b (TopAnchor.topOrder N) ≠ 0
  ```
- In [`SieveHighestDyadicCoordinate.lean:15`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BiScaleUncertainty/SieveHighestDyadicCoordinate.lean#L15), `TopAnchor.topOrder N` is defined as `2 ^ Nat.log 2 N`.
- For every $N \ge 4$, $2^{\lfloor\log_2 N\rfloor}$ is a multiple of $4$, and its only multiple in $[1, N]$ is itself. Consequently, for **every** sieve weight $b$ supported on squarefree integers—including literal Möbius $\mu(d)$, Selberg tapers, and Barban–Vehov weights—`selbergMultiplesCoord N b (TopAnchor.topOrder N) = 0` identically for all $N \ge 4$ ([`hard-obstacles-summary-1810.md` §1.7](file:///Users/michael/Documents/code/hgt/docs/reports/hard-obstacles-summary-1810.md#L75-L82)). Moreover, the stability constants in [`SieveLocalVisibilityClassification.lean:66, 107`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BiScaleUncertainty/SieveLocalVisibilityClassification.lean#L66) scale as $(N!)^6$.

#### 1.3 Misidentified Quantifier in `BezoutValuationIncidence` (`ε` Fixed vs. `ε ↓ 0`) and Self-Cancelling Integration by Parts
- [`BezoutValuationIncidence/README.md` Trap 6 (line 115)](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/README.md#L115) frames Wall 1 as obtaining a "uniform-in-$\varepsilon$ tail bound" as $\varepsilon \to 0^+$.
- However, inspecting the actual Lean receiver [`riemannHypothesis_of_pmBezoutInteriorPronicEnergy_bounded`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/PronicPotentialSelfCancellationAndInteriorGradientConservation.lean#L394-L397) and the spectral bridge [`pmPowerDampedFermiSource_memLp_and_analytic_of_sieveEnergyCenteredPronicGramForm_budget`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/RoutePMCofactorSieveBridgeAndUnifiedEnergyEquivalence.lean#L283-L288) reveals the exact quantifier:
  $$\forall \delta > 0,\; \exists \varepsilon \in (0, \delta),\; \exists B_\varepsilon \in \mathbb{R},\; \forall T \ge 1,\quad \mathrm{pmBezoutInteriorPronicEnergy}(\varepsilon, T) \le B_\varepsilon$$
  (or $\forall Q \in \mathbb{N},\; \mathrm{pmPowerDampedRamanujanEnergyVariance}(\varepsilon, Q) \le B_\varepsilon$).
- **The constant $B_\varepsilon$ is allowed to depend on $\varepsilon$ and may diverge as $\varepsilon \downarrow 0$!**
- Why, then, is this still open even at a **fixed** $\varepsilon \in (0, 1/2]$ (e.g., $\varepsilon = 1/4$, which corresponds to analyticity on $\operatorname{Re}(s) > 3/4$)?
  1. In [`PMPowerDampedMobiusRamanujanAbsolute.lean:90-109`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/PMPowerDampedMobiusRamanujanAbsolute.lean#L90-L109), [`exists_pmPowerDampedRamanujan_variance_budget_of_half_lt`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/PMPowerDampedMobiusRamanujanAbsolute.lean#L106-L109) proves $\sup_Q \mathrm{pmPowerDampedRamanujanEnergyVariance}(\varepsilon, Q) \le B_\varepsilon$ **only for $\varepsilon > 1/2$** (the trivial half-plane $\operatorname{Re}(s) > 1$), by bounding $\{N/d\} \le (N/d)^a$ with $1 - \varepsilon < a < 1/2$ ([`pmPowerDampedRamanujanPrefixEnergy_le_rpow_budget`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/PMPowerDampedMobiusRamanujanAbsolute.lean#L56-L60)). For $\varepsilon \le 1/2$, no such exponent $a$ exists because $a < 1/2$ and $\varepsilon + a > 1$ are incompatible.
  2. In [`UniformRenormalizedInteriorEnergyRemainder.lean:129-135`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/UniformRenormalizedInteriorEnergyRemainder.lean#L129-L135), [`exists_pmBezoutInterior_compensated_energy_bound`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/UniformRenormalizedInteriorEnergyRemainder.lean#L129-L135) proves that for any fixed $\varepsilon > 0$,
     $$\bigl|2\,\mathrm{pmBezoutInteriorMartingaleSum}(\varepsilon, T) + 2\,\mathrm{pmInteriorLogCounterterm}(\varepsilon)\,H_T^{\mathrm{comp}} - E_\varepsilon(T)\bigr| \le C_\varepsilon.$$
     This bounds the **difference** between two quantities, neither of which is known to be bounded as $T \to \infty$.
  3. When [`PronicPotentialSelfCancellationAndInteriorGradientConservation.lean:191-219`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/PronicPotentialSelfCancellationAndInteriorGradientConservation.lean#L191-L219) applies summation by parts to `2 * pmBezoutInteriorMartingaleSum ε T` ([`two_mul_pmBezoutInteriorMartingaleSum_eq_discreteEnergy_sub`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/PronicPotentialSelfCancellationAndInteriorGradientConservation.lean#L191-L201)), it produces $+E_\varepsilon(T)$ on the right-hand side, which **cancels $-E_\varepsilon(T)$ identically** ([`pmBezoutInteriorGradient_add_two_mul_localImpulse_eq_activeDeleted_add_predecessorPeak`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/PronicPotentialSelfCancellationAndInteriorGradientConservation.lean#L209-L218))! Thus, summation by parts yields a conservation law for the interior gradient plus local impulse, leaving $E_\varepsilon(T)$ completely unestimated for every $\varepsilon \in (0, 1/2]$.

#### 1.4 Tautological Linear Rearrangements Packaged as "Criteria for RH" in `TransHorizonIncidenceMechanics`
- In [`CoshCollarNodalDefectBezoutShellAndMobiusWaveBridge.lean:502-588`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/CoshCollarNodalDefectBezoutShellAndMobiusWaveBridge.lean#L502-L588), [`riemannHypothesis_of_odd_eigenvector_four_term_posGraph_ge_groundPotential`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/CoshCollarNodalDefectBezoutShellAndMobiusWaveBridge.lean#L535-L546) states that if the 4-term positive-lobe jump sum is at least $\|q^+_1\|^2 - \langle V_{\mathrm{ground}} q^+_1, q^+_1\rangle$ for every odd eigenvector with $\mu \in (1/2, 1)$, then RH holds.
- Look at the proof of [`eigenvalue_le_one_half_of_four_term_posGraph_ge_groundPotential`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/CoshCollarNodalDefectBezoutShellAndMobiusWaveBridge.lean#L502-L527) (lines 514–520):
  - `hbal1` (`posGraph_five_term_jump_eq_diagonals_of_eigenvector`) is the exact identity:
    $$\text{(4-term jump sum)} + \frac{2\mu - 1}{\mu}\|q^+_1\|^2 = \langle D_{\mathrm{arch}} q^+_1, q^+_1\rangle + \langle D_{\mathrm{prime}} q^+_1, q^+_1\rangle.$$
  - `hbal2` (`arch_add_primeDiagonal_eq_norm_sq_sub_groundPotential`) is the exact identity:
    $$\langle D_{\mathrm{arch}} q^+_1, q^+_1\rangle + \langle D_{\mathrm{prime}} q^+_1, q^+_1\rangle = \|q^+_1\|^2 - \langle V_{\mathrm{ground}} q^+_1, q^+_1\rangle.$$
  - Subtracting the hypothesis `‖q⁺₁‖² - ⟪V_ground q⁺₁, q⁺₁⟫ ≤ (4-term jump sum)` from `hbal1 + hbal2` gives $\frac{2\mu-1}{\mu}\|q^+_1\|^2 \le 0$ in a single `linarith` call (line 519)!
- In other words, the hypothesis of `riemannHypothesis_of_odd_eigenvector_four_term_posGraph_ge_groundPotential` is an **algebraic restatement** of $\frac{2\mu-1}{\mu}\|q^+_1\|^2 \le 0$ (i.e., $\mu \le 1/2$). Meanwhile, the unconditional inequality proved in the same file ([`odd_eigenvector_nodalDefectGraph_subinvariance_and_bilateral_cs`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/CoshCollarNodalDefectBezoutShellAndMobiusWaveBridge.lean#L431-L450) and [`eigenvector_nodalDefectGraph_ground_energy_ge_spectral_excess_sq`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/NodalDefectMarkovSubinvarianceAndCenteringPronicGramBridge.lean#L245-L253)) bounds `4 * sourcePair (posGraph q) (negGraph q) ^ 2` **from above** by Cauchy–Schwarz, which goes in the opposite direction to the lower bound needed by the criterion.

#### 1.5 Unresolved Sign of the Critical Prime Kernel in `arithmetic-positivity-theory`
- While [`FactorialTailSpanWeilCoercivity.lean:221-284`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialTailSpanWeilCoercivity.lean#L221-L284) proves unconditional Weil positivity on high-scale ($M \ge M_0$) subcritical ($\beta = 3/2 > 1/2$) factorial tails—where archimedean $\log|r|$ growth dominates by triangle inequality regardless of whether RH holds—APT also contains a 13-module sequence (`FactorialCriticalPrimeAdmission.lean` through `FactorialCriticalPrimeKernelMass.lean`) analyzing the critical envelope $\beta = 1/2$.
- In [`FactorialCriticalTranslatedPrimeHarmonicDiagonal.lean:139-200`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialCriticalTranslatedPrimeHarmonicDiagonal.lean#L139-L200), [`factorialCriticalTranslatedPrimeLimit_eq_harmonic_diagonal`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialCriticalTranslatedPrimeHarmonicDiagonal.lean#L139-L142) proves that the limiting prime form of a translated finite factorial pattern equals:
  $$\frac{4}{\pi^4}\sum_{m=1}^\infty \frac{\mathrm{factorialCriticalPrimeHarmonicCharge}(m)\,\mathrm{factorialCriticalPatternHarmonicMass}(S, b, m)}{m^4},$$
  and [`factorialCriticalTranslatedPrimeHarmonic_sign`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialCriticalTranslatedPrimeHarmonicDiagonal.lean#L192-L200) proves that the $m = 2$ term is **strictly negative** for every nonzero pattern, $m = 1$ and $4 \mid m$ vanish, and $m > 2$ with $4 \nmid m$ are strictly positive.
- As the module docstring at [`FactorialCriticalTranslatedPrimeHarmonicDiagonal.lean:6-7`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialCriticalTranslatedPrimeHarmonicDiagonal.lean#L6-L7) explicitly admits: *"its individual harmonic signs are rigid, while the sign of their total sum is left open."* Furthermore, this is only the prime channel of a specific limiting pattern, not the complete Weil form.

---

## Adversarial Critique

Let us subject our diagnosis and potential research proposals to strict adversarial scrutiny:

### Critique 1: Stop Confusing "Missing Estimates in Our Formulation" with "Mathematics as a Whole Missing a Grand Theory"
- **What is wrong with grandiose claims about "global mathematics":**
  In our first pass, we claimed that "mathematics as a whole" is missing grand new fields like a "Mirror-Lobe Harnack–Poincaré Calculus" or a "Scale-Recursive Cofactor Volterra Contraction Theory." Both of those claims collapse under direct inspection of the Lean files:
  1. **Why the "Cofactor Volterra Contraction" claim was wrong:** In [`NaturalCutoffMultiDepthCofactorAndConditionalTailBridge.lean:217-231`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/NaturalCutoffMultiDepthCofactorAndConditionalTailBridge.lean#L217-L231), [`pmRamanujanEnergyCenteredPrimeCofactorPacket_head`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/NaturalCutoffMultiDepthCofactorAndConditionalTailBridge.lean#L217-L231) holds **only under the hypothesis `hNp : N < p`** (before the first prime multiple of $p$, where $\lfloor N/p\rfloor = 0$). However, `pmPowerDampedRamanujanEnergyVariance ε Q` ([lines 273–276, 386–390](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/NaturalCutoffMultiDepthCofactorAndConditionalTailBridge.lean#L273-L276)) is an infinite series over **all $N \in \mathbb{N}$**, and its difficulty lies in the tail $N \ge p$ (and $N > Q$), where $\lfloor N/(pr)\rfloor$ jumps non-trivially and `pmRamanujanEnergyCenteredPrimeCofactorPacket_head` **does not apply**! Treating a pre-first-multiple identity ($N < p$) as a global recursion for the infinite-horizon pronic variance was mathematical slop.
  2. **Why the "Mirror-Lobe Harnack Lower Bound" claim was unverified:** In [`CoshCollarNodalDefectBezoutShellAndMobiusWaveBridge.lean:438-441`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/CoshCollarNodalDefectBezoutShellAndMobiusWaveBridge.lean#L438-L441), the pointwise sub-invariance is
     $$q^+_1 \le_{\text{a.e.}} R_{\mathrm{stat}}\bigl(V_{\mathrm{collar},\mu}(q^+_1)\bigr).$$
     This is an *upper* bound on $q^+_1$ by the stationary resolvent applied to $q^+_1$ itself. While it implies $\operatorname{nodalDefectGraph} \mu q \ge 0$ a.e., it does **not** automatically prevent $q^+_1$ from concentrating far from the origin or oscillating across prime-shift shells; asserting that it implies a quantitative lower bound on $-\operatorname{sourcePair}(q^+, q^-)$ without a proof mechanism is wishful thinking.

### Critique 2: Why Proposing a 5th Research Program Is Counterproductive Organizational Bloat
- **Evidence from the repository:**
  Look at what happened when [`TransHorizonIncidenceMechanics`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/TransHorizonIncidenceMechanics.lean) was created as the 4th program to "unify" `BiScaleUncertainty`, `BezoutValuationIncidence`, and `RHTower`:
  - Out of 90 modules in `THIM`, dozens are bridge modules (`...Bridge.lean`) that import theorems from two or three libraries and join them with `∧` (e.g., [`pmSecondLayer_and_returnWindow_two_moment_bridge`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/CoshCollarNodalDefectBezoutShellAndMobiusWaveBridge.lean#L682-L704) and [`kleinGordon_chebyshev_transport_mobius_three_piece_and_lightCone_bridge`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/CoshCollarNodalDefectBezoutShellAndMobiusWaveBridge.lean#L722-L753)).
  - Joining four already-proved theorems from different namespaces with `∧` in a 750-line file adds **zero mathematical power** while increasing build times, context-window overhead, and documentation drift.
- **Conclusion:** Creating a 5th research program before any of the existing 4 programs has proved a single strip-entering analytic estimate (such as bounding `pmPowerDampedRamanujanEnergyVariance ε Q` for *any* $\varepsilon < 1/2$) would merely create a 5th directory of bridge theorems and reformulations.

### Critique 3: Are the Four Existing Programs Even Targeting the Right Inequalities?
- Let us check each program's current trajectory against its actual receivers:
  1. **`BezoutValuationIncidence`:** Has spent 128 modules on exact identities over $N!$, finite Selberg polytopes, fixed-$\varepsilon$ $O_\varepsilon(1)$ differences of diverging quantities (`UniformRenormalizedInteriorEnergyRemainder.lean`), and existential prime-pair statements (`DilationClockComplementPrimeSurvival.lean`), while its actual receiver `pmPowerDampedRamanujanEnergyVariance ε Q ≤ B_ε` remains stuck at the trivial absolute-convergence threshold $\varepsilon > 1/2$ (`PMPowerDampedMobiusRamanujanAbsolute.lean:106`).
  2. **`TransHorizonIncidenceMechanics`:** Has spent 90 modules building Fermi trace inequalities with $(\log_2 N)^2$ losses (`FermiCompleteTraceValuationStability.lean:79-83`), finite $p \le 13$ collar evaluations (`CollectiveLowPrimeChebyshevTransportAndSinhAbsorption.lean`), and tautological `linarith` wrappers (`CoshCollarNodalDefectBezoutShellAndMobiusWaveBridge.lean:535-588`).
  3. **`arithmetic-positivity-theory`:** Has spent 37 of its 50 modules on high-scale ($M \ge M_0$) subcritical ($\beta = 3/2$) tail coercivity that holds regardless of RH, and in the 13 modules that do reach the critical envelope $\beta = 1/2$, stopped short of bounding the negative $m=2$ harmonic against the $m \ge 3$ positive harmonics or including the archimedean/polar terms.
  4. **`BiScaleUncertainty`:** Has spent 536 modules on general autocorrelation/Hilbert-space identities and finite-horizon moment recovery whose top-anchor hypothesis (`TopAnchor.topOrder N`) is identically zero on all squarefree sieve weights for $N \ge 4$.

---

## Final Answer

In Phase 3, we accept all three adversarial critiques and discard every unverified buzzword from our initial draft. Here are the direct, honest answers to your three questions.

---

### Question 1: What Mathematical Tools Are We—or Mathematics as a Whole—Missing?

#### A. What Our Research Program Is Missing (Self-Inflicted Gaps vs. Real Obstacles)
Across all 804 modules in the four programs, **we have been substituting exact algebraic identities, finite-period classifications, and conditional reformulations for quantitative signed estimates.** Specifically:
1. **We have not crossed the trivial $\operatorname{Re}(s) > 1$ ($\varepsilon > 1/2$) barrier in the discrete pronic/cofactor energy:**
   In [`PMPowerDampedMobiusRamanujanAbsolute.lean:101-109`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/PMPowerDampedMobiusRamanujanAbsolute.lean#L101-L109), `pmPowerDampedRamanujanEnergyVariance ε Q` is bounded uniformly in $Q$ **only for $\varepsilon > 1/2$** via the unsigned triangle inequality $\{N/d\} \le (N/d)^a$. For $0 < \varepsilon \le 1/2$ (which corresponds to $1/2 < \operatorname{Re}(s) \le 1$), BVI has not proved uniform boundedness in $Q$ (or $T$) for **any** $\varepsilon \le 1/2$—not even $\varepsilon = 1/2 - 10^{-6}$. Instead, [`UniformRenormalizedInteriorEnergyRemainder.lean:129-135`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/UniformRenormalizedInteriorEnergyRemainder.lean#L129-L135) bounded the difference between two potentially diverging quantities, and [`PronicPotentialSelfCancellationAndInteriorGradientConservation.lean:209-219`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/PronicPotentialSelfCancellationAndInteriorGradientConservation.lean#L209-L219) applied summation by parts in a way that cancelled $E_\varepsilon(T)$ from both sides.
2. **We have confused upper bounds with lower bounds on odd-sector nodal jump terms:**
   In [`NodalDefectMarkovSubinvarianceAndCenteringPronicGramBridge.lean:154-181, 245-253`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/NodalDefectMarkovSubinvarianceAndCenteringPronicGramBridge.lean#L154-L181), the 5-term `absGraph` identity and `nodalDefectGraph` Cauchy–Schwarz inequality give **upper bounds** on the cross-lobe interaction $\operatorname{sourcePair}(q^+, q^-)^2$. To exclude odd eigenvectors with $\mu \in (1/2, 1)$ ([`CoshCollarNodalDefectBezoutShellAndMobiusWaveBridge.lean:535-546`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/CoshCollarNodalDefectBezoutShellAndMobiusWaveBridge.lean#L535-L546)), one needs a **lower bound** on the 4-term positive-lobe jump energy, which we do not have.
3. **We have proved positivity only on RH-nonselective subcritical families ($\beta > 1/2$, $M \ge M_0$):**
   In [`FactorialTailSpanWeilCoercivity.lean:221-284`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialTailSpanWeilCoercivity.lean#L221-L284), positivity is achieved by pushing frequencies to $|r| > \eta M \to \infty$ where the archimedean Gamma factor dominates the prime and polar terms by absolute values ($\beta = 3/2 > 1/2$). This holds whether RH is true or false. At the critical envelope $\beta = 1/2$ ([`FactorialCriticalTranslatedPrimeHarmonicDiagonal.lean:192-200`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialCriticalTranslatedPrimeHarmonicDiagonal.lean#L192-L200)), the $m = 2$ harmonic is negative and even the sign of the prime channel alone is unproved.

#### B. What Mathematics as a Whole Is Missing
As corrected in [`docs/reports/hard-obstacles-summary-1810.md` §3–§4](file:///Users/michael/Documents/code/hgt/docs/reports/hard-obstacles-summary-1810.md#L105-L199), the six obstacle families are not six separate "missing disciplines"—their shared mathematical deficit is **a quantitative, source-specific signed cancellation estimate that survives the limit into the critical strip**. In standard mathematical terms, mathematics currently lacks:
1. **Quantitative Bilinear Fractional-Part / Kloosterman Cancellation for Multiplicative Sieve Weights Below the Absolute-Convergence Exponent ($\varepsilon \le 1/2$):**
   In [`PMPowerDampedMobiusRamanujanAbsolute.lean:35-60`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/PMPowerDampedMobiusRamanujanAbsolute.lean#L35-L60), bounding $\sum_{N=1}^T \frac{1}{N(N+1)}\bigl|\sum_{d \le Q} c_{\varepsilon, Q}(d)\{N/d\}\bigr|^2$ uniformly in $Q, T$ for $\varepsilon \le 1/2$ requires nontrivial cancellation in the off-diagonal pronic Gram sum $\sum_{e_1, e_2 \le Q} Y_\varepsilon(e_1)Y_\varepsilon(e_2) \mathcal{G}^{\mathrm{ec}}(e_1, e_2)$ driven by the alternating signs of $\mu(e)$ (or equivalent bilinear sawtooth cancellation). Classical analytic number theory (Vaughan's identity, Fouvry–Iwaniec, Deshouillers–Iwaniec) proves such bilinear cancellation down to $\sigma > 1/2 + \theta$ (e.g., $\theta = 1/6$ or $7/64$ in zero-density estimates, or in the boundary value of the Báez–Duarte / Bettin–Conrey– Farmer cotangent sums) only with $T^\varepsilon$ losses or over smooth averages, not as a uniform $O_\varepsilon(1)$ pronic norm bound for all $\varepsilon > 0$.
2. **Sign-Preserving Spectral Lower Bounds for Non-Local Operators on Odd / Nodal Sectors:**
   For self-adjoint operators whose ground state $\mathbf{1}$ lies in the even sector, standard Markov/Dirichlet spectral gap methods (Beurling–Deny contraction $v \mapsto |v|$, Perron–Frobenius, Harnack inequalities) map odd test functions into the even cone, losing the spectral separation between the even ground state ($\mu = 1$) and the odd threshold ($\mu = 1/2$). Existing spectral theory has no general lower-bound tool for the odd-sector Dirichlet form [`riemannHypothesis_iff_forall_odd_phiDoob_dirichlet_poincare`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilPhiDoobArchimedeanJumpAndHalfLineFolding.lean#L40) when the potential has exponential polar growth ($\sinh(x/2)$ / `phiDoobCoshMass`) as support radius $R \to \infty$.
3. **Quantitative Growing-Cutoff / Moving-Scale Correlation Bounds for Multiplicative Functions:**
   While recent analytic number theory (including the September 2026 preprint on qualitative ordinary two-point correlations of multiplicative functions noted in [`hard-obstacles-summary-1810.md` §3.1](file:///Users/michael/Documents/code/hgt/docs/reports/hard-obstacles-summary-1810.md#L127)) addresses fixed-shift qualitative asymptotics, receivers such as [`MobiusAdditiveStrictOffDiagonalLinearPolylogUpperBound`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/MobiusAdditiveTriangleChowlaFrontier.lean#L162-L165) or trans-horizon sieve energy require **quantitative** cancellation rates (or uniform control as the sieve cutoff $N$ and window $M$ grow together).

---

### Question 2: What to Research Next in Each of the Four Research Programs

Each program must immediately stop producing bridge conjunctions (`A ∧ B ∧ C`), tautological `riemannHypothesis_of_...` wrappers, and vacuous finite-period theorems, and execute the following concrete tasks:

#### 1. `BezoutValuationIncidence` ([`formal/GaloisForLFunctions/BezoutValuationIncidence`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/README.md))
- **What to stop doing:**
  - Stop manipulating the summation-by-parts identity on `pmBezoutInteriorMartingaleSum` ([`PronicPotentialSelfCancellationAndInteriorGradientConservation.lean:209-219`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/PronicPotentialSelfCancellationAndInteriorGradientConservation.lean#L209-L219)): $E_\varepsilon(T)$ cancels identically from both sides of that equation, so it can never bound $E_\varepsilon(T)$.
  - Stop proving fixed-ratio $M = (B+1)N$ moment formulas or existential two-prime statements like [`exists_prime_clock_complement_near_diagonal`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/DilationClockComplementPrimeSurvival.lean#L116-L123).
- **What to research next:**
  1. **Break the $\varepsilon = 1/2$ barrier in [`PMPowerDampedMobiusRamanujanAbsolute.lean:90-109`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/PMPowerDampedMobiusRamanujanAbsolute.lean#L90-L109) using bilinear / Gram cancellation:**
     In [`RoutePMCofactorSieveBridgeAndUnifiedEnergyEquivalence.lean:283-294`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/RoutePMCofactorSieveBridgeAndUnifiedEnergyEquivalence.lean#L283-L294), `pmPowerDampedRamanujanEnergyVariance ε Q` is identically the quadratic form `sieveEnergyCenteredPronicGramForm (Q + 1) (pmCofactorDivisorWeight ε Q)` with Selberg coordinates $Y_\varepsilon(e) = \mu(e)e^{-\varepsilon}$ ($2 \le e \le Q+1$). Instead of bounding $\{N/d\} \le (N/d)^a$ by absolute values (which stops at $\varepsilon > 1/2$), use the explicit off-diagonal decay of `pmRamanujanEnergyCenteredGram e₁ e₂` (and the signed clock-complement error bounds in [`DilationClockComplementPrimeSurvival.lean:26-35`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/DilationClockComplementPrimeSurvival.lean#L26-L35)) to prove $\sup_Q \mathrm{pmPowerDampedRamanujanEnergyVariance}(\varepsilon, Q) \le B_\varepsilon < \infty$ for a concrete range **below** $\varepsilon = 1/2$ (e.g., $\varepsilon \in (1/3, 1/2]$ as a first falsifiable milestone).
  2. **Sum the signed clock-complement error over dyadic prime packets:**
     Upgrade [`clock_successor_total_error_le_relative_gap`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/DilationClockComplementPrimeSurvival.lean#L26-L35) from a pointwise bound on a pair $(p, q)$ to a bilinear quadratic-form bound over all prime pairs $p, q \in (P, 2P]$ weighted by $Y_\varepsilon(pr)Y_\varepsilon(qr)$.

#### 2. `TransHorizonIncidenceMechanics` ([`formal/GaloisForLFunctions/TransHorizonIncidenceMechanics`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/README.md))
- **What to stop doing:**
  - Stop writing 700-line `*Bridge.lean` files that bundle unrelated theorems with `∧`.
  - Stop proving conditional theorems (`riemannHypothesis_of_...`) whose premise is a `linarith` rearrangement of the eigenvalue equation.
  - Stop proving lower bounds on `chainVariance` for the inserted test sequence $n^\beta + n^{-\beta}$ without an upper bound on the same quantity.
- **What to research next:**
  1. **Fix the mathematical errors in [`THIM/README.md`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/README.md):**
     Correct the invalid $L^2((0, 1/N), dx/x^2)$ tail measure (lines 28, 50, 111, 130, 170) to the true $L^2((0,\infty), dx)$ Báez–Duarte weak-closure criterion; restore the `if Nat.Prime (d / lagVisibilityClock d)` guard to the von Mangoldt formula (lines 46, 87); and remove the false claim that BVI only applies to $M + 1 \le N$ (line 21).
  2. **Quantify the all-scale low-prime diagonal collar integral in [`CollectiveLowPrimeChebyshevTransportAndSinhAbsorption.lean:124-196`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/CollectiveLowPrimeChebyshevTransportAndSinhAbsorption.lean#L124-L196):**
     In [`WeilPhiDoobArchimedeanJumpAndHalfLineFolding.lean:38-41`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilPhiDoobArchimedeanJumpAndHalfLineFolding.lean#L38-L41), the odd-sector Doob Poincaré inequality requires absorbing `phiDoobCoshMass (v^2)` for arbitrary support radius $R$. `THIM` already showed that high primes ($\log d \ge 2R$) are absorbed by half-line shift jumps (`SupportRadiusCollarCutoffAndAllScaleObstacleBBridge.lean:175`) and rewrote low primes ($\log d < 2R$) via `oddProfileCollarMixed` into `2 * ∫ collarMixedDiagKernel` plus a reflected square (`CollectiveLowPrimeChebyshevTransportAndSinhAbsorption.lean:84-139`). Instead of evaluating this only for $p \le 13$, prove a general bound for $\sum_{\log d < 2R} \mathrm{vonMangoldtAtom}(d) \int_0^{\log d} \mathrm{collarMixedDiagKernel}(a, \log d, x) w(x)^2\,dx$ via Stieltjes integration by parts against $\psi(e^t) - e^t$, retaining explicit dependence on both $R$ and $a$.
  3. **Eliminate or bypass the $(\log_2 N)^2$ loss in [`FermiCompleteTraceValuationStability.lean:79-83`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/FermiCompleteTraceValuationStability.lean#L79-L83):**
     Determine whether including the $2 \parallel n$ Fermi boundary cells removes the quadratic dyadic-depth factor $((L+4)(L+1))$ in `sieveTotalPronicEnergy_le_depth_selected`, and bound the resulting complete trace for concrete sieve weights $c$.

#### 3. `arithmetic-positivity-theory` ([`formal/GaloisForLFunctions/arithmetic-positivity-theory`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/arithmetic-positivity-theory/README.md))
- **What to stop doing:**
  - Stop proving more high-scale ($M \ge M_0$) subcritical ($\beta > 1/2$) tail coercivity variants where archimedean $\log|r|$ growth dominates by triangle inequality (`FactorialTailSpanWeilCoercivity.lean`).
- **What to research next:**
  1. **Resolve the sign of the critical prime kernel (`m = 2` vs. `m ≥ 3`) in [`FactorialCriticalTranslatedPrimeHarmonicDiagonal.lean:139-200`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialCriticalTranslatedPrimeHarmonicDiagonal.lean#L139-L200):**
     Compute explicit bounds on `factorialCriticalPrimeHarmonicCharge 2` (the sole negative harmonic) versus the positive harmonics $m \ge 3$ ($4 \nmid m$), or directly bound the continuous unit-cell kernel `factorialCriticalPrimeContinuousRealKernel t` on $[0, 1]$ ([`FactorialCriticalPrimeContinuousKernel.lean:148-187`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialCriticalPrimeContinuousKernel.lean#L148-L187)), to determine when `factorialCriticalTranslatedPrimeLimit S b` has a definite sign.
  2. **Assemble the complete Weil form at the critical envelope $\beta = 1/2$:**
     Combine `factorialCriticalTranslatedPrimeLimit S b` with the corresponding critical-envelope archimedean and polar terms on the pole-free subspace `ker factorialPoleFunctional` ([`RankOnePoleReadoutAndZeroNullspace.lean:252-284`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/arithmetic-positivity-theory/RankOnePoleReadoutAndZeroNullspace.lean#L252-L284)), and quantify the finite-scale approximation error before taking the $N \to \infty$ pattern limit.

#### 4. `BiScaleUncertainty` ([`formal/GaloisForLFunctions/BiScaleUncertainty`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BiScaleUncertainty/README.md))
- **What to stop doing:**
  - Freeze elementary $2\times 2$ Schur-complement, Bessel-sphere, and Hilbert-space polarization variations (which already account for >400 of its 536 modules).
  - Stop proving theorems anchored on `TopAnchor.topOrder N = 2 ^ Nat.log 2 N` without checking whether actual arithmetic sources have nonzero support there.
- **What to research next:**
  1. **Prove a squarefree-anchored local visibility classification to replace [`SieveLocalVisibilityClassification.lean:150-168`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BiScaleUncertainty/SieveLocalVisibilityClassification.lean#L150-L168):**
     Since `selbergMultiplesCoord N b (TopAnchor.topOrder N) = 0` for all $N \ge 4$ whenever $b$ is supported on squarefree integers, prove the local stability / visibility classification anchored at a prime mode $p \in (N/2, N]$ (where `selbergMultiplesCoord N b p = b(p)/p` is non-zero for Möbius and Barban–Vehov weights), and replace the $(N!)^6$ full-period moment constants with polynomial-horizon bounds.
  2. **Explicitly integrate the two-prime clock correlation kernel in [`PrimeGraphClockOffDiagonalSynthesisAndStationaryEnergyProducer.lean:595-616`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BiScaleUncertainty/PrimeGraphClockOffDiagonalSynthesisAndStationaryEnergyProducer.lean#L595-L616):**
     Compute the mass and momentum inner products of `canonicalPrimeGraphClockAtom k N p` and `canonicalPrimeGraphClockAtom k N p'` as explicit functions of the prime-ratio lag $\log(p'/p)$, rather than relying on abstract norm-density of their span (`lines 624–750`).

---

### Question 3: Do We Need Another Research Program to Develop New Mathematics That Nobody Has Developed Yet?

**No.**

1. **Why we do NOT need a 5th research program right now:**
   - `TransHorizonIncidenceMechanics` (`THIM`) was already created as a 4th program to unify the continuous/spectral side (`BiScaleUncertainty`, `RHTower`) and the discrete/incidence side (`BezoutValuationIncidence`).
   - Instead of producing the missing quantitative signed estimates, creating a new top-level program resulted in 90 modules dominated by cross-library bridge conjunctions and conditional reformulations.
   - As [`docs/reports/hard-obstacles-summary-1810.md` §4](file:///Users/michael/Documents/code/hgt/docs/reports/hard-obstacles-summary-1810.md#L186-L199) accurately concludes, the four existing programs already cover the exact division of mathematical labor needed:
     - **APT:** Complete explicit-formula / Weil form bounds on explicit growing test families;
     - **BiScale:** Norm-compatible approximation/observation losses and escaping-profile control;
     - **BVI:** Signed divisor/cofactor remainders across growing cutoffs $Q$ and horizons $T$ in the strip $0 < \varepsilon \le 1/2$;
     - **THIM:** Discrete-to-continuous transfer estimates with all cutoff, damping, and boundary costs paid.
2. **When—and only when—a 5th program would be justified:**
   A new research program should only be spun out **after** we prove a falsifiable, non-trivial strip estimate inside one of the existing four programs—for example, proving $\sup_Q \mathrm{pmPowerDampedRamanujanEnergyVariance}(\varepsilon, Q) < \infty$ for some $\varepsilon < 1/2$ (breaking the $\operatorname{Re}(s) = 1$ absolute-convergence barrier in [`PMPowerDampedMobiusRamanujanAbsolute.lean:106`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/PMPowerDampedMobiusRamanujanAbsolute.lean#L106)), or proving an all-$R$ low-prime Chebyshev collar bound in [`CollectiveLowPrimeChebyshevTransportAndSinhAbsorption.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/CollectiveLowPrimeChebyshevTransportAndSinhAbsorption.lean). Until such an estimate exists, adding a 5th program is organizational procrastination.


---

## 6. Exact Step-by-Step Execution Plan: Connecting the Four Programmes to Unconditional Signed Arithmetic Estimates (`RHTower/Sieve` & `RHTower`)

### Why the Four Programmes Are Currently Cut Off (Root-Cause Diagnosis)
As [`docs/reports/review-1910/opus.md`](file:///Users/michael/Documents/code/hgt/docs/reports/review-1910/opus.md) identified, out of 808 Lean files across the four programmes, only **1** file ([`BiScaleUncertainty/HighFrequencyLaplaceEnergyMeanValue.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BiScaleUncertainty/HighFrequencyLaplaceEnergyMeanValue.lean)) imports a classical analytic estimate from `RHTower/Sieve`. Inspecting the Lean source reveals **three concrete interface/definition disconnects** that prevented the four programmes from consuming `RHTower/Sieve`:

1. **The Truncated Divisor-Sum vs. `ArithmeticFunction` Disconnect (BVI & THIM vs. `RHTower/Sieve`):**
   - `BezoutValuationIncidence` and `TransHorizonIncidenceMechanics` define truncated Möbius divisor sums as `sieveSeq N moebiusReal k = ∑ d ∈ Finset.Icc 1 N, if d ∣ k then moebiusReal d else 0` (`Nat → ℝ`).
   - Meanwhile, [`RHTower/Sieve/VaughanTypeIIEstimate.lean:19-21`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/Sieve/VaughanTypeIIEstimate.lean#L19-L21) defines the Vaughan Type-II short factor as `typeIIShort (V : ℕ) : ArithmeticFunction ℝ := 1 - zeta * truncAF moebius V`.
   - For every $k \ge 1$, `((zeta : ArithmeticFunction ℝ) * truncAF (moebius : ArithmeticFunction ℝ) V) k = sieveSeq V moebiusReal k`, and for every $k \ge 2$, **`typeIIShort V k = - sieveSeq V moebiusReal k`**.
   - Because this 10-line bridge was never written:
     - BVI proved linear-band $L^2$ bounds on `sieveL2PrefixEnergy N M moebiusReal` only for $M \le (B+1)N$ with $B^3$ blowup ([`CofinalLinearWindowMobiusEnergyAndDefectBounds.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/CofinalLinearWindowMobiusEnergyAndDefectBounds.lean)), unaware that [`RHTower/Sieve/TypeIICoefficientEnergy.lean:53`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/Sieve/TypeIICoefficientEnergy.lean#L53) (`sum_typeIIShort_sq_le`) **already** bounds $\sum_{m=1}^L |\operatorname{typeIIShort} V m|^2 \le 2L + 2L(\operatorname{invSum} L)^3$ unconditionally for **all** $V, L \in \mathbb{N}$!
     - BVI proved only a qualitative $o(M)$ cofinal discrepancy bound in [`UniformCofinalMobiusPrefixDiscrepancy.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/UniformCofinalMobiusPrefixDiscrepancy.lean) via `PNTPlus.Consequences`, instead of importing [`RHTower/Sieve/VinogradovKorobovMoebius.lean:423`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/Sieve/VinogradovKorobovMoebius.lean#L423) (`exists_abs_sum_moebius_le_vk_rate`) and [`RHTower/Sieve/MoebiusMeanSquareUnconditional.lean:21`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/Sieve/MoebiusMeanSquareUnconditional.lean#L21) (`exists_sum_normSq_moebius_window_le`).

2. **The Critical-Band Frequency Cutoff in `BiScaleUncertainty`:**
   - [`HighFrequencyLaplaceEnergyMeanValue.lean:51`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BiScaleUncertainty/HighFrequencyLaplaceEnergyMeanValue.lean#L51) proves the bridge `atomicFourier_eq_dirPoly : atomicFourier N ξ = dirPoly (N + 2) (atomicCoefficient N) (-(2 * π * ξ))` and uses `dirichlet_meanValue_sharp` on the high-frequency tail $|\xi| \ge \sqrt{N+2}$, followed by [`BandLimitedLaplaceEnergy.lean:160`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BiScaleUncertainty/BandLimitedLaplaceEnergy.lean#L160) (`laplaceEnergy_le_band_add_linear`).
   - However, inside the critical band $|\xi| \le \sqrt{N+2}$, `BiScaleUncertainty` never connects `atomicFourier_eq_dirPoly` to the level-set and Halász $L^1$ bounds in [`RHTower/Sieve/DirichletMeasureLargeValues.lean:23,171`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/Sieve/DirichletMeasureLargeValues.lean#L23-L171) (`volume_largeValues_le`, `integral_norm_dirPoly_halasz_l1`), nor does it feed [`RHTower/Sieve/VinogradovKorobovPrimeNumberTheorem.lean:178`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/Sieve/VinogradovKorobovPrimeNumberTheorem.lean#L178) (`exists_abs_sum_vonMangoldt_sub_self_vk_rate`) into `band_le_chebyshev_mean_square` (`BandLimitedLaplaceEnergy.lean:189`).

3. **The Unwindowed Zero-Set Disconnect in `arithmetic-positivity-theory` & `TransHorizonIncidenceMechanics` (CHMD):**
   - In [`ZeroDiskOverlap.lean:59`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/arithmetic-positivity-theory/ZeroDiskOverlap.lean#L59) and [`FactorialTailSampling.lean:112`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialTailSampling.lean#L112), APT bounds the zero-side majorant $\mathcal{Z}(f)$ using only the unit-height Riemann–von Mangoldt count `exists_xiUnitHeightPacket_global_log_bound` across the full strip $-1/4 \le \operatorname{Re} s \le 5/4$.
   - In [`CHMDQuarterZeroBound.lean:136,229`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDQuarterZeroBound.lean#L136-L229), CHMD bound-state counts require the unproved hypothesis `(hfin : offLineZeros.Finite)` because `quarterZeros` is unwindowed in height and abscissa.
   - Meanwhile, [`RHTower/ZetaZeroDensitySeparatedSelection.lean:94`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/ZetaZeroDensitySeparatedSelection.lean#L94) defines the **unconditionally finite** height-abscissa box `zeroHeightBox (σ T : ℝ) : Set XiZeroCopy`, equipped with:
     - the folded layer-cake decomposition [`RHTower.sum_rpow_re_le_zeroHeightBox`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/XiZeroFoldedHeightCount.lean#L152) (`XiZeroFoldedHeightCount.lean`),
     - the Ingham–Huxley zero-density bound [`RHTower.exists_zeroHeightBox_ncard_le_ingham_huxley`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/ZetaZeroDensityInghamHuxley.lean#L226) (`ZetaZeroDensityInghamHuxley.lean`), and
     - the zero-free box width [`RHTower.exists_zeroHeightBox_zeroFree`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/XiZeroFreeHeightBox.lean#L27) (`XiZeroFreeHeightBox.lean`).

---

### Exact Module-by-Module Steps Across the Four Programmes

All steps below obey the strict Lean rules: 100% unconditional theorems (no unproved hypotheses, axioms, or `sorry`), foreground single-file verification via `lake env lean --old <file>`, no raised heartbeat hacks, and wiring into the respective umbrella files without running full umbrella builds.

#### Phase 1: `BezoutValuationIncidence` (BVI) — Connect to Vaughan Type I/II, Divisor Square Moments, Vinogradov–Korobov, and Unconditional Short-Window Mean Square

- **Step 1.1: Create `formal/GaloisForLFunctions/BezoutValuationIncidence/VaughanTypeIIShortAndAllHorizonMobiusL2Energy.lean`**
  - **Imports:**
    - `GaloisForLFunctions.BezoutValuationIncidence.CofinalLinearWindowMobiusEnergyAndDefectBounds`
    - `GaloisForLFunctions.RHTower.Sieve.VaughanTypeIIEstimate`
    - `GaloisForLFunctions.RHTower.Sieve.TypeIICoefficientEnergy`
  - **Exact Declarations to Prove:**
    1. `zeta_mul_truncAF_moebius_eq_sieveSeq_moebiusReal {N k : ℕ} (hk : 1 ≤ k) : ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) N) k = sieveSeq N moebiusReal k`
    2. `typeIIShort_eq_ite_one_sub_sieveSeq_moebiusReal {N k : ℕ} (hk : 1 ≤ k) : RHTower.Sieve.typeIIShort N k = (if k = 1 then 1 else 0) - sieveSeq N moebiusReal k`
    3. `typeIIShort_eq_neg_sieveSeq_moebiusReal_of_two_le {N k : ℕ} (hk : 2 ≤ k) : RHTower.Sieve.typeIIShort N k = -sieveSeq N moebiusReal k`
    4. **All-Horizon Unconditional $L^2$ Energy Bound (removing the $M \le (B+1)N$ restriction):**
       Using `RHTower.Sieve.sum_typeIIShort_sq_le N M` (`TypeIICoefficientEnergy.lean:53`), prove for **all** $N \ge 1$ and $M \ge 1$:
       `sieveL2PrefixEnergy N M moebiusReal ≤ 1 + 2 * (M : ℝ) + 2 * ((M : ℝ) * RHTower.invSum M ^ (3 : ℕ))`
       and the corresponding unconditional bound on `|sieveRenormalizedPrefixDefect N M moebiusReal|`.
    5. **Möbius Vaughan Identity & Trans-Horizon Type I / Type II Decomposition:**
       Prove `moebius_vaughan_identity (U V : ℕ)` in `ArithmeticFunction ℝ`:
       `(moebius : ArithmeticFunction ℝ) = truncAF moebius U + truncAF moebius V - zeta * truncAF moebius U * truncAF moebius V + (moebius - truncAF moebius U) * typeIIShort V`
       and substitute it into the quotient-window formula `sum_sieveSeq_moebiusReal_eq_one_sub_quotient_windows` (`UniformCofinalMobiusPrefixDiscrepancy.lean:39`) for $N \ge \max(U, V)$, splitting each trans-horizon window $\sum_{d \in (N, M/q]} \mu(d)$ into a Type-I BVI divisor sum at cutoff $U V$ plus a Type-II bilinear convolution with `typeIIShort V`.

- **Step 1.2: Create `formal/GaloisForLFunctions/BezoutValuationIncidence/VinogradovKorobovCofinalMobiusDiscrepancy.lean`**
  - **Imports:**
    - `GaloisForLFunctions.BezoutValuationIncidence.UniformCofinalMobiusPrefixDiscrepancy`
    - `GaloisForLFunctions.RHTower.Sieve.VinogradovKorobovMoebius`
  - **Exact Declarations to Prove:**
    1. Bridge `mertensM n` (`MoebiusMaximalWindow.lean:101`) to [`RHTower.Sieve.exists_abs_sum_moebius_le_vk_rate`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/Sieve/VinogradovKorobovMoebius.lean#L423):
       `exists_mertensM_le_vk_rate : ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n : ℕ in atTop, |mertensM n| ≤ B * (n : ℝ) * Real.exp (-(RHTower.Sieve.vkKappa * RHTower.Sieve.vkScale (n : ℝ) / 24))`
    2. Upgrade `abs_sum_sieveSeq_moebiusReal_le_mertensSup` (`UniformCofinalMobiusPrefixDiscrepancy.lean:79`) to an **explicit Vinogradov–Korobov rate bound** on the trans-horizon quotient windows $\sum_{q=1}^B \sum_{d \in (N, M/q]} \mu(d)$ and on `∑ k ∈ Finset.Icc 1 M, sieveSeq N moebiusReal k` for $M \le (B+1)N$.

- **Step 1.3: Create `formal/GaloisForLFunctions/BezoutValuationIncidence/ShortIntervalMobiusMeanSquareAndTransHorizonEnergy.lean`**
  - **Imports:**
    - `GaloisForLFunctions.BezoutValuationIncidence.QuotientDualOctaveReciprocityAndValuationSwitching`
    - `GaloisForLFunctions.RHTower.Sieve.MoebiusMeanSquareUnconditional`
  - **Exact Declarations to Prove:**
    1. Using first-octave reciprocity `sieveSeq_moebius_eq_neg_moebius_on_first_octave` (`QuotientDualOctaveReciprocityAndValuationSwitching.lean:125`, which proves `sieveSeq N moebiusReal k = -moebiusReal k` for $N < k \le 2N$), identify the short-interval sum $\sum_{n \in \mathrm{Ioc}(Y+k, Y+k+L)} s_{N,\mu}(n)$ for $N \le Y$ and $Y + K + L \le 2N$ with $-\sum_{n \in \mathrm{Ioc}(Y+k, Y+k+L)} \mu(n)$.
    2. Apply [`RHTower.Sieve.exists_sum_normSq_moebius_window_le`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/Sieve/MoebiusMeanSquareUnconditional.lean#L21) directly to bound the short-interval $L^2$ mean square $\sum_{k \in \mathrm{range}\,K} |\sum_{n \in \mathrm{Ioc}(Y+k, Y+k+L)} s_{N,\mu}(n)|^2$ on the trans-horizon octave $(N, 2N]$.

---

#### Phase 2: `BiScaleUncertainty` — Connect Critical-Band Spectral Density $S_N(\xi)$ to Large Values, Halász $L^1$ Bounds, and VK Chebyshev Error

- **Step 2.1: Create `formal/GaloisForLFunctions/BiScaleUncertainty/CriticalBandLargeValuesAndHalaszSpectralBounds.lean`**
  - **Imports:**
    - `GaloisForLFunctions.BiScaleUncertainty.BandLimitedLaplaceEnergy`
    - `GaloisForLFunctions.RHTower.Sieve.DirichletMeasureLargeValues`
  - **Exact Declarations to Prove:**
    1. Using `atomicFourier_eq_dirPoly N ξ` (`HighFrequencyLaplaceEnergyMeanValue.lean:51`) and `twoSidedAtomicMean_le` (`HighFrequencyLaplaceEnergyMeanValue.lean:245`), prove the **sharp Montgomery–Vaughan large-values measure bound** for `atomicFourier N`:
       For every $\Xi > 0$ and threshold $V > 0$,
       `V ^ 2 * volume.real {ξ ∈ Set.Icc (-Ξ) Ξ | V ≤ ‖atomicFourier N ξ‖} ≤ (2 * Ξ * atomicDiagonal N + 104 / π * atomicSecondMoment N)`
       and substitute `atomicDiagonal_le_cutoff_mul N` and `atomicSecondMoment_le_cutoff_mul N` (`BandLimitedLaplaceEnergy.lean:49,54`) to obtain a fully explicit bound in terms of $N$ and $L = \log(N+2)$.
    2. Transfer [`RHTower.Sieve.integral_norm_dirPoly_halasz_l1`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/Sieve/DirichletMeasureLargeValues.lean#L171) to `atomicFourier N`, bounding the $L^1$ frequency moment $\int_0^\Xi \|\operatorname{atomicFourier} N \xi\|\,d\xi$ across the critical band $\Xi = \operatorname{bandFrequency} N = \sqrt{N+2}$.

- **Step 2.2: Create `formal/GaloisForLFunctions/BiScaleUncertainty/VinogradovKorobovBandEnergyAndChebyshevProducer.lean`**
  - **Imports:**
    - `GaloisForLFunctions.BiScaleUncertainty.SawtoothPhaseCancellationAndBandSpectralProducer`
    - `GaloisForLFunctions.RHTower.Sieve.VinogradovKorobovPrimeNumberTheorem`
  - **Exact Declarations to Prove:**
    1. Connect `chebyshevErrorSeq n = chebyshevPsiSeq n - n` (`SawtoothPhaseCancellationAndBandSpectralProducer.lean:89`) to [`RHTower.Sieve.exists_abs_sum_vonMangoldt_sub_self_vk_rate`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/Sieve/VinogradovKorobovPrimeNumberTheorem.lean#L178), proving the explicit Vinogradov–Korobov bound on the common-cutoff sawtooth phase discrepancy:
       `∃ B ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, |(n : ℝ) * (moebiusLogHarmonicSum (n + k) - 1) - weightedFractSumSeq vonMangoldtDivisorWeight (n + k) n| ≤ B * (n : ℝ) * Real.exp (-(vkKappa * vkScale n / 24))`
    2. Combine with ` dyadicChebyshevDiffSeq_two_mul_eq_fractSum_diff` (`SawtoothPhaseCancellationAndBandSpectralProducer.lean:135`) to bound `|dyadicChebyshevDiffSeq (2 * m)| = |Φ_fract(2m+k, 2m) - 2 Φ_fract(2m+k, m)|` at Vinogradov–Korobov strength, improving the elementary $(\log 4 + 4)(2m)$ bound by the exponential saving $\exp(-c (\log m)^{3/5} (\log \log m)^{-5/3})$.

---

#### Phase 3: `arithmetic-positivity-theory` (APT) — Connect Zero-Side Majorant $\mathcal{Z}(f)$ and Aperture Selectivity to Ingham–Huxley Zero Density and Nyquist Lattice Laws

- **Step 3.1: Create `formal/GaloisForLFunctions/arithmetic-positivity-theory/InghamHuxleyHeightBoxZeroMajorant.lean`**
  - **Imports:**
    - `GaloisForLFunctions.«arithmetic-positivity-theory».SourceRelativeSchurMarginAndPerturbationCalculus`
    - `GaloisForLFunctions.RHTower.ZetaZeroDensityInghamHuxley`
    - `GaloisForLFunctions.RHTower.XiZeroFoldedHeightCount`
    - `GaloisForLFunctions.RHTower.XiZeroFreeHeightBox`
  - **Exact Declarations to Prove:**
    1. **Layer-Cake + Ingham–Huxley Dyadic Zero-Square Bound:**
       For any source $f : \mathbb{R} \to \mathbb{C}$ whose readout on a dyadic zero packet $G \subseteq \operatorname{XiZeroCopy}$ ($T \le |(q.1 : \mathbb{C}).\operatorname{im}| \le 2T$) satisfies $\|F_f(q.1)\|^2 \le C_f x^{(q.1 : \mathbb{C}).\operatorname{re} - 1}$ ($x \ge 1$), combine [`RHTower.sum_rpow_re_le_zeroHeightBox`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/XiZeroFoldedHeightCount.lean#L152) (`XiZeroFoldedHeightCount.lean`) with [`RHTower.exists_zeroHeightBox_ncard_le_ingham_huxley`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/ZetaZeroDensityInghamHuxley.lean#L226) and [`RHTower.exists_zeroHeightBox_zeroFree`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/XiZeroFreeHeightBox.lean#L27) to bound $\sum_{q \in G} \|F_f(q.1)\|^2$ with the Ingham–Huxley density exponent $T^{(A(\sigma)+\varepsilon)(1-\sigma)}$ and zero-free slab cutoff $\sigma \le 1 - w(4T/3)$.
    2. **Measure of Exceptional Height Windows in $[T, 2T]$:**
       Using `exists_zeroHeightBox_ncard_le_ingham_huxley`, prove that for any $\sigma \in (1/2, 1]$ and $\varepsilon \in (0, 1]$, the cardinality of any 1-separated set of heights $t_j \in [T, 2T]$ carrying a zero in $\{s : \operatorname{Re} s \ge \sigma, |\operatorname{Im} s - t_j| \le 1/2\}$ is $\le D (1 + \log T)^B T^{(A(\sigma)+\varepsilon)(1-\sigma)}$.

- **Step 3.2: Create `formal/GaloisForLFunctions/arithmetic-positivity-theory/ApertureSelectivityCriterionAndLatticeBlindness.lean`**
  - **Imports:**
    - `GaloisForLFunctions.«arithmetic-positivity-theory».SourceRelativeSchurMarginAndPerturbationCalculus`
    - `GaloisForLFunctions.RHTower.ZeroLatticeDepthNyquistLaw`
  - **Exact Declarations to Prove:**
    1. **Universal Non-Selectivity of Bounded-Aperture Test Families:**
       Using [`RHTower.offLineLattice_weil_positive_iff`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/ZeroLatticeDepthNyquistLaw.lean#L608), prove that for **any** test family $\mathcal{F} \subseteq C^2(\mathbb{R}, \mathbb{C})$ supported in $[-a, a]$ ($a > 0$) and any off-line depth $\delta \in (0, 1/2]$, every off-line vertical lattice configuration `offLineLatticeConfig hL hδ hδ'` with ordinate spacing $2\pi/L \le \pi/a$ ($L \ge 2a$) satisfies $\operatorname{Re} \mathcal{W}_{\mathrm{lat}}(f, f) \ge 0$ for all $f \in \mathcal{F}$, while still possessing infinitely many off-line zeros of real part $1/2 + \delta$.

---

#### Phase 4: `TransHorizonIncidenceMechanics` (THIM) — Remove the `offLineZeros.Finite` Premise via Windowed Ingham–Huxley Bound-State Counts and VK Chebyshev Transport

- **Step 4.1: Create `formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/WindowedQuarterZeroDensityAndCHMDBoundStateCount.lean`**
  - **Imports:**
    - `GaloisForLFunctions.RHTower.CHMDQuarterZeroBound`
    - `GaloisForLFunctions.RHTower.ZetaZeroDensityInghamHuxley`
  - **Exact Declarations to Prove:**
    1. Define the height-and-depth windowed quarter zero set:
       `def windowedQuarterZeros (σ T : ℝ) : Set ℂ := {ρ ∈ RHTower.CHMDPolar.quarterZeros | σ ≤ ρ.re ∧ T ≤ ρ.im ∧ ρ.im ≤ 2 * T}`
    2. Prove **unconditionally** (without `offLineZeros.Finite`!) that `windowedQuarterZeros σ T` is finite (`windowedQuarterZeros_finite (σ T : ℝ) : (windowedQuarterZeros σ T).Finite`) and satisfies `(windowedQuarterZeros σ T).ncard ≤ (RHTower.zeroHeightBox σ T).ncard`.
    3. Combine with `RHTower.exists_zeroHeightBox_ncard_le_ingham_huxley` to prove the **unconditional Ingham–Huxley bound on windowed quarter zeros**:
       `∀ σ ∈ Ioc (1/2) 1, ∀ ε ∈ Ioc 0 1, ∃ D ≥ 0, ∃ B : ℕ, ∃ T₀ ≥ 1, ∀ T ≥ T₀, ((windowedQuarterZeros σ T).ncard : ℝ) ≤ D * (1 + Real.log T) ^ B * T ^ ((RHTower.inghamHuxleyExponent σ + ε) * (1 - σ))`
    4. Prove the **unconditional windowed Birman–Schwinger negative-index bound**: any family of $k$ real compact tests `q : Fin k → SourceGraph` whose off-line zero-defect vanish outside `windowedQuarterZeros σ T` and on which `weilForm` is negative-definite satisfies `k ≤ 2 * (windowedQuarterZeros σ T).ncard`, hence is unconditionally bounded by $2 D (1 + \log T)^B T^{(A(\sigma)+\varepsilon)(1-\sigma)}$.

- **Step 4.2: Create `formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/VinogradovKorobovChebyshevTransportAndLowPrimeBudget.lean`**
  - **Imports:**
    - `GaloisForLFunctions.TransHorizonIncidenceMechanics.CollectiveLowPrimeChebyshevTransportAndSinhAbsorption`
    - `GaloisForLFunctions.RHTower.Sieve.VinogradovKorobovPrimeNumberTheorem`
  - **Exact Declarations to Prove:**
    1. Connect THIM's `chebyshevCountStep s = ∑ d ∈ Finset.Icc 1 ⌊Real.exp s⌋₊, ArithmeticFunction.vonMangoldt d` (`CollectiveLowPrimeChebyshevTransportAndSinhAbsorption.lean:212`) to `RHTower.Sieve.exists_abs_sum_vonMangoldt_sub_self_vk_rate` (`VinogradovKorobovPrimeNumberTheorem.lean:178`), proving the explicit Vinogradov–Korobov bound on THIM's Chebyshev Stieltjes discrepancy `|chebyshevCountDiscrepancy s| = |chebyshevCountStep s - Real.exp s|` for large $s$.

---

### Verification & Audit Protocol (Per Module)
1. **Before writing each module:** Verify every imported declaration signature in a `/tmp/check_imports.lean` file via `lake env lean /tmp/check_imports.lean`, then delete `/tmp/check_imports.lean`.
2. **Foreground single-file compile:** Run `lake env lean --old formal/GaloisForLFunctions/<Programme>/<NewModule>.lean` (one foreground process at a time, zero `maxHeartbeats` raises).
3. **Axiom & lint audit:** Verify `#print axioms` via a temporary `/tmp` file (only `propext`, `Classical.choice`, `Quot.sound` permitted), run `python3 scripts/formal_tools.py lint`, wire the module into its umbrella (`formal/GaloisForLFunctions/<Programme>.lean`) without running a full umbrella build, and clean up all `/tmp` scratch files.
