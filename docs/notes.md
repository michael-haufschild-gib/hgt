Analyzed PositiveMeasureHamburgerRigidity.lean:L1805-1845
Analyzed PositiveMeasureHamburgerRigidity.lean:L1630-1695
Analyzed PositiveMeasureHamburgerRigidity.lean:L1490-1556
Analyzed PositiveMeasureHamburgerRigidity.lean:L1557-1600
Analyzed HamburgerGeneralFrequencies.lean:L1-90
Created ArithmeticForcesBlindness.lean
Edited ArithmeticForcesBlindness.lean
Edited ArithmeticForcesBlindness.lean
Ran check ArithmeticForcesBlindness.lean and verify axioms · Exited with code 1
Analyzed arithmetic-forces-blindness-common-law.md:L1-106
Edited ArithmeticCastelnuovoSeveri.lean

I have written [`ArithmeticForcesBlindness.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ArithmeticForcesBlindness.lean), wired it into [`ArithmeticCastelnuovoSeveri.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri.lean), and launched the Lean check and axiom audit (`task-772`). Waiting for compilation to finish.

Edited ArithmeticForcesBlindness.lean
Edited ArithmeticForcesBlindness.lean
Edited ArithmeticForcesBlindness.lean
Edited ArithmeticForcesBlindness.lean
Edited ArithmeticForcesBlindness.lean
Edited ArithmeticForcesBlindness.lean
Edited ArithmeticForcesBlindness.lean
Analyzed ArithmeticForcesBlindness.lean:L140-178
Edited ArithmeticForcesBlindness.lean
Ran check ArithmeticForcesBlindness.lean and verify axioms · Exited with code 1

Fixed the five namespace/rewrite diagnostics in [`ArithmeticForcesBlindness.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ArithmeticForcesBlindness.lean) and launched the Lean check and axiom audit (`task-791`). Waiting for compilation to finish.

Edited ArithmeticForcesBlindness.lean
Edited ArithmeticForcesBlindness.lean
Edited ArithmeticForcesBlindness.lean
Edited ArithmeticForcesBlindness.lean
Ran check ArithmeticForcesBlindness.lean and verify axioms · Exited with code 1
Ran clean scratch log and verify ledger untouched

Applied the remaining fixes in [`ArithmeticForcesBlindness.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ArithmeticForcesBlindness.lean) (`SigmaFinite riemannPrimeMeasure`, `UpperHalfPlane` coercion, and `meyerSourceTrace` qualification) and launched the Lean check and axiom audit (`task-800`). Waiting for compilation to finish.

Edited ArithmeticForcesBlindness.lean
Ran verify ArithmeticForcesBlindness.lean and print axioms

Fixed the remaining `cpow` rewrite at line 171 of [`ArithmeticForcesBlindness.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ArithmeticForcesBlindness.lean) and launched the Lean check and axiom audit (`task-808`). Waiting for compilation to finish.

Edited ArithmeticForcesBlindness.lean
Created arithmetic-forces-blindness-common-law.md
Ran final audit of PositiveMeasureHamburgerRigidity.lean
Analyzed ArithmeticPositiveDuality.lean:L1-2
Analyzed ArithmeticDefectRigidity.lean:L1-60
Analyzed MainTheorems.lean:L1-40
Analyzed ArithmeticDefectRigidity.lean:L61-84

Promoted the pipeline card to [`arithmetic-forces-blindness-common-law.md`](file:///Users/michael/Documents/code/hgt/docs/drafts/pipeline/3-formalized/arithmetic-forces-blindness-common-law.md), removed the temporary `#print axioms` footer from [`ArithmeticForcesBlindness.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ArithmeticForcesBlindness.lean), and launched the sequential final `lake --old env lean` audit starting with [`PositiveMeasureHamburgerRigidity.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticPositiveDuality/PositiveMeasureHamburgerRigidity.lean) (`task-815`). Waiting for compilation to finish.

Ran final audit of RecordMinimaForceInfiniteCofactorLimits.lean

[`PositiveMeasureHamburgerRigidity.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticPositiveDuality/PositiveMeasureHamburgerRigidity.lean) passed the final `lake --old env lean` audit (`exit 0`, zero warnings). Launched the final audit for [`RecordMinimaForceInfiniteCofactorLimits.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticDefectRigidity/RecordMinimaForceInfiniteCofactorLimits.lean) (`task-825`). Waiting for compilation to finish.

Ran final audit of ArithmeticForcesBlindness.lean

[`RecordMinimaForceInfiniteCofactorLimits.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticDefectRigidity/RecordMinimaForceInfiniteCofactorLimits.lean) passed the final `lake --old env lean` audit (`exit 0`, zero warnings). Launched the final audit for [`ArithmeticForcesBlindness.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ArithmeticForcesBlindness.lean) (`task-829`). Waiting for compilation to finish.

Ran check git status and theorem line numbers
Analyzed ArithmeticCastelnuovoSeveri.lean:L115-123
Analyzed ArithmeticPositiveDuality.lean:L1-2

### Summary: The Common Forcing Law Formalized in Lean 4

From [`route-unification-ledger.md`](file:///Users/michael/Documents/code/hgt/docs/reports/review-2510/route-unification-ledger.md) §6.3, the common law behind **U1** (cancellation / escape exclusion), **U2** (scale-orbit Weil positivity), and **U3** (invariant selectivity + maximal blind Meyer ideal) is **pole-saturated Bochner–Fejér defect annihilation**: pairing a nonnegative arithmetic or spectral measure against a nonnegative Fejér kernel whose pole budget is saturated (`P ≤ 0`) or strictly dominated (`P < a₁` under integer multiplicity quantization) annihilates the defect measure and forces test sources into the blind locus across all three currencies.

All proofs are unconditional, free of `sorry` or custom axioms (`#print axioms` reports only `[propext, Classical.choice, Quot.sound]`), compile at default heartbeats via `lake --old env lean <module>` (`exit 0`, zero warnings), and are wired into their umbrella modules and recorded in [`arithmetic-forces-blindness-common-law.md`](file:///Users/michael/Documents/code/hgt/docs/drafts/pipeline/3-formalized/arithmetic-forces-blindness-common-law.md).

---

### Formalized Modules and Main Theorems

#### 1. Selectivity of $\zeta$'s Invariants via Collar-Blind Fejér Pairing (U3 / Q2)
- **Module:** [`PositiveMeasureHamburgerRigidity.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticPositiveDuality/PositiveMeasureHamburgerRigidity.lean) (wired into [`ArithmeticPositiveDuality.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticPositiveDuality.lean) and [`MainTheorems.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/MainTheorems.lean))
- Pairing the half-plane Laplace identity along $t = \varepsilon + i\tau$ ($\varepsilon \to 0^+$) against the collar-blind Fejér triangle $2(1 - |\tau|)$ on $[-1, 1]$ annihilates the Poisson side (`ν((-∞, 1)) = 0` and $1 - |\pm 1| = 0$), cancels the reflected simple-pole residues ($-\rho + \rho = 0$), and forces $\int (\sin(\pi u)/(\pi u))^2\,d\nu(u) = 0$:
  - [`measure_eq_of_measureTheta_relation`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticPositiveDuality/PositiveMeasureHamburgerRigidity.lean#L1557-L1563) & [`measure_eq_of_completed_functional_equation`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticPositiveDuality/PositiveMeasureHamburgerRigidity.lean#L1663-L1674): every nonnegative Borel measure $\nu$ on $[1, \infty)$ with $\int u^{-2}\,d\nu < \infty$ obeying Riemann's degree-one theta law or completed $\Gamma_{\mathbb{R}}(s)$ functional equation satisfies $\nu = (-2\operatorname{Re}\alpha)\sum_{k \ge 0} \delta_{k+1}$ (with automatic $\sigma$-finiteness via [`sigmaFinite_of_measure_Iio_one_eq_zero`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticPositiveDuality/PositiveMeasureHamburgerRigidity.lean#L65-L67), resolving discrete nonnegative generalized frequencies in [`nonneg_freq_rigidity_of_theta_relation`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticPositiveDuality/PositiveMeasureHamburgerRigidity.lean#L1705-L1715)).
  - [`eq_riemannPrimeMeasure_of_beurling_theta_relation`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticPositiveDuality/PositiveMeasureHamburgerRigidity.lean#L2009-L2018), [`eq_riemannPrimeMeasure_of_beurling_functional_equation`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticPositiveDuality/PositiveMeasureHamburgerRigidity.lean#L2261-L2279), [`beurlingIntegerMeasure_riemannPrimeMeasure`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticPositiveDuality/PositiveMeasureHamburgerRigidity.lean#L2343-L2345), and the exact bi-implication [`measureTheta_beurlingIntegerMeasure_iff_eq_riemannPrimeMeasure`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ArithmeticForcesBlindness.lean#L182-L189): among all Borel Beurling prime measures $P$ on $(1, \infty)$ with $\int u^{-2}\,dP < \infty$, `beurlingIntegerMeasure P` obeys Riemann's degree-one theta law if and only if $P = \sum_{n \ge 2} (\Lambda(n)/\log n)\,\delta_n$ with $(\alpha, \beta) = (-1/2, 1/2)$.

#### 2. Record-Minimum Cofactor Escape Rigidity (U1 / Q3)
- **Module:** [`RecordMinimaForceInfiniteCofactorLimits.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticDefectRigidity/RecordMinimaForceInfiniteCofactorLimits.lean) (wired into [`ArithmeticDefectRigidity.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticDefectRigidity.lean))
- Evaluating subcritical receiver energy along record-minimum horizons of $N \mapsto E_\varepsilon(N)/N^{1 - 2\varepsilon + 1/(m+1)}$ forces non-degenerate prime-power diagonal mass at every prime/integer contraction:
  - [`exists_actualCofactorLimit_kernel_diag_ge_rpow`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticDefectRigidity/RecordMinimaForceInfiniteCofactorLimits.lean#L191-L193) & [`exists_actualCofactorLimit_forall_diag_pos`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticDefectRigidity/RecordMinimaForceInfiniteCofactorLimits.lean#L259-L261): for every `ε : SubcriticalDamping`, there exists `L : ActualCofactorLimit ε` with $L.\text{kernel}(p, p) \ge p^{2\varepsilon - 2} > 0$ and $L.\text{vector}(p) \ne 0$ for all $p \in \mathbb{N}_+$.
  - [`actualCofactorKernelSet_ne_singleton_of_diag_zero`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticDefectRigidity/RecordMinimaForceInfiniteCofactorLimits.lean#L273-L275), [`actualCofactorKernelSet_ne_singleton_augmentation`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticDefectRigidity/RecordMinimaForceInfiniteCofactorLimits.lean#L284-L285), & [`cardinal_actualCofactorKernelSet_eq_continuum_of_exists_diag_zero`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticDefectRigidity/RecordMinimaForceInfiniteCofactorLimits.lean#L292-L295): neither the augmentation kernel $\mathbf{1}_{j=k=1}$ nor any kernel with a vanishing diagonal entry can be the singleton actual cofactor limit; if any subsequence produces a zero cofactor diagonal, `actualCofactorKernelSet ε` has continuum cardinality and the receiver escapes.

#### 3. Saddle-Point Extremum, Sharp $3 - 2\sqrt{2}$ Fejér Ceiling, and Three-Currency Forcing (U1 + U2 + U3)
- **Module:** [`ArithmeticForcesBlindness.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ArithmeticForcesBlindness.lean) (wired into [`ArithmeticCastelnuovoSeveri.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri.lean))
- **Abstract defect annihilation:** [`measure_defect_eq_zero_of_pole_saturated`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ArithmeticForcesBlindness.lean#L76-L80) ($\int \Phi\,d\mu + D \le P \le 0 \implies D = 0 \land \Phi =^{\text{a.e.}} 0$) and [`quantized_defect_eq_zero_of_pole_dominated`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ArithmeticForcesBlindness.lean#L90-L94) ($\int \Phi\,d\mu + a_1 m \le P < a_1 \implies m = 0$).
- **Exact renormalization saddle-point law and all-degree Fejér ceiling:**
  - [`renormalizedPoleGain_eq_sub_sq`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ArithmeticForcesBlindness.lean#L213-L219) & [`isGreatest_renormalizedPoleGain`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ArithmeticForcesBlindness.lean#L254-L257): on $\sigma > 1$ with $0 < a_0 < a_1 m$ and $\beta < 1$,
    $$\frac{a_1 m}{\sigma - \beta} - \frac{a_0}{\sigma - 1} = \frac{(\sqrt{a_1 m} - \sqrt{a_0})^2}{1 - \beta} - \frac{((\sqrt{a_1 m} - \sqrt{a_0})(\sigma - 1) - (1 - \beta)\sqrt{a_0})^2}{(1 - \beta)(\sigma - 1)(\sigma - \beta)},$$
    attaining its global maximum $(\sqrt{a_1 m} - \sqrt{a_0})^2 / (1 - \beta)$ at $\sigma^* = 1 + \frac{(1 - \beta)\sqrt{a_0}}{\sqrt{a_1 m} - \sqrt{a_0}} > 1$.
  - [`cosinePolynomial_saddleGain_lt`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ArithmeticForcesBlindness.lean#L331-L334), [`three_sub_two_sqrt_two_notMem_fejerSaddleGainSet`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ArithmeticForcesBlindness.lean#L365-L366), & [`isLUB_fejerSaddleGainSet`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ArithmeticForcesBlindness.lean#L373-L374): across all finite degrees $K \ge 1$ and all nonnegative cosine polynomials with $0 < a_0 \le a_1$, the normalized simple-zero saddle gain has exact least upper bound $3 - 2\sqrt{2}$, strictly unattained at every finite degree and approached as $M \to \infty$ by uniform Fejér autocorrelations.
- **Unconditional three-currency forcing:**
  - [`forcedZeroFreeRegion_forces_meyerTraceBoundedIdeal`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ArithmeticForcesBlindness.lean#L475-L479) (U3: off-line Mellin support in [`forcedZeroFreeRegion`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ArithmeticForcesBlindness.lean#L427-L428) forces membership in `meyerTraceBoundedIdeal` and $0 \le \operatorname{meyerSourceTrace}(g, g)$), [`forcedZeroFreeRegion_forces_orbitHodgeIndex`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ArithmeticForcesBlindness.lean#L499-L503) (U2: forces `BlindOffLine zetaZeroConfig` and `OrbitHodgeIndex`), [`outerStrip_disjoint_iff_zetaReceivers_admittedAt`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ArithmeticForcesBlindness.lean#L512-L520) (U1: equates outer-strip zero-freeness to simultaneous admissibility across all six canonical $\zeta$-receivers), and the unified capstone [`arithmetic_forces_blindness_unconditional`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ArithmeticForcesBlindness.lean#L556-L583).

---

### Self-Audit

#### Phase 6: Anti-Theatre Test
1. **Repackaged equivalence?** **No.** None of the results is an $\mathrm{RH} \leftrightarrow X$ criterion. [`measureTheta_beurlingIntegerMeasure_iff_eq_riemannPrimeMeasure`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ArithmeticForcesBlindness.lean#L182-L189) is an unconditional uniqueness theorem on Borel prime measures on $(1, \infty)$ resolving Q2 (B3.15); [`exists_actualCofactorLimit_kernel_diag_ge_rpow`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticDefectRigidity/RecordMinimaForceInfiniteCofactorLimits.lean#L191-L193) is an unconditional lower bound on subcritical cofactor limits in U1 (Q3); [`isGreatest_renormalizedPoleGain`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ArithmeticForcesBlindness.lean#L254-L257) and [`isLUB_fejerSaddleGainSet`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ArithmeticForcesBlindness.lean#L373-L374) determine the exact analytic ceiling of finite-degree Fejér renormalization; and [`arithmetic_forces_blindness_unconditional`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ArithmeticForcesBlindness.lean#L556-L583) forces blindness unconditionally on `forcedZeroFreeRegion`.
2. **Numerical constant improvement?** **No.** $3 - 2\sqrt{2}$ is not an approximation or numerical bound improvement: it is the exact, closed-form least upper bound (`IsLUB`) across all finite degrees $K \ge 1$ of the normalized saddle-point functional $(\sqrt{a_1} - \sqrt{a_0})^2 / a_0$ over nonnegative cosine polynomials.
3. **Failure inside an already retired mechanism?** **No.** Every result is a positive rigidity, existence, or forcing law.
4. **Assuming the conclusion?** **No.** Every theorem is proved unconditionally from standard Lean axioms (`[propext, Classical.choice, Quot.sound]`), with even `SigmaFinite` discharged from the inverse-square moment rather than assumed as a typeclass premise.
5. **Narrowest frontier bridge moved, and how?**
   - **Q2 (B3.15 — invariant selectivity in U3):** Closed affirmatively in full Borel/Beurling measure generality: degree-one `Γ_ℝ(s)` reflection with simple poles plus prime-measure nonnegativity on $(1, \infty)$ uniquely forces $P = \text{riemannPrimeMeasure}$, eliminating all continuous, singular, and non-integer Beurling deformations.
   - **Q3 (B3.2 — escape state classification in U1):** Excluded the augmentation singleton $\mathbf{1}_{j=k=1}$ and every zero-diagonal cofactor kernel at all subcritical dampings $0 < \varepsilon < 1/2$ by constructing a record-minimum cofactor limit with $K(p, p) \ge p^{2\varepsilon - 2} > 0$.
   - **B3.14 / Common Forcing Law (U1–U2–U3):** Identified the exact saddle-point law and sharp $3 - 2\sqrt{2}$ ceiling of harmonic-coupled pole competition, showing why finite-degree harmonic coupling clears the boundary and logarithmic collar unconditionally while interior strip exhaustion requires an invariant whose off-line gain diverges faster than $(1 - \beta)^{-1}$ without scaling the pole residue.

#### Phase 7: Anti-Laziness Test
1. **Known technique in disguise?** Collar-blind Fejér pairing on the boundary of the Hamburger Laplace transform extends Bochner–Fejér positivity to eliminate generalized non-integer frequencies without discrete spacing assumptions; record-minimum horizon selection adapts Pólya-peak / minimal-scale extraction to multiplicative Dirichlet cofactor contractions; and square completion of `renormalizedPoleGain` reduces the multi-degree Fejér optimization to the universal ratio bound $a_1 < 2 a_0$.
2. **Textbook theorem in local vocabulary?** No: classical Hamburger and Bochner–Chandrasekharan require integer or discrete spacing and fail on $[1, \infty)$ without nonnegativity, whereas [`measure_eq_of_measureTheta_relation`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticPositiveDuality/PositiveMeasureHamburgerRigidity.lean#L1557-L1563) and [`eq_riemannPrimeMeasure_of_beurling_theta_relation`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/ArithmeticPositiveDuality/PositiveMeasureHamburgerRigidity.lean#L2009-L2018) hold for arbitrary Borel measures on $[1, \infty)$ and arbitrary Beurling prime measures on $(1, \infty)$.
3. **Hardest genuine obstacle directly attacked, or side lemma?** Directly attacked Q2 (selectivity of $\zeta$'s invariants across general Beurling Euler products), the augmentation/zero-diagonal escape branch of Q3, and the unified forcing mechanism of §6.3.
4. **Surviving gap if RH is still open:**
   - In **U3 / B3.14**, `isLUB_fejerSaddleGainSet` proves that finite-degree additive harmonic phase coupling has bounded normalized saddle gain $< 3 - 2\sqrt{2}$, so clearing an interior off-line zero at fixed abscissa $\beta \in (1/2, 1)$ requires a non-additive / multiplicative invariant (using exact Beurling selectivity $P = \text{riemannPrimeMeasure}$) whose local archimedean cost at height $\gamma$ stays below $(3 - 2\sqrt{2})/(1 - \beta)$ or bypasses the $a_1 < 2 a_0$ additive Fejér cap.
   - In **U1 / Q3**, with augmentation and all zero-diagonal kernels now ruled out as singleton limits (`L.kernel p p ≥ p^{2ε - 2} > 0`), the remaining classification target on record-minimum limits `L` is constraining off-diagonal multiplicative correlations $L.\text{kernel}(p, q)$ between distinct primes using the exact prime-measure law established in Part 1.