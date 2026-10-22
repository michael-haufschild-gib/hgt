# Reverse Twisted-Arc Duality on the $2\times 2$ Pole-Compression Matrix

- **ID:** reverse-twisted-arc-pole-compression
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/review-2110/argon.md · §1.5 Mechanism 4
- **Statement:** Unconditional formalization of the Four-Part Reverse Twisted-Arc Duality & $2\times 2$ Pole-Compression Theorem (`reverse_twisted_arc_pole_compression_master_theorem`) in `GaloisForLFunctions.ReverseTwistedArcPoleCompression`:
  1. **Rank-One Even-Pole Collapse & Reverse Twisted-Arc Conservation Law for $\Lambda$ (`TwistedArcShiftedGammaPoleProjection.lean`):**
     - Proves that the $j=0$ shifted-Gamma test $F_0 = \text{xiShiftedGammaTest } 0$ projects purely onto the **even** pole channel: $\int_{\mathbb{R}} F_0(u)\cosh(u/2)\,du = 1/2$ and $\int_{\mathbb{R}} F_0(u)\sinh(u/2)\,du = 0$ (`integral_xiShiftedGammaTest_zero_cosh_half`, `integral_xiShiftedGammaTest_zero_sinh_half`).
     - Proves that because $Q_j(i/2) = 0$ for every $j \ge 1$, the entire infinite shifted-Gamma pole pairing $\sum_{j=0}^\infty w_j \cdot 2(\int_{\mathbb{R}} F_j(u)e^{-u/2}\,du)(\int_{\mathbb{R}} F_j(u)e^{u/2}\,du)$ collapses unconditionally to the **rank-one $j=0$ mode** $w_0 / 2$ for every sequence $w : \mathbb{N} \to \mathbb{R}$ (`tsum_shiftedGamma_pole_eq_half_mul_zero`).
     - Proves that the actual von Mangoldt function $\Lambda$ satisfies the linear partial-sum bound $|\text{primeWeightPartialSum } \Lambda \, N| \le (\log 4 + 4)(N+1)$ (`abs_primeWeightPartialSum_vonMangoldt_le`), and deduces the **Reverse Twisted-Arc Conservation Law for $\Lambda$** (`exists_twistedArc_weights_vonMangoldt_blind_and_pole_limit`): there exist unconditional twisted-arc weights $w_j \ge 0$ with $w_0 > 0$ and $\sum_j w_j (j!(3/2)^j)^2 < \infty$ such that as the truncation aperture $L \to \infty$,
       - the zero-side sum $\sum_{j=0}^\infty w_j \operatorname{Re} W_\zeta(\text{truncTest } F_j L, \text{truncTest } F_j L) \to 0$,
       - the actual von Mangoldt prime-power sum $\sum_{j=0}^\infty w_j \text{atomPairing}(\Lambda, \text{truncTest } F_j L \star \widetilde{\text{truncTest } F_j L}) \to 0$,
       - the truncated pole sum $\sum_{j=0}^\infty w_j \cdot 2(\int_{\mathbb{R}} \text{truncTest } F_j L(u)e^{-u/2}\,du)(\int_{\mathbb{R}} \text{truncTest } F_j L(u)e^{u/2}\,du) \to w_0 / 2 > 0$, and
       - the pure archimedean Gamma functional ($\beta = 0$, $v = 0$) satisfies $\sum_{j=0}^\infty w_j \operatorname{Re}(\text{weilPoleWeightFunctional } 0 \, (\text{fun } \_ \Rightarrow 0) (\text{weilTest } (\text{truncTest } F_j L) (\text{truncTest } F_j L))) \to -w_0 / 2 < 0$.
  2. **Parity-Split Null Duality & Three-Way Decomposition of the $2\times 2$ Pole Space (`ParitySplitNullPoleDuality.lean`):**
     - Proves that the odd-type null test $\text{oddNullTest} = F_1 - \frac{1}{4} F_0$ projects purely onto the **odd** pole channel: $\int_{\mathbb{R}} \text{oddNullTest}(u)\cosh(u/2)\,du = 0$ and $\int_{\mathbb{R}} \text{oddNullTest}(u)\sinh(u/2)\,du = 1/8$, with strictly negative pole pairing $-1/32 < 0$ (`integral_oddNullTest_cosh_half`, `integral_oddNullTest_sinh_half`).
     - Proves that the depth-null test at the true pole depth $c = 1/2$, $\text{depthNullTest}(1/2)$, is orthogonal to the entire $2\times 2$ pole space $\text{span}(e^{-u/2}, e^{u/2}, \cosh(u/2), \sinh(u/2))$ with zero pole pairing (`integral_depthNullTest_half_exp_neg_half`, `integral_depthNullTest_half_exp_half`, `integral_depthNullTest_half_cosh_half`, `integral_depthNullTest_half_sinh_half`, `pole_depthNullTest_half`).
     - Packages the three-way orthogonal decomposition of $\Xi$-divisible shifted-Gamma tests (`xiDivisible_two_by_two_pole_channel_decomposition`) together with two-sided pole-weight and pole-depth rigidity ($\beta = 1$ and $c^2 = 1/4$).
  3. **Unified Five-Way Pole-Compression & Twisted-Arc Equivalence + Opposite-Curvature Wall-Crossing Dichotomy (`PoleCompressionTwistedArcBridge.lean`):**
     - Proves `poleCompression_iff_weilCone_nonempty_and_deficit_bound`: the $2\times 2$ pole-compression bound $\forall a, |\text{ccmWeilPoleCross } a| \le \text{ccmWeilPoleDiagonal } a$ is unconditionally equivalent to parity-pole nonnegativity, coupled prime-polynomial dominance $\operatorname{Re} \Pi_f(\xi) \le \operatorname{Re} A_f(\xi)$, the square-root logarithmic Chebyshev deficit primitive bound $|\text{ccmLogChebyshevDeficitPrimitive } t| \le B e^{t/2}$, and nonemptiness (and singleton rigidity at $\Lambda$) of the full Weil positivity cone $\exists \lambda, \text{WeilPositiveFull } \lambda$.
     - Proves `exists_threshold_poleCompression_trace_pos_and_opposite_curvatures`: above an explicit threshold $A_0$, the $2\times 2$ pole trace $2\,\text{ccmWeilPoleDiagonal } a > 0$ is strictly positive, the even and odd pole chambers have strictly opposite second derivatives (`ccmWeilEvenPoleChamber_second_pos`, `ccmWeilOddPoleChamber_second_neg`), and any hypothetical violation $|\text{ccmWeilPoleCross } a| > \text{ccmWeilPoleDiagonal } a$ can flip the sign of **at most one** parity pole channel while the opposite parity channel remains strictly positive.
  4. **Master Reverse Twisted-Arc Pole-Compression Theorem (`MasterReverseTwistedArcPoleCompressionTheorem.lean`):**
     - Synthesizes all four legs into `reverse_twisted_arc_pole_compression_master_theorem` and isolates the exact remaining boundary between $\Xi$-divisible twisted-arc tests and the literal finite-aperture CCM pole-compression vectors.

## Goal
To research, derive, and formalize §1.5 Mechanism 4 of Project Argon (`docs/reports/review-2110/argon.md`), bridging the $2\times 2$ pole-compression matrix (`CCMRestrictedWeilPoleCompressionRHCriterion`, `PrimeTailCouplingCriterion`, `CCMRestrictedWeilPoleTracePositivity`, `CCMRestrictedWeilPoleParityCurvature`) with the twisted-arc minimum principle and $\Xi$-divisible shifted-Gamma pole-rigidity tower (`WeilConeUniquenessUnconditional`, `WeilPoleWeightBelowOneEmpty`, `WeilPoleWeightAboveOneVonMangoldt`, `WeilPoleDepthRigidity`) in its own subfolder `formal/GaloisForLFunctions/ReverseTwistedArcPoleCompression/`.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem `GaloisForLFunctions.ReverseTwistedArcPoleCompression.reverse_twisted_arc_pole_compression_master_theorem`, `lake --old env lean` green, zero axioms/sorrys
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Log
- 2026-10-22 — Created in `1-in-progress`.
