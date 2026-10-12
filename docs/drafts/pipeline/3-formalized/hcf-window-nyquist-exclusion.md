# HCF window ⇒ critical line up to the Nyquist height 2πe^{4√K}

- **ID:** C597
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** hcf-exact-layer-loop-2026-10-09.md rows 593, 596; MUST-1274; HF-F52 (`hodgeIndex_forces_critical_line_below_landau`)
- **Statement:** If the heat Hankel form is eventually nonnegative on the pole hyperplane in the window aN ≤ K (`HeatWindowNonneg K`), then every isolated zero of ξ with ordinate t₀ ≤ (1−η)·2πe^{4√K} (under the HF-F52 separation and multiplicity hypotheses) lies on the critical line.

## Goal
This gives route HCF a direct, sharp zero-location consequence: a finite window certifies RH below the Nyquist height 2πe^{2A}, A = 2√K. That is the height at which the window's β=2 log-gas freezes the zero sites (row 596). Two inputs are in hand:
- MUST-1274 turns window nonnegativity into `EvenPoleWeilNonneg A` for all A < 2√K.
- HF-F52 detects off-line zeros at the sharp Nyquist constant, but with complex modulated tests.

The missing step is an even-test detection inequality. Not circular: no RH input; the hypotheses are window positivity and zero-separation data.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea
- [x] 1 → 2  fully-proven: paper proof of the even-test detection inequality
- [x] 2 → 3  formalized: `heatWindow_forces_critical_line_below_landau`, `evenHodgeIndex_forces_critical_line_below_landau`; MUST-1281; standard axioms
- [ ] 3 → 4  publication-ready

## Approach
1. **Parity split of the corpus detection test.** The detection test is v = e^{−iγ₀u}s(u), with s odd and real.
   - Re v = cos(γ₀u)s(u) is odd and Im v = −sin(γ₀u)s(u) is even.
   - The Hermitian form satisfies W(v) = Q(Re v) + Q(Im v), since the form is real-symmetric and the zero set is closed under conjugation.
   - At an off-line zero z₀ = γ₀ − iβ₀ we have F_s(±iβ) real, because s is real. Hence F_{Re v}(z₀) ≈ ½F_s(−iβ₀) is real and contributes positively, while F_{Im v}(z₀) is imaginary and contributes negatively.
   - On-line zeros contribute squares ≥ 0 in both parts. So Q(Im v) ≤ W(v) − Q(Re v) ≤ W(v) + (other off-line contributions), and the even part inherits the negativity.
2. **Pole correction.** HF-F52 uses a polar-free modulated bump. Check that the parity split preserves pole vanishing: both parts are pole-vanishing if v is, since the moments are real and imaginary parts of a vanishing complex moment.
3. **Smoothness.** HF-F52 tests are compactly supported but may only be C²; `EvenPoleWeilNonneg` asks for C^∞. Mollify, using continuity of Q in the strip norm ∫|f''|e^{|x|/2}, which bounds |z|²|F_f(z)|.
4. **Assemble.** Window K ⇒ even pole-vanishing positivity at every A < 2√K ⇒ no isolated off-line zero below (1−η)2πe^{2A}.

## Attack (Phase 4)
- **False?** A cluster of off-line zeros could mask the even part while the odd part stays negative. HF-F52 assumes separation, which removes this.
- **Circular?** No.
- **Rediscovered?** HF-F52 is the Weil-side statement. The new content is the parity split, showing that even tests suffice at the sharp constant, and the HCF transport.
- **Significance:** moderate. It is a transport plus a parity lemma, but it gives the classical HCF object a sharp partial-RH certificate.

## Log
- 2026-10-12 — created from rows 593/596 (Coulomb-gas frozen region = Nyquist height)
- 2026-10-12 — proved in Lean. Symmetrized pair inequality: the cross terms carry the cutoff tail ε, because ĥ vanishes at the conjugate zeros. Constant 49N³A₀²(147+12L); exponent balance reused with δ₀^{3/2}. Bridge: real/imaginary split of even tests, CCM bridge, mollification limit. Modules `RHTower/EvenLandauPairTest`, `RHTower/EvenLandauSharpOffLineExclusion`, `RHTower/XiGaussianHeatWindowNyquistExclusion`.
