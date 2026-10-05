# RH ⇒ Báez-Duarte discrete distances tend to 0 (hard direction of Nyman–Beurling)

- **ID:** nb-hard-direction
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper → Lean)
- **Source:** RH goal loop cycle 277; corpus has only `riemannHypothesis_of_tendsto_bdDistDiscrete`
  (easy direction) and the floor `bdDistDiscrete_floor_of_zero`.
- **Statement:** RH ⇒ `bdDistDiscrete N → 0` (Báez-Duarte 2003), hence RH ⟺ `d_N → 0`.

## Goal
Complete the corpus Nyman–Beurling/Báez-Duarte criterion into an iff with an unconditional proof of
the hard direction from RH. Only reciprocal-integer dilations θ = 1/n are used, so this is the
discrete strengthening.

## Approach (paper proof)
Notation: s = ½+it, Z(w) = (w−1)ζ(w), corpus carrier ≅ L²((0,1], dy) ≅ L²(ℝ) via y = e^{−u},
f ↦ e^{−u/2} f(e^{−u}). Span of generators = {Σ a_n {1/(ny)} : Σ a_n/n = 0} (finite).
1. **Plancherel distance.** For finite real a with Σ a_n/n = 0, P(s) = Σ a_n n^{−s}:
   ‖1_{(0,1]} + Σ a_n{1/(ny)}‖² = (1/2π) ∫ |1 − ζ(s)P(s)|² dt/|s|².
   (Fourier of e^{−u/2}1_{u≥0} is 1/s; fractGramPull gives −ζP/s.)
2. **δ-limit (RH).** ∫ |1 − ζ(s)/ζ(s+δ)|² dt/|s|² → 0 as δ ↓ 0: pointwise → 0; domination
   |ζ(s)/ζ(s+δ)| ≤ |G(s+δ)/G(s)| ≤ C(1+|t|)^{δ/2}, G = ½s(s−1)π^{−s/2}Γ(s/2), using
   `norm_XiC_vertical_monotoneOn_of_rh` (|ξ| nondecreasing to the right of the line under RH).
3. **Riesz-mean mollifier (RH).** Q_N(z) = Σ_{n≤N} μ(n)(1−n/N)n^{−z}. Perron (PNTPlus
   `Perron.formulaGtOne/LtOne`): Q_N(z) = (1/2πi)∫_{(c₀)} N^u/(ζ(z+u)u(u+1)) du. Shift to Re u = −c
   (0 < c < δ, Re z = ½+δ) past the residue 1/ζ(z): |Q_N(z) − 1/ζ(z)| ≤ C N^{−c}(|t|+3)^ε, using RH
   growth `RiemannHypothesisZetaGrowth.exists_norm_riemannZeta_two_sided` (+ compact part).
4. **Assembly.** P = Q_N(·+δ) − Q_N(1+δ)·[n=1]: terms ≤ 3(∫|1−ζ/ζ(·+δ)|² + ∫|ζ|²|1/ζ(·+δ)−Q_N|²
   + |Q_N(1+δ)|²∫|ζ|²)/|s|²; second → 0 (N→∞) by step 3 + ∫|ζ|²(|t|+3)^{2ε}/|s|² < ∞ (fourth
   moment, Cauchy–Schwarz); third small since Q_N(1+δ) → 1/ζ(1+δ) and ζ(1+δ) ≥ 1/δ.
5. Transfer step 1 to the corpus carrier (`bdGen`, `bdTarget`, `bdDistDiscrete`).

## Lean status
- [x] S1 Plancherel distance formula — `RHTower.integrable_and_norm_sq_bdTarget_sub_sum_bdGen` (BaezDuarteDistancePlancherel)
- [x] S2 δ-limit under RH — `RHTower.tendsto_integral_one_sub_riemannZeta_ratio_of_rh` (ZetaShiftRatioMeanSquareLimit); ratio bound `exists_norm_riemannZeta_half_le_of_rh`
- [x] S3 Riesz–Perron contour shift — `RHTower.exists_norm_moebiusRieszPoly_sub_le_of_rh` (InverseZetaRieszPerronShift)
- [x] S4 assembly — `RHTower.exists_norm_sq_bdTarget_sub_bdRiesz_le_of_rh` (BaezDuarteCriterionHardDirection)
- [x] S5 corpus transfer + iff — `RHTower.riemannHypothesis_iff_tendsto_bdDistDiscrete`

## Log
- 2026-10-05 — created; ingredients located (ξ monotonicity, fourth moment, RH ζ-growth, Perron).
- 2026-10-05 — S1 formalized: ‖bdTarget − Σc_n bdGen(1/n)‖² = (1/2π)∫|1+ζ(s)P_c(s)|²dt/(¼+t²), P_c(s) = Σc_n(n^{−s}−1/n).
- 2026-10-05 — S2 formalized: RH ⇒ |ζ(½+it)| ≤ K(1+|t|)^{1/8}|ζ(½+δ+it)| (0≤δ≤¼) and ∫|1−ζ(s)/ζ(s+δ)|²/(¼+t²) → 0.
- S3 plan: Q_X(z)=Σ_{n≤X}μ(n)(1−n/X)n^{−z} = (1/2πi)∫_{(1)} X^w/(w(w+1))·(z+w−1)/ζ_u(z+w) dw (PNTPlus kernel), shift to Re w=−δ/2 via `HTGeometry.verticalIntegral'_sub_of_simple_pole`, RH input `ZetaGrowth.exists_norm_riemannZeta_two_sided`.
- 2026-10-05 — S3–S5 formalized; RH ⟺ d_N → 0 is axiom-clean (MUST-778). Card complete → 3-formalized.
