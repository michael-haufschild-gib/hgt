# OWU: the real cut is exactly the even mean-zero deficit (2026-10-16, Lean)

Card: docs/drafts/pipeline/3-formalized/owu-cut-is-even-mean-zero-deficit-2026-10-16.md. STATUS MUST-1549/1550.
Lean: formal/GaloisForLFunctions/RHTower/WeilCutEvenMeanZeroDeficit.lean and WeilCutFreeHolomorphicExtension.lean
(namespace RHTower.OddResolvent), wired into RHTower.lean, axioms [propext, Classical.choice, Quot.sound].

Results (all unconditional):
- `re_weilFullFunctional_eq_integral_spectralWeight_sub`: for odd-positive lam with Nevanlinna data (ν, c) of aΨ(½+a),
  z = a², and EVERY C² compact test f: Re W_lam(f⋆f̃) = ∫ Θ_f dν − c‖f̂(0)‖².
- `spectralWeight_eq_of_pos` (critical ordinates, any f), `spectralWeight_eq_of_neg_of_even` (cut, even f:
  [|f̂(0)|² − (1+γ²)|f̂(i√(−γ))|²]/(−γ)), centre by continuity, `spectralWeight_nonneg_of_meanZero_of_not_cut`.
- `cut_measure_eq_zero_of_even_meanZero_nonneg`: W ≥ 0 on even tests with f̂(0)=0 ⟹ ν{ζ≠1, γ<0} = 0.
  Mechanism: two-bump test b(·−L)−2b+b(·+L); f̂_L(v) = (2cos Lv − 2)b̂(v) on ℝ (critical part ≤ 4L²(‖b‖₁²+‖b''‖₁²)ν(S¹)),
  f̂_L(ir) = (2cosh rL − 2)∫b e^{−ru} on the cut (≥ (rL)²/2 · ∫b), so r₀⁴(∫b)²L⁴ν(cut_{r₀}) ≤ 4L²(...)ν(S¹) ⟹ ν(cut_{r₀}) = 0.
- `weilFullFunctional_nonneg_of_cut_eq_zero` (converse, all mean-zero tests), `even_meanZero_nonneg_iff_cut_eq_zero`.
- `exists_extension_of_cut_eq_zero`: cut-free ⟹ holomorphic extension of weilFunction to Re s > ½
  (cutFreeExtension ν c s = (∫(γz−1)/(z+γ) dν − c)/(s−½); dominated differentiation off (−∞,0]; identity theorem).
- `exists_extension_of_weilPositiveOdd_of_even_meanZero_nonneg`, `eq_vonMangoldt_and_riemannHypothesis_of_even_meanZero_nonneg`
  (odd ∧ even-mean-zero ∧ Re Φ ≥ 0 on (½,∞) ⟹ λ = Λ ∧ RH via the square-root transfer).

Reading: the modulo-constants cone (WeilPositiveModConst) = cut-free part of the odd cone; Full = ModConst + central
nonnegativity. OWU Needs now: even mean-zero positivity (= cut removal) from the arithmetic source, central
nonnegativity, odd-positive source existence (⟺ PrimeBlindPositiveOddAt 1 by odd Farkas).

Lean notes: ContDiffBump (0:ℝ) := ⟨1,2,one_pos,one_lt_two⟩ with .neg/.nonneg'/.contDiff/.hasCompactSupport;
integral_complex_ofReal; pow_le_pow_left₀; Set.indicator_of_notMem; hasDerivAt_integral_of_dominated_loc_of_deriv_le
needs explicit (F := ..) (F' := ..); HasDerivAt.div over ℂ: use .congr_deriv not convert;
measureReal_eq_zero_iff (measure_ne_top ν _).
