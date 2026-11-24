import GaloisForLFunctions.ArithmeticPositiveDuality.TheMeromorphicTemperedEulerFirewall
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.EulerAcceleratedSignedPartialSums
import GaloisForLFunctions.RHTower.SmoothAFEZetaGeneralTwoHeadTruncation
import GaloisForLFunctions.RHTower.GammaVerticalRatioUniform
import GaloisForLFunctions.RHTower.RouteBOfflineDomination
import GaloisForLFunctions.RHTower.WeilPrimeDeficitSetRigidity
import GaloisForLFunctions.RHTower.MertensVonMangoldtEulerConstant
import GaloisForLFunctions.HTGeometry.VerticalStripContourShift
import GaloisForLFunctions.HTGeometry.DirichletBohrSpectrum
import Mathlib.NumberTheory.LSeries.Convolution

/-!
# Cross-Height Gaussian Dual-Dirichlet Mechanism, Sublinear Left-Strip Witnesses, Conductor-12 Twin Classification, and Unconditional Collapse of the Tempered Euler Firewall

Single-ordinate methods in the left critical strip `0 < Re s < 1 / 2` face two sharp structural
barriers:
* single-ordinate Euler–Knopp partial sums (`eulerEtaPartialSum`) require `O(|Im s|)` terms to
  control `(1 - 2^{1-s}) ζ(s)` because Pochhammer differences grow like `|Im s|^{M+1}`;
* the meromorphic tempered positive Euler-product model `posTruncatedZeta P₀ (β + i γ₀)`
  (`TheMeromorphicTemperedEulerFirewall`) has real nonnegative multiplicative Ramanujan-bounded
  coefficients `0 ≤ a(n) ≤ C_ε n^ε`, prime-power log-derivative `0 ≤ Λ̃ ≤ 2 Λ`, polynomial vertical
  bounds on `F` and `F⁻¹` right of `Θ`, and holomorphy across `Re s ≥ 1 / 2` (away from `s = 1`)
  whenever `β < 3 / 2 - Θ`, yet carries exact off-line zeros `{β ± i γ₀}`.

This module constructs and analyzes the cross-height Gaussian dual-Dirichlet mechanism that
simultaneously invokes:
1. **Unit-bounded Dirichlet coefficients** `‖a(n)‖ ≤ 1` (`n ≥ 1`),
2. **Global pole-freeness across the open left critical strip** `0 < Re s < 1 / 2`, and
3. **Functional-equation reflection `ξ_F(s) = ω ξ_F(1 - s)` across vertical heights** rather than at
   a single isolated ordinate,

establishing four unconditional theorem packages:

1. **Unconditional three-axis collapse of `posTruncatedZeta` without `RiemannHypothesis`
   (`zetaZeroAbscissa_le_sub_sevenEighths`, `not_summable_posTruncatedCoeff_prime_excess`,
   `infinite_primes_posTruncatedCoeff_gt_one`, `unbounded_squarefree_posTruncatedCoeff`,
   `exists_left_strip_pole_and_regular_reflection_above_height`,
   `posTruncatedZeta_antipodal_asymmetry_at_planted_zero`):**
   Unconditionally `Θ = zetaZeroAbscissa ≤ 20999 / 24000 < 1`. For every `β ∈ (0, 1)` and `γ₀ ≠ 0`,
   `posTruncatedCoeff P₀ β γ₀` exceeds `1` on infinitely many primes `p > P₀` and is unbounded on
   squarefree integers. Removing the `RiemannHypothesis` hypothesis of
   `exists_left_strip_pole_above_of_riemannHypothesis` via the asymptotic zero-free infimum `Θ_∞`,
   for every `β ∈ (Θ_∞, 1)`, `γ₀ ∈ ℝ`, `P₀ ∈ ℕ`, and `T ∈ ℝ`, `posTruncatedZeta P₀ (β + i γ₀)` has a
   genuine pole `s₀` inside `0 < Re s₀ < 1 - Θ_∞ ≤ 1 / 2` with `|Im s₀| > T` while remaining
   analytic and nonzero at `1 - s₀`, forcing `‖F(s) - X(s) F(1 - s)‖ → +∞` on `𝓝[≠] s₀` for every
   multiplier `X` continuous at `s₀`.

2. **General cross-height Gaussian dual-Dirichlet mechanism, `2r`-step `zetaChi` recurrence,
   sublinear `O(|Im s|^{1/2 + η})` left-strip witnesses across `Ω_open`, and quantitative failure on
   `posTruncatedZeta` (`UnitPoleFreeCrossHeightDatum`, `crossHeight_gaussian_two_tsum_eq`,
   `zetaChi_sub_two_mul`, `smoothAFEZetaDualCoefficientGeneral_eq_deep_even`,
   `exists_sublinear_crossHeight_witness_bound_on_remaining_strip`,
   `rh_iff_sublinear_crossHeight_witness_on_remaining_strip`,
   `crossHeight_gaussian_mechanism_fails_on_posTruncatedZeta`):**
   Every `(F, a, b, R, Q, ω)` satisfying `UnitPoleFreeCrossHeightDatum` admits an exact cross-height
   Gaussian two-series expansion throughout `0 < Re s < 1 / 2`. Shifting each reflected coefficient
   contour to `Re w = -2r` via `zetaChi(z - 2r) = (-1)^r (4π²)^{-r} (∏_{j=1}^{2r}(z - j)) zetaChi z`
   at balanced scale `x = √|Im s|` truncates both series at sublinear length
   `L = max 2 ⌈|Im s|^{1/2 + η}⌉₊` (`0 < η < 1 / 2`) with error `O_{r,η}(|Im s|^{-B})` across all
   `3001 / 24000 ≤ Re s < 1 / 2`, `184 < |Im s|` (extending beyond the corpus's `1 / 4 ≤ Re s < 1 / 2`
   and superlinear fixed-`x` truncation). By contrast, on `posTruncatedZeta`, any unit-bounded
   cross-height Gaussian series stays locally bounded on `0 < Re s < 1 / 2` while the representation
   error blows up to `+∞` at infinitely many unbounded-height left-strip poles.

3. **Conductor-`12` classification and critical-line purity of unit-bounded multiplicative twins
   (`unit_bounded_multiplicative_twin_classification`, `exists_even_conductor_four_unimodular_twin`):**
   Whereas bounded-coefficient multiplicative twins `zetaTwin p r` realize every off-line abscissa
   `b ∈ [Θ, 1)` (`TheMultiplicativeTwinsRealizeEveryAbscissaAboveTheZeros`), tightening `|a(n)| ≤ C`
   to `‖a(n)‖ ≤ 1` forces the conductor `Q` of any finite multiplicative twin `F(s) = ζ(s) D(s)` to
   be an integer dividing `12` (`Q ∈ {1, 2, 3, 4, 6, 12}`) and forces **every** zero of `D(s)` onto
   `Re s = 1 / 2` (`D(s) = 0 → s.re = 1 / 2`). At `Q = 4`, `(1 - 2^{1 - s} + 2^{1 - 2s}) ζ(s)` has
   strictly unimodular multiplicative coefficients `a(n) ∈ {-1, 1}`, global pole-freeness off `s = 1`,
   exact even completion reflection across all heights, and all twin zeros on `Re s = 1 / 2`.

4. **Sharp necessity of cross-height reflection over single-ordinate reflection on `Ω_open`
   (`exists_unit_bounded_poleFree_singleOrdinate_countermodel_on_remaining_strip`):**
   At every point `s₀` with `3001 / 24000 ≤ Re s₀ < 1 / 2`, an explicit `{2, 3}`-supported
   multiplicative Dirichlet series with `a(1) = 1`, `‖a(n)‖ ≤ 1`, global pole-freeness on `ℂ \ {1}`,
   and nonzero residue at `s = 1` vanishes at both `s₀` and `1 - s₀`, satisfying single-point
   reflection `ξ_F(s₀) = ξ_F(1 - s₀) = 0` while violating nonvanishing on `Ω_open`.
-/

noncomputable section

open Complex Filter Set MeasureTheory intervalIntegral
open scoped BigOperators ComplexConjugate Topology ArithmeticFunction

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

open GaloisForLFunctions.ArithmeticPositiveDuality
open _root_.RHTower

/-! ### Part 1: Unconditional Three-Axis Collapse of `posTruncatedZeta` Without `RiemannHypothesis` -/

/-- **Unconditional sub-`7/8` bound on `zetaZeroAbscissa`:** reflecting the unconditional left-strip
zero-free region `0 < Re s < 3001 / 24000` (`riemannZeta_ne_zero_of_re_lt_sub_one_eighth`) bounds
`zetaZeroAbscissa ≤ 20999 / 24000 < 1` without case-splitting on `AsymptoticAbscissaLaw`. -/
theorem zetaZeroAbscissa_le_sub_sevenEighths :
    zetaZeroAbscissa ≤ 20999 / 24000 := by
  refine csSup_le zetaZeroReSet_nonempty ?_
  rintro x ⟨ρ, hζ, rfl⟩
  by_contra hgt
  push Not at hgt
  have h0 : 0 < ρ.re := by linarith
  have h1 : ρ.re < 1 := not_le.mp fun hge => riemannZeta_ne_zero_of_one_le_re hge hζ
  have h1ρ_pos : 0 < (1 - ρ).re := by simp; linarith
  have h1ρ_lt : (1 - ρ).re < 3001 / 24000 := by simp; linarith
  have hζ1 : riemannZeta (1 - ρ) = 0 :=
    riemannZeta_one_sub_eq_zero_of_mem_openStrip hζ h0 h1
  exact MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_ne_zero_of_re_lt_sub_one_eighth
    h1ρ_pos h1ρ_lt hζ1

/-- `zetaZeroAbscissa < 1` holds unconditionally. -/
theorem zetaZeroAbscissa_lt_one_unconditional : zetaZeroAbscissa < 1 :=
  zetaZeroAbscissa_le_sub_sevenEighths.trans_lt (by norm_num)

private theorem two_mul_max_neg_cos_ge (θ : ℝ) :
    1 / 2 + (1 / 2 : ℝ) * Real.cos (2 * θ) - Real.cos θ ≤ 2 * max 0 (-Real.cos θ) := by
  set u : ℝ := Real.cos θ
  have hu_lo : -1 ≤ u := Real.neg_one_le_cos θ
  have hu_hi : u ≤ 1 := Real.cos_le_one θ
  have hcos2 : Real.cos (2 * θ) = 2 * u ^ 2 - 1 := Real.cos_two_mul θ
  rw [hcos2]
  rcases le_or_gt u 0 with hneg | hpos
  · have hmax : max (0 : ℝ) (-u) = -u := max_eq_right (by linarith)
    rw [hmax]
    nlinarith
  · have hmax : max (0 : ℝ) (-u) = 0 := max_eq_left (by linarith)
    rw [hmax]
    nlinarith

private theorem log_mul_rpow_neg_le_div_mul_rpow {x β σ : ℝ}
    (hx : 1 ≤ x) (hβ : 0 < β) (hσ : 1 < σ) :
    Real.log x * x ^ (-σ) ≤ (1 / β) * x ^ (β - 1) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hlog : Real.log x ≤ x ^ β / β := by
    have h1 : β * Real.log x = Real.log (x ^ β) := by
      rw [Real.log_rpow hx0]
    have h2 : Real.log (x ^ β) ≤ x ^ β - 1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx0 β)
    rw [le_div_iff₀ hβ, mul_comm]
    linarith
  have hrpow : x ^ (-σ) ≤ x ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hlog_nn : 0 ≤ Real.log x := Real.log_nonneg hx
  calc Real.log x * x ^ (-σ)
      ≤ (x ^ β / β) * x ^ (-1 : ℝ) :=
        mul_le_mul hlog hrpow (Real.rpow_nonneg hx0.le _) (div_nonneg (Real.rpow_nonneg hx0.le _) hβ.le)
    _ = (1 / β) * (x ^ β * x ^ (-1 : ℝ)) := by ring
    _ = (1 / β) * x ^ (β - 1) := by
        rw [← Real.rpow_add hx0, sub_eq_add_neg]

private theorem re_lseries_vonMangoldt_term {σ t : ℝ} (n : ℕ) (hn : 1 ≤ n) :
    (LSeries.term (fun m => (Λ m : ℂ)) ((σ : ℂ) + (t : ℂ) * I) n).re =
      Λ n * Real.cos (t * Real.log n) * (n : ℝ) ^ (-σ) := by
  have hn0 : n ≠ 0 := by omega
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [LSeries.term_of_ne_zero hn0, div_eq_mul_inv, ← Complex.cpow_neg,
    ← Complex.ofReal_natCast n, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hnpos.ne'),
    ← Complex.ofReal_log hnpos.le]
  have hexp' : ((Real.log n : ℝ) : ℂ) * -((σ : ℂ) + (t : ℂ) * I) =
      ((-σ * Real.log n : ℝ) : ℂ) + ((-t * Real.log n : ℝ) : ℂ) * I := by push_cast; ring
  rw [hexp', Complex.exp_add_mul_I, ← Complex.ofReal_exp, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hre : ((Λ n : ℂ) * (((Real.exp (-σ * Real.log n) : ℝ) : ℂ) *
      (((Real.cos (-t * Real.log n) : ℝ) : ℂ) + ((Real.sin (-t * Real.log n) : ℝ) : ℂ) * I))).re =
      Λ n * Real.exp (-σ * Real.log n) * Real.cos (-t * Real.log n) := by
    simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero]
    ring
  rw [hre, show -t * Real.log n = -(t * Real.log n) by ring, Real.cos_neg,
    Real.rpow_def_of_pos hnpos, show Real.log n * -σ = -σ * Real.log n by ring]
  ring

/-- **Divergence of the prime excess sum of `posTruncatedCoeff`:** for every `0 < β < 1`, `γ₀ ≠ 0`,
and `P₀ : ℕ`, the positive prime excesses `max 0 (posTruncatedCoeff P₀ β γ₀ p - 1)` over primes
`p > P₀` have divergent infinite sum. -/
theorem not_summable_posTruncatedCoeff_prime_excess (P₀ : ℕ) {β γ₀ : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hγ₀ : γ₀ ≠ 0) :
    ¬ Summable (fun n : ℕ =>
      if n.Prime ∧ P₀ < n then max 0 (posTruncatedCoeff P₀ β γ₀ n - 1) else 0) := by
  intro hsum
  set M_ex : ℝ := ∑' n : ℕ,
    if n.Prime ∧ P₀ < n then max 0 (posTruncatedCoeff P₀ β γ₀ n - 1) else 0
  have hM_nn : 0 ≤ M_ex := tsum_nonneg fun n => by split_ifs <;> positivity
  -- Non-prime and `≤ P₀` von Mangoldt terms are uniformly bounded across all `σ > 1`.
  have hnonprime_sum : Summable (fun n : ℕ => if n.Prime then (0 : ℝ) else Λ n / n) :=
    _root_.RHTower.WeilPrimeDeficit.summable_nonprime_vonMangoldt_div
  set C_np : ℝ := ∑' n : ℕ, if n.Prime then (0 : ℝ) else Λ n / n
  set C_small : ℝ := ∑ n ∈ Finset.range (P₀ + 1), Λ n
  -- Continuity of `-logDeriv riemannZeta` on `[1, 2]` at nonzero ordinates `γ₀` and `2 * γ₀`.
  have hcont_shift : ∀ t : ℝ, t ≠ 0 →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ σ ∈ Icc (1 : ℝ) 2,
        ‖-logDeriv riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ B := by
    intro t ht
    have hcont : ContinuousOn (fun σ : ℝ => -logDeriv riemannZeta ((σ : ℂ) + (t : ℂ) * I))
        (Icc 1 2) := by
      intro σ hσ
      have hne1 : ((σ : ℂ) + (t : ℂ) * I) ≠ 1 := by
        intro heq
        have him := congrArg Complex.im heq
        simp at him
        exact ht him
      have hζ_ne : riemannZeta ((σ : ℂ) + (t : ℂ) * I) ≠ 0 :=
        riemannZeta_ne_zero_of_one_le_re (by simp; exact hσ.1)
      have hd : DifferentiableAt ℂ riemannZeta ((σ : ℂ) + (t : ℂ) * I) :=
        differentiableAt_riemannZeta hne1
      have h_ana : AnalyticAt ℂ riemannZeta ((σ : ℂ) + (t : ℂ) * I) :=
        analyticOn_riemannZeta _ (Set.mem_compl_singleton_iff.mpr hne1)
      have hld_cont : ContinuousAt (fun z : ℂ => -logDeriv riemannZeta z) ((σ : ℂ) + (t : ℂ) * I) := by
        have heq : (fun z : ℂ => -logDeriv riemannZeta z) =
            fun z => -(deriv riemannZeta z / riemannZeta z) := by
          funext z; simp [logDeriv_apply]
        rw [heq]
        exact (h_ana.deriv.continuousAt.div hd.continuousAt hζ_ne).neg
      exact (ContinuousAt.comp (f := fun u : ℝ => (u : ℂ) + (t : ℂ) * I) hld_cont
        (by fun_prop)).continuousWithinAt
    obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
    exact ⟨max B 0, le_max_right _ _, fun σ hσ => (hB σ hσ).trans (le_max_left _ _)⟩
  obtain ⟨B₁, hB₁, hb₁⟩ := hcont_shift γ₀ hγ₀
  obtain ⟨B₂, hB₂, hb₂⟩ := hcont_shift (2 * γ₀) (mul_ne_zero two_ne_zero hγ₀)
  -- For every `σ ∈ (1, 2]`, relate `(1/2) Re(-ζ'/ζ(σ))` to `M_ex / β + C_small + C_np + B₁ + B₂`.
  have hub_real : ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      (1 / 2 : ℝ) * (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re ≤
        M_ex / β + 2 * C_small + 2 * C_np + B₁ + (1 / 2) * B₂ := by
    intro σ hσ1 hσ2
    have hL_re : ∀ t : ℝ,
        (-logDeriv riemannZeta ((σ : ℂ) + (t : ℂ) * I)).re =
          ∑' n : ℕ, (LSeries.term (fun m => (Λ m : ℂ)) ((σ : ℂ) + (t : ℂ) * I) n).re := by
      intro t
      have hw : 1 < (((σ : ℂ) + (t : ℂ) * I)).re := by simp; exact hσ1
      have hsumL : Summable (LSeries.term (fun m => (Λ m : ℂ)) ((σ : ℂ) + (t : ℂ) * I)) :=
        ArithmeticFunction.LSeriesSummable_vonMangoldt hw
      have hld : -logDeriv riemannZeta ((σ : ℂ) + (t : ℂ) * I) =
          LSeries (fun m => (Λ m : ℂ)) ((σ : ℂ) + (t : ℂ) * I) := by
        rw [logDeriv_apply, ← neg_div,
          ← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hw]
      rw [hld, LSeries, ← Complex.re_tsum hsumL]
    have hsum_t : ∀ t : ℝ, Summable (fun n : ℕ =>
        (LSeries.term (fun m => (Λ m : ℂ)) ((σ : ℂ) + (t : ℂ) * I) n).re) := fun t => by
      have hw : 1 < (((σ : ℂ) + (t : ℂ) * I)).re := by simp; exact hσ1
      exact Complex.reCLM.summable (ArithmeticFunction.LSeriesSummable_vonMangoldt hw)
    set f₀ := fun n : ℕ => (LSeries.term (fun m => (Λ m : ℂ)) ((σ : ℂ) + ((0 : ℝ) : ℂ) * I) n).re
    set f₁ := fun n : ℕ => (LSeries.term (fun m => (Λ m : ℂ)) ((σ : ℂ) + (γ₀ : ℂ) * I) n).re
    set f₂ := fun n : ℕ => (LSeries.term (fun m => (Λ m : ℂ)) ((σ : ℂ) + ((2 * γ₀ : ℝ) : ℂ) * I) n).re
    have hcomb_eq :
        (1 / 2 : ℝ) * (-logDeriv riemannZeta (σ : ℂ)).re +
          (1 / 2 : ℝ) * (-logDeriv riemannZeta ((σ : ℂ) + ((2 * γ₀ : ℝ) : ℂ) * I)).re -
          (-logDeriv riemannZeta ((σ : ℂ) + (γ₀ : ℂ) * I)).re =
        ∑' n : ℕ, ((1 / 2 : ℝ) * f₀ n + (1 / 2 : ℝ) * f₂ n - f₁ n) := by
      have hL0 : (-logDeriv riemannZeta (σ : ℂ)).re = ∑' n : ℕ, f₀ n := by
        simpa [f₀] using hL_re 0
      rw [hL0, hL_re (2 * γ₀), hL_re γ₀,
        ← tsum_mul_left, ← tsum_mul_left,
        ← ((hsum_t 0).mul_left (1 / 2)).tsum_add ((hsum_t (2 * γ₀)).mul_left (1 / 2)),
        ← (((hsum_t 0).mul_left (1 / 2)).add ((hsum_t (2 * γ₀)).mul_left (1 / 2))).tsum_sub (hsum_t γ₀)]
    -- Pointwise majorant on each `n : ℕ`
    set maj : ℕ → ℝ := fun n =>
      (1 / β) * (if n.Prime ∧ P₀ < n then max 0 (posTruncatedCoeff P₀ β γ₀ n - 1) else 0) +
      2 * (if n ≤ P₀ then Λ n else 0) +
      2 * (if n.Prime then 0 else Λ n / n)
    have hsum_small : Summable (fun n : ℕ => if n ≤ P₀ then Λ n else 0) :=
      summable_of_ne_finset_zero (s := Finset.range (P₀ + 1)) fun n hn => by
        rw [Finset.mem_range, not_lt] at hn
        exact if_neg (by omega)
    have hsum_maj : Summable maj :=
      ((hsum.mul_left (1 / β)).add (hsum_small.mul_left 2)).add (hnonprime_sum.mul_left 2)
    have hpt : ∀ n : ℕ, (1 / 2 : ℝ) * f₀ n + (1 / 2 : ℝ) * f₂ n - f₁ n ≤ maj n := by
      intro n
      rcases eq_or_ne n 0 with rfl | hn0
      · dsimp only [f₀, f₁, f₂, maj]
        simp [ArithmeticFunction.map_zero]
      · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
        have hr0 := re_lseries_vonMangoldt_term (σ := σ) (t := 0) n hn1
        have hr1 := re_lseries_vonMangoldt_term (σ := σ) (t := γ₀) n hn1
        have hr2 := re_lseries_vonMangoldt_term (σ := σ) (t := 2 * γ₀) n hn1
        change (1 / 2 : ℝ) * (LSeries.term _ _ n).re + (1 / 2 : ℝ) * (LSeries.term _ _ n).re -
          (LSeries.term _ _ n).re ≤ maj n
        rw [hr0, hr1, hr2, zero_mul, Real.cos_zero, mul_one]
        have htrig : (1 / 2 : ℝ) * (Λ n * (n : ℝ) ^ (-σ)) +
            (1 / 2 : ℝ) * (Λ n * Real.cos (2 * γ₀ * Real.log n) * (n : ℝ) ^ (-σ)) -
            Λ n * Real.cos (γ₀ * Real.log n) * (n : ℝ) ^ (-σ) =
            (1 / 2 + (1 / 2 : ℝ) * Real.cos (2 * (γ₀ * Real.log n)) -
              Real.cos (γ₀ * Real.log n)) * (Λ n * (n : ℝ) ^ (-σ)) := by
          rw [mul_assoc 2 γ₀ (Real.log n)]
          ring
        rw [htrig]
        have hΛ_nn : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
        have hrp_nn : 0 ≤ (n : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
        have hcoef_le2 : 1 / 2 + (1 / 2 : ℝ) * Real.cos (2 * (γ₀ * Real.log n)) -
            Real.cos (γ₀ * Real.log n) ≤ 2 := by
          linarith [Real.cos_le_one (2 * (γ₀ * Real.log n)), Real.neg_one_le_cos (γ₀ * Real.log n)]
        by_cases hp : n.Prime
        · by_cases hpP : P₀ < n
          · have hnot_le : ¬(n ≤ P₀) := not_le.mpr hpP
            have hcoeff_eq : posTruncatedCoeff P₀ β γ₀ n - 1 =
                -2 * (n : ℝ) ^ (β - 1) * Real.cos (γ₀ * Real.log n) := by
              have h1 := posTruncatedCoeff_prime_pow P₀ β γ₀ hp (k := 1)
              rw [pow_one] at h1
              rw [h1]
              unfold posLocalCoeff
              rw [if_neg one_ne_zero, if_neg hnot_le, if_pos rfl]
              ring
            have hmax_eq : max 0 (posTruncatedCoeff P₀ β γ₀ n - 1) =
                2 * (n : ℝ) ^ (β - 1) * max 0 (-Real.cos (γ₀ * Real.log n)) := by
              rw [hcoeff_eq, show -2 * (n : ℝ) ^ (β - 1) * Real.cos (γ₀ * Real.log n) =
                (2 * (n : ℝ) ^ (β - 1)) * (-Real.cos (γ₀ * Real.log n)) by ring,
                mul_max_of_nonneg (0 : ℝ) (-Real.cos (γ₀ * Real.log n)) (by positivity),
                mul_zero]
            have hcos_bd := two_mul_max_neg_cos_ge (γ₀ * Real.log n)
            have hlog_bd := log_mul_rpow_neg_le_div_mul_rpow
              (by exact_mod_cast hp.one_lt.le : (1 : ℝ) ≤ n) hβ0 hσ1
            have hΛ_p : Λ n = Real.log n := ArithmeticFunction.vonMangoldt_apply_prime hp
            dsimp only [maj]
            rw [if_pos ⟨hp, hpP⟩, if_neg hnot_le, if_pos hp, hmax_eq, hΛ_p]
            have h1 : (1 / 2 + (1 / 2 : ℝ) * Real.cos (2 * (γ₀ * Real.log n)) -
                Real.cos (γ₀ * Real.log n)) * (Real.log n * (n : ℝ) ^ (-σ)) ≤
                (2 * max 0 (-Real.cos (γ₀ * Real.log n))) * ((1 / β) * (n : ℝ) ^ (β - 1)) :=
              mul_le_mul hcos_bd hlog_bd (mul_nonneg (Real.log_nonneg (by exact_mod_cast hp.one_lt.le)) hrp_nn)
                (by positivity)
            linarith
          · have hleP : n ≤ P₀ := not_lt.mp hpP
            have hrp_le1 : (n : ℝ) ^ (-σ) ≤ 1 :=
              Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn1) (by linarith)
            dsimp only [maj]
            rw [if_neg (fun h => hpP h.2), if_pos hleP, if_pos hp]
            have hprod_le : Λ n * (n : ℝ) ^ (-σ) ≤ Λ n :=
              mul_le_of_le_one_right hΛ_nn hrp_le1
            have h1 : (1 / 2 + (1 / 2 : ℝ) * Real.cos (2 * (γ₀ * Real.log n)) -
                Real.cos (γ₀ * Real.log n)) * (Λ n * (n : ℝ) ^ (-σ)) ≤ 2 * Λ n := by
              calc (1 / 2 + (1 / 2 : ℝ) * Real.cos (2 * (γ₀ * Real.log n)) -
                    Real.cos (γ₀ * Real.log n)) * (Λ n * (n : ℝ) ^ (-σ))
                  ≤ 2 * (Λ n * (n : ℝ) ^ (-σ)) :=
                    mul_le_mul_of_nonneg_right hcoef_le2 (mul_nonneg hΛ_nn hrp_nn)
                _ ≤ 2 * Λ n := mul_le_mul_of_nonneg_left hprod_le two_pos.le
            linarith
        · have hrp_le_inv : (n : ℝ) ^ (-σ) ≤ (n : ℝ)⁻¹ := by
            rw [← Real.rpow_neg_one]
            exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) (by linarith)
          dsimp only [maj]
          rw [if_neg (fun h => hp h.1), if_neg hp]
          have hsmall_nn : 0 ≤ (if n ≤ P₀ then Λ n else 0) := by split_ifs <;> positivity
          have hdiv_eq : Λ n / (n : ℝ) = Λ n * (n : ℝ)⁻¹ := div_eq_mul_inv _ _
          rw [hdiv_eq]
          have hprod_le : Λ n * (n : ℝ) ^ (-σ) ≤ Λ n * (n : ℝ)⁻¹ :=
            mul_le_mul_of_nonneg_left hrp_le_inv hΛ_nn
          have h1 : (1 / 2 + (1 / 2 : ℝ) * Real.cos (2 * (γ₀ * Real.log n)) -
              Real.cos (γ₀ * Real.log n)) * (Λ n * (n : ℝ) ^ (-σ)) ≤ 2 * (Λ n * (n : ℝ)⁻¹) := by
            calc (1 / 2 + (1 / 2 : ℝ) * Real.cos (2 * (γ₀ * Real.log n)) -
                  Real.cos (γ₀ * Real.log n)) * (Λ n * (n : ℝ) ^ (-σ))
                ≤ 2 * (Λ n * (n : ℝ) ^ (-σ)) :=
                  mul_le_mul_of_nonneg_right hcoef_le2 (mul_nonneg hΛ_nn hrp_nn)
              _ ≤ 2 * (Λ n * (n : ℝ)⁻¹) := mul_le_mul_of_nonneg_left hprod_le two_pos.le
          linarith
    have hsum_lhs : Summable (fun n : ℕ => (1 / 2 : ℝ) * f₀ n + (1 / 2 : ℝ) * f₂ n - f₁ n) :=
      (((hsum_t 0).mul_left (1 / 2)).add ((hsum_t (2 * γ₀)).mul_left (1 / 2))).sub (hsum_t γ₀)
    have htsum_le := hsum_lhs.tsum_le_tsum hpt hsum_maj
    have hmaj_eval : (∑' n : ℕ, maj n) ≤ M_ex / β + 2 * C_small + 2 * C_np := by
      dsimp only [maj]
      rw [(((hsum.mul_left (1 / β)).add (hsum_small.mul_left 2)).tsum_add (hnonprime_sum.mul_left 2)),
        (hsum.mul_left (1 / β)).tsum_add (hsum_small.mul_left 2),
        tsum_mul_left, tsum_mul_left, tsum_mul_left]
      have hsm_eq : (∑' n : ℕ, if n ≤ P₀ then Λ n else 0) = C_small := by
        rw [tsum_eq_sum (s := Finset.range (P₀ + 1)) fun n hn => by
          rw [Finset.mem_range, not_lt] at hn; exact if_neg (by omega)]
        exact Finset.sum_congr rfl fun n hn => if_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))
      rw [hsm_eq]
      dsimp only [M_ex, C_np]
      exact (by ring : (1 / β) * M_ex + 2 * C_small + 2 * C_np =
        M_ex / β + 2 * C_small + 2 * C_np).le
    -- Bound the shifted `-logDeriv` terms on `σ ∈ [1, 2]`.
    have hmem : σ ∈ Icc (1 : ℝ) 2 := ⟨hσ1.le, hσ2⟩
    have hre1_bd : |(-logDeriv riemannZeta ((σ : ℂ) + (γ₀ : ℂ) * I)).re| ≤ B₁ :=
      (Complex.abs_re_le_norm _).trans (hb₁ σ hmem)
    have hre2_bd : |(-logDeriv riemannZeta ((σ : ℂ) + ((2 * γ₀ : ℝ) : ℂ) * I)).re| ≤ B₂ := by
      have hcast : ((σ : ℂ) + ((2 * γ₀ : ℝ) : ℂ) * I) = (σ : ℂ) + (2 * γ₀ : ℝ) * I := rfl
      exact (Complex.abs_re_le_norm _).trans (by simpa using hb₂ σ hmem)
    have hld0 : (-logDeriv riemannZeta (σ : ℂ)).re =
        (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re := by
      rw [logDeriv_apply, ← neg_div]
    rw [← hld0]
    linarith [hcomb_eq.le.trans (htsum_le.trans hmaj_eval), abs_le.mp hre1_bd, abs_le.mp hre2_bd]
  -- Contradict `(σ - 1)⁻¹ → +∞` as `σ ↓ 1⁺` via `tendsto_neg_logDeriv_riemannZeta_sub_one_div_real`.
  set K_tot : ℝ := M_ex / β + 2 * C_small + 2 * C_np + B₁ + (1 / 2) * B₂
  have hlim := tendsto_neg_logDeriv_riemannZeta_sub_one_div_real
  have hre_lim : Tendsto (fun σ : ℝ =>
      (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ) - ((σ : ℂ) - 1)⁻¹).re)
      (𝓝[>] 1) (𝓝 (-Real.eulerMascheroniConstant)) := by
    have h := (Complex.continuous_re.tendsto _).comp hlim
    simpa only [Function.comp_def, Complex.neg_re, Complex.ofReal_re, one_div] using h
  have hev1 : ∀ᶠ σ : ℝ in 𝓝[>] 1,
      -Real.eulerMascheroniConstant - 1 <
        (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ) - ((σ : ℂ) - 1)⁻¹).re :=
    hre_lim.eventually (Ioi_mem_nhds (by linarith))
  set δ : ℝ := min 1 (1 / (max 1 (2 * K_tot + |Real.eulerMascheroniConstant| + 4)))
  have hδ_pos : 0 < δ := by dsimp only [δ]; positivity
  have hev2 : ∀ᶠ σ : ℝ in 𝓝[>] 1, σ < 1 + δ :=
    tendsto_nhdsWithin_iff.mp tendsto_id |>.1.eventually (Iio_mem_nhds (by linarith))
  obtain ⟨σ₀, ⟨hgt_lim, hlt_δ⟩, hgt1⟩ := (hev1.and hev2 |>.and self_mem_nhdsWithin).exists
  have hσ1 : 1 < σ₀ := hgt1
  have hσ2 : σ₀ ≤ 2 := by
    have hδ1 : δ ≤ 1 := min_le_left _ _
    linarith
  have hinv_re : (((σ₀ : ℂ) - 1)⁻¹).re = 1 / (σ₀ - 1) := by
    have hsub : (σ₀ : ℂ) - 1 = ((σ₀ - 1 : ℝ) : ℂ) := by push_cast; ring
    rw [hsub, ← Complex.ofReal_inv, Complex.ofReal_re, one_div]
  rw [Complex.sub_re, hinv_re] at hgt_lim
  have hσ_sub_pos : 0 < σ₀ - 1 := by linarith
  have hσ_sub_lt : σ₀ - 1 < 1 / (max 1 (2 * K_tot + |Real.eulerMascheroniConstant| + 4)) :=
    lt_of_lt_of_le (by linarith) (min_le_right _ _)
  have hinv_gt : max 1 (2 * K_tot + |Real.eulerMascheroniConstant| + 4) < 1 / (σ₀ - 1) := by
    rw [lt_one_div (by positivity) hσ_sub_pos]
    exact hσ_sub_lt
  have hbound : (1 / 2 : ℝ) * (-deriv riemannZeta (σ₀ : ℂ) / riemannZeta (σ₀ : ℂ)).re ≤ K_tot :=
    hub_real σ₀ hσ1 hσ2
  have hγ_abs : -|Real.eulerMascheroniConstant| ≤ -Real.eulerMascheroniConstant :=
    neg_le_neg (le_abs_self _)
  have hmax_K : 2 * K_tot + |Real.eulerMascheroniConstant| + 4 ≤
      max 1 (2 * K_tot + |Real.eulerMascheroniConstant| + 4) := le_max_right _ _
  linarith only [hgt_lim, hinv_gt, hbound, hγ_abs, hmax_K]

/-- **Infinitely many primes exceed the unit cap on `posTruncatedZeta`:** for every `0 < β < 1`,
`γ₀ ≠ 0`, and `P₀ : ℕ`, infinitely many rational primes `p > P₀` satisfy
`1 < posTruncatedCoeff P₀ β γ₀ p`. -/
theorem infinite_primes_posTruncatedCoeff_gt_one (P₀ : ℕ) {β γ₀ : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hγ₀ : γ₀ ≠ 0) :
    {p : ℕ | p.Prime ∧ P₀ < p ∧ 1 < posTruncatedCoeff P₀ β γ₀ p}.Infinite := by
  intro hfin
  refine not_summable_posTruncatedCoeff_prime_excess P₀ hβ0 hβ1 hγ₀ ?_
  refine summable_of_ne_finset_zero (s := hfin.toFinset) fun n hn => ?_
  rw [Set.Finite.mem_toFinset] at hn
  by_cases hp : n.Prime ∧ P₀ < n
  · rw [if_pos hp, max_eq_left_iff]
    have hle : posTruncatedCoeff P₀ β γ₀ n ≤ 1 :=
      not_lt.mp fun hgt => hn ⟨hp.1, hp.2, hgt⟩
    linarith
  · exact if_neg hp

private theorem prod_one_add_ge_one_add_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    1 + ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 + f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have hfa : 0 ≤ f a := hf a (Finset.mem_insert_self a s)
    have hsum_nn : 0 ≤ ∑ i ∈ s, f i :=
      Finset.sum_nonneg fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hih := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    nlinarith [mul_nonneg hfa hsum_nn]

/-- **Squarefree unboundedness of `posTruncatedCoeff`:** despite satisfying the Ramanujan bound
`0 ≤ a(n) ≤ C_ε n^ε` for every `ε > 0`, `posTruncatedCoeff P₀ β γ₀` is unbounded on squarefree
integers coprime to `∏_{p ≤ P₀} p` for every `0 < β < 1` and `γ₀ ≠ 0`. In particular, it violates
`∀ n ≥ 1, |a(n)| ≤ 1` and every uniform bound `∀ n ≥ 1, |a(n)| ≤ B`. -/
theorem unbounded_squarefree_posTruncatedCoeff (P₀ : ℕ) {β γ₀ : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hγ₀ : γ₀ ≠ 0) (B : ℝ) :
    ∃ n : ℕ, 1 ≤ n ∧ Squarefree n ∧ B < posTruncatedCoeff P₀ β γ₀ n := by
  classical
  set g : ℕ → ℝ := fun n =>
    if n.Prime ∧ P₀ < n then max 0 (posTruncatedCoeff P₀ β γ₀ n - 1) else 0
  have hg_nn : ∀ n : ℕ, 0 ≤ g n := fun n => by dsimp only [g]; split_ifs <;> positivity
  have hnot_sum : ¬ Summable g := not_summable_posTruncatedCoeff_prime_excess P₀ hβ0 hβ1 hγ₀
  have hex_N : ∃ N : ℕ, max B 0 < ∑ n ∈ Finset.range N, g n := by
    by_contra! hle
    exact hnot_sum (summable_of_sum_range_le hg_nn hle)
  obtain ⟨N, hN⟩ := hex_N
  set S : Finset ℕ := (Finset.range N).filter
    (fun p => p.Prime ∧ P₀ < p ∧ 1 < posTruncatedCoeff P₀ β γ₀ p)
  have hsum_eq : (∑ n ∈ Finset.range N, g n) =
      ∑ p ∈ S, (posTruncatedCoeff P₀ β γ₀ p - 1) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    dsimp only [g]
    by_cases hp : n.Prime ∧ P₀ < n
    · rw [if_pos hp]
      by_cases hgt : 1 < posTruncatedCoeff P₀ β γ₀ n
      · rw [if_pos ⟨hp.1, hp.2, hgt⟩, max_eq_right (by linarith)]
      · rw [if_neg (fun h => hgt h.2.2), max_eq_left (by linarith [not_lt.mp hgt])]
    · rw [if_neg hp, if_neg (fun h => hp ⟨h.1, h.2.1⟩)]
  set m : ℕ := ∏ p ∈ S, p
  have hm_pos : 0 < m := Finset.prod_pos fun p hp => (Finset.mem_filter.mp hp).2.1.pos
  have hsqf_gen : ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) → Squarefree (∏ p ∈ s, p) := by
    intro s hs
    induction s using Finset.induction_on with
    | empty => simp
    | insert q t hq ih =>
      rw [Finset.prod_insert hq]
      have hqp : q.Prime := hs q (Finset.mem_insert_self q t)
      have hcop : Nat.Coprime q (∏ p ∈ t, p) :=
        Nat.Coprime.prod_right fun p hp =>
          (Nat.coprime_primes hqp (hs p (Finset.mem_insert_of_mem hp))).mpr
            fun heq => hq (heq ▸ hp)
      exact (Nat.squarefree_mul hcop).mpr
        ⟨hqp.squarefree, ih fun p hp => hs p (Finset.mem_insert_of_mem hp)⟩
  have hm_sqf : Squarefree m :=
    hsqf_gen S fun p hp => (Finset.mem_filter.mp hp).2.1
  have ha_mul_gen : ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) →
      posTruncatedCoeff P₀ β γ₀ (∏ p ∈ s, p) = ∏ p ∈ s, posTruncatedCoeff P₀ β γ₀ p := by
    intro s hs
    induction s using Finset.induction_on with
    | empty => simp [posTruncatedCoeff_one]
    | insert q t hq ih =>
      rw [Finset.prod_insert hq, Finset.prod_insert hq]
      have hqp : q.Prime := hs q (Finset.mem_insert_self q t)
      have hcop : Nat.Coprime q (∏ p ∈ t, p) :=
        Nat.Coprime.prod_right fun p hp =>
          (Nat.coprime_primes hqp (hs p (Finset.mem_insert_of_mem hp))).mpr
            fun heq => hq (heq ▸ hp)
      rw [(isMultiplicative_posTruncatedCoeff P₀ β γ₀).2 hcop,
        ih fun p hp => hs p (Finset.mem_insert_of_mem hp)]
  have ha_mul : posTruncatedCoeff P₀ β γ₀ m = ∏ p ∈ S, posTruncatedCoeff P₀ β γ₀ p :=
    ha_mul_gen S fun p hp => (Finset.mem_filter.mp hp).2.1
  have hprod_ge : 1 + ∑ p ∈ S, (posTruncatedCoeff P₀ β γ₀ p - 1) ≤
      ∏ p ∈ S, posTruncatedCoeff P₀ β γ₀ p := by
    have h1 := prod_one_add_ge_one_add_sum S
      (fun p => posTruncatedCoeff P₀ β γ₀ p - 1)
      (fun p hp => by linarith [(Finset.mem_filter.mp hp).2.2.2])
    refine h1.trans_eq (Finset.prod_congr rfl fun p _ => by ring)
  refine ⟨m, hm_pos, hm_sqf, ?_⟩
  rw [ha_mul]
  linarith [le_max_left B 0, hN, hsum_eq, hprod_ge]

/-- Asymptotic high-ordinate zero-free abscissa `Θ_∞ = inf {σ ∈ [1/2, 1] | ∃ T₀ > 0, ...}` of `ζ`. -/
def zetaAsympZeroSet : Set ℝ :=
  {σ : ℝ | 1 / 2 ≤ σ ∧ σ ≤ 1 ∧
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ z : ℂ, σ < z.re → T₀ < |z.im| → riemannZeta z ≠ 0}

/-- Infimal high-ordinate zero-free abscissa `Θ_∞ ∈ [1/2, zetaZeroAbscissa]` of `riemannZeta`. -/
def zetaAsympZeroAbscissa : ℝ := sInf zetaAsympZeroSet

theorem zetaAsympZeroSet_nonempty : zetaAsympZeroSet.Nonempty :=
  ⟨1, by norm_num, le_rfl, 1, zero_lt_one,
    fun _ hz _ => riemannZeta_ne_zero_of_one_lt_re hz⟩

theorem zetaAsympZeroSet_bddBelow : BddBelow zetaAsympZeroSet :=
  ⟨1 / 2, fun _ h => h.1⟩

theorem half_le_zetaAsympZeroAbscissa : 1 / 2 ≤ zetaAsympZeroAbscissa :=
  le_csInf zetaAsympZeroSet_nonempty fun _ h => h.1

theorem zetaAsympZeroAbscissa_le_zetaZeroAbscissa :
    zetaAsympZeroAbscissa ≤ zetaZeroAbscissa := by
  have hΘ_half : 1 / 2 ≤ zetaZeroAbscissa := half_le_zetaZeroAbscissa
  have hΘ_one : zetaZeroAbscissa ≤ 1 := zetaZeroAbscissa_le_one
  refine csInf_le zetaAsympZeroSet_bddBelow ⟨hΘ_half, hΘ_one, 1, zero_lt_one, ?_⟩
  intro z hz _
  exact riemannZeta_ne_zero_of_zetaZeroAbscissa_lt hz

private theorem differentiableAt_posFiniteFactor_of_re_neg (P₀ : ℕ) (ρ₀ s : ℂ)
    (h1 : (ρ₀ - 1 - s).re < 0) (h2 : (conj ρ₀ - 1 - s).re < 0) :
    DifferentiableAt ℂ (posFiniteFactor P₀ ρ₀) s := by
  have hd_q : ∀ (q : Nat.Primes) {c : ℂ}, (c - s).re < 0 →
      DifferentiableAt ℂ (fun z : ℂ => (1 - ((q : ℕ) : ℂ) ^ (c - z))⁻¹) s := by
    intro q c hc
    have hp0 : ((q : ℕ) : ℂ) ≠ 0 := by exact_mod_cast q.prop.ne_zero
    have heq : (fun z : ℂ => 1 - ((q : ℕ) : ℂ) ^ (c - z)) =
        fun z : ℂ => 1 - Complex.exp (Complex.log ((q : ℕ) : ℂ) * (c - z)) := by
      funext z; rw [Complex.cpow_def_of_ne_zero hp0]
    have hd_sub : DifferentiableAt ℂ (fun z : ℂ => 1 - ((q : ℕ) : ℂ) ^ (c - z)) s := by
      rw [heq]
      exact differentiableAt_const _ |>.sub
        ((differentiableAt_const _ |>.mul
          (differentiableAt_const _ |>.sub differentiableAt_id)).cexp)
    have hne0 : 1 - ((q : ℕ) : ℂ) ^ (c - s) ≠ 0 := by
      intro heq0
      have hn := congrArg norm (sub_eq_zero.mp heq0).symm
      rw [show ((q : ℕ) : ℂ) = (((q : ℕ) : ℝ) : ℂ) by simp,
        Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast q.prop.pos), norm_one] at hn
      exact (Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast q.prop.one_lt) hc).ne hn
    exact hd_sub.inv hne0
  have hpf : posFiniteFactor P₀ ρ₀ = ∏ q ∈ smallPrimes P₀, fun z : ℂ =>
      (1 - ((q : ℕ) : ℂ) ^ ((ρ₀ - 1) - z))⁻¹ *
        (1 - ((q : ℕ) : ℂ) ^ ((conj ρ₀ - 1) - z))⁻¹ := by
    funext z; unfold posFiniteFactor; simp only [Finset.prod_apply]
  rw [hpf]
  exact Finset.prod_induction _ (fun g => DifferentiableAt ℂ g s)
    (fun _ _ hg₁ hg₂ => hg₁.mul hg₂) (differentiableAt_const 1) fun q _ =>
      (hd_q q h1).mul (hd_q q h2)

/-- **Unconditional infinite unbounded-height left-strip poles and reflected analyticity of
`posTruncatedZeta` (without `RiemannHypothesis`):** for every `β ∈ (zetaAsympZeroAbscissa, 1)`
(hence every `β ∈ (zetaZeroAbscissa, 1)`), `γ₀ ∈ ℝ`, `P₀ : ℕ`, and height `T : ℝ`, there exists
`s₀ : ℂ` inside the open left critical strip `0 < Re s₀ < 1 - zetaAsympZeroAbscissa ≤ 1 / 2` with
`|Im s₀| > T` such that:
1. `posTruncatedZeta P₀ (β + i γ₀)` has a genuine pole (`‖F(s)‖ → +∞`, `¬ AnalyticAt`) at `s₀`;
2. `posTruncatedZeta P₀ (β + i γ₀)` is complex differentiable and strictly nonzero at `1 - s₀`;
3. for every multiplier `X : ℂ → ℂ` continuous at `s₀`, the cross-height reflection defect
   `‖F(s) - X(s) F(1 - s)‖` diverges to `+∞` on `𝓝[≠] s₀`. -/
theorem exists_left_strip_pole_and_regular_reflection_above_height
    {β : ℝ} (hβ_lo : zetaAsympZeroAbscissa < β) (hβ1 : β < 1)
    (γ₀ : ℝ) (P₀ : ℕ) (T : ℝ) :
    ∃ s₀ : ℂ, 0 < s₀.re ∧ s₀.re < 1 - zetaAsympZeroAbscissa ∧ T < |s₀.im| ∧
      Tendsto (fun s => ‖posTruncatedZeta P₀ ((β : ℂ) + (γ₀ : ℂ) * I) s‖) (𝓝[≠] s₀) atTop ∧
      ¬ AnalyticAt ℂ (posTruncatedZeta P₀ ((β : ℂ) + (γ₀ : ℂ) * I)) s₀ ∧
      DifferentiableAt ℂ (posTruncatedZeta P₀ ((β : ℂ) + (γ₀ : ℂ) * I)) (1 - s₀) ∧
      posTruncatedZeta P₀ ((β : ℂ) + (γ₀ : ℂ) * I) (1 - s₀) ≠ 0 ∧
      ∀ X : ℂ → ℂ, ContinuousAt X s₀ →
        Tendsto (fun s =>
          ‖posTruncatedZeta P₀ ((β : ℂ) + (γ₀ : ℂ) * I) s -
            X s * posTruncatedZeta P₀ ((β : ℂ) + (γ₀ : ℂ) * I) (1 - s)‖) (𝓝[≠] s₀) atTop := by
  have hΘ_half : 1 / 2 ≤ zetaAsympZeroAbscissa := half_le_zetaAsympZeroAbscissa
  set η : ℝ := min (β - zetaAsympZeroAbscissa) (1 - β) / 4
  have hη_pos : 0 < η := by
    dsimp only [η]
    exact div_pos (lt_min (sub_pos.mpr hβ_lo) (sub_pos.mpr hβ1)) (by norm_num)
  have hη_le1 : 4 * η ≤ β - zetaAsympZeroAbscissa := by
    dsimp only [η]; linarith [min_le_left (β - zetaAsympZeroAbscissa) (1 - β)]
  have hη_le2 : 4 * η ≤ 1 - β := by
    dsimp only [η]; linarith [min_le_right (β - zetaAsympZeroAbscissa) (1 - β)]
  -- Step 1: Extract high-ordinate zero-free threshold `T₀` right of `Θ_∞ + η`.
  obtain ⟨σ_hi, hσ_hi_mem, hσ_hi_lt⟩ :=
    exists_lt_of_csInf_lt zetaAsympZeroSet_nonempty (by linarith : zetaAsympZeroAbscissa < zetaAsympZeroAbscissa + η)
  obtain ⟨_, _, T₀, hT₀_pos, hzf_T₀⟩ := hσ_hi_mem
  have hzf_high : ∀ z : ℂ, zetaAsympZeroAbscissa + η ≤ z.re → T₀ < |z.im| → riemannZeta z ≠ 0 :=
    fun z hz hzim => hzf_T₀ z (lt_of_lt_of_le hσ_hi_lt hz) hzim
  -- Step 2: Produce a zero `ρ₁` of `riemannZeta` with `Θ_∞ - η < ρ₁.re` and `|ρ₁.im| > T₁`.
  set T₁ : ℝ := max |T| T₀ + 2 * |γ₀| + 10
  have hT₁_pos : 0 < T₁ := by dsimp only [T₁]; positivity
  obtain ⟨ρ₁, hζ_ρ₁, hρ₁_gt, hρ₁_im⟩ :
      ∃ ρ₁ : ℂ, riemannZeta ρ₁ = 0 ∧ zetaAsympZeroAbscissa - η < ρ₁.re ∧ T₁ < |ρ₁.im| := by
    rcases lt_or_ge (zetaAsympZeroAbscissa - η) (1 / 2) with hlt_half | hge_half
    · obtain ⟨t, ht_gt, hXi⟩ := exists_Xi_zero_gt T₁
      have ht_pos : 0 < t := lt_of_lt_of_le hT₁_pos ht_gt.le
      set w₀ : ℂ := 1 / 2 + (t : ℂ) * I
      have hw_ne0 : w₀ ≠ 0 := fun h => by have := congrArg Complex.re h; simp [w₀] at this
      have hΛ : completedRiemannZeta w₀ = 0 := by
        rw [completedRiemannZeta_critical_eq_Xi t, hXi]; simp
      have hζ_w : riemannZeta w₀ = 0 := by
        rw [riemannZeta_def_of_ne_zero hw_ne0, hΛ, zero_div]
      have hw₀_re : w₀.re = 1 / 2 := by dsimp only [w₀]; norm_num
      refine ⟨w₀, hζ_w, by rw [hw₀_re]; exact hlt_half, ?_⟩
      have him : w₀.im = t := by simp [w₀]
      rw [him, abs_of_pos ht_pos]
      exact ht_gt
    · have hnot_mem : zetaAsympZeroAbscissa - η ∉ zetaAsympZeroSet := fun hm =>
        (by linarith : ¬(zetaAsympZeroAbscissa ≤ zetaAsympZeroAbscissa - η))
          (csInf_le zetaAsympZeroSet_bddBelow hm)
      have hle1 : zetaAsympZeroAbscissa - η ≤ 1 := by
        linarith [zetaAsympZeroAbscissa_le_zetaZeroAbscissa, zetaZeroAbscissa_le_one]
      have hnot_ex : ¬∃ T' : ℝ, 0 < T' ∧
          ∀ z : ℂ, zetaAsympZeroAbscissa - η < z.re → T' < |z.im| → riemannZeta z ≠ 0 :=
        fun hex => hnot_mem ⟨hge_half, hle1, hex⟩
      push Not at hnot_ex
      obtain ⟨z, hz_re, hz_im, hz_zero⟩ := hnot_ex T₁ hT₁_pos
      exact ⟨z, hz_zero, hz_re, hz_im⟩
  have hρ₁_im_gt_T₀ : T₀ < |ρ₁.im| :=
    lt_of_le_of_lt (by dsimp only [T₁]; linarith [le_max_right |T| T₀, abs_nonneg γ₀]) hρ₁_im
  have hρ₁_lt_hi : ρ₁.re < zetaAsympZeroAbscissa + η :=
    not_le.mp fun hge => hzf_high ρ₁ hge hρ₁_im_gt_T₀ hζ_ρ₁
  have hρ₁_pos : 0 < ρ₁.re := by linarith
  have hρ₁_lt1 : ρ₁.re < 1 := by linarith
  -- Step 3: Verify left-strip pole at `s₀ := ρ₀ - ρ₁` and regularity + nonvanishing at `1 - s₀`.
  set ρ₀ : ℂ := (β : ℂ) + (γ₀ : ℂ) * I
  set s₀ : ℂ := ρ₀ - ρ₁
  have hs₀_re : s₀.re = β - ρ₁.re := by simp [s₀, ρ₀]
  have hs₀_im : s₀.im = γ₀ - ρ₁.im := by simp [s₀, ρ₀]
  have hs₀_pos : 0 < s₀.re := by linarith
  have hs₀_lt_left : s₀.re < 1 - zetaAsympZeroAbscissa := by linarith
  have hs₀_lt1 : s₀.re < 1 := by linarith
  have hs₀_ne1 : s₀ ≠ 1 := fun h => by rw [h] at hs₀_lt1; simp at hs₀_lt1
  have hs₀_im_lb : max |T| T₀ + |γ₀| + 10 < |s₀.im| := by
    have htri : |ρ₁.im| - |γ₀| ≤ |γ₀ - ρ₁.im| := by
      have h := abs_sub_abs_le_abs_sub ρ₁.im γ₀
      rwa [abs_sub_comm] at h
    rw [hs₀_im]
    dsimp only [T₁] at hρ₁_im
    linarith
  have hs₀_im_gt_T : T < |s₀.im| :=
    lt_of_le_of_lt (by linarith [le_abs_self T, le_max_left |T| T₀, abs_nonneg γ₀]) hs₀_im_lb
  have h1s₀_re : (1 - s₀).re = 1 - β + ρ₁.re := by simp [hs₀_re]; ring
  have h1s₀_im : |(1 - s₀).im| = |s₀.im| := by simp
  have hζ_1s₀_ne : riemannZeta (1 - s₀) ≠ 0 := by
    refine hzf_high (1 - s₀) (by linarith) ?_
    rw [h1s₀_im]
    linarith [le_max_right |T| T₀, abs_nonneg γ₀]
  have hζ_s₀_ne : riemannZeta s₀ ≠ 0 := fun h0 =>
    hζ_1s₀_ne (riemannZeta_one_sub_eq_zero_of_mem_openStrip h0 hs₀_pos hs₀_lt1)
  have hfin1 : (ρ₀ - 1 - s₀).re < 0 := by
    have : (ρ₀ - 1 - s₀).re = ρ₁.re - 1 := by dsimp only [s₀]; simp
    linarith
  have hfin2 : (conj ρ₀ - 1 - s₀).re < 0 := by
    have : (conj ρ₀ - 1 - s₀).re = ρ₁.re - 1 := by dsimp only [s₀, ρ₀]; simp
    linarith
  have hw1_eq : s₀ + 1 - ρ₀ = 1 - ρ₁ := by dsimp only [s₀]; ring
  have hw1_ne1 : s₀ + 1 - ρ₀ ≠ 1 := by
    rw [hw1_eq]; intro h; have := congrArg Complex.re h; simp at this; linarith
  have hw2_ne1 : s₀ + 1 - conj ρ₀ ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    have hre : (s₀ + 1 - conj ρ₀).re = 1 - ρ₁.re := by dsimp only [s₀, ρ₀]; simp; ring
    rw [hre] at this; simp at this; linarith
  have hw1_zero : riemannZeta (s₀ + 1 - ρ₀) = 0 := by
    rw [hw1_eq]
    exact riemannZeta_one_sub_eq_zero_of_mem_openStrip hζ_ρ₁ hρ₁_pos hρ₁_lt1
  obtain ⟨htop, hnot_an⟩ := tendsto_norm_posTruncatedZeta_atTop_of_shifted_zero P₀
    hs₀_ne1 hζ_s₀_ne hfin1 hfin2 hw1_ne1 hw2_ne1 hw1_zero
  -- Regularity and nonvanishing of `posTruncatedZeta P₀ ρ₀` at `1 - s₀`.
  have h1s₀_ne1 : 1 - s₀ ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  set u₁ : ℂ := 1 - s₀ + 1 - ρ₀
  set u₂ : ℂ := 1 - s₀ + 1 - conj ρ₀
  have hu₁_re : u₁.re = ρ₁.re + 2 * (1 - β) := by dsimp only [u₁, s₀, ρ₀]; simp; ring
  have hu₂_re : u₂.re = ρ₁.re + 2 * (1 - β) := by dsimp only [u₂, s₀, ρ₀]; simp; ring
  have hu₁_im : u₁.im = ρ₁.im - 2 * γ₀ := by dsimp only [u₁, s₀, ρ₀]; simp; ring
  have hu₂_im : u₂.im = ρ₁.im := by dsimp only [u₂, s₀, ρ₀]; simp
  have hu₁_im_gt : T₀ < |u₁.im| := by
    have htri : |ρ₁.im| - |2 * γ₀| ≤ |ρ₁.im - 2 * γ₀| := abs_sub_abs_le_abs_sub _ _
    have habs2 : |2 * γ₀| = 2 * |γ₀| := by rw [abs_mul, abs_of_pos two_pos]
    rw [habs2] at htri
    rw [hu₁_im]
    dsimp only [T₁] at hρ₁_im
    linarith [le_max_right |T| T₀]
  have hu₂_im_gt : T₀ < |u₂.im| := by rw [hu₂_im]; exact hρ₁_im_gt_T₀
  have hu₁_ne1 : u₁ ≠ 1 := fun h => by
    have him1 : u₁.im = 0 := by simpa using congrArg Complex.im h
    rw [him1, abs_zero] at hu₁_im_gt; linarith
  have hu₂_ne1 : u₂ ≠ 1 := fun h => by
    have him2 : u₂.im = 0 := by simpa using congrArg Complex.im h
    rw [him2, abs_zero] at hu₂_im_gt; linarith
  have hζ_u₁_ne : riemannZeta u₁ ≠ 0 := hzf_high u₁ (by linarith) hu₁_im_gt
  have hζ_u₂_ne : riemannZeta u₂ ≠ 0 := hzf_high u₂ (by linarith) hu₂_im_gt
  have hfin_r1 : (ρ₀ - 1 - (1 - s₀)).re < 0 := by
    have : (ρ₀ - 1 - (1 - s₀)).re = β - 2 + s₀.re := by dsimp only [ρ₀]; simp; ring
    linarith
  have hfin_r2 : (conj ρ₀ - 1 - (1 - s₀)).re < 0 := by
    have : (conj ρ₀ - 1 - (1 - s₀)).re = β - 2 + s₀.re := by dsimp only [ρ₀]; simp; ring
    linarith
  have hd_inv1 : DifferentiableAt ℂ (fun z => Sieve.invZeta (z + 1 - ρ₀)) (1 - s₀) :=
    (Sieve.differentiableAt_invZeta_of_zeta_ne_zero hu₁_ne1 hζ_u₁_ne).comp (1 - s₀)
      ((differentiableAt_id.add_const 1).sub_const ρ₀)
  have hd_inv2 : DifferentiableAt ℂ (fun z => Sieve.invZeta (z + 1 - conj ρ₀)) (1 - s₀) :=
    (Sieve.differentiableAt_invZeta_of_zeta_ne_zero hu₂_ne1 hζ_u₂_ne).comp (1 - s₀)
      ((differentiableAt_id.add_const 1).sub_const (conj ρ₀))
  have hd_fin : DifferentiableAt ℂ (posFiniteFactor P₀ ρ₀) (1 - s₀) :=
    differentiableAt_posFiniteFactor_of_re_neg P₀ ρ₀ (1 - s₀) hfin_r1 hfin_r2
  have hd_1s₀ : DifferentiableAt ℂ (posTruncatedZeta P₀ ρ₀) (1 - s₀) :=
    (differentiableAt_riemannZeta h1s₀_ne1).mul ((hd_inv1.mul hd_inv2).mul hd_fin)
  have hne_1s₀ : posTruncatedZeta P₀ ρ₀ (1 - s₀) ≠ 0 := by
    unfold posTruncatedZeta posCofactor posFiniteFactor
    refine mul_ne_zero hζ_1s₀_ne (mul_ne_zero (mul_ne_zero ?_ ?_) ?_)
    · rw [Sieve.invZeta_eq_inv hu₁_ne1]; exact inv_ne_zero hζ_u₁_ne
    · rw [Sieve.invZeta_eq_inv hu₂_ne1]; exact inv_ne_zero hζ_u₂_ne
    · refine Finset.prod_ne_zero_iff.mpr fun q _ => mul_ne_zero (inv_ne_zero ?_) (inv_ne_zero ?_)
      · intro heq
        have hn := congrArg norm (sub_eq_zero.mp heq).symm
        rw [show ((q : ℕ) : ℂ) = (((q : ℕ) : ℝ) : ℂ) by simp,
          Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast q.prop.pos), norm_one] at hn
        exact (Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast q.prop.one_lt) hfin_r1).ne hn
      · intro heq
        have hn := congrArg norm (sub_eq_zero.mp heq).symm
        rw [show ((q : ℕ) : ℂ) = (((q : ℕ) : ℝ) : ℂ) by simp,
          Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast q.prop.pos), norm_one] at hn
        exact (Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast q.prop.one_lt) hfin_r2).ne hn
  -- Step 4: Blow-up of `‖F(s) - X(s) F(1 - s)‖` on `𝓝[≠] s₀` for any `X` continuous at `s₀`.
  refine ⟨s₀, hs₀_pos, hs₀_lt_left, hs₀_im_gt_T, htop, hnot_an, hd_1s₀, hne_1s₀, fun X hX => ?_⟩
  have hcont_rhs : ContinuousAt
      (fun s : ℂ => X s * posTruncatedZeta P₀ ρ₀ (1 - s)) s₀ :=
    hX.mul (hd_1s₀.continuousAt.comp (continuous_const.sub continuous_id).continuousAt)
  set B_rhs : ℝ := ‖X s₀ * posTruncatedZeta P₀ ρ₀ (1 - s₀)‖ + 1
  have hev_rhs : ∀ᶠ s in 𝓝[≠] s₀,
      ‖X s * posTruncatedZeta P₀ ρ₀ (1 - s)‖ < B_rhs :=
    eventually_nhdsWithin_of_eventually_nhds
      (hcont_rhs.norm.eventually (Iio_mem_nhds (by dsimp only [B_rhs]; linarith)))
  rw [Filter.tendsto_atTop]
  intro M
  filter_upwards [htop.eventually (eventually_ge_atTop (M + B_rhs)), hev_rhs] with s hs_big hs_bd
  have htri := norm_sub_norm_le (posTruncatedZeta P₀ ρ₀ s) (X s * posTruncatedZeta P₀ ρ₀ (1 - s))
  linarith

/-- **Antipodal asymmetry of `posTruncatedZeta` at the reflected partner `1 - ρ₀` of its planted
zero:** for every `β ∈ (zetaZeroAbscissa, 1)`, `γ₀ ≠ 0`, and `P₀ : ℕ`, setting `ρ₀ = β + i γ₀`,
`posTruncatedZeta P₀ ρ₀ ρ₀ = 0` whereas at `1 - ρ₀ ∈ {0 < Re s < 1 / 2}` either `posTruncatedZeta`
is differentiable and strictly nonzero or its norm diverges to `+∞` on `𝓝[≠] (1 - ρ₀)`. -/
theorem posTruncatedZeta_antipodal_asymmetry_at_planted_zero
    {β γ₀ : ℝ} (hΘβ : zetaZeroAbscissa < β) (hβ1 : β < 1) (hγ₀ : γ₀ ≠ 0) (P₀ : ℕ) :
    let ρ₀ : ℂ := (β : ℂ) + (γ₀ : ℂ) * I
    posTruncatedZeta P₀ ρ₀ ρ₀ = 0 ∧
    ((DifferentiableAt ℂ (posTruncatedZeta P₀ ρ₀) (1 - ρ₀) ∧
        posTruncatedZeta P₀ ρ₀ (1 - ρ₀) ≠ 0) ∨
      Tendsto (fun s => ‖posTruncatedZeta P₀ ρ₀ s‖) (𝓝[≠] (1 - ρ₀)) atTop) := by
  have hΘ_half : 1 / 2 ≤ zetaZeroAbscissa := half_le_zetaZeroAbscissa
  set ρ₀ : ℂ := (β : ℂ) + (γ₀ : ℂ) * I
  have hzero_ρ₀ : posTruncatedZeta P₀ ρ₀ ρ₀ = 0 := by
    have hzf : ∀ z : ℂ, zetaZeroAbscissa < z.re → riemannZeta z ≠ 0 :=
      fun _ hz => riemannZeta_ne_zero_of_zetaZeroAbscissa_lt hz
    have hset := zeroSet_posTruncatedZeta_eq_pair hΘ_half hΘβ hβ1 hγ₀ hzf P₀
    have hmem : ρ₀ ∈ ({ρ₀, conj ρ₀} : Set ℂ) := Set.mem_insert _ _
    rw [← hset] at hmem
    exact hmem.2.2
  refine ⟨hzero_ρ₀, ?_⟩
  set sL : ℂ := 1 - ρ₀
  have hsL_re : sL.re = 1 - β := by simp [sL, ρ₀]
  have hsL_pos : 0 < sL.re := by linarith
  have hsL_lt1 : sL.re < 1 := by linarith
  have hsL_ne1 : sL ≠ 1 := fun h => by rw [h] at hsL_lt1; simp at hsL_lt1
  have hζ_ρ₀_ne : riemannZeta ρ₀ ≠ 0 :=
    riemannZeta_ne_zero_of_zetaZeroAbscissa_lt (by simp [ρ₀]; exact hΘβ)
  have hζ_sL_ne : riemannZeta sL ≠ 0 := fun h0 =>
    hζ_ρ₀_ne (by simpa [sL] using riemannZeta_one_sub_eq_zero_of_mem_openStrip h0 hsL_pos hsL_lt1)
  have hw2_eq : sL + 1 - conj ρ₀ = ((2 - 2 * β : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [sL, ρ₀]; ring
  have hw2_ne1 : sL + 1 - conj ρ₀ ≠ 1 := by
    rw [hw2_eq]; intro h; have := congrArg Complex.re h; simp at this; linarith
  have hζ_w2_ne : riemannZeta (sL + 1 - conj ρ₀) ≠ 0 := by
    rw [hw2_eq]
    exact riemannZeta_real_strip_ne_zero (by linarith) (by linarith)
  have hw1_eq : sL + 1 - ρ₀ = 2 - 2 * ρ₀ := by dsimp only [sL]; ring
  have hw1_ne1 : sL + 1 - ρ₀ ≠ 1 := by
    rw [hw1_eq]; intro h; have := congrArg Complex.im h; simp [ρ₀] at this; exact hγ₀ this
  have hfin1 : (ρ₀ - 1 - sL).re < 0 := by
    have : (ρ₀ - 1 - sL).re = 2 * β - 2 := by dsimp only [sL, ρ₀]; simp; ring
    linarith
  have hfin2 : (conj ρ₀ - 1 - sL).re < 0 := by
    have : (conj ρ₀ - 1 - sL).re = 2 * β - 2 := by dsimp only [sL, ρ₀]; simp; ring
    linarith
  rcases eq_or_ne (riemannZeta (sL + 1 - ρ₀)) 0 with hw1_zero | hw1_nz
  · exact Or.inr (tendsto_norm_posTruncatedZeta_atTop_of_shifted_zero P₀
      hsL_ne1 hζ_sL_ne hfin1 hfin2 hw1_ne1 hw2_ne1 hw1_zero).1
  · left
    have hd_inv1 : DifferentiableAt ℂ (fun z => Sieve.invZeta (z + 1 - ρ₀)) sL :=
      (Sieve.differentiableAt_invZeta_of_zeta_ne_zero hw1_ne1 hw1_nz).comp sL
        ((differentiableAt_id.add_const 1).sub_const ρ₀)
    have hd_inv2 : DifferentiableAt ℂ (fun z => Sieve.invZeta (z + 1 - conj ρ₀)) sL :=
      (Sieve.differentiableAt_invZeta_of_zeta_ne_zero hw2_ne1 hζ_w2_ne).comp sL
        ((differentiableAt_id.add_const 1).sub_const (conj ρ₀))
    have hd_fin : DifferentiableAt ℂ (posFiniteFactor P₀ ρ₀) sL :=
      differentiableAt_posFiniteFactor_of_re_neg P₀ ρ₀ sL hfin1 hfin2
    refine ⟨(differentiableAt_riemannZeta hsL_ne1).mul ((hd_inv1.mul hd_inv2).mul hd_fin), ?_⟩
    unfold posTruncatedZeta posCofactor posFiniteFactor
    refine mul_ne_zero hζ_sL_ne (mul_ne_zero (mul_ne_zero ?_ ?_) ?_)
    · rw [Sieve.invZeta_eq_inv hw1_ne1]; exact inv_ne_zero hw1_nz
    · rw [Sieve.invZeta_eq_inv hw2_ne1]; exact inv_ne_zero hζ_w2_ne
    · refine Finset.prod_ne_zero_iff.mpr fun q _ => mul_ne_zero (inv_ne_zero ?_) (inv_ne_zero ?_)
      · intro heq
        have hn := congrArg norm (sub_eq_zero.mp heq).symm
        rw [show ((q : ℕ) : ℂ) = (((q : ℕ) : ℝ) : ℂ) by simp,
          Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast q.prop.pos), norm_one] at hn
        exact (Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast q.prop.one_lt) hfin1).ne hn
      · intro heq
        have hn := congrArg norm (sub_eq_zero.mp heq).symm
        rw [show ((q : ℕ) : ℂ) = (((q : ℕ) : ℝ) : ℂ) by simp,
          Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast q.prop.pos), norm_one] at hn
        exact (Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast q.prop.one_lt) hfin2).ne hn


/-! ### Part 2: Cross-Height Gaussian Dual-Dirichlet Mechanism, `2r`-Step `zetaChi` Recurrence, Sublinear `O(|Im s|^{1/2 + η})` Left-Strip Witnesses Across `Ω_open`, and Quantitative Failure on `posTruncatedZeta` -/

/-- Structural datum simultaneously encoding the three cross-height reflection axioms:
1. unit-bounded direct and dual Dirichlet coefficients `‖a(n)‖ ≤ 1`, `‖b(n)‖ ≤ 1` (`n ≥ 1`);
2. global pole-freeness on `0 < Re z < 1 / 2` (`holo_leftStrip`), together with analyticity on
   `Re z ≤ 0` and `Re z ≥ 1 / 2 \ {1}` with simple-pole residue `R` at `z = 1`;
3. cross-height functional-equation reflection across vertical lines in `Re z < 0` with conductor
   `Q > 0` and unimodular root number `‖ω‖ = 1`. -/
structure UnitPoleFreeCrossHeightDatum
    (F : ℂ → ℂ) (a b : ℕ → ℂ) (R : ℂ) (Q : ℝ) (ω : ℂ) : Prop where
  Q_pos : 0 < Q
  norm_ω : ‖ω‖ = 1
  unit_a : ∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤ 1
  unit_b : ∀ n : ℕ, 1 ≤ n → ‖b n‖ ≤ 1
  dirichlet_eq : ∀ z : ℂ, 1 < z.re →
    F z = ∑' n : ℕ, a (n + 1) * ((n + 1 : ℕ) : ℂ) ^ (-z)
  holo_leftStrip : ∀ z : ℂ, 0 < z.re → z.re < 1 / 2 → DifferentiableAt ℂ F z
  holo_rightOffOne : ∀ z : ℂ, 1 / 2 ≤ z.re → z ≠ 1 → DifferentiableAt ℂ F z
  holo_nonpos : ∀ z : ℂ, z.re ≤ 0 → DifferentiableAt ℂ F z
  pole_res : Tendsto (fun z : ℂ => (z - 1) * F z) (𝓝[≠] 1) (𝓝 R)
  poly_growth : ∀ B : ℝ, ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧
    ∀ σ t : ℝ, |σ| ≤ B → 1 ≤ |t| → ‖F ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * |t| ^ N
  crossHeight_refl : ∀ z : ℂ, z.re < 0 →
    F z = ω * (Q : ℂ) ^ ((1 / 2 : ℂ) - z) * zetaChi z *
      ∑' m : ℕ, b (m + 1) * ((m + 1 : ℕ) : ℂ) ^ (-(1 - z))

/-- `riemannZeta` satisfies `UnitPoleFreeCrossHeightDatum` at `(a, b, R, Q, ω) = (1, 1, 1, 1, 1)`. -/
theorem unitPoleFreeCrossHeightDatum_riemannZeta :
    UnitPoleFreeCrossHeightDatum riemannZeta (fun _ => 1) (fun _ => 1) 1 1 1 := by
  refine ⟨zero_lt_one, norm_one, (fun _ _ => by simp), (fun _ _ => by simp), ?_, ?_, ?_, ?_,
    riemannZeta_residue_one, exists_bound_norm_riemannZeta_strip, ?_⟩
  · intro z hz
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hz]
    refine tsum_congr fun n => ?_
    rw [one_mul, one_div, ← Complex.cpow_neg]
    push_cast; ring
  · intro z _ hz_lt
    exact differentiableAt_riemannZeta (fun h => by rw [h] at hz_lt; norm_num at hz_lt)
  · intro z _ hne
    exact differentiableAt_riemannZeta hne
  · intro z hz
    exact differentiableAt_riemannZeta (fun h => by rw [h] at hz; norm_num at hz)
  · intro z hz
    have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
    have hz1 : z ≠ 1 := fun h => by rw [h] at hz; norm_num at hz
    have h1z : 1 < (1 - z).re := by simp; linarith
    have hG : Complex.Gammaℝ (1 - z) ≠ 0 :=
      Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
    rw [zeta_eq_zetaChi_mul hz0 hz1 hG, zeta_eq_tsum_one_div_nat_add_one_cpow h1z]
    simp only [Complex.ofReal_one, Complex.one_cpow, one_mul]
    congr 1
    refine tsum_congr fun m => ?_
    rw [one_div, ← Complex.cpow_neg]
    push_cast; ring

private theorem UnitPoleFreeCrossHeightDatum.differentiableAt_of_ne_one
    {F : ℂ → ℂ} {a b : ℕ → ℂ} {R : ℂ} {Q : ℝ} {ω : ℂ}
    (hD : UnitPoleFreeCrossHeightDatum F a b R Q ω) {z : ℂ} (hz : z ≠ 1) :
    DifferentiableAt ℂ F z := by
  rcases le_or_gt z.re 0 with hle0 | hgt0
  · exact hD.holo_nonpos z hle0
  · rcases lt_or_ge z.re (1 / 2) with hlt_half | hge_half
    · exact hD.holo_leftStrip z hgt0 hlt_half
    · exact hD.holo_rightOffOne z hge_half hz

private theorem UnitPoleFreeCrossHeightDatum.differentiable_regularized
    {F : ℂ → ℂ} {a b : ℕ → ℂ} {R : ℂ} {Q : ℝ} {ω : ℂ}
    (hD : UnitPoleFreeCrossHeightDatum F a b R Q ω) :
    Differentiable ℂ (Function.update (fun z => (z - 1) * F z) 1 R) := by
  intro z
  rcases eq_or_ne z 1 with rfl | hz
  · refine (analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
    · filter_upwards [self_mem_nhdsWithin] with w hw
      have hraw : DifferentiableAt ℂ (fun u => (u - 1) * F u) w :=
        (differentiableAt_id.sub_const 1).mul (hD.differentiableAt_of_ne_one hw)
      refine hraw.congr_of_eventuallyEq ?_
      filter_upwards [isOpen_ne.mem_nhds hw] with u hu
      exact Function.update_of_ne hu _ _
    · simpa only [continuousAt_update_same] using hD.pole_res
  · have hraw : DifferentiableAt ℂ (fun u => (u - 1) * F u) z :=
      (differentiableAt_id.sub_const 1).mul (hD.differentiableAt_of_ne_one hz)
    refine hraw.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ne.mem_nhds hz] with u hu
    exact Function.update_of_ne hu _ _

/-- The exact cross-height Gaussian two-Dirichlet-series functional for coefficient pair `(a, b)`,
residue `R`, conductor `Q`, root number `ω`, and Mellin scale `x`. -/
def crossHeightGaussianTwoSeries
    (a b : ℕ → ℂ) (R : ℂ) (Q : ℝ) (ω : ℂ) (s : ℂ) (x : ℝ) : ℂ :=
  (∑' n : ℕ, a (n + 1) * (((n + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / x))) -
    ω * (Q : ℂ) ^ ((1 / 2 : ℂ) - s) *
      (∑' m : ℕ, b (m + 1) * smoothAFEZetaDualCoefficientGeneral s (x / Q) m) -
    R * smoothAFEZetaShiftedPoleResidue s x

private theorem integrable_tsum_of_summable_integral_norm_aux {G : ℕ → ℝ → ℂ}
    (hG : ∀ n, Integrable (G n)) (hs : Summable fun n => ∫ v, ‖G n v‖) :
    Integrable (fun v => ∑' n, G n v) := by
  have hlint : ∀ n, ∫⁻ v, ‖G n v‖ₑ = ENNReal.ofReal (∫ v, ‖G n v‖) := fun n => by
    rw [ofReal_integral_eq_lintegral_ofReal (hG n).norm
      (Filter.Eventually.of_forall fun _ => norm_nonneg _)]
    congr 1; funext v; rw [ofReal_norm]
  have hfin : ∑' n, ∫⁻ v, ‖G n v‖ₑ ≠ ⊤ := by
    simp_rw [hlint]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => integral_nonneg fun _ => norm_nonneg _) hs]
    exact ENNReal.ofReal_ne_top
  have hlt : ∫⁻ v, ∑' n, ‖G n v‖ₑ < ⊤ := by
    rw [lintegral_tsum fun n => (hG n).1.enorm]
    exact lt_top_iff_ne_top.2 hfin
  have hae : ∀ᵐ v, ∑' n, ‖G n v‖ₑ < ⊤ :=
    ae_lt_top' (AEMeasurable.tsum fun n => (hG n).1.enorm) hlt.ne
  have hsum : ∀ᵐ v, Summable fun n => G n v := by
    filter_upwards [hae] with v hv
    refine Summable.of_norm ?_
    exact NNReal.summable_coe.2 (ENNReal.tsum_coe_ne_top_iff_summable.1 (by simpa [enorm] using hv.ne))
  refine ⟨aestronglyMeasurable_of_tendsto_ae (u := (Filter.atTop : Filter (Finset ℕ)))
      (f := fun s v => ∑ n ∈ s, G n v)
      (fun s => Finset.aestronglyMeasurable_fun_sum s fun n _ => (hG n).1)
      (by filter_upwards [hsum] with v hv; exact hv.hasSum), ?_⟩
  unfold HasFiniteIntegral
  exact (lintegral_mono fun _ => enorm_tsum_le_tsum_enorm).trans_lt hlt

/-- **Exact cross-height Gaussian two-series expansion across `0 < Re s < 1 / 2`:**
simultaneously invoking `‖a(n)‖ ≤ 1`, `‖b(n)‖ ≤ 1`, global pole-freeness across `0 < Re z < 1 / 2`,
and cross-height reflection across `Re z < 0` yields an exact Gaussian dual-Dirichlet identity at
every point `s` of the open left critical strip and every scale `x > 0`. -/
theorem crossHeight_gaussian_two_tsum_eq
    {F : ℂ → ℂ} {a b : ℕ → ℂ} {R : ℂ} {Q : ℝ} {ω : ℂ}
    (hD : UnitPoleFreeCrossHeightDatum F a b R Q ω)
    {x : ℝ} (hx : 0 < x) {s : ℂ} (h0 : 0 < s.re) (h_half : s.re < 1 / 2) :
    F s = crossHeightGaussianTwoSeries a b R Q ω s x := by
  have hs_ne1 : s ≠ 1 := fun h => by rw [h] at h_half; norm_num at h_half
  have h1 : s.re < 1 := by linarith
  have hQ : 0 < Q := hD.Q_pos
  have hxQ : 0 < x / Q := div_pos hx hQ
  set regF : ℂ → ℂ := Function.update (fun z => (z - 1) * F z) 1 R
  have hreg_diff : Differentiable ℂ regF := hD.differentiable_regularized
  set MF : ℂ → ℂ := fun w => F (s + w) * (x : ℂ) ^ w * smoothAFEGaussianKernel w
  set NF : ℂ → ℂ := fun w => (x : ℂ) ^ w * Complex.exp (w ^ (2 : ℕ)) * regF (s + w)
  set remF : ℂ → ℂ := dslope (dslope NF 0) (1 - s)
  have hNF_diff : Differentiable ℂ NF := by
    haveI : NeZero (x : ℂ) := ⟨Complex.ofReal_ne_zero.mpr hx.ne'⟩
    exact (((differentiable_const_cpow_of_neZero (x : ℂ)).comp differentiable_id).mul
      (differentiable_exp.comp (differentiable_pow 2))).mul
      (hreg_diff.comp (differentiable_const s |>.add differentiable_id))
  have hrem_diff : Differentiable ℂ remF := by
    have hQ1 : Differentiable ℂ (dslope NF 0) := by
      apply differentiableOn_univ.1
      rw [differentiableOn_dslope Filter.univ_mem]
      exact hNF_diff.differentiableOn
    apply differentiableOn_univ.1
    rw [differentiableOn_dslope Filter.univ_mem]
    exact hQ1.differentiableOn
  -- Two-pole Cauchy kernel decomposition of `MF` at `0` and `1 - s`.
  have hdecomp : ∀ w : ℂ, w ≠ 0 → w ≠ 1 - s →
      MF w = F s * (w - 0)⁻¹ +
        ((R * smoothAFEZetaShiftedPoleResidue s x) * (w - (1 - s))⁻¹ + remF w) := by
    intro w hw0 hwρ
    have hρ0 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr hs_ne1.symm
    have hsw1 : s + w ≠ 1 := fun h => hwρ (by linear_combination h)
    have hwρ0 : w - (1 - s) ≠ 0 := sub_ne_zero.mpr hwρ
    have hN0 : NF 0 = (s - 1) * F s := by
      dsimp only [NF, regF]
      rw [add_zero, Function.update_of_ne hs_ne1]
      simp
    have hNρ : NF (1 - s) = (x : ℂ) ^ (1 - s) * Complex.exp ((1 - s) ^ (2 : ℕ)) * R := by
      dsimp only [NF, regF]
      rw [show s + (1 - s) = 1 by ring, Function.update_self]
    have hMF_quot : MF w = NF w / (w * (w - (1 - s))) := by
      dsimp only [MF, NF, regF]
      rw [smoothAFEGaussianKernel, Function.update_of_ne hsw1,
        show s + w - 1 = w - (1 - s) by ring]
      field_simp [hw0, hwρ0]
    have hrem_eq : remF w =
        (((NF w - NF 0) / w) - ((NF (1 - s) - NF 0) / (1 - s))) / (w - (1 - s)) := by
      dsimp only [remF]
      rw [dslope_of_ne _ hwρ, slope_def_field, dslope_of_ne _ hw0, slope_def_field,
        dslope_of_ne _ hρ0, slope_def_field]
      simp only [sub_zero]
    rw [hMF_quot, hrem_eq, hN0, hNρ, smoothAFEZetaShiftedPoleResidue, sub_zero]
    field_simp [hw0, hρ0, hwρ0]
    ring
  -- Step 1: Finite rectangle identity on `[-1, 1] × [-T, T]` for `T > |s.im|`.
  have hrect : ∀ T : ℝ, |s.im| < T →
      ((∫ u : ℝ in (-1 : ℝ)..1, MF ((u : ℂ) - (T : ℂ) * I)) -
          (∫ u : ℝ in (-1 : ℝ)..1, MF ((u : ℂ) + (T : ℂ) * I)) +
        I • (∫ v : ℝ in (-T)..T, MF ((1 : ℂ) + (v : ℂ) * I))) -
        I • (∫ v : ℝ in (-T)..T, MF ((-1 : ℂ) + (v : ℂ) * I)) =
        2 * Real.pi * I * (F s + R * smoothAFEZetaShiftedPoleResidue s x) := by
    intro T hT
    have hTpos : 0 < T := (abs_nonneg _).trans_lt hT
    have habs := abs_lt.mp hT
    set z₁ : ℂ := (-1 : ℂ) - (T : ℂ) * I
    set z₂ : ℂ := (1 : ℂ) + (T : ℂ) * I
    have hz₁_re : z₁.re = -1 := by simp [z₁]
    have hz₁_im : z₁.im = -T := by simp [z₁]
    have hz₂_re : z₂.re = 1 := by simp [z₂]
    have hz₂_im : z₂.im = T := by simp [z₂]
    have hbox := rectIntegral_eq_two_pole_residues
      (F := MF) (R := remF) (p := 0) (q := 1 - s)
      (rp := F s) (rq := R * smoothAFEZetaShiftedPoleResidue s x)
      (z₁ := z₁) (z₂ := z₂)
      (by rw [hz₁_re]; norm_num) (by rw [hz₂_re]; norm_num)
      (by rw [hz₁_im]; simp; linarith) (by rw [hz₂_im]; simp; linarith)
      (by rw [hz₁_re]; simp; linarith) (by rw [hz₂_re]; simp; linarith)
      (by rw [hz₁_im]; simp; linarith) (by rw [hz₂_im]; simp; linarith)
      hrem_diff hdecomp
    simpa [rectIntegral, z₁, z₂, sub_eq_add_neg] using hbox
  -- Step 2: Vanishing of horizontal edges as `T → +∞` via `poly_growth`.
  obtain ⟨Cp, Np, hCp0, hCp⟩ := hD.poly_growth (|s.re| + 1)
  have hhoriz : ∀ ε : ℝ, |ε| = 1 →
      Tendsto (fun T : ℝ => ∫ u : ℝ in (-1 : ℝ)..1, MF ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I))
        atTop (𝓝 0) := by
    intro ε hε
    set K_h : ℝ := Cp * max x x⁻¹ * Real.exp 1
    refine GaloisForLFunctions.HTGeometry.tendsto_intervalIntegral_of_tendsto_bound
      (M := fun T => K_h * ((|s.im| + T) ^ Np * Real.exp (-(T ^ (2 : ℕ)))))
      (hgt := fun T => ε * T) ?_
      (by simpa using (tendsto_shifted_pow_mul_exp_neg_sq |s.im| Np).const_mul K_h)
    filter_upwards [eventually_ge_atTop (|s.im| + 1)] with T hT u hu
    rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hu
    have hTpos : 0 < T := lt_of_lt_of_le (by positivity) hT
    have habsv : |ε * T| = T := by rw [abs_mul, hε, one_mul, abs_of_pos hTpos]
    have hv1 : 1 ≤ |ε * T| := by rw [habsv]; linarith [abs_nonneg s.im]
    set w : ℂ := (u : ℂ) + ((ε * T : ℝ) : ℂ) * I
    have hw_re : w.re = u := by simp [w]
    have hw_im : w.im = ε * T := by simp [w]
    have hsw_eq : (((s + w).re : ℝ) : ℂ) + (((s + w).im : ℝ) : ℂ) * I = s + w :=
      Complex.re_add_im _
    have hsw_re : |(s + w).re| ≤ |s.re| + 1 := by
      rw [Complex.add_re, hw_re]
      have hu_abs : |u| ≤ 1 := abs_le.mpr ⟨hu.1.le, hu.2⟩
      linarith [abs_add_le s.re u]
    have hsw_im_ge : 1 ≤ |(s + w).im| := by
      rw [Complex.add_im, hw_im]
      have htri : |ε * T| - |s.im| ≤ |s.im + ε * T| := by
        have h := abs_sub_abs_le_abs_sub (ε * T) (-s.im)
        simpa [abs_neg, sub_neg_eq_add, add_comm] using h
      linarith
    have hsw_im_le : |(s + w).im| ≤ |s.im| + T := by
      calc |(s + w).im| = |s.im + ε * T| := by rw [Complex.add_im, hw_im]
        _ ≤ |s.im| + |ε * T| := abs_add_le _ _
        _ = |s.im| + T := by rw [habsv]
    have hF_bd : ‖F (s + w)‖ ≤ Cp * (|s.im| + T) ^ Np := by
      have hb := hCp (s + w).re (s + w).im hsw_re hsw_im_ge
      rw [hsw_eq] at hb
      exact hb.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hsw_im_le Np) hCp0)
    have hx_bd : ‖(x : ℂ) ^ w‖ ≤ max x x⁻¹ := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, hw_re]
      rcases le_total 1 x with h1x | h1x
      · exact (Real.rpow_le_rpow_of_exponent_le h1x hu.2).trans (by rw [Real.rpow_one]; exact le_max_left _ _)
      · exact (Real.rpow_le_rpow_of_exponent_ge hx h1x hu.1.le).trans
          (by rw [Real.rpow_neg_one]; exact le_max_right _ _)
    have hker_bd : ‖smoothAFEGaussianKernel w‖ ≤ Real.exp 1 * Real.exp (-(T ^ (2 : ℕ))) := by
      have hk := norm_smoothAFEGaussianKernel_le_of_im (u := u) (v := ε * T)
        (by linarith) hu.1.le hu.2
      have hsq : (ε * T) ^ (2 : ℕ) = T ^ (2 : ℕ) := by
        calc (ε * T) ^ (2 : ℕ) = |ε| ^ (2 : ℕ) * T ^ (2 : ℕ) := by rw [mul_pow, sq_abs]
          _ = T ^ (2 : ℕ) := by rw [hε]; ring
      rw [habsv, hsq] at hk
      exact hk.trans (div_le_self (by positivity) (by linarith [abs_nonneg s.im]))
    dsimp only [MF, K_h]
    rw [norm_mul, norm_mul]
    calc ‖F (s + w)‖ * ‖(x : ℂ) ^ w‖ * ‖smoothAFEGaussianKernel w‖
        ≤ (Cp * (|s.im| + T) ^ Np) * max x x⁻¹ * (Real.exp 1 * Real.exp (-(T ^ (2 : ℕ)))) := by
          refine mul_le_mul (mul_le_mul hF_bd hx_bd (norm_nonneg _) (by positivity))
            hker_bd (norm_nonneg _) ?_
          exact mul_nonneg (by positivity) (hx.le.trans (le_max_left _ _))
      _ = (Cp * max x x⁻¹ * Real.exp 1) * ((|s.im| + T) ^ Np * Real.exp (-(T ^ (2 : ℕ)))) := by ring
  -- Step 3: Direct edge `Re w = 1` integrability and termwise expansion via `unit_a`.
  have hsc1 : 1 < s.re + 1 := by linarith
  have hMF_right_eq : ∀ v : ℝ,
      MF ((1 : ℂ) + (v : ℂ) * I) =
        ∑' n : ℕ, a (n + 1) * smoothAFEZetaMellinTerm s x n ((1 : ℂ) + (v : ℂ) * I) := by
    intro v
    have hre : 1 < (s + ((1 : ℂ) + (v : ℂ) * I)).re := by simp; linarith
    dsimp only [MF]
    rw [hD.dirichlet_eq _ hre, ← tsum_mul_right, ← tsum_mul_right]
    refine tsum_congr fun n => ?_
    rw [smoothAFEZetaMellinTerm, one_div, ← Complex.cpow_neg]
    push_cast; ring
  have hterm_dir_int : ∀ n : ℕ,
      Integrable (fun v : ℝ => a (n + 1) * smoothAFEZetaMellinTerm s x n ((1 : ℂ) + (v : ℂ) * I)) :=
    fun n => (smoothAFEZetaMellinTerm_verticalIntegrable hx zero_lt_one n).const_mul (a (n + 1))
  have hsum_dir_norm : Summable (fun n : ℕ =>
      ∫ v : ℝ, ‖a (n + 1) * smoothAFEZetaMellinTerm s x n ((1 : ℂ) + (v : ℂ) * I)‖) := by
    refine Summable.of_nonneg_of_le
      (fun _ => integral_nonneg fun _ => norm_nonneg _)
      (fun n => ?_)
      (summable_integral_norm_smoothAFEZetaMellinTerm hx zero_lt_one hsc1)
    refine integral_mono_ae (hterm_dir_int n).norm
      (smoothAFEZetaMellinTerm_verticalIntegrable hx zero_lt_one n).norm
      (Filter.Eventually.of_forall fun v => ?_)
    dsimp only
    rw [norm_mul, show (((1 : ℝ) : ℂ)) = (1 : ℂ) by norm_num]
    exact mul_le_of_le_one_left (norm_nonneg _) (hD.unit_a (n + 1) (Nat.succ_pos n))
  have hMF_right_int : Integrable (fun v : ℝ => MF ((1 : ℂ) + (v : ℂ) * I)) :=
    (integrable_tsum_of_summable_integral_norm_aux hterm_dir_int hsum_dir_norm).congr
      (Filter.Eventually.of_forall fun v => (hMF_right_eq v).symm)
  have hint_right : ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ v : ℝ, MF ((1 : ℂ) + (v : ℂ) * I)) =
      ∑' n : ℕ, a (n + 1) * (((n + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / x)) := by
    have h1eq : (∫ v : ℝ, MF ((1 : ℂ) + (v : ℂ) * I)) =
        ∑' n : ℕ, ∫ v : ℝ, a (n + 1) * smoothAFEZetaMellinTerm s x n ((1 : ℂ) + (v : ℂ) * I) := by
      calc (∫ v : ℝ, MF ((1 : ℂ) + (v : ℂ) * I))
          = ∫ v : ℝ, ∑' n : ℕ, a (n + 1) * smoothAFEZetaMellinTerm s x n ((1 : ℂ) + (v : ℂ) * I) :=
            integral_congr_ae (Filter.Eventually.of_forall hMF_right_eq)
        _ = ∑' n : ℕ, ∫ v : ℝ, a (n + 1) * smoothAFEZetaMellinTerm s x n ((1 : ℂ) + (v : ℂ) * I) :=
            (MeasureTheory.integral_tsum_of_summable_integral_norm hterm_dir_int hsum_dir_norm).symm
    rw [h1eq, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    rw [MeasureTheory.integral_const_mul,
      show (∫ v : ℝ, smoothAFEZetaMellinTerm s x n ((1 : ℂ) + (v : ℂ) * I)) =
        ∫ v : ℝ, smoothAFEZetaMellinTerm s x n (((1 : ℝ) : ℂ) + (v : ℂ) * I) by norm_num,
      integral_smoothAFEZetaMellinTerm_eq_cpow_mul_cutoffIntegral hx,
      ← smoothAFECutoffAt_eq_smoothAFECutoff (div_pos (by exact_mod_cast Nat.succ_pos n) hx) zero_lt_one,
      smoothAFECutoffAt_eq_integral, Complex.real_smul]
    push_cast; ring
  -- Step 4: Left edge `Re w = -1` integrability and termwise dual expansion via `crossHeight_refl` & `unit_b`.
  have hMF_left_eq : ∀ v : ℝ,
      MF ((-1 : ℂ) + (v : ℂ) * I) =
        ω * (Q : ℂ) ^ ((1 / 2 : ℂ) - s) *
          ∑' m : ℕ, b (m + 1) * smoothAFEZetaReflectedTerm s (x / Q) m ((-1 : ℂ) + (v : ℂ) * I) := by
    intro v
    set w : ℂ := (-1 : ℂ) + (v : ℂ) * I
    have hsw_neg : (s + w).re < 0 := by simp [w]; linarith
    have hQ0 : (Q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hQ.ne'
    have hQpow : (Q : ℂ) ^ ((1 / 2 : ℂ) - (s + w)) * (x : ℂ) ^ w =
        (Q : ℂ) ^ ((1 / 2 : ℂ) - s) * ((x / Q : ℝ) : ℂ) ^ w := by
      have hsplit : (Q : ℂ) ^ ((1 / 2 : ℂ) - (s + w)) =
          (Q : ℂ) ^ ((1 / 2 : ℂ) - s) * (Q : ℂ) ^ (-w) := by
        rw [show (1 / 2 : ℂ) - (s + w) = ((1 / 2 : ℂ) - s) + (-w) by ring,
          Complex.cpow_add _ _ hQ0]
      have hdiv := cpow_div_pos_neg hx hQ (-w)
      rw [neg_neg] at hdiv
      rw [hsplit, hdiv]
      ring
    dsimp only [MF]
    rw [hD.crossHeight_refl (s + w) hsw_neg]
    have hsum_b : Summable (fun m : ℕ => b (m + 1) * ((m + 1 : ℕ) : ℂ) ^ (-(1 - (s + w)))) := by
      have h1sw : 1 < (1 - (s + w)).re := by simp [w]; linarith
      have hbase : Summable (fun m : ℕ => ‖(1 : ℂ) / ((m + 1 : ℕ) : ℂ) ^ (1 - (s + w))‖) := by
        have hs0 := (Complex.summable_one_div_nat_cpow.mpr h1sw).norm
        simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr hs0
      refine Summable.of_norm_bounded hbase fun m => ?_
      rw [norm_mul, Complex.cpow_neg, ← one_div]
      exact mul_le_of_le_one_left (norm_nonneg _) (hD.unit_b (m + 1) (Nat.succ_pos m))
    calc (ω * (Q : ℂ) ^ ((1 / 2 : ℂ) - (s + w)) * zetaChi (s + w) *
            ∑' m : ℕ, b (m + 1) * ((m + 1 : ℕ) : ℂ) ^ (-(1 - (s + w)))) *
          (x : ℂ) ^ w * smoothAFEGaussianKernel w
        = ω * ((Q : ℂ) ^ ((1 / 2 : ℂ) - (s + w)) * (x : ℂ) ^ w) *
            ((∑' m : ℕ, b (m + 1) * ((m + 1 : ℕ) : ℂ) ^ (-(1 - (s + w)))) *
              (zetaChi (s + w) * smoothAFEGaussianKernel w)) := by ring
      _ = ω * (Q : ℂ) ^ ((1 / 2 : ℂ) - s) *
            ((∑' m : ℕ, b (m + 1) * ((m + 1 : ℕ) : ℂ) ^ (-(1 - (s + w)))) *
              (zetaChi (s + w) * ((x / Q : ℝ) : ℂ) ^ w * smoothAFEGaussianKernel w)) := by
          rw [hQpow]; ring
      _ = ω * (Q : ℂ) ^ ((1 / 2 : ℂ) - s) *
            ∑' m : ℕ, b (m + 1) * smoothAFEZetaReflectedTerm s (x / Q) m w := by
          rw [← tsum_mul_right]
          congr 1
          refine tsum_congr fun m => ?_
          rw [smoothAFEZetaReflectedTerm_eq_cpow, show -(1 - (s + w)) = s + w - 1 by ring]
          push_cast; ring
  have hterm_dual_int : ∀ m : ℕ,
      Integrable (fun v : ℝ =>
        b (m + 1) * smoothAFEZetaReflectedTerm s (x / Q) m ((-1 : ℂ) + (v : ℂ) * I)) :=
    fun m => (smoothAFEZetaReflectedTerm_general_left_one_integrable hxQ h0 h1 m).const_mul (b (m + 1))
  have hsum_dual_norm : Summable (fun m : ℕ =>
      ∫ v : ℝ, ‖b (m + 1) * smoothAFEZetaReflectedTerm s (x / Q) m ((-1 : ℂ) + (v : ℂ) * I)‖) := by
    refine Summable.of_nonneg_of_le
      (fun _ => integral_nonneg fun _ => norm_nonneg _)
      (fun m => ?_)
      (summable_integral_norm_smoothAFEZetaReflectedTerm_general_left_one hxQ h0 h1)
    refine integral_mono_ae (hterm_dual_int m).norm
      (smoothAFEZetaReflectedTerm_general_left_one_integrable hxQ h0 h1 m).norm
      (Filter.Eventually.of_forall fun v => ?_)
    dsimp only
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hD.unit_b (m + 1) (Nat.succ_pos m))
  have hMF_left_int : Integrable (fun v : ℝ => MF ((-1 : ℂ) + (v : ℂ) * I)) :=
    ((integrable_tsum_of_summable_integral_norm_aux hterm_dual_int hsum_dual_norm).const_mul
      (ω * (Q : ℂ) ^ ((1 / 2 : ℂ) - s))).congr
      (Filter.Eventually.of_forall fun v => (hMF_left_eq v).symm)
  have hint_left : ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ v : ℝ, MF ((-1 : ℂ) + (v : ℂ) * I)) =
      ω * (Q : ℂ) ^ ((1 / 2 : ℂ) - s) *
        ∑' m : ℕ, b (m + 1) * smoothAFEZetaDualCoefficientGeneral s (x / Q) m := by
    have h1eq : (∫ v : ℝ, MF ((-1 : ℂ) + (v : ℂ) * I)) =
        ω * (Q : ℂ) ^ ((1 / 2 : ℂ) - s) *
          ∑' m : ℕ, ∫ v : ℝ,
            b (m + 1) * smoothAFEZetaReflectedTerm s (x / Q) m ((-1 : ℂ) + (v : ℂ) * I) := by
      calc (∫ v : ℝ, MF ((-1 : ℂ) + (v : ℂ) * I))
          = ∫ v : ℝ, ω * (Q : ℂ) ^ ((1 / 2 : ℂ) - s) *
              ∑' m : ℕ, b (m + 1) * smoothAFEZetaReflectedTerm s (x / Q) m ((-1 : ℂ) + (v : ℂ) * I) :=
            integral_congr_ae (Filter.Eventually.of_forall hMF_left_eq)
        _ = ω * (Q : ℂ) ^ ((1 / 2 : ℂ) - s) *
              ∫ v : ℝ, ∑' m : ℕ,
                b (m + 1) * smoothAFEZetaReflectedTerm s (x / Q) m ((-1 : ℂ) + (v : ℂ) * I) :=
            MeasureTheory.integral_const_mul _ _
        _ = ω * (Q : ℂ) ^ ((1 / 2 : ℂ) - s) *
              ∑' m : ℕ, ∫ v : ℝ,
                b (m + 1) * smoothAFEZetaReflectedTerm s (x / Q) m ((-1 : ℂ) + (v : ℂ) * I) := by
            rw [MeasureTheory.integral_tsum_of_summable_integral_norm hterm_dual_int hsum_dual_norm]
    rw [h1eq, show ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (ω * (Q : ℂ) ^ ((1 / 2 : ℂ) - s) *
          ∑' m : ℕ, ∫ v : ℝ,
            b (m + 1) * smoothAFEZetaReflectedTerm s (x / Q) m ((-1 : ℂ) + (v : ℂ) * I)) =
        ω * (Q : ℂ) ^ ((1 / 2 : ℂ) - s) *
          (((1 / (2 * Real.pi) : ℝ) : ℂ) *
            ∑' m : ℕ, ∫ v : ℝ,
              b (m + 1) * smoothAFEZetaReflectedTerm s (x / Q) m ((-1 : ℂ) + (v : ℂ) * I)) by ring,
      ← tsum_mul_left]
    congr 1
    refine tsum_congr fun m => ?_
    rw [MeasureTheory.integral_const_mul,
      integral_smoothAFEZetaReflectedTerm_general_left_one_eq hxQ h0 h1]
    unfold smoothAFEZetaDualCoefficientGeneral smoothAFEZetaDualCutoffGeneral
    rw [show (((-1 : ℝ) : ℂ)) = (-1 : ℂ) by norm_num, Complex.real_smul]
    ring
  -- Step 5: Pass `T → +∞` in the rectangle identity and divide by `2π i`.
  have hlim_right : Tendsto (fun T : ℝ => ∫ v : ℝ in (-T)..T, MF ((1 : ℂ) + (v : ℂ) * I))
      atTop (𝓝 (∫ v : ℝ, MF ((1 : ℂ) + (v : ℂ) * I))) :=
    intervalIntegral_tendsto_integral hMF_right_int tendsto_neg_atTop_atBot tendsto_id
  have hlim_left : Tendsto (fun T : ℝ => ∫ v : ℝ in (-T)..T, MF ((-1 : ℂ) + (v : ℂ) * I))
      atTop (𝓝 (∫ v : ℝ, MF ((-1 : ℂ) + (v : ℂ) * I))) :=
    intervalIntegral_tendsto_integral hMF_left_int tendsto_neg_atTop_atBot tendsto_id
  have htop : Tendsto (fun T : ℝ => ∫ u : ℝ in (-1 : ℝ)..1, MF ((u : ℂ) + (T : ℂ) * I))
      atTop (𝓝 0) := by
    refine (hhoriz 1 (by norm_num)).congr fun T => ?_
    refine intervalIntegral.integral_congr fun u _ => ?_
    congr 1; push_cast; ring
  have hbot : Tendsto (fun T : ℝ => ∫ u : ℝ in (-1 : ℝ)..1, MF ((u : ℂ) - (T : ℂ) * I))
      atTop (𝓝 0) := by
    refine (hhoriz (-1) (by norm_num)).congr fun T => ?_
    refine intervalIntegral.integral_congr fun u _ => ?_
    congr 1; push_cast; ring
  have hcomb := ((hbot.sub htop).add (hlim_right.const_smul I)).sub (hlim_left.const_smul I)
  have hev : ∀ᶠ T : ℝ in atTop,
      ((∫ u : ℝ in (-1 : ℝ)..1, MF ((u : ℂ) - (T : ℂ) * I)) -
          (∫ u : ℝ in (-1 : ℝ)..1, MF ((u : ℂ) + (T : ℂ) * I)) +
        I • (∫ v : ℝ in (-T)..T, MF ((1 : ℂ) + (v : ℂ) * I))) -
        I • (∫ v : ℝ in (-T)..T, MF ((-1 : ℂ) + (v : ℂ) * I)) =
        2 * Real.pi * I * (F s + R * smoothAFEZetaShiftedPoleResidue s x) := by
    filter_upwards [eventually_gt_atTop |s.im|] with T hT
    exact hrect T hT
  have hinf := tendsto_nhds_unique (hcomb.congr' hev) tendsto_const_nhds
  have hcancel :
      (∫ v : ℝ, MF ((1 : ℂ) + (v : ℂ) * I)) - (∫ v : ℝ, MF ((-1 : ℂ) + (v : ℂ) * I)) =
        (2 * Real.pi : ℂ) * (F s + R * smoothAFEZetaShiftedPoleResidue s x) := by
    apply mul_left_cancel₀ Complex.I_ne_zero
    simpa [smul_eq_mul, mul_sub, mul_assoc, mul_left_comm, mul_comm] using hinf
  have hpi : (2 * Real.pi : ℂ) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  unfold crossHeightGaussianTwoSeries
  rw [← hint_right, ← hint_left, ← mul_sub, hcancel]
  have hinv : ((1 / (2 * Real.pi) : ℝ) : ℂ) * (2 * Real.pi : ℂ) = 1 := by
    push_cast; field_simp [Real.pi_ne_zero]
  linear_combination -((F s + R * smoothAFEZetaShiftedPoleResidue s x) * hinv)

/-- **Exact two-step `zetaChi` recurrence:** shifting `z` by `-2` multiplies `zetaChi z` by
`-(z - 1)(z - 2) / (4π²)` throughout `Re z < 1` away from nonpositive even integers. -/
theorem zetaChi_sub_two {z : ℂ} (hre : z.re < 1) (heven : ∀ m : ℕ, z ≠ -(2 * (m : ℂ))) :
    zetaChi (z - 2) = -((z - 1) * (z - 2) / (4 * (Real.pi : ℂ) ^ 2)) * zetaChi z := by
  have hpi0 : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h1z_ne0 : (1 - z) / 2 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hz2_ne0 : (z - 2) / 2 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hΓz_ne0 : Complex.Gamma (z / 2) ≠ 0 := by
    refine Complex.Gamma_ne_zero fun m hm => heven m ?_
    linear_combination 2 * hm
  have hΓz2_ne0 : Complex.Gamma ((z - 2) / 2) ≠ 0 := by
    refine Complex.Gamma_ne_zero fun m hm => ?_
    rcases m with _ | m'
    · exact hz2_ne0 (by simpa using hm)
    · refine heven m' ?_
      push_cast at hm
      linear_combination 2 * hm
  have hΓ_num : Complex.Gamma ((1 - (z - 2)) / 2) =
      ((1 - z) / 2) * Complex.Gamma ((1 - z) / 2) := by
    rw [show (1 - (z - 2)) / 2 = (1 - z) / 2 + 1 by ring, Complex.Gamma_add_one ((1 - z) / 2) h1z_ne0]
  have hΓ_den : Complex.Gamma (z / 2) = ((z - 2) / 2) * Complex.Gamma ((z - 2) / 2) := by
    rw [show z / 2 = (z - 2) / 2 + 1 by ring, Complex.Gamma_add_one ((z - 2) / 2) hz2_ne0]
  have hpi_num : (Real.pi : ℂ) ^ (-(1 - (z - 2)) / 2) =
      (Real.pi : ℂ) ^ (-(1 - z) / 2) * (Real.pi : ℂ)⁻¹ := by
    rw [show -(1 - (z - 2)) / 2 = -(1 - z) / 2 + (-1 : ℂ) by ring,
      Complex.cpow_add _ _ hpi0, Complex.cpow_neg_one]
  have hpi_den : (Real.pi : ℂ) ^ (-(z - 2) / 2) =
      (Real.pi : ℂ) ^ (-z / 2) * (Real.pi : ℂ) := by
    rw [show -(z - 2) / 2 = -z / 2 + 1 by ring, Complex.cpow_add _ _ hpi0, Complex.cpow_one]
  unfold zetaChi
  rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def, Complex.Gammaℝ_def, Complex.Gammaℝ_def,
    hΓ_num, hΓ_den, hpi_num, hpi_den]
  have hpi_z : (Real.pi : ℂ) ^ (-z / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hpi0)
  have hz2' : z - 2 ≠ 0 := fun h => hz2_ne0 (by rw [h, zero_div])
  have hz2'' : -2 + z ≠ 0 := fun h => hz2' (by linear_combination h)
  field_simp [hpi0, hpi_z, hz2_ne0, hz2', hz2'', hΓz2_ne0]; ring

/-- **Iterated `2r`-step `zetaChi` recurrence across the critical strip:** for every `z` with
`0 < Re z < 1` and every `r : ℕ`, `z - 2k` avoids all even integers (`Re z ∉ ℤ`), yielding the
exact polynomial identity
`zetaChi (z - 2r) = ((-1)^r / (4π²)^r) (∏_{j=0}^{2r-1} (z - (j + 1))) zetaChi z`. -/
theorem zetaChi_sub_two_mul {z : ℂ} (h0 : 0 < z.re) (h1 : z.re < 1) (r : ℕ) :
    zetaChi (z - ((2 * r : ℕ) : ℂ)) =
      ((-1 : ℂ) ^ r / (4 * (Real.pi : ℂ) ^ 2) ^ r) *
        (∏ j ∈ Finset.range (2 * r), (z - ((j + 1 : ℕ) : ℂ))) * zetaChi z := by
  induction r with
  | zero => simp
  | succ r ih =>
    set w : ℂ := z - ((2 * r : ℕ) : ℂ)
    have hw_re : w.re < 1 := by
      dsimp only [w]; simp; linarith
    have hw_even : ∀ m : ℕ, w ≠ -(2 * (m : ℂ)) := by
      intro m heq
      have hre := congrArg Complex.re heq
      dsimp only [w] at hre
      simp at hre
      rcases le_or_gt r m with hrm | hmr
      · have hrmR : (r : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hrm
        linarith
      · have hmrR : (m : ℝ) + 1 ≤ (r : ℝ) := by exact_mod_cast hmr
        linarith
    have hstep : z - ((2 * (r + 1) : ℕ) : ℂ) = w - 2 := by
      dsimp only [w]; push_cast; ring
    rw [hstep, zetaChi_sub_two hw_re hw_even, ih,
      show 2 * (r + 1) = 2 * r + 1 + 1 by omega,
      Finset.prod_range_succ, Finset.prod_range_succ]
    have hw1 : w - 1 = z - ((2 * r + 1 : ℕ) : ℂ) := by dsimp only [w]; push_cast; ring
    have hw2 : w - 2 = z - ((2 * r + 1 + 1 : ℕ) : ℂ) := by dsimp only [w]; push_cast; ring
    have hpi4 : (4 * (Real.pi : ℂ) ^ 2) ≠ 0 := by
      exact_mod_cast mul_ne_zero (by norm_num : (4 : ℝ) ≠ 0) (pow_ne_zero 2 Real.pi_ne_zero)
    rw [hw1, hw2, pow_succ (-1 : ℂ), pow_succ (4 * (Real.pi : ℂ) ^ 2)]
    field_simp [hpi4]

/-- **Sharp `|t|^{1/2 - σ}` bound on `zetaChi` across `[σ_min, 1 / 2]`:** for every `0 < σ_min ≤ 1 / 2`,
there exists `C₀ > 0` such that `‖zetaChi (σ + i t)‖ ≤ C₀ (1 + |t|)^{1/2 - σ}` for all
`σ ∈ [σ_min, 1 / 2]` and all `t ∈ ℝ` (without the `d ≤ 1 / 4` restriction of
`SmoothAFEZetaDisplacedUniformValueTruncation`). -/
theorem exists_norm_zetaChi_leftStrip_rpow_le {σ_min : ℝ}
    (hσ0 : 0 < σ_min) (hσ_half : σ_min ≤ 1 / 2) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ σ t : ℝ, σ_min ≤ σ → σ ≤ 1 / 2 →
      ‖zetaChi ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C₀ * (1 + |t|) ^ (1 / 2 - σ) := by
  obtain ⟨c_γ, _, hc_γ_pos, _, hγ_two⟩ :=
    GaloisForLFunctions.RHTower.exists_twoSided_gamma_vertical_ratio
      (a₁ := 1 / 4) (δ₁ := 1 / 2) (by norm_num) (by norm_num)
  -- Compactness bound on `[σ_min, 1/2] × [-2, 2]`.
  set K_box : Set ℂ := Icc σ_min (1 / 2) ×ℂ Icc (-2 : ℝ) 2
  have hK_comp : IsCompact K_box := isCompact_Icc.reProdIm isCompact_Icc
  have hχ_cont : ContinuousOn zetaChi K_box := by
    intro z hz
    rw [Complex.mem_reProdIm] at hz
    refine (zetaChi_analyticAt ?_).continuousAt.continuousWithinAt
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    simp; linarith [hz.1.2]
  obtain ⟨M_box, hM_box⟩ := hK_comp.exists_bound_of_continuousOn hχ_cont
  refine ⟨max (max M_box 1) (c_γ⁻¹ + 1), by positivity, fun σ t hlo hhi => ?_⟩
  have h1t_ge1 : (1 : ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
  have hexp_nn : 0 ≤ 1 / 2 - σ := by linarith
  rcases le_or_gt |t| 2 with ht_small | ht_big
  · have hmem : ((σ : ℂ) + (t : ℂ) * I) ∈ K_box := by
      rw [Complex.mem_reProdIm]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero,
        Complex.add_im, Complex.mul_im, mul_one, zero_add]
      exact ⟨⟨hlo, hhi⟩, abs_le.mp ht_small⟩
    have hb := hM_box _ hmem
    have hrp1 : (1 : ℝ) ≤ (1 + |t|) ^ (1 / 2 - σ) :=
      Real.one_le_rpow h1t_ge1 hexp_nn
    have hM_le : M_box ≤ max (max M_box 1) (c_γ⁻¹ + 1) :=
      (le_max_left _ _).trans (le_max_left _ _)
    calc ‖zetaChi ((σ : ℂ) + (t : ℂ) * I)‖
        ≤ M_box := hb
      _ ≤ max (max M_box 1) (c_γ⁻¹ + 1) * 1 := by linarith
      _ ≤ max (max M_box 1) (c_γ⁻¹ + 1) * (1 + |t|) ^ (1 / 2 - σ) :=
          mul_le_mul_of_nonneg_left hrp1 (by positivity)
  · set τ : ℝ := |t| / 2
    have hτ1 : 1 ≤ τ := by dsimp only [τ]; linarith
    have hτ_pos : 0 < τ := zero_lt_one.trans_le hτ1
    set a : ℝ := σ / 2
    set δ : ℝ := 1 / 2 - σ
    have ha0 : 0 ≤ a := by dsimp only [a]; linarith
    have ha1 : a ≤ 1 / 4 := by dsimp only [a]; linarith
    have hδ1 : δ ≤ 1 / 2 := by dsimp only [δ]; linarith
    have hlow := (hγ_two a δ τ ha0 ha1 hexp_nn hδ1 hτ1).1
    have hΓ_num_pos : 0 < ‖Complex.Gamma (((a + δ : ℝ) : ℂ) + (τ : ℂ) * I)‖ := by
      refine norm_pos_iff.mpr (Complex.Gamma_ne_zero fun m hm => ?_)
      have him := congrArg Complex.im hm
      simp at him
      linarith
    have hΓ_den_pos : 0 < ‖Complex.Gamma ((a : ℂ) + (τ : ℂ) * I)‖ := by
      refine norm_pos_iff.mpr (Complex.Gamma_ne_zero fun m hm => ?_)
      have him := congrArg Complex.im hm
      simp at him
      linarith
    have hinv_ratio :
        ‖Complex.Gamma (((a + δ : ℝ) : ℂ) + (τ : ℂ) * I)‖ /
            ‖Complex.Gamma ((a : ℂ) + (τ : ℂ) * I)‖ ≤
          c_γ⁻¹ * τ ^ δ := by
      rw [div_le_iff₀ hΓ_den_pos]
      have h1 : c_γ * τ ^ (-δ) * ‖Complex.Gamma (((a + δ : ℝ) : ℂ) + (τ : ℂ) * I)‖ ≤
          ‖Complex.Gamma ((a : ℂ) + (τ : ℂ) * I)‖ := (le_div_iff₀ hΓ_num_pos).mp hlow
      have hmul : (c_γ⁻¹ * τ ^ δ) * (c_γ * τ ^ (-δ)) = 1 := by
        have hpow_c : τ ^ δ * τ ^ (-δ) = 1 := by
          rw [← Real.rpow_add hτ_pos, add_neg_cancel, Real.rpow_zero]
        calc (c_γ⁻¹ * τ ^ δ) * (c_γ * τ ^ (-δ))
            = (c_γ⁻¹ * c_γ) * (τ ^ δ * τ ^ (-δ)) := by ring
          _ = 1 := by rw [inv_mul_cancel₀ hc_γ_pos.ne', hpow_c, mul_one]
      calc ‖Complex.Gamma (((a + δ : ℝ) : ℂ) + (τ : ℂ) * I)‖
          = ((c_γ⁻¹ * τ ^ δ) * (c_γ * τ ^ (-δ))) *
              ‖Complex.Gamma (((a + δ : ℝ) : ℂ) + (τ : ℂ) * I)‖ := by rw [hmul, one_mul]
        _ = (c_γ⁻¹ * τ ^ δ) *
              (c_γ * τ ^ (-δ) * ‖Complex.Gamma (((a + δ : ℝ) : ℂ) + (τ : ℂ) * I)‖) := by ring
        _ ≤ (c_γ⁻¹ * τ ^ δ) * ‖Complex.Gamma ((a : ℂ) + (τ : ℂ) * I)‖ :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
    -- Match `‖Complex.Gamma ((1 - z) / 2)‖` and `‖Complex.Gamma (z / 2)‖` to `τ = |t| / 2`.
    have hnorm_conj : ∀ x y : ℝ,
        ‖Complex.Gamma ((x : ℂ) + (y : ℂ) * I)‖ =
          ‖Complex.Gamma ((x : ℂ) + ((|y| : ℝ) : ℂ) * I)‖ := by
      intro x y
      rcases le_or_gt 0 y with hy | hy
      · rw [abs_of_nonneg hy]
      · rw [abs_of_neg hy]
        have hc : starRingEnd ℂ ((x : ℂ) + (y : ℂ) * I) = (x : ℂ) + ((-y : ℝ) : ℂ) * I := by
          simp
        rw [← Complex.norm_conj (Complex.Gamma _), ← Complex.Gamma_conj, hc]
    have harg1 : (1 - ((σ : ℂ) + (t : ℂ) * I)) / 2 =
        ((a + δ : ℝ) : ℂ) + ((-t / 2 : ℝ) : ℂ) * I := by
      dsimp only [a, δ]; push_cast; ring
    have harg2 : ((σ : ℂ) + (t : ℂ) * I) / 2 =
        (a : ℂ) + ((t / 2 : ℝ) : ℂ) * I := by
      dsimp only [a]; push_cast; ring
    have habs1 : |-t / 2| = τ := by rw [neg_div, abs_neg, abs_div, abs_two]
    have habs2 : |t / 2| = τ := by rw [abs_div, abs_two]
    rw [norm_zetaChi_eq, show (((σ : ℂ) + (t : ℂ) * I)).re = σ by simp,
      harg1, harg2, hnorm_conj (a + δ) (-t / 2), hnorm_conj a (t / 2), habs1, habs2]
    have hpi_le1 : Real.pi ^ (σ - 1 / 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (by linarith)
    have hτ_le : τ ^ δ ≤ (1 + |t|) ^ δ :=
      Real.rpow_le_rpow hτ_pos.le (by dsimp only [τ]; linarith [abs_nonneg t]) hexp_nn
    have hc_le : c_γ⁻¹ ≤ max (max M_box 1) (c_γ⁻¹ + 1) :=
      (by linarith : c_γ⁻¹ ≤ c_γ⁻¹ + 1).trans (le_max_right (max M_box 1) (c_γ⁻¹ + 1))
    calc Real.pi ^ (σ - 1 / 2) * ‖Complex.Gamma (((a + δ : ℝ) : ℂ) + (τ : ℂ) * I)‖ /
            ‖Complex.Gamma ((a : ℂ) + (τ : ℂ) * I)‖
        = Real.pi ^ (σ - 1 / 2) *
            (‖Complex.Gamma (((a + δ : ℝ) : ℂ) + (τ : ℂ) * I)‖ /
              ‖Complex.Gamma ((a : ℂ) + (τ : ℂ) * I)‖) := mul_div_assoc _ _ _
      _ ≤ 1 * (c_γ⁻¹ * τ ^ δ) :=
          mul_le_mul hpi_le1 hinv_ratio (by positivity) zero_le_one
      _ ≤ max (max M_box 1) (c_γ⁻¹ + 1) * (1 + |t|) ^ (1 / 2 - σ) := by
          rw [one_mul]
          exact mul_le_mul hc_le hτ_le (by positivity) (by positivity)

/-- **Uniform factored bound on `zetaChi (s - 2r + i v)` across `σ_min ≤ Re s < 1 / 2`:**
combining `zetaChi_sub_two_mul` with `exists_norm_zetaChi_leftStrip_rpow_le` separates `|Im s|`
and `|v|` into `(1 + |Im s|)^{2r + 1/2 - Re s} * (1 + |v|)^{2r + 1}`. -/
theorem exists_norm_zetaChi_deep_even_le {σ_min : ℝ}
    (hσ0 : 0 < σ_min) (hσ_half : σ_min ≤ 1 / 2) (r : ℕ) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (s : ℂ) (v : ℝ), σ_min ≤ s.re → s.re < 1 / 2 →
      ‖zetaChi (s + (((-2 * (r : ℝ) : ℝ) : ℂ) + (v : ℂ) * I))‖ ≤
        C₁ * (1 + |s.im|) ^ ((2 * r : ℝ) + 1 / 2 - s.re) * (1 + |v|) ^ (2 * r + 1) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := exists_norm_zetaChi_leftStrip_rpow_le hσ0 hσ_half
  set K_lin : ℝ := ((2 * r + 1 : ℕ) : ℝ) ^ (2 * r)
  set K_pi : ℝ := (1 / (4 * Real.pi ^ 2)) ^ r
  refine ⟨K_pi * K_lin * C₀ + 1, by positivity, fun s v hlo hhi => ?_⟩
  set z : ℂ := s + (v : ℂ) * I
  have hz_re : z.re = s.re := by simp [z]
  have hz_im : z.im = s.im + v := by simp [z]
  have hz0 : 0 < z.re := by linarith
  have hz1 : z.re < 1 := by linarith
  have hshift : s + (((-2 * (r : ℝ) : ℝ) : ℂ) + (v : ℂ) * I) = z - ((2 * r : ℕ) : ℂ) := by
    dsimp only [z]; push_cast; ring
  rw [hshift, zetaChi_sub_two_mul hz0 hz1 r, norm_mul, norm_mul]
  have hnorm_pref : ‖(-1 : ℂ) ^ r / (4 * (Real.pi : ℂ) ^ 2) ^ r‖ = K_pi := by
    rw [norm_div, norm_pow, norm_neg, norm_one, one_pow, norm_pow, norm_mul,
      norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    dsimp only [K_pi]
    have h4 : ‖(4 : ℂ)‖ = 4 := by norm_num
    rw [h4, div_pow, one_pow]
  -- Bound each linear factor `‖z - (j + 1)‖` by `(2r + 1)(1 + |s.im|)(1 + |v|)`.
  have hprod_le : ‖∏ j ∈ Finset.range (2 * r), (z - ((j + 1 : ℕ) : ℂ))‖ ≤
      K_lin * (1 + |s.im|) ^ (2 * r) * (1 + |v|) ^ (2 * r) := by
    rw [norm_prod]
    have hfac : ∀ j ∈ Finset.range (2 * r),
        ‖z - ((j + 1 : ℕ) : ℂ)‖ ≤
          ((2 * r + 1 : ℕ) : ℝ) * (1 + |s.im|) * (1 + |v|) := by
      intro j hj
      have hj_lt : j < 2 * r := Finset.mem_range.mp hj
      have h1 : ‖z - ((j + 1 : ℕ) : ℂ)‖ ≤ |(z - ((j + 1 : ℕ) : ℂ)).re| + |(z - ((j + 1 : ℕ) : ℂ)).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      have hre_j : |(z - ((j + 1 : ℕ) : ℂ)).re| ≤ ((2 * r + 1 : ℕ) : ℝ) := by
        rw [Complex.sub_re, hz_re, Complex.natCast_re, abs_le]
        have hj_le : (j + 1 : ℝ) ≤ (2 * r : ℝ) := by exact_mod_cast hj_lt
        constructor <;> push_cast <;> linarith
      have him_j : |(z - ((j + 1 : ℕ) : ℂ)).im| ≤ |s.im| + |v| := by
        rw [Complex.sub_im, hz_im, Complex.natCast_im, sub_zero]
        exact abs_add_le _ _
      have hM1 : (1 : ℝ) ≤ ((2 * r + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos (2 * r)
      nlinarith [abs_nonneg s.im, abs_nonneg v, mul_nonneg (abs_nonneg s.im) (abs_nonneg v)]
    calc (∏ j ∈ Finset.range (2 * r), ‖z - ((j + 1 : ℕ) : ℂ)‖)
        ≤ ∏ _j ∈ Finset.range (2 * r), (((2 * r + 1 : ℕ) : ℝ) * (1 + |s.im|) * (1 + |v|)) :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) hfac
      _ = K_lin * (1 + |s.im|) ^ (2 * r) * (1 + |v|) ^ (2 * r) := by
          rw [Finset.prod_const, Finset.card_range, mul_pow, mul_pow]
  -- Bound `‖zetaChi z‖` by `C₀ * (1 + |s.im|)^{1/2 - s.re} * (1 + |v|)`.
  have hchi_le : ‖zetaChi z‖ ≤ C₀ * (1 + |s.im|) ^ (1 / 2 - s.re) * (1 + |v|) := by
    have hz_eq : ((s.re : ℂ) + ((s.im + v : ℝ) : ℂ) * I) = z := by
      apply Complex.ext <;> simp [z]
    have hb := hC₀ s.re (s.im + v) hlo hhi.le
    rw [hz_eq] at hb
    have hmul_iv : 1 + |s.im + v| ≤ (1 + |s.im|) * (1 + |v|) := by
      nlinarith [abs_add_le s.im v, abs_nonneg s.im, abs_nonneg v]
    have hexp_nn : 0 ≤ 1 / 2 - s.re := by linarith
    have hexp_le1 : 1 / 2 - s.re ≤ 1 := by linarith
    have hrp : (1 + |s.im + v|) ^ (1 / 2 - s.re) ≤
        (1 + |s.im|) ^ (1 / 2 - s.re) * (1 + |v|) := by
      calc (1 + |s.im + v|) ^ (1 / 2 - s.re)
          ≤ ((1 + |s.im|) * (1 + |v|)) ^ (1 / 2 - s.re) :=
            Real.rpow_le_rpow (by positivity) hmul_iv hexp_nn
        _ = (1 + |s.im|) ^ (1 / 2 - s.re) * (1 + |v|) ^ (1 / 2 - s.re) :=
            Real.mul_rpow (by positivity) (by positivity)
        _ ≤ (1 + |s.im|) ^ (1 / 2 - s.re) * (1 + |v|) ^ (1 : ℝ) :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg v]) hexp_le1) (by positivity)
        _ = (1 + |s.im|) ^ (1 / 2 - s.re) * (1 + |v|) := by rw [Real.rpow_one]
    exact hb.trans ((mul_le_mul_of_nonneg_left hrp hC₀_pos.le).trans_eq (by ring))
  rw [hnorm_pref]
  have h1sim_pos : 0 < 1 + |s.im| := by positivity
  have hrp_comb : (1 + |s.im|) ^ (2 * r) * (1 + |s.im|) ^ (1 / 2 - s.re) =
      (1 + |s.im|) ^ ((2 * r : ℝ) + 1 / 2 - s.re) := by
    rw [← Real.rpow_natCast (1 + |s.im|) (2 * r), ← Real.rpow_add h1sim_pos]
    push_cast; ring_nf
  calc K_pi * ‖∏ j ∈ Finset.range (2 * r), (z - ((j + 1 : ℕ) : ℂ))‖ * ‖zetaChi z‖
      ≤ K_pi * (K_lin * (1 + |s.im|) ^ (2 * r) * (1 + |v|) ^ (2 * r)) *
          (C₀ * (1 + |s.im|) ^ (1 / 2 - s.re) * (1 + |v|)) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hprod_le (by positivity))
          hchi_le (norm_nonneg _) (by positivity)
    _ = (K_pi * K_lin * C₀) * ((1 + |s.im|) ^ (2 * r) * (1 + |s.im|) ^ (1 / 2 - s.re)) *
          ((1 + |v|) ^ (2 * r) * (1 + |v|)) := by ring
    _ = (K_pi * K_lin * C₀) * (1 + |s.im|) ^ ((2 * r : ℝ) + 1 / 2 - s.re) *
          (1 + |v|) ^ (2 * r + 1) := by rw [hrp_comb, pow_succ]
    _ ≤ (K_pi * K_lin * C₀ + 1) * (1 + |s.im|) ^ ((2 * r : ℝ) + 1 / 2 - s.re) *
          (1 + |v|) ^ (2 * r + 1) := by
        have hpos : 0 ≤ (1 + |s.im|) ^ ((2 * r : ℝ) + 1 / 2 - s.re) * (1 + |v|) ^ (2 * r + 1) :=
          by positivity
        nlinarith

/-- **Deep negative-line contour shift for `smoothAFEZetaDualCoefficientGeneral` across ALL
`0 < Re s < 1 / 2`:** for every integer `r ≥ 1`, `x > 0`, `0 < Re s < 1 / 2`, and `n : ℕ`,
the reflected integrand `smoothAFEZetaReflectedTerm s x n` is holomorphic across
`-2r ≤ Re w ≤ -1`, shifting the integral from `Re w = -1` to `Re w = -2r` without residues. -/
theorem smoothAFEZetaDualCoefficientGeneral_eq_deep_even
    {r : ℕ} (hr : 1 ≤ r) {x : ℝ} (hx : 0 < x)
    {s : ℂ} (h0 : 0 < s.re) (h_half : s.re < 1 / 2) (n : ℕ) :
    smoothAFEZetaDualCoefficientGeneral s x n =
      (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
        ∫ v : ℝ, smoothAFEZetaReflectedTerm s x n
          (((-2 * (r : ℝ) : ℝ) : ℂ) + (v : ℂ) * I) := by
  have h1 : s.re < 1 := by linarith
  set c : ℝ := -2 * (r : ℝ)
  have hcd : c ≤ -1 := by
    dsimp only [c]
    have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  have hc_ne : c ≠ 0 := by linarith
  -- Representation at `d = -1`.
  have heq_m1 : smoothAFEZetaDualCoefficientGeneral s x n =
      (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
        ∫ v : ℝ, smoothAFEZetaReflectedTerm s x n (((-1 : ℝ) : ℂ) + (v : ℂ) * I) := by
    unfold smoothAFEZetaDualCoefficientGeneral smoothAFEZetaDualCutoffGeneral
    rw [Complex.real_smul, show (((-1 : ℝ) : ℂ)) = (-1 : ℂ) by norm_num]
    calc (zetaChi s * (n + 1 : ℂ) ^ (s - 1)) *
          ((((1 / (2 * Real.pi) : ℝ) : ℂ)) *
            ∫ v : ℝ, smoothAFEDualRatioIntegrand s (1 / ((n + 1 : ℝ) * x)) ((-1 : ℂ) + (v : ℂ) * I))
        = (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
            ((zetaChi s * (n + 1 : ℂ) ^ (s - 1)) *
              ∫ v : ℝ, smoothAFEDualRatioIntegrand s (1 / ((n + 1 : ℝ) * x)) ((-1 : ℂ) + (v : ℂ) * I)) := by ring
      _ = (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
            ∫ v : ℝ, smoothAFEZetaReflectedTerm s x n ((-1 : ℂ) + (v : ℂ) * I) := by
          rw [integral_smoothAFEZetaReflectedTerm_general_left_one_eq hx h0 h1]
  rw [heq_m1]
  congr 1
  -- Holomorphy on `verticalStrip c (-1)`.
  set G : ℂ → ℂ := smoothAFEZetaReflectedTerm s x n
  have hG_eq : G = fun w =>
      zetaChi (s + w) * (n + 1 : ℂ) ^ (s + w - 1) * (x : ℂ) ^ w * smoothAFEGaussianKernel w := by
    funext w; exact smoothAFEZetaReflectedTerm_eq_cpow s x n w
  have hdiff : DifferentiableOn ℂ G (GaloisForLFunctions.HTGeometry.verticalStrip c (-1)) := by
    intro w hw
    rw [GaloisForLFunctions.HTGeometry.mem_verticalStrip] at hw
    have hw_ne0 : w ≠ 0 := fun h => by rw [h] at hw; norm_num at hw
    haveI : NeZero (x : ℂ) := ⟨Complex.ofReal_ne_zero.mpr hx.ne'⟩
    have hn_ne0 : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    letI : NeZero (n + 1 : ℂ) := ⟨hn_ne0⟩
    have hG_re : 0 < (1 - (s + w)).re := by simp; linarith [hw.2]
    have hd_chi : DifferentiableAt ℂ (fun u => zetaChi (s + u)) w :=
      (zetaChi_analyticAt (Complex.Gammaℝ_ne_zero_of_re_pos hG_re)).differentiableAt.comp w
        (differentiableAt_const s |>.add differentiableAt_id)
    have hd_n : DifferentiableAt ℂ (fun u => (n + 1 : ℂ) ^ (s + u - 1)) w :=
      (differentiable_const_cpow_of_neZero (n + 1 : ℂ)).differentiableAt.comp w
        ((differentiableAt_const s |>.add differentiableAt_id).sub_const 1)
    have hd_x : DifferentiableAt ℂ (fun u => (x : ℂ) ^ u) w :=
      (differentiable_const_cpow_of_neZero (x : ℂ)).differentiableAt
    have hd_ker : DifferentiableAt ℂ smoothAFEGaussianKernel w := by
      unfold smoothAFEGaussianKernel
      exact ((differentiable_exp.comp (differentiable_pow 2)).differentiableAt).div
        differentiableAt_id hw_ne0
    rw [hG_eq]
    exact (((hd_chi.mul hd_n).mul hd_x).mul hd_ker).differentiableWithinAt
  -- Integrability at `c = -2r`.
  obtain ⟨C₁, hC₁_pos, hC₁⟩ := exists_norm_zetaChi_deep_even_le (σ_min := s.re / 2)
    (by linarith) (by linarith) r
  have hc_int : Integrable (fun v : ℝ => G ((c : ℂ) + (v : ℝ) * I)) := by
    set D_c : ℝ := C₁ * (1 + |s.im|) ^ ((2 * r : ℝ) + 1 / 2 - s.re) *
      (n + 1 : ℝ) ^ (s.re + c - 1) * x ^ c * (Real.exp (c ^ 2) / |c|)
    refine Integrable.mono'
      ((integrable_shifted_pow_mul_exp_neg_sq 1 (2 * r + 1)).const_mul D_c) ?_ ?_
    · haveI : NeZero (x : ℂ) := ⟨Complex.ofReal_ne_zero.mpr hx.ne'⟩
      have hn_ne0 : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      letI : NeZero (n + 1 : ℂ) := ⟨hn_ne0⟩
      let w : ℝ → ℂ := fun v => (c : ℂ) + (v : ℂ) * I
      have hw : Continuous w := by dsimp only [w]; fun_prop
      have hchi : Continuous (fun v : ℝ => zetaChi (s + w v)) := by
        rw [continuous_iff_continuousAt]; intro v
        refine (zetaChi_analyticAt ?_).continuousAt.comp (by dsimp only [w]; fun_prop)
        apply Complex.Gammaℝ_ne_zero_of_re_pos
        dsimp only [w]; simp; linarith
      have hker : Continuous (fun v : ℝ => smoothAFEGaussianKernel (w v)) := by
        unfold smoothAFEGaussianKernel
        exact (Complex.continuous_exp.comp (hw.pow 2)).div hw fun v h0w => by
          have := congrArg Complex.re h0w; dsimp only [w] at this; simp at this; exact hc_ne this
      have hcont : Continuous (fun v : ℝ => G ((c : ℂ) + (v : ℝ) * I)) := by
        rw [hG_eq]
        exact (((hchi.mul ((continuous_const_cpow (n + 1 : ℂ)).comp (by fun_prop))).mul
          ((continuous_const_cpow (x : ℂ)).comp hw)).mul hker)
      exact hcont.aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun v => ?_
      have hn_pos : (0 : ℝ) < n + 1 := by exact_mod_cast Nat.succ_pos n
      have hchi_v := hC₁ s v (by linarith) h_half
      have hker_v := norm_smoothAFEGaussianKernel_vertical_le_of_ne (σ := c) hc_ne v
      rw [hG_eq]
      dsimp only
      rw [norm_mul, norm_mul, norm_mul,
        show (n : ℂ) + 1 = ((n + 1 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_cpow_eq_rpow_re_of_pos hn_pos,
        Complex.norm_cpow_eq_rpow_re_of_pos hx]
      have hre_n : (s + ((c : ℂ) + (v : ℂ) * I) - 1).re = s.re + c - 1 := by simp
      have hre_x : (((c : ℂ) + (v : ℂ) * I).re) = c := by simp
      rw [hre_n, hre_x]
      calc ‖zetaChi (s + ((c : ℂ) + (v : ℂ) * I))‖ *
            (n + 1 : ℝ) ^ (s.re + c - 1) * x ^ c *
            ‖smoothAFEGaussianKernel ((c : ℂ) + (v : ℂ) * I)‖
          ≤ (C₁ * (1 + |s.im|) ^ ((2 * r : ℝ) + 1 / 2 - s.re) * (1 + |v|) ^ (2 * r + 1)) *
              (n + 1 : ℝ) ^ (s.re + c - 1) * x ^ c *
              ((Real.exp (c ^ 2) / |c|) * Real.exp (-(v ^ 2))) := by
            gcongr
        _ = D_c * ((1 + |v|) ^ (2 * r + 1) * Real.exp (-(v ^ 2))) := by
            dsimp only [D_c]; ring
  -- Integrability at `d = -1`.
  have hd_int : Integrable (fun v : ℝ => G (((-1 : ℝ) : ℂ) + (v : ℝ) * I)) := by
    simpa [G] using smoothAFEZetaReflectedTerm_general_left_one_integrable hx h0 h1 n
  -- Horizontal segments `c..-1` at `± i T` vanish via `hasStripPolyGrowthOffReal_zetaChi`.
  obtain ⟨T₀_s, N_s, C_s, hCs_pos, hchi_strip⟩ :=
    hasStripPolyGrowthOffReal_zetaChi (s.re + c) (s.re - 1)
  have hhoriz_shift : ∀ ε : ℝ, |ε| = 1 →
      Tendsto (fun T : ℝ => ∫ u : ℝ in c..(-1 : ℝ), G ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I))
        atTop (𝓝 0) := by
    intro ε hε
    set X_bd : ℝ := max (x ^ c) (x ^ (-1 : ℝ))
    set K_sh : ℝ := C_s * X_bd * Real.exp (c ^ 2)
    refine GaloisForLFunctions.HTGeometry.tendsto_intervalIntegral_of_tendsto_bound
      (M := fun T => K_sh * (((1 + |s.im|) + T) ^ N_s * Real.exp (-(T ^ (2 : ℕ)))))
      (hgt := fun T => ε * T) ?_
      (by simpa using (tendsto_shifted_pow_mul_exp_neg_sq (1 + |s.im|) N_s).const_mul K_sh)
    filter_upwards [eventually_ge_atTop (max 1 (|T₀_s| + |s.im| + 2))] with T hT u hu
    rw [Set.uIoc_of_le hcd] at hu
    have hT1 : 1 ≤ T := (le_max_left _ _).trans hT
    have hT_big : |T₀_s| + |s.im| + 2 ≤ T := (le_max_right _ _).trans hT
    have habsv : |ε * T| = T := by rw [abs_mul, hε, one_mul, abs_of_pos (zero_lt_one.trans_le hT1)]
    set w : ℂ := (u : ℂ) + ((ε * T : ℝ) : ℂ) * I
    have hsw_re1 : s.re + c ≤ (s + w).re := by simp [w]; linarith [hu.1.le]
    have hsw_re2 : (s + w).re ≤ s.re - 1 := by simp [w]; linarith [hu.2]
    have hsw_im_ge : T₀_s ≤ |(s + w).im| := by
      rw [Complex.add_im, show w.im = ε * T by simp [w]]
      have htri : |ε * T| - |s.im| ≤ |s.im + ε * T| := by
        have h := abs_sub_abs_le_abs_sub (ε * T) (-s.im)
        simpa [abs_neg, sub_neg_eq_add, add_comm] using h
      linarith [le_abs_self T₀_s]
    have hsw_im_le : 1 + |(s + w).im| ≤ (1 + |s.im|) + T := by
      calc 1 + |(s + w).im|
          = 1 + |s.im + ε * T| := by rw [Complex.add_im, show w.im = ε * T by simp [w]]
        _ ≤ 1 + (|s.im| + |ε * T|) := by linarith [abs_add_le s.im (ε * T)]
        _ = (1 + |s.im|) + T := by rw [habsv]; ring
    have hchi_bd : ‖zetaChi (s + w)‖ ≤ C_s * ((1 + |s.im|) + T) ^ N_s :=
      (hchi_strip (s + w) hsw_re1 hsw_re2 hsw_im_ge).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hsw_im_le N_s) hCs_pos)
    have hn_le1 : ‖(n + 1 : ℂ) ^ (s + w - 1)‖ ≤ 1 := by
      have hn_pos : (0 : ℝ) < n + 1 := by exact_mod_cast Nat.succ_pos n
      rw [show (n : ℂ) + 1 = ((n + 1 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_cpow_eq_rpow_re_of_pos hn_pos]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast Nat.succ_pos n)
        (by simp [w]; linarith [hu.2])
    have hx_le : ‖(x : ℂ) ^ w‖ ≤ X_bd := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, show w.re = u by simp [w]]
      rcases le_total 1 x with h1x | h1x
      · exact (Real.rpow_le_rpow_of_exponent_le h1x hu.2).trans (le_max_right _ _)
      · exact (Real.rpow_le_rpow_of_exponent_ge hx h1x hu.1.le).trans (le_max_left _ _)
    have hker_le : ‖smoothAFEGaussianKernel w‖ ≤ Real.exp (c ^ 2) * Real.exp (-(T ^ (2 : ℕ))) := by
      rw [smoothAFEGaussianKernel, norm_div, Complex.norm_exp]
      have hw_re_sq : (w ^ 2).re = u ^ 2 - T ^ (2 : ℕ) := by
        dsimp only [w]
        simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
        have hε2 : ε * ε = 1 := by
          have := sq_abs ε; rw [hε] at this; nlinarith
        nlinarith
      have hu2 : u ^ 2 ≤ c ^ 2 := by nlinarith [hu.1.le, hu.2]
      have hwnorm1 : 1 ≤ ‖w‖ := by
        calc (1 : ℝ) ≤ T := hT1
          _ = |w.im| := by simp [w, habsv]
          _ ≤ ‖w‖ := Complex.abs_im_le_norm w
      rw [hw_re_sq]
      exact (div_le_self (Real.exp_nonneg _) hwnorm1).trans
        (by rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith))
    rw [hG_eq]
    dsimp only [K_sh]
    rw [norm_mul, norm_mul, norm_mul]
    have hX_nn : 0 ≤ X_bd := (Real.rpow_nonneg hx.le c).trans (le_max_left _ _)
    calc ‖zetaChi (s + w)‖ * ‖(n + 1 : ℂ) ^ (s + w - 1)‖ * ‖(x : ℂ) ^ w‖ * ‖smoothAFEGaussianKernel w‖
        ≤ (C_s * ((1 + |s.im|) + T) ^ N_s) * 1 * X_bd * (Real.exp (c ^ 2) * Real.exp (-(T ^ (2 : ℕ)))) := by
          refine mul_le_mul (mul_le_mul (mul_le_mul hchi_bd hn_le1 (norm_nonneg _) (by positivity))
            hx_le (norm_nonneg _) (by positivity)) hker_le (norm_nonneg _) (by positivity)
      _ = (C_s * X_bd * Real.exp (c ^ 2)) * (((1 + |s.im|) + T) ^ N_s * Real.exp (-(T ^ (2 : ℕ)))) := by ring
  have hbot_sh : Tendsto (fun T : ℝ => ∫ u : ℝ in c..(-1 : ℝ), G ((u : ℂ) + ((-T : ℝ) : ℂ) * I))
      atTop (𝓝 0) := by
    simpa [neg_one_mul] using hhoriz_shift (-1) (by norm_num)
  have htop_sh : Tendsto (fun T : ℝ => ∫ u : ℝ in c..(-1 : ℝ), G ((u : ℂ) + ((T : ℝ) : ℂ) * I))
      atTop (𝓝 0) := by
    simpa [one_mul] using hhoriz_shift 1 (by norm_num)
  exact GaloisForLFunctions.HTGeometry.integral_vertical_line_eq_of_horizontal_tendsto
    hcd hdiff hc_int hd_int hbot_sh htop_sh

/-- **Uniform `s`-explicit deep coefficient and tail bound on `smoothAFEZetaDualCoefficientGeneral`:**
for every `0 < σ_min ≤ 1 / 2` and `r ≥ 1`, there exists `K_dual > 0` depending **only** on
`(σ_min, r)` (independent of `s`, `x`, `n`, and `L`) bounding both the `n`-th dual coefficient and
the tail sum past `L`. -/
theorem exists_norm_smoothAFEZetaDualCoefficientGeneral_deep_le
    {σ_min : ℝ} (hσ0 : 0 < σ_min) (hσ_half : σ_min ≤ 1 / 2) {r : ℕ} (hr : 1 ≤ r) :
    ∃ K_dual : ℝ, 0 < K_dual ∧
      ∀ (s : ℂ) (x : ℝ), σ_min ≤ s.re → s.re < 1 / 2 → 0 < x →
        (∀ n : ℕ, ‖smoothAFEZetaDualCoefficientGeneral s x n‖ ≤
          K_dual * x ^ (-2 * (r : ℝ)) * (1 + |s.im|) ^ ((2 * r : ℝ) + 1 / 2 - s.re) *
            (n + 1 : ℝ) ^ (-(2 * (r : ℝ) + 1 - s.re))) ∧
        (∀ L : ℕ, 1 ≤ L →
          ∑' j : ℕ, ‖smoothAFEZetaDualCoefficientGeneral s x (j + L)‖ ≤
            K_dual * x ^ (-2 * (r : ℝ)) * (1 + |s.im|) ^ ((2 * r : ℝ) + 1 / 2 - s.re) *
              (L : ℝ) ^ (s.re - 2 * (r : ℝ))) := by
  obtain ⟨C₁, hC₁_pos, hC₁⟩ := exists_norm_zetaChi_deep_even_le hσ0 hσ_half r
  set c : ℝ := -2 * (r : ℝ)
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hc_ne : c ≠ 0 := by dsimp only [c]; linarith
  have hgauss_int : Integrable (fun v : ℝ => (1 + |v|) ^ (2 * r + 1) * Real.exp (-(v ^ 2))) :=
    integrable_shifted_pow_mul_exp_neg_sq 1 (2 * r + 1)
  set G_int : ℝ := ∫ v : ℝ, (1 + |v|) ^ (2 * r + 1) * Real.exp (-(v ^ 2))
  have hG_nn : 0 ≤ G_int := integral_nonneg fun _ => by positivity
  set K_dual : ℝ := (1 / (2 * Real.pi)) * C₁ * (Real.exp (c ^ 2) / |c|) * G_int + 1
  refine ⟨K_dual, by positivity, fun s x hlo hhi hx => ?_⟩
  have hs0 : 0 < s.re := hσ0.trans_le hlo
  have hcoeff : ∀ n : ℕ, ‖smoothAFEZetaDualCoefficientGeneral s x n‖ ≤
      K_dual * x ^ (-2 * (r : ℝ)) * (1 + |s.im|) ^ ((2 * r : ℝ) + 1 / 2 - s.re) *
        (n + 1 : ℝ) ^ (-(2 * (r : ℝ) + 1 - s.re)) := by
    intro n
    rw [smoothAFEZetaDualCoefficientGeneral_eq_deep_even hr hx hs0 hhi n,
      norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
    set D_n : ℝ := C₁ * (1 + |s.im|) ^ ((2 * r : ℝ) + 1 / 2 - s.re) *
      (n + 1 : ℝ) ^ (-(2 * (r : ℝ) + 1 - s.re)) * x ^ (-2 * (r : ℝ)) * (Real.exp (c ^ 2) / |c|)
    have hpt : ∀ v : ℝ,
        ‖smoothAFEZetaReflectedTerm s x n ((c : ℂ) + (v : ℂ) * I)‖ ≤
          D_n * ((1 + |v|) ^ (2 * r + 1) * Real.exp (-(v ^ 2))) := by
      intro v
      have hn_pos : (0 : ℝ) < n + 1 := by exact_mod_cast Nat.succ_pos n
      have hchi_v := hC₁ s v hlo hhi
      have hker_v := norm_smoothAFEGaussianKernel_vertical_le_of_ne (σ := c) hc_ne v
      rw [smoothAFEZetaReflectedTerm_eq_cpow, norm_mul, norm_mul, norm_mul,
        show (n : ℂ) + 1 = ((n + 1 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_cpow_eq_rpow_re_of_pos hn_pos,
        Complex.norm_cpow_eq_rpow_re_of_pos hx]
      have hre_n : (s + ((c : ℂ) + (v : ℂ) * I) - 1).re = -(2 * (r : ℝ) + 1 - s.re) := by
        dsimp only [c]; simp; ring
      have hre_x : (((c : ℂ) + (v : ℂ) * I).re) = -2 * (r : ℝ) := by dsimp only [c]; simp
      rw [hre_n, hre_x]
      calc ‖zetaChi (s + ((c : ℂ) + (v : ℂ) * I))‖ *
            (n + 1 : ℝ) ^ (-(2 * (r : ℝ) + 1 - s.re)) * x ^ (-2 * (r : ℝ)) *
            ‖smoothAFEGaussianKernel ((c : ℂ) + (v : ℂ) * I)‖
          ≤ (C₁ * (1 + |s.im|) ^ ((2 * r : ℝ) + 1 / 2 - s.re) * (1 + |v|) ^ (2 * r + 1)) *
              (n + 1 : ℝ) ^ (-(2 * (r : ℝ) + 1 - s.re)) * x ^ (-2 * (r : ℝ)) *
              ((Real.exp (c ^ 2) / |c|) * Real.exp (-(v ^ 2))) := by gcongr
        _ = D_n * ((1 + |v|) ^ (2 * r + 1) * Real.exp (-(v ^ 2))) := by dsimp only [D_n]; ring
    have hint_le : ‖∫ v : ℝ, smoothAFEZetaReflectedTerm s x n ((c : ℂ) + (v : ℂ) * I)‖ ≤
        D_n * G_int := by
      have h0 := norm_integral_le_of_norm_le (hgauss_int.const_mul D_n) (Filter.Eventually.of_forall hpt)
      rwa [MeasureTheory.integral_const_mul] at h0
    calc (1 / (2 * Real.pi)) * ‖∫ v : ℝ, smoothAFEZetaReflectedTerm s x n ((c : ℂ) + (v : ℂ) * I)‖
        ≤ (1 / (2 * Real.pi)) * (D_n * G_int) :=
          mul_le_mul_of_nonneg_left hint_le (by positivity)
      _ = ((1 / (2 * Real.pi)) * C₁ * (Real.exp (c ^ 2) / |c|) * G_int) *
            x ^ (-2 * (r : ℝ)) * (1 + |s.im|) ^ ((2 * r : ℝ) + 1 / 2 - s.re) *
            (n + 1 : ℝ) ^ (-(2 * (r : ℝ) + 1 - s.re)) := by dsimp only [D_n]; ring
      _ ≤ K_dual * x ^ (-2 * (r : ℝ)) * (1 + |s.im|) ^ ((2 * r : ℝ) + 1 / 2 - s.re) *
            (n + 1 : ℝ) ^ (-(2 * (r : ℝ) + 1 - s.re)) := by
          have hfac_nn : 0 ≤ x ^ (-2 * (r : ℝ)) * (1 + |s.im|) ^ ((2 * r : ℝ) + 1 / 2 - s.re) *
              (n + 1 : ℝ) ^ (-(2 * (r : ℝ) + 1 - s.re)) := by positivity
          dsimp only [K_dual]
          nlinarith
  refine ⟨hcoeff, fun L hL => ?_⟩
  set P_s : ℝ := 2 * (r : ℝ) + 1 - s.re
  have hP1 : 1 < P_s := by dsimp only [P_s]; linarith
  set A_pre : ℝ := K_dual * x ^ (-2 * (r : ℝ)) * (1 + |s.im|) ^ ((2 * r : ℝ) + 1 / 2 - s.re)
  have hA_nn : 0 ≤ A_pre := by dsimp only [A_pre]; positivity
  have hmaj : Summable (fun j : ℕ => A_pre * (((j + L + 1 : ℕ) : ℝ) ^ (-P_s))) := by
    refine Summable.mul_left _ ?_
    have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-P_s)) := by
      rw [Real.summable_nat_rpow]; linarith
    exact ((summable_nat_add_iff (L + 1)).mpr hbase).congr fun j => by
      push_cast; congr 1; ring
  have hterm_le : ∀ j : ℕ,
      ‖smoothAFEZetaDualCoefficientGeneral s x (j + L)‖ ≤
        A_pre * (((j + L + 1 : ℕ) : ℝ) ^ (-P_s)) := by
    intro j
    simpa only [A_pre, P_s, Nat.cast_add, Nat.cast_one] using hcoeff (j + L)
  have hsum_j := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm_le hmaj
  have hden_ge1 : 1 ≤ P_s - 1 := by dsimp only [P_s]; linarith
  calc (∑' j : ℕ, ‖smoothAFEZetaDualCoefficientGeneral s x (j + L)‖)
      ≤ ∑' j : ℕ, A_pre * (((j + L + 1 : ℕ) : ℝ) ^ (-P_s)) := hsum_j.tsum_le_tsum hterm_le hmaj
    _ = A_pre * ∑' j : ℕ, (((j + L + 1 : ℕ) : ℝ) ^ (-P_s)) := tsum_mul_left
    _ ≤ A_pre * ((L : ℝ) ^ (1 - P_s) / (P_s - 1)) :=
        mul_le_mul_of_nonneg_left (Sieve.tsum_tail_rpow_neg_le hP1 hL) hA_nn
    _ ≤ A_pre * (L : ℝ) ^ (1 - P_s) :=
        mul_le_mul_of_nonneg_left (div_le_self (Real.rpow_nonneg (Nat.cast_nonneg L) _) hden_ge1) hA_nn
    _ = K_dual * x ^ (-2 * (r : ℝ)) * (1 + |s.im|) ^ ((2 * r : ℝ) + 1 / 2 - s.re) *
          (L : ℝ) ^ (s.re - 2 * (r : ℝ)) := by
        dsimp only [A_pre, P_s]
        rw [show 1 - (2 * (r : ℝ) + 1 - s.re) = s.re - 2 * (r : ℝ) by ring]

/-- Finite cross-height Gaussian two-head witness of length `L` at scale `x` (without pole term). -/
def crossHeightDirichletWitness
    (a b : ℕ → ℂ) (Q : ℝ) (ω : ℂ) (s : ℂ) (x : ℝ) (L : ℕ) : ℂ :=
  (∑ n ∈ Finset.range L,
      a (n + 1) * (((n + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / x))) -
    ω * (Q : ℂ) ^ ((1 / 2 : ℂ) - s) *
      (∑ m ∈ Finset.range L, b (m + 1) * smoothAFEZetaDualCoefficientGeneral s (x / Q) m)

/-- **Uniform `(r, x, L)` truncation bound for `crossHeightDirichletWitness` across `[σ_min, 1 / 2)`:**
for every `0 < σ_min ≤ 1 / 2`, `r ≥ 1`, and `(F, a, b, R, Q, ω)` satisfying
`UnitPoleFreeCrossHeightDatum`, there exist `C_dir ≥ 0` and `K_dual > 0` depending **only** on
`(σ_min, r)` bounding `‖F(s) - crossHeightDirichletWitness a b Q ω s x L‖` across all
`σ_min ≤ Re s < 1 / 2`, `x > 0`, and `L ≥ 1`. -/
theorem crossHeightDirichletWitness_sub_le
    {σ_min : ℝ} (hσ0 : 0 < σ_min) (hσ_half : σ_min ≤ 1 / 2)
    {r : ℕ} (hr : 1 ≤ r)
    {F : ℂ → ℂ} {a b : ℕ → ℂ} {R : ℂ} {Q : ℝ} {ω : ℂ}
    (hD : UnitPoleFreeCrossHeightDatum F a b R Q ω) :
    ∃ C_dir K_dual : ℝ, 0 ≤ C_dir ∧ 0 < K_dual ∧
      ∀ (s : ℂ) (x : ℝ) (L : ℕ),
        σ_min ≤ s.re → s.re < 1 / 2 → 0 < x → 1 ≤ L →
          ‖F s - crossHeightDirichletWitness a b Q ω s x L‖ ≤
            C_dir * x ^ (2 * (r : ℝ)) * (L : ℝ) ^ (1 - (s.re + 2 * (r : ℝ))) +
              ‖ω * (Q : ℂ) ^ ((1 / 2 : ℂ) - s)‖ *
                (K_dual * (x / Q) ^ (-2 * (r : ℝ)) *
                  (1 + |s.im|) ^ ((2 * r : ℝ) + 1 / 2 - s.re) *
                  (L : ℝ) ^ (s.re - 2 * (r : ℝ))) +
              ‖R * smoothAFEZetaShiftedPoleResidue s x‖ := by
  have hr1R : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have h2r_pos : (0 : ℝ) < 2 * (r : ℝ) := by linarith
  obtain ⟨C_dir, hC_dir0, hC_dir⟩ := exists_smoothAFE_direct_tail_le h2r_pos
  obtain ⟨K_dual, hK_dual_pos, hK_dual⟩ :=
    exists_norm_smoothAFEZetaDualCoefficientGeneral_deep_le hσ0 hσ_half hr
  refine ⟨C_dir, K_dual, hC_dir0, hK_dual_pos, fun s x L hlo hhi hx hL1 => ?_⟩
  have hs0 : 0 < s.re := hσ0.trans_le hlo
  have hsA : 1 < s.re + 2 * (r : ℝ) := by linarith
  have hxQ_pos : 0 < x / Q := div_pos hx hD.Q_pos
  rw [crossHeight_gaussian_two_tsum_eq hD hx hs0 hhi]
  have hbase_dir := summable_smoothAFE_direct h2r_pos hx hsA
  have hsum_dir : Summable (fun n : ℕ =>
      a (n + 1) * (((n + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / x))) := by
    refine Summable.of_norm_bounded hbase_dir.norm fun n => ?_
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hD.unit_a (n + 1) (Nat.succ_pos n))
  have hsum_dual_zeta : Summable (fun m : ℕ => smoothAFEZetaDualCoefficientGeneral s (x / Q) m) := by
    obtain ⟨Kd0, _, hKd0⟩ := exists_norm_smoothAFEZetaDualCoefficientGeneral_le hxQ_pos hs0 (by linarith)
    exact Summable.of_norm_bounded
      ((summable_smoothAFEZetaMajorant (p := 2 - s.re) (by linarith)).mul_left Kd0) hKd0
  have hsum_dual : Summable (fun m : ℕ =>
      b (m + 1) * smoothAFEZetaDualCoefficientGeneral s (x / Q) m) := by
    refine Summable.of_norm_bounded hsum_dual_zeta.norm fun m => ?_
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hD.unit_b (m + 1) (Nat.succ_pos m))
  unfold crossHeightGaussianTwoSeries crossHeightDirichletWitness
  rw [← hsum_dir.sum_add_tsum_nat_add L, ← hsum_dual.sum_add_tsum_nat_add L]
  have halg :
      ((∑ n ∈ Finset.range L,
            a (n + 1) * (((n + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / x)) +
          ∑' j : ℕ, a (j + L + 1) *
            (((j + L + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((j + L + 1 : ℕ) : ℝ) / x))) -
        ω * (Q : ℂ) ^ ((1 / 2 : ℂ) - s) *
          (∑ m ∈ Finset.range L, b (m + 1) * smoothAFEZetaDualCoefficientGeneral s (x / Q) m +
            ∑' j : ℕ, b (j + L + 1) * smoothAFEZetaDualCoefficientGeneral s (x / Q) (j + L)) -
        R * smoothAFEZetaShiftedPoleResidue s x) -
      ((∑ n ∈ Finset.range L,
            a (n + 1) * (((n + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / x))) -
        ω * (Q : ℂ) ^ ((1 / 2 : ℂ) - s) *
          ∑ m ∈ Finset.range L, b (m + 1) * smoothAFEZetaDualCoefficientGeneral s (x / Q) m) =
      ((∑' j : ℕ, a (j + L + 1) *
            (((j + L + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((j + L + 1 : ℕ) : ℝ) / x))) -
        ω * (Q : ℂ) ^ ((1 / 2 : ℂ) - s) *
          (∑' j : ℕ, b (j + L + 1) * smoothAFEZetaDualCoefficientGeneral s (x / Q) (j + L))) -
        R * smoothAFEZetaShiftedPoleResidue s x := by
    ring
  rw [halg]
  have hshift_z : Summable (fun j : ℕ =>
      ‖(((j + L + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((j + L + 1 : ℕ) : ℝ) / x))‖) :=
    (summable_nat_add_iff
      (f := fun n : ℕ => ‖(((n + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / x))‖) L).mpr
      hbase_dir.norm
  have hpt_j : ∀ j : ℕ,
      ‖a (j + L + 1) * (((j + L + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((j + L + 1 : ℕ) : ℝ) / x))‖ ≤
        ‖(((j + L + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((j + L + 1 : ℕ) : ℝ) / x))‖ := fun j => by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hD.unit_a _ (by omega))
  have hsum_td := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt_j hshift_z
  have hden1 : 1 ≤ s.re + 2 * (r : ℝ) - 1 := by linarith
  have hbd1 : ‖∑' j : ℕ, a (j + L + 1) *
      (((j + L + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((j + L + 1 : ℕ) : ℝ) / x))‖ ≤
      C_dir * x ^ (2 * (r : ℝ)) * (L : ℝ) ^ (1 - (s.re + 2 * (r : ℝ))) :=
    (norm_tsum_le_tsum_norm hsum_td).trans ((hsum_td.tsum_le_tsum hpt_j hshift_z).trans
      ((hC_dir s x hx hsA L hL1).trans (mul_le_mul_of_nonneg_left
        (div_le_self (Real.rpow_nonneg (Nat.cast_nonneg L) _) hden1) (by positivity))))
  have hshift_du : Summable (fun j : ℕ =>
      ‖smoothAFEZetaDualCoefficientGeneral s (x / Q) (j + L)‖) :=
    (summable_nat_add_iff
      (f := fun m : ℕ => ‖smoothAFEZetaDualCoefficientGeneral s (x / Q) m‖) L).mpr
      hsum_dual_zeta.norm
  have hpt_du : ∀ j : ℕ,
      ‖b (j + L + 1) * smoothAFEZetaDualCoefficientGeneral s (x / Q) (j + L)‖ ≤
        ‖smoothAFEZetaDualCoefficientGeneral s (x / Q) (j + L)‖ := fun j => by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hD.unit_b _ (by omega))
  have hsum_tdu := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt_du hshift_du
  have hbd2 : ‖ω * (Q : ℂ) ^ ((1 / 2 : ℂ) - s) *
      ∑' j : ℕ, b (j + L + 1) * smoothAFEZetaDualCoefficientGeneral s (x / Q) (j + L)‖ ≤
      ‖ω * (Q : ℂ) ^ ((1 / 2 : ℂ) - s)‖ *
        (K_dual * (x / Q) ^ (-2 * (r : ℝ)) *
          (1 + |s.im|) ^ ((2 * r : ℝ) + 1 / 2 - s.re) *
          (L : ℝ) ^ (s.re - 2 * (r : ℝ))) := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      ((norm_tsum_le_tsum_norm hsum_tdu).trans ((hsum_tdu.tsum_le_tsum hpt_du hshift_du).trans
        ((hK_dual s (x / Q) hlo hhi hxQ_pos).2 L hL1)))
      (norm_nonneg _)
  have ht1 := norm_sub_le
    ((∑' j : ℕ, a (j + L + 1) *
        (((j + L + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((j + L + 1 : ℕ) : ℝ) / x))) -
      ω * (Q : ℂ) ^ ((1 / 2 : ℂ) - s) *
        ∑' j : ℕ, b (j + L + 1) * smoothAFEZetaDualCoefficientGeneral s (x / Q) (j + L))
    (R * smoothAFEZetaShiftedPoleResidue s x)
  have ht2 := norm_sub_le
    (∑' j : ℕ, a (j + L + 1) *
      (((j + L + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((j + L + 1 : ℕ) : ℝ) / x)))
    (ω * (Q : ℂ) ^ ((1 / 2 : ℂ) - s) *
      ∑' j : ℕ, b (j + L + 1) * smoothAFEZetaDualCoefficientGeneral s (x / Q) (j + L))
  linarith

/-- **Sublinear `O(|Im s|^{1/2 + η})` cross-height Gaussian witness theorem across ALL of `Ω_open`:**
for every `(F, a, b, R, Q, ω)` satisfying `UnitPoleFreeCrossHeightDatum`, every sublinear excess
exponent `η ∈ (0, 1 / 2)`, and every target decay power `B > 0`, there exists an explicit finite
constant `E > 0` such that at **every** point `s` in `3001 / 24000 ≤ Re s < 1 / 2`, `184 < |Im s|`,
the finite cross-height witness at scale `x = √|Im s|` and sublinear length
`L = max 2 ⌈|Im s|^{1/2 + η}⌉₊ = o(|Im s|)` approximates `F(s)` within `E |Im s|^{-B}`. -/
theorem exists_sublinear_crossHeight_witness_bound_on_remaining_strip
    {F : ℂ → ℂ} {a b : ℕ → ℂ} {R : ℂ} {Q : ℝ} {ω : ℂ}
    (hD : UnitPoleFreeCrossHeightDatum F a b R Q ω)
    {η : ℝ} (hη0 : 0 < η) (hη_half : η < 1 / 2)
    {B : ℝ} (hB : 0 < B) :
    ∃ E : ℝ, 0 < E ∧
      ∀ s : ℂ, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 184 < |s.im| →
        ‖F s - crossHeightDirichletWitness a b Q ω s
            (Real.sqrt |s.im|) (max 2 (Nat.ceil (|s.im| ^ (1 / 2 + η))))‖ ≤
          E * |s.im| ^ (-B) := by
  obtain ⟨r, hr1, hr_eta⟩ : ∃ r : ℕ, 1 ≤ r ∧ B + 1 ≤ 2 * (r : ℝ) * η := by
    refine ⟨max 1 (Nat.ceil ((B + 1) / (2 * η))), le_max_left _ _, ?_⟩
    have hceil : (B + 1) / (2 * η) ≤ (Nat.ceil ((B + 1) / (2 * η)) : ℝ) := Nat.le_ceil _
    have hr_ge : (Nat.ceil ((B + 1) / (2 * η)) : ℝ) ≤ ((max 1 (Nat.ceil ((B + 1) / (2 * η))) : ℕ) : ℝ) := by
      exact_mod_cast le_max_right 1 _
    have h2η : 0 < 2 * η := by linarith
    have h := (div_le_iff₀ h2η).mp (hceil.trans hr_ge)
    linarith
  have hr1R : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  obtain ⟨C_dir, K_dual, hC_dir0, hK_dual_pos, htrunc⟩ :=
    crossHeightDirichletWitness_sub_le (σ_min := 3001 / 24000) (by norm_num) (by norm_num) hr1 hD
  obtain ⟨M_B, hMB_gt⟩ : ∃ M_B : ℕ, B + 1 ≤ (M_B : ℝ) := by
    refine ⟨Nat.ceil B + 1, ?_⟩
    have hc : B ≤ (Nat.ceil B : ℝ) := Nat.le_ceil B
    push_cast; linarith
  have hQ_pos : 0 < Q := hD.Q_pos
  obtain ⟨Q_fac, hQ_fac_pos, hQ_fac_eq⟩ :
      ∃ Q_fac : ℝ, 0 < Q_fac ∧ Q_fac = max 1 (Q ^ (1 / 2 : ℝ)) * Q ^ (2 * (r : ℝ)) :=
    ⟨max 1 (Q ^ (1 / 2 : ℝ)) * Q ^ (2 * (r : ℝ)), by positivity, rfl⟩
  refine ⟨C_dir + Q_fac * K_dual * (2 : ℝ) ^ (2 * r + 1) +
      ‖R‖ * Real.exp 1 * (M_B.factorial : ℝ) + 1, by positivity, fun s hlo hhi him => ?_⟩
  have hτ1 : 1 < |s.im| := by linarith
  have hτ_pos : 0 < |s.im| := zero_lt_one.trans hτ1
  have hx_pos : 0 < Real.sqrt |s.im| := Real.sqrt_pos.mpr hτ_pos
  have hL1 : 1 ≤ max 2 (Nat.ceil (|s.im| ^ (1 / 2 + η))) :=
    le_trans (by omega : 1 ≤ 2) (le_max_left _ _)
  have hL_ge : |s.im| ^ (1 / 2 + η) ≤ ((max 2 (Nat.ceil (|s.im| ^ (1 / 2 + η))) : ℕ) : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 2 _)
  have hmain := htrunc s (Real.sqrt |s.im|) (max 2 (Nat.ceil (|s.im| ^ (1 / 2 + η))))
    hlo hhi hx_pos hL1
  -- 1. Direct tail bound `≤ C_dir * |s.im| ^ (-B)`.
  have hbd_dir :
      C_dir * (Real.sqrt |s.im|) ^ (2 * (r : ℝ)) *
          ((max 2 (Nat.ceil (|s.im| ^ (1 / 2 + η))) : ℕ) : ℝ) ^ (1 - (s.re + 2 * (r : ℝ))) ≤
        C_dir * |s.im| ^ (-B) := by
    have hxA : (Real.sqrt |s.im|) ^ (2 * (r : ℝ)) = |s.im| ^ (r : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hτ_pos.le]
      congr 1; ring
    have hexp_neg : 1 - (s.re + 2 * (r : ℝ)) ≤ 0 := by linarith
    have hL_pow :
        ((max 2 (Nat.ceil (|s.im| ^ (1 / 2 + η))) : ℕ) : ℝ) ^ (1 - (s.re + 2 * (r : ℝ))) ≤
          |s.im| ^ ((1 / 2 + η) * (1 - (s.re + 2 * (r : ℝ)))) := by
      calc ((max 2 (Nat.ceil (|s.im| ^ (1 / 2 + η))) : ℕ) : ℝ) ^ (1 - (s.re + 2 * (r : ℝ)))
          ≤ (|s.im| ^ (1 / 2 + η)) ^ (1 - (s.re + 2 * (r : ℝ))) :=
            Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hτ_pos _) hL_ge hexp_neg
        _ = |s.im| ^ ((1 / 2 + η) * (1 - (s.re + 2 * (r : ℝ)))) :=
            (Real.rpow_mul hτ_pos.le _ _).symm
    have hexp_le : (r : ℝ) + (1 / 2 + η) * (1 - (s.re + 2 * (r : ℝ))) ≤ -B := by
      have hid : (r : ℝ) + (1 / 2 + η) * (1 - (s.re + 2 * (r : ℝ))) =
          -(2 * (r : ℝ) * η) + ((1 - s.re) / 2 + η * (1 - s.re)) := by ring
      have hsub1 : (1 - s.re) / 2 + η * (1 - s.re) ≤ 1 := by
        have h1s_nn : 0 ≤ 1 - s.re := by linarith
        have h1s_le1 : 1 - s.re ≤ 1 := by linarith
        have hmul_eta : η * (1 - s.re) ≤ (1 / 2) * 1 :=
          mul_le_mul hη_half.le h1s_le1 h1s_nn (by norm_num)
        linarith
      linarith [hid, hr_eta, hsub1]
    calc C_dir * (Real.sqrt |s.im|) ^ (2 * (r : ℝ)) *
            ((max 2 (Nat.ceil (|s.im| ^ (1 / 2 + η))) : ℕ) : ℝ) ^ (1 - (s.re + 2 * (r : ℝ)))
        ≤ C_dir * |s.im| ^ (r : ℝ) * |s.im| ^ ((1 / 2 + η) * (1 - (s.re + 2 * (r : ℝ)))) := by
          rw [hxA]
          exact mul_le_mul_of_nonneg_left hL_pow (by positivity)
      _ = C_dir * |s.im| ^ ((r : ℝ) + (1 / 2 + η) * (1 - (s.re + 2 * (r : ℝ)))) := by
          rw [mul_assoc, ← Real.rpow_add hτ_pos]
      _ ≤ C_dir * |s.im| ^ (-B) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hτ1.le hexp_le) hC_dir0
  -- 2. Reflected dual tail bound `≤ (Q_fac * K_dual * 2^{2r + 1}) * |s.im| ^ (-B)`.
  have hbd_dual :
      ‖ω * (Q : ℂ) ^ ((1 / 2 : ℂ) - s)‖ *
          (K_dual * (Real.sqrt |s.im| / Q) ^ (-2 * (r : ℝ)) *
            (1 + |s.im|) ^ ((2 * r : ℝ) + 1 / 2 - s.re) *
            ((max 2 (Nat.ceil (|s.im| ^ (1 / 2 + η))) : ℕ) : ℝ) ^ (s.re - 2 * (r : ℝ))) ≤
        (Q_fac * K_dual * (2 : ℝ) ^ (2 * r + 1)) * |s.im| ^ (-B) := by
    have hQ_pref : ‖ω * (Q : ℂ) ^ ((1 / 2 : ℂ) - s)‖ * (Real.sqrt |s.im| / Q) ^ (-2 * (r : ℝ)) ≤
        Q_fac * |s.im| ^ (-(r : ℝ)) := by
      rw [norm_mul, hD.norm_ω, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hQ_pos,
        show ((1 / 2 : ℂ) - s).re = 1 / 2 - s.re by simp]
      have hQ_half : Q ^ (1 / 2 - s.re) ≤ max 1 (Q ^ (1 / 2 : ℝ)) := by
        rcases le_total 1 Q with h1Q | hQ1
        · exact (Real.rpow_le_rpow_of_exponent_le h1Q (by linarith)).trans (le_max_right _ _)
        · exact (Real.rpow_le_one hQ_pos.le hQ1 (by linarith)).trans (le_max_left _ _)
      have hxQ_pow : (Real.sqrt |s.im| / Q) ^ (-2 * (r : ℝ)) =
          Q ^ (2 * (r : ℝ)) * |s.im| ^ (-(r : ℝ)) := by
        rw [Real.div_rpow hx_pos.le hQ_pos.le, show -2 * (r : ℝ) = -(2 * (r : ℝ)) by ring,
          Real.rpow_neg hQ_pos.le, div_inv_eq_mul, mul_comm]
        congr 1
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hτ_pos.le]
        congr 1; ring
      rw [hxQ_pow, hQ_fac_eq]
      calc Q ^ (1 / 2 - s.re) * (Q ^ (2 * (r : ℝ)) * |s.im| ^ (-(r : ℝ)))
          ≤ max 1 (Q ^ (1 / 2 : ℝ)) * (Q ^ (2 * (r : ℝ)) * |s.im| ^ (-(r : ℝ))) :=
            mul_le_mul_of_nonneg_right hQ_half (by positivity)
        _ = max 1 (Q ^ (1 / 2 : ℝ)) * Q ^ (2 * (r : ℝ)) * |s.im| ^ (-(r : ℝ)) := by ring
    have h1τ_le : (1 + |s.im|) ^ ((2 * r : ℝ) + 1 / 2 - s.re) ≤
        (2 : ℝ) ^ (2 * r + 1) * |s.im| ^ ((2 * r : ℝ) + 1 / 2 - s.re) := by
      have hexp_nn : 0 ≤ (2 * r : ℝ) + 1 / 2 - s.re := by linarith
      have hexp_le : (2 * r : ℝ) + 1 / 2 - s.re ≤ ((2 * r + 1 : ℕ) : ℝ) := by push_cast; linarith
      calc (1 + |s.im|) ^ ((2 * r : ℝ) + 1 / 2 - s.re)
          ≤ (2 * |s.im|) ^ ((2 * r : ℝ) + 1 / 2 - s.re) :=
            Real.rpow_le_rpow (by positivity) (by linarith) hexp_nn
        _ = (2 : ℝ) ^ ((2 * r : ℝ) + 1 / 2 - s.re) * |s.im| ^ ((2 * r : ℝ) + 1 / 2 - s.re) :=
            Real.mul_rpow two_pos.le hτ_pos.le
        _ ≤ (2 : ℝ) ^ (((2 * r + 1 : ℕ) : ℝ)) * |s.im| ^ ((2 * r : ℝ) + 1 / 2 - s.re) :=
            mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_le)
              (by positivity)
        _ = (2 : ℝ) ^ (2 * r + 1) * |s.im| ^ ((2 * r : ℝ) + 1 / 2 - s.re) := by rw [Real.rpow_natCast]
    have hL_du :
        ((max 2 (Nat.ceil (|s.im| ^ (1 / 2 + η))) : ℕ) : ℝ) ^ (s.re - 2 * (r : ℝ)) ≤
          |s.im| ^ ((1 / 2 + η) * (s.re - 2 * (r : ℝ))) := by
      have hexp_neg : s.re - 2 * (r : ℝ) ≤ 0 := by linarith
      calc ((max 2 (Nat.ceil (|s.im| ^ (1 / 2 + η))) : ℕ) : ℝ) ^ (s.re - 2 * (r : ℝ))
          ≤ (|s.im| ^ (1 / 2 + η)) ^ (s.re - 2 * (r : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hτ_pos _) hL_ge hexp_neg
        _ = |s.im| ^ ((1 / 2 + η) * (s.re - 2 * (r : ℝ))) := (Real.rpow_mul hτ_pos.le _ _).symm
    have hexp_du_le : -(r : ℝ) + ((2 * r : ℝ) + 1 / 2 - s.re) +
        (1 / 2 + η) * (s.re - 2 * (r : ℝ)) ≤ -B := by
      have hid : -(r : ℝ) + ((2 * r : ℝ) + 1 / 2 - s.re) +
          (1 / 2 + η) * (s.re - 2 * (r : ℝ)) =
          -(2 * (r : ℝ) * η) + ((1 - s.re) / 2 + η * s.re) := by ring
      have hsub1 : (1 - s.re) / 2 + η * s.re ≤ 1 := by
        have hs_nn : 0 ≤ s.re := by linarith
        have hmul_eta : η * s.re ≤ (1 / 2) * (1 / 2) :=
          mul_le_mul hη_half.le hhi.le hs_nn (by norm_num)
        linarith
      linarith [hid, hr_eta, hsub1]
    calc ‖ω * (Q : ℂ) ^ ((1 / 2 : ℂ) - s)‖ *
            (K_dual * (Real.sqrt |s.im| / Q) ^ (-2 * (r : ℝ)) *
              (1 + |s.im|) ^ ((2 * r : ℝ) + 1 / 2 - s.re) *
              ((max 2 (Nat.ceil (|s.im| ^ (1 / 2 + η))) : ℕ) : ℝ) ^ (s.re - 2 * (r : ℝ)))
        = K_dual * (‖ω * (Q : ℂ) ^ ((1 / 2 : ℂ) - s)‖ * (Real.sqrt |s.im| / Q) ^ (-2 * (r : ℝ))) *
            (1 + |s.im|) ^ ((2 * r : ℝ) + 1 / 2 - s.re) *
            ((max 2 (Nat.ceil (|s.im| ^ (1 / 2 + η))) : ℕ) : ℝ) ^ (s.re - 2 * (r : ℝ)) := by ring
      _ ≤ K_dual * (Q_fac * |s.im| ^ (-(r : ℝ))) *
            ((2 : ℝ) ^ (2 * r + 1) * |s.im| ^ ((2 * r : ℝ) + 1 / 2 - s.re)) *
            |s.im| ^ ((1 / 2 + η) * (s.re - 2 * (r : ℝ))) := by
          refine mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hQ_pref hK_dual_pos.le)
            h1τ_le (by positivity) (by positivity)) hL_du (by positivity) (by positivity)
      _ = (Q_fac * K_dual * (2 : ℝ) ^ (2 * r + 1)) *
            (|s.im| ^ (-(r : ℝ)) * |s.im| ^ ((2 * r : ℝ) + 1 / 2 - s.re) *
              |s.im| ^ ((1 / 2 + η) * (s.re - 2 * (r : ℝ)))) := by ring
      _ = (Q_fac * K_dual * (2 : ℝ) ^ (2 * r + 1)) *
            |s.im| ^ (-(r : ℝ) + ((2 * r : ℝ) + 1 / 2 - s.re) + (1 / 2 + η) * (s.re - 2 * (r : ℝ))) := by
          rw [← Real.rpow_add hτ_pos, ← Real.rpow_add hτ_pos]
      _ ≤ (Q_fac * K_dual * (2 : ℝ) ^ (2 * r + 1)) * |s.im| ^ (-B) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hτ1.le hexp_du_le) (by positivity)
  -- 3. Shifted pole residue bound `≤ (‖R‖ * exp 1 * M_B!) * |s.im| ^ (-B)`.
  have hbd_pole : ‖R * smoothAFEZetaShiftedPoleResidue s (Real.sqrt |s.im|)‖ ≤
      (‖R‖ * Real.exp 1 * (M_B.factorial : ℝ)) * |s.im| ^ (-B) := by
    rw [norm_mul, smoothAFEZetaShiftedPoleResidue, norm_div, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hx_pos, Complex.norm_exp]
    have h1s_norm : 1 ≤ ‖(1 : ℂ) - s‖ := by
      calc (1 : ℝ) ≤ |s.im| := hτ1.le
        _ = |((1 : ℂ) - s).im| := by simp
        _ ≤ ‖(1 : ℂ) - s‖ := Complex.abs_im_le_norm _
    have hx_1s : (Real.sqrt |s.im|) ^ ((1 - s).re) ≤ |s.im| := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hτ_pos.le, show (1 - s).re = 1 - s.re by simp]
      exact (Real.rpow_le_rpow_of_exponent_le hτ1.le (by linarith : 1 / 2 * (1 - s.re) ≤ 1)).trans_eq
        (Real.rpow_one |s.im|)
    have hre_sq : (((1 - s) ^ (2 : ℕ)).re) ≤ 1 - |s.im| ^ 2 := by
      have h1 : (((1 - s) ^ (2 : ℕ)).re) = (1 - s.re) ^ 2 - s.im ^ 2 := by
        simp only [pow_two, Complex.mul_re, Complex.sub_re, Complex.sub_im,
          Complex.one_re, Complex.one_im]
        ring
      have h1s_sq : (1 - s.re) ^ 2 ≤ 1 * 1 :=
        mul_self_le_mul_self (by linarith) (by linarith)
      rw [h1, ← sq_abs s.im]
      linarith
    have hexp_tau : Real.exp (-(|s.im| ^ 2)) ≤ (M_B.factorial : ℝ) * |s.im| ^ (-(M_B : ℝ)) := by
      have hsq_ge : |s.im| ≤ |s.im| ^ 2 := by
        rw [pow_two]
        exact le_mul_of_one_le_left hτ_pos.le hτ1.le
      have hpow_fac : |s.im| ^ M_B / (M_B.factorial : ℝ) ≤ Real.exp (|s.im| ^ 2) :=
        (Real.pow_div_factorial_le_exp |s.im| hτ_pos.le M_B).trans (Real.exp_le_exp.mpr hsq_ge)
      have hfac_pos : (0 : ℝ) < (M_B.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos M_B
      rw [Real.rpow_neg hτ_pos.le, Real.rpow_natCast, Real.exp_neg,
        inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
      have h1 : |s.im| ^ M_B ≤ Real.exp (|s.im| ^ 2) * (M_B.factorial : ℝ) :=
        (div_le_iff₀ hfac_pos).mp hpow_fac
      have hpow_pos : 0 < |s.im| ^ M_B := pow_pos hτ_pos M_B
      calc (1 : ℝ) = (|s.im| ^ M_B)⁻¹ * |s.im| ^ M_B := (inv_mul_cancel₀ hpow_pos.ne').symm
        _ ≤ (|s.im| ^ M_B)⁻¹ * (Real.exp (|s.im| ^ 2) * (M_B.factorial : ℝ)) :=
            mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hpow_pos.le)
        _ = (M_B.factorial : ℝ) * (|s.im| ^ M_B)⁻¹ * Real.exp (|s.im| ^ 2) := by ring
    have htau_MB : |s.im| * |s.im| ^ (-(M_B : ℝ)) ≤ |s.im| ^ (-B) := by
      rw [show |s.im| * |s.im| ^ (-(M_B : ℝ)) = |s.im| ^ (1 : ℝ) * |s.im| ^ (-(M_B : ℝ)) by rw [Real.rpow_one],
        ← Real.rpow_add hτ_pos]
      exact Real.rpow_le_rpow_of_exponent_le hτ1.le (by linarith)
    have hdiv_le : (Real.sqrt |s.im|) ^ ((1 - s).re) * Real.exp (((1 - s) ^ (2 : ℕ)).re) / ‖(1 : ℂ) - s‖ ≤
        Real.exp 1 * (M_B.factorial : ℝ) * |s.im| ^ (-B) := by
      calc (Real.sqrt |s.im|) ^ ((1 - s).re) * Real.exp (((1 - s) ^ (2 : ℕ)).re) / ‖(1 : ℂ) - s‖
          ≤ (Real.sqrt |s.im|) ^ ((1 - s).re) * Real.exp (((1 - s) ^ (2 : ℕ)).re) :=
            div_le_self (by positivity) h1s_norm
        _ ≤ |s.im| * Real.exp (1 - |s.im| ^ 2) :=
            mul_le_mul hx_1s (Real.exp_le_exp.mpr hre_sq) (Real.exp_nonneg _) hτ_pos.le
        _ = Real.exp 1 * (|s.im| * Real.exp (-(|s.im| ^ 2))) := by
            rw [show 1 - |s.im| ^ 2 = 1 + -(|s.im| ^ 2) by ring, Real.exp_add]; ring
        _ ≤ Real.exp 1 * (|s.im| * ((M_B.factorial : ℝ) * |s.im| ^ (-(M_B : ℝ)))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp_tau hτ_pos.le) (Real.exp_nonneg _)
        _ = Real.exp 1 * (M_B.factorial : ℝ) * (|s.im| * |s.im| ^ (-(M_B : ℝ))) := by ring
        _ ≤ Real.exp 1 * (M_B.factorial : ℝ) * |s.im| ^ (-B) :=
            mul_le_mul_of_nonneg_left htau_MB (by positivity)
    exact (mul_le_mul_of_nonneg_left hdiv_le (norm_nonneg _)).trans_eq (by ring)
  calc ‖F s - crossHeightDirichletWitness a b Q ω s
          (Real.sqrt |s.im|) (max 2 (Nat.ceil (|s.im| ^ (1 / 2 + η))))‖
      ≤ C_dir * |s.im| ^ (-B) +
          (Q_fac * K_dual * (2 : ℝ) ^ (2 * r + 1)) * |s.im| ^ (-B) +
          (‖R‖ * Real.exp 1 * (M_B.factorial : ℝ)) * |s.im| ^ (-B) :=
        hmain.trans (add_le_add (add_le_add hbd_dir hbd_dual) hbd_pole)
    _ = (C_dir + Q_fac * K_dual * (2 : ℝ) ^ (2 * r + 1) +
          ‖R‖ * Real.exp 1 * (M_B.factorial : ℝ)) * |s.im| ^ (-B) := by ring
    _ ≤ (C_dir + Q_fac * K_dual * (2 : ℝ) ^ (2 * r + 1) +
          ‖R‖ * Real.exp 1 * (M_B.factorial : ℝ) + 1) * |s.im| ^ (-B) :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hτ_pos.le _)

/-- Full two-head cross-height zeta witness including the shifted pole residue at scale `x`. -/
def crossHeightZetaFullWitness (s : ℂ) (x : ℝ) (L : ℕ) : ℂ :=
  crossHeightDirichletWitness (fun _ => 1) (fun _ => 1) 1 1 s x L -
    smoothAFEZetaShiftedPoleResidue s x

/-- **Unconditional `RiemannHypothesis` equivalence with cross-height Gaussian witnesses starting
at sublinear square-root length `L ≥ max 2 ⌈|Im s|^{1/2 + η}⌉₊` across ALL of `Ω_open`:**
for every `η ∈ (0, 1 / 2)`, there exist explicit `s`-independent constants `C_dir, K_dual > 0`
such that:
1. at every `s ∈ Ω_open` and every `L ≥ 1`, `‖riemannZeta s - crossHeightZetaFullWitness s (√|Im s|) L‖`
   is bounded by the explicit `r = 1` power-decaying tail `C_dir |Im s| L^{-(1 + Re s)} + K_dual |Im s|^{-1} (1 + |Im s|)^{5/2 - Re s} L^{Re s - 2}`;
2. `RiemannHypothesis` holds if and only if at **every** point of `Ω_open`
   (`3001 / 24000 ≤ Re s < 1 / 2`, `184 < |Im s|`), some `L ≥ max 2 ⌈|Im s|^{1/2 + η}⌉₊` beats that
   certified error (and whenever `E |Im s|^{-B} < ‖riemannZeta s‖ / 2`, `L = max 2 ⌈|Im s|^{1/2 + η}⌉₊`
   itself already suffices). -/
theorem rh_iff_sublinear_crossHeight_witness_on_remaining_strip
    {η : ℝ} (hη0 : 0 < η) (hη_half : η < 1 / 2) :
    ∃ C_dir K_dual : ℝ, 0 < C_dir ∧ 0 < K_dual ∧
      (∀ s : ℂ, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 184 < |s.im| →
        ∀ L : ℕ, 1 ≤ L →
          ‖riemannZeta s - crossHeightZetaFullWitness s (Real.sqrt |s.im|) L‖ ≤
            C_dir * |s.im| * (L : ℝ) ^ (-(1 + s.re)) +
              K_dual * |s.im|⁻¹ * (1 + |s.im|) ^ ((5 / 2 : ℝ) - s.re) * (L : ℝ) ^ (s.re - 2)) ∧
      (RiemannHypothesis ↔
        ∀ s : ℂ, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 184 < |s.im| →
          ∃ L : ℕ, max 2 (Nat.ceil (|s.im| ^ (1 / 2 + η))) ≤ L ∧
            C_dir * |s.im| * (L : ℝ) ^ (-(1 + s.re)) +
              K_dual * |s.im|⁻¹ * (1 + |s.im|) ^ ((5 / 2 : ℝ) - s.re) * (L : ℝ) ^ (s.re - 2) <
              ‖crossHeightZetaFullWitness s (Real.sqrt |s.im|) L‖) := by
  obtain ⟨C₀, hC₀, hC_dir⟩ := exists_smoothAFE_direct_tail_le (A := 2) (by norm_num)
  obtain ⟨K_dual, hK_dual_pos, hK_dual⟩ :=
    exists_norm_smoothAFEZetaDualCoefficientGeneral_deep_le
      (σ_min := 3001 / 24000) (by norm_num) (by norm_num) (r := 1) le_rfl
  set C_dir : ℝ := C₀ + 1
  have hC_dir_pos : 0 < C_dir := by dsimp only [C_dir]; positivity
  -- Prove the uniform `r = 1` tail bound first.
  have htail_bound : ∀ s : ℂ, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 184 < |s.im| →
      ∀ L : ℕ, 1 ≤ L →
        ‖riemannZeta s - crossHeightZetaFullWitness s (Real.sqrt |s.im|) L‖ ≤
          C_dir * |s.im| * (L : ℝ) ^ (-(1 + s.re)) +
            K_dual * |s.im|⁻¹ * (1 + |s.im|) ^ ((5 / 2 : ℝ) - s.re) * (L : ℝ) ^ (s.re - 2) := by
    intro s hlo hhi him L hL1
    set τ : ℝ := |s.im|
    have hτ_pos : 0 < τ := by dsimp only [τ]; linarith
    set x : ℝ := Real.sqrt τ
    have hx_pos : 0 < x := Real.sqrt_pos.mpr hτ_pos
    have hs0 : 0 < s.re := by linarith
    have hs1 : s.re < 1 := by linarith
    have hsA : 1 < s.re + 2 := by linarith
    rw [crossHeight_gaussian_two_tsum_eq unitPoleFreeCrossHeightDatum_riemannZeta hx_pos hs0 hhi]
    have hsum_dir := summable_smoothAFE_direct (A := 2) (by norm_num) hx_pos hsA
    have hsum_dual : Summable (fun m : ℕ => smoothAFEZetaDualCoefficientGeneral s x m) := by
      obtain ⟨Kd0, _, hKd0⟩ := exists_norm_smoothAFEZetaDualCoefficientGeneral_le hx_pos hs0 hs1
      exact Summable.of_norm_bounded
        ((summable_smoothAFEZetaMajorant (p := 2 - s.re) (by linarith)).mul_left Kd0) hKd0
    unfold crossHeightGaussianTwoSeries crossHeightZetaFullWitness crossHeightDirichletWitness
    simp only [one_mul, Complex.ofReal_one, Complex.one_cpow, div_one]
    rw [← hsum_dir.sum_add_tsum_nat_add L, ← hsum_dual.sum_add_tsum_nat_add L]
    have halg :
        ((∑ n ∈ Finset.range L, (((n + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / x)) +
            ∑' j : ℕ, (((j + L + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((j + L + 1 : ℕ) : ℝ) / x))) -
          (∑ m ∈ Finset.range L, smoothAFEZetaDualCoefficientGeneral s x m +
            ∑' j : ℕ, smoothAFEZetaDualCoefficientGeneral s x (j + L)) -
          smoothAFEZetaShiftedPoleResidue s x) -
        ((∑ n ∈ Finset.range L, (((n + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / x)) -
            ∑ m ∈ Finset.range L, smoothAFEZetaDualCoefficientGeneral s x m) -
          smoothAFEZetaShiftedPoleResidue s x) =
        (∑' j : ℕ, (((j + L + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((j + L + 1 : ℕ) : ℝ) / x))) -
          ∑' j : ℕ, smoothAFEZetaDualCoefficientGeneral s x (j + L) := by
      simp only [Nat.add_assoc, Nat.add_comm L 1]
      ring
    rw [halg]
    have hsh_dir : Summable (fun j : ℕ =>
        ‖(((j + L + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((j + L + 1 : ℕ) : ℝ) / x))‖) :=
      (summable_nat_add_iff
        (f := fun n : ℕ => ‖(((n + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / x))‖) L).mpr
        hsum_dir.norm
    have hsh_du : Summable (fun j : ℕ => ‖smoothAFEZetaDualCoefficientGeneral s x (j + L)‖) :=
      (summable_nat_add_iff
        (f := fun m : ℕ => ‖smoothAFEZetaDualCoefficientGeneral s x m‖) L).mpr
        hsum_dual.norm
    have hb1 : ‖∑' j : ℕ, (((j + L + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((j + L + 1 : ℕ) : ℝ) / x))‖ ≤
        C_dir * τ * (L : ℝ) ^ (-(1 + s.re)) := by
      have h0 := (norm_tsum_le_tsum_norm hsh_dir).trans (hC_dir s x hx_pos hsA L hL1)
      have hx2 : x ^ (2 : ℝ) = τ := by
        dsimp only [x]; rw [Real.rpow_two, Real.sq_sqrt hτ_pos.le]
      have hden1 : 1 ≤ s.re + 2 - 1 := by linarith
      rw [hx2, show 1 - (s.re + 2) = -(1 + s.re) by ring] at h0
      calc ‖∑' j : ℕ, (((j + L + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((j + L + 1 : ℕ) : ℝ) / x))‖
          ≤ C₀ * τ * (L : ℝ) ^ (-(1 + s.re)) :=
            h0.trans (mul_le_mul_of_nonneg_left
              (div_le_self (Real.rpow_nonneg (Nat.cast_nonneg L) _) hden1) (by positivity))
        _ ≤ C_dir * τ * (L : ℝ) ^ (-(1 + s.re)) := by
            dsimp only [C_dir]
            have : 0 ≤ τ * (L : ℝ) ^ (-(1 + s.re)) := by positivity
            nlinarith
    have hb2 : ‖∑' j : ℕ, smoothAFEZetaDualCoefficientGeneral s x (j + L)‖ ≤
        K_dual * τ⁻¹ * (1 + τ) ^ ((5 / 2 : ℝ) - s.re) * (L : ℝ) ^ (s.re - 2) := by
      have h0 := (norm_tsum_le_tsum_norm hsh_du).trans ((hK_dual s x hlo hhi hx_pos).2 L hL1)
      have hxm2 : x ^ (-2 * (1 : ℝ)) = τ⁻¹ := by
        dsimp only [x]
        rw [show -2 * (1 : ℝ) = -(2 : ℝ) by ring, Real.rpow_neg hx_pos.le,
          Real.rpow_two, Real.sq_sqrt hτ_pos.le]
      simpa only [Nat.cast_one, hxm2, show (2 * (1 : ℝ)) + 1 / 2 - s.re = (5 / 2 : ℝ) - s.re by ring,
        show s.re - 2 * (1 : ℝ) = s.re - 2 by ring] using h0
    exact (norm_sub_le _ _).trans (add_le_add hb1 hb2)
  refine ⟨C_dir, K_dual, hC_dir_pos, hK_dual_pos, htail_bound, ?_⟩
  -- Equivalence with `RiemannHypothesis` via `rh_iff_linear_euler_signedPartialSum_above_oneHundredEightyFour`.
  have hrh_zeta : RiemannHypothesis ↔
      ∀ s : ℂ, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 184 < |s.im| → riemannZeta s ≠ 0 := by
    rw [rh_iff_linear_euler_signedPartialSum_above_oneHundredEightyFour.2]
    refine forall₄_congr fun s hlo hhi him => ?_
    have hs0 : 0 < s.re := by linarith
    have hs1 : s.re < 1 := by linarith
    have hceil185 : 185 ≤ Nat.ceil |s.im| := by
      have : 184 < Nat.ceil |s.im| := (Nat.lt_ceil).mpr (by exact_mod_cast him)
      omega
    have hmax1 : max 1 (Nat.ceil |s.im|) = Nat.ceil |s.im| := max_eq_right (by omega)
    rw [← (exists_linear_eulerEtaPartialSum_beats_tail_iff_zeta_ne_zero hs0 hs1).2, hmax1]
  rw [hrh_zeta]
  refine forall₄_congr fun s hlo hhi him => ?_
  constructor
  · intro hζ_ne
    have hζ_pos : 0 < ‖riemannZeta s‖ := norm_pos_iff.mpr hζ_ne
    -- Both `L^{-(1 + s.re)}` and `L^{s.re - 2}` are `≤ L^{-3/2} ≤ L^{-1}` for `L ≥ 1` and `s.re < 1/2`.
    set A_tot : ℝ := C_dir * |s.im| + K_dual * |s.im|⁻¹ * (1 + |s.im|) ^ ((5 / 2 : ℝ) - s.re)
    have hA_pos : 0 < A_tot := by
      dsimp only [A_tot]
      have : 0 < |s.im| := by linarith
      positivity
    set L₀ : ℕ := max (max 2 (Nat.ceil (|s.im| ^ (1 / 2 + η))))
      (Nat.ceil (2 * A_tot / ‖riemannZeta s‖) + 1)
    have hL₀_ge : max 2 (Nat.ceil (|s.im| ^ (1 / 2 + η))) ≤ L₀ := le_max_left _ _
    have hL₀_1 : 1 ≤ L₀ := le_trans (by omega : 1 ≤ 2) ((le_max_left _ _).trans hL₀_ge)
    have hL₀_big : 2 * A_tot / ‖riemannZeta s‖ < (L₀ : ℝ) := by
      have hc : 2 * A_tot / ‖riemannZeta s‖ ≤ (Nat.ceil (2 * A_tot / ‖riemannZeta s‖) : ℝ) :=
        Nat.le_ceil _
      have hm : (Nat.ceil (2 * A_tot / ‖riemannZeta s‖) : ℝ) + 1 ≤ (L₀ : ℝ) := by
        exact_mod_cast le_max_right _ _
      linarith
    have hL₀_pos : 0 < (L₀ : ℝ) := by exact_mod_cast hL₀_1
    have hL₀_1r : (1 : ℝ) ≤ (L₀ : ℝ) := by exact_mod_cast hL₀_1
    have herr_lt : C_dir * |s.im| * (L₀ : ℝ) ^ (-(1 + s.re)) +
        K_dual * |s.im|⁻¹ * (1 + |s.im|) ^ ((5 / 2 : ℝ) - s.re) * (L₀ : ℝ) ^ (s.re - 2) <
        ‖riemannZeta s‖ / 2 := by
      have hp1 : (L₀ : ℝ) ^ (-(1 + s.re)) ≤ (L₀ : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hL₀_1r (by linarith)
      have hp2 : (L₀ : ℝ) ^ (s.re - 2) ≤ (L₀ : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hL₀_1r (by linarith)
      have hinv_lt : (L₀ : ℝ) ^ (-1 : ℝ) < ‖riemannZeta s‖ / (2 * A_tot) := by
        rw [Real.rpow_neg_one, inv_lt_comm₀ hL₀_pos (by positivity), inv_div]
        exact hL₀_big
      calc C_dir * |s.im| * (L₀ : ℝ) ^ (-(1 + s.re)) +
            K_dual * |s.im|⁻¹ * (1 + |s.im|) ^ ((5 / 2 : ℝ) - s.re) * (L₀ : ℝ) ^ (s.re - 2)
          ≤ C_dir * |s.im| * (L₀ : ℝ) ^ (-1 : ℝ) +
              K_dual * |s.im|⁻¹ * (1 + |s.im|) ^ ((5 / 2 : ℝ) - s.re) * (L₀ : ℝ) ^ (-1 : ℝ) := by
            gcongr
        _ = A_tot * (L₀ : ℝ) ^ (-1 : ℝ) := by dsimp only [A_tot]; ring
        _ < A_tot * (‖riemannZeta s‖ / (2 * A_tot)) :=
            mul_lt_mul_of_pos_left hinv_lt hA_pos
        _ = ‖riemannZeta s‖ / 2 := by field_simp [hA_pos.ne']
    have htb := htail_bound s hlo hhi him L₀ hL₀_1
    have htri := norm_sub_norm_le (riemannZeta s) (crossHeightZetaFullWitness s (Real.sqrt |s.im|) L₀)
    refine ⟨L₀, hL₀_ge, ?_⟩
    linarith
  · rintro ⟨L, hL_ge, hbeat⟩ hζ0
    have hL1 : 1 ≤ L := le_trans (by omega : 1 ≤ 2) ((le_max_left _ _).trans hL_ge)
    have htb := htail_bound s hlo hhi him L hL1
    have heq_norm : ‖riemannZeta s - crossHeightZetaFullWitness s (Real.sqrt |s.im|) L‖ =
        ‖crossHeightZetaFullWitness s (Real.sqrt |s.im|) L‖ := by
      rw [hζ0, zero_sub, norm_neg]
    linarith [htb, heq_norm]

/-- **Explicit quantitative failure of the cross-height Gaussian two-series mechanism on
`posTruncatedZeta`:** unconditionally (without `RiemannHypothesis`), for every
`β ∈ (zetaAsympZeroAbscissa, 1)`, `γ₀ ∈ ℝ`, `P₀ : ℕ`, and height `T : ℝ`:
1. `posTruncatedZeta P₀ (β + i γ₀)` admits **no** `UnitPoleFreeCrossHeightDatum`;
2. there exists a left-strip point `s₀` (`0 < Re s₀ < 1 - zetaAsympZeroAbscissa ≤ 1 / 2`, `|Im s₀| > T`)
   such that for **every** choice of unit-bounded sequences `‖a(n)‖ ≤ 1`, `‖b(n)‖ ≤ 1`, residue `R`,
   conductor `Q > 0`, root number `ω`, and scale `x > 0`, the cross-height Gaussian two-series
   error `‖posTruncatedZeta P₀ (β + i γ₀) s - crossHeightGaussianTwoSeries a b R Q ω s x‖`
   diverges to `+∞` on `𝓝[≠] s₀`. -/
theorem crossHeight_gaussian_mechanism_fails_on_posTruncatedZeta
    {β : ℝ} (hβ_lo : zetaAsympZeroAbscissa < β) (hβ1 : β < 1)
    (γ₀ : ℝ) (P₀ : ℕ) (T : ℝ) :
    (∀ (a b : ℕ → ℂ) (R : ℂ) (Q : ℝ) (ω : ℂ),
      ¬ UnitPoleFreeCrossHeightDatum
          (posTruncatedZeta P₀ ((β : ℂ) + (γ₀ : ℂ) * I)) a b R Q ω) ∧
    (∃ s₀ : ℂ, 0 < s₀.re ∧ s₀.re < 1 - zetaAsympZeroAbscissa ∧ T < |s₀.im| ∧
      ∀ (a b : ℕ → ℂ), (∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤ 1) → (∀ n : ℕ, 1 ≤ n → ‖b n‖ ≤ 1) →
        ∀ (R : ℂ) {Q : ℝ}, 0 < Q → ∀ (ω : ℂ) {x : ℝ}, 0 < x →
          Tendsto (fun s =>
            ‖posTruncatedZeta P₀ ((β : ℂ) + (γ₀ : ℂ) * I) s -
              crossHeightGaussianTwoSeries a b R Q ω s x‖) (𝓝[≠] s₀) atTop) := by
  obtain ⟨s₀, hs₀_pos, hs₀_lt, hs₀_im, htop, hnot_an, _, _, _⟩ :=
    exists_left_strip_pole_and_regular_reflection_above_height hβ_lo hβ1 γ₀ P₀ T
  have hΘ_half : 1 / 2 ≤ zetaAsympZeroAbscissa := half_le_zetaAsympZeroAbscissa
  have hs₀_half : s₀.re < 1 / 2 := by linarith
  refine ⟨fun a b R Q ω hD => ?_, s₀, hs₀_pos, hs₀_lt, hs₀_im, ?_⟩
  · -- Any `UnitPoleFreeCrossHeightDatum` is analytic on the open strip `{0 < Re z < 1 / 2}`.
    have hopen : IsOpen {z : ℂ | 0 < z.re ∧ z.re < 1 / 2} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    have hdiff_on : DifferentiableOn ℂ (posTruncatedZeta P₀ ((β : ℂ) + (γ₀ : ℂ) * I))
        {z : ℂ | 0 < z.re ∧ z.re < 1 / 2} :=
      fun z hz => (hD.holo_leftStrip z hz.1 hz.2).differentiableWithinAt
    exact hnot_an (hdiff_on.analyticOnNhd hopen s₀ ⟨hs₀_pos, hs₀_half⟩)
  · intro a b ha hb R Q hQ ω x hx
    -- Bound `crossHeightGaussianTwoSeries a b R Q ω s x` uniformly on a ball around `s₀`.
    set δ₀ : ℝ := min (s₀.re / 2) ((1 / 2 - s₀.re) / 2)
    have hδ₀_pos : 0 < δ₀ := lt_min (by linarith) (by linarith)
    obtain ⟨K_cut, hK_cut0, hK_cut⟩ := exists_norm_smoothAFECutoff_le_neg_rpow (A := 2) (by norm_num)
    obtain ⟨K_du, hK_du_pos, hK_du⟩ :=
      exists_norm_smoothAFEZetaDualCoefficientGeneral_deep_le
        (σ_min := s₀.re / 2) (by linarith) (by linarith) (r := 1) le_rfl
    set S_p2 : ℝ := ∑' n : ℕ, ((n + 1 : ℝ) ^ (-2 : ℝ))
    have hsum_p2 : Summable (fun n : ℕ => (n + 1 : ℝ) ^ (-2 : ℝ)) := by
      have h := Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1)
      simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr h
    set M_dir : ℝ := (K_cut * x ^ (2 : ℝ)) * S_p2
    set M_du : ℝ := ‖ω‖ * max 1 (Q ^ (1 / 2 : ℝ)) * K_du * (x / Q) ^ (-2 * (1 : ℝ)) *
      (1 + |s₀.im| + δ₀) ^ ((5 / 2 : ℝ)) * S_p2
    set M_pole : ℝ := ‖R‖ * (2 * max 1 x * Real.exp 1)
    set M_tot : ℝ := M_dir + M_du + M_pole + 1
    have hev_bd : ∀ᶠ s in 𝓝[≠] s₀, ‖crossHeightGaussianTwoSeries a b R Q ω s x‖ ≤ M_tot := by
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds
        (Metric.ball_mem_nhds s₀ hδ₀_pos)] with s hs_ball
      rw [dist_eq_norm] at hs_ball
      have hs_re_lo : s₀.re / 2 ≤ s.re := by
        have h := Complex.abs_re_le_norm (s - s₀)
        rw [Complex.sub_re] at h
        have hδ1 : δ₀ ≤ s₀.re / 2 := min_le_left _ _
        linarith [(abs_le.mp (h.trans hs_ball.le)).1]
      have hs_re_hi : s.re < 1 / 2 := by
        have h := Complex.abs_re_le_norm (s - s₀)
        rw [Complex.sub_re] at h
        have hδ2 : δ₀ ≤ (1 / 2 - s₀.re) / 2 := min_le_right _ _
        linarith [(abs_le.mp (h.trans hs_ball.le)).2]
      have hs_im_bd : |s.im| ≤ |s₀.im| + δ₀ := by
        have h := Complex.abs_im_le_norm (s - s₀)
        rw [Complex.sub_im] at h
        have htri : |s.im| - |s₀.im| ≤ |s.im - s₀.im| := abs_sub_abs_le_abs_sub _ _
        linarith [h.trans hs_ball.le]
      have hs_re_pos : 0 < s.re := lt_of_lt_of_le (by linarith) hs_re_lo
      -- Direct series bound
      have hb_dir : ‖∑' n : ℕ, a (n + 1) *
          (((n + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / x))‖ ≤ M_dir := by
        have hpt : ∀ n : ℕ, ‖a (n + 1) *
            (((n + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / x))‖ ≤
            (K_cut * x ^ (2 : ℝ)) * (n + 1 : ℝ) ^ (-2 : ℝ) := fun n => by
          rw [norm_mul]
          have h1 := mul_le_of_le_one_left
            (norm_nonneg (((n + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / x)))
            (ha (n + 1) (Nat.succ_pos n))
          have h2 := norm_smoothAFE_term_le hK_cut hx s (n + 1) (Nat.succ_pos n)
          have h3 : (((n + 1 : ℕ) : ℝ) ^ (-(s.re + 2))) ≤ (n + 1 : ℝ) ^ (-2 : ℝ) := by
            push_cast
            exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.succ_pos n) (by linarith)
          exact h1.trans (h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity)))
        have hmaj_d := hsum_p2.mul_left (K_cut * x ^ (2 : ℝ))
        have hs_d := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt hmaj_d
        exact (norm_tsum_le_tsum_norm hs_d).trans
          ((hs_d.tsum_le_tsum hpt hmaj_d).trans_eq tsum_mul_left)
      -- Dual series bound
      have hb_du : ‖ω * (Q : ℂ) ^ ((1 / 2 : ℂ) - s) *
          ∑' m : ℕ, b (m + 1) * smoothAFEZetaDualCoefficientGeneral s (x / Q) m‖ ≤ M_du := by
        set K_loc : ℝ := K_du * (x / Q) ^ (-2 * (1 : ℝ)) * (1 + |s₀.im| + δ₀) ^ ((5 / 2 : ℝ))
        have hpt : ∀ m : ℕ,
            ‖b (m + 1) * smoothAFEZetaDualCoefficientGeneral s (x / Q) m‖ ≤
              K_loc * (m + 1 : ℝ) ^ (-2 : ℝ) := fun m => by
          rw [norm_mul]
          have h1 := mul_le_of_le_one_left
            (norm_nonneg (smoothAFEZetaDualCoefficientGeneral s (x / Q) m))
            (hb (m + 1) (Nat.succ_pos m))
          have h2 : ‖smoothAFEZetaDualCoefficientGeneral s (x / Q) m‖ ≤
              K_du * (x / Q) ^ (-2 * (1 : ℝ)) * (1 + |s.im|) ^ ((5 / 2 : ℝ) - s.re) *
                (m + 1 : ℝ) ^ (-(3 - s.re)) := by
            simpa only [Nat.cast_one,
              show 2 * (1 : ℝ) + 1 / 2 - s.re = (5 / 2 : ℝ) - s.re by ring,
              show 2 * (1 : ℝ) + 1 - s.re = 3 - s.re by ring] using
              (hK_du s (x / Q) hs_re_lo hs_re_hi (div_pos hx hQ)).1 m
          have h1im : (1 + |s.im|) ^ ((5 / 2 : ℝ) - s.re) ≤
              (1 + |s₀.im| + δ₀) ^ ((5 / 2 : ℝ)) := by
            calc (1 + |s.im|) ^ ((5 / 2 : ℝ) - s.re)
                ≤ (1 + |s₀.im| + δ₀) ^ ((5 / 2 : ℝ) - s.re) :=
                  Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
              _ ≤ (1 + |s₀.im| + δ₀) ^ ((5 / 2 : ℝ)) :=
                  Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg s₀.im]) (by linarith)
          have hm_pow : (m + 1 : ℝ) ^ (-(3 - s.re)) ≤ (m + 1 : ℝ) ^ (-2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.succ_pos m) (by linarith)
          refine h1.trans (h2.trans ?_)
          dsimp only [K_loc]
          exact mul_le_mul (mul_le_mul_of_nonneg_left h1im (by positivity))
            hm_pow (by positivity) (by positivity)
        have hmaj_u := hsum_p2.mul_left K_loc
        have hs_u := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt hmaj_u
        have hts_u : ‖∑' m : ℕ, b (m + 1) * smoothAFEZetaDualCoefficientGeneral s (x / Q) m‖ ≤
            K_loc * S_p2 :=
          (norm_tsum_le_tsum_norm hs_u).trans ((hs_u.tsum_le_tsum hpt hmaj_u).trans_eq tsum_mul_left)
        have hQ_s : ‖(Q : ℂ) ^ ((1 / 2 : ℂ) - s)‖ ≤ max 1 (Q ^ (1 / 2 : ℝ)) := by
          rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ, show ((1 / 2 : ℂ) - s).re = 1 / 2 - s.re by simp]
          rcases le_total 1 Q with h1Q | hQ1
          · exact (Real.rpow_le_rpow_of_exponent_le h1Q (by linarith)).trans (le_max_right _ _)
          · exact (Real.rpow_le_one hQ.le hQ1 (by linarith)).trans (le_max_left _ _)
        rw [norm_mul, norm_mul]
        calc ‖ω‖ * ‖(Q : ℂ) ^ ((1 / 2 : ℂ) - s)‖ *
              ‖∑' m : ℕ, b (m + 1) * smoothAFEZetaDualCoefficientGeneral s (x / Q) m‖
            ≤ ‖ω‖ * max 1 (Q ^ (1 / 2 : ℝ)) * (K_loc * S_p2) := by
              refine mul_le_mul (mul_le_mul_of_nonneg_left hQ_s (norm_nonneg _))
                hts_u (norm_nonneg _) (by positivity)
          _ = M_du := by dsimp only [M_du, K_loc]; ring
      -- Pole residue bound
      have hb_pole : ‖R * smoothAFEZetaShiftedPoleResidue s x‖ ≤ M_pole := by
        rw [norm_mul, smoothAFEZetaShiftedPoleResidue, norm_div, norm_mul,
          Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.norm_exp]
        have h1s_ge : 1 / 2 ≤ ‖(1 : ℂ) - s‖ := by
          have h := Complex.abs_re_le_norm ((1 : ℂ) - s)
          rw [Complex.sub_re, Complex.one_re] at h
          linarith [le_abs_self (1 - s.re)]
        have hx_le : x ^ ((1 - s).re) ≤ max 1 x := by
          rw [show (1 - s).re = 1 - s.re by simp]
          rcases le_total 1 x with h1x | hx1
          · calc x ^ (1 - s.re) ≤ x ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le h1x (by linarith)
              _ = x := Real.rpow_one x
              _ ≤ max 1 x := le_max_right 1 x
          · exact (Real.rpow_le_one hx.le hx1 (by linarith)).trans (le_max_left _ _)
        have hexp_le : Real.exp (((1 - s) ^ (2 : ℕ)).re) ≤ Real.exp 1 := by
          refine Real.exp_le_exp.mpr ?_
          have hre2 : (((1 - s) ^ (2 : ℕ)).re) = (1 - s.re) ^ 2 - s.im ^ 2 := by
            simp only [pow_two, Complex.mul_re, Complex.sub_re, Complex.sub_im,
              Complex.one_re, Complex.one_im]
            ring
          rw [hre2]
          nlinarith [sq_nonneg s.im]
        have hquot_le : x ^ ((1 - s).re) * Real.exp (((1 - s) ^ (2 : ℕ)).re) / ‖(1 : ℂ) - s‖ ≤
            2 * max 1 x * Real.exp 1 := by
          rw [div_le_iff₀ (by linarith : 0 < ‖(1 : ℂ) - s‖)]
          have hprod : x ^ ((1 - s).re) * Real.exp (((1 - s) ^ (2 : ℕ)).re) ≤ max 1 x * Real.exp 1 :=
            mul_le_mul hx_le hexp_le (Real.exp_nonneg _) (zero_le_one.trans (le_max_left _ _))
          nlinarith [mul_nonneg (zero_le_one.trans (le_max_left 1 x)) (Real.exp_nonneg 1)]
        exact mul_le_mul_of_nonneg_left hquot_le (norm_nonneg _)
      unfold crossHeightGaussianTwoSeries
      have ht1 := norm_sub_le
        ((∑' n : ℕ, a (n + 1) * (((n + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / x))) -
          ω * (Q : ℂ) ^ ((1 / 2 : ℂ) - s) *
            ∑' m : ℕ, b (m + 1) * smoothAFEZetaDualCoefficientGeneral s (x / Q) m)
        (R * smoothAFEZetaShiftedPoleResidue s x)
      have ht2 := norm_sub_le
        (∑' n : ℕ, a (n + 1) * (((n + 1 : ℕ) : ℂ) ^ (-s) * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / x)))
        (ω * (Q : ℂ) ^ ((1 / 2 : ℂ) - s) *
          ∑' m : ℕ, b (m + 1) * smoothAFEZetaDualCoefficientGeneral s (x / Q) m)
      dsimp only [M_tot]
      linarith
    rw [Filter.tendsto_atTop]
    intro K_target
    filter_upwards [htop.eventually (eventually_ge_atTop (K_target + M_tot)), hev_bd]
      with s hs_big hs_le
    have htri := norm_sub_norm_le
      (posTruncatedZeta P₀ ((β : ℂ) + (γ₀ : ℂ) * I) s)
      (crossHeightGaussianTwoSeries a b R Q ω s x)
    linarith


/-! ### Part 3: Conductor-`12` Classification & Critical-Line Purity of All Unit-Bounded Multiplicative Twins -/

/-- Finite Dirichlet polynomial `D(s) = ∑_{d=1}^M c(d) d^{-s}` of a multiplicative zeta twin. -/
def twinDirichletPoly (M : ℕ) (c : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 M, c d * (d : ℂ) ^ (-s)

/-- Conjugate-coefficient finite Dirichlet polynomial `D^*(s) = ∑_{d=1}^M conj(c(d)) d^{-s}`. -/
def twinDirichletPolyConj (M : ℕ) (c : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 M, star (c d) * (d : ℂ) ^ (-s)

private theorem linear_prime_factor_zero_re_eq_half {p : ℕ} (hp : p.Prime)
    {cp : ℂ} (hnorm : ‖cp‖ ^ 2 = (p : ℝ)) {s : ℂ}
    (hzero : 1 + cp * (p : ℂ) ^ (-s) = 0) :
    s.re = 1 / 2 := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have heq : cp * (p : ℂ) ^ (-s) = -1 := eq_neg_of_add_eq_zero_right hzero
  have hn := congrArg (fun z : ℂ => ‖z‖ ^ 2) heq
  simp only [norm_mul, mul_pow, norm_neg, norm_one, one_pow] at hn
  rw [hnorm, show (p : ℂ) = ((p : ℝ) : ℂ) by simp,
    Complex.norm_cpow_eq_rpow_re_of_pos hp_pos, Complex.neg_re,
    ← Real.rpow_natCast ((p : ℝ) ^ (-s.re)) 2, ← Real.rpow_mul hp_pos.le] at hn
  have h1 : (p : ℝ) ^ ((1 : ℝ) + (-s.re * 2)) = (p : ℝ) ^ (0 : ℝ) := by
    rw [Real.rpow_add hp_pos, Real.rpow_one, Real.rpow_zero]
    simpa using hn
  have hexp := Real.rpow_right_inj hp_pos hp1.ne' |>.mp h1
  linarith

private theorem quadratic_two_factor_zero_re_eq_half {a2 a4 : ℂ}
    (ha2 : ‖a2‖ ≤ 1) (ha4 : ‖a4‖ ≤ 1) (hdiff : ‖a4 - a2‖ ^ 2 = 4)
    {s : ℂ} (hzero : 1 + (a2 - 1) * (2 : ℂ) ^ (-s) + (a4 - a2) * (4 : ℂ) ^ (-s) = 0) :
    s.re = 1 / 2 := by
  -- Step 1: Parallelogram equality forces `a4 = -a2` and `Complex.normSq a2 = 1`.
  have hnsq2 : Complex.normSq a2 ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg a2]
  have hnsq4 : Complex.normSq a4 ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg a4]
  have hnsq_diff : Complex.normSq (a4 - a2) = 4 := by
    rwa [Complex.normSq_eq_norm_sq]
  rw [Complex.normSq_apply] at hnsq2 hnsq4
  have hdiff_coord : (a4.re - a2.re) ^ 2 + (a4.im - a2.im) ^ 2 = 4 := by
    simpa [Complex.normSq_apply, pow_two] using hnsq_diff
  have ha4_neg : a4 = -a2 := by
    apply Complex.ext
    · simp; nlinarith [sq_nonneg (a4.re + a2.re), sq_nonneg (a4.im + a2.im)]
    · simp; nlinarith [sq_nonneg (a4.re + a2.re), sq_nonneg (a4.im + a2.im)]
  have hu_nsq : Complex.normSq a2 = 1 := by
    rw [Complex.normSq_apply]
    nlinarith [sq_nonneg (a4.re + a2.re), sq_nonneg (a4.im + a2.im)]
  -- Step 2: Rewrite `1 - X = a2 * X * (2 * X - 1)` with `X = 2^{-s}` and take `Complex.normSq`.
  set X : ℂ := (2 : ℂ) ^ (-s)
  have h4X : (4 : ℂ) ^ (-s) = X ^ 2 := by
    dsimp only [X]
    rw [pow_two, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      ← Complex.mul_cpow_ofReal_nonneg two_pos.le two_pos.le (-s)]
    norm_num
  rw [ha4_neg, h4X] at hzero
  have hrel : 1 - X = a2 * X * (2 * X - 1) := by linear_combination hzero
  have hnsq_rel := congrArg Complex.normSq hrel
  rw [map_mul, map_mul, hu_nsq, one_mul] at hnsq_rel
  -- Step 3: Polynomial factorization `(2 r - 1) * (2 (x^2 + y^2) + 1 - 2 x) = 0` forces `r = 1 / 2`.
  have hr_half : Complex.normSq X = 1 / 2 := by
    rw [Complex.normSq_apply (1 - X), Complex.normSq_apply X, Complex.normSq_apply (2 * X - 1)] at hnsq_rel
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      Complex.mul_re, Complex.mul_im] at hnsq_rel
    have h4_re : ((2 : ℂ) * X).re = 2 * X.re := by simp
    have h4_im : ((2 : ℂ) * X).im = 2 * X.im := by simp
    have hcoord : (1 - X.re) ^ 2 + (-X.im) ^ 2 =
        (X.re ^ 2 + X.im ^ 2) * ((2 * X.re - 1) ^ 2 + (2 * X.im) ^ 2) := by
      simpa [pow_two] using hnsq_rel
    have hfac : (2 * (X.re ^ 2 + X.im ^ 2) - 1) *
        (2 * (X.re - 1 / 2) ^ 2 + 2 * X.im ^ 2 + 1 / 2) = 0 := by
      nlinarith [hcoord]
    have hpos_fac : 0 < 2 * (X.re - 1 / 2) ^ 2 + 2 * X.im ^ 2 + 1 / 2 := by positivity
    have hzero_fac : 2 * (X.re ^ 2 + X.im ^ 2) - 1 = 0 :=
      (mul_eq_zero.mp hfac).resolve_right hpos_fac.ne'
    rw [Complex.normSq_apply]
    linarith
  -- Step 4: Deduce `s.re = 1 / 2` from `‖2^{-s}‖^2 = 1 / 2`.
  rw [Complex.normSq_eq_norm_sq, show X = ((2 : ℝ) : ℂ) ^ (-s) by simp [X],
    Complex.norm_cpow_eq_rpow_re_of_pos two_pos, Complex.neg_re,
    ← Real.rpow_natCast ((2 : ℝ) ^ (-s.re)) 2, ← Real.rpow_mul two_pos.le] at hr_half
  have h1 : (2 : ℝ) ^ (-s.re * 2) = (2 : ℝ) ^ (-1 : ℝ) := by
    rw [Real.rpow_neg_one]; norm_num at hr_half ⊢; exact hr_half
  have hexp := Real.rpow_right_inj two_pos (by norm_num) |>.mp h1
  linarith

/-- **Conductor-`12` classification and critical-line purity of all unit-bounded multiplicative
twins:** let `c : ℕ → ℂ` be multiplicative (`c(1) = 1`, `c(mn) = c(m)c(n)` on coprime pairs) and
supported on `[1, M]`, with convolved twin coefficients `a(n) = ∑_{d ∣ n} c(d)`. If:
1. `‖a(n)‖ ≤ 1` for all `n ≥ 1`, and
2. `F(s) = ζ(s) D(s)` (`D = twinDirichletPoly M c`) satisfies cross-height completion reflection at
   conductor `Q > 0` and root number `‖ω‖ = 1` along `s = -1 + i t` (`t ∈ ℝ`),
then **`Q` is a positive integer dividing `12`** (`Q ∈ {1, 2, 3, 4, 6, 12}`) and **every zero of
`D(s)` lies on the critical line `Re s = 1 / 2`**. -/
theorem unit_bounded_multiplicative_twin_classification
    {M : ℕ} (hM : 1 ≤ M) {c : ArithmeticFunction ℂ}
    (hc_supp : ∀ d : ℕ, M < d → c d = 0)
    (hc_mul : c.IsMultiplicative)
    {Q : ℝ} (hQ : 0 < Q) {ω : ℂ} (hω : ‖ω‖ = 1)
    (hunit : ∀ n : ℕ, 1 ≤ n → ‖∑ d ∈ n.divisors, c d‖ ≤ 1)
    (hrefl : ∀ t : ℝ,
      let s : ℂ := (-1 : ℂ) + (t : ℂ) * I
      (Q : ℂ) ^ (s / 2) * completedRiemannZeta s * twinDirichletPoly M c s =
        ω * (Q : ℂ) ^ ((1 - s) / 2) * completedRiemannZeta (1 - s) *
          twinDirichletPolyConj M c (1 - s)) :
    (∃ q : ℕ, 1 ≤ q ∧ q ∣ 12 ∧ Q = (q : ℝ)) ∧
      ∀ z : ℂ, twinDirichletPoly M c z = 0 → z.re = 1 / 2 := by
  classical
  set a : ℕ → ℂ := fun n => ∑ d ∈ n.divisors, c d
  have hc1 : c 1 = 1 := hc_mul.1
  -- Step 1: Cancel `completedRiemannZeta` on `s = -1 + i t` and extract Bohr coefficients.
  have htrig_eq : ∀ t : ℝ,
      (∑ d ∈ Finset.Icc 1 M,
          (c d * (((d : ℝ) / Q : ℝ) : ℂ)) * GaloisForLFunctions.expChar (Real.log (Q / d)) t) =
        ∑ m ∈ Finset.Icc 1 M,
          (ω * ((Real.sqrt Q : ℝ) : ℂ) * star (c m) * ((((m : ℝ) ^ 2)⁻¹ : ℝ) : ℂ)) *
            GaloisForLFunctions.expChar (Real.log m) t := by
    intro t
    set s : ℂ := (-1 : ℂ) + (t : ℂ) * I
    have hs0 : s ≠ 0 := fun h => by have := congrArg Complex.re h; simp [s] at this
    have h1s0 : 1 - s ≠ 0 := fun h => by have := congrArg Complex.re h; simp [s] at this
    have h1s_re : 1 < (1 - s).re := by simp [s]
    have hΛ_ne : completedRiemannZeta (1 - s) ≠ 0 := by
      have hζ_ne : riemannZeta (1 - s) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re h1s_re
      have hΓ_ne : Complex.Gammaℝ (1 - s) ≠ 0 :=
        Complex.Gammaℝ_ne_zero_of_re_pos (zero_lt_one.trans h1s_re)
      rw [riemannZeta_def_of_ne_zero h1s0] at hζ_ne
      exact fun h0 => hζ_ne (by rw [h0, zero_div])
    have hfe_line : (Q : ℂ) ^ (s / 2) * completedRiemannZeta s * twinDirichletPoly M c s =
        ω * (Q : ℂ) ^ ((1 - s) / 2) * completedRiemannZeta (1 - s) *
          twinDirichletPolyConj M c (1 - s) := hrefl t
    have h1s_Λ : completedRiemannZeta s = completedRiemannZeta (1 - s) :=
      (completedRiemannZeta_one_sub s).symm
    rw [h1s_Λ] at hfe_line
    have hcancel_Λ : (Q : ℂ) ^ (s / 2) * twinDirichletPoly M c s =
        ω * (Q : ℂ) ^ ((1 - s) / 2) * twinDirichletPolyConj M c (1 - s) := by
      apply mul_left_cancel₀ hΛ_ne
      linear_combination hfe_line
    have hQ0c : (Q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hQ.ne'
    have hmul_Q := congrArg (fun z => (Q : ℂ) ^ (s / 2) * z) hcancel_Λ
    have hQ_lhs : (Q : ℂ) ^ (s / 2) * ((Q : ℂ) ^ (s / 2) * twinDirichletPoly M c s) =
        (Q : ℂ) ^ s * twinDirichletPoly M c s := by
      rw [← mul_assoc, ← Complex.cpow_add _ _ hQ0c, add_halves]
    have hQ_rhs : (Q : ℂ) ^ (s / 2) *
        (ω * (Q : ℂ) ^ ((1 - s) / 2) * twinDirichletPolyConj M c (1 - s)) =
        ω * ((Real.sqrt Q : ℝ) : ℂ) * twinDirichletPolyConj M c (1 - s) := by
      have h12 : (Q : ℂ) ^ (s / 2) * (Q : ℂ) ^ ((1 - s) / 2) = ((Real.sqrt Q : ℝ) : ℂ) := by
        rw [← Complex.cpow_add _ _ hQ0c, show s / 2 + (1 - s) / 2 = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
          ← Complex.ofReal_cpow hQ.le, Real.sqrt_eq_rpow]
      calc (Q : ℂ) ^ (s / 2) * (ω * (Q : ℂ) ^ ((1 - s) / 2) * twinDirichletPolyConj M c (1 - s))
          = ω * ((Q : ℂ) ^ (s / 2) * (Q : ℂ) ^ ((1 - s) / 2)) * twinDirichletPolyConj M c (1 - s) := by ring
        _ = ω * ((Real.sqrt Q : ℝ) : ℂ) * twinDirichletPolyConj M c (1 - s) := by rw [h12]
    rw [hQ_lhs, hQ_rhs] at hmul_Q
    -- Rewrite LHS and RHS terms into `expChar`.
    have hlhs_rw : (Q : ℂ) ^ s * twinDirichletPoly M c s =
        ∑ d ∈ Finset.Icc 1 M,
          (c d * (((d : ℝ) / Q : ℝ) : ℂ)) * GaloisForLFunctions.expChar (Real.log (Q / d)) t := by
      unfold twinDirichletPoly
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun d hd => ?_
      have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hd).1
      have hQd_pos : 0 < Q / (d : ℝ) := div_pos hQ hd_pos
      have hpow_Qd : (Q : ℂ) ^ s * (d : ℂ) ^ (-s) = ((Q / (d : ℝ) : ℝ) : ℂ) ^ s := by
        have h := cpow_div_pos_neg hQ hd_pos (-s)
        rw [neg_neg] at h
        simpa [mul_comm] using h.symm
      have hexp_Qd : ((Q / (d : ℝ) : ℝ) : ℂ) ^ s =
          (((d : ℝ) / Q : ℝ) : ℂ) * GaloisForLFunctions.expChar (Real.log (Q / d)) t := by
        rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hQd_pos.ne'),
          ← Complex.ofReal_log hQd_pos.le]
        have hlin : ((Real.log (Q / d) : ℝ) : ℂ) * s =
            ((-Real.log (Q / d) : ℝ) : ℂ) + ((Real.log (Q / d) * t : ℝ) : ℂ) * I := by
          dsimp only [s]; push_cast; ring
        rw [hlin, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_neg,
          Real.exp_log hQd_pos, inv_div, GaloisForLFunctions.expChar]
        congr 2; push_cast; ring
      calc (Q : ℂ) ^ s * (c d * (d : ℂ) ^ (-s))
          = c d * ((Q : ℂ) ^ s * (d : ℂ) ^ (-s)) := by ring
        _ = (c d * (((d : ℝ) / Q : ℝ) : ℂ)) * GaloisForLFunctions.expChar (Real.log (Q / d)) t := by
            rw [hpow_Qd, hexp_Qd]; ring
    have hrhs_rw : ω * ((Real.sqrt Q : ℝ) : ℂ) * twinDirichletPolyConj M c (1 - s) =
        ∑ m ∈ Finset.Icc 1 M,
          (ω * ((Real.sqrt Q : ℝ) : ℂ) * star (c m) * ((((m : ℝ) ^ 2)⁻¹ : ℝ) : ℂ)) *
            GaloisForLFunctions.expChar (Real.log m) t := by
      unfold twinDirichletPolyConj
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m hm => ?_
      have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hm).1
      have hexp_m : (m : ℂ) ^ (-(1 - s)) =
          ((((m : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) * GaloisForLFunctions.expChar (Real.log m) t := by
        rw [show (m : ℂ) = ((m : ℝ) : ℂ) by simp,
          Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hm_pos.ne'),
          ← Complex.ofReal_log hm_pos.le]
        have hlin : ((Real.log m : ℝ) : ℂ) * (-(1 - s)) =
            ((-2 * Real.log m : ℝ) : ℂ) + ((Real.log m * t : ℝ) : ℂ) * I := by
          dsimp only [s]; push_cast; ring
        have hexp2 : Real.exp (-2 * Real.log m) = ((m : ℝ) ^ 2)⁻¹ := by
          rw [show -2 * Real.log m = -(2 * Real.log m) by ring, Real.exp_neg,
            show 2 * Real.log m = Real.log ((m : ℝ) ^ 2) by rw [Real.log_pow]; ring,
            Real.exp_log (pow_pos hm_pos 2)]
        rw [hlin, Complex.exp_add, ← Complex.ofReal_exp, hexp2, GaloisForLFunctions.expChar]
        congr 2; push_cast; ring
      rw [hexp_m]; ring
    rwa [hlhs_rw, hrhs_rw] at hmul_Q
  have hbohr : ∀ lam : ℝ,
      (∑ d ∈ Finset.Icc 1 M,
          if Real.log (Q / d) = lam then c d * (((d : ℝ) / Q : ℝ) : ℂ) else 0) =
        ∑ m ∈ Finset.Icc 1 M,
          if Real.log m = lam then
            ω * ((Real.sqrt Q : ℝ) : ℂ) * star (c m) * ((((m : ℝ) ^ 2)⁻¹ : ℝ) : ℂ)
          else 0 := by
    intro lam
    have h := congrArg (fun f => GaloisForLFunctions.bohrCoefficient f lam) (funext htrig_eq)
    simpa only [GaloisForLFunctions.bohrCoefficient_sum_expChar] using h
  -- Step 2: Identify `Q = q` where `q = max {d ∈ Icc 1 M | c d ≠ 0}`.
  set S : Finset ℕ := (Finset.Icc 1 M).filter (fun d => c d ≠ 0)
  have h1_mem_S : 1 ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, hM⟩, by rw [hc1]; exact one_ne_zero⟩
  set q : ℕ := S.max' ⟨1, h1_mem_S⟩
  have hq_mem_S : q ∈ S := Finset.max'_mem S ⟨1, h1_mem_S⟩
  have hq_Icc : q ∈ Finset.Icc 1 M := (Finset.mem_filter.mp hq_mem_S).1
  have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq_Icc).1
  have hqM : q ≤ M := (Finset.mem_Icc.mp hq_Icc).2
  have hcq_ne : c q ≠ 0 := (Finset.mem_filter.mp hq_mem_S).2
  have hq_pos : 0 < q := hq1
  have hq0 : q ≠ 0 := by omega
  -- Evaluate `hbohr` at `lam = 0` (`m = 1`) to get `Q = d₀ ≤ q`.
  have hQ_le_q : Q ≤ (q : ℝ) := by
    have hb0 := hbohr 0
    have hrhs0 : (∑ m ∈ Finset.Icc 1 M,
        if Real.log m = 0 then
          ω * ((Real.sqrt Q : ℝ) : ℂ) * star (c m) * ((((m : ℝ) ^ 2)⁻¹ : ℝ) : ℂ)
        else 0) = ω * ((Real.sqrt Q : ℝ) : ℂ) := by
      rw [Finset.sum_eq_single 1]
      · simp [hc1]
      · intro m hm hm1
        have hm_gt1 : (1 : ℝ) < (m : ℝ) := by
          have := (Finset.mem_Icc.mp hm).1; exact_mod_cast (by omega : 1 < m)
        exact if_neg (Real.log_pos hm_gt1).ne'
      · intro hnot; exact absurd (Finset.mem_Icc.mpr ⟨le_rfl, hM⟩) hnot
    rw [hrhs0] at hb0
    have hrhs_ne : ω * ((Real.sqrt Q : ℝ) : ℂ) ≠ 0 :=
      mul_ne_zero (fun h => by rw [h, norm_zero] at hω; norm_num at hω)
        (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hQ).ne')
    rw [← hb0] at hrhs_ne
    obtain ⟨d₀, hd₀_mem, hd₀_ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hrhs_ne
    by_cases hlog : Real.log (Q / d₀) = 0
    · rw [if_pos hlog] at hd₀_ne
      have hcd₀ : c d₀ ≠ 0 := left_ne_zero_of_mul hd₀_ne
      have hd₀_pos : (0 : ℝ) < (d₀ : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hd₀_mem).1
      have hQd₀ : Q / (d₀ : ℝ) = 1 := by
        have := congrArg Real.exp hlog
        rwa [Real.exp_log (div_pos hQ hd₀_pos), Real.exp_zero] at this
      have hQ_eq : Q = (d₀ : ℝ) := (div_eq_one_iff_eq hd₀_pos.ne').mp hQd₀
      have hd₀_le_q : d₀ ≤ q := Finset.le_max' S d₀ (Finset.mem_filter.mpr ⟨hd₀_mem, hcd₀⟩)
      rw [hQ_eq]; exact_mod_cast hd₀_le_q
    · rw [if_neg hlog] at hd₀_ne; exact (hd₀_ne rfl).elim
  -- Evaluate `hbohr` at `lam = Real.log (Q / q)` (`d = q`) to get `(q : ℝ) ≤ Q`.
  have hq_le_Q : (q : ℝ) ≤ Q := by
    have hbq := hbohr (Real.log (Q / q))
    have hlhs_q : (∑ d ∈ Finset.Icc 1 M,
        if Real.log (Q / d) = Real.log (Q / q) then c d * (((d : ℝ) / Q : ℝ) : ℂ) else 0) =
        c q * (((q : ℝ) / Q : ℝ) : ℂ) := by
      rw [Finset.sum_eq_single q]
      · rw [if_pos rfl]
      · intro d hd hdq
        refine if_neg fun hlog => hdq ?_
        have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hd).1
        have hq_posR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq_pos
        have hexp := congrArg Real.exp hlog
        rw [Real.exp_log (div_pos hQ hd_pos), Real.exp_log (div_pos hQ hq_posR)] at hexp
        have hdqR : (d : ℝ) = (q : ℝ) := by
          have := (div_eq_div_iff hd_pos.ne' hq_posR.ne').mp hexp
          nlinarith [hQ]
        exact_mod_cast hdqR
      · intro hnot; exact absurd hq_Icc hnot
    rw [hlhs_q] at hbq
    have hlhs_ne : c q * (((q : ℝ) / Q : ℝ) : ℂ) ≠ 0 :=
      mul_ne_zero hcq_ne (Complex.ofReal_ne_zero.mpr (div_pos (by exact_mod_cast hq_pos) hQ).ne')
    rw [hbq] at hlhs_ne
    obtain ⟨m₀, hm₀_mem, hm₀_ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hlhs_ne
    by_cases hlog : Real.log m₀ = Real.log (Q / q)
    · have hm₀_pos : (0 : ℝ) < (m₀ : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hm₀_mem).1
      have hq_posR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq_pos
      have hexp := congrArg Real.exp hlog
      rw [Real.exp_log hm₀_pos, Real.exp_log (div_pos hQ hq_posR)] at hexp
      have hm₀1 : (1 : ℝ) ≤ (m₀ : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hm₀_mem).1
      have hQ_mul : Q = (m₀ : ℝ) * (q : ℝ) := (eq_div_iff hq_posR.ne').mp hexp |>.symm
      nlinarith
    · rw [if_neg hlog] at hm₀_ne; exact (hm₀_ne rfl).elim
  have hQ_eq_q : Q = (q : ℝ) := le_antisymm hQ_le_q hq_le_Q
  -- Step 3: Exact divisor reciprocity `c d = 0` (`¬ d ∣ q`) and `c d = ω q^{-1/2} d conj(c(q / d))` (`d ∣ q`).
  have hrec : ∀ d ∈ Finset.Icc 1 M,
      (¬(d ∣ q) → c d = 0) ∧
      (d ∣ q → c d = ω * (((Real.sqrt q)⁻¹ : ℝ) : ℂ) * (d : ℂ) * star (c (q / d))) := by
    intro d hd
    have hd_pos : 0 < d := (Finset.mem_Icc.mp hd).1
    have hd_posR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd_pos
    have hq_posR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq_pos
    have hbd := hbohr (Real.log (Q / d))
    have hlhs_d : (∑ k ∈ Finset.Icc 1 M,
        if Real.log (Q / k) = Real.log (Q / d) then c k * (((k : ℝ) / Q : ℝ) : ℂ) else 0) =
        c d * (((d : ℝ) / (q : ℝ) : ℝ) : ℂ) := by
      rw [Finset.sum_eq_single d]
      · rw [if_pos rfl, hQ_eq_q]
      · intro k hk hkd
        refine if_neg fun hlog => hkd ?_
        have hk_posR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hk).1
        have hexp := congrArg Real.exp hlog
        rw [Real.exp_log (div_pos hQ hk_posR), Real.exp_log (div_pos hQ hd_posR)] at hexp
        have hkdR : (k : ℝ) = (d : ℝ) := by
          have := (div_eq_div_iff hk_posR.ne' hd_posR.ne').mp hexp
          nlinarith [hQ]
        exact_mod_cast hkdR
      · intro hnot; exact absurd hd hnot
    rw [hlhs_d] at hbd
    constructor
    · intro hndvd
      have hrhs_zero : (∑ m ∈ Finset.Icc 1 M,
          if Real.log m = Real.log (Q / d) then
            ω * ((Real.sqrt Q : ℝ) : ℂ) * star (c m) * ((((m : ℝ) ^ 2)⁻¹ : ℝ) : ℂ)
          else 0) = 0 := by
        refine Finset.sum_eq_zero fun m hm => if_neg fun hlog => hndvd ?_
        have hm_posR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hm).1
        have hexp := congrArg Real.exp hlog
        rw [Real.exp_log hm_posR, hQ_eq_q, Real.exp_log (div_pos hq_posR hd_posR)] at hexp
        have hmulR : (d : ℝ) * (m : ℝ) = (q : ℝ) := by
          have := (eq_div_iff hd_posR.ne').mp hexp; linarith
        exact ⟨m, by exact_mod_cast hmulR.symm⟩
      rw [hrhs_zero] at hbd
      exact (mul_eq_zero.mp hbd).resolve_right
        (Complex.ofReal_ne_zero.mpr (div_pos hd_posR hq_posR).ne')
    · intro hdvd
      set m₀ : ℕ := q / d
      have hm₀_mul : d * m₀ = q := Nat.mul_div_cancel' hdvd
      have hm₀_pos : 0 < m₀ := by
        by_contra hm0; push Not at hm0; interval_cases m₀; simp at hm₀_mul; omega
      have hm₀_le_q : m₀ ≤ q := Nat.div_le_self q d
      have hm₀_Icc : m₀ ∈ Finset.Icc 1 M := Finset.mem_Icc.mpr ⟨hm₀_pos, hm₀_le_q.trans hqM⟩
      have hQd_eq : Q / (d : ℝ) = (m₀ : ℝ) := by
        rw [hQ_eq_q, div_eq_iff hd_posR.ne']
        exact_mod_cast ((mul_comm m₀ d).trans hm₀_mul).symm
      have hrhs_m₀ : (∑ m ∈ Finset.Icc 1 M,
          if Real.log m = Real.log (Q / d) then
            ω * ((Real.sqrt Q : ℝ) : ℂ) * star (c m) * ((((m : ℝ) ^ 2)⁻¹ : ℝ) : ℂ)
          else 0) =
          ω * ((Real.sqrt q : ℝ) : ℂ) * star (c m₀) * ((((m₀ : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) := by
        rw [Finset.sum_eq_single m₀]
        · rw [hQd_eq, if_pos rfl, hQ_eq_q]
        · intro m hm hmm₀
          refine if_neg fun hlog => hmm₀ ?_
          rw [hQd_eq] at hlog
          have hm_posR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hm).1
          have hm₀_posR : (0 : ℝ) < (m₀ : ℝ) := by exact_mod_cast hm₀_pos
          have hexp := congrArg Real.exp hlog
          rw [Real.exp_log hm_posR, Real.exp_log hm₀_posR] at hexp
          exact_mod_cast hexp
        · intro hnot; exact absurd hm₀_Icc hnot
      rw [hrhs_m₀] at hbd
      have hsq_q : (Real.sqrt q) ^ 2 = (q : ℝ) := Real.sq_sqrt hq_posR.le
      have hsqrt_ne : (Real.sqrt q : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hq_posR).ne'
      have hm₀_posR : (0 : ℝ) < (m₀ : ℝ) := by exact_mod_cast hm₀_pos
      have hm₀_eqR : (m₀ : ℝ) = (q : ℝ) / (d : ℝ) := by
        rw [eq_div_iff hd_posR.ne']
        exact_mod_cast (mul_comm m₀ d).trans hm₀_mul
      have hreal_id : (((d : ℝ) / (q : ℝ))⁻¹ * (Real.sqrt q * ((m₀ : ℝ) ^ 2)⁻¹)) =
          (Real.sqrt q)⁻¹ * (d : ℝ) := by
        rw [hm₀_eqR]
        field_simp [hd_posR.ne', hq_posR.ne', hsqrt_ne]
        nlinarith [hsq_q]
      have hcd_eq : c d = ((((d : ℝ) / (q : ℝ))⁻¹ : ℝ) : ℂ) *
          (ω * ((Real.sqrt q : ℝ) : ℂ) * star (c m₀) * ((((m₀ : ℝ) ^ 2)⁻¹ : ℝ) : ℂ)) := by
        have hinv_dq : (((d : ℝ) / (q : ℝ) : ℝ) : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr (div_pos hd_posR hq_posR).ne'
        apply mul_right_cancel₀ hinv_dq
        rw [hbd]
        have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd_pos.ne'
        have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq_pos.ne'
        have hmC : (m₀ : ℂ) ≠ 0 := by exact_mod_cast hm₀_pos.ne'
        push_cast; field_simp [hdC, hqC, hmC]
      rw [hcd_eq]
      have hcast_id := congrArg (fun r : ℝ => (r : ℂ)) hreal_id
      push_cast at hcast_id ⊢
      linear_combination (ω * star (c m₀)) * hcast_id
  -- Step 4: Prime-power norm law `‖c (p ^ e)‖^2 = p ^ e` and bound `p ^ e ≤ 4`, giving `q ∣ 12`.
  have ha_prime_pow : ∀ {p : ℕ}, p.Prime → ∀ k : ℕ, 1 ≤ k →
      c (p ^ k) = a (p ^ k) - a (p ^ (k - 1)) := by
    intro p hp k hk
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    dsimp only [a]
    rw [Nat.succ_sub_one, Nat.divisors_prime_pow hp, Nat.divisors_prime_pow hp,
      Finset.sum_map, Finset.sum_map, Finset.sum_range_succ]
    simp
  have hpe_norm_sq : ∀ {p : ℕ}, p.Prime → q.factorization p ≠ 0 →
      ‖c (p ^ q.factorization p)‖ ^ 2 = ((p ^ q.factorization p : ℕ) : ℝ) := by
    intro p hp he0
    set e : ℕ := q.factorization p
    have hdvd_pe : p ^ e ∣ q := Nat.ordProj_dvd q p
    set q' : ℕ := q / p ^ e
    have hmul_pe : p ^ e * q' = q := Nat.mul_div_cancel' hdvd_pe
    have hcop_pe : Nat.Coprime (p ^ e) q' := (Nat.coprime_ordCompl hp hq0).pow_left e
    have hpe_pos : 0 < p ^ e := pow_pos hp.pos e
    have hq'_pos : 0 < q' := by
      by_contra h0; push Not at h0; interval_cases q'; simp at hmul_pe; omega
    have hq'_dvd : q' ∣ q := ⟨p ^ e, by rw [← hmul_pe, mul_comm]⟩
    have hq'_Icc : q' ∈ Finset.Icc 1 M :=
      Finset.mem_Icc.mpr ⟨hq'_pos, (Nat.div_le_self q _).trans hqM⟩
    have hdiv_q' : q / q' = p ^ e :=
      Nat.div_eq_of_eq_mul_left hq'_pos (mul_comm (p ^ e) q' ▸ hmul_pe.symm)
    have hcq_rec := (hrec q hq_Icc).2 dvd_rfl
    rw [Nat.div_self hq_pos, hc1, star_one, mul_one] at hcq_rec
    have hcq_norm : ‖c q‖ ^ 2 = (q : ℝ) := by
      have hn := congrArg (fun z : ℂ => ‖z‖ ^ 2) hcq_rec
      simp only [norm_mul, hω, one_mul, Complex.norm_real, Complex.norm_natCast,
        Real.norm_eq_abs, abs_inv, abs_of_pos (Real.sqrt_pos.mpr (by exact_mod_cast hq_pos))] at hn
      rw [hn, mul_pow, inv_pow, Real.sq_sqrt (Nat.cast_nonneg q)]
      have hqR0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq0
      field_simp [hqR0]
    have hcq'_rec := (hrec q' hq'_Icc).2 hq'_dvd
    rw [hdiv_q'] at hcq'_rec
    have hcq'_norm : ‖c q'‖ ^ 2 = ((q' : ℝ) ^ 2 / (q : ℝ)) * ‖c (p ^ e)‖ ^ 2 := by
      have hn := congrArg (fun z : ℂ => ‖z‖ ^ 2) hcq'_rec
      simp only [norm_mul, hω, one_mul, Complex.norm_real, Complex.norm_natCast,
        norm_star, Real.norm_eq_abs, abs_inv,
        abs_of_pos (Real.sqrt_pos.mpr (by exact_mod_cast hq_pos))] at hn
      rw [hn, mul_pow, mul_pow, inv_pow, Real.sq_sqrt (Nat.cast_nonneg q)]
      ring
    have hmul_c : c q = c (p ^ e) * c q' := by
      rw [← hmul_pe]; exact hc_mul.2 hcop_pe
    have hmul_norm : ‖c q‖ ^ 2 = ‖c (p ^ e)‖ ^ 2 * ‖c q'‖ ^ 2 := by
      rw [hmul_c, norm_mul, mul_pow]
    -- Wait: also evaluate `c (p ^ e)` via reciprocity at `d = p ^ e` (`q / p ^ e = q'`)!
    have hpe_Icc : p ^ e ∈ Finset.Icc 1 M :=
      Finset.mem_Icc.mpr ⟨hpe_pos, (Nat.le_of_dvd hq_pos hdvd_pe).trans hqM⟩
    have hcpe_rec := (hrec (p ^ e) hpe_Icc).2 hdvd_pe
    have hcpe_norm : ‖c (p ^ e)‖ ^ 2 = (((p ^ e : ℕ) : ℝ) ^ 2 / (q : ℝ)) * ‖c q'‖ ^ 2 := by
      have hn := congrArg (fun z : ℂ => ‖z‖ ^ 2) hcpe_rec
      simp only [norm_mul, hω, one_mul, Complex.norm_real, Complex.norm_natCast,
        norm_star, Real.norm_eq_abs, abs_inv,
        abs_of_pos (Real.sqrt_pos.mpr (by exact_mod_cast hq_pos))] at hn
      rw [hn, mul_pow, mul_pow, inv_pow, Real.sq_sqrt (Nat.cast_nonneg q)]
      dsimp only [q']
      ring
    -- Combine `hcpe_norm` and `hmul_norm`: `‖c (p ^ e)‖ ^ 4 = ((p ^ e)^2 / q) * q * ...`!
    have hqR_eq : (q : ℝ) = ((p ^ e : ℕ) : ℝ) * (q' : ℝ) := by exact_mod_cast hmul_pe.symm
    have hqR_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq_pos
    have hq'R_pos : (0 : ℝ) < (q' : ℝ) := by exact_mod_cast hq'_pos
    have hcpe_pos : 0 < ‖c (p ^ e)‖ ^ 2 := by
      by_contra h0; push Not at h0
      have hz : ‖c (p ^ e)‖ ^ 2 = 0 := le_antisymm h0 (sq_nonneg _)
      rw [hz, zero_mul, hcq_norm] at hmul_norm
      linarith
    have hsq_eq : (‖c (p ^ e)‖ ^ 2) ^ 2 = (((p ^ e : ℕ) : ℝ)) ^ 2 := by
      have h1 : (q : ℝ) = ‖c (p ^ e)‖ ^ 2 * (((q' : ℝ) ^ 2 / (q : ℝ)) * ‖c (p ^ e)‖ ^ 2) := by
        rw [← hcq'_norm, ← hmul_norm, hcq_norm]
      rw [hqR_eq] at h1
      field_simp [hq'R_pos.ne', (show ((p ^ e : ℕ) : ℝ) ≠ 0 by positivity)] at h1
      nlinarith [h1]
    nlinarith [sq_nonneg (‖c (p ^ e)‖ ^ 2 - ((p ^ e : ℕ) : ℝ)), hcpe_pos]
  have hpe_le4 : ∀ {p : ℕ}, p.Prime → q.factorization p ≠ 0 → p ^ q.factorization p ≤ 4 := by
    intro p hp he0
    set e : ℕ := q.factorization p
    have he1 : 1 ≤ e := Nat.one_le_iff_ne_zero.mpr he0
    have hdiff := ha_prime_pow hp e he1
    have htri : ‖c (p ^ e)‖ ≤ 2 := by
      rw [hdiff]
      have h1 := hunit (p ^ e) (pow_pos hp.pos e)
      have h2 := hunit (p ^ (e - 1)) (pow_pos hp.pos (e - 1))
      linarith [norm_sub_le (a (p ^ e)) (a (p ^ (e - 1)))]
    have hsq : ((p ^ e : ℕ) : ℝ) ≤ 4 := by
      rw [← hpe_norm_sq hp he0]
      nlinarith [norm_nonneg (c (p ^ e))]
    exact_mod_cast hsq
  have hf3_2 : (3 : ℕ).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by decide)
  have hf2_3 : (2 : ℕ).factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by decide)
  have hf4_3 : (4 : ℕ).factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by decide)
  have hf4_2 : (4 : ℕ).factorization 2 = 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.Prime.factorization_pow Nat.prime_two,
      Finsupp.single_eq_same]
  have hf6_2 : (6 : ℕ).factorization 2 = 1 := by
    rw [show (6 : ℕ) = 2 * 3 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_two, hf3_2]
  have hf6_3 : (6 : ℕ).factorization 3 = 1 := by
    rw [show (6 : ℕ) = 2 * 3 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, hf2_3, Nat.Prime.factorization_self Nat.prime_three, zero_add]
  have hf12_2 : (12 : ℕ).factorization 2 = 2 := by
    rw [show (12 : ℕ) = 4 * 3 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, hf4_2, hf3_2]
  have hf12_3 : (12 : ℕ).factorization 3 = 1 := by
    rw [show (12 : ℕ) = 4 * 3 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, hf4_3, Nat.Prime.factorization_self Nat.prime_three, zero_add]
  have hq_dvd_12 : q ∣ 12 := by
    rw [← Nat.factorization_le_iff_dvd hq0 (by norm_num)]
    intro p
    by_cases he0 : q.factorization p = 0
    · simp [he0]
    · have hp : p.Prime := by
        by_contra hnp
        exact he0 (Nat.factorization_eq_zero_of_not_prime q hnp)
      have hle4 := hpe_le4 hp he0
      have hp_le4 : p ≤ 4 := (Nat.le_self_pow he0 p).trans hle4
      have hp_ge2 : 2 ≤ p := hp.two_le
      interval_cases p
      · -- `p = 2`: `2 ^ e ≤ 4 ⟹ e ≤ 2 = (12).factorization 2`.
        have he_le2 : q.factorization 2 ≤ 2 := by
          by_contra hgt
          have : 2 ^ 3 ≤ 2 ^ q.factorization 2 := Nat.pow_le_pow_right two_pos (by omega)
          omega
        omega
      · -- `p = 3`: `3 ^ e ≤ 4 ⟹ e ≤ 1 = (12).factorization 3`.
        have he_le1 : q.factorization 3 ≤ 1 := by
          by_contra hgt
          have : 3 ^ 2 ≤ 3 ^ q.factorization 3 := Nat.pow_le_pow_right (by omega) (by omega)
          omega
        omega
      · exfalso; exact absurd hp (by decide)
  refine ⟨⟨q, hq1, hq_dvd_12, hQ_eq_q⟩, fun z hz => ?_⟩
  -- Step 5: Reduce `twinDirichletPoly M c z` to `q.divisors` and check the 6 divisors of `12`.
  have hpoly_div : twinDirichletPoly M c z = ∑ d ∈ q.divisors, c d * (d : ℂ) ^ (-z) := by
    unfold twinDirichletPoly
    have hsub : q.divisors ⊆ Finset.Icc 1 M := fun d hd =>
      Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,
        (Nat.le_of_dvd hq_pos (Nat.dvd_of_mem_divisors hd)).trans hqM⟩
    refine (Finset.sum_subset hsub fun d hd hnot => ?_).symm
    have hndvd : ¬(d ∣ q) := fun hdvd => hnot (Nat.mem_divisors.mpr ⟨hdvd, hq0⟩)
    rw [(hrec d hd).1 hndvd, zero_mul]
  rw [hpoly_div] at hz
  have hq_le12 : q ≤ 12 := Nat.le_of_dvd (by norm_num) hq_dvd_12
  have hmul_cpow : ∀ m n : ℕ, 0 < m → 0 < n →
      ((m * n : ℕ) : ℂ) ^ (-z) = (m : ℂ) ^ (-z) * (n : ℂ) ^ (-z) := by
    intro m n _ _
    rw [Nat.cast_mul, ← Complex.ofReal_natCast m, ← Complex.ofReal_natCast n,
      ← Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
  interval_cases q
  · -- `q = 1`: `1 = 0` impossible.
    have hdiv : (1 : ℕ).divisors = {1} := by decide
    rw [hdiv] at hz; simp [hc1] at hz
  · -- `q = 2`
    have hdiv : (2 : ℕ).divisors = {1, 2} := by decide
    rw [hdiv] at hz
    simp only [Finset.sum_insert (by decide : (1 : ℕ) ∉ ({2} : Finset ℕ)),
      Finset.sum_singleton, hc1, Nat.cast_one, Complex.one_cpow, mul_one] at hz
    have hf2 : (2 : ℕ).factorization 2 = 1 := Nat.Prime.factorization_self Nat.prime_two
    have hn2 := hpe_norm_sq Nat.prime_two (by rw [hf2]; exact one_ne_zero)
    rw [hf2, pow_one] at hn2
    exact linear_prime_factor_zero_re_eq_half Nat.prime_two hn2 (by simpa using hz)
  · -- `q = 3`
    have hdiv : (3 : ℕ).divisors = {1, 3} := by decide
    rw [hdiv] at hz
    simp only [Finset.sum_insert (by decide : (1 : ℕ) ∉ ({3} : Finset ℕ)),
      Finset.sum_singleton, hc1, Nat.cast_one, Complex.one_cpow, mul_one] at hz
    have hf3 : (3 : ℕ).factorization 3 = 1 := Nat.Prime.factorization_self Nat.prime_three
    have hn3 := hpe_norm_sq Nat.prime_three (by rw [hf3]; exact one_ne_zero)
    rw [hf3, pow_one] at hn3
    exact linear_prime_factor_zero_re_eq_half Nat.prime_three hn3 (by simpa using hz)
  · -- `q = 4`
    have hdiv : (4 : ℕ).divisors = {1, 2, 4} := by decide
    rw [hdiv] at hz
    simp only [Finset.sum_insert (by decide : (1 : ℕ) ∉ ({2, 4} : Finset ℕ)),
      Finset.sum_insert (by decide : (2 : ℕ) ∉ ({4} : Finset ℕ)),
      Finset.sum_singleton, hc1, Nat.cast_one, Complex.one_cpow, mul_one] at hz
    have hn4 := hpe_norm_sq Nat.prime_two (by rw [hf4_2]; exact two_ne_zero)
    rw [hf4_2] at hn4
    norm_num at hn4
    have hc2_eq : c 2 = a 2 - 1 := by
      have h := ha_prime_pow Nat.prime_two 1 le_rfl
      have ha1 : a 1 = 1 := by dsimp only [a]; simp [hc1]
      simpa [ha1] using h
    have hc4_eq : c 4 = a 4 - a 2 := by
      simpa using ha_prime_pow Nat.prime_two 2 (by omega)
    rw [hc4_eq] at hn4
    rw [hc2_eq, hc4_eq] at hz
    exact quadratic_two_factor_zero_re_eq_half (hunit 2 (by omega)) (hunit 4 (by omega))
      hn4 (by push_cast at hz; linear_combination hz)
  · omega
  · -- `q = 6`
    have hdiv : (6 : ℕ).divisors = {1, 2, 3, 6} := by decide
    rw [hdiv] at hz
    simp only [Finset.sum_insert (by decide : (1 : ℕ) ∉ ({2, 3, 6} : Finset ℕ)),
      Finset.sum_insert (by decide : (2 : ℕ) ∉ ({3, 6} : Finset ℕ)),
      Finset.sum_insert (by decide : (3 : ℕ) ∉ ({6} : Finset ℕ)),
      Finset.sum_singleton, hc1, Nat.cast_one, Complex.one_cpow, mul_one] at hz
    have hc6 : c 6 = c 2 * c 3 := hc_mul.2 (by decide : Nat.Coprime 2 3)
    have hp6 := hmul_cpow 2 3 (by omega) (by omega)
    norm_num at hp6
    push_cast at hz
    have hfac6 : (1 + c 2 * (2 : ℂ) ^ (-z)) * (1 + c 3 * (3 : ℂ) ^ (-z)) = 0 := by
      rw [hc6, hp6] at hz; linear_combination hz
    rcases mul_eq_zero.mp hfac6 with hz2 | hz3
    · have hn2 := hpe_norm_sq Nat.prime_two (by rw [hf6_2]; exact one_ne_zero)
      rw [hf6_2, pow_one] at hn2
      exact linear_prime_factor_zero_re_eq_half Nat.prime_two hn2 hz2
    · have hn3 := hpe_norm_sq Nat.prime_three (by rw [hf6_3]; exact one_ne_zero)
      rw [hf6_3, pow_one] at hn3
      exact linear_prime_factor_zero_re_eq_half Nat.prime_three hn3 hz3
  · omega
  · omega
  · omega
  · omega
  · omega
  · -- `q = 12`
    have hdiv : (12 : ℕ).divisors = {1, 2, 3, 4, 6, 12} := by decide
    rw [hdiv] at hz
    simp only [Finset.sum_insert (by decide : (1 : ℕ) ∉ ({2, 3, 4, 6, 12} : Finset ℕ)),
      Finset.sum_insert (by decide : (2 : ℕ) ∉ ({3, 4, 6, 12} : Finset ℕ)),
      Finset.sum_insert (by decide : (3 : ℕ) ∉ ({4, 6, 12} : Finset ℕ)),
      Finset.sum_insert (by decide : (4 : ℕ) ∉ ({6, 12} : Finset ℕ)),
      Finset.sum_insert (by decide : (6 : ℕ) ∉ ({12} : Finset ℕ)),
      Finset.sum_singleton, hc1, Nat.cast_one, Complex.one_cpow, mul_one] at hz
    have hc6 : c 6 = c 2 * c 3 := hc_mul.2 (by decide : Nat.Coprime 2 3)
    have hc12 : c 12 = c 4 * c 3 := hc_mul.2 (by decide : Nat.Coprime 4 3)
    have hp6 := hmul_cpow 2 3 (by omega) (by omega)
    have hp12 := hmul_cpow 4 3 (by omega) (by omega)
    norm_num at hp6 hp12
    push_cast at hz
    have hfac12 : (1 + c 2 * (2 : ℂ) ^ (-z) + c 4 * (4 : ℂ) ^ (-z)) *
        (1 + c 3 * (3 : ℂ) ^ (-z)) = 0 := by
      rw [hc6, hc12, hp6, hp12] at hz; linear_combination hz
    rcases mul_eq_zero.mp hfac12 with hz4 | hz3
    · have hn4 := hpe_norm_sq Nat.prime_two (by rw [hf12_2]; exact two_ne_zero)
      rw [hf12_2] at hn4
      norm_num at hn4
      have hc2_eq : c 2 = a 2 - 1 := by
        have h := ha_prime_pow Nat.prime_two 1 le_rfl
        have ha1 : a 1 = 1 := by dsimp only [a]; simp [hc1]
        simpa [ha1] using h
      have hc4_eq : c 4 = a 4 - a 2 := by
        simpa using ha_prime_pow Nat.prime_two 2 (by omega)
      rw [hc4_eq] at hn4
      rw [hc2_eq, hc4_eq] at hz4
      exact quadratic_two_factor_zero_re_eq_half (hunit 2 (by omega)) (hunit 4 (by omega))
        hn4 (by linear_combination hz4)
    · have hn3 := hpe_norm_sq Nat.prime_three (by rw [hf12_3]; exact one_ne_zero)
      rw [hf12_3, pow_one] at hn3
      exact linear_prime_factor_zero_re_eq_half Nat.prime_three hn3 hz3

/-- **Sharpness of conductor `Q = 4`: explicit even unimodular multiplicative twin
`F₄(s) = (1 - 2 · 2^{-s} + 2 · 4^{-s}) ζ(s)`:** there exists a non-constant real multiplicative
sequence `a₄ : ℕ → ℂ` with `a₄(2) = -1` and `‖a₄(n)‖ = 1` for all `n ≥ 1` whose continuation
`F₄` is holomorphic off `s = 1` with positive residue `1 / 2`, satisfies exact even conductor-`4`
completion symmetry across **all** `s ∈ ℂ`, and has all twin-factor zeros on `Re s = 1 / 2`. -/
theorem exists_even_conductor_four_unimodular_twin :
    ∃ (c₄ a₄ : ArithmeticFunction ℂ),
      (∀ d : ℕ, 4 < d → c₄ d = 0) ∧
      c₄.IsMultiplicative ∧
      a₄.IsMultiplicative ∧
      a₄ 2 = -1 ∧ (∀ n : ℕ, 1 ≤ n → ‖a₄ n‖ = 1) ∧
      (∀ n : ℕ, 1 ≤ n → a₄ n = ∑ d ∈ n.divisors, c₄ d) ∧
      (∀ s : ℂ, 1 < s.re → LSeries a₄ s = riemannZeta s * twinDirichletPoly 4 c₄ s) ∧
      Tendsto (fun s : ℂ => (s - 1) * (riemannZeta s * twinDirichletPoly 4 c₄ s))
        (𝓝[≠] 1) (𝓝 (1 / 2 : ℂ)) ∧
      (∀ s : ℂ, (4 : ℂ) ^ (s / 2) * completedRiemannZeta s * twinDirichletPoly 4 c₄ s =
        (4 : ℂ) ^ ((1 - s) / 2) * completedRiemannZeta (1 - s) *
          twinDirichletPolyConj 4 c₄ (1 - s)) ∧
      (∀ z : ℂ, twinDirichletPoly 4 c₄ z = 0 → z.re = 1 / 2) := by
  set c₄_fn : ℕ → ℂ := fun d => if d = 1 then 1 else if d = 2 then -2 else if d = 4 then 2 else 0
  set a₄_fn : ℕ → ℂ := fun n => if n = 0 then 0 else if n.factorization 2 = 1 then -1 else 1
  set c₄ : ArithmeticFunction ℂ := ⟨c₄_fn, by dsimp only [c₄_fn]; norm_num⟩
  set a₄ : ArithmeticFunction ℂ := ⟨a₄_fn, by dsimp only [a₄_fn]; simp⟩
  have hc₄_apply : ∀ d : ℕ, c₄ d = c₄_fn d := fun _ => rfl
  have ha₄_apply : ∀ n : ℕ, a₄ n = a₄_fn n := fun _ => rfl
  have hc₄_supp : ∀ d : ℕ, 4 < d → c₄ d = 0 := fun d hd => by
    rw [hc₄_apply]; dsimp only [c₄_fn]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have hc₄_mul : c₄.IsMultiplicative := by
    refine ⟨by rw [hc₄_apply]; dsimp only [c₄_fn]; norm_num, fun {m n} hmn => ?_⟩
    rw [hc₄_apply, hc₄_apply, hc₄_apply]
    dsimp only [c₄_fn]
    by_cases hm1 : m = 1
    · subst hm1; simp
    by_cases hn1 : n = 1
    · subst hn1; simp
    have hmn_ne1 : m * n ≠ 1 := fun h => hm1 (Nat.eq_one_of_mul_eq_one_right h)
    have hmn_ne2 : m * n ≠ 2 := by
      intro h
      have hdvd : m ∣ 2 := ⟨n, h.symm⟩
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with rfl | rfl
      · exact hm1 rfl
      · exact hn1 (by omega)
    have hmn_ne4 : m * n ≠ 4 := by
      intro h
      have hdvd : m ∣ 4 := ⟨n, h.symm⟩
      have hm_le4 : m ≤ 4 := Nat.le_of_dvd (by omega) hdvd
      have hm_pos : 0 < m := by by_contra h0; push Not at h0; interval_cases m; simp at h
      interval_cases m
      · exact hm1 rfl
      · have hn2 : n = 2 := by omega
        subst hn2; exact absurd hmn (by decide)
      · omega
      · exact hn1 (by omega)
    rw [if_neg hmn_ne1, if_neg hmn_ne2, if_neg hmn_ne4, if_neg hm1, if_neg hn1]
    by_cases hm2 : m = 2
    · subst hm2
      have hn_ne2 : n ≠ 2 := fun h => by subst h; exact absurd hmn (by decide)
      have hn_ne4 : n ≠ 4 := fun h => by subst h; exact absurd hmn (by decide)
      rw [if_neg hn_ne2, if_neg hn_ne4, mul_zero]
    by_cases hm4 : m = 4
    · subst hm4
      have hn_ne2 : n ≠ 2 := fun h => by subst h; exact absurd hmn (by decide)
      have hn_ne4 : n ≠ 4 := fun h => by subst h; exact absurd hmn (by decide)
      rw [if_neg hn_ne2, if_neg hn_ne4, mul_zero]
    rw [if_neg hm2, if_neg hm4, zero_mul]
  have ha₄_mul : a₄.IsMultiplicative := by
    refine ⟨by rw [ha₄_apply]; dsimp only [a₄_fn]; simp, fun {m n} hmn => ?_⟩
    rw [ha₄_apply, ha₄_apply, ha₄_apply]
    rcases eq_or_ne m 0 with rfl | hm0
    · dsimp only [a₄_fn]; simp
    rcases eq_or_ne n 0 with rfl | hn0
    · dsimp only [a₄_fn]; simp
    have hmn0 : m * n ≠ 0 := mul_ne_zero hm0 hn0
    dsimp only [a₄_fn]
    rw [if_neg hmn0, if_neg hm0, if_neg hn0, Nat.factorization_mul hm0 hn0, Finsupp.add_apply]
    have hnot_both : ¬(2 ∣ m ∧ 2 ∣ n) := fun ⟨h1, h2⟩ =>
      Nat.Prime.not_coprime_iff_dvd.mpr ⟨2, Nat.prime_two, h1, h2⟩ hmn
    rcases not_and_or.mp hnot_both with hnm2 | hnn2
    · have hfm : m.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd hnm2
      rw [hfm, zero_add, if_neg zero_ne_one, one_mul]
    · have hfn : n.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd hnn2
      rw [hfn, add_zero, if_neg zero_ne_one, mul_one]
  have ha₄_2 : a₄ 2 = -1 := by
    rw [ha₄_apply]; dsimp only [a₄_fn]
    rw [if_neg two_ne_zero, Nat.Prime.factorization_self Nat.prime_two, if_pos rfl]
  have ha₄_norm : ∀ n : ℕ, 1 ≤ n → ‖a₄ n‖ = 1 := fun n hn => by
    rw [ha₄_apply]; dsimp only [a₄_fn]; rw [if_neg (by omega)]; split_ifs <;> simp
  have ha₄_conv : ∀ n : ℕ, 1 ≤ n → a₄ n = ∑ d ∈ n.divisors, c₄ d := by
    intro n hn
    have hn0 : n ≠ 0 := by omega
    have hsub : (n.divisors.filter (fun d => d = 1 ∨ d = 2 ∨ d = 4)) ⊆ {1, 2, 4} := by
      intro d hd; rcases (Finset.mem_filter.mp hd).2 with rfl | rfl | rfl <;> decide
    have hsum_eq : (∑ d ∈ n.divisors, c₄ d) =
        c₄ 1 + (if 2 ∣ n then c₄ 2 else 0) + (if 4 ∣ n then c₄ 4 else 0) := by
      have h1 : (∑ d ∈ n.divisors, c₄ d) =
          ∑ d ∈ ({1, 2, 4} : Finset ℕ), if d ∈ n.divisors then c₄ d else 0 := by
        rw [← Finset.sum_filter]
        refine (Finset.sum_subset (fun d hd => (Finset.mem_filter.mp hd).2) fun d hd hnot => ?_).symm
        have hnot124 : d ∉ ({1, 2, 4} : Finset ℕ) := fun hm => hnot (Finset.mem_filter.mpr ⟨hm, hd⟩)
        rw [hc₄_apply]; dsimp only [c₄_fn]
        rw [if_neg (fun h => hnot124 (by simp [h])),
          if_neg (fun h => hnot124 (by simp [h])),
          if_neg (fun h => hnot124 (by simp [h]))]
      rw [h1]
      simp only [Finset.sum_insert (by decide : (1 : ℕ) ∉ ({2, 4} : Finset ℕ)),
        Finset.sum_insert (by decide : (2 : ℕ) ∉ ({4} : Finset ℕ)),
        Finset.sum_singleton, Nat.mem_divisors, hn0, ne_eq, not_false_eq_true, and_true,
        one_dvd, ↓reduceIte, add_assoc]
    rw [hsum_eq, ha₄_apply, hc₄_apply, hc₄_apply, hc₄_apply]
    dsimp only [a₄_fn, c₄_fn]
    rw [if_neg hn0]
    norm_num
    by_cases hd2 : 2 ∣ n
    · by_cases hd4 : 4 ∣ n
      · have hf_ge2 : 2 ≤ n.factorization 2 := by
          have h := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hn0).mp
            (show 2 ^ 2 ∣ n by simpa using hd4)
          exact h
        rw [if_neg (by omega), if_pos hd2, if_pos hd4]; ring
      · have hf_ge1 : 1 ≤ n.factorization 2 :=
          (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hn0).mp hd2
        have hf_lt2 : ¬(2 ≤ n.factorization 2) := fun hge =>
          hd4 (by simpa using (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hn0).mpr hge)
        rw [if_pos (by omega), if_pos hd2, if_neg hd4]; ring
    · have hf0 : n.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd hd2
      have hd4 : ¬(4 ∣ n) := fun h4 => hd2 (dvd_trans (by decide : 2 ∣ 4) h4)
      rw [hf0, if_neg zero_ne_one, if_neg hd2, if_neg hd4]; ring
  -- LSeries identity on `Re s > 1`.
  have hL_eq : ∀ s : ℂ, 1 < s.re → LSeries a₄ s = riemannZeta s * twinDirichletPoly 4 c₄ s := by
    intro s hs
    have ha_eq_conv : LSeries a₄ s = LSeries (LSeries.convolution 1 c₄) s := by
      refine LSeries_congr (fun {n} hn0 => ?_) s
      rw [ha₄_conv n (Nat.one_le_iff_ne_zero.mpr hn0), LSeries.convolution_def]
      dsimp only
      rw [Nat.sum_divisorsAntidiagonal' (f := fun x y => (1 : ℕ → ℂ) x * c₄ y)]
      simp
    have hsum1 : LSeriesSummable 1 s := LSeriesSummable_one_iff.mpr hs
    have hsum_c₄ : LSeriesSummable c₄ s := by
      refine summable_of_ne_finset_zero (s := Finset.range 5) fun n hn => ?_
      rw [Finset.mem_range, not_lt] at hn
      rw [LSeries.term_of_ne_zero (by omega), hc₄_supp n (by omega), zero_div]
    have hLc₄ : LSeries c₄ s = twinDirichletPoly 4 c₄ s := by
      unfold LSeries twinDirichletPoly
      rw [tsum_eq_sum (s := Finset.range 5) fun n hn => by
        rw [Finset.mem_range, not_lt] at hn
        rw [LSeries.term_of_ne_zero (by omega), hc₄_supp n (by omega), zero_div]]
      have hrange : Finset.range 5 = insert 0 (Finset.Icc 1 4) := by decide
      rw [hrange, Finset.sum_insert (by decide), LSeries.term_zero, zero_add]
      refine Finset.sum_congr rfl fun d hd => ?_
      rw [LSeries.term_of_ne_zero (by have := (Finset.mem_Icc.mp hd).1; omega),
        div_eq_mul_inv, ← Complex.cpow_neg]
    rw [ha_eq_conv, LSeries_convolution' hsum1 hsum_c₄, LSeries_one_eq_riemannZeta hs, hLc₄]
  -- Residue `1 / 2` at `s = 1`.
  have hres_half : Tendsto (fun s : ℂ => (s - 1) * (riemannZeta s * twinDirichletPoly 4 c₄ s))
      (𝓝[≠] 1) (𝓝 (1 / 2 : ℂ)) := by
    have hcont_D : ContinuousAt (twinDirichletPoly 4 c₄) 1 := by
      have hfn : twinDirichletPoly 4 c₄ =
          ∑ d ∈ Finset.Icc 1 4, fun s : ℂ => c₄ d * (d : ℂ) ^ (-s) := by
        funext s; unfold twinDirichletPoly; simp only [Finset.sum_apply]
      rw [hfn]
      refine Finset.sum_induction _ (fun g : ℂ → ℂ => ContinuousAt g 1)
        (fun _ _ h₁ h₂ => h₁.add h₂) continuousAt_const fun d hd => continuousAt_const.mul ?_
      have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (by have := (Finset.mem_Icc.mp hd).1; omega : d ≠ 0)
      haveI : NeZero (d : ℂ) := ⟨hd0⟩
      exact ((continuous_const_cpow (d : ℂ)).comp continuous_id.neg).continuousAt
    have hval1 : twinDirichletPoly 4 c₄ 1 = (1 / 2 : ℂ) := by
      unfold twinDirichletPoly
      have hIcc : Finset.Icc 1 4 = {1, 2, 4} ∪ {3} := by decide
      rw [hIcc, Finset.sum_union (by decide)]
      simp only [Finset.sum_insert (by decide : (1 : ℕ) ∉ ({2, 4} : Finset ℕ)),
        Finset.sum_insert (by decide : (2 : ℕ) ∉ ({4} : Finset ℕ)),
        Finset.sum_singleton, hc₄_apply, c₄_fn]
      norm_num [Complex.cpow_neg_one]
    have hmul_lim := riemannZeta_residue_one.mul hcont_D.continuousWithinAt
    rw [hval1, one_mul] at hmul_lim
    exact hmul_lim.congr fun s => by ring
  -- Exact even completion symmetry across all `s ∈ ℂ`.
  have hrefl_all : ∀ s : ℂ,
      (4 : ℂ) ^ (s / 2) * completedRiemannZeta s * twinDirichletPoly 4 c₄ s =
        (4 : ℂ) ^ ((1 - s) / 2) * completedRiemannZeta (1 - s) *
          twinDirichletPolyConj 4 c₄ (1 - s) := by
    intro s
    have hD_conj : twinDirichletPolyConj 4 c₄ (1 - s) = twinDirichletPoly 4 c₄ (1 - s) := by
      unfold twinDirichletPolyConj twinDirichletPoly
      refine Finset.sum_congr rfl fun d _ => ?_
      congr 1; rw [hc₄_apply]; dsimp only [c₄_fn]; split_ifs <;> norm_num
    rw [hD_conj, completedRiemannZeta_one_sub s]
    have h2_0 : (2 : ℂ) ≠ 0 := two_ne_zero
    have h4_s : ∀ w : ℂ, (4 : ℂ) ^ (w / 2) = (2 : ℂ) ^ w := fun w => by
      have h := Complex.mul_cpow_ofReal_nonneg two_pos.le two_pos.le (w / 2)
      calc (4 : ℂ) ^ (w / 2)
          = (((2 : ℝ) * (2 : ℝ) : ℝ) : ℂ) ^ (w / 2) := by norm_num
        _ = (2 : ℂ) ^ (w / 2) * (2 : ℂ) ^ (w / 2) := by simpa using h
        _ = (2 : ℂ) ^ w := by rw [← Complex.cpow_add _ _ h2_0, add_halves]
    have hpoly_s : ∀ w : ℂ,
        (2 : ℂ) ^ w * twinDirichletPoly 4 c₄ w = (2 : ℂ) ^ w - 2 + (2 : ℂ) ^ (1 - w) := by
      intro w
      unfold twinDirichletPoly
      have hIcc : Finset.Icc 1 4 = {1, 2, 4} ∪ {3} := by decide
      rw [hIcc, Finset.sum_union (by decide)]
      simp only [Finset.sum_insert (by decide : (1 : ℕ) ∉ ({2, 4} : Finset ℕ)),
        Finset.sum_insert (by decide : (2 : ℕ) ∉ ({4} : Finset ℕ)),
        Finset.sum_singleton, hc₄_apply, c₄_fn]
      norm_num
      have h2w : (2 : ℂ) ^ w * (2 : ℂ) ^ (-w) = 1 := by
        rw [← Complex.cpow_add _ _ h2_0, add_neg_cancel, Complex.cpow_zero]
      have h4w : (2 : ℂ) ^ w * (4 : ℂ) ^ (-w) = (2 : ℂ) ^ (-w) := by
        have h4eq : (4 : ℂ) ^ (-w) = (2 : ℂ) ^ (-w) * (2 : ℂ) ^ (-w) := by
          have h := Complex.mul_cpow_ofReal_nonneg two_pos.le two_pos.le (-w)
          calc (4 : ℂ) ^ (-w)
              = (((2 : ℝ) * (2 : ℝ) : ℝ) : ℂ) ^ (-w) := by norm_num
            _ = (2 : ℂ) ^ (-w) * (2 : ℂ) ^ (-w) := by simpa using h
        rw [h4eq, ← mul_assoc, h2w, one_mul]
      have h2_1w : (2 : ℂ) * (2 : ℂ) ^ (-w) = (2 : ℂ) ^ (1 - w) := by
        rw [show (1 : ℂ) - w = 1 + (-w) by ring, Complex.cpow_add _ _ h2_0, Complex.cpow_one]
      linear_combination -2 * h2w + 2 * h4w + h2_1w
    have heq_fac : (4 : ℂ) ^ (s / 2) * twinDirichletPoly 4 c₄ s =
        (4 : ℂ) ^ ((1 - s) / 2) * twinDirichletPoly 4 c₄ (1 - s) := by
      rw [h4_s s, h4_s (1 - s), hpoly_s s, hpoly_s (1 - s), show 1 - (1 - s) = s by ring]
      ring
    linear_combination completedRiemannZeta s * heq_fac
  -- Critical-line purity via `unit_bounded_multiplicative_twin_classification`.
  have hpure := (unit_bounded_multiplicative_twin_classification (M := 4) (by omega)
    hc₄_supp hc₄_mul (Q := 4) (by norm_num) (ω := 1) norm_one
    (fun n hn => by rw [← ha₄_conv n hn, ha₄_norm n hn])
    (fun t => by simpa using hrefl_all ((-1 : ℂ) + (t : ℂ) * I))).2
  exact ⟨c₄, a₄, hc₄_supp, hc₄_mul, ha₄_mul, ha₄_2, ha₄_norm, ha₄_conv,
    hL_eq, hres_half, hrefl_all, hpure⟩

/-! ### Part 4: Sharp Necessity of Cross-Height Reflection Over Single-Ordinate Reflection on `Ω_open` -/

private theorem exists_unit_bounded_poly_vanishing_at {w : ℂ} (hw0 : w ≠ 0) {N : ℕ} (hN : 1 ≤ N)
    (hsum_ge1 : 1 ≤ ∑ k ∈ Finset.Icc 1 N, ‖w‖ ^ k) :
    ∃ b : ℕ → ℂ, b 0 = 1 ∧ (∀ k : ℕ, ‖b k‖ ≤ 1) ∧ (∀ k : ℕ, N < k → b k = 0) ∧
      (∑ k ∈ Finset.range (N + 1), b k * w ^ k = 0) ∧
      (∀ u : ℝ, 0 < u → (∑ k ∈ Finset.Icc 1 N, u ^ k) < 1 →
        ∑ k ∈ Finset.range (N + 1), b k * (u : ℂ) ^ k ≠ 0) := by
  set S : ℝ := ∑ k ∈ Finset.Icc 1 N, ‖w‖ ^ k
  have hS_pos : 0 < S := zero_lt_one.trans_le hsum_ge1
  have hwnorm_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  set phase : ℂ := starRingEnd ℂ w / (‖w‖ : ℂ)
  have hphase_norm : ‖phase‖ = 1 := by
    dsimp only [phase]
    rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hwnorm_pos, div_self hwnorm_pos.ne']
  have hphase_mul : phase * w = (‖w‖ : ℂ) := by
    dsimp only [phase]
    have hwn_c : (‖w‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hwnorm_pos.ne'
    have hconj : starRingEnd ℂ w * w = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [div_mul_eq_mul_div, hconj]
    push_cast; field_simp [hwn_c]
  set b : ℕ → ℂ := fun k =>
    if k = 0 then 1 else if k ≤ N then -(phase ^ k) / (S : ℂ) else 0
  have hb0 : b 0 = 1 := by dsimp only [b]; simp
  have hbnorm : ∀ k : ℕ, ‖b k‖ ≤ 1 := fun k => by
    dsimp only [b]
    split_ifs with hk0 hkN
    · simp
    · rw [norm_div, norm_neg, norm_pow, hphase_norm, one_pow,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hS_pos]
      exact div_le_one_of_le₀ hsum_ge1 hS_pos.le
    · simp
  have hbsupp : ∀ k : ℕ, N < k → b k = 0 := fun k hk => by
    dsimp only [b]; rw [if_neg (by omega), if_neg (by omega)]
  have hrange_split : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
    ext k
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have hvanish : ∑ k ∈ Finset.range (N + 1), b k * w ^ k = 0 := by
    rw [hrange_split, Finset.sum_insert (by simp), hb0, pow_zero, mul_one]
    have hIcc_sum : (∑ k ∈ Finset.Icc 1 N, b k * w ^ k) =
        ∑ k ∈ Finset.Icc 1 N, -(((‖w‖ ^ k : ℝ) : ℂ) / (S : ℂ)) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      have hkN : k ≤ N := (Finset.mem_Icc.mp hk).2
      dsimp only [b]
      rw [if_neg (by omega), if_pos hkN]
      have hpw : phase ^ k * w ^ k = ((‖w‖ ^ k : ℝ) : ℂ) := by
        rw [← mul_pow, hphase_mul]; push_cast; rfl
      calc (-(phase ^ k) / (S : ℂ)) * w ^ k
          = -(phase ^ k * w ^ k) / (S : ℂ) := by ring
        _ = -(((‖w‖ ^ k : ℝ) : ℂ) / (S : ℂ)) := by rw [hpw, neg_div]
    rw [hIcc_sum, Finset.sum_neg_distrib, ← Finset.sum_div]
    have hcast_S : (∑ k ∈ Finset.Icc 1 N, ((‖w‖ ^ k : ℝ) : ℂ)) = (S : ℂ) := by
      dsimp only [S]; push_cast; rfl
    rw [hcast_S, div_self (Complex.ofReal_ne_zero.mpr hS_pos.ne'), add_neg_cancel]
  refine ⟨b, hb0, hbnorm, hbsupp, hvanish, fun u hu hsum_u hzero_u => ?_⟩
  rw [hrange_split, Finset.sum_insert (by simp), hb0, pow_zero, mul_one] at hzero_u
  have heq_neg1 : ∑ k ∈ Finset.Icc 1 N, b k * (u : ℂ) ^ k = -1 :=
    eq_neg_of_add_eq_zero_right hzero_u
  have hnorm_1 : (1 : ℝ) ≤ ∑ k ∈ Finset.Icc 1 N, u ^ k := by
    calc (1 : ℝ) = ‖(-1 : ℂ)‖ := by simp
      _ = ‖∑ k ∈ Finset.Icc 1 N, b k * (u : ℂ) ^ k‖ := by rw [heq_neg1]
      _ ≤ ∑ k ∈ Finset.Icc 1 N, ‖b k * (u : ℂ) ^ k‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.Icc 1 N, u ^ k := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
          exact mul_le_of_le_one_left (pow_nonneg hu.le k) (hbnorm k)
  linarith

/-- **Sharp necessity of cross-height reflection over single-ordinate reflection on `Ω_open`:**
for **every** point `s₀ : ℂ` with `3001 / 24000 ≤ Re s₀ < 1 / 2` (in particular every point of
`Ω_open`), there exist a multiplicative sequence `a : ℕ → ℂ` and an analytic continuation `F`
satisfying:
1. `a(1) = 1` and `‖a(n)‖ ≤ 1` for all `n ≥ 1` (**Axiom I**);
2. `F` agrees with `LSeries a` on `Re s > 1`, is globally holomorphic on `ℂ \ {1}` (hence globally
   pole-free across `0 < Re s < 1 / 2`, **Axiom II**), and has a genuine simple pole (`R ≠ 0`) at `1`;
3. `F(s₀) = 0` and `F(1 - s₀) = 0`, so the completed function `ξ_F(s) = Gammaℝ s · F(s)` satisfies
   the **single-ordinate** reflection identity `ξ_F(s₀) = ξ_F(1 - s₀)` (`= 0`) at `s₀`, while
   vanishing inside `Ω_open`. -/
theorem exists_unit_bounded_poleFree_singleOrdinate_countermodel_on_remaining_strip
    {s₀ : ℂ} (hlo : 3001 / 24000 ≤ s₀.re) (hhi : s₀.re < 1 / 2) :
    ∃ (a : ArithmeticFunction ℂ) (F : ℂ → ℂ) (R : ℂ),
      a.IsMultiplicative ∧
      (∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤ 1) ∧
      (∀ s : ℂ, 1 < s.re → LSeries a s = F s) ∧
      (∀ s : ℂ, s ≠ 1 → DifferentiableAt ℂ F s) ∧
      R ≠ 0 ∧ Tendsto (fun s : ℂ => (s - 1) * F s) (𝓝[≠] 1) (𝓝 R) ∧
      F s₀ = 0 ∧ F (1 - s₀) = 0 ∧
      Complex.Gammaℝ s₀ * F s₀ = Complex.Gammaℝ (1 - s₀) * F (1 - s₀) := by
  -- Step 1: Verify `∑_{k=1}^3 |3^{-s₀}|^k ≥ 1` and `∑_{k=1}^{12} |2^{-(1 - s₀)}|^k ≥ 1`.
  set w₁ : ℂ := (3 : ℂ) ^ (-s₀)
  set w₂ : ℂ := (2 : ℂ) ^ (-(1 - s₀))
  have hw₁_0 : w₁ ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  have hw₂_0 : w₂ ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  have hw₁_gt : (11 / 20 : ℝ) < ‖w₁‖ := by
    have hn : ‖w₁‖ = (3 : ℝ) ^ (-s₀.re) := by
      dsimp only [w₁]
      rw [show (3 : ℂ) = ((3 : ℝ) : ℂ) by norm_num,
        Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num), Complex.neg_re]
    have hsq : (11 / 20 : ℝ) ^ 2 < ‖w₁‖ ^ 2 := by
      rw [hn, ← Real.rpow_natCast ((3 : ℝ) ^ (-s₀.re)) 2, ← Real.rpow_mul (by norm_num)]
      have hgt_3 : (3 : ℝ) ^ (-1 : ℝ) < (3 : ℝ) ^ (-s₀.re * 2) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
      have h13 : (11 / 20 : ℝ) ^ 2 < (3 : ℝ) ^ (-1 : ℝ) := by norm_num
      exact h13.trans hgt_3
    by_contra hle; push Not at hle
    nlinarith [norm_nonneg w₁]
  have hsum_w₁ : 1 ≤ ∑ k ∈ Finset.Icc 1 3, ‖w₁‖ ^ k := by
    have hmono : ∑ k ∈ Finset.Icc 1 3, (11 / 20 : ℝ) ^ k ≤ ∑ k ∈ Finset.Icc 1 3, ‖w₁‖ ^ k :=
      Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (by positivity) hw₁_gt.le k
    have hval : (1 : ℝ) ≤ ∑ k ∈ Finset.Icc 1 3, (11 / 20 : ℝ) ^ k := by
      have hIcc : Finset.Icc 1 3 = {1, 2, 3} := by decide
      rw [hIcc]; norm_num
    exact hval.trans hmono
  have hw₂_gt : (13 / 24 : ℝ) < ‖w₂‖ := by
    have hn : ‖w₂‖ = (2 : ℝ) ^ (-(1 - s₀.re)) := by
      dsimp only [w₂]
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
        Complex.norm_cpow_eq_rpow_re_of_pos two_pos, Complex.neg_re, Complex.sub_re, Complex.one_re]
    have hpow8 : (13 / 24 : ℝ) ^ 8 < ‖w₂‖ ^ 8 := by
      rw [hn, ← Real.rpow_natCast ((2 : ℝ) ^ (-(1 - s₀.re))) 8, ← Real.rpow_mul two_pos.le]
      have hgt_2 : (2 : ℝ) ^ (-7 : ℝ) < (2 : ℝ) ^ (-(1 - s₀.re) * 8) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
      have h128 : (13 / 24 : ℝ) ^ 8 < (2 : ℝ) ^ (-7 : ℝ) := by norm_num
      exact h128.trans hgt_2
    by_contra hle; push Not at hle
    have hle8 : ‖w₂‖ ^ 8 ≤ (13 / 24 : ℝ) ^ 8 := pow_le_pow_left₀ (norm_nonneg _) hle 8
    linarith
  have hsum_w₂ : 1 ≤ ∑ k ∈ Finset.Icc 1 12, ‖w₂‖ ^ k := by
    have hmono : ∑ k ∈ Finset.Icc 1 12, (13 / 24 : ℝ) ^ k ≤ ∑ k ∈ Finset.Icc 1 12, ‖w₂‖ ^ k :=
      Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (by positivity) hw₂_gt.le k
    have hval : (1 : ℝ) ≤ ∑ k ∈ Finset.Icc 1 12, (13 / 24 : ℝ) ^ k := by
      have hIcc : Finset.Icc 1 12 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12} := by decide
      rw [hIcc]; norm_num
    exact hval.trans hmono
  -- Step 2: Construct unit-bounded local polynomials `b₁` (at `p = 3`) and `b₂` (at `p = 2`).
  obtain ⟨b₁, hb₁_0, hb₁_norm, hb₁_supp, hb₁_van, hb₁_nz⟩ :=
    exists_unit_bounded_poly_vanishing_at hw₁_0 (N := 3) (by omega) hsum_w₁
  obtain ⟨b₂, hb₂_0, hb₂_norm, hb₂_supp, hb₂_van, hb₂_nz⟩ :=
    exists_unit_bounded_poly_vanishing_at hw₂_0 (N := 12) (by omega) hsum_w₂
  -- Step 3: Define `a(n) = b₁(v₃(n)) * b₂(v₂(n))` and finitely supported Euler increments `c₁, c₂`.
  set a_fn : ℕ → ℂ := fun n => if n = 0 then 0 else b₁ (n.factorization 3) * b₂ (n.factorization 2)
  set a : ArithmeticFunction ℂ := ⟨a_fn, by dsimp only [a_fn]; simp⟩
  have ha_apply : ∀ n : ℕ, a n = a_fn n := fun _ => rfl
  set c₁ : ℕ → ℂ := fun d =>
    if d = 1 then 1 else
      ∑ k ∈ Finset.Icc 1 4, if d = 3 ^ k then b₁ k - b₁ (k - 1) else 0
  set c₂ : ℕ → ℂ := fun d =>
    if d = 1 then 1 else
      ∑ k ∈ Finset.Icc 1 13, if d = 2 ^ k then b₂ k - b₂ (k - 1) else 0
  have ha_mul : a.IsMultiplicative := by
    refine ⟨by rw [ha_apply]; dsimp only [a_fn]; simp [hb₁_0, hb₂_0], fun {m n} hmn => ?_⟩
    rw [ha_apply, ha_apply, ha_apply]
    rcases eq_or_ne m 0 with rfl | hm0
    · dsimp only [a_fn]; simp
    rcases eq_or_ne n 0 with rfl | hn0
    · dsimp only [a_fn]; simp
    dsimp only [a_fn]
    rw [if_neg (mul_ne_zero hm0 hn0), if_neg hm0, if_neg hn0,
      Nat.factorization_mul hm0 hn0, Finsupp.add_apply, Finsupp.add_apply]
    have hcop_p : ∀ {p : ℕ}, p.Prime → ∀ g : ℕ → ℂ, g 0 = 1 →
        g (m.factorization p + n.factorization p) = g (m.factorization p) * g (n.factorization p) := by
      intro p hp g hg0
      have hnb : ¬(p ∣ m ∧ p ∣ n) := fun ⟨h1, h2⟩ =>
        Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, h1, h2⟩ hmn
      rcases not_and_or.mp hnb with hnm | hnn
      · rw [Nat.factorization_eq_zero_of_not_dvd hnm, zero_add, hg0, one_mul]
      · rw [Nat.factorization_eq_zero_of_not_dvd hnn, add_zero, hg0, mul_one]
    rw [hcop_p Nat.prime_three b₁ hb₁_0, hcop_p Nat.prime_two b₂ hb₂_0]
    ring
  have ha_unit : ∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤ 1 := fun n hn => by
    rw [ha_apply]; dsimp only [a_fn]; rw [if_neg (by omega), norm_mul]
    exact mul_le_one₀ (hb₁_norm _) (norm_nonneg _) (hb₂_norm _)
  -- Helper for prime-power increment convolution:
  have hinc_val : ∀ {p N : ℕ}, p.Prime → ∀ (b : ℕ → ℂ), b 0 = 1 → (∀ k, N < k → b k = 0) →
      let cp : ℕ → ℂ := fun d =>
        if d = 1 then 1 else ∑ k ∈ Finset.Icc 1 (N + 1), if d = p ^ k then b k - b (k - 1) else 0
      (∀ k : ℕ, cp (p ^ k) = if k = 0 then 1 else b k - b (k - 1)) ∧
      (∀ d : ℕ, cp d ≠ 0 → ∃ k ≤ N + 1, d = p ^ k) ∧
      (∀ m : ℕ, ∑ j ∈ Finset.range (m + 1), cp (p ^ j) = b m) := by
    intro p N hp b hb0 hbs cp
    have hcp_pk : ∀ k : ℕ, cp (p ^ k) = if k = 0 then 1 else b k - b (k - 1) := by
      intro k
      dsimp only [cp]
      rcases eq_or_ne k 0 with rfl | hk0
      · simp
      · have hpk_ne1 : p ^ k ≠ 1 := (Nat.one_lt_pow hk0 hp.one_lt).ne'
        rw [if_neg hpk_ne1, if_neg hk0]
        by_cases hk_le : k ≤ N + 1
        · rw [Finset.sum_eq_single k]
          · rw [if_pos rfl]
          · intro j _ hjk
            exact if_neg fun heq => hjk ((Nat.pow_right_injective hp.two_le) heq).symm
          · intro hnot
            exact absurd (Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hk0, hk_le⟩) hnot
        · rw [Finset.sum_eq_zero fun j hj => if_neg fun heq => by
            have hjk := (Nat.pow_right_injective hp.two_le) heq
            have := (Finset.mem_Icc.mp hj).2; omega]
          rw [hbs k (by omega), hbs (k - 1) (by omega), sub_self]
    have hcp_supp : ∀ d : ℕ, cp d ≠ 0 → ∃ k ≤ N + 1, d = p ^ k := by
      intro d hne
      dsimp only [cp] at hne
      by_cases hd1 : d = 1
      · exact ⟨0, Nat.zero_le _, by simp [hd1]⟩
      · rw [if_neg hd1] at hne
        obtain ⟨k, hk_mem, hk_ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
        by_cases hdk : d = p ^ k
        · exact ⟨k, (Finset.mem_Icc.mp hk_mem).2, hdk⟩
        · rw [if_neg hdk] at hk_ne; exact (hk_ne rfl).elim
    have htel : ∀ m : ℕ, ∑ j ∈ Finset.range (m + 1), cp (p ^ j) = b m := by
      intro m
      induction m with
      | zero => rw [Finset.sum_range_one, hcp_pk 0, if_pos rfl, hb0]
      | succ m ih =>
        rw [Finset.sum_range_succ, ih, hcp_pk (m + 1), if_neg (Nat.succ_ne_zero m),
          Nat.add_sub_cancel]
        ring
    exact ⟨hcp_pk, hcp_supp, htel⟩
  obtain ⟨hc₁_pk, hc₁_supp, hc₁_tel⟩ := hinc_val Nat.prime_three b₁ hb₁_0 hb₁_supp
  obtain ⟨hc₂_pk, hc₂_supp, hc₂_tel⟩ := hinc_val Nat.prime_two b₂ hb₂_0 hb₂_supp
  -- Identify `a` on `n ≥ 1` with `LSeries.convolution (LSeries.convolution 1 c₁) c₂ n`.
  have hconv1 : ∀ n : ℕ, n ≠ 0 → LSeries.convolution 1 c₁ n = b₁ (n.factorization 3) := by
    intro n hn0
    rw [LSeries.convolution_def]
    dsimp only
    rw [Nat.sum_divisorsAntidiagonal' (f := fun x y => (1 : ℕ → ℂ) x * c₁ y)]
    simp only [Pi.one_apply, one_mul]
    set m₃ : ℕ := n.factorization 3
    have hmap_sub : (Finset.range (m₃ + 1)).image (fun j => 3 ^ j) ⊆ n.divisors := by
      intro d hd
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hd
      exact Nat.mem_divisors.mpr
        ⟨dvd_trans (Nat.pow_dvd_pow 3 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
          (Nat.ordProj_dvd n 3), hn0⟩
    rw [← Finset.sum_subset hmap_sub fun d hd hnot => by
      by_contra hne
      obtain ⟨k, _, rfl⟩ := hc₁_supp d hne
      have hk_le : k ≤ m₃ :=
        (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hn0).mp (Nat.dvd_of_mem_divisors hd)
      exact hnot (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (Nat.lt_succ_of_le hk_le), rfl⟩)]
    rw [Finset.sum_image fun i _ j _ hij => Nat.pow_right_injective (by omega) hij]
    exact hc₁_tel m₃
  have hconv2 : ∀ n : ℕ, n ≠ 0 →
      LSeries.convolution (LSeries.convolution 1 c₁) c₂ n = a n := by
    intro n hn0
    rw [LSeries.convolution_def]
    dsimp only
    rw [Nat.sum_divisorsAntidiagonal' (f := fun x y => LSeries.convolution 1 c₁ x * c₂ y)]
    set m₂ : ℕ := n.factorization 2
    have hmap_sub : (Finset.range (m₂ + 1)).image (fun j => 2 ^ j) ⊆ n.divisors := by
      intro d hd
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hd
      exact Nat.mem_divisors.mpr
        ⟨dvd_trans (Nat.pow_dvd_pow 2 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
          (Nat.ordProj_dvd n 2), hn0⟩
    rw [← Finset.sum_subset hmap_sub fun d hd hnot => by
      by_contra hne
      have hc₂_ne : c₂ d ≠ 0 := right_ne_zero_of_mul hne
      obtain ⟨k, _, rfl⟩ := hc₂_supp d hc₂_ne
      have hk_le : k ≤ m₂ :=
        (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hn0).mp (Nat.dvd_of_mem_divisors hd)
      exact hnot (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (Nat.lt_succ_of_le hk_le), rfl⟩)]
    rw [Finset.sum_image fun i _ j _ hij => Nat.pow_right_injective (by omega) hij]
    have hterm_eq : ∀ j ∈ Finset.range (m₂ + 1),
        LSeries.convolution 1 c₁ (n / 2 ^ j) * c₂ (2 ^ j) =
          b₁ (n.factorization 3) * c₂ (2 ^ j) := by
      intro j hj
      have hdvd_2j : 2 ^ j ∣ n :=
        dvd_trans (Nat.pow_dvd_pow 2 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
          (Nat.ordProj_dvd n 2)
      have hmul_q : n / 2 ^ j * 2 ^ j = n := Nat.div_mul_cancel hdvd_2j
      have hq0_j : n / 2 ^ j ≠ 0 := fun h => hn0 (by rw [← hmul_q, h, zero_mul])
      have hf3_eq : (n / 2 ^ j).factorization 3 = n.factorization 3 := by
        have := congrArg (fun k => k.factorization 3) hmul_q
        rw [Nat.factorization_mul hq0_j (pow_ne_zero j two_ne_zero), Finsupp.add_apply,
          Nat.Prime.factorization_pow Nat.prime_two,
          Finsupp.single_eq_of_ne (by norm_num), add_zero] at this
        exact this
      rw [hconv1 _ hq0_j, hf3_eq]
    rw [Finset.sum_congr rfl hterm_eq, ← Finset.mul_sum, hc₂_tel m₂, ha_apply]
    dsimp only [a_fn]; rw [if_neg hn0]
  -- Step 4: Define `F(s)` globally via factored Euler polynomials and verify all properties.
  set P₁ : ℂ → ℂ := fun s => ∑ k ∈ Finset.range 4, b₁ k * ((3 : ℂ) ^ (-s)) ^ k
  set P₂ : ℂ → ℂ := fun s => ∑ k ∈ Finset.range 13, b₂ k * ((2 : ℂ) ^ (-s)) ^ k
  set F : ℂ → ℂ := fun s => riemannZeta s * ((1 - (3 : ℂ) ^ (-s)) * P₁ s) *
    ((1 - (2 : ℂ) ^ (-s)) * P₂ s)
  -- Identify `LSeries c₁ s = (1 - 3^{-s}) * P₁ s` and `LSeries c₂ s = (1 - 2^{-s}) * P₂ s`.
  have hLc_factor : ∀ {p N : ℕ}, p.Prime → ∀ (b : ℕ → ℂ), b 0 = 1 → (∀ k, N < k → b k = 0) →
      let cp : ℕ → ℂ := fun d =>
        if d = 1 then 1 else ∑ k ∈ Finset.Icc 1 (N + 1), if d = p ^ k then b k - b (k - 1) else 0
      ∀ s : ℂ, LSeriesSummable cp s ∧
        LSeries cp s = (1 - (p : ℂ) ^ (-s)) *
          ∑ k ∈ Finset.range (N + 1), b k * ((p : ℂ) ^ (-s)) ^ k := by
    intro p N hp b hb0 hbs cp s
    obtain ⟨hpk, hsupp_p, _⟩ := hinc_val hp b hb0 hbs
    have hfin_supp : ∀ n : ℕ, n ∉ (Finset.range (N + 2)).image (fun k => p ^ k) →
        LSeries.term cp s n = 0 := by
      intro n hn
      rcases eq_or_ne n 0 with rfl | hn0
      · exact LSeries.term_zero cp s
      · rw [LSeries.term_of_ne_zero hn0]
        have hcp0 : cp n = 0 := by
          by_contra hne
          obtain ⟨k, hk, rfl⟩ := hsupp_p n hne
          exact hn (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (Nat.lt_succ_of_le hk), rfl⟩)
        rw [hcp0, zero_div]
    refine ⟨summable_of_ne_finset_zero hfin_supp, ?_⟩
    unfold LSeries
    rw [tsum_eq_sum hfin_supp,
      Finset.sum_image fun i _ j _ hij => Nat.pow_right_injective hp.two_le hij]
    have hpow_cpow : ∀ k : ℕ, (((p ^ k : ℕ) : ℂ)) ^ (-s) = ((p : ℂ) ^ (-s)) ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ, Nat.cast_mul, ← Complex.ofReal_natCast (p ^ k), ← Complex.ofReal_natCast p,
          Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),
          Complex.ofReal_natCast, Complex.ofReal_natCast, ih, pow_succ]
    have hterm_k : ∀ k ∈ Finset.range (N + 2),
        LSeries.term cp s (p ^ k) =
          (if k = 0 then 1 else b k - b (k - 1)) * ((p : ℂ) ^ (-s)) ^ k := by
      intro k _
      rw [LSeries.term_of_ne_zero (pow_ne_zero k hp.ne_zero), div_eq_mul_inv,
        ← Complex.cpow_neg, hpow_cpow k]
      exact congrArg (· * ((p : ℂ) ^ (-s)) ^ k) (hpk k)
    rw [Finset.sum_congr rfl hterm_k]
    -- Algebraic telescoping `(1 - X) * ∑_{k=0}^N b k * X^k = 1 + ∑_{k=1}^{N+1} (b k - b (k-1)) X^k` since `b (N+1) = 0`.
    set X : ℂ := (p : ℂ) ^ (-s)
    have htel_poly : ∀ m : ℕ,
        (∑ k ∈ Finset.range (m + 1), (if k = 0 then (1 : ℂ) else b k - b (k - 1)) * X ^ k) =
          (1 - X) * (∑ k ∈ Finset.range m, b k * X ^ k) + b m * X ^ m := by
      intro m
      induction m with
      | zero => simp [hb0]
      | succ m ih =>
        rw [show m + 1 + 1 = (m + 1) + 1 by rfl, Finset.sum_range_succ, ih,
          if_neg (Nat.succ_ne_zero m), Nat.add_sub_cancel, Finset.sum_range_succ, pow_succ]
        ring
    rw [show N + 2 = (N + 1) + 1 by omega, htel_poly (N + 1), hbs (N + 1) (by omega),
      zero_mul, add_zero]
  have hL_eq_F : ∀ s : ℂ, 1 < s.re → LSeries a s = F s := by
    intro s hs
    have hsum1 : LSeriesSummable 1 s := LSeriesSummable_one_iff.mpr hs
    obtain ⟨hsum_c₁, hLc₁⟩ := hLc_factor Nat.prime_three b₁ hb₁_0 hb₁_supp s
    obtain ⟨hsum_c₂, hLc₂⟩ := hLc_factor Nat.prime_two b₂ hb₂_0 hb₂_supp s
    have ha_congr : LSeries a s = LSeries (LSeries.convolution (LSeries.convolution 1 c₁) c₂) s :=
      LSeries_congr (fun {n} hn0 => (hconv2 n hn0).symm) s
    rw [ha_congr, LSeries_convolution' (hsum1.convolution hsum_c₁) hsum_c₂,
      LSeries_convolution' hsum1 hsum_c₁, LSeries_one_eq_riemannZeta hs, hLc₁, hLc₂]
    rfl
  -- Differentiability of `F` on `ℂ \ {1}`.
  have hd_p : ∀ (p : ℕ), p ≠ 0 → Differentiable ℂ (fun s : ℂ => (p : ℂ) ^ (-s)) := by
    intro p hp0
    haveI : NeZero (p : ℂ) := ⟨by exact_mod_cast hp0⟩
    exact (differentiable_const_cpow_of_neZero (p : ℂ)).comp differentiable_id.neg
  have hd_P₁ : Differentiable ℂ P₁ := by
    have hfn : P₁ = ∑ k ∈ Finset.range 4, fun s : ℂ => b₁ k * ((3 : ℂ) ^ (-s)) ^ k := by
      funext s; unfold P₁; simp only [Finset.sum_apply]
    rw [hfn]
    exact Finset.sum_induction _ (Differentiable ℂ) (fun _ _ h₁ h₂ => h₁.add h₂)
      (differentiable_const 0) fun k _ => differentiable_const _ |>.mul ((hd_p 3 (by omega)).pow k)
  have hd_P₂ : Differentiable ℂ P₂ := by
    have hfn : P₂ = ∑ k ∈ Finset.range 13, fun s : ℂ => b₂ k * ((2 : ℂ) ^ (-s)) ^ k := by
      funext s; unfold P₂; simp only [Finset.sum_apply]
    rw [hfn]
    exact Finset.sum_induction _ (Differentiable ℂ) (fun _ _ h₁ h₂ => h₁.add h₂)
      (differentiable_const 0) fun k _ => differentiable_const _ |>.mul ((hd_p 2 (by omega)).pow k)
  have hd_E₁ : Differentiable ℂ (fun s => (1 - (3 : ℂ) ^ (-s)) * P₁ s) :=
    (differentiable_const 1 |>.sub (hd_p 3 (by omega))).mul hd_P₁
  have hd_E₂ : Differentiable ℂ (fun s => (1 - (2 : ℂ) ^ (-s)) * P₂ s) :=
    (differentiable_const 1 |>.sub (hd_p 2 (by omega))).mul hd_P₂
  have hF_diff : ∀ s : ℂ, s ≠ 1 → DifferentiableAt ℂ F s := fun s hs =>
    ((differentiableAt_riemannZeta hs).mul (hd_E₁ s)).mul (hd_E₂ s)
  -- Nonzero residue `R` at `s = 1`.
  set R : ℂ := ((1 - (3 : ℂ) ^ (-1 : ℂ)) * P₁ 1) * ((1 - (2 : ℂ) ^ (-1 : ℂ)) * P₂ 1)
  have hR_ne0 : R ≠ 0 := by
    dsimp only [R, P₁, P₂]
    have h3_inv : (3 : ℂ) ^ (-1 : ℂ) = ((1 / 3 : ℝ) : ℂ) := by
      rw [Complex.cpow_neg_one]; norm_num
    have h2_inv : (2 : ℂ) ^ (-1 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by
      rw [Complex.cpow_neg_one]; norm_num
    rw [h3_inv, h2_inv]
    have hP₁_nz : ∑ k ∈ Finset.range 4, b₁ k * ((1 / 3 : ℝ) : ℂ) ^ k ≠ 0 := by
      refine hb₁_nz (1 / 3) (by norm_num) ?_
      have hIcc : Finset.Icc 1 3 = {1, 2, 3} := by decide
      rw [hIcc]; norm_num
    have hP₂_nz : ∑ k ∈ Finset.range 13, b₂ k * ((1 / 2 : ℝ) : ℂ) ^ k ≠ 0 := by
      refine hb₂_nz (1 / 2) (by norm_num) ?_
      have hIcc : Finset.Icc 1 12 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12} := by decide
      rw [hIcc]; norm_num
    exact mul_ne_zero (mul_ne_zero (by norm_num) hP₁_nz) (mul_ne_zero (by norm_num) hP₂_nz)
  have hF_res : Tendsto (fun s : ℂ => (s - 1) * F s) (𝓝[≠] 1) (𝓝 R) := by
    have hcont_prod : ContinuousAt
        (fun s => ((1 - (3 : ℂ) ^ (-s)) * P₁ s) * ((1 - (2 : ℂ) ^ (-s)) * P₂ s)) 1 :=
      (hd_E₁.continuous.mul hd_E₂.continuous).continuousAt
    have hlim := riemannZeta_residue_one.mul hcont_prod.continuousWithinAt
    rw [one_mul] at hlim
    exact hlim.congr fun s => by dsimp only [F]; ring
  -- Vanishing at BOTH `s₀` and `1 - s₀`, hence `ξ_F(s₀) = ξ_F(1 - s₀) = 0`.
  have hF_s₀ : F s₀ = 0 := by
    dsimp only [F, P₁]
    rw [hb₁_van, mul_zero, mul_zero, zero_mul]
  have hF_1s₀ : F (1 - s₀) = 0 := by
    dsimp only [F, P₂]
    rw [hb₂_van, mul_zero, mul_zero]
  refine ⟨a, F, R, ha_mul, ha_unit, hL_eq_F, hF_diff, hR_ne0, hF_res, hF_s₀, hF_1s₀, ?_⟩
  rw [hF_s₀, hF_1s₀, mul_zero, mul_zero]

#print axioms zetaZeroAbscissa_le_sub_sevenEighths
#print axioms zetaZeroAbscissa_lt_one_unconditional
#print axioms not_summable_posTruncatedCoeff_prime_excess
#print axioms infinite_primes_posTruncatedCoeff_gt_one
#print axioms unbounded_squarefree_posTruncatedCoeff
#print axioms exists_left_strip_pole_and_regular_reflection_above_height
#print axioms posTruncatedZeta_antipodal_asymmetry_at_planted_zero
#print axioms unitPoleFreeCrossHeightDatum_riemannZeta
#print axioms crossHeight_gaussian_two_tsum_eq
#print axioms zetaChi_sub_two
#print axioms zetaChi_sub_two_mul
#print axioms exists_norm_zetaChi_leftStrip_rpow_le
#print axioms exists_norm_zetaChi_deep_even_le
#print axioms smoothAFEZetaDualCoefficientGeneral_eq_deep_even
#print axioms exists_norm_smoothAFEZetaDualCoefficientGeneral_deep_le
#print axioms crossHeightDirichletWitness_sub_le
#print axioms exists_sublinear_crossHeight_witness_bound_on_remaining_strip
#print axioms rh_iff_sublinear_crossHeight_witness_on_remaining_strip
#print axioms crossHeight_gaussian_mechanism_fails_on_posTruncatedZeta
#print axioms unit_bounded_multiplicative_twin_classification
#print axioms exists_even_conductor_four_unimodular_twin
#print axioms exists_unit_bounded_poleFree_singleOrdinate_countermodel_on_remaining_strip

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

end
