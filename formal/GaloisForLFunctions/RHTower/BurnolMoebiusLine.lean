import GaloisForLFunctions.RHTower.BurnolPowerLineShift
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# The line integral of `M(f)/ζ` on `Re s = 2` vanishes

Expanding `1/ζ` into the absolutely convergent Möbius series on `Re s = 2` and integrating term by
term, every term is a `k^{-s}` line integral, and those vanish (`BurnolPowerLineShift`).  This is
the first half of Burnol's Proposition 5.4.

## Main results

* `riemannZeta_inv_eq_tsum_term`
* `integral_extendedMellin_zeta_inv_two_eq_zero`
-/

open Complex Set Topology Filter MeasureTheory
open scoped BigOperators ArithmeticFunction

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- The Möbius expansion of `1/ζ` right of the one-line. -/
theorem riemannZeta_inv_eq_tsum_term {s : ℂ} (hs : 1 < s.re) :
    (riemannZeta s)⁻¹
      = ∑' n : ℕ, LSeries.term (fun m : ℕ => ((ArithmeticFunction.moebius m : ℤ) : ℂ)) s n := by
  have hzeta : LSeries (fun m : ℕ => ((ArithmeticFunction.zeta m : ℕ) : ℂ)) s = riemannZeta s :=
    ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs
  have hmul := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs
  rw [hzeta] at hmul
  have hne : riemannZeta s ≠ 0 := by
    intro h
    rw [h, zero_mul] at hmul
    exact zero_ne_one hmul
  field_simp
  rw [← LSeries]
  linear_combination -hmul

theorem norm_lseries_term_moebius_le (n : ℕ) {s : ℂ} (hs : s.re = 2) :
    ‖LSeries.term (fun m : ℕ => ((ArithmeticFunction.moebius m : ℤ) : ℂ)) s n‖
      ≤ (n : ℝ) ^ (-(2 : ℝ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term]
    positivity
  · rw [LSeries.term_of_ne_zero (by omega : n ≠ 0)]
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [norm_div, Complex.norm_natCast_cpow_of_pos hn, hs]
    have hnum : ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 := by
      have h := ArithmeticFunction.moebius_ne_zero_iff_eq_or (n := n)
      rcases eq_or_ne (ArithmeticFunction.moebius n) 0 with h0 | h0
      · rw [h0]; norm_num
      · rcases h.1 h0 with h1 | h1 <;> rw [h1] <;> norm_num
    have hpow : ((n : ℝ) ^ (2 : ℝ))⁻¹ = (n : ℝ) ^ (-(2 : ℝ)) := by
      rw [Real.rpow_neg hnpos.le]
    rw [div_eq_mul_inv, hpow]
    have hnn : (0 : ℝ) ≤ (n : ℝ) ^ (-(2 : ℝ)) := by positivity
    nlinarith [hnum, hnn]

/-! ## The vanishing of the `Re s = 2` integral -/

/-- **Proposition 5.4, first half.**  The line integral of `M(f)/ζ` on `Re s = 2` vanishes. -/
theorem integral_extendedMellin_zeta_inv_two_eq_zero {a : ℝ} (ha : 1 ≤ a) {f : SoninL2} {c d : ℂ}
    (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d)
    (hrapid : HasStripRapidDecrease (extendedMellinContinuation a c d f)) :
    (∫ τ : ℝ, extendedMellinContinuation a c d f ((2 : ℂ) + (τ : ℂ) * I)
        * (riemannZeta ((2 : ℂ) + (τ : ℂ) * I))⁻¹) = 0 := by
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le zero_lt_one ha
  set G : ℂ → ℂ := extendedMellinContinuation a c d f with hGdef
  set F : ℕ → ℝ → ℂ := fun n τ => G ((2 : ℂ) + (τ : ℂ) * I)
    * LSeries.term (fun m : ℕ => ((ArithmeticFunction.moebius m : ℤ) : ℂ))
        ((2 : ℂ) + (τ : ℂ) * I) n with hFdef
  have hre : ∀ τ : ℝ, ((2 : ℂ) + (τ : ℂ) * I).re = 2 := by intro τ; simp
  -- integrability of `G` on the line
  have hcontG : Continuous fun τ : ℝ => G ((2 : ℂ) + (τ : ℂ) * I) := by
    rw [hGdef]
    have h := continuous_extendedMellinContinuation_line ha0 hev hc hd
      (σ := (2 : ℝ)) (by norm_num) (by norm_num)
    simpa using h
  have hintG : Integrable (fun τ : ℝ => G ((2 : ℂ) + (τ : ℂ) * I)) volume := by
    rw [hGdef] at hcontG ⊢
    exact integrable_line_of_stripRapidDecrease hrapid hcontG
  set A : ℝ := ∫ τ : ℝ, ‖G ((2 : ℂ) + (τ : ℂ) * I)‖ with hAdef
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    exact integral_nonneg fun τ => norm_nonneg _
  -- each term
  have hFint : ∀ n : ℕ, Integrable (F n) volume := by
    intro n
    refine Integrable.mono' (hintG.norm.const_mul ((n : ℝ) ^ (-(2 : ℝ)))) ?_ ?_
    · rw [hFdef]
      refine hcontG.aestronglyMeasurable.mul ?_
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · have hz : (fun τ : ℝ => LSeries.term (fun m : ℕ => ((ArithmeticFunction.moebius m : ℤ) : ℂ))
            ((2 : ℂ) + (τ : ℂ) * I) 0) = fun _ => (0 : ℂ) := by
          funext τ
          simp [LSeries.term]
        rw [hz]
        exact aestronglyMeasurable_const
      · have hcont : Continuous fun τ : ℝ =>
            LSeries.term (fun m : ℕ => ((ArithmeticFunction.moebius m : ℤ) : ℂ))
              ((2 : ℂ) + (τ : ℂ) * I) n := by
          have hrw : ∀ τ : ℝ,
              LSeries.term (fun m : ℕ => ((ArithmeticFunction.moebius m : ℤ) : ℂ))
                ((2 : ℂ) + (τ : ℂ) * I) n
              = ((ArithmeticFunction.moebius n : ℤ) : ℂ)
                * ((n : ℂ) ^ ((2 : ℂ) + (τ : ℂ) * I))⁻¹ := by
            intro τ
            rw [LSeries.term_of_ne_zero (by omega : n ≠ 0), div_eq_mul_inv]
          refine Continuous.congr ?_ (fun τ => (hrw τ).symm)
          have hne : ∀ τ : ℝ, ((n : ℂ) ^ ((2 : ℂ) + (τ : ℂ) * I)) ≠ 0 := by
            intro τ
            refine cpow_ne_zero_iff.2 (Or.inl ?_)
            exact_mod_cast (by omega : n ≠ 0)
          refine continuous_const.mul (Continuous.inv₀ ?_ hne)
          have hbase : ((n : ℂ)) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
          have hcpow : Continuous fun τ : ℝ => Complex.exp
              (Complex.log (n : ℂ) * ((2 : ℂ) + (τ : ℂ) * I)) := by fun_prop
          refine hcpow.congr fun τ => ?_
          rw [Complex.cpow_def_of_ne_zero hbase]
        exact hcont.aestronglyMeasurable
    · filter_upwards with τ
      rw [hFdef]
      simp only
      rw [norm_mul]
      have hterm := norm_lseries_term_moebius_le n (hre τ)
      have hG0 : (0:ℝ) ≤ ‖G ((2 : ℂ) + (τ : ℂ) * I)‖ := norm_nonneg _
      nlinarith [hterm, hG0]
  have hFsum : Summable fun n : ℕ => ∫ τ : ℝ, ‖F n τ‖ := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun τ => norm_nonneg _)
      (fun n => ?_) (((Real.summable_nat_rpow_inv (p := 2)).2 (by norm_num)).mul_right A)
    have hbound : ∀ τ : ℝ, ‖F n τ‖ ≤ ((n : ℝ) ^ (2 : ℝ))⁻¹ * ‖G ((2 : ℂ) + (τ : ℂ) * I)‖ := by
      intro τ
      rw [hFdef]
      simp only
      rw [norm_mul]
      have hterm := norm_lseries_term_moebius_le n (hre τ)
      have hG0 : (0:ℝ) ≤ ‖G ((2 : ℂ) + (τ : ℂ) * I)‖ := norm_nonneg _
      have hrw : (n : ℝ) ^ (-(2 : ℝ)) = ((n : ℝ) ^ (2 : ℝ))⁻¹ := by
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · norm_num
        · rw [Real.rpow_neg (by positivity)]
      rw [hrw] at hterm
      nlinarith [hterm, hG0]
    calc (∫ τ : ℝ, ‖F n τ‖) ≤ ∫ τ : ℝ, ((n : ℝ) ^ (2 : ℝ))⁻¹ * ‖G ((2 : ℂ) + (τ : ℂ) * I)‖ := by
          refine integral_mono (hFint n).norm
            (hintG.norm.const_mul (((n : ℝ) ^ (2 : ℝ))⁻¹)) (fun τ => hbound τ)
      _ = ((n : ℝ) ^ (2 : ℝ))⁻¹ * A := by rw [integral_const_mul, hAdef]
  -- the interchange
  have hswap := integral_tsum_of_summable_integral_norm hFint hFsum
  have hterm_zero : ∀ n : ℕ, (∫ τ : ℝ, F n τ) = 0 := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hFdef, LSeries.term]
    · have hnpos : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hka : 1 / (n : ℝ) ≤ a := by
        have hn1 : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        have : 1 / (n : ℝ) ≤ 1 := by
          rw [div_le_one hnpos]
          exact hn1
        linarith
      have hline := burnolPowLine_two_eq_zero ha0 hev hc hd hrapid hnpos hka
      have hrw : (∫ τ : ℝ, F n τ)
          = ((ArithmeticFunction.moebius n : ℤ) : ℂ)
            * burnolPowLine (extendedMellinContinuation a c d f) (n : ℝ) 2 := by
        rw [burnolPowLine, ← MeasureTheory.integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
        rw [hFdef]
        simp only
        rw [LSeries.term_of_ne_zero (by omega : n ≠ 0)]
        have hbase : ((n : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt hnpos)
        have hcast : ((n : ℕ) : ℂ) = ((n : ℝ) : ℂ) := by push_cast; ring
        rw [hcast, Complex.cpow_neg, div_eq_mul_inv,
          show (((2 : ℝ) : ℂ) + (τ : ℂ) * I) = (2 : ℂ) + (τ : ℂ) * I by push_cast; ring]
        ring
      rw [hrw, hline, mul_zero]
  have hzero : (∑' n : ℕ, ∫ τ : ℝ, F n τ) = 0 := by
    rw [tsum_congr hterm_zero, tsum_zero]
  have hintegrand : ∀ τ : ℝ, G ((2 : ℂ) + (τ : ℂ) * I) * (riemannZeta ((2 : ℂ) + (τ : ℂ) * I))⁻¹
      = ∑' n : ℕ, F n τ := by
    intro τ
    rw [hFdef]
    simp only
    rw [tsum_mul_left]
    congr 1
    exact riemannZeta_inv_eq_tsum_term (s := (2 : ℂ) + (τ : ℂ) * I) (by rw [hre τ]; norm_num)
  calc (∫ τ : ℝ, G ((2 : ℂ) + (τ : ℂ) * I) * (riemannZeta ((2 : ℂ) + (τ : ℂ) * I))⁻¹)
      = ∫ τ : ℝ, ∑' n : ℕ, F n τ :=
        integral_congr_ae (Filter.Eventually.of_forall hintegrand)
    _ = ∑' n : ℕ, ∫ τ : ℝ, F n τ := hswap.symm
    _ = 0 := hzero

end

end RHTower
