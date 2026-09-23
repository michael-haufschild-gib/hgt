import GaloisForLFunctions.HTGeometry.VerticalFlatGermElimination
import GaloisForLFunctions.HTGeometry.PolygammaVerticalDecay
import GaloisForLFunctions.HTGeometry.DigammaFieldLexRatio
import GaloisForLFunctions.HTGeometry.GammaVerticalPolynomialDecay

/-!
# Polynomial growth on vertical lines

A function has polynomial growth to the right of `σ₀` when on every vertical line there its modulus
is eventually bounded by a power of the height.  Sums and products of such functions have it, the
rational germs have it, and so does every digamma jet: `ψ` is logarithmic and every higher jet
vanishes.

`Γ` decays faster than every power on a vertical line, so `Γ` times anything of polynomial growth is
flat there.  Together with the line form of the flat elimination this is what separates the `Γ`-adic
direction from the digamma field.
-/

open Filter Topology Complex Polynomial

namespace GaloisForLFunctions

/-- A function has polynomial growth to the right of `σ₀` when on each vertical line its modulus is
eventually dominated by a power of the height. -/
def HasPolyGrowth (σ₀ : ℝ) (A : ℂ → ℂ) : Prop :=
  ∀ σ : ℝ, σ₀ ≤ σ → ∃ (M : ℕ) (C : ℝ), 0 ≤ C ∧
    ∀ᶠ t : ℝ in atTop, ‖A ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * t ^ M

theorem HasPolyGrowth.add {σ₀ : ℝ} {A B : ℂ → ℂ} (hA : HasPolyGrowth σ₀ A)
    (hB : HasPolyGrowth σ₀ B) : HasPolyGrowth σ₀ (fun s => A s + B s) := by
  intro σ hσ
  obtain ⟨M, C, hC, hAb⟩ := hA σ hσ
  obtain ⟨N, D, hD, hBb⟩ := hB σ hσ
  refine ⟨max M N, C + D, by linarith, ?_⟩
  filter_upwards [hAb, hBb, eventually_ge_atTop (1 : ℝ)] with t ha hb ht
  have hM : t ^ M ≤ t ^ (max M N) := pow_le_pow_right₀ ht (le_max_left _ _)
  have hN : t ^ N ≤ t ^ (max M N) := pow_le_pow_right₀ ht (le_max_right _ _)
  calc ‖A ((σ : ℂ) + (t : ℂ) * Complex.I) + B ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ ‖A ((σ : ℂ) + (t : ℂ) * Complex.I)‖ + ‖B ((σ : ℂ) + (t : ℂ) * Complex.I)‖ :=
        norm_add_le _ _
    _ ≤ C * t ^ M + D * t ^ N := add_le_add ha hb
    _ ≤ C * t ^ (max M N) + D * t ^ (max M N) := by
        have h1 : C * t ^ M ≤ C * t ^ (max M N) := mul_le_mul_of_nonneg_left hM hC
        have h2 : D * t ^ N ≤ D * t ^ (max M N) := mul_le_mul_of_nonneg_left hN hD
        linarith
    _ = (C + D) * t ^ (max M N) := by ring

theorem HasPolyGrowth.mul {σ₀ : ℝ} {A B : ℂ → ℂ} (hA : HasPolyGrowth σ₀ A)
    (hB : HasPolyGrowth σ₀ B) : HasPolyGrowth σ₀ (fun s => A s * B s) := by
  intro σ hσ
  obtain ⟨M, C, hC, hAb⟩ := hA σ hσ
  obtain ⟨N, D, hD, hBb⟩ := hB σ hσ
  refine ⟨M + N, C * D, by positivity, ?_⟩
  filter_upwards [hAb, hBb, eventually_ge_atTop (0 : ℝ)] with t ha hb ht
  have hnn : (0 : ℝ) ≤ ‖B ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := norm_nonneg _
  calc ‖A ((σ : ℂ) + (t : ℂ) * Complex.I) * B ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      = ‖A ((σ : ℂ) + (t : ℂ) * Complex.I)‖ * ‖B ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := norm_mul _ _
    _ ≤ (C * t ^ M) * (D * t ^ N) := by
        refine mul_le_mul ha hb hnn (by positivity)
    _ = C * D * t ^ (M + N) := by
        rw [pow_add]
        ring

/-- A bounded function has polynomial growth. -/
theorem hasPolyGrowth_of_eventually_le {σ₀ : ℝ} {A : ℂ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ σ : ℝ, σ₀ ≤ σ → ∀ᶠ t : ℝ in atTop,
      ‖A ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C) : HasPolyGrowth σ₀ A := by
  intro σ hσ
  refine ⟨0, C, hC, ?_⟩
  filter_upwards [h σ hσ] with t ht
  simpa using ht

/-- Polynomial values have polynomial growth. -/
theorem hasPolyGrowth_polynomial {σ₀ : ℝ} (hσ₀ : 0 ≤ σ₀) (p : Polynomial ℂ) :
    HasPolyGrowth σ₀ (fun s => p.eval s) := by
  intro σ hσ
  obtain ⟨C, hC, hb⟩ := eventually_norm_eval_le (le_trans hσ₀ hσ) p
  exact ⟨p.natDegree, C, hC.le, hb⟩

/-- Rational values have polynomial growth. -/
theorem hasPolyGrowth_ratFunc {σ₀ : ℝ} (hσ₀ : 0 ≤ σ₀) (k : RatFunc ℂ) :
    HasPolyGrowth σ₀ (fun s => k.num.eval s / k.denom.eval s) := by
  intro σ hσ
  have hσ0 : 0 ≤ σ := le_trans hσ₀ hσ
  obtain ⟨C, hC, hnum⟩ := eventually_norm_eval_le hσ0 k.num
  obtain ⟨c, hc, hden⟩ := eventually_norm_eval_ge (σ := σ) k.denom_ne_zero
  refine ⟨k.num.natDegree, C / c, by positivity, ?_⟩
  filter_upwards [hnum, hden, eventually_ge_atTop (1 : ℝ)] with t hn hd ht
  have hnorm1 : (1 : ℝ) ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ := by
    have him : ‖((σ : ℂ) + (t : ℂ) * Complex.I).im‖ ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ :=
      Complex.abs_im_le_norm _
    have hval : ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
    rw [hval, Real.norm_eq_abs, abs_of_nonneg (le_trans zero_le_one ht)] at him
    linarith
  have hpowge : (1 : ℝ) ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ k.denom.natDegree :=
    one_le_pow₀ hnorm1
  have hdc : c ≤ ‖k.denom.eval ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by nlinarith
  have hdpos : (0 : ℝ) < ‖k.denom.eval ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := lt_of_lt_of_le hc hdc
  rw [norm_div, div_le_iff₀ hdpos]
  have hstep : C / c * t ^ k.num.natDegree * c
      ≤ C / c * t ^ k.num.natDegree * ‖k.denom.eval ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
    have hnn : (0 : ℝ) ≤ C / c * t ^ k.num.natDegree := by
      have : (0 : ℝ) ≤ t := le_trans zero_le_one ht
      positivity
    exact mul_le_mul_of_nonneg_left hdc hnn
  have hcc : C / c * t ^ k.num.natDegree * c = C * t ^ k.num.natDegree := by
    field_simp
  linarith [hn]

/-- The digamma function has polynomial growth: it is logarithmic on every vertical line. -/
theorem hasPolyGrowth_digamma {σ₀ : ℝ} (hσ₀ : 0 ≤ σ₀) :
    HasPolyGrowth σ₀ (fun s => Complex.digamma s) := by
  intro σ hσ
  have hσ0 : 0 ≤ σ := le_trans hσ₀ hσ
  refine ⟨1, 2 * (1 + Real.pi / 2), by positivity, ?_⟩
  have hdiv := tendsto_digamma_div_vertLog (σ := σ) hσ0
  have hclose : ∀ᶠ t : ℝ in atTop,
      ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) / vertLog t‖ ≤ 2 := by
    have h := hdiv.norm
    have hlt : ∀ᶠ t : ℝ in atTop,
        ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) / vertLog t‖ < 2 :=
      h.eventually (eventually_lt_nhds (by norm_num))
    filter_upwards [hlt] with t ht using ht.le
  filter_upwards [hclose, eventually_vertLog_ne_zero, eventually_ge_atTop (1 : ℝ)]
    with t hc hL ht
  have hlog : Real.log t ≤ t := Real.log_le_sub_one_of_pos (lt_of_lt_of_le zero_lt_one ht) |>.trans
    (by linarith)
  have hLnorm : ‖vertLog t‖ ≤ Real.log t + Real.pi / 2 := norm_vertLog_le ht
  have hLpos : (0 : ℝ) < ‖vertLog t‖ := norm_pos_iff.mpr hL
  have hquot : ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 2 * ‖vertLog t‖ := by
    rw [norm_div, div_le_iff₀ hLpos] at hc
    linarith
  have hbound : ‖vertLog t‖ ≤ (1 + Real.pi / 2) * t := by
    have hpi : (0 : ℝ) ≤ Real.pi / 2 := by positivity
    have hstep : Real.pi / 2 ≤ Real.pi / 2 * t := le_mul_of_one_le_right hpi ht
    calc ‖vertLog t‖ ≤ Real.log t + Real.pi / 2 := hLnorm
      _ ≤ t + Real.pi / 2 * t := by linarith
      _ = (1 + Real.pi / 2) * t := by ring
  calc ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 2 * ‖vertLog t‖ := hquot
    _ ≤ 2 * ((1 + Real.pi / 2) * t) := by linarith
    _ = 2 * (1 + Real.pi / 2) * t ^ (1 : ℕ) := by ring

/-- Every positive-order digamma jet is bounded, hence of polynomial growth. -/
theorem hasPolyGrowth_iteratedDeriv_succ_digamma {σ₀ : ℝ} (hσ₀ : 0 < σ₀) (j : ℕ) :
    HasPolyGrowth σ₀ (fun s => iteratedDeriv (j + 1) Complex.digamma s) := by
  refine hasPolyGrowth_of_eventually_le (C := 1) zero_le_one (fun σ hσ => ?_)
  have hσ0 : 0 < σ := lt_of_lt_of_le hσ₀ hσ
  have h : Tendsto (fun t : ℝ =>
      ‖iteratedDeriv (j + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖) atTop (nhds 0) := by
    simpa using (tendsto_iteratedDeriv_succ_digamma_vertical hσ0 j).norm
  have hlt : ∀ᶠ t : ℝ in atTop,
      ‖iteratedDeriv (j + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ < 1 :=
    h.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hlt] with t ht using ht.le

/-- Every digamma jet has polynomial growth. -/
theorem hasPolyGrowth_digammaJet {σ₀ : ℝ} (hσ₀ : 0 < σ₀) (j : ℕ) :
    HasPolyGrowth σ₀ (fun s => iteratedDeriv j Complex.digamma s) := by
  cases j with
  | zero => simpa using hasPolyGrowth_digamma hσ₀.le
  | succ n => exact hasPolyGrowth_iteratedDeriv_succ_digamma hσ₀ n

/-- **Gamma kills polynomial growth.**  On every vertical line to the right of a positive abscissa,
`Γ` times a function of polynomial growth is flat. -/
theorem isVertFlat_gamma_mul {σ₀ : ℝ} (hσ₀ : 0 < σ₀) {B : ℂ → ℂ} (hB : HasPolyGrowth σ₀ B) :
    IsVertFlat σ₀ (fun s => Complex.Gamma s * B s) := by
  intro N σ hσ
  have hσ0 : 0 < σ := lt_of_lt_of_le hσ₀ hσ
  obtain ⟨M, C, hC, hb⟩ := hB σ hσ
  have hgam := (tendsto_pow_mul_Gamma_vertical hσ0 (N + M)).norm
  have hgam0 : Tendsto (fun t : ℝ => C * ‖(t : ℂ) ^ (N + M)
      * Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖) atTop (nhds 0) := by
    have := hgam.const_mul C
    simpa using this
  refine squeeze_zero' ?_ ?_ hgam0
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    positivity
  filter_upwards [hb, eventually_ge_atTop (0 : ℝ)] with t hbt ht
  have hnormt : ‖(t : ℂ) ^ (N + M)‖ = t ^ (N + M) := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
  have hgnn : (0 : ℝ) ≤ ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := norm_nonneg _
  calc t ^ N * ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)
        * B ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      = t ^ N * (‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖
          * ‖B ((σ : ℂ) + (t : ℂ) * Complex.I)‖) := by rw [norm_mul]
    _ ≤ t ^ N * (‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ * (C * t ^ M)) := by
        have := mul_le_mul_of_nonneg_left hbt hgnn
        exact mul_le_mul_of_nonneg_left this (by positivity)
    _ = C * (t ^ (N + M) * ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖) := by
        rw [pow_add]
        ring
    _ = C * ‖(t : ℂ) ^ (N + M) * Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
        rw [norm_mul, hnormt]

end GaloisForLFunctions
