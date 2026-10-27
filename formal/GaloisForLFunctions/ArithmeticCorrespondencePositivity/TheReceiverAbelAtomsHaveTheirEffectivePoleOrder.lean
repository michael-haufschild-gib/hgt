import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheAbelMassDetectsThePoleOrder
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheReceiverPoleOrdersAreVisibleTranslatedZeroOrders
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheReceiverSpectralDensityAtTheZeroAbscissa
import Mathlib.Analysis.Meromorphic.TrailingCoefficient

/-!
# Arbitrary-multiplicity atoms of the actual Möbius receiver

The effective translated zero order determines the exact local Abel scale.
Analytic factorization accounts for numerator cancellation; the Hardy energy
estimate supplies the actual source on every approaching vertical line.
-/

open Complex Set Filter Topology MeasureTheory
open RHTower GaloisForLFunctions.ArithmeticOrientationTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

/-- A shifted pole factor determines the canonical Laurent coefficient. -/
theorem meromorphicTrailingCoeffAt_eq_of_shifted_pole_factor {F H : ℂ → ℂ} {s : ℂ} {m : ℕ}
    (hH : AnalyticAt ℂ H 0) (hH0 : H 0 ≠ 0)
    (hf : ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 0 → F (s + z) = H z / z ^ m) :
    meromorphicTrailingCoeffAt F s = H 0 := by
  have hA : AnalyticAt ℂ (fun w : ℂ => H (w - s)) s := by
    have hH' : AnalyticAt ℂ H (s - s) := by simpa only [sub_self] using hH
    exact hH'.comp (f := fun w : ℂ => w - s) (analyticAt_id.sub analyticAt_const)
  have h0 : H (s - s) ≠ 0 := by simpa only [sub_self] using hH0
  have ht : Tendsto (fun w : ℂ => w - s) (𝓝 s) (𝓝 0) := by
    simpa only [sub_self] using (by fun_prop : Continuous fun w : ℂ => w - s).tendsto s
  have h := hA.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE
    (f := F) (n := -(m : ℤ)) h0
  apply (by simpa only [sub_self] using h)
  filter_upwards [(ht.eventually hf).filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
    with w hw hws
  have heq := hw (sub_ne_zero.mpr hws)
  rw [show s + (w - s) = w by ring] at heq
  rw [heq]
  simp only [smul_eq_mul, zpow_neg, zpow_natCast, div_eq_mul_inv]
  ring

/-- A local factorization of the centered symbol is a uniform box factorization
of the actual Fourier symbol on approaching vertical lines. -/
theorem exists_receiver_window_factor_of_germ {ε : ℝ} (hε : 0 < ε) {ρ : ℂ}
    (hmax : ρ.re = zetaZeroAbscissa) (hre : 1 / 2 + ε < ρ.re) (hre1 : ρ.re < 1)
    {H : ℂ → ℂ} {m : ℕ} (hH : ContinuousAt H 0)
    (hfac : ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 0 →
      centeredReceiverSymbol ε (ρ - (ε : ℂ) + z) = H z / z ^ m) :
    ∃ δ > 0, ∃ M : ℝ, 0 ≤ M ∧ ∀ e ∈ Ioo 0 δ, ∀ y ∈ Icc (ρ.im - δ) (ρ.im + δ),
      ‖H ((e : ℂ) + ((y - ρ.im : ℝ) : ℂ) * I)‖ ≤ M ∧
      lineSymbol (receiverLogProfile ε) (zetaZeroAbscissa - ε - 1 / 2 + e) y =
        H ((e : ℂ) + ((y - ρ.im : ℝ) : ℂ) * I) /
          ((e : ℂ) + ((y - ρ.im : ℝ) : ℂ) * I) ^ m := by
  have hθ : 0 < zetaZeroAbscissa - ε - 1 / 2 := by rw [← hmax]; linarith
  have hΘ1 : zetaZeroAbscissa < 1 := by rw [← hmax]; exact hre1
  obtain ⟨r₁, hr₁, hf⟩ := Metric.eventually_nhds_iff_ball.mp hfac
  obtain ⟨r₂, hr₂, hHb⟩ := Metric.continuousAt_iff.mp hH 1 zero_lt_one
  let r : ℝ := min r₁ r₂
  have hr : 0 < r := lt_min hr₁ hr₂
  let δ : ℝ := min (r / 3) ((1 - zetaZeroAbscissa) / 2)
  have hδ : 0 < δ := lt_min (by positivity) (by linarith)
  refine ⟨δ, hδ, ‖H 0‖ + 1, by positivity, fun e he y hy => ?_⟩
  have hn : ‖(e : ℂ) + ((y - ρ.im : ℝ) : ℂ) * I‖ < r := by
    have hyδ : |y - ρ.im| ≤ δ := abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
    calc ‖(e : ℂ) + ((y - ρ.im : ℝ) : ℂ) * I‖
        ≤ ‖(e : ℂ)‖ + ‖((y - ρ.im : ℝ) : ℂ) * I‖ := norm_add_le _ _
      _ = e + |y - ρ.im| := by
        simp only [norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos he.1]
      _ < r := by have := min_le_left (r / 3) ((1 - zetaZeroAbscissa) / 2); linarith [he.2]
  refine ⟨?_, ?_⟩
  · have h := hHb (by simpa only [dist_zero_right] using hn.trans_le (min_le_right r₁ r₂))
    rw [dist_eq_norm] at h
    have hnorm := norm_sub_norm_le (H ((e : ℂ) + ((y - ρ.im : ℝ) : ℂ) * I)) (H 0)
    linarith
  · have he1 : e < 1 - zetaZeroAbscissa := by
      have := min_le_right (r / 3) ((1 - zetaZeroAbscissa) / 2)
      linarith [he.2]
    rw [lineSymbol_receiver_eq_centered_at_zeroAbscissa hε hθ he.1 he1]
    have hpt : ρ - (ε : ℂ) + ((e : ℂ) + ((y - ρ.im : ℝ) : ℂ) * I) =
        (((zetaZeroAbscissa - ε + e : ℝ) : ℂ) + (y : ℂ) * I) := by
      apply Complex.ext <;> simp [hmax]
    rw [← hpt]
    apply hf _ ?_ ?_
    · rw [Metric.mem_ball, dist_zero_right]
      exact hn.trans_le (min_le_left r₁ r₂)
    · intro h
      have := congrArg Complex.re h
      simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
        zero_mul, sub_self, add_zero, zero_re] at this
      linarith [he.1]

/-- The exact mass of a multiple pole uses its canonical leading Laurent
coefficient; arbitrary continuous bounded test weights are allowed. -/
theorem receiver_pole_coefficient_ne_zero_and_atom {ε : ℝ} (hε : 0 < ε) {ρ : ℂ}
    (hz : riemannZeta ρ = 0) (hmax : ρ.re = zetaZeroAbscissa)
    (hre : 1 / 2 + ε < ρ.re) (hre1 : ρ.re < 1) {m : ℕ}
    (hm : 0 < m) (horder : visibleTranslatedZetaOrder ε ρ = (m : ℕ∞)) :
    meromorphicTrailingCoeffAt (centeredReceiverSymbol ε) (ρ - (ε : ℂ)) ≠ 0 ∧
      ∃ δ₀ > 0, ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ (w : ℝ → ℝ) (W : ℝ), Continuous w → (∀ y, |w y| ≤ W) →
        Tendsto (fun e : ℝ => e ^ (2 * m - 1) *
          ∫ y in Icc (ρ.im - δ) (ρ.im + δ),
            ‖lineSymbol (receiverLogProfile ε) (zetaZeroAbscissa - ε - 1 / 2 + e) y‖ ^ 2 * w y)
          (𝓝[>] 0) (𝓝 (poleMassConstant m *
            ‖meromorphicTrailingCoeffAt (centeredReceiverSymbol ε) (ρ - (ε : ℂ))‖ ^ 2 * w ρ.im)) := by
  obtain ⟨H, hH, hH0, hfac⟩ := exists_centeredReceiverSymbol_pole_factor hε hz hre hre1 hm horder
  rw [meromorphicTrailingCoeffAt_eq_of_shifted_pole_factor hH hH0 hfac]
  have hθ : 0 < zetaZeroAbscissa - ε - 1 / 2 := by rw [← hmax]; linarith
  obtain ⟨δ₀, hδ₀, M, hM, hbox⟩ :=
    exists_receiver_window_factor_of_germ hε hmax hre hre1 hH.continuousAt hfac
  refine ⟨hH0, δ₀, hδ₀, fun δ hδ hδle w W hw hwW => ?_⟩
  have hbox' : ∀ e ∈ Ioo 0 δ, ∀ y ∈ Icc (ρ.im - δ) (ρ.im + δ),
      ‖H ((e : ℂ) + ((y - ρ.im : ℝ) : ℂ) * I)‖ ≤ M ∧
      lineSymbol (receiverLogProfile ε) (zetaZeroAbscissa - ε - 1 / 2 + e) y =
        H ((e : ℂ) + ((y - ρ.im : ℝ) : ℂ) * I) /
          ((e : ℂ) + ((y - ρ.im : ℝ) : ℂ) * I) ^ m := by
    intro e he y hy
    exact hbox e ⟨he.1, he.2.trans_le hδle⟩ y
      ⟨by linarith [hy.1], by linarith [hy.2]⟩
  refine tendsto_window_atom_of_pole_order (Nat.one_le_iff_ne_zero.mpr hm.ne') hδ
    hM ?_ hH.continuousAt (fun e he y hy => (hbox' e he y hy).1)
    (fun e he y hy => (hbox' e he y hy).2) hw hwW
  · intro e he
    exact continuous_lineSymbol (receiver_data_at_zeroAbscissa hε hθ he.1).1

/-- Every positive effective order supplies a nonzero finite-height atom. -/
theorem exists_receiver_pole_order_atom {ε : ℝ} (hε : 0 < ε) {ρ : ℂ}
    (hz : riemannZeta ρ = 0) (hmax : ρ.re = zetaZeroAbscissa)
    (hre : 1 / 2 + ε < ρ.re) (hre1 : ρ.re < 1) {m : ℕ}
    (hm : 0 < m) (horder : visibleTranslatedZetaOrder ε ρ = (m : ℕ∞)) :
    ∃ a : ℂ, a ≠ 0 ∧ ∃ δ₀ > 0, ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ (w : ℝ → ℝ) (W : ℝ), Continuous w → (∀ y, |w y| ≤ W) →
        Tendsto (fun e : ℝ => e ^ (2 * m - 1) *
          ∫ y in Icc (ρ.im - δ) (ρ.im + δ),
            ‖lineSymbol (receiverLogProfile ε) (zetaZeroAbscissa - ε - 1 / 2 + e) y‖ ^ 2 * w y)
          (𝓝[>] 0) (𝓝 (poleMassConstant m * ‖a‖ ^ 2 * w ρ.im)) :=
  ⟨_, receiver_pole_coefficient_ne_zero_and_atom hε hz hmax hre hre1 hm horder⟩

/-- Full multiplicity cancellation leaves the actual spectral density bounded
in a window, including when both zeta factors vanish there. -/
theorem exists_receiver_regular_window_bound {ε : ℝ} (hε : 0 < ε) {ρ : ℂ}
    (hz : riemannZeta ρ = 0) (hmax : ρ.re = zetaZeroAbscissa)
    (hre : 1 / 2 + ε < ρ.re) (hre1 : ρ.re < 1)
    (horder : visibleTranslatedZetaOrder ε ρ = 0) :
    ∃ δ > 0, ∃ M : ℝ, 0 ≤ M ∧ ∀ e ∈ Ioo 0 δ, ∀ y ∈ Icc (ρ.im - δ) (ρ.im + δ),
      ‖lineSymbol (receiverLogProfile ε) (zetaZeroAbscissa - ε - 1 / 2 + e) y‖ ≤ M := by
  obtain ⟨H, hH, hf⟩ := exists_centeredReceiverSymbol_regular_factor hε hz hre hre1 horder
  have hf' : ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 0 →
      centeredReceiverSymbol ε (ρ - (ε : ℂ) + z) = H z / z ^ (0 : ℕ) := by
    simpa only [pow_zero, div_one] using hf
  obtain ⟨δ, hδ, M, hM, hbox⟩ :=
    exists_receiver_window_factor_of_germ hε hmax hre hre1 hH.continuousAt hf'
  refine ⟨δ, hδ, M, hM, fun e he y hy => ?_⟩
  obtain ⟨hb, heq⟩ := hbox e he y hy
  rw [heq, pow_zero, div_one]
  exact hb

#print axioms exists_receiver_pole_order_atom
#print axioms receiver_pole_coefficient_ne_zero_and_atom
#print axioms exists_receiver_regular_window_bound

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
