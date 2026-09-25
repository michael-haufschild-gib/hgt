import GaloisForLFunctions.RHTower.SquareRootSummatoryMellin
import GaloisForLFunctions.RHTower.MobiusDivisorCriticalStepMellinWeld

/-!
# Mellin transform of the literal critical square-root Abel source

The coefficient `Λ(n) - 1` has a single correction at `n = 1`. Its partial
sum is exactly `ψ(n) - n + 2γ`, so the pre-existing square-root summatory
convolution theorem applies to the actual critical source. The resulting
Mellin value is the step-source current gap, with no formal replacement of
the arithmetic coefficient.
-/

noncomputable section
open Complex MeasureTheory Set Finset ArithmeticFunction Filter Topology
namespace RHTower

/-- Atomic coefficient whose partial sum is the complete critical defect. -/
def criticalSourceCoeff (n : ℕ) : ℂ :=
  (vonMangoldt n : ℂ) - 1 +
    2 * (Real.eulerMascheroniConstant : ℂ) * LSeries.delta n

/-- Exact cumulative identification, including the correction at one. -/
theorem criticalSourceCoeff_cumulative (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Icc 1 N, criticalSourceCoeff n) = (psiDefect N : ℂ) := by
  simp only [criticalSourceCoeff, sum_add_distrib, sum_sub_distrib,
    ← Finset.mul_sum]
  have hdelta : (∑ n ∈ Icc 1 N, LSeries.delta n) = (1 : ℂ) := by
    simpa [LSeries.delta] using (show (∑ n ∈ Icc 1 N,
      if n = 1 then (1 : ℂ) else 0) = 1 by
        rw [sum_ite_eq']
        simp [hN])
  rw [hdelta]
  simp [psiDefect, chebyshevPsi]

private def criticalSourceCoeffBound : ℝ :=
  Real.log 4 + 6 + 2 * |Real.eulerMascheroniConstant|

private theorem criticalSourceCoeffBound_nonneg : 0 ≤ criticalSourceCoeffBound := by
  unfold criticalSourceCoeffBound
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  positivity

private theorem criticalSourceCoeff_cumulative_bound (N : ℕ) :
    ‖∑ n ∈ Icc 1 N, criticalSourceCoeff n‖ ≤
      criticalSourceCoeffBound * (N : ℝ) ^ (1 : ℝ) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  rw [criticalSourceCoeff_cumulative N hN, Complex.norm_real,
    Real.norm_eq_abs, Real.rpow_one]
  have hpsi : chebyshevPsi N ≤ (Real.log 4 + 4) * (N : ℝ) :=
    Mertens.sum_vonMangoldt_Icc_le N
  have hpsi0 : 0 ≤ chebyshevPsi N :=
    Finset.sum_nonneg fun _ _ => vonMangoldt_nonneg
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  unfold criticalSourceCoeffBound
  rw [psiDefect]
  apply abs_le.mpr
  constructor <;> nlinarith [le_abs_self Real.eulerMascheroniConstant,
    neg_abs_le Real.eulerMascheroniConstant,
    mul_nonneg (abs_nonneg Real.eulerMascheroniConstant) (sub_nonneg.mpr hNR)]

private theorem criticalSourceCoeff_summable {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable criticalSourceCoeff s := by
  have hvm : LSeriesSummable (fun n => (vonMangoldt n : ℂ)) s :=
    LSeriesSummable_vonMangoldt hs
  have hone : LSeriesSummable (1 : ℕ → ℂ) s := LSeriesSummable_one_iff.mpr hs
  have hbase : LSeriesSummable
      ((fun n => (vonMangoldt n : ℂ)) - (1 : ℕ → ℂ)) s := hvm.sub hone
  refine LSeriesSummable.congr' s ?_ hbase
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  have hn1 : n ≠ 1 := by omega
  simp [criticalSourceCoeff, LSeries.delta, hn1, Pi.sub_apply]

/-- The coefficient series is the literal step-source Mellin integral. -/
theorem criticalSourceCoeff_LSeries_eq_stepMellin {w : ℂ} (hw : 1 < w.re) :
    LSeries criticalSourceCoeff w = w * criticalStepSourceMellin w := by
  have hm := mellin_complexPartialSum_eq_LSeries
    criticalSourceCoeffBound_nonneg criticalSourceCoeff_cumulative_bound
    (show 0 < w.re by linarith) hw (criticalSourceCoeff_summable hw)
  rw [← hm]
  congr 1
  rw [criticalStepSourceMellin]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  change (1 : ℝ) < t at ht
  have ht0 : 0 ≤ t := le_of_lt (zero_lt_one.trans ht)
  have ht1 : 1 ≤ ⌊t⌋₊ :=
    (Nat.le_floor_iff ht0).mpr (by simpa using ht.le)
  dsimp only
  rw [criticalSourceCoeff_cumulative _ ht1]
  rw [show -w - 1 = -(w + 1) by ring]

/-- Exact Mellin transform of the critical Abel primitive in its initial
convergence half-plane. The source value is the nonflat current-gap integral. -/
theorem hasMellin_criticalSourceAbelPrimitive {s : ℂ} (hs : 3 / 2 < s.re) :
    HasMellin (squareRootSummatoryPrimitive criticalSourceCoeff) (-s)
      (criticalStepSourceMellin (s - 1 / 2) / (2 * s)) := by
  have hw : 1 < (s - 1 / 2).re := by
    simp only [sub_re]
    norm_num at hs ⊢
    linarith
  have htheta : (1 : ℝ) < s.re - 1 / 2 := by linarith
  have hm := hasMellin_squareRootSummatoryPrimitive
    criticalSourceCoeffBound_nonneg criticalSourceCoeff_cumulative_bound
    (show 1 / 2 < s.re by linarith) htheta
    (criticalSourceCoeff_summable hw)
  refine ⟨hm.1, hm.2.trans ?_⟩
  rw [criticalSourceCoeff_LSeries_eq_stepMellin hw]
  have hw0 : s - 1 / 2 ≠ 0 := ne_zero_of_re_pos (by linarith)
  have hs0 : s ≠ 0 := ne_zero_of_re_pos (by linarith)
  field_simp
  have hden : s * 2 - 1 ≠ 0 := by
    intro h
    apply hw0
    calc
      s - 1 / 2 = (s * 2 - 1) / 2 := by ring
      _ = 0 := by rw [h]; ring
  rw [mul_div_cancel_left₀ _ hden]

/-- The Mellin transform of the actual critical Abel primitive is nonzero
throughout a sufficiently small punctured right neighborhood of its
convergence boundary. This is the terminal-source consequence of the
centered current's finite analytic jet, not an RH-strength estimate. -/
theorem criticalSourceAbelPrimitive_mellin_eventually_ne_zero_right :
    ∀ᶠ w : ℂ in 𝓝 1, 1 < w.re →
      mellin (squareRootSummatoryPrimitive criticalSourceCoeff) (-(w + 1 / 2)) ≠ 0 := by
  filter_upwards [criticalStepSourceMellin_eventually_ne_zero_right] with w hA hw
  have hs : (3 / 2 : ℝ) < (w + 1 / 2).re := by
    simp only [add_re]
    norm_num at hw ⊢
    linarith
  have hm := (hasMellin_criticalSourceAbelPrimitive hs).2
  have hshift : w + 1 / 2 - 1 / 2 = w := by ring
  rw [hshift] at hm
  rw [hm]
  exact div_ne_zero (hA hw) (mul_ne_zero (by norm_num)
    (ne_zero_of_re_pos (by linarith)))

end RHTower
