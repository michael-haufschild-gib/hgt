import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailArchimedeanLimit
import GaloisForLFunctions.HTGeometry.DigammaGaussSeries
import GaloisForLFunctions.RHTower.SeamDivisionSourceSplit
import GaloisForLFunctions.RHTower.BurnolAlternatingHarmonic

/-!
# The archimedean Mellin value of a power tail

The regularized jet profile splits into a positive geometric series and
`1/(1+t)`. Integrating the series gives the difference of two Gauss
series, hence the logarithmic derivative of the real Gamma factor.
-/

noncomputable section

open Finset Filter Topology MeasureTheory

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

private def jetMellinTerm (a : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  2 * (t ^ (2 * (n : ℝ) - a) - t ^ (2 * (n : ℝ)))

private def jetMellinCoefficient (a : ℝ) (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + (1 - a) / 2) - 1 / ((n : ℝ) + 1 / 2)

private theorem hasSum_jetMellinCoefficient {a : ℝ} (ha1 : a < 1) :
    HasSum (fun n => (jetMellinCoefficient a n : ℂ))
      (Complex.digamma (1 / 2) - Complex.digamma ((1 - (a : ℂ)) / 2)) := by
  have hhalf : 0 < (1 / 2 : ℂ).re := by norm_num
  have hb : 0 < ((1 - (a : ℂ)) / 2).re := by
    simp only [Complex.div_ofNat_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re]
    linarith only [ha1]
  have hsum := (RHTower.summable_gaussDigammaSeriesTerm hhalf).hasSum.sub
    (RHTower.summable_gaussDigammaSeriesTerm hb).hasSum
  have hval : (∑' n, RHTower.gaussDigammaSeriesTerm (1 / 2) n) -
      (∑' n, RHTower.gaussDigammaSeriesTerm ((1 - (a : ℂ)) / 2) n) =
      Complex.digamma (1 / 2) - Complex.digamma ((1 - (a : ℂ)) / 2) := by
    rw [RHTower.digamma_eq_neg_euler_add_tsum_gauss hhalf,
      RHTower.digamma_eq_neg_euler_add_tsum_gauss hb]
    ring
  rw [hval] at hsum
  apply hsum.congr
  intro S
  apply sum_congr rfl
  intro n _
  simp only [jetMellinCoefficient, RHTower.gaussDigammaSeriesTerm]
  push_cast
  ring

private theorem integrableOn_jetMellinTerm {a : ℝ} (ha1 : a < 1) (n : ℕ) :
    IntegrableOn (jetMellinTerm a n) (Set.Ioo 0 1) := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hleft : IntervalIntegrable (fun t : ℝ => t ^ (2 * (n : ℝ) - a)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith only [ha1, hn])
  have hright : IntervalIntegrable (fun t : ℝ => t ^ (2 * (n : ℝ))) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith only [hn])
  exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
    ((hleft.sub hright).const_mul 2)).mono_set Set.Ioo_subset_Ioc_self

private theorem jetMellinTerm_nonneg {a t : ℝ} (ha : 0 < a)
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) (n : ℕ) : 0 ≤ jetMellinTerm a n t := by
  apply mul_nonneg (by norm_num)
  apply sub_nonneg.mpr
  exact Real.rpow_le_rpow_of_exponent_ge ht.1 ht.2.le (by linarith only [ha])

private theorem integral_jetMellinTerm {a : ℝ} (ha1 : a < 1) (n : ℕ) :
    (∫ t in Set.Ioo (0 : ℝ) 1, jetMellinTerm a n t) = jetMellinCoefficient a n := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hleft : -1 < 2 * (n : ℝ) - a := by linarith only [ha1, hn]
  have hright : -1 < 2 * (n : ℝ) := by linarith only [hn]
  have hi1 := (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
    (intervalIntegral.intervalIntegrable_rpow' hleft)
  have hi2 := (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
    (intervalIntegral.intervalIntegrable_rpow' hright)
  have hd3 : 2 * (n : ℝ) - a + 1 ≠ 0 := by linarith only [ha1, hn]
  have hd4 : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
  rw [← integral_Ioc_eq_integral_Ioo]
  simp only [jetMellinTerm]
  rw [integral_const_mul, integral_sub hi1 hi2,
    ← intervalIntegral.integral_of_le zero_le_one,
    ← intervalIntegral.integral_of_le zero_le_one,
    integral_rpow (Or.inl hleft), integral_rpow (Or.inl hright)]
  simp only [Real.one_rpow, Real.zero_rpow hd3, Real.zero_rpow hd4, sub_zero]
  dsimp only [jetMellinCoefficient]
  rw [show 2 * (n : ℝ) - a + 1 = 2 * ((n : ℝ) + (1 - a) / 2) by ring,
    show 2 * (n : ℝ) + 1 = 2 * ((n : ℝ) + 1 / 2) by ring]
  simp only [one_div, mul_inv_rev]
  ring

private theorem hasSum_jetMellinTerm {a t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HasSum (fun n => jetMellinTerm a n t) (2 * (t ^ (-a) - 1) / (1 - t ^ 2)) := by
  have hsmall : ‖t ^ 2‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)]
    nlinarith only [ht.1, ht.2]
  have hgeom := (hasSum_geometric_of_norm_lt_one hsmall).mul_left (2 * (t ^ (-a) - 1))
  rw [div_eq_mul_inv]
  apply hgeom.congr
  intro S
  apply sum_congr rfl
  intro n _
  have he : t ^ (2 * (n : ℝ) - a) = t ^ (-a) * (t ^ 2) ^ n := by
    rw [show 2 * (n : ℝ) - a = -a + ((2 * n : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_add ht.1, Real.rpow_natCast, pow_mul]
  have he' : t ^ (2 * (n : ℝ)) = (t ^ 2) ^ n := by
    rw [show 2 * (n : ℝ) = ((2 * n : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast, pow_mul]
  change 2 * (t ^ (-a) - 1) * (t ^ 2) ^ n =
    2 * (t ^ (2 * (n : ℝ) - a) - t ^ (2 * (n : ℝ)))
  rw [he, he']
  ring

private theorem integral_jetMellinSeries {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ((∫ t in Set.Ioo (0 : ℝ) 1, 2 * (t ^ (-a) - 1) / (1 - t ^ 2) : ℝ) : ℂ) =
      Complex.digamma (1 / 2) - Complex.digamma ((1 - (a : ℂ)) / 2) := by
  have hG := hasSum_jetMellinCoefficient ha1
  have hreal := Complex.reCLM.hasSum hG
  have hreal' : HasSum (jetMellinCoefficient a)
      (Complex.digamma (1 / 2) - Complex.digamma ((1 - (a : ℂ)) / 2)).re := by
    simpa only [Complex.reCLM_apply, Complex.ofReal_re] using hreal
  have hnorm (n : ℕ) :
      (∫ t in Set.Ioo (0 : ℝ) 1, ‖jetMellinTerm a n t‖) = jetMellinCoefficient a n := by
    rw [← integral_jetMellinTerm ha1 n]
    exact setIntegral_congr_fun measurableSet_Ioo fun t ht =>
      (Real.norm_eq_abs _).trans (abs_of_nonneg (jetMellinTerm_nonneg ha ht n))
  have hs := hasSum_integral_of_summable_integral_norm (integrableOn_jetMellinTerm ha1)
    (by simp only [hnorm]; exact hreal'.summable)
  simp only [integral_jetMellinTerm ha1] at hs
  have hval : (∫ t in Set.Ioo (0 : ℝ) 1, ∑' n, jetMellinTerm a n t) =
      ∫ t in Set.Ioo (0 : ℝ) 1, 2 * (t ^ (-a) - 1) / (1 - t ^ 2) :=
    setIntegral_congr_fun measurableSet_Ioo fun t ht => (hasSum_jetMellinTerm ht).tsum_eq
  rw [hval] at hs
  exact (Complex.ofRealCLM.hasSum hs).unique hG

/-- The Mellin integral of the regularized jet row is a digamma difference. -/
theorem ofReal_integral_powerTailJetProfile {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ((∫ t in (0 : ℝ)..1, powerTailJetProfile a t : ℝ) : ℂ) =
      -Complex.digamma ((1 - (a : ℂ)) / 2) - Real.eulerMascheroniConstant -
        (Real.log 2 : ℂ) := by
  have hi := intervalIntegrable_of_powerTailBound ha1 (continuousOn_powerTailJetProfile a)
    (fun t ht => abs_powerTailJetProfile_le ha ha1 ht)
  have hjet := (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hi
  have hr : IntegrableOn (fun t : ℝ => 1 / (1 + t)) (Set.Ioc 0 1) := by
    have hc : ContinuousOn (fun t : ℝ => 1 / (1 + t)) (Set.Icc 0 1) := by
      intro t ht
      exact (continuousAt_const.div (continuousAt_const.add continuousAt_id)
        (show (1 : ℝ) + t ≠ 0 by linarith only [ht.1])).continuousWithinAt
    exact hc.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have he (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
      powerTailJetProfile a t - 1 / (1 + t) = 2 * (t ^ (-a) - 1) / (1 - t ^ 2) := by
    rw [powerTailJetProfile, if_neg ht.2.ne]
    have h1 : 1 - t ≠ 0 := by linarith only [ht.2]
    have h2 : 1 + t ≠ 0 := by linarith only [ht.1]
    have h3 : 1 - t ^ 2 ≠ 0 := by nlinarith only [ht.1, ht.2]
    field_simp [h1, h2, h3]
    ring
  have hdiff : (∫ t in (0 : ℝ)..1, powerTailJetProfile a t) - Real.log 2 =
      ∫ t in Set.Ioo (0 : ℝ) 1, 2 * (t ^ (-a) - 1) / (1 - t ^ 2) := by
    rw [← _root_.RHTower.integral_one_div_one_add, intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_of_le zero_le_one, ← integral_sub hjet hr,
      integral_Ioc_eq_integral_Ioo]
    exact setIntegral_congr_fun measurableSet_Ioo he
  have hclosed := integral_jetMellinSeries ha ha1
  rw [← hdiff] at hclosed
  push_cast at hclosed
  rw [SeamSplit.digamma_half, ← Complex.ofReal_ofNat, ← Complex.ofReal_log (by norm_num)] at hclosed
  norm_num only [Complex.ofReal_ofNat] at hclosed
  linear_combination hclosed

/-- The archimedean row equals twice the logarithmic derivative of `GammaR`. -/
theorem ofReal_powerTailArchimedeanRowLimit {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    (powerTailArchimedeanRowLimit a : ℂ) =
      Complex.digamma ((1 - (a : ℂ)) / 2) - (Real.log Real.pi : ℂ) := by
  rw [powerTailArchimedeanRowLimit]
  push_cast
  rw [ofReal_integral_powerTailJetProfile ha ha1,
    Real.log_mul (by norm_num) Real.pi_pos.ne']
  push_cast
  ring

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
