import GaloisForLFunctions.SelbergClass.OrdinaryMellinContourShift

/-!
# Entire Taylor remainder below degree one

Convergence of the contour-generated partial sums at every positive real point
implies absolute convergence at every complex point. The Taylor series therefore
defines an entire function, with the only polar contribution kept separate.
-/

noncomputable section
open Complex Filter Topology Set MeasureTheory
open GaloisForLFunctions.HTGeometry RHTower

namespace GaloisForLFunctions.SelbergClass

theorem summable_ordinaryTaylor (F : ExtendedSelbergClass)
    (hd0 : 0 < F.gammaData.degree) (hd1 : F.gammaData.degree < 1) (z : ℂ) :
    Summable (fun k : ℕ => ordinaryTaylorCoeff F k * z ^ k) := by
  have hx : 0 < ‖z‖ + 1 := by positivity
  apply summable_powerSeries_of_norm_lt
    (tendsto_ordinaryTaylor_partialSum F hd0 hd1 hx).cauchySeq
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
  exact lt_add_one ‖z‖

/-- The ordinary Taylor series has infinite radius below degree one. -/
theorem radius_ordinaryTaylor (F : ExtendedSelbergClass)
    (hd0 : 0 < F.gammaData.degree) (hd1 : F.gammaData.degree < 1) :
    (FormalMultilinearSeries.ofScalars ℂ (ordinaryTaylorCoeff F)).radius = ⊤ := by
  apply FormalMultilinearSeries.radius_eq_top_of_summable_norm
  intro r
  have hs := (summable_ordinaryTaylor F hd0 hd1 (r : ℂ)).norm
  simpa only [FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg r.coe_nonneg] using hs

/-- Entire remainder in the ordinary exponential expansion. -/
def ordinaryTaylorFunction (F : ExtendedSelbergClass) : ℂ → ℂ :=
  (FormalMultilinearSeries.ofScalars ℂ (ordinaryTaylorCoeff F)).sum

theorem ordinaryTaylorFunction_eq_tsum (F : ExtendedSelbergClass) (z : ℂ) :
    ordinaryTaylorFunction F z = ∑' k : ℕ, ordinaryTaylorCoeff F k * z ^ k := by
  rw [ordinaryTaylorFunction, FormalMultilinearSeries.sum]
  exact tsum_congr fun k => by rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]

theorem analyticOnNhd_ordinaryTaylorFunction (F : ExtendedSelbergClass)
    (hd0 : 0 < F.gammaData.degree) (hd1 : F.gammaData.degree < 1) :
    AnalyticOnNhd ℂ (ordinaryTaylorFunction F) univ := by
  have hrad := radius_ordinaryTaylor F hd0 hd1
  have hp := (FormalMultilinearSeries.ofScalars ℂ (ordinaryTaylorCoeff F)).hasFPowerSeriesOnBall
    (by rw [hrad]; exact ENNReal.zero_lt_top)
  intro z _
  exact hp.analyticOnNhd z (by simp [hrad])

/-- On the positive axis the entire remainder is the Mellin integral minus its
polar contribution. -/
theorem ordinaryTaylorFunction_eq_mellin_sub_polar (F : ExtendedSelbergClass)
    (hd0 : 0 < F.gammaData.degree) (hd1 : F.gammaData.degree < 1)
    {x : ℝ} (hx : 0 < x) :
    ordinaryTaylorFunction F (x : ℂ) =
      (∫ t : ℝ, ordinaryMellinIntegrand F 0 (x : ℂ) (2 + (t : ℂ) * I)) /
        (2 * (Real.pi : ℂ)) - ordinaryPolarPart F (x : ℂ) := by
  rw [ordinaryTaylorFunction_eq_tsum]
  exact tendsto_nhds_unique (summable_ordinaryTaylor F hd0 hd1 (x : ℂ)).hasSum.tendsto_sum_nat
    (tendsto_ordinaryTaylor_partialSum F hd0 hd1 hx)

end GaloisForLFunctions.SelbergClass
