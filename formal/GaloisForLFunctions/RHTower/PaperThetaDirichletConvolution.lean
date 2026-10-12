import GaloisForLFunctions.RHTower.PaperThetaDiniDensity

/-! # The paper's literal Dirichlet convolution on the full theta L¹ domain -/

noncomputable section

open MeasureTheory Set Filter Topology

namespace RHTower.PaperThetaEndpoint

open GaloisForLFunctions.HTGeometry FourierLLogL

private theorem centered_phase_integrable (z : L1Point) (t u : ℝ) :
    IntegrableOn (fun y => periodicMode z.val (t-y) * Period.phase u y) Period.centerWin := by
  apply (integrable_centered_periodicMode z t).norm.mono'
    (((measurable_periodicMode z.val).comp (measurable_const.sub measurable_id)).mul
      (Period.phase_cont u).measurable).aestronglyMeasurable
  exact Eventually.of_forall fun y => by
    change ‖periodicMode z.val (t-y) * Period.phase u y‖ ≤ _
    rw [norm_mul, Period.phase_unimod, mul_one]

private theorem unit_phase_integral (n : ℤ) :
    (∫ y, Period.phase n y ∂Period.μ₁) = if n = 0 then 1 else 0 := by
  have hc : (∫ y, Period.phase n y ∂Period.μ₁) =
      fourierCoeff (fun _ : Torus => (1 : ℂ)) (-n) := by
    rw [fourierCoeff_eq_integral, ← Period.map_circle_volume]
    rw [integral_map (f := fun x : Torus => (1 : ℂ) * fourier (- -n) x)
      Period.measurable_circle.aemeasurable (by fun_prop)]
    simp only [one_mul, neg_neg, Period.fourier_circle]
  rw [hc]
  have he : (fun _ : Torus => (1 : ℂ)) = fourier (0 : ℤ) := by
    funext x
    exact fourier_zero.symm
  rw [he, fourierCoeff_fourier]
  by_cases hn : n = 0 <;> simp [hn]

private theorem centered_phase_integral (n : ℤ) :
    (∫ y in Period.centerWin, Period.phase n y) = if n = 0 then 1 else 0 := by
  have h := Period.seg_period_unit (Period.phase n) (Period.phase_periodic n) (-1/2)
  rw [unit_phase_integral] at h
  convert h using 1; norm_num [Period.centerWin]

theorem integral_centered_dirichlet (N : ℕ) :
    (∫ y in Period.centerWin, Period.dirichlet N y) = 1 := by
  unfold Period.dirichlet
  rw [integral_finsetSum]
  · simp_rw [centered_phase_integral]
    simp
  · intro n _
    exact Period.seg_integrable _ (Period.phase_cont n).measurable 1 _ _
      (fun y _ => (Period.phase_unimod n y).le)

theorem sumReal_centered_L1 (z : L1Point) (N : ℕ) (t : ℝ) :
    Period.sumReal (periodicMode z.val) N t =
      ∫ y in Period.centerWin, periodicMode z.val (t-y) * Period.dirichlet N y := by
  have hterm (n : ℤ) :
      (∫ y, periodicMode z.val y * Period.phase (-n : ℤ) y ∂Period.μ₁) * Period.phase n t =
        ∫ y in Period.centerWin, periodicMode z.val (t-y) * Period.phase n y := by
    let p (y : ℝ) := periodicMode z.val y * Period.phase (-n : ℤ) y * Period.phase n t
    have hp : Function.Periodic p 1 := by
      intro y
      dsimp only [p]
      rw [periodic_periodicMode z.val y, Period.phase_periodic (-n) y]
    have he (y : ℝ) : p (t-y) = periodicMode z.val (t-y) * Period.phase n y := by
      dsimp only [p]
      push_cast
      rw [mul_assoc, mul_comm (Period.phase _ _), ← Period.phase_sub]
      congr 2
      ring
    rw [← integral_mul_const]
    change (∫ y, p y ∂Period.μ₁) = _
    simp_rw [← he]
    have h := Period.seg_translate_scale_rev p t (by norm_num : (-1/2 : ℝ) ≤ 1/2)
      (by norm_num : (0 : ℝ) < 1)
    simp only [one_mul, inv_one, one_smul] at h
    rw [show t-(-1/2 : ℝ) = (t-1/2)+1 by ring, Period.seg_period_unit p hp] at h
    simpa only [Period.centerWin, neg_div] using h.symm
  unfold Period.sumReal
  simp_rw [hterm, Period.dirichlet, Finset.mul_sum]
  rw [integral_finsetSum]
  exact fun n _ => centered_phase_integrable z t n

theorem symmetricPartialSum_centered_L1 (z : L1Point) (N : ℕ) (t : ℝ) :
    symmetricPartialSum (circleMode z.val) N (Period.circle t) =
      ∫ y in Period.centerWin, periodicMode z.val (t-y) * Period.dirichlet N y := by
  rw [Period.sum_eq _ (measurable_circleMode_all z.val)]
  exact sumReal_centered_L1 z N t

private theorem centered_dirichlet_integrable (N : ℕ) :
    IntegrableOn (Period.dirichlet N) Period.centerWin :=
  Period.seg_integrable _ (Period.dirichlet_cont N).measurable (2*(N : ℝ)+1) _ _
    (fun y _ => Period.dirichlet_bound N y)

private theorem centered_product_integrable (z : L1Point) (N : ℕ) (t : ℝ) :
    IntegrableOn (fun y => periodicMode z.val (t-y) * Period.dirichlet N y) Period.centerWin := by
  apply ((integrable_centered_periodicMode z t).norm.const_mul (2*(N : ℝ)+1)).mono'
    (((measurable_periodicMode z.val).comp (measurable_const.sub measurable_id)).mul
      (Period.dirichlet_cont N).measurable).aestronglyMeasurable
  filter_upwards [] with y
  change ‖periodicMode z.val (t-y) * Period.dirichlet N y‖ ≤ _
  rw [norm_mul]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (Period.dirichlet_bound N y)
    (norm_nonneg (periodicMode z.val (t-y)))

/-- The entire Fourier error is the oscillatory integral of the paid local quotient. -/
theorem symmetric_error_eq_dini_integral (z : L1Point) (t : Ioo (0 : ℝ) 1) (N : ℕ) :
    symmetricPartialSum (circleMode z.val) N (Period.circle t.val) - flatModePullback z.val t.val =
      ∫ y in Period.centerWin,
        diniDifference z.val t.val y * (Real.sin (Period.ang N y + Real.pi*y) : ℂ) := by
  rw [symmetricPartialSum_centered_L1, ← periodicMode_eq_pullback z.val t]
  have he : (∫ y in Period.centerWin,
      (periodicMode z.val (t.val-y) - periodicMode z.val t.val) * Period.dirichlet N y) =
      (∫ y in Period.centerWin, periodicMode z.val (t.val-y) * Period.dirichlet N y) -
        periodicMode z.val t.val := by
    simp_rw [sub_mul]
    rw [integral_sub (centered_product_integrable z N t.val)
      ((centered_dirichlet_integrable N).const_mul _), integral_const_mul,
      integral_centered_dirichlet, mul_one]
  rw [← he]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ico] with y hy
  exact diniDifference_dirichlet z.val t.val N ⟨y, hy⟩

end RHTower.PaperThetaEndpoint
