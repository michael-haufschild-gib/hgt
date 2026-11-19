import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.ZeroCrowdingForcesDecayOfTheConfinedTrace
import GaloisForLFunctions.HTGeometry.HardyLineIsometry
import GaloisForLFunctions.RHTower.XiThetaSquareRateBoundary

/-!
# The mean-square wall trace in a finite off-line layer

Critical-line crowding forces the mean-square wall trace to vanish at every
crossing. Plancherel turns uniform decay on the half-plane into a bound for
the exponentially weighted square mass adjacent to the wall.
-/

noncomputable section
open MeasureTheory Complex Filter Set Metric Zeta23
open scoped Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

private def dampedMass (F : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ v in Ioi (0:ℝ), Real.exp (-(2*x*v))*(F (-v))^2

private theorem damped_nonneg (F : ℝ → ℝ) (x : ℝ) : 0 ≤ dampedMass F x :=
  integral_nonneg fun _ => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)

private theorem line_mass_eq {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {x : ℝ}
    (hx : 0 < x) :
    (∫ y : ℝ, ‖negativeHalfLineLaplace (cx F) (hardyVerticalLine x y)‖^2) =
      2*Real.pi*dampedMass F x := by
  have hi : Integrable (cx F) := hF.integrable.ofReal
  have h2 : MemLp (cx F) 2 volume :=
    (memLp_two_iff_integrable_sq_norm hi.aestronglyMeasurable).mpr
      (by simpa only [cx,Complex.norm_real,Real.norm_eq_abs,sq_abs] using hF.sq)
  have hs (u : ℝ) (hu : 0 ≤ u) : cx F u = 0 := by simp [cx,hF.support u hu]
  simp_rw [negativeHalfLineLaplace_eq_laplaceRay_reflect _ hs]
  simpa only [cx,Complex.norm_real,Real.norm_eq_abs,sq_abs,dampedMass] using
    integral_norm_sq_laplaceRay_vertical (memLp_reflected_negativeProfile h2) hx

/-- Arclength on a far-right vertical line sees a Cauchy majorant with
total mass pi/x. Both coordinates must be controlled uniformly. -/
private theorem dampedMass_gain {R : ℝ} (hr : 0 < R) {F : ℝ → ℝ}
    (hF : IsConfinedNullVector R F) (hf : BacklundConverse.FiniteOffLine)
    {η : ℝ} (hη : 0 < η) : ∀ᶠ x : ℝ in atTop, x*dampedMass F x ≤ η^2 := by
  obtain ⟨T,hT,hb⟩ := hF.interior_half_plane_laplace_little_o hr hf (by norm_num : (-4:ℝ)<0) hη
  filter_upwards [eventually_ge_atTop T] with x hx
  have hx0 : 0 < x := hT.trans_le hx
  have hk := integral_inv_sq_add_sq_univ hx0
  have hki : Integrable (fun y : ℝ => (x^2+y^2)⁻¹) :=
    Integrable.of_integral_ne_zero (by rw [hk]; positivity)
  have hpt (y : ℝ) : ‖negativeHalfLineLaplace (cx F) (hardyVerticalLine x y)‖^2 ≤
      η^2*(x^2+y^2)⁻¹ := by
    let w := hardyVerticalLine x y
    have hre : w.re = x := hardyVerticalLine_re _ _
    have hw : x ≤ ‖w‖ := by simpa only [hre] using (le_abs_self w.re).trans (Complex.abs_re_le_norm w)
    have h := pow_le_pow_left₀ (norm_nonneg _) (hb w (hre.symm ▸ hx0.le) (hx.trans hw)) 2
    rw [norm_mul,mul_pow] at h
    have he : ‖w+5‖^2 = (x+5)^2+y^2 := by
      rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
      simp [w,hardyVerticalLine]; ring
    have hd : x^2+y^2 ≤ ‖w+5‖^2 := by rw [he]; linarith only [hx0]
    rw [← div_eq_mul_inv,le_div_iff₀ (by positivity)]
    rw [mul_comm]
    exact (mul_le_mul_of_nonneg_right hd (sq_nonneg _)).trans h
  have hint := integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _)
    (hki.const_mul (η^2)) (Eventually.of_forall hpt)
  rw [line_mass_eq hF.1 hx0,integral_const_mul,hk,← mul_div_assoc,le_div_iff₀ hx0] at hint
  have hmass : 0 ≤ x*dampedMass F x := mul_nonneg hx0.le (damped_nonneg _ _)
  apply le_of_mul_le_mul_left (a := Real.pi) _ Real.pi_pos
  nlinarith only [hint,mul_nonneg Real.pi_pos.le hmass]

/-- The terminal squared mass after exponential damping has zero Abel mean
at every crossing with finitely many off-line zeros. -/
theorem IsConfinedNullVector.abel_square_wall_limit {R : ℝ} (hr : 0 < R) {F : ℝ → ℝ}
    (hF : IsConfinedNullVector R F) (hf : BacklundConverse.FiniteOffLine) :
    Tendsto (fun x : ℝ => x * ∫ v in Ioi (0:ℝ), Real.exp (-(2*x*v))*(F (-v))^2)
      atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η := min (ε/2) 1
  have hη : 0 < η := lt_min (half_pos hε) zero_lt_one
  filter_upwards [dampedMass_gain hr hF hf hη,eventually_ge_atTop (0:ℝ)] with x hx hx0
  change dist (x*dampedMass F x) 0 < ε
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (mul_nonneg hx0 (damped_nonneg _ _))]
  have he : η^2 ≤ η := by rw [sq]; exact mul_le_of_le_one_right hη.le (min_le_right _ _)
  exact hx.trans_lt (he.trans_lt ((min_le_left _ _).trans_lt (half_lt_self hε)))

private theorem terminal_le_damped {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {h : ℝ}
    (hh : 0 < h) : (∫ u in Ioo (-h) 0, F u^2) ≤ Real.exp 2*dampedMass F h⁻¹ := by
  let f := fun v : ℝ => F (-v)^2
  let g := fun v : ℝ => Real.exp (-(2*h⁻¹*v))*f v
  have hi : Integrable f := (Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp_of_integrable hF.sq
  have hgi : IntegrableOn g (Ioi 0) := by
    apply hi.integrableOn.mono' (by
      exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).aestronglyMeasurable.mul
        hi.aestronglyMeasurable.restrict) : AEStronglyMeasurable g (volume.restrict (Ioi 0)))
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with v hv
    have hv' : 0 ≤ v := le_of_lt hv
    change ‖Real.exp (-(2*h⁻¹*v))*f v‖ ≤ f v
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
    have hneg : -(2*h⁻¹*v) ≤ 0 := neg_nonpos.mpr
      (mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr hh.le)) hv')
    exact mul_le_of_le_one_left (sq_nonneg _) (Real.exp_le_one_iff.mpr hneg)
  have hsub : Ioo (0:ℝ) h ⊆ Ioi 0 := fun _ hv => hv.1
  have hlo : Real.exp (-2)*(∫ v in Ioo (0:ℝ) h, f v) ≤ dampedMass F h⁻¹ := by
    rw [← integral_const_mul]
    calc _ ≤ ∫ v in Ioo (0:ℝ) h, g v := by
              apply integral_mono_of_nonneg (Eventually.of_forall fun v => mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
                (hgi.mono_set hsub)
              filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioo] with v hv
              apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
              apply Real.exp_le_exp.mpr
              have hvh := mul_le_mul_of_nonneg_left hv.2.le (inv_nonneg.mpr hh.le)
              rw [inv_mul_cancel₀ hh.ne'] at hvh
              linarith only [hvh]
         _ ≤ _ := setIntegral_mono_set hgi (Eventually.of_forall fun v => mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
            (Eventually.of_forall hsub)
  rw [← integral_reflect_initial_interval (fun u => F u^2) h]
  have hmul := mul_le_mul_of_nonneg_left hlo (Real.exp_pos 2).le
  rw [← mul_assoc,← Real.exp_add,add_neg_cancel,Real.exp_zero,one_mul] at hmul
  exact hmul

/-- The average of the squared profile next to the wall tends to zero at every
positive-ratio crossing of a finite off-line layer. -/
theorem IsConfinedNullVector.mean_square_wall_trace_zero {R : ℝ} (hr : 0 < R) {F : ℝ → ℝ}
    (hF : IsConfinedNullVector R F) (hf : BacklundConverse.FiniteOffLine) :
    Tendsto (fun h : ℝ => (∫ u in Ioo (-h) 0, F u^2)/h) (𝓝[>] 0) (𝓝 0) := by
  have hlim := ((hF.abel_square_wall_limit hr hf).comp tendsto_inv_nhdsGT_zero).const_mul (Real.exp 2)
  rw [mul_zero] at hlim
  apply squeeze_zero' _ _ hlim
  · filter_upwards [self_mem_nhdsWithin] with h hh
    exact div_nonneg (integral_nonneg fun _ => sq_nonneg _) (le_of_lt hh)
  · filter_upwards [self_mem_nhdsWithin] with h hh
    have hpos : 0 < h := hh
    have h := mul_le_mul_of_nonneg_left (terminal_le_damped hF.1 hpos) (inv_nonneg.mpr hpos.le)
    simpa only [Function.comp_apply,div_eq_inv_mul,mul_left_comm,dampedMass] using h

#print axioms IsConfinedNullVector.abel_square_wall_limit
#print axioms IsConfinedNullVector.mean_square_wall_trace_zero
end GaloisForLFunctions.ExclusionOfTheCriticalState
