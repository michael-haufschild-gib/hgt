import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNonstationaryWeight

/-! Original subtracted nonstationary moments and a frequency-uniform remainder bound. -/
namespace RHTower.D4BMJointSource
open Complex Set Filter Topology MeasureTheory D4BMLaplaceRadial GaloisForLFunctions.HTGeometry
open scoped Polynomial
noncomputable section
set_option autoImplicit false

def nonstationaryCore (P : ℂ[X]) (j : ℕ) (w : ℂ) (x : ℝ) : ℂ :=
  power (-4*w) (2-x)*nonstationaryWeight P j x

def nonstationaryCoreFirst (P : ℂ[X]) (j : ℕ) (w : ℂ) (x : ℝ) : ℂ :=
  -powerFirst (-4*w) (2-x)*nonstationaryWeight P j x+
    power (-4*w) (2-x)*nonstationaryWeightFirst P j x

def nonstationaryMoment (P : ℂ[X]) (j : ℕ) (w : ℂ) : ℂ :=
  firstEndpointMellin (fun _ => nonstationaryCore P j w) 1 w

theorem nonstationaryCore_hasDerivAt (P : ℂ[X]) (j : ℕ) (w : ℂ) {x : ℝ}
    (hx : x ∈ Ioo (-(1/2):ℝ) 2) :
    HasDerivAt (nonstationaryCore P j w) (nonstationaryCoreFirst P j w x) x := by
  have hp : HasDerivAt (fun y : ℝ => power (-4*w) (2-y)) (-powerFirst (-4*w) (2-x)) x := by
    simpa only [zero_sub,neg_one_smul,Function.comp_apply,Pi.sub_apply,id_eq] using!
      (power_derivatives (-4*w) (by linarith [hx.2] : 0 < 2-x)).1.scomp x
        ((hasDerivAt_const x (2:ℝ)).sub (hasDerivAt_id x))
  exact hp.mul (nonstationaryWeight_hasDerivAt P j hx)

theorem nonstationaryCoreFirst_continuousAt (P : ℂ[X]) (j : ℕ) (w : ℂ) {x : ℝ}
    (hx : x ∈ Ioo (-(1/2):ℝ) 2) : ContinuousAt (nonstationaryCoreFirst P j w) x := by
  have hp := (power_derivatives (-4*w) (by linarith [hx.2] : 0 < 2-x)).1.continuousAt.comp
    (continuousAt_const.sub continuousAt_id)
  have hdp := (power_derivatives (-4*w) (by linarith [hx.2] : 0 < 2-x)).2.continuousAt.comp
    (continuousAt_const.sub continuousAt_id)
  exact (hdp.neg.mul (nonstationaryWeight_hasDerivAt P j hx).continuousAt).add
    (hp.mul (nonstationaryWeightFirst_continuousAt P j hx))

theorem nonstationaryCore_first_bound (P : ℂ[X]) (j : ℕ) (w : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Ioc (0:ℝ) 1,
      ‖nonstationaryCore P j w x-nonstationaryCore P j w 0‖ ≤ C*x := by
  have hc : ContinuousOn (nonstationaryCoreFirst P j w) (Icc (0:ℝ) 1) := by
    intro x hx
    exact (nonstationaryCoreFirst_continuousAt P j w
      (by constructor <;> linarith [hx.1,hx.2])).continuousWithinAt
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro x hx
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := nonstationaryCore P j w) (f' := nonstationaryCoreFirst P j w) (s := Icc (0:ℝ) 1)
    (fun y hy => (nonstationaryCore_hasDerivAt P j w
      (by constructor <;> linarith [hy.1,hy.2])).hasDerivWithinAt)
    (fun y hy => (hC y hy).trans (le_max_left C 0)) (convex_Icc (0:ℝ) 1)
    (by constructor <;> norm_num : (0:ℝ) ∈ Icc (0:ℝ) 1) ⟨hx.1.le,hx.2⟩
  simpa only [sub_zero,Real.norm_eq_abs,abs_of_nonneg hx.1.le] using h

theorem nonstationaryMoment_cutoff (P : ℂ[X]) (j : ℕ) (w : ℂ)
    (hw : -2 < w.re) (hw1 : w+1 ≠ 0) :
    Tendsto (fun e : ℝ => (∫ x in e..1, (x:ℂ)^w*nonstationaryCore P j w x)+
      nonstationaryCore P j w 0*(e:ℂ)^(w+1)/(w+1))
      (𝓝[>] (0:ℝ)) (𝓝 (nonstationaryMoment P j w)) := by
  obtain ⟨C,_,hC⟩ := nonstationaryCore_first_bound P j w
  have hm : Measurable (nonstationaryCore P j w) := by
    unfold nonstationaryCore nonstationaryWeight power
    fun_prop
  have hi := firstEndpointMellinRemainder_integrable (F := fun _ => nonstationaryCore P j w)
    (by norm_num : (0:ℝ)≤1) hw hm hC
  exact firstEndpointMellin_cutoff_of_integrable _ w hw1
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ)≤1)).mpr hi)

/-- Uniform absolute control of the actual nonstationary phase after one endpoint zero. -/
theorem nonstationaryKernel_bound (w : ℂ) (hw : w.re ∈ Icc (-(3/2):ℝ) (-1))
    {x : ℝ} (hx : x ∈ Ioc (0:ℝ) 1) :
    ‖(x:ℂ)^w*power (-4*w) (2-x)‖*x ≤ 64*x^(-(1/2):ℝ) := by
  have hp : 0 < 2-x := by linarith [hx.2]
  have hreal : (-4*w).re = -4*w.re := by simp
  have hbig : (2-x)^(-4*w.re) ≤ (64:ℝ) := by
    calc
      _ ≤ (2-x)^(6:ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith [hx.2]) (by linarith [hw.1])
      _ ≤ (2:ℝ)^(6:ℝ) := Real.rpow_le_rpow hp.le (by linarith [hx.1]) (by norm_num)
      _ = _ := by norm_num [← Real.rpow_natCast]
  have hsmall : x^(w.re+1) ≤ x^(-(1/2):ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2 (by linarith [hw.1])
  calc
    _ = x^(w.re+1)*(2-x)^(-4*w.re) := by
      rw [norm_mul,power,Complex.norm_cpow_eq_rpow_re_of_pos hx.1,
        Complex.norm_cpow_eq_rpow_re_of_pos hp,hreal,Real.rpow_add hx.1,Real.rpow_one]
      ring
    _ ≤ x^(-(1/2):ℝ)*64 := mul_le_mul hsmall hbig
      (Real.rpow_nonneg hp.le _) (Real.rpow_nonneg hx.1.le _)
    _ = _ := by ring

/-- Every algebraically generated remainder has one uniform bound across the physical strip. -/
theorem nonstationaryMoment_step_uniform_bound (P : ℂ[X]) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, w.re ∈ Icc (-(3/2):ℝ) (-1) →
      IntegrableOn (fun x : ℝ => (x:ℂ)^w*nonstationaryCore (nonstationaryWeightStep P j) (j+2) w x)
        (Ioc (0:ℝ) 1) ∧ ‖nonstationaryMoment (nonstationaryWeightStep P j) (j+2) w‖ ≤ C := by
  obtain ⟨C,hC0,hC⟩ := nonstationaryWeight_step_bound P j
  let bound : ℝ → ℝ := fun x => 64*C*x^(-(1/2):ℝ)
  have hbi : IntegrableOn bound (Ioc (0:ℝ) 1) := by
    exact (((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ)≤1)).mp
      (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1:ℝ)< -(1/2)))).const_mul (64*C))
  refine ⟨max (∫ x in Ioc (0:ℝ) 1, bound x) 0,le_max_right _ _,?_⟩
  intro w hw
  have hb (x : ℝ) (hx : x ∈ Ioc (0:ℝ) 1) :
      ‖(x:ℂ)^w*nonstationaryCore (nonstationaryWeightStep P j) (j+2) w x‖ ≤ bound x := by
    calc
      _ = ‖(x:ℂ)^w*power (-4*w) (2-x)‖*‖nonstationaryWeight (nonstationaryWeightStep P j) (j+2) x‖ := by
        rw [nonstationaryCore,← mul_assoc,norm_mul]
      _ ≤ ‖(x:ℂ)^w*power (-4*w) (2-x)‖*(C*x) := mul_le_mul_of_nonneg_left (hC x hx) (norm_nonneg _)
      _ = C*(‖(x:ℂ)^w*power (-4*w) (2-x)‖*x) := by ring
      _ ≤ C*(64*x^(-(1/2):ℝ)) := mul_le_mul_of_nonneg_left (nonstationaryKernel_bound w hw hx) hC0
      _ = bound x := by dsimp only [bound]; ring
  have hi : IntegrableOn (fun x : ℝ => (x:ℂ)^w*nonstationaryCore (nonstationaryWeightStep P j) (j+2) w x)
      (Ioc (0:ℝ) 1) := by
    apply hbi.mono'
    · have hm : Measurable (fun x : ℝ => (x:ℂ)^w*
          nonstationaryCore (nonstationaryWeightStep P j) (j+2) w x) := by
        unfold nonstationaryCore nonstationaryWeight power
        fun_prop
      exact hm.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact hb x hx
  refine ⟨hi,?_⟩
  have hz : nonstationaryCore (nonstationaryWeightStep P j) (j+2) w 0=0 := by
    simp only [nonstationaryCore,nonstationaryWeight,Complex.ofReal_zero,nonstationaryWeightStep_zero,zero_div,mul_zero]
  have he : nonstationaryMoment (nonstationaryWeightStep P j) (j+2) w =
      ∫ x in Ioc (0:ℝ) 1, (x:ℂ)^w*nonstationaryCore (nonstationaryWeightStep P j) (j+2) w x := by
    simp only [nonstationaryMoment,firstEndpointMellin,hz,zero_mul,zero_div,zero_add,
      firstEndpointMellinRemainder,sub_zero]
  rw [he]
  apply (norm_integral_le_integral_norm _).trans
  apply (integral_mono_ae hi.norm hbi ?_).trans (le_max_left _ _)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact hb x hx

end
end RHTower.D4BMJointSource
