import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeJointEnergy

/-! Removal of the Dirichlet endpoint cutoff for the actual native angular family.
The zero trace and a uniform weighted cutoff derivative bound control the full
radial product-rule error in the original angular L² space. -/
open MeasureTheory Set Filter Topology
open scoped ContDiff
namespace RHTower.D4BMNativeResponse
open D4BMJointWave
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Smooth interior cutoff with an endpoint margin tending to zero. -/
def nativeDirichletCutoff (n : ℕ) (x : ℝ) : ℝ :=
  1-scaledCuspCutoff (1/((n:ℝ)+1)) (-x)

private theorem width_pos (n : ℕ) : (0:ℝ) < 1/((n:ℝ)+1) := by positivity

private theorem width_le_one (n : ℕ) : (1:ℝ)/((n:ℝ)+1) ≤ 1 := by
  rw [div_le_one (by positivity : (0:ℝ) < (n:ℝ)+1)]
  have hn : (0:ℝ) ≤ n := by positivity
  linarith

/-- Every member is smooth, lies between zero and one, vanishes in an endpoint
neighborhood, and equals one below its transition interval. -/
theorem nativeDirichletCutoff_profile (n : ℕ) :
    ContDiff ℝ ∞ (nativeDirichletCutoff n) ∧
    (∀ x, 0 ≤ nativeDirichletCutoff n x ∧ nativeDirichletCutoff n x ≤ 1) ∧
    (∀ x, -2*(1/((n:ℝ)+1)) ≤ x → nativeDirichletCutoff n x = 0) ∧
    (∀ x, x ≤ -3*(1/((n:ℝ)+1)) → nativeDirichletCutoff n x = 1) := by
  refine ⟨contDiff_const.sub ((scaledCuspCutoff_smooth _).comp contDiff_id.neg),?_,?_,?_⟩
  · intro x
    have h := baseCuspCutoff_bounds (-x/(1/((n:ℝ)+1)))
    change 0 ≤ 1-baseCuspCutoff _ ∧ 1-baseCuspCutoff _ ≤ 1
    constructor <;> linarith
  · intro x hx
    rw [nativeDirichletCutoff,scaledCuspCutoff_low _ _ (width_pos n) (by linarith),sub_self]
  · intro x hx
    rw [nativeDirichletCutoff,scaledCuspCutoff_high _ _ (width_pos n) (by linarith),sub_zero]

private theorem cutoff_deriv (n : ℕ) (x : ℝ) :
    deriv (nativeDirichletCutoff n) x = deriv (scaledCuspCutoff (1/((n:ℝ)+1))) (-x) := by
  have hs := ((scaledCuspCutoff_smooth (1/((n:ℝ)+1))).differentiable (by simp)).differentiableAt.hasDerivAt
    (x := -x)
  have h := (hasDerivAt_const x (1:ℝ)).sub (hs.comp x (hasDerivAt_id x).neg)
  have he : ((fun _ : ℝ => (1:ℝ)) - scaledCuspCutoff (1/((n:ℝ)+1)) ∘ Neg.neg) =
      (fun y => 1-scaledCuspCutoff (1/((n:ℝ)+1)) (-y)) := by
    funext y
    rfl
  rw [he] at h
  change deriv (fun y => 1-scaledCuspCutoff (1/((n:ℝ)+1)) (-y)) x = _
  simpa only [Function.comp_def,id_eq,mul_neg,mul_one,zero_sub,neg_neg] using h.deriv

/-- The exact weighted derivative stays bounded as the endpoint margin shrinks. -/
theorem nativeDirichletCutoff_weighted_derivative_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (x : ℝ), |x*deriv (nativeDirichletCutoff n) x| ≤ C := by
  obtain ⟨C,hC,h⟩ := scaledCuspCutoff_derivative_bounds
  refine ⟨C,hC,fun n x => ?_⟩
  rw [cutoff_deriv]
  simpa only [neg_mul,abs_neg] using (h (1/((n:ℝ)+1)) (-x)).1

private theorem cutoff_germ_one (n : ℕ) (x : ℝ)
    (hx : x < -3*(1/((n:ℝ)+1))) :
    nativeDirichletCutoff n =ᶠ[𝓝 x] fun _ => (1:ℝ) := by
  filter_upwards [gt_mem_nhds hx] with y hy
  exact (nativeDirichletCutoff_profile n).2.2.2 y hy.le

/-- At each strictly negative radius the cutoff is eventually constant one on
a neighborhood, so its actual derivative eventually vanishes there. -/
theorem nativeDirichletCutoff_eventually_one (x : ℝ) (hx : x < 0) :
    ∀ᶠ n : ℕ in atTop, nativeDirichletCutoff n =ᶠ[𝓝 x] fun _ => (1:ℝ) := by
  have hw := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
    (gt_mem_nhds (by linarith : (0:ℝ) < -x/3))
  filter_upwards [hw] with n hn
  exact cutoff_germ_one n x (by linarith)

private theorem cutoff_deriv_zero_below (n : ℕ) (x : ℝ) (hx : x < -3) :
    deriv (nativeDirichletCutoff n) x = 0 := by
  have he := cutoff_germ_one n x (by linarith [width_le_one n])
  rw [he.deriv_eq,deriv_const]

/-- The full radial product-rule error of the actual native family is integrable
at every scale and tends to zero in the original angular L² norm. -/
theorem nativeTimePrimitiveAngularEnergy_endpoint_error_tendsto_zero
    (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) (n : ℕ) :
    (∀ m : ℕ, Integrable (fun x => ‖deriv (nativeDirichletCutoff m) x •
      D4BMModularCore.embedding (nativeTimePrimitiveAngularEnergy q s amplitude t n x)‖^(2 : ℕ))
      radialMeasure) ∧
    Tendsto (fun m : ℕ => ∫ x, ‖deriv (nativeDirichletCutoff m) x •
      D4BMModularCore.embedding (nativeTimePrimitiveAngularEnergy q s amplitude t n x)‖^(2 : ℕ)
      ∂radialMeasure) atTop (𝓝 0) := by
  let f : ℝ → D4BMModularCore.Space := fun x =>
    D4BMModularCore.embedding (nativeTimePrimitiveAngularEnergy q s amplitude t n x)
  have hf : ContDiff ℝ 1 f := nativeTimePrimitiveAngularEnergy_value_contDiff q s amplitude t n
  have hc : HasCompactSupport f := (nativeTimePrimitiveAngularEnergy_compact q s amplitude t n).comp_left
    (map_zero D4BMModularCore.embedding)
  have hz : f 0 = 0 := by
    dsimp only [f]
    rw [nativeTimePrimitiveAngularEnergy_boundary,map_zero]
  obtain ⟨D,hD⟩ := hc.deriv.exists_bound_of_continuous (contDiff_one_iff_deriv.mp hf).2
  have hD₀ : 0 ≤ D := (norm_nonneg _).trans (hD 0)
  have hlin (x : ℝ) : ‖f x‖ ≤ D*|x| := by
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun y (_ : y ∈ (univ : Set ℝ)) =>
        (hf.differentiable (by simp)).differentiableAt.hasDerivAt.hasDerivWithinAt)
      (fun y _ => hD y) convex_univ (mem_univ (0:ℝ)) (mem_univ x)
    simpa only [hz,sub_zero,Real.norm_eq_abs] using h
  obtain ⟨C,hC,hbound⟩ := nativeDirichletCutoff_weighted_derivative_bound
  let M : ℝ → ℝ := (Icc (-3:ℝ) 0).indicator (fun _ => (D*C)^(2 : ℕ))
  have hM : Integrable M radialMeasure :=
    (integrableOn_const (μ := radialMeasure) (s := Icc (-3:ℝ) 0)
      (C := (D*C)^(2 : ℕ)) isCompact_Icc.measure_lt_top.ne).integrable_indicator measurableSet_Icc
  have hcont (m : ℕ) : Continuous (fun x => ‖deriv (nativeDirichletCutoff m) x • f x‖^(2 : ℕ)) :=
    (((contDiff_infty_iff_deriv.mp (nativeDirichletCutoff_profile m).1).2.continuous).smul
      hf.continuous).norm.pow 2
  have hb (m : ℕ) : ∀ᵐ x ∂radialMeasure,
      ‖‖deriv (nativeDirichletCutoff m) x • f x‖^(2 : ℕ)‖ ≤ M x := by
    filter_upwards [ae_restrict_mem measurableSet_Iio] with x hx
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    by_cases hk : x ∈ Icc (-3:ℝ) 0
    · dsimp only [M]
      rw [indicator_of_mem hk]
      have he : ‖deriv (nativeDirichletCutoff m) x • f x‖ ≤ D*C := by
        rw [norm_smul,Real.norm_eq_abs]
        calc
          _ ≤ |deriv (nativeDirichletCutoff m) x| *(D*|x|) :=
            mul_le_mul_of_nonneg_left (hlin x) (abs_nonneg _)
          _ = D*|x*deriv (nativeDirichletCutoff m) x| := by rw [abs_mul]; ring
          _ ≤ D*C := mul_le_mul_of_nonneg_left (hbound m x) hD₀
      nlinarith [norm_nonneg (deriv (nativeDirichletCutoff m) x • f x),mul_nonneg hD₀ hC]
    · have hx' : x < -3 := lt_of_not_ge (fun hl => hk ⟨hl,le_of_lt hx⟩)
      dsimp only [M]
      rw [indicator_of_notMem hk,cutoff_deriv_zero_below m x hx',zero_smul,norm_zero]
      simp
  refine ⟨fun m => hM.mono' (hcont m).aestronglyMeasurable (hb m),?_⟩
  change Tendsto (fun m : ℕ => ∫ x, ‖deriv (nativeDirichletCutoff m) x • f x‖^(2 : ℕ) ∂radialMeasure)
    atTop (𝓝 0)
  have h := tendsto_integral_of_dominated_convergence M
    (fun m => (hcont m).aestronglyMeasurable) hM hb (f := fun _ : ℝ => (0:ℝ)) ?_
  · simpa only [integral_zero] using h
  · filter_upwards [ae_restrict_mem measurableSet_Iio] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [nativeDirichletCutoff_eventually_one x hx] with m hm
    rw [hm.deriv_eq,deriv_const,zero_smul,norm_zero]
    simp

private theorem cutoff_value_convergence {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (hf : Continuous f) (hc : HasCompactSupport f) :
    (∀ m : ℕ, Integrable (fun x => ‖nativeDirichletCutoff m x • f x-f x‖^(2 : ℕ)) radialMeasure) ∧
    Tendsto (fun m : ℕ => ∫ x, ‖nativeDirichletCutoff m x • f x-f x‖^(2 : ℕ) ∂radialMeasure)
      atTop (𝓝 0) := by
  have hM : Integrable (fun x => ‖f x‖^(2 : ℕ)) radialMeasure :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp
      (hf.memLp_of_hasCompactSupport hc)
  have ha (m : ℕ) : AEStronglyMeasurable
      (fun x => ‖nativeDirichletCutoff m x • f x-f x‖^(2 : ℕ)) radialMeasure :=
    (((nativeDirichletCutoff_profile m).1.continuous.smul hf).sub hf).norm.pow 2 |>.aestronglyMeasurable
  have hb (m : ℕ) (x : ℝ) : ‖‖nativeDirichletCutoff m x • f x-f x‖^(2 : ℕ)‖ ≤ ‖f x‖^(2 : ℕ) := by
    have h := (nativeDirichletCutoff_profile m).2.1 x
    have he : |nativeDirichletCutoff m x-1| ≤ 1 := abs_le.mpr ⟨by linarith,by linarith⟩
    have he' : ‖nativeDirichletCutoff m x • f x-f x‖ ≤ ‖f x‖ := by
      rw [show nativeDirichletCutoff m x • f x-f x =
        (nativeDirichletCutoff m x-1) • f x by rw [sub_smul,one_smul],norm_smul,Real.norm_eq_abs]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right he (norm_nonneg (f x))
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    nlinarith [norm_nonneg (nativeDirichletCutoff m x • f x-f x),norm_nonneg (f x)]
  refine ⟨fun m => hM.mono' (ha m) (Eventually.of_forall (hb m)),?_⟩
  have h := tendsto_integral_of_dominated_convergence (fun x => ‖f x‖^(2 : ℕ)) ha hM
    (fun m => Eventually.of_forall (hb m)) (f := fun _ : ℝ => (0:ℝ)) ?_
  · simpa only [integral_zero] using h
  · filter_upwards [ae_restrict_mem measurableSet_Iio] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [nativeDirichletCutoff_eventually_one x hx] with m hm
    rw [hm.eq_of_nhds,one_smul,sub_self,norm_zero]
    simp

/-- The endpoint cutoffs converge in the actual angular energy norm, so both
angular derivative slots converge along with the original value. -/
theorem nativeTimePrimitiveAngularEnergy_endpoint_value_convergence
    (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) (n : ℕ) :
    (∀ m : ℕ, Integrable (fun x => ‖nativeDirichletCutoff m x •
      nativeTimePrimitiveAngularEnergy q s amplitude t n x-
      nativeTimePrimitiveAngularEnergy q s amplitude t n x‖^(2 : ℕ)) radialMeasure) ∧
    Tendsto (fun m : ℕ => ∫ x, ‖nativeDirichletCutoff m x •
      nativeTimePrimitiveAngularEnergy q s amplitude t n x-
      nativeTimePrimitiveAngularEnergy q s amplitude t n x‖^(2 : ℕ) ∂radialMeasure)
      atTop (𝓝 0) :=
  cutoff_value_convergence _ (nativeTimePrimitiveAngularEnergy_continuous q s amplitude t n)
    (nativeTimePrimitiveAngularEnergy_compact q s amplitude t n)

private theorem integral_sq_add_tendsto_zero {E : Type*} [NormedAddCommGroup E]
    (a b : ℕ → ℝ → E) (ha : ∀ m, AEStronglyMeasurable (a m) radialMeasure)
    (hb : ∀ m, AEStronglyMeasurable (b m) radialMeasure)
    (hai : ∀ m, Integrable (fun x => ‖a m x‖^(2 : ℕ)) radialMeasure)
    (hbi : ∀ m, Integrable (fun x => ‖b m x‖^(2 : ℕ)) radialMeasure)
    (hal : Tendsto (fun m => ∫ x, ‖a m x‖^(2 : ℕ) ∂radialMeasure) atTop (𝓝 0))
    (hbl : Tendsto (fun m => ∫ x, ‖b m x‖^(2 : ℕ) ∂radialMeasure) atTop (𝓝 0)) :
    (∀ m, Integrable (fun x => ‖a m x+b m x‖^(2 : ℕ)) radialMeasure) ∧
    Tendsto (fun m => ∫ x, ‖a m x+b m x‖^(2 : ℕ) ∂radialMeasure) atTop (𝓝 0) := by
  have hi (m : ℕ) : Integrable (fun x => ‖a m x+b m x‖^(2 : ℕ)) radialMeasure :=
    (memLp_two_iff_integrable_sq_norm ((ha m).add (hb m))).mp
      (((memLp_two_iff_integrable_sq_norm (ha m)).mpr (hai m)).add
        ((memLp_two_iff_integrable_sq_norm (hb m)).mpr (hbi m)))
  refine ⟨hi,?_⟩
  have hl : Tendsto (fun m => 2*((∫ x, ‖a m x‖^(2 : ℕ) ∂radialMeasure)+
      (∫ x, ‖b m x‖^(2 : ℕ) ∂radialMeasure))) atTop (𝓝 0) := by
    simpa only [add_zero,mul_zero] using (hal.add hbl).const_mul 2
  apply squeeze_zero (fun m => integral_nonneg (fun x => sq_nonneg _)) ?_ hl
  intro m
  have hu : Integrable (fun x => 2*(‖a m x‖^(2 : ℕ)+‖b m x‖^(2 : ℕ))) radialMeasure :=
    ((hai m).add (hbi m)).const_mul 2
  calc
    _ ≤ ∫ x, 2*(‖a m x‖^(2 : ℕ)+‖b m x‖^(2 : ℕ)) ∂radialMeasure := integral_mono (hi m) hu (fun x => by
      have h := norm_add_le (a m x) (b m x)
      have hn := norm_nonneg (a m x+b m x)
      nlinarith [sq_nonneg (‖a m x‖-‖b m x‖)])
    _ = _ := by rw [integral_const_mul,integral_add (hai m) (hbi m)]

/-- The actual radial derivative of the endpoint-cutoff value converges to the
literal native radial derivative, including the full product-rule correction. -/
theorem nativeTimePrimitiveAngularEnergy_endpoint_radial_convergence
    (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) (n : ℕ) :
    let f : ℝ → D4BMModularCore.Space := fun x =>
      D4BMModularCore.embedding (nativeTimePrimitiveAngularEnergy q s amplitude t n x)
    (∀ m : ℕ, Integrable (fun x => ‖deriv (fun y => nativeDirichletCutoff m y • f y) x-
      nativeTimePrimitiveAngularRadial q s amplitude t n x‖^(2 : ℕ)) radialMeasure) ∧
    Tendsto (fun m : ℕ => ∫ x, ‖deriv (fun y => nativeDirichletCutoff m y • f y) x-
      nativeTimePrimitiveAngularRadial q s amplitude t n x‖^(2 : ℕ) ∂radialMeasure)
      atTop (𝓝 0) := by
  intro f
  have hf : ContDiff ℝ 1 f := nativeTimePrimitiveAngularEnergy_value_contDiff q s amplitude t n
  have hc : HasCompactSupport f := (nativeTimePrimitiveAngularEnergy_compact q s amplitude t n).comp_left
    (map_zero D4BMModularCore.embedding)
  have hd : deriv f = nativeTimePrimitiveAngularRadial q s amplitude t n :=
    funext (fun x => (nativeTimePrimitiveAngularEnergy_value_hasDerivAt q s amplitude t n x).deriv)
  let a (m : ℕ) (x : ℝ) := deriv (nativeDirichletCutoff m) x • f x
  let b (m : ℕ) (x : ℝ) := nativeDirichletCutoff m x • deriv f x-deriv f x
  have ha (m : ℕ) : Continuous (a m) :=
    ((contDiff_infty_iff_deriv.mp (nativeDirichletCutoff_profile m).1).2.continuous).smul hf.continuous
  have hb (m : ℕ) : Continuous (b m) :=
    ((nativeDirichletCutoff_profile m).1.continuous.smul (contDiff_one_iff_deriv.mp hf).2).sub
      (contDiff_one_iff_deriv.mp hf).2
  have he (m : ℕ) (x : ℝ) : deriv (fun y => nativeDirichletCutoff m y • f y) x-
      nativeTimePrimitiveAngularRadial q s amplitude t n x = a m x+b m x := by
    have h := (((nativeDirichletCutoff_profile m).1.differentiable (by simp)).differentiableAt.hasDerivAt
      (x := x)).smul ((hf.differentiable (by simp)).differentiableAt.hasDerivAt (x := x))
    have heq : nativeDirichletCutoff m • f = (fun y => nativeDirichletCutoff m y • f y) := by
      funext y
      rfl
    rw [heq] at h
    rw [h.deriv,← hd]
    dsimp only [a,b]
    abel
  obtain ⟨hai,hal⟩ := nativeTimePrimitiveAngularEnergy_endpoint_error_tendsto_zero q s amplitude t n
  obtain ⟨hbi,hbl⟩ := cutoff_value_convergence (deriv f) (contDiff_one_iff_deriv.mp hf).2 hc.deriv
  simpa only [he] using integral_sq_add_tendsto_zero a b
    (fun m => (ha m).aestronglyMeasurable) (fun m => (hb m).aestronglyMeasurable) hai hbi hal hbl

end
end RHTower.D4BMNativeResponse
