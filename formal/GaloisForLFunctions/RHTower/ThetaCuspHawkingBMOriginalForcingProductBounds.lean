import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalFixedForcingProducts

/-! Exact two-field decomposition of the original forcing products, retaining
the three canonical principal terms, original causal onset, both reader branches,
and the physical squared metric horizon weight. Estimates hold in the temporal
convergence half-plane; complete metric/QNM matching is not asserted. -/

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace RHTower.D4BMOriginalForcingProductBounds
open D4BMJointSource D4BMModularCore D4BMLaplaceRadial D4BMOriginalReaderCuspBounds
open D4BMOriginalCornerForcing D4BMOriginalCollarCurrentBounds
noncomputable section
set_option autoImplicit false

private theorem unit_collar_limit : Tendsto (fun L : ℝ => radialUnit (-L/2)) atTop (𝓝 (1:ℝ)) := by
  have he := Real.tendsto_exp_neg_atTop_nhds_zero
  have hform (L : ℝ) : radialUnit (-L/2)=(1-Real.exp (-L))/(1+Real.exp (-L)) := by
    apply (eq_div_iff (ne_of_gt (by positivity : 0 < 1+Real.exp (-L)))).mpr
    have h := radialUnit_one_sub (-L/2)
    rw [show 2*(-L/2)=-L by ring] at h
    nlinarith
  simp_rw [hform]
  convert! (tendsto_const_nhds.sub he).div (tendsto_const_nhds.add he)
    (by norm_num : (1:ℝ)+0 ≠ 0) using 1
  norm_num

private theorem smooth_coefficient_error (F : ℝ → ℂ) (hF : DifferentiableAt ℝ F 1) :
    ∃ B : ℝ,0 ≤ B ∧ ∀ᶠ L : ℝ in atTop,‖F (radialUnit (-L/2))-F 1‖ ≤ B*Real.exp (-L) := by
  obtain ⟨B,hB,hb⟩ := hF.isBigO_sub.exists_pos
  refine ⟨2*B,by positivity,?_⟩
  filter_upwards [unit_collar_limit.eventually hb.bound,eventually_gt_atTop (0:ℝ)] with L h hL
  have hu := (radialUnit_bounds (-L/2) (by linarith)).2
  have he := radialUnit_one_sub (-L/2)
  rw [show 2*(-L/2)=-L by ring] at he
  have hn : ‖radialUnit (-L/2)-(1:ℝ)‖=1-radialUnit (-L/2) := by
    rw [Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr hu.le)]
    ring
  rw [hn,he] at h
  calc
    _ ≤ B*(Real.exp (-L)*(1+radialUnit (-L/2))) := h
    _ ≤ B*(Real.exp (-L)*2) := by gcongr; linarith
    _ = _ := by ring

/-- Both original radial reader branches preserve the geometric error of every
actual smooth compact-radius coefficient. -/
theorem reader_smooth_coefficient_error (q : XiZeroCopy) (w : ℂ) (hwi : w.im ≠ 0)
    (hw : 1 ≤ w.re) (F : ℝ → ℂ) (hF : DifferentiableAt ℝ F 1) :
    ∃ B : ℝ,0 ≤ B ∧ ∀ᶠ L : ℝ in atTop,
      ‖reader q w L*F (radialUnit (-L/2))-horizonReader q w*F 1‖ ≤
        B*(Real.exp (-L)+Real.exp (-w.re*L)) := by
  obtain ⟨C,hC,hc⟩ := smooth_coefficient_error F hF
  obtain ⟨D,hD,hd⟩ := normalizable_reader_collar_error w (physicalRadialFrequency q) hwi
  let beta := horizonReader q w
  let K := ‖beta‖+2*D
  have hK : 0 ≤ K := by dsimp [K];positivity
  refine ⟨K*C+D*‖F 1‖,by positivity,?_⟩
  filter_upwards [hc,hd,eventually_gt_atTop (0:ℝ)] with L hcL hdL hL
  let S := Real.exp (-L)+Real.exp (-w.re*L)
  have hS : 0 ≤ S := by dsimp [S];positivity
  have hS2 : S ≤ 2 := by
    have h1 : Real.exp (-L) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h2 : Real.exp (-w.re*L) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    dsimp [S]
    linarith
  have he : ‖reader q w L-beta‖ ≤ D*S := hdL
  have hn : ‖reader q w L‖ ≤ K := by
    have ht := norm_sub_norm_le (reader q w L) beta
    have hm := mul_le_mul_of_nonneg_left hS2 hD
    dsimp [K]
    linarith
  rw [show reader q w L*F (radialUnit (-L/2))-horizonReader q w*F 1=
    reader q w L*(F (radialUnit (-L/2))-F 1)+(reader q w L-beta)*F 1 by dsimp [beta];ring]
  calc
    _ ≤ ‖reader q w L‖*‖F (radialUnit (-L/2))-F 1‖+‖reader q w L-beta‖*‖F 1‖ := by
      simpa only [norm_mul] using norm_add_le
        (reader q w L*(F (radialUnit (-L/2))-F 1)) ((reader q w L-beta)*F 1)
    _ ≤ K*(C*Real.exp (-L))+(D*S)*‖F 1‖ :=
      add_le_add (mul_le_mul hn hcL (norm_nonneg _) hK) (mul_le_mul_of_nonneg_right he (norm_nonneg _))
    _ ≤ K*(C*S)+(D*S)*‖F 1‖ := by
      have hLS : Real.exp (-L) ≤ S := le_add_of_nonneg_right (Real.exp_nonneg _)
      gcongr
    _ = _ := by ring

/-- The two original forcing coefficients in the square/half-gradient basis. -/
def radialCoefficient (q : XiZeroCopy) (br : Bool) (amp : ℂ) (gradient : Bool) (u : ℝ) : ℂ :=
  if gradient then forcingProfile (physicalRate q br) amp 0 1 u
    else forcingProfile (physicalRate q br) amp 1 0 u

private theorem coefficient_smooth (q : XiZeroCopy) (br : Bool) (amp : ℂ) (gradient : Bool) :
    DifferentiableAt ℝ (radialCoefficient q br amp gradient) 1 := by
  have hp := ((power_derivatives (2*physicalRate q br) (by norm_num : 0 < 1+(1:ℝ))).1.scomp 1
    ((hasDerivAt_id (1:ℝ)).const_add 1)).differentiableAt
  have hu := (hasDerivAt_id (1:ℝ)).ofReal_comp.differentiableAt
  cases gradient <;> change DifferentiableAt ℝ (forcingProfile (physicalRate q br) amp _ _) 1
  all_goals unfold forcingProfile;fun_prop

private theorem damped_onset_bound (q : XiZeroCopy) (br : Bool) (w : ℂ) (hw : 1 ≤ w.re) :
    ∃ D : ℝ,0 ≤ D ∧ ∀ p : ℝ,0 < p →
      ‖Complex.exp (-w*(p:ℂ))*timeOnset (2*physicalRate q br) p‖ ≤ D*Real.exp (-p) := by
  have hs := currentRate_re_lt q br
  change (2*physicalRate q br).re < -2 at hs
  obtain ⟨D,hD,hd⟩ := timeOnset_pair_bound (2*physicalRate q br) 0 (by linarith)
  refine ⟨D,hD,?_⟩
  intro p hp
  have hO : ‖timeOnset (2*physicalRate q br) p‖ ≤ D := by
    have h := (le_add_of_nonneg_right (norm_nonneg (timeOnsetFirst (2*physicalRate q br) p))).trans (hd p)
    simpa only [neg_zero,zero_mul,Real.exp_zero,mul_one] using h
  rw [norm_mul,Complex.norm_exp]
  have he : (-w*(p:ℂ)).re=-w.re*p := by simp
  rw [he]
  calc
    _ ≤ Real.exp (-w.re*p)*D := mul_le_mul_of_nonneg_left hO (Real.exp_nonneg _)
    _ ≤ Real.exp (-p)*D := by gcongr;nlinarith
    _ = _ := mul_comm _ _

end
end RHTower.D4BMOriginalForcingProductBounds

namespace RHTower.D4BMOriginalForcingProductBounds
open D4BMJointSource D4BMModularCore D4BMOriginalCornerForcing D4BMOriginalForcingAngularPeriod
open D4BMOriginalReaderCuspBounds D4BMOriginalAngularReaderBounds
noncomputable section
set_option autoImplicit false

private theorem forcing_profile_linear (s amp J K : ℂ) (u : ℝ) :
    forcingProfile s amp J K u=forcingProfile s amp 1 0 u*J+forcingProfile s amp 0 1 u*K := by
  unfold forcingProfile
  ring

private theorem principal_profile_linear (q : XiZeroCopy) (br : Bool) (amp : ℂ) (u : ℝ) (i : Fin 3) :
    profilePrincipal q br amp u i=radialCoefficient q br amp false u*sourceCoefficient q br false i+
      radialCoefficient q br amp true u*sourceCoefficient q br true i :=
  forcing_profile_linear (physicalRate q br) amp (principalAmplitude q i) (principalGradient q br i) u

/-- Literal normalized forcing, with its actual onset and all three original principal products. -/
def normalizedProduct (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (d : Bool) (p L x k : ℝ) : ℂ :=
  reader q w L*((timeOriginalForcing q br amp (p+L/2) (-L/2) ![x,Real.exp k]/
    (horizonCoordinate (-L/2):ℂ))*angularJet q d x k-
    timeOnset (2*physicalRate q br) p*(∑ i : Fin 3,profilePrincipal q br amp (radialUnit (-L/2)) i*
      (Real.exp k:ℂ)^(principalExponent q i))*angularPrincipal q d k)

/-- The unchanged forcing trace and its corresponding original principal products. -/
def horizonProduct (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (d : Bool) (p x k : ℝ) : ℂ :=
  horizonReader q w*(forcingTrace (physicalRate q br) amp (fullSquarePotential q ![x,Real.exp k])
    (fullGradientEnergy q ![x,Real.exp k]/2) p*angularJet q d x k-
    timeOnset (2*physicalRate q br) p*(∑ i : Fin 3,profilePrincipal q br amp 1 i*
      (Real.exp k:ℂ)^(principalExponent q i))*angularPrincipal q d k)

private theorem profile_product_decomposition (q : XiZeroCopy) (br : Bool) (amp : ℂ)
    (d : Bool) (u x k : ℝ) :
    forcingProfile (physicalRate q br) amp (fullSquarePotential q ![x,Real.exp k])
      (fullGradientEnergy q ![x,Real.exp k]/2) u*angularJet q d x k-
      (∑ i : Fin 3,profilePrincipal q br amp u i*(Real.exp k:ℂ)^(principalExponent q i))*angularPrincipal q d k=
      radialCoefficient q br amp false u*fixedProduct q br false d x k+
      radialCoefficient q br amp true u*fixedProduct q br true d x k := by
  rw [forcing_profile_linear]
  simp_rw [principal_profile_linear]
  simp only [Fin.sum_univ_three,fixedProduct,sourcePrincipal,Matrix.cons_val]
  simp only [radialCoefficient,sourceField,sourceCoefficient,Bool.false_eq_true,↓reduceIte]
  ring

private theorem normalized_product_decomposition (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (d : Bool) (p L x k : ℝ) (hL : 0 < L) :
    normalizedProduct q br amp w d p L x k=reader q w L*timeOnset (2*physicalRate q br) p*
      (radialCoefficient q br amp false (radialUnit (-L/2))*fixedProduct q br false d x k+
       radialCoefficient q br amp true (radialUnit (-L/2))*fixedProduct q br true d x k) := by
  rw [normalizedProduct,original_full_forcing_normalized q br amp hL]
  have h := profile_product_decomposition q br amp d (radialUnit (-L/2)) x k
  linear_combination reader q w L*timeOnset (2*physicalRate q br) p*h

private theorem horizon_product_decomposition (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (d : Bool) (p x k : ℝ) :
    horizonProduct q br amp w d p x k=horizonReader q w*timeOnset (2*physicalRate q br) p*
      (radialCoefficient q br amp false 1*fixedProduct q br false d x k+
       radialCoefficient q br amp true 1*fixedProduct q br true d x k) := by
  rw [horizonProduct,forcingTrace]
  have h := profile_product_decomposition q br amp d 1 x k
  linear_combination horizonReader q w*timeOnset (2*physicalRate q br) p*h

/-- The complete normalized forcing product, including its gradient source and
original three counterterms, has independent cusp, horizon and time control. -/
theorem original_forcing_product_error (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (d : Bool) (N : ℕ) (hwi : w.im ≠ 0) (hw : 1 ≤ w.re) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ᶠ L : ℝ in atTop,∀ p x k : ℝ,0 < p → 0 ≤ k →
      ‖Complex.exp (-w*(p:ℂ))*(normalizedProduct q br amp w d p L x k-horizonProduct q br amp w d p x k)‖ ≤
        C*(Real.exp (-L)+Real.exp (-w.re*L))*Real.exp (-(N:ℝ)*k)*Real.exp (-p) := by
  obtain ⟨A,hA,ha⟩ := fixed_product_decay q br false d N
  obtain ⟨B,hB,hb⟩ := fixed_product_decay q br true d N
  obtain ⟨D,hD,hd⟩ := damped_onset_bound q br w hw
  obtain ⟨E,hE,he⟩ := reader_smooth_coefficient_error q w hwi hw
    (radialCoefficient q br amp false) (coefficient_smooth q br amp false)
  obtain ⟨F,hF,hf⟩ := reader_smooth_coefficient_error q w hwi hw
    (radialCoefficient q br amp true) (coefficient_smooth q br amp true)
  refine ⟨D*(E*A+F*B),by positivity,?_⟩
  filter_upwards [he,hf,eventually_gt_atTop (0:ℝ)] with L heL hfL hL p x k hp hk
  let S := Real.exp (-L)+Real.exp (-w.re*L)
  let delta (b : Bool) := reader q w L*radialCoefficient q br amp b (radialUnit (-L/2))-
    horizonReader q w*radialCoefficient q br amp b 1
  have h0 : ‖delta false‖ ≤ E*S := heL
  have h1 : ‖delta true‖ ≤ F*S := hfL
  have heq : Complex.exp (-w*(p:ℂ))*(normalizedProduct q br amp w d p L x k-horizonProduct q br amp w d p x k)=
      (Complex.exp (-w*(p:ℂ))*timeOnset (2*physicalRate q br) p)*
        (delta false*fixedProduct q br false d x k+delta true*fixedProduct q br true d x k) := by
    rw [normalized_product_decomposition q br amp w d p L x k hL,horizon_product_decomposition]
    dsimp [delta]
    ring
  rw [heq,norm_mul]
  have hbnd : ‖delta false*fixedProduct q br false d x k+delta true*fixedProduct q br true d x k‖ ≤
      (E*A+F*B)*S*Real.exp (-(N:ℝ)*k) := by
    calc
      _ ≤ ‖delta false‖*‖fixedProduct q br false d x k‖+‖delta true‖*‖fixedProduct q br true d x k‖ := by
        simpa only [norm_mul] using norm_add_le (delta false*fixedProduct q br false d x k) (delta true*fixedProduct q br true d x k)
      _ ≤ (E*S)*(A*Real.exp (-(N:ℝ)*k))+(F*S)*(B*Real.exp (-(N:ℝ)*k)) :=
        add_le_add (mul_le_mul h0 (ha x k hk) (norm_nonneg _) (by dsimp [S];positivity))
          (mul_le_mul h1 (hb x k hk) (norm_nonneg _) (by dsimp [S];positivity))
      _ = _ := by ring
  calc
    _ ≤ (D*Real.exp (-p))*((E*A+F*B)*S*Real.exp (-(N:ℝ)*k)) :=
      mul_le_mul (hd p hp) hbnd (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- The unchanged normalized forcing comparison remains uniform after the
actual source-time integral, for every upper time cutoff. -/
theorem original_forcing_product_time_error (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (d : Bool) (N : ℕ) (hwi : w.im ≠ 0) (hw : 1 ≤ w.re) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ᶠ L : ℝ in atTop,∀ T x k : ℝ,0 ≤ T → 0 ≤ k →
      ‖∫ p in (0:ℝ)..T,Complex.exp (-w*(p:ℂ))*(normalizedProduct q br amp w d p L x k-horizonProduct q br amp w d p x k)‖ ≤
        C*(Real.exp (-L)+Real.exp (-w.re*L))*Real.exp (-(N:ℝ)*k) := by
  obtain ⟨C,hC,h⟩ := original_forcing_product_error q br amp w d N hwi hw
  refine ⟨C,hC,?_⟩
  filter_upwards [h] with L hL T x k hT hk
  let B := C*(Real.exp (-L)+Real.exp (-w.re*L))*Real.exp (-(N:ℝ)*k)
  have hB : 0 ≤ B := by dsimp [B];positivity
  have hi : IntervalIntegrable (fun p : ℝ => B*Real.exp (-p)) volume 0 T := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hb := intervalIntegral.norm_integral_le_of_norm_le hT
    (Filter.Eventually.of_forall (fun p hp => hL p x k hp.1 hk)) hi
  calc
    _ ≤ ∫ p in (0:ℝ)..T,B*Real.exp (-p) := hb
    _ = B*(1-Real.exp (-T)) := by
      rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_neg,integral_exp,neg_zero,Real.exp_zero]
    _ ≤ _ := by change B*(1-Real.exp (-T)) ≤ B;nlinarith [Real.exp_nonneg (-T)]

end
end RHTower.D4BMOriginalForcingProductBounds

namespace RHTower.D4BMOriginalForcingProductBounds
open D4BMJointSource D4BMJointWave D4BMModularCore D4BMOriginalReaderCuspBounds
open D4BMOriginalAngularReaderBounds D4BMOriginalForcingAngularPeriod
noncomputable section
set_option autoImplicit false

/-- Actual forcing product before division by the horizon coordinate. -/
def rawProduct (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (d : Bool) (p L x k : ℝ) : ℂ :=
  reader q w L*(timeOriginalForcing q br amp (p+L/2) (-L/2) ![x,Real.exp k]*angularJet q d x k-
    (horizonCoordinate (-L/2):ℂ)*timeOnset (2*physicalRate q br) p*
      (∑ i : Fin 3,profilePrincipal q br amp (radialUnit (-L/2)) i*
        (Real.exp k:ℂ)^(principalExponent q i))*angularPrincipal q d k)

theorem raw_product_factor (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (d : Bool)
    (p L x k : ℝ) (hL : 0 < L) :
    rawProduct q br amp w d p L x k=
      (horizonCoordinate (-L/2):ℂ)*normalizedProduct q br amp w d p L x k := by
  have hZ : (horizonCoordinate (-L/2):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (horizonCoordinate_interior (-L/2) (by linarith)).1)
  unfold rawProduct normalizedProduct
  generalize (horizonCoordinate (-L/2):ℂ)=z at hZ ⊢
  field_simp [hZ]

private theorem geometric_collar_bound (L : ℝ) (hL : 0 < L) :
    Real.exp (-L) ≤ (tortoiseRadius (-L/2))^(2 : ℕ)-1 := by
  let R := tortoiseRadius (-L/2)
  have hR : 1 < R := tortoiseRadius_exterior (-L/2) (by linarith)
  have hR0 : R ≠ 0 := by linarith
  have h := radialUnit_one_sub (-L/2)
  rw [show 2*(-L/2)=-L by ring,radialUnit_inverse_radius] at h
  change 1-R⁻¹=Real.exp (-L)*(1+R⁻¹) at h
  have he : R-1=Real.exp (-L)*(R+1) := by
    have hh := congrArg (fun t : ℝ => t*R) h
    field_simp [hR0] at hh
    nlinarith
  calc
    _ ≤ Real.exp (-L)*(R+1)^(2 : ℕ) := le_mul_of_one_le_right (Real.exp_nonneg _) (by nlinarith)
    _ = (Real.exp (-L)*(R+1))*(R+1) := by ring
    _ = R^(2 : ℕ)-1 := by rw [← he];ring

/-- The full forcing transfer survives the squared singular metric denominator.
Its original horizon trace is retained; cusp decay is uniform in both other cutoffs. -/
theorem metric_forcing_product_time_error (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (d : Bool) (N : ℕ) (hwi : w.im ≠ 0) (hw : 1 ≤ w.re) :
    ∃ B : ℝ,0 ≤ B ∧ ∀ᶠ L : ℝ in atTop,∀ T x k : ℝ,0 ≤ T → 0 ≤ k →
      ‖((tortoiseRadius (-L/2):ℂ)^(2 : ℕ)*(∫ p in (0:ℝ)..T,Complex.exp (-w*(p:ℂ))*(rawProduct q br amp w d p L x k-
        (horizonCoordinate (-L/2):ℂ)*horizonProduct q br amp w d p x k)))/
          ((tortoiseRadius (-L/2):ℂ)^(2 : ℕ)-1)^(2 : ℕ)‖ ≤ B*Real.exp (-(N:ℝ)*k) := by
  obtain ⟨B,hB,h⟩ := original_forcing_product_time_error q br amp w d N hwi hw
  refine ⟨2*B,by positivity,?_⟩
  filter_upwards [h,eventually_gt_atTop (0:ℝ)] with L hL hpos T x k hT hk
  let R := tortoiseRadius (-L/2)
  let Z := horizonCoordinate (-L/2)
  have hR : 1 < R := tortoiseRadius_exterior (-L/2) (by linarith)
  have hR0 : R ≠ 0 := by linarith
  have hf : 0 < R^(2 : ℕ)-1 := by nlinarith
  have hZ : 0 < Z := (horizonCoordinate_interior (-L/2) (by linarith)).1
  have hZscale : Z*R^(2 : ℕ)=R^(2 : ℕ)-1 := by
    dsimp [Z]
    rw [horizonCoordinate,radialUnit_inverse_radius]
    change (1-R⁻¹^(2 : ℕ))*R^(2 : ℕ)=R^(2 : ℕ)-1
    field_simp
  have hgeo : Real.exp (-L) ≤ R^(2 : ℕ)-1 := geometric_collar_bound L hpos
  have hdec : Real.exp (-w.re*L) ≤ Real.exp (-L) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hS : Real.exp (-L)+Real.exp (-w.re*L) ≤ 2*(R^(2 : ℕ)-1) := by linarith
  have hn : ‖(R:ℂ)^(2 : ℕ)-1‖=R^(2 : ℕ)-1 := by
    rw [← Complex.ofReal_pow,← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos hf]
  have heq (p : ℝ) : Complex.exp (-w*(p:ℂ))*(rawProduct q br amp w d p L x k-
      (horizonCoordinate (-L/2):ℂ)*horizonProduct q br amp w d p x k)=
      (Z:ℂ)*(Complex.exp (-w*(p:ℂ))*(normalizedProduct q br amp w d p L x k-
        horizonProduct q br amp w d p x k)) := by
    rw [raw_product_factor q br amp w d p L x k hpos]
    dsimp [Z]
    ring
  simp_rw [heq]
  rw [intervalIntegral.integral_const_mul]
  change ‖((R:ℂ)^(2 : ℕ)*((Z:ℂ)*(_ : ℂ)))/((R:ℂ)^(2 : ℕ)-1)^(2 : ℕ)‖ ≤ _
  simp only [norm_div,norm_mul,norm_pow,hn,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hZ,abs_of_pos (show 0 < R by linarith)]
  rw [← mul_assoc,mul_comm (R^(2 : ℕ)) Z,hZscale]
  apply (div_le_iff₀ (sq_pos_of_pos hf)).mpr
  calc
    _ ≤ (R^(2 : ℕ)-1)*(B*(Real.exp (-L)+Real.exp (-w.re*L))*Real.exp (-(N:ℝ)*k)) :=
      mul_le_mul_of_nonneg_left (hL T x k hT hk) hf.le
    _ ≤ (R^(2 : ℕ)-1)*(B*(2*(R^(2 : ℕ)-1))*Real.exp (-(N:ℝ)*k)) := by gcongr
    _ = _ := by ring

/-- Independent horizon/cusp matching of the actual forcing transfer, with
its squared metric weight, along arbitrary nonnegative time-cutoff nets. -/
theorem metric_forcing_product_joint_limit (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (d : Bool) (hwi : w.im ≠ 0) (hw : 1 ≤ w.re)
    (T : ℝ × ℝ → Ici (0:ℝ)) (X : ℝ × ℝ → ℝ) :
    Tendsto (fun z : ℝ × ℝ =>
      ((tortoiseRadius (-z.1/2):ℂ)^(2 : ℕ)*(∫ p in (0:ℝ)..(T z:ℝ),Complex.exp (-w*(p:ℂ))*(rawProduct q br amp w d p z.1 (X z) z.2-
        (horizonCoordinate (-z.1/2):ℂ)*horizonProduct q br amp w d p (X z) z.2)))/
          ((tortoiseRadius (-z.1/2):ℂ)^(2 : ℕ)-1)^(2 : ℕ))
      ((atTop : Filter ℝ) ×ˢ (atTop : Filter ℝ)) (𝓝 0) := by
  obtain ⟨B,hB,hb⟩ := metric_forcing_product_time_error q br amp w d 1 hwi hw
  have he : Tendsto (fun z : ℝ × ℝ => B*Real.exp (-z.2))
      ((atTop : Filter ℝ) ×ˢ (atTop : Filter ℝ)) (𝓝 0) := by
    simpa only [Function.comp_def,mul_zero] using (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul B).comp tendsto_snd
  apply squeeze_zero_norm' _ he
  filter_upwards [hb.prod_mk (eventually_ge_atTop (0:ℝ))] with z hz
  simpa only [Nat.cast_one,neg_one_mul] using hz.1 (T z) (X z) z.2 (T z).property hz.2

end
end RHTower.D4BMOriginalForcingProductBounds
