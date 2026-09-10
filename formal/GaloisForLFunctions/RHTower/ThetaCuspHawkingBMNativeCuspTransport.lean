import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeCircleMean
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourcePrincipalData
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMWeightedSquareCuspBound

/-! Exact transport of all three original cusp powers by the native circle mean. -/
open Set Filter Topology MeasureTheory
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMNativeCircle
open D4BMModularCore D4BMGlobalAngularResponse D4BMAngularSeries D4BMJointSource
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace

/-- The native angular coefficient of a complex height monomial. -/
def powerCircle (alpha : ℂ) (d : ℝ) : ℂ :=
  average (fun theta => (height d theta : ℂ)^alpha)

/-- All three transported principal powers, with their original completed amplitudes. -/
def transportedPrincipal (q : XiZeroCopy) (d k : ℝ) : ℂ :=
  ∑ i : Fin 3, principalAmplitude q i*(Real.exp k : ℂ)^(principalExponent q i)*
    powerCircle (principalExponent q i) d

/-- The complete native mean after removing precisely its transported cusp powers. -/
def cuspMeanRemainder (q : XiZeroCopy) (d x k : ℝ) : ℂ :=
  mean q d x k-transportedPrincipal q d k

private theorem height_positive (d theta : ℝ) : 0 < height d theta :=
  one_div_pos.mpr (denominator_pos _ _)

private theorem power_height_continuous (alpha : ℂ) (d : ℝ) :
    Continuous (fun theta => (height d theta:ℂ)^alpha) := by
  have hden : Continuous (denominator d) := by unfold denominator; fun_prop
  have hh : Continuous (fun theta => (height d theta:ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_const.div₀ hden (fun theta => (denominator_pos d theta).ne'))
  exact hh.cpow continuous_const (fun theta => Complex.ofReal_mem_slitPlane.mpr (height_positive _ _))

private theorem circle_positive (d theta x k : ℝ) : 0 < logCircle d theta x k 1 :=
  mul_pos (Real.exp_pos k) (height_positive d theta)

private theorem source_continuous (q : XiZeroCopy) (d x k : ℝ) :
    Continuous (fun theta => source q d theta x k) := by
  have hmap : Continuous (fun theta : ℝ => (![d,theta,x,k] : Fin 4 → ℝ)) := by fun_prop
  convert! (source_smooth q).continuous.comp hmap using 1

private theorem principal_circle_eq (q : XiZeroCopy) (d theta x k : ℝ) :
    principalSquare q (logCircle d theta x k) =
      ∑ i : Fin 3, (principalAmplitude q i*(Real.exp k:ℂ)^(principalExponent q i))*
        (height d theta:ℂ)^(principalExponent q i) := by
  rw [principalSquare_expansion q _ (circle_positive _ _ _ _)]
  apply Finset.sum_congr rfl
  intro i _
  have hy : logCircle d theta x k 1=Real.exp k*height d theta := rfl
  rw [hy,Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (Real.exp_pos _).le (height_positive _ _).le]
  ring

private theorem principal_circle_continuous (q : XiZeroCopy) (d x k : ℝ) :
    Continuous (fun theta => principalSquare q (logCircle d theta x k)) := by
  simp only [principal_circle_eq]
  exact continuous_finsetSum _ (fun i _ => continuous_const.mul (power_height_continuous _ _))

private theorem half_remainder_eq (q : XiZeroCopy) (z : Fin 2 → ℝ) :
    squareRemainder (D4BMGlobalAngularResponse.center q) z/2 =
      fullSquarePotential q z-principalSquare q z := by
  dsimp [squareRemainder,fullSquarePotential,principalSquare]
  ring

private theorem remainder_continuous (q : XiZeroCopy) (d x k : ℝ) :
    Continuous (fun theta => squareRemainder (D4BMGlobalAngularResponse.center q)
      (logCircle d theta x k)/2) := by
  simp only [half_remainder_eq]
  exact (source_continuous q d x k).sub (principal_circle_continuous q d x k)

/-- Exact full-source cusp expansion of the native mean; the entire signed Fourier remainder remains. -/
theorem mean_cusp_expansion (q : XiZeroCopy) (d x k : ℝ) :
    mean q d x k = transportedPrincipal q d k+
      average (fun theta => squareRemainder (D4BMGlobalAngularResponse.center q)
        (logCircle d theta x k)/2) := by
  have hp : average (fun theta => principalSquare q (logCircle d theta x k))=
      transportedPrincipal q d k := by
    simp only [principal_circle_eq,average,transportedPrincipal,powerCircle]
    have hint (i : Fin 3) : IntegrableOn (fun theta =>
        (principalAmplitude q i*(Real.exp k:ℂ)^(principalExponent q i))*
          (height d theta:ℂ)^(principalExponent q i)) (Ioc 0 (2*Real.pi)) :=
      (continuous_const.mul (power_height_continuous _ _)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
    rw [integral_finsetSum (Finset.univ : Finset (Fin 3)) (fun i _ => hint i),Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_const_mul]
    ring
  have he (theta : ℝ) : source q d theta x k =
      principalSquare q (logCircle d theta x k)+
        squareRemainder (D4BMGlobalAngularResponse.center q) (logCircle d theta x k)/2 := by
    rw [half_remainder_eq]
    dsimp only [source]
    ring
  simp only [mean,he,average]
  rw [integral_add ((principal_circle_continuous q d x k).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    ((remainder_continuous q d x k).integrableOn_Icc.mono_set Ioc_subset_Icc_self),mul_add]
  exact congrArg (fun v => v+_) hp

/-- The difference from all three transported cusp powers is exactly the original remainder integral. -/
theorem cuspMeanRemainder_integral (q : XiZeroCopy) (d x k : ℝ) :
    cuspMeanRemainder q d x k = average (fun theta =>
      squareRemainder (D4BMGlobalAngularResponse.center q) (logCircle d theta x k)/2) := by
  rw [cuspMeanRemainder,mean_cusp_expansion]
  ring

private theorem denominator_upper (d theta : ℝ) (hd : 0 ≤ d) :
    denominator d theta ≤ Real.exp d := by
  rw [← Real.cosh_add_sinh]
  have hs := Real.sinh_nonneg_iff.mpr hd
  dsimp [denominator]
  nlinarith [Real.neg_one_le_cos theta]

private theorem circle_height_lower (d theta x k : ℝ) (hd : 0 ≤ d) :
    Real.exp (k-d) ≤ logCircle d theta x k 1 := by
  rw [Real.exp_sub]
  change Real.exp k/Real.exp d ≤ Real.exp k*(1/denominator d theta)
  rw [← div_eq_mul_one_div]
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le (denominator_pos _ _) (denominator_upper _ _ hd)

private theorem average_norm_le {f : ℝ → ℂ} {C : ℝ} (h : ∀ theta, ‖f theta‖ ≤ C) :
    ‖average f‖ ≤ C := by
  have hb := norm_integral_le_of_norm_le_const (μ := volume.restrict (Ioc 0 (2*Real.pi)))
    (Filter.Eventually.of_forall h)
  have hm : (volume.restrict (Ioc 0 (2*Real.pi))).real Set.univ=2*Real.pi := by
    simp [Measure.real,Real.volume_Ioc,Real.pi_pos.le]
  rw [hm] at hb
  dsimp only [average]
  rw [norm_mul,norm_div,norm_one,norm_mul,Complex.norm_ofNat,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  calc
    _ ≤ (1/(2*Real.pi))*(C*(2*Real.pi)) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = C := by field_simp

/-- Every inverse-height decay order survives the native mean, with explicit radius dependence. -/
theorem cuspMeanRemainder_rapid_bound (q : XiZeroCopy) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d x k : ℝ, 0 ≤ d → d ≤ k →
      ‖cuspMeanRemainder q d x k‖ ≤ C*Real.exp ((N:ℝ)*(d-k)) := by
  obtain ⟨C,hC,hb⟩ := weighted_squareRemainder_bounded
    (D4BMGlobalAngularResponse.center q) (N:ℂ) 1 (by norm_num)
  refine ⟨C/2,by positivity,?_⟩
  intro d x k hd hk
  rw [cuspMeanRemainder_integral]
  apply average_norm_le
  intro theta
  let z := logCircle d theta x k
  have hz0 : 0 < z 1 := circle_positive _ _ _ _
  have hz : 1 ≤ z 1 := (Real.one_le_exp_iff.mpr (sub_nonneg.mpr hk)).trans (circle_height_lower _ _ _ _ hd)
  have h := hb z hz
  rw [norm_mul,Complex.cpow_natCast,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hz0] at h
  have he : Real.exp ((N:ℝ)*(k-d)) ≤ (z 1)^N := by
    rw [Real.exp_nat_mul]
    gcongr
    exact circle_height_lower _ _ _ _ hd
  have hprod : Real.exp ((N:ℝ)*(k-d))*‖squareRemainder (D4BMGlobalAngularResponse.center q) z‖ ≤ C :=
    (mul_le_mul_of_nonneg_right he (norm_nonneg _)).trans h
  have hrem : ‖squareRemainder (D4BMGlobalAngularResponse.center q) z‖ ≤
      C*Real.exp ((N:ℝ)*(d-k)) := by
    have ht : ‖squareRemainder (D4BMGlobalAngularResponse.center q) z‖ ≤ C/Real.exp ((N:ℝ)*(k-d)) :=
      (le_div_iff₀ (Real.exp_pos ((N:ℝ)*(k-d)))).mpr (by simpa only [mul_comm] using hprod)
    have heq : C/Real.exp ((N:ℝ)*(k-d))=C*Real.exp ((N:ℝ)*(d-k)) := by
      rw [div_eq_mul_inv,← Real.exp_neg]
      congr 2
      ring
    exact ht.trans_eq heq
  rw [norm_div,Complex.norm_ofNat]
  exact (div_le_div_of_nonneg_right hrem (by norm_num)).trans_eq (by ring)

private theorem source_base_circle_continuous (q : XiZeroCopy) (d : ℝ) :
    Continuous (fun p : UpperHalfPlane × ℝ =>
      source q d p.2 p.1.re (Real.log p.1.im)) := by
  have hmap : Continuous (fun p : UpperHalfPlane × ℝ =>
      (![d,p.2,p.1.re,Real.log p.1.im] : Fin 4 → ℝ)) := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_const
    · exact continuous_snd
    · exact UpperHalfPlane.continuous_re.comp continuous_fst
    · exact (UpperHalfPlane.continuous_im.comp continuous_fst).log (fun p => p.1.im_pos.ne')
  convert! (source_smooth q).continuous.comp hmap using 1
/-- The normalized native circle is continuous in its original upper-half-plane basepoint. -/
theorem mean_base_continuous (q : XiZeroCopy) (d : ℝ) :
    Continuous (fun z : UpperHalfPlane => mean q d z.re (Real.log z.im)) := by
  have hf := source_base_circle_continuous q d
  have h : Continuous (fun z : UpperHalfPlane => ∫ theta in (0:ℝ)..(2*Real.pi),
      source q d theta z.re (Real.log z.im)) := by
    convert! intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (z : UpperHalfPlane) theta => source q d theta z.re (Real.log z.im))
      (μ := volume) hf 0 (2*Real.pi) using 1
  have he : (fun z : UpperHalfPlane => mean q d z.re (Real.log z.im))=
      fun z => (1/(2*Real.pi:ℂ))*(∫ theta in (0:ℝ)..(2*Real.pi),
        source q d theta z.re (Real.log z.im)) := by
    funext z
    rw [intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2*Real.pi)]
    rfl
  rw [he]
  exact continuous_const.mul h

/-- Subtract the transported cusp powers with the original modular cutoff. -/
def nativeCutoffResidual (q : XiZeroCopy) (d : ℝ) (z : UpperHalfPlane) : ℂ :=
  mean q d z.re (Real.log z.im)-cutoff (coordinates z)*transportedPrincipal q d (Real.log z.im)

private theorem transported_base_continuous (q : XiZeroCopy) (d : ℝ) :
    Continuous (fun z : UpperHalfPlane => transportedPrincipal q d (Real.log z.im)) := by
  have he : (fun z : UpperHalfPlane => transportedPrincipal q d (Real.log z.im))=
      fun z => ∑ i : Fin 3, principalAmplitude q i*(z.im:ℂ)^(principalExponent q i)*powerCircle (principalExponent q i) d := by
    funext z
    simp only [transportedPrincipal,Real.exp_log z.im_pos]
  rw [he]
  apply continuous_finsetSum
  intro i _
  exact (continuous_const.mul ((Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).cpow
    continuous_const (fun z => Complex.ofReal_mem_slitPlane.mpr z.im_pos))).mul continuous_const

/-- The actual cutoff-subtracted native circle mean belongs to the original modular L² space. -/
theorem nativeCutoffResidual_memLp (q : XiZeroCopy) (d : ℝ) (hd : 0 ≤ d) :
    MemLp (nativeCutoffResidual q d) 2 D4BMModularCore.measure := by
  have hcoord : Continuous (coordinates : UpperHalfPlane → Fin 2 → ℝ) := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact UpperHalfPlane.continuous_re
    · exact UpperHalfPlane.continuous_im
  have hc : Continuous (nativeCutoffResidual q d) :=
    (mean_base_continuous q d).sub ((sourceCutoff_smooth.continuous.comp hcoord).mul
      (transported_base_continuous q d))
  obtain ⟨C,hC,hb⟩ := cuspMeanRemainder_rapid_bound q 0
  obtain ⟨A,hA⟩ := (truncated_cell_compact (3+Real.exp d)).exists_bound_of_continuousOn hc.continuousOn
  apply MemLp.of_bound hc.aestronglyMeasurable (max A C)
  filter_upwards [ae_restrict_mem ModularGroup.isClosed_fd.measurableSet] with z hz
  by_cases hy : z.im ≤ 3+Real.exp d
  · exact (hA z ⟨hz,hy⟩).trans (le_max_left _ _)
  · have h3 : 3 < z.im := by linarith [Real.exp_pos d]
    have hk : d ≤ Real.log z.im := by
      rw [← Real.exp_le_exp,Real.exp_log z.im_pos]
      linarith
    have h := hb d z.re (Real.log z.im) hd hk
    have he : nativeCutoffResidual q d z=cuspMeanRemainder q d z.re (Real.log z.im) := by
      unfold nativeCutoffResidual cutoff cuspMeanRemainder
      rw [Real.smoothTransition.one_of_one_le (by change 1 ≤ z.im-2; linarith)]
      simp
    rw [he]
    exact (by simpa using h : ‖cuspMeanRemainder q d z.re (Real.log z.im)‖ ≤ C).trans (le_max_right _ _)

end
end RHTower.D4BMNativeCircle
