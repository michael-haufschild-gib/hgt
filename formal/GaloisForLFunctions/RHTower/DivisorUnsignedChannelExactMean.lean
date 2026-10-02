import GaloisForLFunctions.RHTower.DivisorTerminalModularMean
import GaloisForLFunctions.RHTower.DivisorSmoothSquareBlockMean

/-!
# Exact leading coefficient of the unsigned divisor channels

The signed terminal modular mean vanishes at its natural scale. Retaining
the exact square-birth contribution gives the centered Abel coefficient
`-1/24`, and the smooth mean then gives the complete unit coefficient
`log(2π)/2 - γ - 1/4`. Exact square-root interpolation makes the relative
error uniform in every positive dilation once its quotient is large.
-/

noncomputable section
open Finset Filter Topology HTGeometry
namespace RHTower

private lemma birth_mean_error {d : ℕ} (hd : 0<d) :
    1/24-1/(12*(d:ℝ))≤centeredModularMeanMagnitude d*halfOrderAbelStep (d*d) 0 ∧
    centeredModularMeanMagnitude d*halfOrderAbelStep (d*d) 0≤1/24 := by
  let w := halfOrderAbelStep (d*d) 0
  have hdR : (0:ℝ)<d := by exact_mod_cast hd
  have hd1 : (1:ℝ)≤d := by exact_mod_cast hd
  have hw0 : 0≤w := halfOrderAbelStep_nonneg _ _
  have hwd : (d:ℝ)*w≤1/2 := halfOrderAbelStep_square_initial d
  have hw : w≤1/2 := by nlinarith only [hwd,mul_nonneg (sub_nonneg.mpr hd1) hw0]
  have hs := Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) (d*d+1))
  have heq : 2*(d:ℝ)*w+w^2=1 := by
    dsimp [w,halfOrderAbelStep]
    simp only [Nat.cast_mul,Real.sqrt_mul_self (Nat.cast_nonneg d)]
    push_cast at hs ⊢
    nlinarith only [hs]
  have hquad : (d:ℝ)*w^2≤1/4 := by
    have h := mul_le_mul_of_nonneg_right hwd hw0
    nlinarith only [h,hw]
  have hscaled := congrArg (fun x : ℝ => (d:ℝ)*x) heq
  have hB : centeredModularMeanMagnitude d≤(d:ℝ)/12 := by
    unfold centeredModularMeanMagnitude
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  constructor
  · change _≤centeredModularMeanMagnitude d*w
    unfold centeredModularMeanMagnitude
    field_simp [hdR.ne']
    nlinarith only [hscaled,hquad,hw]
  · have h := mul_le_mul_of_nonneg_right hB hw0
    change centeredModularMeanMagnitude d*w≤_
    nlinarith only [h,hwd]

private lemma centered_birth_channels_through_sqrt (M : ℕ) :
    centeredDivisorHyperbolaAbel M = ∑ d ∈ Icc 1 (Nat.sqrt M),
      ∑ k ∈ Ico (d*d) M,centeredModularRamp d k*halfOrderAbelStep 0 k := by
  rw [centeredDivisorHyperbolaAbel_eq_birth_channels]
  apply sum_subset (Icc_subset_Icc le_rfl (Nat.sqrt_le_sqrt (Nat.sub_le M 1)))
  intro d hd hnot
  have hd1 := (mem_Icc.mp hd).1
  have hbase := Nat.le_sqrt.mp (mem_Icc.mp hd).2
  have hnotbase : ¬d*d≤M-1 := by
    intro h
    exact hnot (mem_Icc.mpr ⟨hd1,Nat.le_sqrt.mpr h⟩)
  have heq : d*d=M := by omega
  simp [heq]

private def terminalSum (M : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 (Nat.sqrt M),(centeredModularMeanMagnitude d+centeredModularPrimitive d M)

/-- Exact centered-channel remainder, retaining the signed terminal primitive. -/
theorem centeredDivisorHyperbolaAbel_mean_error (M : ℕ) :
    |centeredDivisorHyperbolaAbel M+(Nat.sqrt M:ℝ)/24-
      halfOrderAbelStep 0 M*(∑ d ∈ Icc 1 (Nat.sqrt M),
        (centeredModularMeanMagnitude d+centeredModularPrimitive d M))|≤
        (5/48:ℝ)*((harmonic (Nat.sqrt M):ℚ):ℝ) := by
  change |centeredDivisorHyperbolaAbel M+(Nat.sqrt M:ℝ)/24-
    halfOrderAbelStep 0 M*terminalSum M|≤_
  let f := fun d => (∑ k ∈ Ico (d*d) M,centeredModularRamp d k*halfOrderAbelStep 0 k)+1/24-
    (centeredModularMeanMagnitude d+centeredModularPrimitive d M)*halfOrderAbelStep 0 M
  have hpoint (d : ℕ) (hd : d ∈ Icc 1 (Nat.sqrt M)) : |f d|≤5/(48*(d:ℝ)) := by
    have hdpos : 0<d := (mem_Icc.mp hd).1
    have herr := abs_le.mp (abs_centeredModularRamp_halfOrder_Ico_mean_error_le hdpos
      (Nat.le_sqrt.mp (mem_Icc.mp hd).2))
    have hB := birth_mean_error hdpos
    have he : 1/(48*(d:ℝ))+1/(12*(d:ℝ))=5/(48*(d:ℝ)) := by ring
    apply abs_le.mpr
    dsimp [f]
    constructor <;> linarith only [herr.1,herr.2,hB.1,hB.2,he]
  have hid : centeredDivisorHyperbolaAbel M+(Nat.sqrt M:ℝ)/24-
      halfOrderAbelStep 0 M*terminalSum M=∑ d ∈ Icc 1 (Nat.sqrt M),f d := by
    simp only [f,sum_sub_distrib,sum_add_distrib,← sum_mul,terminalSum]
    rw [← centered_birth_channels_through_sqrt]
    simp
    ring
  rw [hid]
  calc
    _ ≤ ∑ d ∈ Icc 1 (Nat.sqrt M),|f d| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Icc 1 (Nat.sqrt M),5/(48*(d:ℝ)) := sum_le_sum hpoint
    _ = _ := by
      simp_rw [show ∀ d : ℕ,5/(48*(d:ℝ))=(5/48)*(1/(d:ℝ)) by intro d; ring]
      rw [← mul_sum]
      simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,one_div]

private lemma sqrt_inv_tendsto : Tendsto (fun M : ℕ => (Real.sqrt (M:ℝ))⁻¹) atTop (𝓝 0) := by
  exact tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)

private lemma log_div_sqrt_tendsto :
    Tendsto (fun M : ℕ => Real.log M/Real.sqrt M) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_atTop (r:=(1:ℝ)/2) (by norm_num)).tendsto_div_nhds_zero
  simpa only [Real.sqrt_eq_rpow,Function.comp_def] using h.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun M : ℕ => (M:ℝ)) atTop atTop)

private lemma harmonic_sqrt_cutoff_tendsto :
    Tendsto (fun M : ℕ => ((harmonic (Nat.sqrt M):ℚ):ℝ)/Real.sqrt M) atTop (𝓝 0) := by
  have hnonneg (n : ℕ) : (0:ℚ)≤harmonic n := by
    rw [harmonic_eq_sum_Icc]
    exact sum_nonneg (fun _ _ => by positivity)
  have hlim : Tendsto (fun M : ℕ => (1+Real.log M)/Real.sqrt M) atTop (𝓝 0) := by
    simpa only [add_div,one_div,zero_add] using sqrt_inv_tendsto.add log_div_sqrt_tendsto
  apply squeeze_zero' (Eventually.of_forall (fun M =>
    div_nonneg (by exact_mod_cast hnonneg (Nat.sqrt M)) (Real.sqrt_nonneg _))) _ hlim
  filter_upwards [eventually_ge_atTop (1:ℕ)] with M hM
  have hN : 1≤Nat.sqrt M := Nat.le_sqrt.mpr (by simpa using hM)
  have hn : (0:ℝ)<Nat.sqrt M := by exact_mod_cast hN
  have hlog := Real.log_le_log hn (show (Nat.sqrt M:ℝ)≤(M:ℝ) by exact_mod_cast Nat.sqrt_le_self M)
  exact div_le_div_of_nonneg_right (by linarith only [hlog,harmonic_le_one_add_log (Nat.sqrt M)])
    (Real.sqrt_nonneg _)

private lemma nat_sqrt_div_sqrt_tendsto :
    Tendsto (fun M : ℕ => (Nat.sqrt M:ℝ)/Real.sqrt M) atTop (𝓝 1) := by
  have he : Tendsto (fun M : ℕ => 1-(Nat.sqrt M:ℝ)/Real.sqrt M) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ sqrt_inv_tendsto
    · filter_upwards [eventually_ge_atTop (1:ℕ)] with M hM
      have hs : 0<Real.sqrt (M:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hM)
      have h := Real.nat_sqrt_le_real_sqrt (a:=M)
      rw [sub_nonneg,div_le_one hs]
      exact h
    · filter_upwards [eventually_ge_atTop (1:ℕ)] with M hM
      have hs : 0<Real.sqrt (M:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hM)
      have h := Real.real_sqrt_le_nat_sqrt_succ (a:=M)
      rw [← one_div,le_div_iff₀ hs]
      have he : (1-(Nat.sqrt M:ℝ)/Real.sqrt M)*Real.sqrt M=Real.sqrt M-(Nat.sqrt M:ℝ) := by field_simp
      rw [he]
      linarith only [h]
  have h := (tendsto_const_nhds (x:=(1:ℝ))).sub he
  simpa only [sub_sub_cancel,sub_zero] using h

private lemma terminal_boundary_tendsto :
    Tendsto (fun M : ℕ => halfOrderAbelStep 0 M*terminalSum M/Real.sqrt M) atTop (𝓝 0) := by
  have hlim : Tendsto (fun M : ℕ => |terminalSum M/(M:ℝ)|) atTop (𝓝 0) := by
    simpa only [abs_zero,terminalSum] using tendsto_terminal_modular_mean.abs
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
  filter_upwards [eventually_ge_atTop (1:ℕ)] with M hM
  have hm : (0:ℝ)<M := by exact_mod_cast hM
  have hs : 0<Real.sqrt (M:ℝ) := Real.sqrt_pos.mpr hm
  let w := halfOrderAbelStep 0 M
  have hw : 0≤w := halfOrderAbelStep_nonneg _ _
  have hs2 := Real.sq_sqrt hm.le
  have hsu := Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) (M+1))
  have hc : 2*Real.sqrt M*w+w^2=1 := by
    dsimp [w,halfOrderAbelStep]
    push_cast at hsu ⊢
    simp only [zero_add]
    nlinarith only [hs2,hsu]
  have hbound : w*Real.sqrt M≤1 := by nlinarith only [hc,sq_nonneg w]
  have heq : w*terminalSum M/Real.sqrt M=(w*Real.sqrt M)*(terminalSum M/(M:ℝ)) := by
    field_simp
    nlinarith only [congrArg (fun x : ℝ => w*terminalSum M*x) hs2]
  change ‖w*terminalSum M/Real.sqrt M‖≤_
  rw [Real.norm_eq_abs,heq,abs_mul,abs_of_nonneg (mul_nonneg hw hs.le)]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hbound (abs_nonneg (terminalSum M/(M:ℝ)))

/-- The complete centered hyperbola has exact half-order coefficient `-1/24`. -/
theorem tendsto_centeredDivisorHyperbolaAbel_div_sqrt :
    Tendsto (fun M : ℕ => centeredDivisorHyperbolaAbel M/Real.sqrt M) atTop (𝓝 (-1/24)) := by
  have hlim : Tendsto (fun M : ℕ => (5/48:ℝ)*((harmonic (Nat.sqrt M):ℚ):ℝ)/Real.sqrt M)
      atTop (𝓝 0) := by
    simpa only [mul_zero,mul_div_assoc] using harmonic_sqrt_cutoff_tendsto.const_mul (5/48:ℝ)
  have herr : Tendsto (fun M : ℕ =>
      centeredDivisorHyperbolaAbel M/Real.sqrt M+(Nat.sqrt M:ℝ)/Real.sqrt M/24-
        halfOrderAbelStep 0 M*terminalSum M/Real.sqrt M) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
    apply Eventually.of_forall
    intro M
    have h := div_le_div_of_nonneg_right (centeredDivisorHyperbolaAbel_mean_error M)
      (Real.sqrt_nonneg (M:ℝ))
    have heq : centeredDivisorHyperbolaAbel M/Real.sqrt M+(Nat.sqrt M:ℝ)/Real.sqrt M/24-
        halfOrderAbelStep 0 M*terminalSum M/Real.sqrt M =
      (centeredDivisorHyperbolaAbel M+(Nat.sqrt M:ℝ)/24-halfOrderAbelStep 0 M*terminalSum M)/Real.sqrt M := by ring
    rw [Real.norm_eq_abs,heq,abs_div,abs_of_nonneg (Real.sqrt_nonneg _)]
    exact h
  have h := (herr.sub (nat_sqrt_div_sqrt_tendsto.div_const 24)).add terminal_boundary_tendsto
  convert h using 1
  · ext M; ring
  · norm_num

private lemma smooth_abel_div_sqrt_tendsto :
    Tendsto (fun M : ℕ => divisorHyperbolaSmoothAbel M/Real.sqrt M) atTop
      (𝓝 divisorHyperbolaSmoothMean) := by
  let a := divisorHyperbolaSmoothMean
  have hlim : Tendsto (fun M : ℕ => (9*Real.log M+34+|a|)/Real.sqrt M) atTop (𝓝 0) := by
    have h := (log_div_sqrt_tendsto.const_mul 9).add (sqrt_inv_tendsto.const_mul (34+|a|))
    simpa only [mul_zero,zero_add,div_eq_mul_inv,add_mul,mul_assoc,add_assoc] using h
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
  filter_upwards [eventually_ge_atTop (1:ℕ)] with M hM
  have hm : (0:ℝ)<M := by exact_mod_cast hM
  have hs : 0<Real.sqrt (M:ℝ) := Real.sqrt_pos.mpr hm
  have hlog : Real.log ((M:ℝ)+1)≤Real.log M+1 := by
    have h := Real.log_le_log (by positivity : (0:ℝ)<M+1)
      (show (M:ℝ)+1≤2*(M:ℝ) by
        have hm1 : (1:ℝ)≤M := by exact_mod_cast hM
        linarith only [hm1])
    rw [Real.log_mul (by norm_num) hm.ne'] at h
    have h2 : Real.log (2:ℝ)≤1 := by
      have hb := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
      norm_num at hb
      exact hb
    linarith only [h,h2]
  have hb := divisorHyperbolaSmoothAbel_mean_error M
  have heq : divisorHyperbolaSmoothAbel M/Real.sqrt M-a=
      (divisorHyperbolaSmoothAbel M-a*Real.sqrt M)/Real.sqrt M := by field_simp
  change ‖divisorHyperbolaSmoothAbel M/Real.sqrt M-a‖≤_
  rw [Real.norm_eq_abs,heq,abs_div,abs_of_nonneg hs.le]
  apply div_le_div_of_nonneg_right _ hs.le
  change |divisorHyperbolaSmoothAbel M-a*Real.sqrt M|≤_ at hb
  linarith only [hb,hlog]

/-- The literal unsigned unit channel has an exact leading coefficient. -/
theorem tendsto_divisorUnsignedDilationChannel_one_div_sqrt :
    Tendsto (fun M : ℕ => divisorUnsignedDilationChannel M 1/Real.sqrt M) atTop
      (𝓝 (Real.log (2*Real.pi)/2-Real.eulerMascheroniConstant-1/4)) := by
  have h := smooth_abel_div_sqrt_tendsto.add (tendsto_centeredDivisorHyperbolaAbel_div_sqrt.const_mul 2)
  convert h using 1
  · ext M
    have hid := mobiusDivisorDilationChannel_one_eq_hyperbola M
    rw [mobiusDivisorDilationChannel_eq_moebius_unsigned] at hid
    simp only [ArithmeticFunction.moebius_apply_one,Int.cast_one,one_mul] at hid
    rw [hid]
    ring
  · unfold divisorHyperbolaSmoothMean
    ring

/-- The exact leading coefficient holds uniformly in all positive dilation indices
on a common quotient tail, with the clipped endpoint included. -/
theorem exists_divisorUnsignedDilationChannel_uniform_mean_error (ε : ℝ) (hε : 0<ε) :
    ∃ T : ℕ,1≤T ∧ ∀ M d : ℕ,0<d → T≤M/d →
      |divisorUnsignedDilationChannel M d-
        (Real.log (2*Real.pi)/2-Real.eulerMascheroniConstant-1/4)*Real.sqrt M|≤ε*Real.sqrt M := by
  let c := Real.log (2*Real.pi)/2-Real.eulerMascheroniConstant-1/4
  obtain ⟨T,hT⟩ := Metric.tendsto_atTop.mp tendsto_divisorUnsignedDilationChannel_one_div_sqrt ε hε
  have hunit (N : ℕ) (hNT : T≤N) (hN1 : 1≤N) :
      (c-ε)*Real.sqrt N≤divisorUnsignedDilationChannel N 1 ∧
      divisorUnsignedDilationChannel N 1≤(c+ε)*Real.sqrt N := by
    have hn : 0<Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hN1)
    have h := hT N hNT
    rw [Real.dist_eq] at h
    change |divisorUnsignedDilationChannel N 1/Real.sqrt N-c|<ε at h
    obtain ⟨hl,hu⟩ := abs_lt.mp h
    constructor
    · apply (le_div_iff₀ hn).mp
      linarith only [hl]
    · apply (div_le_iff₀ hn).mp
      linarith only [hu]
  refine ⟨max T 1,le_max_right _ _,?_⟩
  intro M d hd hMd
  have hN : T≤M/d := (le_max_left _ _).trans hMd
  have hN1 : 1≤M/d := (le_max_right _ _).trans hMd
  have hA := hunit (M/d) hN hN1
  have hB := hunit (M/d+1) (by omega) (by omega)
  have hw0 := divisorPrimeClipWeight_nonneg M d hd
  have hw1 : 0≤1-divisorPrimeClipWeight M d := by
    have h := divisorPrimeClipWeight_lt_one M d hd
    linarith only [h]
  have hc := divisorUnsignedDilationChannel_prime_interpolation M d 1 hd
  simp only [Nat.mul_one] at hc
  have hclock := divisorPrimeClipWeight_mul_step M d hd
  push_cast at hclock
  rw [Real.sqrt_mul (Nat.cast_nonneg d)] at hclock
  have hclock' : Real.sqrt (d:ℝ)*
      ((1-divisorPrimeClipWeight M d)*Real.sqrt (M/d:ℕ)+
        divisorPrimeClipWeight M d*Real.sqrt (M/d+1:ℕ))=Real.sqrt M := by
    push_cast
    nlinarith only [hclock]
  have hlow := mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left hA.1 hw1) (mul_le_mul_of_nonneg_left hB.1 hw0))
    (Real.sqrt_nonneg (d:ℝ))
  have hupp := mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left hA.2 hw1) (mul_le_mul_of_nonneg_left hB.2 hw0))
    (Real.sqrt_nonneg (d:ℝ))
  have hLc := congrArg (fun x : ℝ => (c-ε)*x) hclock'
  have hUc := congrArg (fun x : ℝ => (c+ε)*x) hclock'
  change |divisorUnsignedDilationChannel M d-c*Real.sqrt M|≤_
  apply abs_le.mpr
  rw [hc]
  constructor <;> nlinarith only [hlow,hupp,hLc,hUc]

end RHTower
