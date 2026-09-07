import GaloisForLFunctions.HTGeometry.SecondCenteredModularAbel
import GaloisForLFunctions.RHTower.DivisorHyperbolaPositivePrefix
import GaloisForLFunctions.RHTower.MobiusDivisorAbelQuadraticDiagonal
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Second-centered bounds for the actual divisor hyperbola

The period mean and terminal residue of every centered modular birth are
retained exactly, leaving only a harmonic error. The complete centered term
has a strictly negative square-root band. Combining it with the smooth
prefix floor gives the unsigned unit channel a one-sixteenth square-root
floor with logarithmic error.
-/

noncomputable section
open Finset Filter Topology HTGeometry
namespace RHTower

private theorem modular_mean_birth_bounds {d M : ℕ} (hd : 0<d) (hM : d*d≤M) :
    let B := centeredModularMeanMagnitude d
    let w := halfOrderAbelStep (d*d) 0
    (1/24-1/(12*(d:ℝ)) ≤ B*w ∧ B*w ≤ 1/24) ∧
    (0 ≤ B ∧ B ≤ (d:ℝ)/12) ∧
    halfOrderAbelStep 0 M ≤ 1/2 := by
  dsimp only
  let w := halfOrderAbelStep (d*d) 0
  have hdR : (0:ℝ)<d := by positivity
  have hd1 : (1:ℝ)≤d := by exact_mod_cast hd
  have hw0 : 0≤w := halfOrderAbelStep_nonneg _ _
  have hbd : (d:ℝ)*w ≤ 1/2 := halfOrderAbelStep_square_initial d
  have hw : w ≤ 1/2 := by nlinarith only [hbd,mul_nonneg (sub_nonneg.mpr hd1) hw0]
  have hmono : halfOrderAbelStep 0 M≤w := by
    simpa only [w,halfOrderAbelStep,Nat.zero_add,Nat.add_zero] using halfOrderAbelStep_antitone 0 hM
  have hs := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) (d*d+1))
  have heq : 2*(d:ℝ)*w+w^2=1 := by
    dsimp [w,halfOrderAbelStep]
    simp only [Nat.cast_mul,Real.sqrt_mul_self (Nat.cast_nonneg d)]
    push_cast at hs ⊢
    nlinarith only [hs]
  have hquad : (d:ℝ)*w^2 ≤ 1/4 := by
    have h := mul_le_mul_of_nonneg_right hbd hw0
    nlinarith only [h,hw]
  have hscaled := congrArg (fun x : ℝ => (d:ℝ)*x) heq
  have hB0 : 0 ≤ centeredModularMeanMagnitude d := by
    unfold centeredModularMeanMagnitude
    apply div_nonneg _ (by positivity)
    nlinarith only [hd1]
  have hB : centeredModularMeanMagnitude d ≤ (d:ℝ)/12 := by
    unfold centeredModularMeanMagnitude
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hBu := mul_le_mul_of_nonneg_right hB hw0
  have hBl : 1/24-1/(12*(d:ℝ)) ≤ centeredModularMeanMagnitude d*w := by
    unfold centeredModularMeanMagnitude
    field_simp [hdR.ne']
    nlinarith only [hscaled,hquad,hw]
  exact ⟨⟨hBl,by nlinarith only [hBu,hbd]⟩,⟨hB0,hB⟩,hmono.trans hw⟩

/-- Every active modular hyperbola channel retains its negative mean with a harmonic-sized error. -/
theorem centeredDivisorBirthChannel_second_bounds {d M : ℕ} (hd : 0<d) (hM : d*d≤M) :
    -1/24-(d:ℝ)/24*halfOrderAbelStep 0 M-1/(16*(d:ℝ)) ≤
      (∑ k ∈ Ico (d*d) M,centeredModularRamp d k*halfOrderAbelStep 0 k) ∧
    (∑ k ∈ Ico (d*d) M,centeredModularRamp d k*halfOrderAbelStep 0 k) ≤
      -1/24+(d:ℝ)/12*halfOrderAbelStep 0 M+5/(48*(d:ℝ)) := by
  have herr := abs_le.mp (abs_centeredModularRamp_halfOrder_Ico_mean_error_le hd hM)
  obtain ⟨hBirth,hB,hw⟩ := modular_mean_birth_bounds hd hM
  have hw0 := halfOrderAbelStep_nonneg 0 M
  have hP := centeredModularPrimitive_bounds d M
  have hendU : (centeredModularMeanMagnitude d+centeredModularPrimitive d M)*halfOrderAbelStep 0 M ≤
      (d:ℝ)/12*halfOrderAbelStep 0 M :=
    mul_le_mul_of_nonneg_right (by linarith only [hB.2,hP.2]) hw0
  have hBexact : centeredModularMeanMagnitude d=(d:ℝ)/12-1/(12*(d:ℝ)) := by
    unfold centeredModularMeanMagnitude
    field_simp
  have hcoef : -(d:ℝ)/24-1/(12*(d:ℝ)) ≤
      centeredModularMeanMagnitude d+centeredModularPrimitive d M := by
    rw [hBexact]
    linarith only [hP.1]
  have hendL := mul_le_mul_of_nonneg_right hcoef hw0
  have hsmall := mul_le_mul_of_nonneg_left hw (show (0:ℝ)≤1/(12*(d:ℝ)) by positivity)
  have hnorm : 1/(12*(d:ℝ))*(1/2)+1/(48*(d:ℝ))=1/(16*(d:ℝ)) := by ring
  have hnormU : 1/(12*(d:ℝ))+1/(48*(d:ℝ))=5/(48*(d:ℝ)) := by ring
  constructor <;> nlinarith only [herr.1,herr.2,hBirth.1,hBirth.2,hendL,hendU,hsmall,hnorm,hnormU]

private theorem sum_nat_cast_Icc (s : ℕ) :
    (∑ d ∈ Icc 1 s,(d:ℝ))=(s:ℝ)*(s+1)/2 := by
  induction s with
  | zero => simp
  | succ s ih => rw [sum_Icc_succ_top (by omega),ih]; push_cast; ring

/-- Summing every actual square birth gives two explicit centered-source bounds with only harmonic error. -/
theorem centeredDivisorHyperbolaAbel_second_bounds (M : ℕ) :
    let s : ℝ := Nat.sqrt (M-1);
    -s/24-s*(s+1)/48*halfOrderAbelStep 0 M-((harmonic (Nat.sqrt (M-1)):ℚ):ℝ)/16 ≤
      centeredDivisorHyperbolaAbel M ∧
    centeredDivisorHyperbolaAbel M ≤
      -s/24+s*(s+1)/24*halfOrderAbelStep 0 M+5*((harmonic (Nat.sqrt (M-1)):ℚ):ℝ)/48 := by
  let s := Nat.sqrt (M-1)
  have hlo (d : ℕ) (hd : d ∈ Icc 1 s) := (centeredDivisorBirthChannel_second_bounds
    (show 0<d by have := (mem_Icc.mp hd).1; omega)
    (show d*d≤M by have h := Nat.le_sqrt.mp (mem_Icc.mp hd).2; omega)).1
  have hhi (d : ℕ) (hd : d ∈ Icc 1 s) := (centeredDivisorBirthChannel_second_bounds
    (show 0<d by have := (mem_Icc.mp hd).1; omega)
    (show d*d≤M by have h := Nat.le_sqrt.mp (mem_Icc.mp hd).2; omega)).2
  have hL := sum_le_sum hlo
  have hU := sum_le_sum hhi
  rw [← centeredDivisorHyperbolaAbel_eq_birth_channels] at hL hU
  have hrec : (∑ d ∈ Icc 1 s,1/(d:ℝ))=((harmonic s:ℚ):ℝ) := by
    simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,one_div]
  have hrec16 : (∑ d ∈ Icc 1 s,1/(16*(d:ℝ)))=((harmonic s:ℚ):ℝ)/16 := by
    simp_rw [show ∀ d : ℕ,1/(16*(d:ℝ))=(1/(d:ℝ))/16 by intro d; ring]
    rw [← sum_div,hrec]
  have hrec48 : (∑ d ∈ Icc 1 s,5/(48*(d:ℝ)))=5*((harmonic s:ℚ):ℝ)/48 := by
    simp_rw [show ∀ d : ℕ,5/(48*(d:ℝ))=(5*(1/(d:ℝ)))/48 by intro d; ring]
    rw [← sum_div,← mul_sum,hrec]
  simp only [sum_sub_distrib,sum_add_distrib,sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul,
    ← sum_mul,← sum_div,sum_nat_cast_Icc,hrec16,hrec48] at hL hU
  dsimp only
  change -(s:ℝ)/24-(s:ℝ)*(s+1)/48*halfOrderAbelStep 0 M-((harmonic s:ℚ):ℝ)/16 ≤ _ ∧ _
  constructor <;> nlinarith only [hL,hU]

/-- The complete centered hyperbola has strictly negative square-root scale, up to an explicit logarithmic error. -/
theorem centeredDivisorHyperbolaAbel_sqrt_log_bounds (M : ℕ) :
    -5*Real.sqrt M/96-Real.log ((M:ℝ)+1)/16-7/96 ≤ centeredDivisorHyperbolaAbel M ∧
    centeredDivisorHyperbolaAbel M ≤ -Real.sqrt M/48+5*Real.log ((M:ℝ)+1)/48+1/6 := by
  by_cases hM : M=0
  · subst M
    norm_num [centeredDivisorHyperbolaAbel]
  let s := Nat.sqrt (M-1)
  have hs0 : (0:ℝ)≤ s := Nat.cast_nonneg _
  have hM1 : 1≤M := by omega
  have hMpos : (0:ℝ)<M := by positivity
  have hroot := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) M)
  have hsR : (s:ℝ)≤Real.sqrt M :=
    (Real.nat_sqrt_le_real_sqrt (a := M-1)).trans
      (Real.sqrt_le_sqrt (by exact_mod_cast (show M-1≤M by omega)))
  have hMsq : (M:ℝ)≤((s:ℝ)+1)^2 := by
    have h := Nat.lt_succ_sqrt (M-1)
    change M-1<(s+1)*(s+1) at h
    have h' : M≤(s+1)*(s+1) := by omega
    rw [pow_two]
    exact_mod_cast h'
  have hRs : Real.sqrt M≤(s:ℝ)+1 := by
    nlinarith only [hMsq,hroot,hs0,Real.sqrt_nonneg (M:ℝ)]
  have hw0 := halfOrderAbelStep_nonneg 0 M
  have hclock : Real.sqrt M*halfOrderAbelStep 0 M≤1/2 := by
    have hnext := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) (M+1))
    have hsq := sq_nonneg (halfOrderAbelStep 0 M)
    simp only [halfOrderAbelStep,Nat.zero_add] at hsq ⊢
    push_cast at hnext hsq ⊢
    nlinarith only [hroot,hnext,hsq]
  have hsw : (s:ℝ)*halfOrderAbelStep 0 M≤1/2 :=
    (mul_le_mul_of_nonneg_right hsR hw0).trans hclock
  have hprod : (s:ℝ)*(s+1)*halfOrderAbelStep 0 M≤(Real.sqrt M+1)/2 := by
    have h := mul_le_mul_of_nonneg_right hsw (show (0:ℝ)≤(s:ℝ)+1 by positivity)
    nlinarith only [h,hsR]
  have hH : ((harmonic s:ℚ):ℝ)≤1+Real.log ((M:ℝ)+1) := by
    by_cases hs : s=0
    · simp only [hs,harmonic_zero,Rat.cast_zero]
      have hlog := Real.log_nonneg (show (1:ℝ)≤(M:ℝ)+1 by have := Nat.cast_nonneg (α := ℝ) M; linarith)
      linarith only [hlog]
    have hsM : (s:ℝ)≤(M:ℝ)+1 := by
      have h := Nat.sqrt_le_self (M-1)
      exact_mod_cast (show s≤M+1 by dsimp [s]; omega)
    have hl := Real.log_le_log (show (0:ℝ)<s by positivity) hsM
    have hh := harmonic_le_one_add_log s
    linarith only [hl,hh]
  have hb := centeredDivisorHyperbolaAbel_second_bounds M
  change -(s:ℝ)/24-(s:ℝ)*(s+1)/48*halfOrderAbelStep 0 M-((harmonic s:ℚ):ℝ)/16 ≤ _ ∧ _ at hb
  constructor <;> nlinarith only [hb.1,hb.2,hsR,hRs,hprod,hH]

private theorem eventually_log_add_one_le_sqrt (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ M : ℕ in atTop,Real.log ((M:ℝ)+1)+1≤ε*Real.sqrt M := by
  have hlog : Tendsto (fun M : ℕ => Real.log M/Real.sqrt M) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_atTop (r := (1:ℝ)/2) (by norm_num)).tendsto_div_nhds_zero
    simpa only [Real.sqrt_eq_rpow,Function.comp_def] using
      h.comp (tendsto_natCast_atTop_atTop : Tendsto (fun M : ℕ => (M:ℝ)) atTop atTop)
  have hroot : Tendsto (fun M : ℕ => Real.sqrt M) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hinv := tendsto_inv_atTop_zero.comp hroot
  have hlim : Tendsto (fun M : ℕ => (Real.log M+2)/Real.sqrt M) atTop (𝓝 0) := by
    have h := hlog.add (hinv.const_mul 2)
    simpa only [Function.comp_def,mul_zero,zero_add,add_div,div_eq_mul_inv,add_mul] using h
  have hev : ∀ᶠ M : ℕ in atTop,(Real.log M+2)/Real.sqrt M<ε :=
    hlim.eventually (gt_mem_nhds hε)
  filter_upwards [hev,eventually_ge_atTop 1] with M hsmall hM
  have hMp : (0:ℝ)<M := by positivity
  have hrootp : 0<Real.sqrt M := Real.sqrt_pos.mpr hMp
  have hlog' := Real.log_le_sub_one_of_pos (x := ((M:ℝ)+1)/M) (by positivity)
  rw [Real.log_div (by positivity) hMp.ne'] at hlog'
  have hrat : ((M:ℝ)+1)/M-1≤1 := by
    rw [sub_le_iff_le_add,div_le_iff₀ hMp]
    have : (1:ℝ)≤M := by exact_mod_cast hM
    linarith only [this]
  have hm := (div_lt_iff₀ hrootp).mp hsmall
  linarith only [hm,hlog',hrat]

/-- The actual centered response is trapped between two negative square-root coefficients with arbitrarily small relative error. -/
theorem eventually_centeredDivisorHyperbolaAbel_scaled_bounds (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ M : ℕ in atTop,(-5/96-ε)*Real.sqrt M ≤ centeredDivisorHyperbolaAbel M ∧
      centeredDivisorHyperbolaAbel M ≤ (-1/48+ε)*Real.sqrt M := by
  filter_upwards [eventually_log_add_one_le_sqrt ε hε] with M herror
  have hlog := Real.log_nonneg (show (1:ℝ)≤(M:ℝ)+1 by have := Nat.cast_nonneg (α := ℝ) M; linarith)
  have hb := centeredDivisorHyperbolaAbel_sqrt_log_bounds M
  constructor <;> nlinarith only [herror,hlog,hb.1,hb.2]

/-- The centered arithmetic contribution tends to negative infinity, with a proved square-root scale. -/
theorem tendsto_centeredDivisorHyperbolaAbel_atBot :
    Tendsto centeredDivisorHyperbolaAbel atTop atBot := by
  apply tendsto_atBot.2
  intro B
  have hroot : Tendsto (fun M : ℕ => Real.sqrt M) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hev := hroot.eventually_ge_atTop (-96*B)
  filter_upwards [eventually_centeredDivisorHyperbolaAbel_scaled_bounds (1/96) (by norm_num),hev] with M hM hB
  nlinarith only [hM.2,hB]

private theorem sqrt_mul_clock_gap_le {k : ℕ} (hk : 0<k) :
    Real.sqrt k*(halfOrderAbelStep 0 k-halfOrderAbelStep 0 (k+1))≤1/(4*(k:ℝ)) := by
  rw [halfOrderAbelStep_gap_eq]
  simp only [Nat.zero_add]
  have h1 : Real.sqrt k≤Real.sqrt (k+1:ℕ) := Real.sqrt_le_sqrt (by exact_mod_cast (show k≤k+1 by omega))
  have h2 : Real.sqrt k≤Real.sqrt (k+2:ℕ) := Real.sqrt_le_sqrt (by exact_mod_cast (show k≤k+2 by omega))
  have hden : (2*Real.sqrt k)^3 ≤
      (Real.sqrt k+Real.sqrt (k+1:ℕ))*(Real.sqrt (k+1:ℕ)+Real.sqrt (k+2:ℕ))*
      (Real.sqrt k+Real.sqrt (k+2:ℕ)) := by
    have h := mul_le_mul (mul_le_mul
      (by linarith only [h1] : 2*Real.sqrt k≤Real.sqrt k+Real.sqrt (k+1:ℕ))
      (by linarith only [h1,h2] : 2*Real.sqrt k≤Real.sqrt (k+1:ℕ)+Real.sqrt (k+2:ℕ))
      (by positivity) (by positivity))
      (by linarith only [h2] : 2*Real.sqrt k≤Real.sqrt k+Real.sqrt (k+2:ℕ))
      (by positivity) (by positivity)
    nlinarith only [h]
  have hs := congrArg (fun x : ℝ => 8*Real.sqrt k*x) (Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) k))
  rw [← mul_div_assoc,div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith only [hden,hs]

/-- Retaining the square-root prefix error avoids losing half the smooth main coefficient. -/
theorem sum_divisorHyperbolaSmoothRemainder_ge_linear_sqrt (N : ℕ) :
    (N:ℝ)/6-17*Real.sqrt N≤∑ k ∈ Icc 1 N,divisorHyperbolaSmoothRemainder k := by
  by_cases hN : N=0
  · simp [hN]
  have h := sum_divisorHyperbolaSmoothRemainder_ge (show 1≤N by omega)
  have hs := Real.nat_sqrt_le_real_sqrt (a := N)
  have hhi : (N:ℝ)≤(Nat.sqrt N:ℝ)^2+2*Nat.sqrt N := by
    have hn := Nat.sqrt_le_add N
    rw [pow_two]
    exact_mod_cast (show N≤Nat.sqrt N*Nat.sqrt N+2*Nat.sqrt N by omega)
  have hz : (0:ℝ)≤Nat.sqrt N := Nat.cast_nonneg _
  nlinarith only [h,hs,hhi,hz]

/-- The actual smooth Abel source has a one-sixth square-root floor with only logarithmic loss. -/
theorem divisorHyperbolaSmoothAbel_ge_sqrt_log (M : ℕ) :
    Real.sqrt M/6-17*Real.log ((M:ℝ)+1)/4-13≤divisorHyperbolaSmoothAbel M := by
  by_cases hM : M≤1
  · have hz : divisorHyperbolaSmoothAbel M=0 := by
      interval_cases M <;> norm_num [divisorHyperbolaSmoothAbel,divisorHyperbolaSmoothRemainder]
    have hr : Real.sqrt M≤1 := by simpa using Real.sqrt_le_sqrt (show (M:ℝ)≤1 by exact_mod_cast hM)
    have hl := Real.log_nonneg (show (1:ℝ)≤(M:ℝ)+1 by have := Nat.cast_nonneg (α := ℝ) M; linarith)
    rw [hz]
    nlinarith only [hr,hl]
  let N := M-1
  let w := halfOrderAbelStep 0
  let f := fun k => divisorHyperbolaSmoothRemainder k-1/6
  have hN : 1≤N := by dsimp [N]; omega
  have hMN : N+1=M := by dsimp [N]; omega
  have hpre (n : ℕ) : -17*Real.sqrt n≤∑ k ∈ Icc 1 n,f k := by
    have h := sum_divisorHyperbolaSmoothRemainder_ge_linear_sqrt n
    simp only [f,sum_sub_distrib,sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul]
    linarith only [h]
  have hg (k : ℕ) : 0≤w k-w (k+1) := sub_nonneg.mpr (halfOrderAbelStep_antitone 0 (show k≤k+1 by omega))
  have hs := sum_le_sum (fun k (_hk : k ∈ Icc 1 N) => mul_le_mul_of_nonneg_right (hpre k) (hg k))
  have hb := sum_le_sum (fun k (hk : k ∈ Icc 1 N) => sqrt_mul_clock_gap_le (show 0<k by have := (mem_Icc.mp hk).1; omega))
  have hrec : (∑ k ∈ Icc 1 N,1/(4*(k:ℝ)))=((harmonic N:ℚ):ℝ)/4 := by
    simp_rw [show ∀ k : ℕ,1/(4*(k:ℝ))=(1/(k:ℝ))/4 by intro k; ring]
    rw [← sum_div]
    simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,one_div]
  rw [hrec] at hb
  have hrootclock : Real.sqrt N*w (N+1)≤1/2 := by
    have h0 := mul_le_mul_of_nonneg_left (halfOrderAbelStep_antitone 0 (show N≤N+1 by omega)) (Real.sqrt_nonneg (N:ℝ))
    have h1 := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) (N+1))
    have h2 := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) N)
    have h3 := sq_nonneg (w N)
    dsimp [w,halfOrderAbelStep] at h0 h3 ⊢
    push_cast at h0 h1 h2 h3 ⊢
    simp only [zero_add] at h0 h3 ⊢
    nlinarith only [h0,h1,h2,h3]
  have ht := mul_le_mul_of_nonneg_right (hpre N) (halfOrderAbelStep_nonneg 0 (N+1))
  have hab := sum_mul_eq_partial_mul_diff_ring f w N
  have hw : (∑ k ∈ Icc 1 N,w k)=Real.sqrt M-1 := by
    have ht := sum_sqrt_succ_sub_sqrt_Icc_general hN
    simpa only [w,halfOrderAbelStep,Nat.zero_add,hMN,Nat.cast_one,Real.sqrt_one] using ht
  have hSmooth : (∑ k ∈ Icc 1 N,divisorHyperbolaSmoothRemainder k*w k)=divisorHyperbolaSmoothAbel M := by
    rw [← Ico_add_one_right_eq_Icc,hMN,sum_Ico_eq_sub _ (show 1≤M by omega)]
    have hz : divisorHyperbolaSmoothRemainder 0=0 := by norm_num [divisorHyperbolaSmoothRemainder]
    simp only [sum_range_one,hz,zero_mul,sub_zero,divisorHyperbolaSmoothAbel,w]
  have hleft : (∑ k ∈ Icc 1 N,f k*w k)=divisorHyperbolaSmoothAbel M-(Real.sqrt M-1)/6 := by
    simp only [f,sub_mul,sum_sub_distrib,← mul_sum]
    rw [hSmooth,hw]
    ring
  have hH : ((harmonic N:ℚ):ℝ)≤1+Real.log ((M:ℝ)+1) := by
    have hl := Real.log_le_log (show (0:ℝ)<N by positivity)
      (show (N:ℝ)≤(M:ℝ)+1 by exact_mod_cast (show N≤M+1 by omega))
    linarith only [hl,harmonic_le_one_add_log N]
  rw [hleft] at hab
  simp only [mul_assoc,← mul_sum] at hs
  change _ ≤ (harmonic N:ℝ)/4 at hb
  change -17*Real.sqrt N*w (N+1)≤_ at ht
  nlinarith only [hs,hb,ht,hab,hrootclock,hH]

/-- Second centering gives the literal unsigned unit channel a one-sixteenth square-root floor with logarithmic error. -/
theorem divisorUnsignedDilationChannel_one_ge_sqrt_log (M : ℕ) :
    Real.sqrt M/16-5*Real.log ((M:ℝ)+1)-14≤divisorUnsignedDilationChannel M 1 := by
  have hid := mobiusDivisorDilationChannel_one_eq_hyperbola M
  rw [mobiusDivisorDilationChannel_eq_moebius_unsigned] at hid
  simp only [ArithmeticFunction.moebius_apply_one,Int.cast_one,one_mul] at hid
  have hs := divisorHyperbolaSmoothAbel_ge_sqrt_log M
  have hc := (centeredDivisorHyperbolaAbel_sqrt_log_bounds M).1
  have hl := Real.log_nonneg (show (1:ℝ)≤(M:ℝ)+1 by have := Nat.cast_nonneg (α := ℝ) M; linarith)
  linarith only [hid,hs,hc,hl]

/-- The unit source eventually exceeds every square-root coefficient strictly below one sixteenth. -/
theorem eventually_divisorUnsignedDilationChannel_one_ge_sqrt_coefficient (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ M : ℕ in atTop,(1/16-ε)*Real.sqrt M≤divisorUnsignedDilationChannel M 1 := by
  filter_upwards [eventually_log_add_one_le_sqrt (ε/14) (by positivity)] with M hM
  have h := divisorUnsignedDilationChannel_one_ge_sqrt_log M
  have hl := Real.log_nonneg (show (1:ℝ)≤(M:ℝ)+1 by have := Nat.cast_nonneg (α := ℝ) M; linarith)
  nlinarith only [hM,h,hl]
end RHTower
