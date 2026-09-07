import GaloisForLFunctions.RHTower.MobiusDivisorPrimeFibreInterpolation
import GaloisForLFunctions.RHTower.MobiusDivisorAdaptivePrimeEnergyObstruction
import GaloisForLFunctions.RHTower.MobiusDivisorLatePrimeHeadAsymptotic
import GaloisForLFunctions.RHTower.ThreePlaneSourceMargin
/-!
# The actual coupled two-coordinate source cone

After the fixed prime core below fifteen excluding two, child cutoffs two,
seven and fourteen positively span the retained head and prime-two plane.
All signs follow from analytic source bounds and exact prime-two reflection.
Compactness gives a uniform directional margin, retained under sufficiently
small independent adjacent-cutoff clipping. No experimental value is used.
-/

noncomputable section
open Finset
namespace RHTower

def mobiusDivisorCoupledTwoCore : Finset ℕ := (mobiusDivisorSelectionPrimes 15).erase 2

/-- The fixed core processes every active child prime other than two through cutoff fifteen. -/
theorem mobiusDivisorCoupledTwoCore_covers {K : ℕ} (hK : K≤15) :
    mobiusDivisorSelectionPrimes K\{2}⊆mobiusDivisorCoupledTwoCore := by
  intro p hp
  obtain ⟨hp,hp2⟩ := mem_sdiff.mp hp
  obtain ⟨hp,hprime⟩ := mem_filter.mp hp
  exact mem_erase.mpr ⟨by simpa using hp2,mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp hp; omega),hprime⟩⟩

private theorem core_two_not : 2∉mobiusDivisorCoupledTwoCore := by simp [mobiusDivisorCoupledTwoCore]

/-- The exact two surviving source coordinates when every other active prime has been processed. -/
theorem mobiusDivisorSelectionFibre_one_remaining (M p : ℕ) (P : Finset ℕ)
    (hp : p.Prime) (hpP : p∉P) (hP : mobiusDivisorSelectionPrimes M\{p}⊆P) :
    mobiusDivisorSelectionFibre M P ∅=mobiusDivisorLastPrimeFree M p ∧
    mobiusDivisorSelectionFibre M P {p}=mobiusDivisorLastPrimeDivisible M p := by
  have hlabel {d : ℕ} (hd : d∈Icc 1 M) (hdM : d≠M) :
      d.primeFactors\P=if p∣d then {p} else ∅ := by
    have hsub : d.primeFactors\P⊆{p} := by
      intro q hq
      obtain ⟨hq,hqP⟩ := mem_sdiff.mp hq
      by_contra hqp
      apply hqP
      apply hP
      apply mem_sdiff.mpr
      refine ⟨mem_filter.mpr ⟨mem_range.mpr ?_,(Nat.mem_primeFactors.mp hq).1⟩,hqp⟩
      have := Nat.le_of_mem_primeFactors hq
      have := mem_Icc.mp hd
      omega
    by_cases hpd : p∣d
    · rw [if_pos hpd]
      apply subset_antisymm hsub
      apply singleton_subset_iff.mpr
      exact mem_sdiff.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp,hpd,by have := (mem_Icc.mp hd).1; omega⟩,hpP⟩
    · rw [if_neg hpd]
      apply eq_empty_iff_forall_notMem.mpr
      intro q hq
      have he : q=p := mem_singleton.mp (hsub hq)
      subst q
      exact hpd (Nat.mem_primeFactors.mp (mem_sdiff.mp hq).1).2.1
  have hz (hd : M∈Icc 1 M) : mobiusDivisorDilationChannel M M=0 := by
    have := (mem_Icc.mp hd).1
    simp [mobiusDivisorDilationChannel,Icc_eq_empty_of_lt (show M-1<M by omega)]
  constructor
  all_goals rw [mobiusDivisorSelectionFibre_eq_sum_Icc]
  · unfold mobiusDivisorLastPrimeFree
    rw [sum_filter]
    apply sum_congr rfl
    intro d hd
    by_cases he : d=M
    · subst d; simp [hz hd]
    · rw [hlabel hd he]
      by_cases hpd : p∣d <;> simp [hpd]
  · unfold mobiusDivisorLastPrimeDivisible
    rw [sum_filter]
    apply sum_congr rfl
    intro d hd
    by_cases he : d=M
    · subst d; simp [hz hd]
    · rw [hlabel hd he]
      by_cases hpd : p∣d <;> simp [hpd]

/-- Only the head and the one unprocessed prime label can survive a complete complementary core. -/
theorem mobiusDivisorSelectionFibre_one_remaining_zero (M p : ℕ) (P R : Finset ℕ)
    (hP : mobiusDivisorSelectionPrimes M\{p}⊆P) (hR0 : R≠∅) (hRp : R≠{p}) :
    mobiusDivisorSelectionFibre M P R=0 := by
  unfold mobiusDivisorSelectionFibre subsetLabelFibre
  apply sum_eq_zero
  intro d hd
  have hn := mem_Icc.mp (mem_filter.mp hd).1
  have hsub : d.primeFactors\P⊆{p} := by
    intro q hq
    obtain ⟨hq,hqP⟩ := mem_sdiff.mp hq
    by_contra hqp
    apply hqP
    apply hP
    exact mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_range.mpr (by
      have := Nat.le_of_mem_primeFactors hq; omega),(Nat.mem_primeFactors.mp hq).1⟩,hqp⟩
  have he : d.primeFactors\P≠R := by
    intro he
    rw [he] at hsub
    have hcases := subset_singleton_iff.mp hsub
    exact hcases.elim hR0 hRp
  simp [he]

private theorem core_fibres {K : ℕ} (hK : K≤15) :
    mobiusDivisorSelectionFibre K mobiusDivisorCoupledTwoCore ∅=mobiusDivisorLastPrimeFree K 2 ∧
    mobiusDivisorSelectionFibre K mobiusDivisorCoupledTwoCore {2}=mobiusDivisorLastPrimeDivisible K 2 :=
  mobiusDivisorSelectionFibre_one_remaining K 2 _ Nat.prime_two core_two_not (mobiusDivisorCoupledTwoCore_covers hK)

private theorem source_eleven_upper :
    (∑ d∈Icc 1 11,mobiusDivisorDilationChannel 11 d)≤-(28:ℝ)/100 := by
  obtain ⟨h1,h2,h3,h5,h6,h7,h10⟩ := mobiusDivisorDilationChannel_eleven_box
  obtain ⟨z4,z8,z9,z11⟩ := mobiusDivisorDilationChannel_eleven_zero
  norm_num [sum_Icc_succ_top,z4,z8,z9,z11]
  linarith

private theorem source_psi_small : psiDefect 11≤(1:ℝ)/2 ∧ psiDefect 12≤0 ∧ psiDefect 13≤(6:ℝ)/5 := by
  have vzero (n : ℕ) (h2 : 2∣n) (h3 : 3∣n) (hn : 0<n) : ArithmeticFunction.vonMangoldt n=0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    rw [Nat.not_isPrimePow_iff_nontrivial_of_two_le (Nat.le_of_dvd hn h2)]
    exact ⟨2,Nat.mem_primeFactors.mpr ⟨Nat.prime_two,h2,by omega⟩,
      3,Nat.mem_primeFactors.mpr ⟨Nat.prime_three,h3,by omega⟩,by norm_num⟩
  have v10 : ArithmeticFunction.vonMangoldt 10=0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    rw [Nat.not_isPrimePow_iff_nontrivial_of_two_le (by norm_num)]
    exact ⟨2,Nat.mem_primeFactors.mpr ⟨Nat.prime_two,by norm_num,by norm_num⟩,
      5,Nat.mem_primeFactors.mpr ⟨Nat.prime_five,by norm_num,by norm_num⟩,by norm_num⟩
  have v4 : ArithmeticFunction.vonMangoldt 4=Real.log 2 := by
    rw [show (4:ℕ)=2^2 by norm_num,ArithmeticFunction.vonMangoldt_apply_pow (by norm_num),ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    norm_num
  have v8 : ArithmeticFunction.vonMangoldt 8=Real.log 2 := by
    rw [show (8:ℕ)=2^3 by norm_num,ArithmeticFunction.vonMangoldt_apply_pow (by norm_num),ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    norm_num
  have v9 : ArithmeticFunction.vonMangoldt 9=Real.log 3 := by
    rw [show (9:ℕ)=3^2 by norm_num,ArithmeticFunction.vonMangoldt_apply_pow (by norm_num),ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three]
    norm_num
  have l7 : Real.log 7≤1.955 := by
    have h := Real.log_le_sub_one_of_pos (x := (7:ℝ)/8) (by norm_num)
    rw [Real.log_div (by norm_num) (by norm_num),show Real.log 8=3*Real.log 2 by
      rw [show (8:ℝ)=2^3 by norm_num,Real.log_pow]; norm_num] at h
    linarith [Real.log_two_lt_d9]
  have l11 : Real.log 11≤2*Real.log 2+Real.log 3 := by
    have h := Real.log_le_log (by norm_num : (0:ℝ)<11) (by norm_num : (11:ℝ)≤4*3)
    rwa [Real.log_mul (by norm_num) (by norm_num),Real.log_four_eq] at h
  have l13 : Real.log 13≤Real.log 2+Real.log 7 := by
    have h := Real.log_le_log (by norm_num : (0:ℝ)<13) (by norm_num : (13:ℝ)≤2*7)
    rwa [Real.log_mul (by norm_num) (by norm_num)] at h
  have hg := eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion
  have v6 := vzero 6 (by norm_num) (by norm_num) (by norm_num)
  have v12 := vzero 12 (by norm_num) (by norm_num) (by norm_num)
  norm_num [psiDefect,chebyshevPsi,sum_Icc_succ_top,v4,v6,v8,v9,v10,v12,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_five,
    ArithmeticFunction.vonMangoldt_apply_prime (show Nat.Prime 7 by norm_num),
    ArithmeticFunction.vonMangoldt_apply_prime (show Nat.Prime 11 by norm_num),
    ArithmeticFunction.vonMangoldt_apply_prime (show Nat.Prime 13 by norm_num)]
  refine ⟨?_,?_,?_⟩ <;> linarith [Real.log_two_lt_d9,Real.log_three_lt_d9,Real.log_five_lt_d9]

private theorem source_fourteen_neg : (∑ d∈Icc 1 14,mobiusDivisorDilationChannel 14 d)<0 := by
  have he : (∑ d∈Icc 1 14,mobiusDivisorDilationChannel 14 d)=
      (∑ d∈Icc 1 11,mobiusDivisorDilationChannel 11 d)+
      (Real.sqrt 12-Real.sqrt 11)*psiDefect 11+
      (Real.sqrt 13-Real.sqrt 12)*psiDefect 12+
      (Real.sqrt 14-Real.sqrt 13)*psiDefect 13 := by
    simp only [sum_mobiusDivisorDilationChannel_eq_psiDefect_abel]
    rw [Finset.sum_Ico_eq_sub _ (by norm_num : 1≤14),Finset.sum_Ico_eq_sub _ (by norm_num : 1≤11)]
    rw [show (14:ℕ)=11+1+1+1 by norm_num,Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_succ]
    norm_num
    ring
  obtain ⟨h11,h12,h13⟩ := source_psi_small
  have w0 (k : ℝ) : 0≤Real.sqrt (k+1)-Real.sqrt k :=
    sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))
  have w1 : Real.sqrt 12-Real.sqrt 11≤(3:ℝ)/20 := by
    have a := Real.sq_sqrt (by norm_num : (0:ℝ)≤12)
    have b := Real.sq_sqrt (by norm_num : (0:ℝ)≤11)
    nlinarith [Real.sqrt_nonneg 12,Real.sqrt_nonneg 11,sq_nonneg (Real.sqrt 11-3.316),sq_nonneg (Real.sqrt 12-3.4642)]
  have w3 : Real.sqrt 14-Real.sqrt 13≤(7:ℝ)/50 := by
    have a := Real.sq_sqrt (by norm_num : (0:ℝ)≤14)
    have b := Real.sq_sqrt (by norm_num : (0:ℝ)≤13)
    nlinarith [Real.sqrt_nonneg 14,Real.sqrt_nonneg 13,sq_nonneg (Real.sqrt 13-3.605),sq_nonneg (Real.sqrt 14-3.742)]
  have p1 := mul_le_mul_of_nonneg_left h11 (show 0≤Real.sqrt 12-Real.sqrt 11 by convert w0 11 using 1 <;> norm_num)
  have p2 := mul_le_mul_of_nonneg_left h12 (show 0≤Real.sqrt 13-Real.sqrt 12 by convert w0 12 using 1 <;> norm_num)
  have p3 := mul_le_mul_of_nonneg_left h13 (show 0≤Real.sqrt 14-Real.sqrt 13 by convert w0 13 using 1 <;> norm_num)
  rw [he]
  nlinarith only [source_eleven_upper,w1,w3,p1,p2,p3]

/-- Actual two-coordinate child profile after a fixed prime core that leaves two unprocessed. -/
def mobiusDivisorCoupledTwoProfile (K : ℕ) : ℝ × ℝ :=
  (mobiusDivisorSelectionFibre K mobiusDivisorCoupledTwoCore ∅,
   mobiusDivisorSelectionFibre K mobiusDivisorCoupledTwoCore {2})

/-- Three analytically certified source directions: positive horizontal, negative in both coordinates, and negative-positive. -/
theorem mobiusDivisorCoupledTwoProfile_three_signs :
    0<(mobiusDivisorCoupledTwoProfile 2).1 ∧ (mobiusDivisorCoupledTwoProfile 2).2=0 ∧
    (mobiusDivisorCoupledTwoProfile 7).1<0 ∧ (mobiusDivisorCoupledTwoProfile 7).2<0 ∧
    (mobiusDivisorCoupledTwoProfile 14).1<0 ∧ 0<(mobiusDivisorCoupledTwoProfile 14).2 := by
  have h7 := mobiusDivisorLastPrime_seven_both_neg 2 (by simp)
  obtain ⟨f2,b2⟩ := core_fibres (K := 2) (by norm_num)
  obtain ⟨f7,b7⟩ := core_fibres (K := 7) (by norm_num)
  obtain ⟨f14,b14⟩ := core_fibres (K := 14) (by norm_num)
  have htwo : mobiusDivisorSelectionFibre 14 mobiusDivisorCoupledTwoCore {2}=
      -Real.sqrt 2*mobiusDivisorSelectionFibre 7 mobiusDivisorCoupledTwoCore ∅ := by
    have h := mobiusDivisorSelectionFibre_prime_interpolation Nat.prime_two 14
      mobiusDivisorCoupledTwoCore ∅ core_two_not (by simp)
    simpa [mobiusDivisorInterpolatedFibre,divisorPrimeClipWeight] using h
  have hp14 : 0 < mobiusDivisorSelectionFibre 14 mobiusDivisorCoupledTwoCore {2} := by
    rw [htwo,f7]
    exact mul_pos_of_neg_of_neg (by have := Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2); linarith) h7.1
  have hn14 : mobiusDivisorSelectionFibre 14 mobiusDivisorCoupledTwoCore ∅<0 := by
    have hh := mobiusDivisorLastPrime_add_eq_total 14 2
    rw [← f14,← b14] at hh
    linarith only [hh,hp14,source_fourteen_neg]
  have hd1 : 0<primeFreeDivisorDefect 1 := by
    have h := (harmonic_mascheroni_half_bounds (n := 4) (by norm_num)).2
    norm_num [harmonic,sum_range_succ,Real.log_four_eq] at h
    norm_num [primeFreeDivisorDefect]
    linarith [Real.log_two_lt_d9]
  have hf2 : 0 < mobiusDivisorSelectionFibre 2 mobiusDivisorCoupledTwoCore ∅ := by
    rw [f2]
    norm_num [mobiusDivisorLastPrimeFree,sum_filter,sum_Icc_succ_top,mobiusDivisorDilationChannel]
    exact mul_pos (sub_pos.mpr (by have := Real.sqrt_lt_sqrt (by norm_num : (0:ℝ)≤1) (by norm_num : (1:ℝ)<2); simpa using this)) hd1
  have hb2 : mobiusDivisorSelectionFibre 2 mobiusDivisorCoupledTwoCore {2}=0 := by
    rw [b2]
    norm_num [mobiusDivisorLastPrimeDivisible,sum_filter,sum_Icc_succ_top,mobiusDivisorDilationChannel]
  exact ⟨hf2,hb2,by simpa only [mobiusDivisorCoupledTwoProfile, f7] using h7.1,
    by simpa only [mobiusDivisorCoupledTwoProfile, b7] using h7.2,hn14,hp14⟩

/-- The actual source contains a strictly positive three-vector circuit spanning the head and nonempty coordinate. -/
theorem exists_mobiusDivisorCoupledTwo_positive_circuit :
    ∃ a b c : ℝ,0<a ∧ 0<b ∧ 0<c ∧
      a*(mobiusDivisorCoupledTwoProfile 2).1+b*(mobiusDivisorCoupledTwoProfile 7).1+
        c*(mobiusDivisorCoupledTwoProfile 14).1=0 ∧
      a*(mobiusDivisorCoupledTwoProfile 2).2+b*(mobiusDivisorCoupledTwoProfile 7).2+
        c*(mobiusDivisorCoupledTwoProfile 14).2=0 := by
  obtain ⟨ha,ha0,hb,hb',hc,hc'⟩ := mobiusDivisorCoupledTwoProfile_three_signs
  let a := ((mobiusDivisorCoupledTwoProfile 14).1*(mobiusDivisorCoupledTwoProfile 7).2-
    (mobiusDivisorCoupledTwoProfile 7).1*(mobiusDivisorCoupledTwoProfile 14).2)/(mobiusDivisorCoupledTwoProfile 2).1
  refine ⟨a,(mobiusDivisorCoupledTwoProfile 14).2,-(mobiusDivisorCoupledTwoProfile 7).2,?_,hc',by linarith,?_,?_⟩
  · apply div_pos _ ha
    have h1 := mul_pos_of_neg_of_neg hc hb'
    have h2 := mul_neg_of_neg_of_pos hb hc'
    linarith
  · dsimp [a]
    field_simp
    ring
  · rw [ha0]
    ring

/-- Every nonzero joint head/nonempty direction admits a strict descent direction in the literal reflected source. -/
theorem exists_mobiusDivisorCoupledTwo_source_descent (x y : ℝ) (hxy : x≠0 ∨ y≠0) :
    ∃ K∈({2,7,14}:Finset ℕ),
      0<x*(mobiusDivisorCoupledTwoProfile K).1+y*(mobiusDivisorCoupledTwoProfile K).2 := by
  obtain ⟨ha,ha0,hb,hb',hc,hc'⟩ := mobiusDivisorCoupledTwoProfile_three_signs
  by_cases hx : 0<x
  · refine ⟨2,by simp,?_⟩
    rw [ha0,mul_zero,add_zero]
    exact mul_pos hx ha
  have hx0 : x≤0 := le_of_not_gt hx
  by_cases hy : y<0
  · refine ⟨7,by simp,?_⟩
    exact add_pos_of_nonneg_of_pos (mul_nonneg_of_nonpos_of_nonpos hx0 hb.le) (mul_pos_of_neg_of_neg hy hb')
  · have hy0 : 0≤y := le_of_not_gt hy
    refine ⟨14,by simp,?_⟩
    by_cases hx' : x=0
    · have hyp : 0<y := lt_of_le_of_ne hy0 (by rcases hxy with h|h; exact False.elim (h hx'); exact Ne.symm h)
      rw [hx',zero_mul,zero_add]
      exact mul_pos hyp hc'
    · exact add_pos_of_pos_of_nonneg (mul_pos_of_neg_of_neg (lt_of_le_of_ne hx0 hx') hc)
        (mul_nonneg hy0 hc'.le)

/-- The three actual child profiles have one uniform positive directional margin. -/
theorem exists_mobiusDivisorCoupledTwo_uniform_margin :
    ∃ c : ℝ,0<c ∧ ∀ z : ℝ × ℝ,
      c*‖z‖ ≤ max (z.1*(mobiusDivisorCoupledTwoProfile 2).1+z.2*(mobiusDivisorCoupledTwoProfile 2).2)
        (max (z.1*(mobiusDivisorCoupledTwoProfile 7).1+z.2*(mobiusDivisorCoupledTwoProfile 7).2)
          (z.1*(mobiusDivisorCoupledTwoProfile 14).1+z.2*(mobiusDivisorCoupledTwoProfile 14).2)) := by
  apply exists_threePlaneSource_margin
  intro z hz
  have hxy : z.1≠0 ∨ z.2≠0 := by
    by_contra hn
    push Not at hn
    apply hz
    exact Prod.ext hn.1 hn.2
  obtain ⟨K,hK,hpos⟩ := exists_mobiusDivisorCoupledTwo_source_descent z.1 z.2 hxy
  simp only [mem_insert,mem_singleton] at hK
  rcases hK with rfl|rfl|rfl
  · exact hpos.trans_le (le_max_left _ _)
  · exact hpos.trans_le ((le_max_left _ _).trans (le_max_right _ _))
  · exact hpos.trans_le ((le_max_right _ _).trans (le_max_right _ _))

/-- Adjacent child profiles at the literal affine clipping coordinate. -/
def mobiusDivisorCoupledTwoInterpolatedProfile (K : ℕ) (w : ℝ) : ℝ × ℝ :=
  mobiusDivisorCoupledTwoProfile K+w • (mobiusDivisorCoupledTwoProfile (K+1)-mobiusDivisorCoupledTwoProfile K)

/-- A single positive clipping tolerance preserves directional control of both actual retained coordinates. -/
theorem exists_mobiusDivisorCoupledTwo_clip_margin :
    ∃ ε c : ℝ,0<ε ∧ 0<c ∧ ∀ u v w : ℝ,
      0≤u → u≤ε → 0≤v → v≤ε → 0≤w → w≤ε → ∀ z : ℝ × ℝ,
      c*‖z‖ ≤ max (z.1*(mobiusDivisorCoupledTwoInterpolatedProfile 2 u).1+z.2*(mobiusDivisorCoupledTwoInterpolatedProfile 2 u).2)
        (max (z.1*(mobiusDivisorCoupledTwoInterpolatedProfile 7 v).1+z.2*(mobiusDivisorCoupledTwoInterpolatedProfile 7 v).2)
          (z.1*(mobiusDivisorCoupledTwoInterpolatedProfile 14 w).1+z.2*(mobiusDivisorCoupledTwoInterpolatedProfile 14 w).2)) := by
  obtain ⟨c,hc,hmargin⟩ := exists_mobiusDivisorCoupledTwo_uniform_margin
  let B : ℝ := 1+‖mobiusDivisorCoupledTwoProfile 3-mobiusDivisorCoupledTwoProfile 2‖+
    ‖mobiusDivisorCoupledTwoProfile 8-mobiusDivisorCoupledTwoProfile 7‖+
    ‖mobiusDivisorCoupledTwoProfile 15-mobiusDivisorCoupledTwoProfile 14‖
  have hB : 0<B := by dsimp [B]; positivity
  let ε := c/(4*B)
  have hε : 0<ε := div_pos hc (by positivity)
  refine ⟨ε,c/2,hε,by positivity,?_⟩
  intro u v w hu hu' hv hv' hw hw' z
  have bound (K : ℕ) (a : ℝ) (ha : 0≤a) (ha' : a≤ε)
      (hK : ‖mobiusDivisorCoupledTwoProfile (K+1)-mobiusDivisorCoupledTwoProfile K‖≤B) :
      ‖mobiusDivisorCoupledTwoInterpolatedProfile K a-mobiusDivisorCoupledTwoProfile K‖≤c/4 := by
    rw [mobiusDivisorCoupledTwoInterpolatedProfile,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg ha]
    have h := mul_le_mul ha' hK (norm_nonneg _) hε.le
    have he : ε*B=c/4 := by dsimp [ε]; field_simp
    exact h.trans_eq he
  apply threePlaneSource_margin_perturb _ _ _ _ _ _ c hc hmargin
  · apply bound 2 u hu hu'
    dsimp [B]
    have h0 := norm_nonneg (mobiusDivisorCoupledTwoProfile 8-mobiusDivisorCoupledTwoProfile 7)
    have h1 := norm_nonneg (mobiusDivisorCoupledTwoProfile 15-mobiusDivisorCoupledTwoProfile 14)
    linarith
  · apply bound 7 v hv hv'
    dsimp [B]
    have h0 := norm_nonneg (mobiusDivisorCoupledTwoProfile 3-mobiusDivisorCoupledTwoProfile 2)
    have h1 := norm_nonneg (mobiusDivisorCoupledTwoProfile 15-mobiusDivisorCoupledTwoProfile 14)
    linarith
  · apply bound 14 w hw hw'
    dsimp [B]
    have h0 := norm_nonneg (mobiusDivisorCoupledTwoProfile 3-mobiusDivisorCoupledTwoProfile 2)
    have h1 := norm_nonneg (mobiusDivisorCoupledTwoProfile 8-mobiusDivisorCoupledTwoProfile 7)
    linarith

end RHTower
