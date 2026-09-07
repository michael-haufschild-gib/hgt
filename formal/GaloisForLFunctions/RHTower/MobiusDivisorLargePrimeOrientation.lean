import GaloisForLFunctions.RHTower.DivisorSmoothSquareBlockMean

/-!
# Large first-prime orientation and actual two-prime ceilings

Analytic inequalities for the first five exact unit endpoints give a uniform
one-fifteenth ceiling for every clipped dilation with M <= 5p. The actual unit
source eventually exceeds that coefficient. Only cofactors one through four
can have active children in this sector, so exact interpolation gives a common
parent cutoff above which every child is dominated by its parent. A first prime
at least one fifth of the cutoff therefore preserves every retained sign, and
any second prime contracts energy and stays below the original ceiling.

No stored channel value or computational certificate enters these proofs.
The smaller-prime sector, remaining middle quotient profiles and full adaptive
schedule remain open.
-/

noncomputable section
open Finset Filter Topology HTGeometry
namespace RHTower

private theorem first_two_defect_bounds :
    primeFreeDivisorDefect 1 ≤ 1/6 ∧ primeFreeDivisorDefect 2 ≤ 1/24 := by
  have hg : Real.eulerMascheroniConstant < 7/12 := by
    have h := eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion
    linarith only [h]
  have hl := log_le_half_sub_inv_cubic (x := (2:ℝ)) (by norm_num)
  norm_num at hl
  constructor <;> norm_num [primeFreeDivisorDefect,Finset.sum_Icc_succ_top] <;> linarith only [hg,hl]

/-- The first three actual unit endpoints have a one-sixteenth normalized ceiling. -/
private theorem divisorUnsignedDilationChannel_one_le_sixteenth_of_le_three {N : ℕ} (hN : N ≤ 3) :
    divisorUnsignedDilationChannel N 1 ≤ Real.sqrt N/16 := by
  have h0 : divisorUnsignedDilationChannel 0 1=0 := by simp [divisorUnsignedDilationChannel]
  have h1 : divisorUnsignedDilationChannel 1 1=0 := by simp [divisorUnsignedDilationChannel]
  have h2 : divisorUnsignedDilationChannel 2 1=(Real.sqrt 2-1)*primeFreeDivisorDefect 1 := by
    rw [show 2=1+1 by rfl,divisorUnsignedDilationChannel_succ,h1]
    norm_num
  have h3 : divisorUnsignedDilationChannel 3 1=divisorUnsignedDilationChannel 2 1+
      (Real.sqrt 3-Real.sqrt 2)*primeFreeDivisorDefect 2 := by
    simpa using divisorUnsignedDilationChannel_succ 2 1
  have hs2lo : 1 ≤ Real.sqrt 2 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hs2hi : Real.sqrt 2 ≤ 3/2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hs3lo : 1 ≤ Real.sqrt 3 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hs23 : Real.sqrt 2 ≤ Real.sqrt 3 := Real.sqrt_le_sqrt (by norm_num)
  have hb2 := mul_le_mul_of_nonneg_left first_two_defect_bounds.1 (sub_nonneg.mpr hs2lo)
  have hb3 := mul_le_mul_of_nonneg_left first_two_defect_bounds.2 (sub_nonneg.mpr hs23)
  interval_cases N
  · simp [h0]
  · simp [h1]
  · rw [h2]
    norm_num only [Nat.cast_ofNat]
    nlinarith only [hb2,hs2hi]
  · rw [h3,h2]
    norm_num only [Nat.cast_ofNat]
    nlinarith only [hb2,hb3,hs2hi,hs3lo]


/-- All five initial unit endpoints have an analytic one-fifteenth normalized ceiling. -/
theorem divisorUnsignedDilationChannel_one_le_fifteenth_of_le_five {N : ℕ} (hN : N ≤ 5) :
    divisorUnsignedDilationChannel N 1 ≤ Real.sqrt N/15 := by
  by_cases h3 : N ≤ 3
  · have h := divisorUnsignedDilationChannel_one_le_sixteenth_of_le_three h3
    have hr := Real.sqrt_nonneg (N:ℝ)
    linarith only [h,hr]
  have hg : Real.eulerMascheroniConstant ≤ 28861/50000 := by
    have h := eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion
    linarith only [h]
  have hl2 : Real.log 2 ≤ 1733/2500 := by linarith only [Real.log_two_lt_d9]
  have hl3 : Real.log 3 ≤ 10987/10000 := by linarith only [Real.log_three_lt_d9]
  have hD1 : primeFreeDivisorDefect 1 ≤ 3861/25000 := by
    norm_num [primeFreeDivisorDefect]
    linarith only [hg]
  have hD2 : primeFreeDivisorDefect 2 ≤ 13/6250 := by
    norm_num [primeFreeDivisorDefect,Finset.sum_Icc_succ_top]
    linarith only [hg,hl2]
  have hD3 : primeFreeDivisorDefect 3 ≤ 12761/50000 := by
    norm_num [primeFreeDivisorDefect,Finset.sum_Icc_succ_top]
    linarith only [hg,hl2,hl3]
  have hD4 : primeFreeDivisorDefect 4 ≤ 0 := by
    norm_num [primeFreeDivisorDefect,Finset.sum_Icc_succ_top,Real.log_four_eq]
    linarith only [hg,hl2,hl3]
  have hs2lo : (1414:ℝ)/1000 ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hs2hi : Real.sqrt 2 ≤ (1415:ℝ)/1000 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hs3lo : (1732:ℝ)/1000 ≤ Real.sqrt 3 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hs3hi : Real.sqrt 3 ≤ (1733:ℝ)/1000 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hs23 : Real.sqrt 2 ≤ Real.sqrt 3 := Real.sqrt_le_sqrt (by norm_num)
  have hs34 : Real.sqrt 3 ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hw1 : Real.sqrt 2-1 ≤ (415:ℝ)/1000 := by linarith only [hs2hi]
  have hw2 : Real.sqrt 3-Real.sqrt 2 ≤ (319:ℝ)/1000 := by linarith only [hs2lo,hs3hi]
  have hw3 : 2-Real.sqrt 3 ≤ (268:ℝ)/1000 := by linarith only [hs3lo]
  have hb1 := mul_le_mul hD1 hw1 (by linarith only [hs2lo] : 0 ≤ Real.sqrt 2-1) (by norm_num : (0:ℝ) ≤ 3861/25000)
  have hb2 := mul_le_mul hD2 hw2 (sub_nonneg.mpr hs23) (by norm_num : (0:ℝ) ≤ 13/6250)
  have hb3 := mul_le_mul hD3 hw3 (sub_nonneg.mpr hs34) (by norm_num : (0:ℝ) ≤ 12761/50000)
  have hK4 : divisorUnsignedDilationChannel 4 1 ≤ 2/15 := by
    have h1 : divisorUnsignedDilationChannel 1 1=0 := by simp [divisorUnsignedDilationChannel]
    rw [show 4=3+1 by rfl,divisorUnsignedDilationChannel_succ,
      show 3=2+1 by rfl,divisorUnsignedDilationChannel_succ,
      show 2=1+1 by rfl,divisorUnsignedDilationChannel_succ,h1]
    norm_num
    nlinarith only [hb1,hb2,hb3]
  by_cases h4 : N=4
  · subst N
    norm_num
    exact hK4
  have h5 : N=5 := by omega
  subst N
  have hs45 : (2:ℝ) ≤ Real.sqrt 5 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hprod := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ Real.sqrt 5-2 by linarith only [hs45]) hD4
  rw [show 5=4+1 by rfl,divisorUnsignedDilationChannel_succ]
  norm_num
  nlinarith only [hK4,hprod,hs45]

private theorem smooth_mean_fifteenth_margin : 41/240 < divisorHyperbolaSmoothMean := by
  have hlim := ((Real.continuousAt_log (show Real.sqrt Real.pi ≠ 0 by positivity)).tendsto).comp
    (Stirling.tendsto_stirlingSeq_sqrt_pi.comp (tendsto_add_atTop_nat 1))
  have hc : 1-(12:ℝ)⁻¹-Real.log 2/2 ≤ Real.log (Real.sqrt Real.pi) :=
    ge_of_tendsto hlim (Eventually.of_forall Stirling.log_stirlingSeq_bounded_by_constant)
  rw [Real.log_sqrt Real.pi_pos.le] at hc
  have hg := eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion
  unfold divisorHyperbolaSmoothMean
  rw [Real.log_mul (by norm_num) Real.pi_pos.ne']
  norm_num at hc
  linarith only [hc,hg]

/-- Every dilation in the first five quotient blocks has a uniform one-fifteenth ceiling, including the clipped terminal block. -/
theorem divisorUnsignedDilationChannel_le_fifteenth_of_le_five_mul {M p : ℕ}
    (hp : 0<p) (hMp : M ≤ 5*p) :
    divisorUnsignedDilationChannel M p ≤ Real.sqrt M/15 := by
  by_cases he : M=5*p
  · rw [he,show 5*p=p*5 by omega]
    have hc := divisorUnsignedDilationChannel_mul p 5 1
    simp only [Nat.mul_one] at hc
    rw [hc]
    have hb := mul_le_mul_of_nonneg_left
      (divisorUnsignedDilationChannel_one_le_fifteenth_of_le_five (N := 5) le_rfl) (Real.sqrt_nonneg (p:ℝ))
    push_cast
    rw [Real.sqrt_mul (Nat.cast_nonneg p)]
    nlinarith only [hb]
  have hq : M/p < 5 := (Nat.div_lt_iff_lt_mul hp).mpr (by omega)
  have hw0 := divisorPrimeClipWeight_nonneg M p hp
  have hw1 : 0 ≤ 1-divisorPrimeClipWeight M p := by
    have h := divisorPrimeClipWeight_lt_one M p hp; linarith only [h]
  have hA := mul_le_mul_of_nonneg_left
    (divisorUnsignedDilationChannel_one_le_fifteenth_of_le_five (N := M/p) (by omega)) hw1
  have hB := mul_le_mul_of_nonneg_left
    (divisorUnsignedDilationChannel_one_le_fifteenth_of_le_five (N := M/p+1) (by omega)) hw0
  have hs := mul_le_mul_of_nonneg_left (add_le_add hA hB) (Real.sqrt_nonneg (p:ℝ))
  have hc := divisorUnsignedDilationChannel_prime_interpolation M p 1 hp
  simp only [Nat.mul_one] at hc
  have hw := divisorPrimeClipWeight_mul_step M p hp
  push_cast at hw
  rw [Real.sqrt_mul (Nat.cast_nonneg p)] at hw
  rw [hc]
  push_cast at hs ⊢
  nlinarith only [hs,hw]

/-- The complete unit source eventually exceeds the one-fifteenth coefficient strictly enough for uniform comparison. -/
theorem eventually_divisorUnsignedDilationChannel_one_ge_fifteenth :
    ∀ᶠ M : ℕ in atTop,Real.sqrt M/15 ≤ divisorUnsignedDilationChannel M 1 := by
  let ε := (divisorHyperbolaSmoothMean-41/240)/2
  have hε : 0<ε := by dsimp [ε]; linarith only [smooth_mean_fifteenth_margin]
  filter_upwards [eventually_divisorUnsignedDilationChannel_one_exact_mean_bounds ε hε] with M hM
  have hcoef : (1:ℝ)/15 ≤ divisorHyperbolaSmoothMean-5/48-ε := by
    dsimp [ε]; linarith only [smooth_mean_fifteenth_margin]
  have h := mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg (M:ℝ))
  nlinarith only [h,hM.1]

/-- Above one universal parent cutoff, every one-fifth dilation is dominated by its parent in every cofactor. -/
theorem exists_divisorUnsignedDilationChannel_above_fifth_cofactor_domination :
    ∃ M₀ : ℕ, ∀ M : ℕ,M₀ ≤ M → ∀ p : ℕ,0<p → M ≤ 5*p → ∀ d : ℕ,
      divisorUnsignedDilationChannel M (p*d) ≤ divisorUnsignedDilationChannel M d := by
  obtain ⟨T,hT⟩ := eventually_atTop.mp eventually_divisorUnsignedDilationChannel_one_ge_fifteenth
  refine ⟨4*max T 1,?_⟩
  intro M hM p hp hMp d
  by_cases hd : d=0
  · simp [hd]
  have hd0 : 0<d := by omega
  by_cases hdb : d ≤ 4
  · have hN : T ≤ M/d := by
      apply (Nat.le_div_iff_mul_le hd0).mpr
      have hTmax : T ≤ max T 1 := le_max_left _ _
      nlinarith only [hM,hdb,hTmax]
    have hw0 := divisorPrimeClipWeight_nonneg M d hd0
    have hw1 : 0 ≤ 1-divisorPrimeClipWeight M d := by
      have h := divisorPrimeClipWeight_lt_one M d hd0; linarith only [h]
    have hA := mul_le_mul_of_nonneg_left (hT (M/d) hN) hw1
    have hB := mul_le_mul_of_nonneg_left (hT (M/d+1) (by omega)) hw0
    have hs := mul_le_mul_of_nonneg_left (add_le_add hA hB) (Real.sqrt_nonneg (d:ℝ))
    have hc := divisorUnsignedDilationChannel_prime_interpolation M d 1 hd0
    simp only [Nat.mul_one] at hc
    have hw := divisorPrimeClipWeight_mul_step M d hd0
    push_cast at hw
    rw [Real.sqrt_mul (Nat.cast_nonneg d)] at hw
    have hparent : Real.sqrt M/15 ≤ divisorUnsignedDilationChannel M d := by
      rw [hc]
      push_cast at hs ⊢
      nlinarith only [hs,hw]
    exact (divisorUnsignedDilationChannel_le_fifteenth_of_le_five_mul
      (show 0<p*d by positivity) (by nlinarith only [hMp,hd0])).trans hparent
  · have hzero : divisorUnsignedDilationChannel M (p*d)=0 := by
      unfold divisorUnsignedDilationChannel
      have hpdM : M ≤ p*d := by nlinarith only [hMp,hdb,hp]
      have hpos : 0<p*d := by positivity
      rw [Icc_eq_empty_of_lt (by omega : M-1<p*d),sum_empty]
    rw [hzero]
    exact divisorUnsignedDilationChannel_nonneg M d

private theorem selection_fibre_zero_of_nonprime_label (M : ℕ) (P R : Finset ℕ)
    {r : ℕ} (hr : r ∈ R) (hnr : ¬r.Prime) : mobiusDivisorSelectionFibre M P R=0 := by
  unfold mobiusDivisorSelectionFibre subsetLabelFibre
  apply sum_eq_zero
  intro d hd
  have he : d.primeFactors \ P ≠ R := by
    intro he
    have hm : r ∈ d.primeFactors \ P := he.symm ▸ hr
    exact hnr (Nat.prime_of_mem_primeFactors (mem_sdiff.mp hm).1)
  simp only [if_neg he]

/-- A first prime in the one-fifth sector preserves the original sign of every retained fibre at every sufficiently large cutoff. -/
theorem exists_mobiusDivisorSelectionFibre_above_fifth_parity :
    ∃ M₀ : ℕ, ∀ M : ℕ,M₀ ≤ M → ∀ p : ℕ,p.Prime → M ≤ 5*p →
      ∀ R : Finset ℕ,0 ≤ (-1:ℝ)^R.card*mobiusDivisorSelectionFibre M {p} R := by
  obtain ⟨M₀,hdom⟩ := exists_divisorUnsignedDilationChannel_above_fifth_cofactor_domination
  refine ⟨M₀,?_⟩
  intro M hM p hp hMp R
  by_cases hpR : p ∈ R
  · rw [show ({p}:Finset ℕ)=insert p ∅ by rfl,mobiusDivisorSelectionFibre_insert,if_pos hpR,mul_zero]
  by_cases hR : ∀ r ∈ R,r.Prime
  · change 0 ≤ mobiusDivisorOrientedFibre M {p} R
    rw [show ({p}:Finset ℕ)=insert p ∅ by rfl,mobiusDivisorOrientedFibre_insert M ∅ R p hpR,
      mobiusDivisorOrientedFibre_empty_eq_unsigned_product R hR,
      mobiusDivisorOrientedFibre_empty_eq_unsigned_product (insert p R) (by simpa using And.intro hp hR),
      prod_insert hpR]
    exact sub_nonneg.mpr (hdom M hM p hp.pos hMp _)
  · push Not at hR
    obtain ⟨r,hr,hnr⟩ := hR
    rw [selection_fibre_zero_of_nonprime_label M {p} R hr hnr,mul_zero]

/-- After a first prime at least one fifth of the cutoff, every second prime contracts energy and meets the original ceiling, uniformly at large cutoffs. -/
theorem exists_mobiusDivisorSelectionEnergy_above_fifth_two_prime_ceiling :
    ∃ M₀ : ℕ, ∀ M p q : ℕ,M₀ ≤ M → p.Prime → q.Prime → p<M → q<M → p≠q → M ≤ 5*p →
      mobiusDivisorSelectionEnergy M (insert q {p}) ≤ mobiusDivisorSelectionEnergy M {p} ∧
      mobiusDivisorSelectionEnergy M (insert q {p}) ≤ mobiusDivisorSelectionEnergy M ∅ := by
  obtain ⟨M₀,hparity⟩ := exists_mobiusDivisorSelectionFibre_above_fifth_parity
  refine ⟨M₀,?_⟩
  intro M p q hM hp hq hpM hqM hpq hMp
  have hsecond := mobiusDivisorSelectionEnergy_insert_le_of_parity_nonneg M {p} hq hqM
    (by simpa using hpq.symm) (hparity M hM p hp hMp)
  have hfirst := mobiusDivisorSelectionEnergy_insert_le_of_parity_nonneg M ∅ hp hpM (by simp)
    (fun R => mobiusDivisorSelectionFibre_empty_parity_nonneg M R)
  simp only [insert_empty_eq] at hfirst
  exact ⟨hsecond,hsecond.trans hfirst⟩
/-- At sufficiently large parent cutoffs, an original two-prime ceiling failure requires both primes below one fifth of the cutoff. -/
theorem exists_mobiusDivisorSelectionEnergy_two_prime_failure_below_fifth :
    ∃ M₀ : ℕ, ∀ M p q : ℕ,M₀ ≤ M → p.Prime → q.Prime → p<M → q<M → p≠q →
      mobiusDivisorSelectionEnergy M ∅ < mobiusDivisorSelectionEnergy M (insert q {p}) →
      5*p<M ∧ 5*q<M := by
  obtain ⟨M₀,hceil⟩ := exists_mobiusDivisorSelectionEnergy_above_fifth_two_prime_ceiling
  refine ⟨M₀,?_⟩
  intro M p q hM hp hq hpM hqM hpq hfail
  constructor
  · by_contra hn
    have h := (hceil M p q hM hp hq hpM hqM hpq (by omega)).2
    linarith only [h,hfail]
  · by_contra hn
    have h := (hceil M q p hM hq hp hqM hpM hpq.symm (by omega)).2
    have he : insert p ({q}:Finset ℕ)=insert q {p} := by ext r; simp only [mem_insert,mem_singleton]; tauto
    rw [he] at h
    linarith only [h,hfail]
/-- Above a fixed parent cutoff, every actual factor-two failure lies in a bounded middle quotient range. -/
theorem exists_divisorUnsignedDilationChannel_factor_two_failure_middle_quotient :
    ∃ M₀ T : ℕ,1 ≤ T ∧ ∀ M p : ℕ,M₀ ≤ M → 0<p →
      2*divisorUnsignedDilationChannel M 1 < divisorUnsignedDilationChannel M p →
      5*p<M ∧ 5 ≤ M/p ∧ M/p<T := by
  obtain ⟨M₀,hdom⟩ := exists_divisorUnsignedDilationChannel_above_fifth_cofactor_domination
  obtain ⟨T,hT,hbound⟩ := exists_divisorUnsignedDilationChannel_factor_two_failure_quotient_bound
  refine ⟨M₀,T,hT,?_⟩
  intro M p hM hp hfail
  have hsmall : 5*p<M := by
    by_contra hn
    have h := hdom M hM p hp (by omega) 1
    simp only [Nat.mul_one] at h
    have hz := divisorUnsignedDilationChannel_nonneg M 1
    linarith only [h,hz,hfail]
  exact ⟨hsmall,(Nat.le_div_iff_mul_le hp).mpr hsmall.le,hbound M p hp hfail⟩

end RHTower
