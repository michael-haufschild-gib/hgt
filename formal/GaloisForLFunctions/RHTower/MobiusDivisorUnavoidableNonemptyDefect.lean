import GaloisForLFunctions.RHTower.MobiusDivisorNonemptyEnergyObstruction
import GaloisForLFunctions.RHTower.MobiusDivisorParityDefectTransport

/-!
# Every source order creates a nonempty defect at cutoff twenty-one

The last unprocessed member of the prime triangle `{2,3,5}` has a strictly
negative oriented singleton once its other two members are processed.
Exact source support and analytic channel bounds retain every possible
additional cofactor. Taking the last first-occurrence position proves the
obstruction for every covering list, without an energy-budget hypothesis.
No numerical source value or path enumeration is used.
-/

noncomputable section
open Finset
namespace RHTower

private lemma gamma_lower : (0.5768:ℝ) ≤ Real.eulerMascheroniConstant := by
  have h := (harmonic_mascheroni_half_bounds (n := 16) (by norm_num)).2
  have hlog : Real.log (16:ℝ)=4*Real.log 2 := by
    rw [show (16:ℝ)=2^(4 : ℕ) by norm_num,Real.log_pow]
    norm_num
  norm_num [harmonic,Finset.sum_range_succ,hlog] at h
  linarith [Real.log_two_lt_d9]

private lemma defect_ten_lower : (-1:ℝ) ≤ primeFreeDivisorDefect 10 := by
  have h4 : Real.log 4 = 2*Real.log 2 := Real.log_four_eq
  have h6 : Real.log 6 = Real.log 2+Real.log 3 := by
    rw [← Real.log_mul (by norm_num : (2:ℝ)≠0) (by norm_num : (3:ℝ)≠0)]
    norm_num
  have h8 : Real.log 8 = 3*Real.log 2 := by
    rw [show (8:ℝ)=2^(3 : ℕ) by norm_num,Real.log_pow]; norm_num
  have h9 : Real.log 9 = 2*Real.log 3 := by
    rw [show (9:ℝ)=3^(2 : ℕ) by norm_num,Real.log_pow]; norm_num
  have h10 : Real.log 10 = Real.log 2+Real.log 5 := by
    rw [← Real.log_mul (by norm_num : (2:ℝ)≠0) (by norm_num : (5:ℝ)≠0)]
    norm_num
  have hp := Real.log_le_log (by norm_num : (0:ℝ)<2^(13 : ℕ))
    (by norm_num : (2:ℝ)^(13 : ℕ)≤3^(4 : ℕ)*5^(2 : ℕ)*7)
  rw [Real.log_mul (by norm_num) (by norm_num),Real.log_mul (by norm_num) (by norm_num)] at hp
  simp only [Real.log_pow,Nat.cast_ofNat] at hp
  norm_num [primeFreeDivisorDefect,sum_Icc_succ_top,h4,h6,h8,h9,h10]
  linarith [gamma_lower,Real.log_two_gt_d9]

private lemma two_upper : divisorUnsignedDilationChannel 21 2 ≤ (0.38:ℝ) := by
  have h11 := mobiusDivisorDilationChannel_eleven_box.1.2
  rw [mobiusDivisorDilationChannel_eq_moebius_unsigned] at h11
  simp only [ArithmeticFunction.moebius_apply_one,Int.cast_one,one_mul] at h11
  have hm := divisorUnsignedDilationChannel_mul 2 11 1
  norm_num only at hm
  have hs2 : Real.sqrt (2:ℝ)≤1.5 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sqrt_nonneg (2:ℝ)]
  have h22 : divisorUnsignedDilationChannel 22 2≤(0.27:ℝ) := by
    rw [hm]
    have h := mul_le_mul_of_nonneg_left h11 (Real.sqrt_nonneg 2)
    nlinarith only [h,hs2]
  have hs21 : (4.582:ℝ)≤Real.sqrt 21 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤21),Real.sqrt_nonneg (21:ℝ)]
  have hs22 : Real.sqrt (22:ℝ)≤4.692 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤22),Real.sqrt_nonneg (22:ℝ)]
  have hw : 0≤Real.sqrt (22:ℝ)-Real.sqrt 21 := sub_nonneg.mpr (Real.sqrt_le_sqrt (by norm_num))
  have hbound := mul_nonneg hw (show 0≤primeFreeDivisorDefect 10+1 by linarith [defect_ten_lower])
  have hstep := divisorUnsignedDilationChannel_succ 21 2
  norm_num only at hstep
  nlinarith only [hstep,h22,hbound,hs21,hs22]

private lemma six_lower : (0.23:ℝ) < divisorUnsignedDilationChannel 21 6 := by
  have h7 := mobiusDivisorDilationChannel_seven_box.2.1.1
  rw [mobiusDivisorDilationChannel_eq_moebius_unsigned,
    ArithmeticFunction.moebius_apply_prime Nat.prime_two] at h7
  norm_num only [Int.cast_neg,Int.cast_one,neg_one_mul,neg_neg] at h7
  have hm := divisorUnsignedDilationChannel_mul 3 7 2
  norm_num only at hm
  have hs : (1.7:ℝ)<Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤3),Real.sqrt_nonneg (3:ℝ)]
  have h := mul_le_mul_of_nonneg_left h7 (Real.sqrt_nonneg 3)
  rw [hm]
  nlinarith only [h,hs]

private lemma ten_lower : (0.19:ℝ) < divisorUnsignedDilationChannel 21 10 := by
  have h1 : (0.1536:ℝ)≤primeFreeDivisorDefect 1 := by
    norm_num [primeFreeDivisorDefect,sum_Icc_succ_top]
    linarith only [gamma_lower]
  have h2 : 0≤primeFreeDivisorDefect 2 := by
    norm_num [primeFreeDivisorDefect,sum_Icc_succ_top]
    linarith [gamma_lower,Real.log_two_gt_d9]
  have hm := divisorUnsignedDilationChannel_mul_add 10 2 1 1 (by omega) (by omega)
  have hu : divisorUnsignedDilationChannel 2 1=(Real.sqrt 2-1)*primeFreeDivisorDefect 1 := by
    norm_num [divisorUnsignedDilationChannel,sum_Icc_succ_top]
  norm_num only at hm
  rw [hu] at hm
  have hr : Real.sqrt (10:ℝ)*Real.sqrt 2=Real.sqrt 20 := by
    rw [← Real.sqrt_mul (by norm_num)]
    norm_num
  have heq : divisorUnsignedDilationChannel 21 10=
      (Real.sqrt 20-Real.sqrt 10)*primeFreeDivisorDefect 1+
      (Real.sqrt 21-Real.sqrt 20)*primeFreeDivisorDefect 2 := by
    rw [hm]
    nlinarith only [congrArg (fun x : ℝ => x*primeFreeDivisorDefect 1) hr]
  have hs20 : (4.47:ℝ)≤Real.sqrt 20 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤20),Real.sqrt_nonneg (20:ℝ)]
  have hs10 : Real.sqrt (10:ℝ)≤3.17 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤10),Real.sqrt_nonneg (10:ℝ)]
  have hw : 0≤Real.sqrt (21:ℝ)-Real.sqrt 20 := sub_nonneg.mpr (Real.sqrt_le_sqrt (by norm_num))
  have hprod := mul_nonneg (show 0≤Real.sqrt (20:ℝ)-Real.sqrt 10-1.3 by linarith)
    (show 0≤primeFreeDivisorDefect 1 by linarith only [h1])
  have htail := mul_nonneg hw h2
  rw [heq]
  nlinarith only [hprod,htail,h1]

private lemma signed_prime (p : ℕ) (hp : p.Prime) :
    mobiusDivisorDilationChannel 21 p = -divisorUnsignedDilationChannel 21 p := by
  rw [mobiusDivisorDilationChannel_eq_moebius_unsigned,ArithmeticFunction.moebius_apply_prime hp]
  norm_num

private lemma signed_pair (p r : ℕ) (hp : p.Prime) (hr : r.Prime) (hne : p≠r) :
    mobiusDivisorDilationChannel 21 (p*r) = divisorUnsignedDilationChannel 21 (p*r) := by
  rw [mobiusDivisorDilationChannel_eq_moebius_unsigned,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (hp.coprime_iff_not_dvd.mpr
      (fun h => hne ((Nat.dvd_prime hr).mp h |>.resolve_left hp.ne_one))),
    ArithmeticFunction.moebius_apply_prime hp,ArithmeticFunction.moebius_apply_prime hr]
  norm_num

private lemma factors_pair (p r : ℕ) (hp : p.Prime) (hr : r.Prime) :
    (p*r).primeFactors=({p,r}:Finset ℕ) := by
  rw [Nat.primeFactors_mul hp.ne_zero hr.ne_zero,hp.primeFactors,hr.primeFactors]
  simp

private lemma channel_square_zero (n p : ℕ) (hp : 1<p) (hd : p*p ∣ n) :
    mobiusDivisorDilationChannel 21 n=0 := by
  have hn : ¬Squarefree n := by
    intro h
    have hu := h p hd
    have he : p=1 := Nat.isUnit_iff.mp hu
    omega
  rw [mobiusDivisorDilationChannel_eq_moebius_unsigned,
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn]
  norm_num

private lemma fibre_singleton_divisors (P : Finset ℕ) (q : ℕ) (hq : 0<q) :
    mobiusDivisorSelectionFibre 21 P {q} =
      ∑ n ∈ Icc 1 (21/q), if (q*n).primeFactors \ P={q} then
        mobiusDivisorDilationChannel 21 (q*n) else 0 := by
  rw [mobiusDivisorSelectionFibre_eq_sum_Icc]
  have hrestrict : (∑ n ∈ Icc 1 21,
      if n.primeFactors \ P={q} then mobiusDivisorDilationChannel 21 n else 0) =
      ∑ n ∈ (Icc 1 21).filter (fun n => q ∣ n),
        if n.primeFactors \ P={q} then mobiusDivisorDilationChannel 21 n else 0 := by
    rw [sum_filter]
    apply sum_congr rfl
    intro n hn
    by_cases hd : q ∣ n
    · simp [hd]
    · have hne : n.primeFactors \ P≠{q} := by
        intro he
        have hm : q ∈ n.primeFactors := (mem_sdiff.mp (he.symm ▸ mem_singleton_self q)).1
        exact hd (Nat.mem_primeFactors.mp hm).2.1
      simp [hd,hne]
  rw [hrestrict,sum_Icc_filter_dvd_reindex q 21 hq]

private lemma singleton_triangle_formulas (P : Finset ℕ) :
    (2 ∉ P → 3 ∈ P → 5 ∈ P → mobiusDivisorOrientedFibre 21 P {2}=
      divisorUnsignedDilationChannel 21 2-divisorUnsignedDilationChannel 21 6-
      divisorUnsignedDilationChannel 21 10-(if 7∈P then divisorUnsignedDilationChannel 21 14 else 0)) ∧
    (3 ∉ P → 2 ∈ P → mobiusDivisorOrientedFibre 21 P {3}=
      divisorUnsignedDilationChannel 21 3-divisorUnsignedDilationChannel 21 6-
      (if 5∈P then divisorUnsignedDilationChannel 21 15 else 0)) ∧
    (5 ∉ P → 2 ∈ P → 3 ∈ P → mobiusDivisorOrientedFibre 21 P {5}=
      divisorUnsignedDilationChannel 21 5-divisorUnsignedDilationChannel 21 10-
      divisorUnsignedDilationChannel 21 15) := by
  have z4 := channel_square_zero 4 2 (by omega) (by norm_num)
  have z8 := channel_square_zero 8 2 (by omega) (by norm_num)
  have z12 := channel_square_zero 12 2 (by omega) (by norm_num)
  have z16 := channel_square_zero 16 2 (by omega) (by norm_num)
  have z18 := channel_square_zero 18 3 (by omega) (by norm_num)
  have z20 := channel_square_zero 20 2 (by omega) (by norm_num)
  have z9 := channel_square_zero 9 3 (by omega) (by norm_num)
  have z21 : mobiusDivisorDilationChannel 21 21=0 := by
    norm_num [mobiusDivisorDilationChannel]
  have hp7 : Nat.Prime 7 := by norm_num
  have f6 := factors_pair 2 3 Nat.prime_two Nat.prime_three
  have f10 := factors_pair 2 5 Nat.prime_two Nat.prime_five
  have f14 := factors_pair 2 7 Nat.prime_two hp7
  have f15 := factors_pair 3 5 Nat.prime_three Nat.prime_five
  have c6 := signed_pair 2 3 Nat.prime_two Nat.prime_three (by omega)
  have c10 := signed_pair 2 5 Nat.prime_two Nat.prime_five (by omega)
  have c14 := signed_pair 2 7 Nat.prime_two hp7 (by omega)
  have c15 := signed_pair 3 5 Nat.prime_three Nat.prime_five (by omega)
  norm_num only at f6 f10 f14 f15 c6 c10 c14 c15
  have hn27 : ({2,7}:Finset ℕ)≠{2} := by
    intro h
    have hh := congrArg (fun S : Finset ℕ => 7∈S) h
    norm_num at hh
  have hn35 : ({3,5}:Finset ℕ)≠{3} := by
    intro h
    have hh := congrArg (fun S : Finset ℕ => 5∈S) h
    norm_num at hh
  refine ⟨?_,?_,?_⟩
  · intro h2 h3 h5
    unfold mobiusDivisorOrientedFibre
    rw [fibre_singleton_divisors P 2 (by omega)]
    norm_num [sum_Icc_succ_top,z4,z8,z12,z16,z18,z20,f6,f10,f14,c6,c10,c14,
      signed_prime 2 Nat.prime_two,Nat.prime_two.primeFactors,
      Finset.sdiff_eq_filter,Finset.filter_insert,Finset.filter_singleton,h2,h3,h5]
    by_cases h7 : 7∈P <;> simp [h7,hn27] <;> ring
  · intro h3 h2
    unfold mobiusDivisorOrientedFibre
    rw [fibre_singleton_divisors P 3 (by omega)]
    norm_num [sum_Icc_succ_top,z9,z12,z18,z21,f6,f15,c6,c15,
      signed_prime 3 Nat.prime_three,Nat.prime_three.primeFactors,
      Finset.sdiff_eq_filter,Finset.filter_insert,Finset.filter_singleton,h2,h3]
    by_cases h5 : 5∈P <;> simp [h5,hn35] <;> ring
  · intro h5 h2 h3
    unfold mobiusDivisorOrientedFibre
    rw [fibre_singleton_divisors P 5 (by omega)]
    norm_num [sum_Icc_succ_top,z20,f10,f15,c10,c15,
      signed_prime 5 Nat.prime_five,Nat.prime_five.primeFactors,
      Finset.sdiff_eq_filter,Finset.filter_insert,Finset.filter_singleton,h2,h3,h5]
    ring

/-- Whichever prime of the actual triangle remains, the other two create a
strictly negative singleton. Every additional processed cofactor is retained. -/
theorem mobiusDivisor_twentyOne_last_triangle_negative (P : Finset ℕ) {q : ℕ}
    (hq : q ∈ ({2,3,5}:Finset ℕ)) (hfree : q ∉ P)
    (hprocessed : ∀ r ∈ ({2,3,5}:Finset ℕ), r≠q → r∈P) :
    mobiusDivisorOrientedFibre 21 P {q} < (-1/50:ℝ) := by
  simp only [mem_insert,mem_singleton] at hq
  rcases hq with rfl | rfl | rfl
  · have h3 : 3∈P := hprocessed 3 (by simp) (by omega)
    have h5 : 5∈P := hprocessed 5 (by simp) (by omega)
    rw [(singleton_triangle_formulas P).1 hfree h3 h5]
    have htail : 0≤(if 7∈P then divisorUnsignedDilationChannel 21 14 else 0) := by
      split_ifs
      · exact divisorUnsignedDilationChannel_nonneg 21 14
      · exact le_rfl
    linarith only [two_upper,six_lower,ten_lower,htail]
  · have h2 : 2∈P := hprocessed 2 (by simp) (by omega)
    rw [(singleton_triangle_formulas P).2.1 hfree h2]
    have hbase := (singleton_triangle_formulas ({2}:Finset ℕ)).2.1 (by simp) (by simp)
    norm_num [mobiusDivisorOrientedFibre] at hbase
    have htail : 0≤(if 5∈P then divisorUnsignedDilationChannel 21 15 else 0) := by
      split_ifs
      · exact divisorUnsignedDilationChannel_nonneg 21 15
      · exact le_rfl
    linarith only [hbase,mobiusDivisorSelectionFibre_twentyOne_three_gt,htail]
  · have h2 : 2∈P := hprocessed 2 (by simp) (by omega)
    have h3 : 3∈P := hprocessed 3 (by simp) (by omega)
    rw [(singleton_triangle_formulas P).2.2 hfree h2 h3]
    have hb := mobiusDivisorDilationChannel_twentyOne_tail_box
    have c10 := signed_pair 2 5 Nat.prime_two Nat.prime_five (by omega)
    have c15 := signed_pair 3 5 Nat.prime_three Nat.prime_five (by omega)
    norm_num only at c10 c15
    rw [signed_prime 5 Nat.prime_five,c10,c15] at hb
    linarith only [hb.1.1,hb.2]

/-- Every list covering the three source primes has a proper prefix with a
negative nonempty singleton, independently of all energy budgets and all
choices of intervening primes. Even repetitions in the list are allowed. -/
theorem mobiusDivisor_every_cover_twentyOne_nonempty_defect (l : List ℕ)
    (hcover : ({2,3,5}:Finset ℕ) ⊆ l.toFinset) :
    ∃ k : ℕ, k<l.length ∧ ∃ q ∈ ({2,3,5}:Finset ℕ),
      q ∉ (l.take k).toFinset ∧
      mobiusDivisorOrientedFibre 21 (l.take k).toFinset {q} < (-1/50:ℝ) := by
  obtain ⟨q,hq,hmax⟩ := Finset.exists_max_image ({2,3,5}:Finset ℕ) (fun r => l.idxOf r)
    (by simp)
  have hql : q∈l := List.mem_toFinset.mp (hcover hq)
  have hfree : q ∉ (l.take (l.idxOf q)).toFinset := by
    rw [List.mem_toFinset,List.mem_take_iff_idxOf_lt hql]
    exact lt_irrefl _
  refine ⟨l.idxOf q,List.idxOf_lt_length_of_mem hql,q,hq,hfree,?_⟩
  apply mobiusDivisor_twentyOne_last_triangle_negative _ hq hfree
  intro r hr hne
  have hrl : r∈l := List.mem_toFinset.mp (hcover hr)
  have hle := hmax r hr
  have hidx : l.idxOf r≠l.idxOf q := fun h => hne ((List.idxOf_inj hrl).mp h)
  rw [List.mem_toFinset,List.mem_take_iff_idxOf_lt hrl]
  omega

end RHTower
