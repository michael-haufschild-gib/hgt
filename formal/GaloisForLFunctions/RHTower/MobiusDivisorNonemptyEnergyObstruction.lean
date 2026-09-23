import GaloisForLFunctions.RHTower.MobiusDivisorNonemptyEnergy
import GaloisForLFunctions.RHTower.MobiusDivisorElevenChannelBounds

/-!
# Nonempty retained energy can increase at cutoff twenty-one

After processing prime two, the three-singleton inherits a positive sign from
its exact reflected source at cutoff seven. Pairing prime five then creates
more nonempty mixed energy than its removed singleton square. Analytic boxes
for the first four divisor defects and square-root endpoints certify a strict
gain, without a numerical premise.
-/

noncomputable section
open Finset
namespace RHTower

private theorem tail_gamma_box :
    (0.5768:ℝ) ≤ Real.eulerMascheroniConstant ∧ Real.eulerMascheroniConstant ≤ 0.57722 := by
  have h := (harmonic_mascheroni_half_bounds (n := 16) (by norm_num)).2
  have hlog : Real.log (16:ℝ)=4*Real.log 2 := by
    rw [show (16:ℝ)=2^(4 : ℕ) by norm_num,Real.log_pow]
    norm_num
  norm_num [harmonic,Finset.sum_range_succ,hlog] at h
  constructor
  · linarith [Real.log_two_lt_d9]
  · linarith [eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion]

private theorem tail_defect_boxes :
    (0.1536 ≤ primeFreeDivisorDefect 1 ∧ primeFreeDivisorDefect 1 ≤ 0.1545) ∧
    (0.0003 ≤ primeFreeDivisorDefect 2 ∧ primeFreeDivisorDefect 2 ≤ 0.0021) ∧
    (0.2525 ≤ primeFreeDivisorDefect 3 ∧ primeFreeDivisorDefect 3 ≤ 0.2551) ∧
    (-0.2076 ≤ primeFreeDivisorDefect 4 ∧ primeFreeDivisorDefect 4 ≤ -0.2041) := by
  obtain ⟨hg0,hg1⟩ := tail_gamma_box
  have h2lo := Real.log_two_gt_d9
  have h2hi := Real.log_two_lt_d9
  have h3lo := Real.log_three_gt_d9
  have h3hi := Real.log_three_lt_d9
  norm_num [primeFreeDivisorDefect,Finset.sum_Icc_succ_top,Real.log_four_eq]
  constructor
  · constructor <;> linarith
  constructor
  · constructor <;> linarith
  constructor <;> constructor <;> linarith

private theorem tail_roots :
    ((2.236:ℝ) ≤ Real.sqrt 5 ∧ Real.sqrt 5 ≤ 2.237) ∧
    ((3.162:ℝ) ≤ Real.sqrt 10 ∧ Real.sqrt 10 ≤ 3.163) ∧
    ((3.872:ℝ) ≤ Real.sqrt 15 ∧ Real.sqrt 15 ≤ 3.874) ∧
    ((4.472:ℝ) ≤ Real.sqrt 20 ∧ Real.sqrt 20 ≤ 4.473) ∧
    ((4.582:ℝ) ≤ Real.sqrt 21 ∧ Real.sqrt 21 ≤ 4.583) := by
  have h (n l u : ℝ) (hn : 0 ≤ n) (hl : 0 ≤ l) (hu : 0 ≤ u)
      (hlo : l^(2 : ℕ) ≤ n) (hhi : n ≤ u^(2 : ℕ)) : l ≤ Real.sqrt n ∧ Real.sqrt n ≤ u := by
    have hs := Real.sq_sqrt hn
    have hp := Real.sqrt_nonneg n
    constructor <;> nlinarith
  exact ⟨h 5 2.236 2.237 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    h 10 3.162 3.163 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    h 15 3.872 3.874 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    h 20 4.472 4.473 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    h 21 4.582 4.583 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)⟩

private theorem tail_mobius : ArithmeticFunction.moebius 10=1 ∧ ArithmeticFunction.moebius 15=1 := by
  have hm5 := ArithmeticFunction.moebius_apply_prime Nat.prime_five
  constructor
  · simpa [ArithmeticFunction.moebius_apply_prime Nat.prime_two,hm5] using
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (show Nat.Coprime 2 5 by norm_num)
  · simpa [ArithmeticFunction.moebius_apply_prime Nat.prime_three,hm5] using
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (show Nat.Coprime 3 5 by norm_num)

private theorem tail_channel_formulas :
    mobiusDivisorDilationChannel 21 5+mobiusDivisorDilationChannel 21 10 =
      (Real.sqrt 5+Real.sqrt 20-2*Real.sqrt 10)*primeFreeDivisorDefect 1+
      (Real.sqrt 10+Real.sqrt 21-Real.sqrt 15-Real.sqrt 20)*primeFreeDivisorDefect 2-
      (Real.sqrt 20-Real.sqrt 15)*primeFreeDivisorDefect 3-
      (Real.sqrt 21-Real.sqrt 20)*primeFreeDivisorDefect 4 ∧
    mobiusDivisorDilationChannel 21 15=(Real.sqrt 21-Real.sqrt 15)*primeFreeDivisorDefect 1 := by
  obtain ⟨h10,h15⟩ := tail_mobius
  constructor
  · rw [mobiusDivisorDilationChannel_eq_quotientBlocks (by norm_num : 1 ≤ 5),
      mobiusDivisorDilationChannel_eq_quotientBlocks (by norm_num : 1 ≤ 10)]
    norm_num [sum_Icc_succ_top,divisorDilationClippedAbelWeight,h10,
      ArithmeticFunction.moebius_apply_prime Nat.prime_five]
    have r10 : Real.sqrt 10=Real.sqrt 5*Real.sqrt 2 := by
      rw [show (10:ℝ)=5*2 by norm_num,Real.sqrt_mul (by norm_num)]
    have r15 : Real.sqrt 15=Real.sqrt 5*Real.sqrt 3 := by
      rw [show (15:ℝ)=5*3 by norm_num,Real.sqrt_mul (by norm_num)]
    have r20 : Real.sqrt 20=2*Real.sqrt 5 := by
      rw [show (20:ℝ)=4*5 by norm_num,Real.sqrt_mul (by norm_num)]
      norm_num
    rw [r10,r15,r20]
    ring_nf
    norm_num [Real.sq_sqrt]
    ring
  · rw [mobiusDivisorDilationChannel_eq_quotientBlocks (by norm_num : 1 ≤ 15)]
    norm_num [sum_Icc_succ_top,divisorDilationClippedAbelWeight,h15]

private theorem positive_product_box {w x l u a b : ℝ}
    (hl : 0 ≤ l) (hw : l ≤ w ∧ w ≤ u) (hx : a ≤ x ∧ x ≤ b) (ha : 0 ≤ a) :
    l*a ≤ w*x ∧ w*x ≤ u*b := by
  have hw0 := hl.trans hw.1
  have hu0 := hw0.trans hw.2
  have hx0 := ha.trans hx.1
  exact ⟨(mul_le_mul_of_nonneg_right hw.1 ha).trans (mul_le_mul_of_nonneg_left hx.1 hw0),
    (mul_le_mul_of_nonneg_right hw.2 hx0).trans (mul_le_mul_of_nonneg_left hx.2 hu0)⟩

/-- Analytic bounds for the singleton absorbed at five and its nonempty joint partner at cutoff twenty-one. -/
theorem mobiusDivisorDilationChannel_twentyOne_tail_box :
    (-0.08 < mobiusDivisorDilationChannel 21 5+mobiusDivisorDilationChannel 21 10 ∧
      mobiusDivisorDilationChannel 21 5+mobiusDivisorDilationChannel 21 10 < -0.06) ∧
    0.1 < mobiusDivisorDilationChannel 21 15 := by
  obtain ⟨h1,h2,h3,h4⟩ := tail_defect_boxes
  obtain ⟨r5,r10,r15,r20,r21⟩ := tail_roots
  have p1 := positive_product_box (w := Real.sqrt 5+Real.sqrt 20-2*Real.sqrt 10)
    (x := primeFreeDivisorDefect 1) (l := 0.382) (u := 0.386) (by norm_num)
    ⟨by linarith,by linarith⟩ h1 (by norm_num)
  have p2 := positive_product_box (w := Real.sqrt 15+Real.sqrt 20-Real.sqrt 10-Real.sqrt 21)
    (x := primeFreeDivisorDefect 2) (l := 0.598) (u := 0.603) (by norm_num)
    ⟨by linarith,by linarith⟩ h2 (by norm_num)
  have p3 := positive_product_box (w := Real.sqrt 20-Real.sqrt 15)
    (x := primeFreeDivisorDefect 3) (l := 0.598) (u := 0.601) (by norm_num)
    ⟨by linarith,by linarith⟩ h3 (by norm_num)
  have p4 := positive_product_box (w := Real.sqrt 21-Real.sqrt 20)
    (x := -primeFreeDivisorDefect 4) (l := 0.109) (u := 0.111) (a := 0.2041) (b := 0.2076)
    (by norm_num) ⟨by linarith,by linarith⟩ ⟨by linarith,by linarith⟩ (by norm_num)
  have p15 := positive_product_box (w := Real.sqrt 21-Real.sqrt 15)
    (x := primeFreeDivisorDefect 1) (l := 0.708) (u := 0.711) (by norm_num)
    ⟨by linarith,by linarith⟩ h1 (by norm_num)
  obtain ⟨hb,hc⟩ := tail_channel_formulas
  rw [hb,hc]
  constructor
  · constructor <;> nlinarith only [p1.1,p1.2,p2.1,p2.2,p3.1,p3.2,p4.1,p4.2]
  · nlinarith only [p15.1]

private theorem tail_prime_factors :
    Nat.primeFactors 6=({2,3}:Finset ℕ) ∧ Nat.primeFactors 10=({2,5}:Finset ℕ) ∧
      Nat.primeFactors 15=({3,5}:Finset ℕ) := by
  constructor
  · rw [show (6:ℕ)=2*3 by omega,Nat.primeFactors_mul (by omega) (by omega),
      Nat.prime_two.primeFactors,Nat.prime_three.primeFactors]
    simp
  constructor
  · rw [show (10:ℕ)=2*5 by omega,Nat.primeFactors_mul (by omega) (by omega),
      Nat.prime_two.primeFactors,Nat.prime_five.primeFactors]
    simp
  · rw [show (15:ℕ)=3*5 by omega,Nat.primeFactors_mul (by omega) (by omega),
      Nat.prime_three.primeFactors,Nat.prime_five.primeFactors]
    simp

private theorem channel_twenty_zero : mobiusDivisorDilationChannel 21 20=0 := by
  have hm4 : ArithmeticFunction.moebius 4=0 := by
    simpa using ArithmeticFunction.moebius_apply_prime_pow Nat.prime_two (show (2:ℕ)≠0 by omega)
  have hm20 : ArithmeticFunction.moebius 20=0 := by
    rw [show (20:ℕ)=4*5 by omega,
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (show Nat.Coprime 4 5 by norm_num),hm4]
    simp
  simp [mobiusDivisorDilationChannel,hm20]

private theorem tail_five_fibre (R : Finset ℕ) (hpR : 5 ∉ R) :
    mobiusDivisorSelectionFibre 21 {2} (insert 5 R)=
      if R=∅ then mobiusDivisorDilationChannel 21 5+mobiusDivisorDilationChannel 21 10
      else if R={3} then mobiusDivisorDilationChannel 21 15 else 0 := by
  rw [mobiusDivisorSelectionFibre_eq_sum_Icc]
  have hrestrict : (∑ n ∈ Icc 1 21,
      if n.primeFactors \ {2}=insert 5 R then mobiusDivisorDilationChannel 21 n else 0) =
      ∑ n ∈ (Icc 1 21).filter (fun n => 5 ∣ n),
        if n.primeFactors \ {2}=insert 5 R then mobiusDivisorDilationChannel 21 n else 0 := by
    rw [sum_filter]
    apply sum_congr rfl
    intro n hn
    by_cases hpn : 5 ∣ n
    · simp [hpn]
    · have hne : n.primeFactors \ {2} ≠ insert 5 R := by
        intro he
        have hm : 5 ∈ n.primeFactors := (mem_sdiff.mp (he.symm ▸ mem_insert_self 5 R)).1
        exact hpn (Nat.mem_primeFactors.mp hm).2.1
      simp [hpn,hne]
  rw [hrestrict,sum_Icc_filter_dvd_reindex 5 21 (by omega)]
  obtain ⟨_,h10,h15⟩ := tail_prime_factors
  have h0 : ({5}:Finset ℕ)=insert 5 R ↔ R=∅ := by
    constructor
    · intro he
      have h := congrArg (fun S : Finset ℕ => S.erase 5) he
      norm_num [Finset.erase_insert,hpR] at h
      exact h.symm
    · rintro rfl
      rfl
  have h3 : ({3,5}:Finset ℕ)=insert 5 R ↔ R={3} := by
    constructor
    · intro he
      have h := congrArg (fun S : Finset ℕ => S.erase 5) he
      norm_num [Finset.erase_insert,hpR] at h
      exact h.symm
    · rintro rfl
      ext x
      simp [or_comm]
  norm_num [sum_Icc_succ_top,channel_twenty_zero,h10,h15,Nat.prime_five.primeFactors,
    Finset.sdiff_eq_filter,Finset.filter_insert,Finset.filter_singleton,h0,h3]
  by_cases hr : R=∅
  · simp [hr]
  · simp [hr]

/-- The retained three-singleton at cutoff twenty-one reverses sign through the smaller actual source at seven. -/
theorem mobiusDivisorSelectionFibre_twentyOne_three_gt :
    0.04 < mobiusDivisorSelectionFibre 21 {2} {3} := by
  have hb : mobiusDivisorSelectionFibre 7 {2} ∅=
      mobiusDivisorDilationChannel 7 1+mobiusDivisorDilationChannel 7 2 := by
    rw [mobiusDivisorSelectionFibre_eq_sum_Icc]
    obtain ⟨h4,h7⟩ := mobiusDivisorDilationChannel_seven_zero
    obtain ⟨h6,_,_⟩ := tail_prime_factors
    norm_num [sum_Icc_succ_top,h4,h7,h6,Nat.prime_two.primeFactors,
      Nat.prime_three.primeFactors,Nat.prime_five.primeFactors,Finset.sdiff_eq_filter,
      Finset.filter_insert,Finset.filter_singleton]
  have hi := mobiusDivisorSelectionFibre_prime_interpolation Nat.prime_three 21 {2} ∅
    (by simp) (by simp)
  norm_num [mobiusDivisorInterpolatedFibre,divisorPrimeClipWeight] at hi
  rw [hi,hb]
  obtain ⟨h1,h2,_,_,_⟩ := mobiusDivisorDilationChannel_seven_box
  have hs : (1.7:ℝ) < Real.sqrt 3 := by
    have := Real.sq_sqrt (by norm_num : (0:ℝ)≤3)
    have := Real.sqrt_nonneg (3:ℝ)
    nlinarith
  have hprod := mul_le_mul_of_nonneg_left
    (show (0.024:ℝ) ≤ -(mobiusDivisorDilationChannel 7 1+mobiusDivisorDilationChannel 7 2) by linarith)
    (Real.sqrt_nonneg 3)
  nlinarith only [hprod,hs]


/-- The entire nonempty energy change at cutoff twenty-one retains exactly one mixed pair. -/
theorem mobiusDivisorNonemptyEnergy_twentyOne_step :
    mobiusDivisorNonemptyEnergy 21 (insert 5 {2})-mobiusDivisorNonemptyEnergy 21 {2} =
      2*mobiusDivisorSelectionFibre 21 {2} {3}*mobiusDivisorDilationChannel 21 15-
        (mobiusDivisorDilationChannel 21 5+mobiusDivisorDilationChannel 21 10)^(2 : ℕ) := by
  rw [mobiusDivisorNonemptyEnergy_insert_cross Nat.prime_five 21 {2} (by omega) (by simp)]
  have h5 := tail_five_fibre ∅ (by simp)
  simp only [insert_empty_eq,if_true] at h5
  rw [h5]
  have hs : (∑ R ∈ (((mobiusDivisorSelectionPrimes 21).erase 5).powerset.erase ∅),
      mobiusDivisorSelectionFibre 21 {2} R*mobiusDivisorSelectionFibre 21 {2} (insert 5 R)) =
      mobiusDivisorSelectionFibre 21 {2} {3}*mobiusDivisorDilationChannel 21 15 := by
    have hmem : ({3}:Finset ℕ) ∈ (((mobiusDivisorSelectionPrimes 21).erase 5).powerset.erase ∅) := by
      apply mem_erase.mpr
      refine ⟨by simp,mem_powerset.mpr ?_⟩
      apply singleton_subset_iff.mpr
      apply mem_erase.mpr
      exact ⟨by omega,mem_filter.mpr ⟨mem_range.mpr (by omega),Nat.prime_three⟩⟩
    rw [sum_eq_single ({3}:Finset ℕ)]
    · rw [tail_five_fibre {3} (by simp)]
      simp
    · intro R hR hR3
      have hpR : 5 ∉ R := by
        intro hp
        have := mem_powerset.mp (mem_erase.mp hR).2 hp
        simp at this
      rw [tail_five_fibre R hpR,if_neg (mem_erase.mp hR).1,if_neg hR3,mul_zero]
    · intro hn
      exact (hn hmem).elim
  rw [hs]
  ring

/-- The actual nonempty-fibre energy strictly grows by more than one thousandth after primes two then five. -/
theorem mobiusDivisorNonemptyEnergy_twentyOne_strict_growth :
    1/1000+mobiusDivisorNonemptyEnergy 21 {2} < mobiusDivisorNonemptyEnergy 21 (insert 5 {2}) := by
  have ha := mobiusDivisorSelectionFibre_twentyOne_three_gt
  obtain ⟨hb,hc⟩ := mobiusDivisorDilationChannel_twentyOne_tail_box
  have hprod := mul_lt_mul_of_pos_left hc (show 0 < mobiusDivisorSelectionFibre 21 {2} {3} by linarith)
  have hbsq : (mobiusDivisorDilationChannel 21 5+mobiusDivisorDilationChannel 21 10)^(2 : ℕ) < (0.08:ℝ)^(2 : ℕ) := by
    have h := mul_pos (show 0 < mobiusDivisorDilationChannel 21 5+mobiusDivisorDilationChannel 21 10+0.08 by linarith)
      (show 0 < 0.08-(mobiusDivisorDilationChannel 21 5+mobiusDivisorDilationChannel 21 10) by linarith)
    nlinarith only [h]
  have he := mobiusDivisorNonemptyEnergy_twentyOne_step
  nlinarith only [ha,hprod,hbsq,he]

/-- Literal source arithmetic does not make every prime merger contract the energy outside the head. -/
theorem not_forall_mobiusDivisorNonemptyEnergy_insert_le :
    ¬∀ (M : ℕ) (P : Finset ℕ) (p : ℕ),p.Prime → p<M → p ∉ P →
      mobiusDivisorNonemptyEnergy M (insert p P) ≤ mobiusDivisorNonemptyEnergy M P := by
  intro hall
  have h := hall 21 {2} 5 Nat.prime_five (by omega) (by simp)
  have hg := mobiusDivisorNonemptyEnergy_twentyOne_strict_growth
  linarith only [h,hg]

end RHTower
