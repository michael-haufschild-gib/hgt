import GaloisForLFunctions.RHTower.CCMFUSuzukiMobiusDivisorDilationChannels
import GaloisForLFunctions.RHTower.HarmonicHalfErrorBounds

/-!
# Analytic boxes for the literal half-order channels at cutoffs eleven and seven

Harmonic half-reciprocal corrections, analytic logarithm inequalities and rational
square-root sandwiches bound every nonzero channel at these cutoffs. Every other channel
vanishes exactly. No numerical experiment is used as a proof input.
-/

noncomputable section
open Finset
namespace RHTower

private theorem gcd_gamma_box :
    (5768/10000 : ℝ) ≤ Real.eulerMascheroniConstant ∧
      Real.eulerMascheroniConstant ≤ 57722/100000 := by
  have h := (harmonic_mascheroni_half_bounds (n := 16) (by norm_num)).2
  have hlog : Real.log (16:ℝ) = 4*Real.log 2 := by
    rw [show (16:ℝ)=2^(4 : ℕ) by norm_num, Real.log_pow]
    norm_num
  norm_num [harmonic, Finset.sum_range_succ, hlog] at h
  constructor
  · linarith [Real.log_two_lt_d9]
  · linarith [eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion]

private theorem gcd_log_seven_box :
    (19455/10000 : ℝ) ≤ Real.log 7 ∧ Real.log 7 ≤ 19545/10000 := by
  have hi := log_le_half_sub_inv (x := (8:ℝ)/7) (by norm_num)
  have lo := Real.log_le_sub_one_of_pos (x := (7:ℝ)/8) (by norm_num)
  have h8 : Real.log (8:ℝ) = 3*Real.log 2 := by
    rw [show (8:ℝ)=2^(3 : ℕ) by norm_num, Real.log_pow]
    norm_num
  rw [Real.log_div (by norm_num) (by norm_num),h8] at hi lo
  norm_num at hi lo
  constructor <;> linarith [Real.log_two_gt_d9,Real.log_two_lt_d9]


private def gcdRootLower : ℕ → ℝ
  | 1 => 1
  | 2 => (7071/5000)
  | 3 => (433/250)
  | 4 => 2
  | 5 => (559/250)
  | 6 => (12247/5000)
  | 7 => (26457/10000)
  | 8 => (7071/2500)
  | 9 => 3
  | 10 => (15811/5000)
  | 11 => (16583/5000)
  | _ => 0

private def gcdRootUpper : ℕ → ℝ
  | 1 => 1
  | 2 => (14143/10000)
  | 3 => (17321/10000)
  | 4 => 2
  | 5 => (22361/10000)
  | 6 => (4899/2000)
  | 7 => (13229/5000)
  | 8 => (5657/2000)
  | 9 => 3
  | 10 => (31623/10000)
  | 11 => (33167/10000)
  | _ => 0

private theorem gcd_root_box {n : ℕ} (hn : n ∈ Icc 1 11) :
    gcdRootLower n ≤ Real.sqrt n ∧ Real.sqrt n ≤ gcdRootUpper n := by
  have hs := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n)
  have hp := Real.sqrt_nonneg (n:ℝ)
  obtain ⟨hn1,hn11⟩ := mem_Icc.mp hn
  interval_cases n <;> norm_num [gcdRootLower,gcdRootUpper]
  all_goals norm_num only [Nat.cast_ofNat] at hs hp
  all_goals constructor <;> nlinarith

private theorem gcd_defect_ten_explicit :
    primeFreeDivisorDefect 1 = -1+2*Real.eulerMascheroniConstant ∧
    primeFreeDivisorDefect 2 = 1*Real.log 2 - 3+4*Real.eulerMascheroniConstant ∧
    primeFreeDivisorDefect 3 = 1*Real.log 2 + 1*Real.log 3 - 5+6*Real.eulerMascheroniConstant ∧
    primeFreeDivisorDefect 4 = 3*Real.log 2 + 1*Real.log 3 - 8+8*Real.eulerMascheroniConstant ∧
    primeFreeDivisorDefect 5 = 3*Real.log 2 + 1*Real.log 3 + 1*Real.log 5 - 10+10*Real.eulerMascheroniConstant ∧
    primeFreeDivisorDefect 6 = 4*Real.log 2 + 2*Real.log 3 + 1*Real.log 5 - 14+12*Real.eulerMascheroniConstant ∧
    primeFreeDivisorDefect 7 = 4*Real.log 2 + 2*Real.log 3 + 1*Real.log 5 + 1*Real.log 7 - 16+14*Real.eulerMascheroniConstant ∧
    primeFreeDivisorDefect 8 = 7*Real.log 2 + 2*Real.log 3 + 1*Real.log 5 + 1*Real.log 7 - 20+16*Real.eulerMascheroniConstant ∧
    primeFreeDivisorDefect 9 = 7*Real.log 2 + 4*Real.log 3 + 1*Real.log 5 + 1*Real.log 7 - 23+18*Real.eulerMascheroniConstant ∧
    primeFreeDivisorDefect 10 = 8*Real.log 2 + 4*Real.log 3 + 2*Real.log 5 + 1*Real.log 7 - 27+20*Real.eulerMascheroniConstant := by
  have h4 : Real.log 4 = 2*Real.log 2 := Real.log_four_eq
  have h6 : Real.log 6 = Real.log 2+Real.log 3 := by
    rw [← Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by norm_num : (3:ℝ) ≠ 0)]
    norm_num
  have h8 : Real.log 8 = 3*Real.log 2 := by
    rw [show (8:ℝ)=2^(3 : ℕ) by norm_num,Real.log_pow]
    norm_num
  have h9 : Real.log 9 = 2*Real.log 3 := by
    rw [show (9:ℝ)=3^(2 : ℕ) by norm_num,Real.log_pow]
    norm_num
  have h10 : Real.log 10 = Real.log 2+Real.log 5 := by
    rw [← Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by norm_num : (5:ℝ) ≠ 0)]
    norm_num
  norm_num [primeFreeDivisorDefect,Finset.sum_Icc_succ_top,h4,h6,h8,h9,h10]
  all_goals ring_nf
  all_goals trivial

private def gcdDefectLower : ℕ → ℝ
  | 1 => 0.1536
  | 2 => 0.0003
  | 3 => 0.2525
  | 4 => -0.2076
  | 5 => 0.5554
  | 6 => -0.4992
  | 7 => 0.5999
  | 8 => -0.1671
  | 9 => 0.1838
  | 10 => -0.3601
  | _ => 0

private def gcdDefectUpper : ℕ → ℝ
  | 1 => 0.1545
  | 2 => 0.0021
  | 3 => 0.2551
  | 4 => -0.2041
  | 5 => 0.5598
  | 6 => -0.4940
  | 7 => 0.6149
  | 8 => -0.1512
  | 9 => 0.2004
  | 10 => -0.3425
  | _ => 0

private theorem gcd_defect_box {q : ℕ} (hq : q ∈ Icc 1 10) :
    gcdDefectLower q ≤ primeFreeDivisorDefect q ∧
      primeFreeDivisorDefect q ≤ gcdDefectUpper q := by
  obtain ⟨hglo,hghi⟩ := gcd_gamma_box
  obtain ⟨h7lo,h7hi⟩ := gcd_log_seven_box
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩ := gcd_defect_ten_explicit
  obtain ⟨hq1,hq10⟩ := mem_Icc.mp hq
  have h2lo := Real.log_two_gt_d9
  have h2hi := Real.log_two_lt_d9
  have h3lo := Real.log_three_gt_d9
  have h3hi := Real.log_three_lt_d9
  have h5lo := Real.log_five_gt_d9
  have h5hi := Real.log_five_lt_d9
  interval_cases q
  all_goals simp only [gcdDefectLower,gcdDefectUpper,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10]
  all_goals constructor <;> linarith


private def gcdAbelStep (k : ℕ) : ℝ := Real.sqrt (k+1 : ℕ)-Real.sqrt k
private def gcdWeightLower (k : ℕ) : ℝ := gcdRootLower (k+1)-gcdRootUpper k
private def gcdWeightUpper (k : ℕ) : ℝ := gcdRootUpper (k+1)-gcdRootLower k

private theorem gcd_weight_box {k : ℕ} (hk : k ∈ Icc 1 10) :
    0 ≤ gcdWeightLower k ∧
      (gcdWeightLower k ≤ gcdAbelStep k ∧ gcdAbelStep k ≤ gcdWeightUpper k) := by
  have hk1 : k ∈ Icc 1 11 := by have := mem_Icc.mp hk; simp only [mem_Icc]; omega
  have hk2 : k+1 ∈ Icc 1 11 := by have := mem_Icc.mp hk; simp only [mem_Icc]; omega
  have h1 := gcd_root_box hk1
  have h2 := gcd_root_box hk2
  constructor
  · obtain ⟨hlo,hhi⟩ := mem_Icc.mp hk
    interval_cases k <;> norm_num [gcdWeightLower,gcdRootLower,gcdRootUpper]
  · dsimp [gcdWeightLower,gcdWeightUpper,gcdAbelStep]
    constructor <;> linarith [h1.1,h1.2,h2.1,h2.2]

private theorem gcd_mul_nonneg_box {w x l u a b : ℝ}
    (hl : 0 ≤ l) (hw : l ≤ w ∧ w ≤ u) (hx : a ≤ x ∧ x ≤ b) (ha : 0 ≤ a) :
    l*a ≤ w*x ∧ w*x ≤ u*b := by
  have hw0 := hl.trans hw.1
  have hu0 := hw0.trans hw.2
  have hx0 := ha.trans hx.1
  constructor
  · exact (mul_le_mul_of_nonneg_right hw.1 ha).trans
      (mul_le_mul_of_nonneg_left hx.1 hw0)
  · exact (mul_le_mul_of_nonneg_right hw.2 hx0).trans
      (mul_le_mul_of_nonneg_left hx.2 hu0)

private theorem gcd_mul_nonpos_box {w x l u a b : ℝ}
    (hl : 0 ≤ l) (hw : l ≤ w ∧ w ≤ u) (hx : a ≤ x ∧ x ≤ b) (hb : b ≤ 0) :
    u*a ≤ w*x ∧ w*x ≤ l*b := by
  have h := gcd_mul_nonneg_box (w := w) (x := -x) (a := -b) (b := -a)
    hl hw ⟨by linarith,by linarith⟩ (by linarith)
  constructor <;> nlinarith only [h.1,h.2]

private def gcdNegativeDefects : Finset ℕ := {4,6,8,10}
private def gcdTermLower (k q : ℕ) : ℝ :=
  if q ∈ gcdNegativeDefects then gcdWeightUpper k*gcdDefectLower q
  else gcdWeightLower k*gcdDefectLower q
private def gcdTermUpper (k q : ℕ) : ℝ :=
  if q ∈ gcdNegativeDefects then gcdWeightLower k*gcdDefectUpper q
  else gcdWeightUpper k*gcdDefectUpper q

private theorem gcd_term_box {k q : ℕ} (hk : k ∈ Icc 1 10) (hq : q ∈ Icc 1 10) :
    gcdTermLower k q ≤ gcdAbelStep k*primeFreeDivisorDefect q ∧
      gcdAbelStep k*primeFreeDivisorDefect q ≤ gcdTermUpper k q := by
  obtain ⟨hwp,hw⟩ := gcd_weight_box hk
  have hD := gcd_defect_box hq
  by_cases hneg : q ∈ gcdNegativeDefects
  · have hsign : gcdDefectUpper q ≤ 0 := by
      simp only [gcdNegativeDefects,mem_insert,mem_singleton] at hneg
      rcases hneg with rfl | rfl | rfl | rfl <;> norm_num [gcdDefectUpper]
    simpa only [gcdTermLower,gcdTermUpper,hneg,if_true] using
      gcd_mul_nonpos_box hwp hw hD hsign
  · have hsign : 0 ≤ gcdDefectLower q := by
      obtain ⟨hlo,hhi⟩ := mem_Icc.mp hq
      interval_cases q <;> norm_num [gcdNegativeDefects,gcdDefectLower] at *
    simpa only [gcdTermLower,gcdTermUpper,hneg,if_false] using
      gcd_mul_nonneg_box hwp hw hD hsign


private def gcdActiveEleven : Finset ℕ := {1,2,3,5,6,7,10}
private def gcdChannelLower : ℕ → ℝ
  | 1 => 0.15 | 2 => 0.20 | 3 => 0.19 | 5 => 0.14
  | 6 => 0.13 | 7 => 0.10 | 10 => 0.023 | _ => 0
private def gcdChannelUpper : ℕ → ℝ
  | 1 => 0.18 | 2 => 0.21 | 3 => 0.20 | 5 => 0.15
  | 6 => 0.14 | 7 => 0.11 | 10 => 0.025 | _ => 0
private def gcdUnsignedEleven (d : ℕ) : ℝ :=
  ∑ k ∈ Icc d 10, gcdAbelStep k*primeFreeDivisorDefect (k/d)

set_option maxHeartbeats 800000 in
private theorem gcd_unsigned_eleven_box {d : ℕ} (hd : d ∈ gcdActiveEleven) :
    gcdChannelLower d ≤ gcdUnsignedEleven d ∧
      gcdUnsignedEleven d ≤ gcdChannelUpper d := by
  have hd1 : 1 ≤ d := by
    simp only [gcdActiveEleven,mem_insert,mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hidx (k : ℕ) (hk : k ∈ Icc d 10) :
      k ∈ Icc 1 10 ∧ k/d ∈ Icc 1 10 := by
    obtain ⟨hdk,hk10⟩ := mem_Icc.mp hk
    constructor
    · exact mem_Icc.mpr ⟨hd1.trans hdk,hk10⟩
    · apply mem_Icc.mpr
      constructor
      · exact (Nat.le_div_iff_mul_le (by omega : 0 < d)).mpr (by simpa using hdk)
      · exact (Nat.div_le_self k d).trans hk10
  have hlo : (∑ k ∈ Icc d 10, gcdTermLower k (k/d)) ≤ gcdUnsignedEleven d := by
    apply sum_le_sum
    intro k hk
    exact (gcd_term_box (hidx k hk).1 (hidx k hk).2).1
  have hhi : gcdUnsignedEleven d ≤ ∑ k ∈ Icc d 10, gcdTermUpper k (k/d) := by
    apply sum_le_sum
    intro k hk
    exact (gcd_term_box (hidx k hk).1 (hidx k hk).2).2
  simp only [gcdActiveEleven,mem_insert,mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [sum_Icc_succ_top,gcdTermLower,gcdTermUpper,gcdNegativeDefects,
    gcdWeightLower,gcdWeightUpper,gcdRootLower,gcdRootUpper,gcdDefectLower,gcdDefectUpper,
    gcdChannelLower,gcdChannelUpper] at hlo hhi ⊢
  all_goals constructor <;> linarith

private theorem gcd_signed_eleven (d : ℕ) :
    mobiusDivisorDilationChannel 11 d =
      ((ArithmeticFunction.moebius d : ℤ) : ℝ)*gcdUnsignedEleven d := rfl

/-- Analytic rational bounds for every nonzero channel at the first coprime-component witness. -/
theorem mobiusDivisorDilationChannel_eleven_box :
    (0.15 ≤ mobiusDivisorDilationChannel 11 1 ∧ mobiusDivisorDilationChannel 11 1 ≤ 0.18) ∧
    (0.20 ≤ -mobiusDivisorDilationChannel 11 2 ∧ -mobiusDivisorDilationChannel 11 2 ≤ 0.21) ∧
    (0.19 ≤ -mobiusDivisorDilationChannel 11 3 ∧ -mobiusDivisorDilationChannel 11 3 ≤ 0.20) ∧
    (0.14 ≤ -mobiusDivisorDilationChannel 11 5 ∧ -mobiusDivisorDilationChannel 11 5 ≤ 0.15) ∧
    (0.13 ≤ mobiusDivisorDilationChannel 11 6 ∧ mobiusDivisorDilationChannel 11 6 ≤ 0.14) ∧
    (0.10 ≤ -mobiusDivisorDilationChannel 11 7 ∧ -mobiusDivisorDilationChannel 11 7 ≤ 0.11) ∧
    (0.023 ≤ mobiusDivisorDilationChannel 11 10 ∧ mobiusDivisorDilationChannel 11 10 ≤ 0.025) := by
  have hm2 := ArithmeticFunction.moebius_apply_prime Nat.prime_two
  have hm3 := ArithmeticFunction.moebius_apply_prime Nat.prime_three
  have hm5 := ArithmeticFunction.moebius_apply_prime Nat.prime_five
  have hm7 := ArithmeticFunction.moebius_apply_prime (show Nat.Prime 7 by norm_num)
  have hm6 : ArithmeticFunction.moebius 6 = 1 := by
    simpa [hm2,hm3] using ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
      (show Nat.gcd 2 3 = 1 by rfl)
  have hm10 : ArithmeticFunction.moebius 10 = 1 := by
    simpa [hm2,hm5] using ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
      (show Nat.gcd 2 5 = 1 by rfl)
  have h1 := gcd_unsigned_eleven_box (d := 1) (by simp [gcdActiveEleven])
  have h2 := gcd_unsigned_eleven_box (d := 2) (by simp [gcdActiveEleven])
  have h3 := gcd_unsigned_eleven_box (d := 3) (by simp [gcdActiveEleven])
  have h5 := gcd_unsigned_eleven_box (d := 5) (by simp [gcdActiveEleven])
  have h6 := gcd_unsigned_eleven_box (d := 6) (by simp [gcdActiveEleven])
  have h7 := gcd_unsigned_eleven_box (d := 7) (by simp [gcdActiveEleven])
  have h10 := gcd_unsigned_eleven_box (d := 10) (by simp [gcdActiveEleven])
  simpa only [gcd_signed_eleven,hm2,hm3,hm5,hm6,hm7,hm10,
    ArithmeticFunction.moebius_apply_one,Int.cast_one,Int.cast_neg,neg_mul,one_mul,neg_neg,
    gcdChannelLower,gcdChannelUpper] using And.intro h1 (And.intro h2
      (And.intro h3 (And.intro h5 (And.intro h6 (And.intro h7 h10)))))

/-- Every omitted channel at cutoff eleven vanishes exactly. -/
theorem mobiusDivisorDilationChannel_eleven_zero :
    mobiusDivisorDilationChannel 11 4 = 0 ∧ mobiusDivisorDilationChannel 11 8 = 0 ∧
      mobiusDivisorDilationChannel 11 9 = 0 ∧ mobiusDivisorDilationChannel 11 11 = 0 := by
  have hm4 : ArithmeticFunction.moebius 4 = 0 := by
    simpa using ArithmeticFunction.moebius_apply_prime_pow Nat.prime_two
      (show (2:ℕ) ≠ 0 by norm_num)
  have hm8 : ArithmeticFunction.moebius 8 = 0 := by
    simpa using ArithmeticFunction.moebius_apply_prime_pow Nat.prime_two
      (show (3:ℕ) ≠ 0 by norm_num)
  have hm9 : ArithmeticFunction.moebius 9 = 0 := by
    simpa using ArithmeticFunction.moebius_apply_prime_pow Nat.prime_three
      (show (2:ℕ) ≠ 0 by norm_num)
  simp [mobiusDivisorDilationChannel,hm4,hm8,hm9]

private def adaptiveActiveSeven : Finset ℕ := {1,2,3,5,6}
private def adaptiveChannelLower : ℕ → ℝ
  | 1 => 0.102 | 2 => 0.139 | 3 => 0.110 | 5 => 0.060 | 6 => 0.030 | _ => 0
private def adaptiveChannelUpper : ℕ → ℝ
  | 1 => 0.115 | 2 => 0.145 | 3 => 0.115 | 5 => 0.065 | 6 => 0.031 | _ => 0
private def adaptiveUnsignedSeven (d : ℕ) : ℝ :=
  ∑ k ∈ Icc d 6, gcdAbelStep k*primeFreeDivisorDefect (k/d)

private theorem adaptive_unsigned_seven_box {d : ℕ} (hd : d ∈ adaptiveActiveSeven) :
    adaptiveChannelLower d ≤ adaptiveUnsignedSeven d ∧
      adaptiveUnsignedSeven d ≤ adaptiveChannelUpper d := by
  have hd1 : 1 ≤ d := by
    simp only [adaptiveActiveSeven,mem_insert,mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl <;> omega
  have hidx (k : ℕ) (hk : k ∈ Icc d 6) :
      k ∈ Icc 1 10 ∧ k/d ∈ Icc 1 10 := by
    obtain ⟨hdk,hk10⟩ := mem_Icc.mp hk
    constructor
    · exact mem_Icc.mpr ⟨hd1.trans hdk,by omega⟩
    · apply mem_Icc.mpr
      constructor
      · exact (Nat.le_div_iff_mul_le (by omega : 0 < d)).mpr (by simpa using hdk)
      · exact (Nat.div_le_self k d).trans (by omega : k ≤ 10)
  have hlo : (∑ k ∈ Icc d 6, gcdTermLower k (k/d)) ≤ adaptiveUnsignedSeven d := by
    apply sum_le_sum
    intro k hk
    exact (gcd_term_box (hidx k hk).1 (hidx k hk).2).1
  have hhi : adaptiveUnsignedSeven d ≤ ∑ k ∈ Icc d 6, gcdTermUpper k (k/d) := by
    apply sum_le_sum
    intro k hk
    exact (gcd_term_box (hidx k hk).1 (hidx k hk).2).2
  simp only [adaptiveActiveSeven,mem_insert,mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [sum_Icc_succ_top,gcdTermLower,gcdTermUpper,gcdNegativeDefects,
    gcdWeightLower,gcdWeightUpper,gcdRootLower,gcdRootUpper,gcdDefectLower,gcdDefectUpper,
    adaptiveChannelLower,adaptiveChannelUpper] at hlo hhi ⊢
  all_goals constructor <;> linarith


/-- Analytic channel boxes for the order-independent last-pair obstruction at seven. -/
theorem mobiusDivisorDilationChannel_seven_box :
    (0.102 ≤ mobiusDivisorDilationChannel 7 1 ∧ mobiusDivisorDilationChannel 7 1 ≤ 0.115) ∧
    (0.139 ≤ -mobiusDivisorDilationChannel 7 2 ∧ -mobiusDivisorDilationChannel 7 2 ≤ 0.145) ∧
    (0.110 ≤ -mobiusDivisorDilationChannel 7 3 ∧ -mobiusDivisorDilationChannel 7 3 ≤ 0.115) ∧
    (0.060 ≤ -mobiusDivisorDilationChannel 7 5 ∧ -mobiusDivisorDilationChannel 7 5 ≤ 0.065) ∧
    (0.030 ≤ mobiusDivisorDilationChannel 7 6 ∧ mobiusDivisorDilationChannel 7 6 ≤ 0.031) := by
  have hm2 := ArithmeticFunction.moebius_apply_prime Nat.prime_two
  have hm3 := ArithmeticFunction.moebius_apply_prime Nat.prime_three
  have hm5 := ArithmeticFunction.moebius_apply_prime Nat.prime_five
  have hm6 : ArithmeticFunction.moebius 6 = 1 := by
    simpa [hm2,hm3] using ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
      (show Nat.gcd 2 3 = 1 by rfl)
  have h1 := adaptive_unsigned_seven_box (d := 1) (by simp [adaptiveActiveSeven])
  have h2 := adaptive_unsigned_seven_box (d := 2) (by simp [adaptiveActiveSeven])
  have h3 := adaptive_unsigned_seven_box (d := 3) (by simp [adaptiveActiveSeven])
  have h5 := adaptive_unsigned_seven_box (d := 5) (by simp [adaptiveActiveSeven])
  have h6 := adaptive_unsigned_seven_box (d := 6) (by simp [adaptiveActiveSeven])
  have heq (d : ℕ) : mobiusDivisorDilationChannel 7 d =
      ((ArithmeticFunction.moebius d : ℤ):ℝ)*adaptiveUnsignedSeven d := rfl
  simpa only [heq,hm2,hm3,hm5,hm6,ArithmeticFunction.moebius_apply_one,
    Int.cast_one,Int.cast_neg,neg_mul,one_mul,neg_neg,adaptiveChannelLower,adaptiveChannelUpper]
    using And.intro h1 (And.intro h2 (And.intro h3 (And.intro h5 h6)))

/-- The squareful and terminal channels at seven vanish exactly. -/
theorem mobiusDivisorDilationChannel_seven_zero :
    mobiusDivisorDilationChannel 7 4 = 0 ∧ mobiusDivisorDilationChannel 7 7 = 0 := by
  have hm4 : ArithmeticFunction.moebius 4 = 0 := by
    simpa using ArithmeticFunction.moebius_apply_prime_pow Nat.prime_two
      (show (2:ℕ) ≠ 0 by norm_num)
  simp [mobiusDivisorDilationChannel,hm4]

end RHTower
