import GaloisForLFunctions.RHTower.DivisorSmoothSquareMaximum
import GaloisForLFunctions.RHTower.MobiusDivisorLargePrimeOrientation
import GaloisForLFunctions.RHTower.MobiusDivisorFirstPrimeCertificateObstruction

/-!
# Every second prime is admissible after a large quotient-twelve merger

The uniform three-fifths ceiling and analytic quotient-twelve bounds control
all original four-cofactor blocks. Large second primes have no joint child;
small second primes have two parent channels approaching the same mean.
Consequently every second prime respects the original complete diagonal at
twelve times a sufficiently large first prime, even though that first state's
geometric parity certificate fails. No numerical premise is used.
-/

noncomputable section
open Finset Filter Topology
namespace RHTower
private lemma mean_lower : (0.091:ℝ) ≤
    Real.log (2*Real.pi)/2-Real.eulerMascheroniConstant-1/4 := by
  have hlog := Real.log_le_log (by norm_num : (0:ℝ)<157/25)
    (by linarith [Real.pi_gt_d2] : (157/25:ℝ)≤2*Real.pi)
  have hr := Real.log_le_sub_one_of_pos (x:=(625/628:ℝ)) (by norm_num)
  have he : Real.log (157/25:ℝ)+Real.log (625/628:ℝ) = 2*Real.log 5-2*Real.log 2 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
    rw [show (25/4:ℝ)=5^2/2^2 by norm_num,Real.log_div (by norm_num) (by norm_num),Real.log_pow,Real.log_pow]
    norm_num
  have hg := eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion
  linarith [Real.log_five_gt_d9,Real.log_two_lt_d9]
private lemma small_defects : primeFreeDivisorDefect 4 ≤ 0 ∧ primeFreeDivisorDefect 5 ≤ (0.56:ℝ) := by
  have hg := eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion
  constructor <;> norm_num [primeFreeDivisorDefect,Finset.sum_Icc_succ_top,Real.log_four_eq]
  all_goals linarith [Real.log_two_lt_d9,Real.log_three_lt_d9,Real.log_five_lt_d9]
private lemma unit_six_bound {N : ℕ} (hN : N≤6) :
    divisorUnsignedDilationChannel N 1 ≤ (0.104:ℝ)*Real.sqrt N := by
  by_cases h5 : N≤5
  · have h := divisorUnsignedDilationChannel_one_le_fifteenth_of_le_five h5
    nlinarith [Real.sqrt_nonneg (N:ℝ)]
  have he : N=6 := by omega
  subst N
  have h4 := divisorUnsignedDilationChannel_one_le_fifteenth_of_le_five (N:=4) (by omega)
  norm_num only [Nat.cast_ofNat,Real.sqrt_eq_iff_mul_self_eq_of_pos] at h4
  have hs5lo : (2.236:ℝ)≤Real.sqrt 5 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤5),Real.sqrt_nonneg (5:ℝ)]
  have hs6hi : Real.sqrt (6:ℝ)≤2.45 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤6),Real.sqrt_nonneg (6:ℝ)]
  have hs6lo : (2.44:ℝ)≤Real.sqrt 6 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤6),Real.sqrt_nonneg (6:ℝ)]
  have h54 := divisorUnsignedDilationChannel_succ 4 1
  have h65 := divisorUnsignedDilationChannel_succ 5 1
  norm_num at h54 h65 h4
  have hminus := mul_nonpos_of_nonneg_of_nonpos (show 0≤Real.sqrt (5:ℝ)-2 by linarith) small_defects.1
  have hweight : 0≤Real.sqrt (6:ℝ)-Real.sqrt 5 := sub_nonneg.mpr (Real.sqrt_le_sqrt (by norm_num))
  have hlast := mul_le_mul_of_nonneg_left small_defects.2 hweight
  nlinarith only [h54,h65,h4,hminus,hlast,hs5lo,hs6hi,hs6lo]
private lemma channel_six_bound {M d : ℕ} (hd : 0<d) (hM : M≤6*d) :
    divisorUnsignedDilationChannel M d ≤ (0.104:ℝ)*Real.sqrt M := by
  by_cases he : M=6*d
  · rw [he,Nat.mul_comm 6 d]
    have hm := divisorUnsignedDilationChannel_mul d 6 1
    simp only [Nat.mul_one] at hm
    rw [hm]
    have h := mul_le_mul_of_nonneg_left (unit_six_bound (N:=6) (by omega)) (Real.sqrt_nonneg (d:ℝ))
    push_cast
    rw [Real.sqrt_mul (Nat.cast_nonneg d)]
    nlinarith only [h]
  have hq : M/d<6 := (Nat.div_lt_iff_lt_mul hd).mpr (by omega)
  have hw0 := divisorPrimeClipWeight_nonneg M d hd
  have hw1 : 0≤1-divisorPrimeClipWeight M d := by have := divisorPrimeClipWeight_lt_one M d hd; linarith
  have h0 := mul_le_mul_of_nonneg_left (unit_six_bound (N:=M/d) (by omega)) hw1
  have h1 := mul_le_mul_of_nonneg_left (unit_six_bound (N:=M/d+1) (by omega)) hw0
  have hsum := mul_le_mul_of_nonneg_left (add_le_add h0 h1) (Real.sqrt_nonneg (d:ℝ))
  have hc := divisorUnsignedDilationChannel_prime_interpolation M d 1 hd
  simp only [Nat.mul_one] at hc
  have hclock := divisorPrimeClipWeight_mul_step M d hd
  push_cast at hclock
  rw [Real.sqrt_mul (Nat.cast_nonneg d)] at hclock
  rw [hc]
  push_cast at hsum ⊢
  nlinarith only [hsum,hclock]
private lemma defect_eleven_upper : primeFreeDivisorDefect 11 ≤ (1.22:ℝ) := by
  have hg := eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion
  have h7 := Real.log_le_sub_one_of_pos (x:=(7/8:ℝ)) (by norm_num)
  have h11 := Real.log_le_sub_one_of_pos (x:=(11/12:ℝ)) (by norm_num)
  have h4 : Real.log 4=2*Real.log 2 := Real.log_four_eq
  have h6 : Real.log 6=Real.log 2+Real.log 3 := by
    rw [← Real.log_mul (by norm_num : (2:ℝ)≠0) (by norm_num : (3:ℝ)≠0)]; norm_num
  have h8 : Real.log 8=3*Real.log 2 := by
    rw [show (8:ℝ)=2^3 by norm_num,Real.log_pow]; norm_num
  have h9 : Real.log 9=2*Real.log 3 := by
    rw [show (9:ℝ)=3^2 by norm_num,Real.log_pow]; norm_num
  have h10 : Real.log 10=Real.log 2+Real.log 5 := by
    rw [← Real.log_mul (by norm_num : (2:ℝ)≠0) (by norm_num : (5:ℝ)≠0)]; norm_num
  have h12 : Real.log 12=2*Real.log 2+Real.log 3 := by
    rw [show (12:ℝ)=4*3 by norm_num,Real.log_mul (by norm_num) (by norm_num),h4]
  rw [Real.log_div (by norm_num) (by norm_num),h8] at h7
  rw [Real.log_div (by norm_num) (by norm_num),h12] at h11
  norm_num [primeFreeDivisorDefect,Finset.sum_Icc_succ_top,h4,h6,h8,h9,h10]
  linarith [Real.log_two_lt_d9,Real.log_three_lt_d9,Real.log_five_lt_d9]
private lemma twelve_profile_bound {d : ℕ} (hd : 0<d) :
    divisorUnsignedDilationChannel 12 d ≤ (0.104:ℝ)*Real.sqrt 12 := by
  by_cases h1 : d=1
  · subst d
    have h11 := mobiusDivisorDilationChannel_eleven_box.1.2
    rw [mobiusDivisorDilationChannel_eq_moebius_unsigned] at h11
    simp only [ArithmeticFunction.moebius_apply_one,Int.cast_one,one_mul] at h11
    have hstep := divisorUnsignedDilationChannel_succ 11 1
    norm_num only at hstep
    have hs11 : (3.31662:ℝ)≤Real.sqrt 11 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤11),Real.sqrt_nonneg (11:ℝ)]
    have hs12hi : Real.sqrt (12:ℝ)≤3.46411 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤12),Real.sqrt_nonneg (12:ℝ)]
    have hs12lo : (3.464:ℝ)≤Real.sqrt 12 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤12),Real.sqrt_nonneg (12:ℝ)]
    have hw : 0≤Real.sqrt (12:ℝ)-Real.sqrt 11 := sub_nonneg.mpr (Real.sqrt_le_sqrt (by norm_num))
    have hb := mul_le_mul_of_nonneg_left defect_eleven_upper hw
    nlinarith only [hstep,h11,hs11,hs12hi,hs12lo,hb]
  · exact channel_six_bound hd (by omega)

private lemma separated_block {a b c h : ℝ} (hh : 0≤h)
    (ha : 0.09*h≤a) (hb0 : 0≤b) (hc0 : 0≤c)
    (hb : b≤0.104*h) (hc : c≤0.6*h) :
    (a-b-c)^2≤a^2+b^2+c^2 := by
  have ha0 : 0≤a := by linarith
  by_cases hs : b≤0.09*h
  · have h0 := mul_nonneg ha0 hb0
    have h1 := mul_nonneg hc0 (show 0≤a-b by linarith)
    nlinarith only [h0,h1]
  · have h1 := mul_nonneg (show 0≤0.6*h-c by linarith) (show 0≤b-0.09*h by linarith)
    have h2 := mul_nonneg (show 0≤0.104*h-b by linarith) (show 0≤0.51*h by positivity)
    have h3 := mul_nonneg (show 0≤a-0.09*h by linarith) (add_nonneg hb0 hc0)
    nlinarith [sq_nonneg h]
private lemma adjacent_block {a b c e h : ℝ} (hh : 0≤h)
    (ha : 0.09*h≤a) (hc : 0.09*h≤c) (hnear : |a-c|≤0.001*h)
    (hb0 : 0≤b) (he0 : 0≤e) (hb : b≤0.104*h) (he : e≤0.104*h) :
    (a-b-c+e)^2≤a^2+b^2+c^2+e^2 := by
  obtain ⟨hl,hu⟩ := abs_le.mp hnear
  have hsa := mul_self_le_mul_self (by positivity : 0≤0.09*h) ha
  have hsc := mul_self_le_mul_self (by positivity : 0≤0.09*h) hc
  have hs := mul_nonneg (show 0≤0.105*h-(a-b-c+e) by linarith)
    (show 0≤0.105*h+(a-b-c+e) by linarith)
  nlinarith [sq_nonneg b,sq_nonneg e,sq_nonneg h]

/-- At fixed quotient twelve, every original four-channel block contracts once
the first dilation is large, uniformly in both the second dilation and cofactor. -/
theorem exists_twelve_large_dilation_all_two_coordinate_blocks :
    ∃ T : ℕ, 1≤T ∧ ∀ p : ℕ, T≤p → ∀ q r : ℕ, 0<q → 0<r →
      (divisorUnsignedDilationChannel (12*p) r-
        divisorUnsignedDilationChannel (12*p) (p*r)-
        divisorUnsignedDilationChannel (12*p) (q*r)+
        divisorUnsignedDilationChannel (12*p) (p*(q*r)))^2 ≤
      (divisorUnsignedDilationChannel (12*p) r)^2+
        (divisorUnsignedDilationChannel (12*p) (p*r))^2+
        (divisorUnsignedDilationChannel (12*p) (q*r))^2+
        (divisorUnsignedDilationChannel (12*p) (p*(q*r)))^2 := by
  obtain ⟨T,hT,hmean⟩ := exists_divisorUnsignedDilationChannel_uniform_mean_error
    (1/2000) (by norm_num)
  refine ⟨12*T,by omega,?_⟩
  intro p hp q r hq hr
  have hp0 : 0<p := by omega
  let M := 12*p
  let c0 := Real.log (2*Real.pi)/2-Real.eulerMascheroniConstant-1/4
  have hM : 0<M := by dsimp [M]; positivity
  have hh : 0≤Real.sqrt (M:ℝ) := Real.sqrt_nonneg _
  have hz (d : ℕ) (hd : M≤d) : divisorUnsignedDilationChannel M d=0 := by
    simp [divisorUnsignedDilationChannel,Icc_eq_empty_of_lt (by omega : M-1<d)]
  have hlarge (d : ℕ) (hd : 0<d) (hdb : d≤144) :
      |divisorUnsignedDilationChannel M d-c0*Real.sqrt M|≤(1/2000:ℝ)*Real.sqrt M := by
    apply hmean M d hd
    apply (Nat.le_div_iff_mul_le hd).mpr
    have hm := Nat.mul_le_mul_left T hdb
    have hp' := Nat.mul_le_mul_left 12 hp
    dsimp [M]
    nlinarith only [hm,hp']
  have hchild (d : ℕ) (hd : 0<d) :
      divisorUnsignedDilationChannel M (p*d)≤(0.104:ℝ)*Real.sqrt M := by
    have hbound := mul_le_mul_of_nonneg_left (twelve_profile_bound hd) (Real.sqrt_nonneg (p:ℝ))
    have hm := divisorUnsignedDilationChannel_mul p 12 d
    rw [Nat.mul_comm p 12] at hm
    change divisorUnsignedDilationChannel M (p*d)=_ at hm
    rw [hm]
    have hroot : Real.sqrt (p:ℝ)*Real.sqrt 12=Real.sqrt M := by
      rw [← Real.sqrt_mul (Nat.cast_nonneg p)]
      congr 1
      simp only [M,Nat.cast_mul,Nat.cast_ofNat]
      ring
    nlinarith only [hbound,hroot]
  have hqr : r≤q*r := by
    calc
      r = 1*r := by omega
      _ ≤ q*r := Nat.mul_le_mul_right r (by omega)
  change (divisorUnsignedDilationChannel M r-divisorUnsignedDilationChannel M (p*r)-
    divisorUnsignedDilationChannel M (q*r)+divisorUnsignedDilationChannel M (p*(q*r)))^2≤_
  by_cases hr12 : r≤12
  · have hA := hlarge r hr (by omega)
    have ha : (0.09:ℝ)*Real.sqrt M≤divisorUnsignedDilationChannel M r := by
      have hc := mul_le_mul_of_nonneg_right mean_lower hh
      change (0.091:ℝ)*Real.sqrt M≤c0*Real.sqrt M at hc
      have hl := (abs_le.mp hA).1
      nlinarith only [hc,hl,hh]
    have hb := hchild r hr
    have hb0 := divisorUnsignedDilationChannel_nonneg M (p*r)
    by_cases hq12 : q≤12
    · have hqr0 : 0<q*r := Nat.mul_pos hq hr
      have hqr144 : q*r≤144 := by nlinarith only [Nat.mul_le_mul hq12 hr12]
      have hC := hlarge (q*r) hqr0 hqr144
      have hc : (0.09:ℝ)*Real.sqrt M≤divisorUnsignedDilationChannel M (q*r) := by
        have hc := mul_le_mul_of_nonneg_right mean_lower hh
        change (0.091:ℝ)*Real.sqrt M≤c0*Real.sqrt M at hc
        have hl := (abs_le.mp hC).1
        nlinarith only [hc,hl,hh]
      have hnear : |divisorUnsignedDilationChannel M r-divisorUnsignedDilationChannel M (q*r)|≤
          (0.001:ℝ)*Real.sqrt M := by
        obtain ⟨hAl,hAu⟩ := abs_le.mp hA
        obtain ⟨hCl,hCu⟩ := abs_le.mp hC
        apply abs_le.mpr
        constructor <;> linarith
      exact adjacent_block hh ha hc hnear hb0 (divisorUnsignedDilationChannel_nonneg M (p*(q*r)))
        hb (hchild (q*r) hqr0)
    · have he : divisorUnsignedDilationChannel M (p*(q*r))=0 := by
        apply hz
        have h12qr : 12≤q*r := by nlinarith only [hq12,hr,hqr]
        have hm := Nat.mul_le_mul_left p h12qr
        dsimp [M]
        nlinarith only [hm]
      rw [he]
      simp only [add_zero,zero_pow (by omega : (2:ℕ)≠0)]
      exact separated_block hh ha hb0 (divisorUnsignedDilationChannel_nonneg M (q*r)) hb
        (by simpa only [show (3/5:ℝ)=0.6 by norm_num] using
          divisorUnsignedDilationChannel_le_three_fifths_sqrt M (q*r))
  · have hb : divisorUnsignedDilationChannel M (p*r)=0 := by
      apply hz
      have hm := Nat.mul_le_mul_left p (show 12≤r by omega)
      dsimp [M]
      nlinarith only [hm]
    have he : divisorUnsignedDilationChannel M (p*(q*r))=0 := by
      apply hz
      have hm := Nat.mul_le_mul_left p ((show 12≤r by omega).trans hqr)
      dsimp [M]
      nlinarith only [hm]
    rw [hb,he]
    simp only [sub_zero,add_zero,zero_pow (by omega : (2:ℕ)≠0)]
    nlinarith [mul_nonneg (divisorUnsignedDilationChannel_nonneg M r)
      (divisorUnsignedDilationChannel_nonneg M (q*r))]

/-- Every available second prime meets the original diagonal after a sufficiently
large first prime at twelve times that prime. -/
theorem exists_twelve_large_prime_all_second_energy_bounds :
    ∃ T : ℕ, ∀ p : ℕ, T≤p → p.Prime → ∀ q : ℕ, q.Prime → q<12*p → p≠q →
      mobiusDivisorSelectionEnergy (12*p) (insert q {p}) ≤ mobiusDivisorSelectionEnergy (12*p) ∅ := by
  obtain ⟨T,hT,hblocks⟩ := exists_twelve_large_dilation_all_two_coordinate_blocks
  refine ⟨T,?_⟩
  intro p hpT hp q hq hqM hpq
  have hpM : p<12*p := by have := hp.pos; omega
  rw [mobiusDivisorSelectionEnergy_two_primes_eq_blocks (12*p) p q hpq,
    mobiusDivisorSelectionEnergy_empty_eq_two_prime_blocks (12*p) hp hq hpM hqM hpq]
  apply sum_le_sum
  intro R hR
  have hqR : q∉R := by
    intro hh
    exact (mem_erase.mp (mem_powerset.mp hR hh)).1 rfl
  have hpR : p∉R := by
    intro hh
    exact (mem_erase.mp (mem_erase.mp (mem_powerset.mp hR hh)).2).1 rfl
  have hpr : ∀ r∈R, r.Prime := by
    intro r hr
    exact (mem_filter.mp (mem_erase.mp (mem_erase.mp (mem_powerset.mp hR hr)).2).2).2
  have hpi : ∀ r∈insert p R, r.Prime := by simpa using And.intro hp hpr
  have hqi : ∀ r∈insert q R, r.Prime := by simpa using And.intro hq hpr
  have hpqi : ∀ r∈insert p (insert q R), r.Prime := by simpa using And.intro hp hqi
  rw [mobiusDivisorOrientedFibre_empty_eq_unsigned_product R hpr,
    mobiusDivisorOrientedFibre_empty_eq_unsigned_product (insert p R) hpi,
    mobiusDivisorOrientedFibre_empty_eq_unsigned_product (insert q R) hqi,
    mobiusDivisorOrientedFibre_empty_eq_unsigned_product (insert p (insert q R)) hpqi]
  simp only [prod_insert hpR,prod_insert hqR,prod_insert (show p∉insert q R by simp [hpq,hpR])]
  exact hblocks p hpT q (∏ r∈R,r) hq.pos (prod_pos (fun r hr => (hpr r hr).pos))

/-- Arbitrarily large actual first-prime states fail the geometric certificate
while every available second-prime merger still meets the original diagonal. -/
theorem exists_failed_certificate_with_all_second_energy_bounds (n : ℕ) :
    ∃ p : ℕ, n≤p ∧ p.Prime ∧
      mobiusDivisorSelectionEnergy (12*p) {p} ≤ mobiusDivisorSelectionEnergy (12*p) ∅ ∧
      mobiusDivisorSelectionEnergy (12*p) ∅ < mobiusDivisorSelectionEnergy (12*p) {p}+
        2*Real.sqrt (mobiusDivisorParityGoodEnergy (12*p) {p})*
          Real.sqrt (mobiusDivisorParityDefectEnergy (12*p) {p}) ∧
      ∀ q : ℕ, q.Prime → q<12*p → p≠q →
        mobiusDivisorSelectionEnergy (12*p) (insert q {p}) ≤ mobiusDivisorSelectionEnergy (12*p) ∅ := by
  obtain ⟨Te,he⟩ := exists_twelve_large_prime_all_second_energy_bounds
  obtain ⟨Tc,hc⟩ := exists_firstPrime_twelve_geometric_excess 0
  obtain ⟨p,hp,hpprime⟩ := Nat.exists_infinite_primes (max n (max Te Tc))
  have heP : Te≤p := (le_max_left _ _).trans ((le_max_right _ _).trans hp)
  have hcP : Tc≤p := (le_max_right _ _).trans ((le_max_right _ _).trans hp)
  have hfail := hc p hcP hpprime
  have hcontract := sum_mobiusDivisorPrimePair_sq_le hpprime (12*p)
  rw [← mobiusDivisorSelectionEnergy_singleton_eq_primePair (12*p) hpprime,
    ← mobiusDivisorSelectionEnergy_empty] at hcontract
  refine ⟨p,(le_max_left _ _).trans hp,hpprime,hcontract,?_,he p heP hpprime⟩
  linarith only [hfail]
end RHTower
