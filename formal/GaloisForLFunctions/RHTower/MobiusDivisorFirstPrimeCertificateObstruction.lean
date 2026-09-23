import GaloisForLFunctions.RHTower.DivisorUnsignedChannelExactMean
import GaloisForLFunctions.RHTower.MobiusDivisorElevenChannelBounds
import GaloisForLFunctions.RHTower.MobiusDivisorFirstPrimeReserve
import GaloisForLFunctions.RHTower.MobiusDivisorParityDefectTransport
import GaloisForLFunctions.RHTower.DivisorUniformSquareRootBound

/-!
# A first-prime energy contraction whose geometric certificate fails

At the fixed quotient twelve the unsigned unit channel exceeds its limiting
square-root coefficient. For a large prime p at cutoff 12p this creates a
negative head of square-root size. Its complete defect energy is linear in p,
whereas complete good energy remains quadratic and the released diagonal
reserve is only linear. The geometric certificate excess grows faster than
every fixed multiple of p, although actual first-prime energy contracts.
All estimates retain the complete source and use analytic bounds only.
-/

noncomputable section
open Finset Filter Topology
namespace RHTower
private lemma gamma_lower : (0.5768:ℝ) ≤ Real.eulerMascheroniConstant := by
  have h := (harmonic_mascheroni_half_bounds (n := 16) (by norm_num)).2
  have hlog : Real.log (16:ℝ)=4*Real.log 2 := by
    rw [show (16:ℝ)=2^(4 : ℕ) by norm_num,Real.log_pow]
    norm_num
  norm_num [harmonic,Finset.sum_range_succ,hlog] at h
  linarith [Real.log_two_lt_d9]
private lemma mean_upper :
    Real.log (2*Real.pi)/2-Real.eulerMascheroniConstant-1/4 ≤ (37/400:ℝ) := by
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ)≤1.838) 12
  norm_num [Finset.sum_range_succ, Nat.factorial] at he
  have hlog : Real.log (2*Real.pi) < (1.838:ℝ) := by
    apply (Real.log_lt_iff_lt_exp (by positivity)).mpr
    linarith [Real.pi_lt_d4]
  linarith [gamma_lower]
private lemma defect_eleven_lower : (1.175:ℝ) ≤ primeFreeDivisorDefect 11 := by
  have h7 := log_le_half_sub_inv (x := (8:ℝ)/7) (by norm_num)
  have h8 : Real.log (8:ℝ)=3*Real.log 2 := by
    rw [show (8:ℝ)=2^(3 : ℕ) by norm_num,Real.log_pow]; norm_num
  rw [Real.log_div (by norm_num) (by norm_num),h8] at h7
  norm_num at h7
  have h11 := Real.log_le_log (by norm_num : (0:ℝ)<2^(8 : ℕ)*5)
    (by norm_num : (2:ℝ)^(8 : ℕ)*5≤11^(3 : ℕ))
  rw [Real.log_mul (by norm_num) (by norm_num)] at h11
  simp only [Real.log_pow, Nat.cast_ofNat] at h11
  have h4 : Real.log 4=2*Real.log 2 := Real.log_four_eq
  have h6 : Real.log 6=Real.log 2+Real.log 3 := by
    rw [← Real.log_mul (by norm_num : (2:ℝ)≠0) (by norm_num : (3:ℝ)≠0)]; norm_num
  have h9 : Real.log 9=2*Real.log 3 := by
    rw [show (9:ℝ)=3^(2 : ℕ) by norm_num,Real.log_pow]; norm_num
  have h10 : Real.log 10=Real.log 2+Real.log 5 := by
    rw [← Real.log_mul (by norm_num : (2:ℝ)≠0) (by norm_num : (5:ℝ)≠0)]; norm_num
  norm_num [primeFreeDivisorDefect,Finset.sum_Icc_succ_top,h4,h6,h8,h9,h10]
  linarith [gamma_lower,Real.log_two_gt_d9,Real.log_three_gt_d9,Real.log_five_gt_d9]
private lemma twelve_lower : (0.323:ℝ) ≤ divisorUnsignedDilationChannel 12 1 := by
  have h11 := mobiusDivisorDilationChannel_eleven_box.1.1
  rw [mobiusDivisorDilationChannel_eq_moebius_unsigned] at h11
  simp only [ArithmeticFunction.moebius_apply_one,Int.cast_one,one_mul] at h11
  have hstep := divisorUnsignedDilationChannel_succ 11 1
  norm_num only at hstep
  have hs11 : Real.sqrt (11:ℝ)≤3.3167 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤11),Real.sqrt_nonneg (11:ℝ)]
  have hs12 : (3.464:ℝ)≤Real.sqrt 12 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤12),Real.sqrt_nonneg (12:ℝ)]
  have hm := mul_nonneg (show 0≤Real.sqrt (12:ℝ)-Real.sqrt 11-0.1473 by linarith)
    (show 0≤primeFreeDivisorDefect 11-1.175 by linarith [defect_eleven_lower])
  nlinarith [defect_eleven_lower]
/-- The exact quotient-twelve profile exceeds the asymptotic unsigned coefficient
by at least one two-thousandth of its square-root scale. -/
theorem divisorUnsignedDilationChannel_twelve_mean_overshoot :
    (Real.log (2*Real.pi)/2-Real.eulerMascheroniConstant-1/4+1/2000)*Real.sqrt 12 ≤
      divisorUnsignedDilationChannel 12 1 := by
  have hs12 : Real.sqrt (12:ℝ)≤3.465 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤12),Real.sqrt_nonneg (12:ℝ)]
  have h := mul_le_mul_of_nonneg_right mean_upper (Real.sqrt_nonneg (12:ℝ))
  nlinarith [twelve_lower]

private lemma twelve_head_defect :
    ∃ T : ℕ, 1≤T ∧ ∀ p : ℕ, T≤p → p.Prime →
      (p:ℝ)/2000000 ≤ mobiusDivisorParityDefectEnergy (12*p) {p} := by
  obtain ⟨T,hT,hmean⟩ := exists_divisorUnsignedDilationChannel_uniform_mean_error
    (1/4000) (by norm_num)
  refine ⟨T,hT,?_⟩
  intro p hpT hp
  have hp0 : 0≤Real.sqrt (p:ℝ) := Real.sqrt_nonneg _
  have hm : T≤(12*p)/1 := by omega
  have hupper := (abs_le.mp (hmean (12*p) 1 (by norm_num) hm)).2
  have hchild := mul_le_mul_of_nonneg_left divisorUnsignedDilationChannel_twelve_mean_overshoot hp0
  have hmul := divisorUnsignedDilationChannel_mul p 12 1
  simp only [Nat.mul_one] at hmul
  rw [Nat.mul_comm p 12] at hmul
  have hroot : Real.sqrt (p:ℝ)*Real.sqrt 12=Real.sqrt (12*p:ℕ) := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg p)]
    congr 1
    push_cast
    ring
  have hhead : mobiusDivisorOrientedFibre (12*p) {p} ∅ =
      divisorUnsignedDilationChannel (12*p) 1-divisorUnsignedDilationChannel (12*p) p := by
    change mobiusDivisorOrientedFibre (12*p) (insert p ∅) ∅ = _
    rw [mobiusDivisorOrientedFibre_insert _ ∅ ∅ p (notMem_empty p),insert_empty_eq,
      mobiusDivisorOrientedFibre_empty_eq_unsigned_product ∅ (by simp) (12*p),
      mobiusDivisorOrientedFibre_empty_eq_unsigned_product {p} (by simpa using hp) (12*p)]
    simp
  have hlow : Real.sqrt (12*p:ℕ)/4000 ≤ -mobiusDivisorOrientedFibre (12*p) {p} ∅ := by
    rw [hhead,hmul]
    have hscaled := congrArg (fun x : ℝ =>
      (Real.log (2*Real.pi)/2-Real.eulerMascheroniConstant-1/4+1/2000)*x) hroot
    nlinarith only [hupper,hchild,hscaled]
  have hmax : Real.sqrt (12*p:ℕ)/4000 ≤ max (-mobiusDivisorOrientedFibre (12*p) {p} ∅) 0 :=
    hlow.trans (le_max_left _ _)
  have hsq := mul_self_le_mul_self (by positivity : 0≤Real.sqrt (12*p:ℕ)/4000) hmax
  have hsum : (max (-mobiusDivisorOrientedFibre (12*p) {p} ∅) 0)^(2 : ℕ) ≤
      mobiusDivisorParityDefectEnergy (12*p) {p} := by
    unfold mobiusDivisorParityDefectEnergy
    exact Finset.single_le_sum
      (f := fun R : Finset ℕ => (max (-mobiusDivisorOrientedFibre (12*p) {p} R) 0)^(2 : ℕ))
      (fun R _ => sq_nonneg _) (mem_powerset.mpr (empty_subset _))
  have hs := Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) (12*p))
  norm_num only [Nat.cast_mul,Nat.cast_ofNat] at hs hsq
  nlinarith only [hs,hsq,hsum,Nat.cast_nonneg (α:=ℝ) p]

private lemma twelve_defect_upper {p : ℕ} (hp : p.Prime) :
    mobiusDivisorParityDefectEnergy (12*p) {p} ≤ 122018*(p:ℝ) := by
  have hp0 : 0<p := hp.pos
  have hdiv : (12*p)/p=12 := Nat.mul_div_cancel 12 hp0
  have h := mobiusDivisorParityDefectEnergy_singleton_le_quadratic (12*p) hp (by omega)
  rw [hdiv] at h
  norm_num only [Nat.cast_ofNat,Nat.reduceAdd,Nat.reducePow] at h
  have hw := divisorPrimeClipWeight_nonneg (12*p) p hp0
  have hw1 := divisorPrimeClipWeight_lt_one (12*p) p hp0
  nlinarith [mul_nonneg (show 0≤(p:ℝ) by positivity) (show 0≤1-divisorPrimeClipWeight (12*p) p by linarith)]

private lemma twelve_release_upper {p : ℕ} (hp : p.Prime) :
    mobiusDivisorSelectionEnergy (12*p) ∅-mobiusDivisorSelectionEnergy (12*p) {p} ≤
      14112*(p:ℝ) := by
  let M := 12*p
  let f := fun d => (((ArithmeticFunction.moebius d:ℤ):ℝ)^(2 : ℕ)*
      divisorUnsignedDilationChannel M d*divisorUnsignedDilationChannel M (p*d))
  have hnon (d : ℕ) : 0≤f d := mul_nonneg
    (mul_nonneg (sq_nonneg _) (divisorUnsignedDilationChannel_nonneg M d))
    (divisorUnsignedDilationChannel_nonneg M (p*d))
  have hterm (d : ℕ) : f d≤49*(M:ℝ) := by
    have hmu : (((ArithmeticFunction.moebius d:ℤ):ℝ))^(2 : ℕ)≤1 := by
      have h : |((ArithmeticFunction.moebius d:ℤ):ℝ)|≤1 := by
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n:=d))
      obtain ⟨hl,hu⟩ := abs_le.mp h
      nlinarith
    have ha := divisorUnsignedDilationChannel_le_seven_sqrt M d
    have hb := divisorUnsignedDilationChannel_le_seven_sqrt M (p*d)
    have hab := mul_le_mul ha hb (divisorUnsignedDilationChannel_nonneg M (p*d)) (by positivity)
    have hscale := mul_le_mul_of_nonneg_right hmu
      (mul_nonneg (divisorUnsignedDilationChannel_nonneg M d)
        (divisorUnsignedDilationChannel_nonneg M (p*d)))
    have hs := Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) M)
    dsimp [f]
    nlinarith only [hab,hscale,hs]
  have hrestrict : (∑ d ∈ Icc 1 M,f d) = ∑ d ∈ Icc 1 12,f d := by
    symm
    apply sum_subset
    · intro d hd
      obtain ⟨hl,hu⟩ := mem_Icc.mp hd
      apply mem_Icc.mpr
      exact ⟨hl,hu.trans (by dsimp [M]; have := hp.one_le; omega)⟩
    · intro d hd hnot
      have hd12 : 12<d := by
        have hd1 := (mem_Icc.mp hd).1
        simp only [mem_Icc] at hnot
        omega
      have hmd : M<p*d := by
        dsimp [M]
        have h := Nat.mul_lt_mul_of_pos_left hd12 hp.pos
        omega
      have hz : divisorUnsignedDilationChannel M (p*d)=0 := by
        simp [divisorUnsignedDilationChannel,Icc_eq_empty_of_lt (by omega : M-1<p*d)]
      simp [f,hz]
  have hfilter : (∑ d ∈ (Icc 1 M).filter (fun d => ¬p∣d),f d) ≤ ∑ d ∈ Icc 1 M,f d :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun d _ _ => hnon d)
  rw [hrestrict] at hfilter
  have hsum := sum_le_sum (s:=Icc 1 12) (fun d _ => hterm d)
  norm_num at hsum
  have he := sum_mobiusDivisorPrimePair_sq_eq hp M
  rw [← mobiusDivisorSelectionEnergy_singleton_eq_primePair M hp,
    ← mobiusDivisorSelectionEnergy_empty] at he
  change mobiusDivisorSelectionEnergy M {p}=mobiusDivisorSelectionEnergy M ∅-2*∑ d ∈ (Icc 1 M).filter (fun d => ¬p∣d),f d at he
  change mobiusDivisorSelectionEnergy M ∅-mobiusDivisorSelectionEnergy M {p}≤_
  have hM : (M:ℝ)=12*(p:ℝ) := by simp [M]
  nlinarith only [he,hfilter,hsum,hM]

private lemma twelve_diagonal_lower :
    ∃ b : ℝ, 0<b ∧ ∃ T : ℕ, ∀ p : ℕ, T≤p →
      b*(p:ℝ)^(2 : ℕ) ≤ mobiusDivisorSelectionEnergy (12*p) ∅ := by
  obtain ⟨c,hc,T,hT,h⟩ := exists_mobiusDivisorSelectionEnergy_first_prime_reserve
  refine ⟨72*c,by positivity,T,?_⟩
  intro p hpT
  have hr := h (12*p) 2 (by norm_num) (by omega)
  have hq : 0≤ mobiusDivisorSelectionEnergy (12*p) {2} := by
    rw [← mobiusDivisorParityGoodEnergy_add_defect]
    exact add_nonneg (mobiusDivisorParityGoodEnergy_nonneg _ _) (mobiusDivisorParityDefectEnergy_nonneg _ _)
  push_cast at hr
  nlinarith only [hr,hq]

/-- At fixed quotient twelve, the complete good energy has a quadratic lower bound,
while both defect energy and released reserve have linear bounds in the selected prime. -/
theorem exists_firstPrime_twelve_energy_balance :
    ∃ b : ℝ, 0<b ∧ ∃ T : ℕ, ∀ p : ℕ, T≤p → p.Prime →
      b*(p:ℝ)^(2 : ℕ)-136130*(p:ℝ) ≤ mobiusDivisorParityGoodEnergy (12*p) {p} ∧
      (p:ℝ)/2000000 ≤ mobiusDivisorParityDefectEnergy (12*p) {p} ∧
      mobiusDivisorParityDefectEnergy (12*p) {p} ≤ 122018*(p:ℝ) ∧
      0 ≤ mobiusDivisorSelectionEnergy (12*p) ∅-mobiusDivisorSelectionEnergy (12*p) {p} ∧
      mobiusDivisorSelectionEnergy (12*p) ∅-mobiusDivisorSelectionEnergy (12*p) {p} ≤ 14112*(p:ℝ) := by
  obtain ⟨b,hb,Tb,hB⟩ := twelve_diagonal_lower
  obtain ⟨Td,hTd,hD⟩ := twelve_head_defect
  refine ⟨b,hb,max Tb Td,?_⟩
  intro p hpT hp
  have hbase := hB p ((le_max_left _ _).trans hpT)
  have hdefect := hD p ((le_max_right _ _).trans hpT) hp
  have hupper := twelve_defect_upper hp
  have hrelease := twelve_release_upper hp
  have he := mobiusDivisorParityGoodEnergy_add_defect (12*p) {p}
  have hcontract := sum_mobiusDivisorPrimePair_sq_le hp (12*p)
  rw [← mobiusDivisorSelectionEnergy_singleton_eq_primePair (12*p) hp,
    ← mobiusDivisorSelectionEnergy_empty] at hcontract
  refine ⟨?_,hdefect,hupper,sub_nonneg.mpr hcontract,hrelease⟩
  nlinarith only [hbase,hupper,hrelease,he]

/-- The first-prime geometric-certificate excess at quotient twelve eventually
exceeds every prescribed linear multiple of the prime. -/
theorem exists_firstPrime_twelve_geometric_excess (L : ℝ) :
    ∃ T : ℕ, ∀ p : ℕ, T≤p → p.Prime →
      L*(p:ℝ) < mobiusDivisorSelectionEnergy (12*p) {p}+
        2*Real.sqrt (mobiusDivisorParityGoodEnergy (12*p) {p})*
          Real.sqrt (mobiusDivisorParityDefectEnergy (12*p) {p})-
            mobiusDivisorSelectionEnergy (12*p) ∅ := by
  obtain ⟨b,hb,Tb,hB⟩ := twelve_diagonal_lower
  obtain ⟨Td,hTd,hD⟩ := twelve_head_defect
  let K := |L|+14113
  have hK : 0<K := by dsimp [K]; positivity
  obtain ⟨N,hN⟩ := exists_nat_gt ((2000000*K^(2 : ℕ)+136130)/b)
  refine ⟨max Tb (max Td N),?_⟩
  intro p hpT hp
  have hpp : (0:ℝ)<p := by exact_mod_cast hp.pos
  have hpB : Tb≤p := (le_max_left _ _).trans hpT
  have hpD : Td≤p := (le_max_left _ _).trans ((le_max_right _ _).trans hpT)
  have hpN : N≤p := (le_max_right _ _).trans ((le_max_right _ _).trans hpT)
  have hsize : 2000000*K^(2 : ℕ)+136130 ≤ b*(p:ℝ) := by
    have hpNr : (N:ℝ)≤p := by exact_mod_cast hpN
    have hs : (2000000*K^(2 : ℕ)+136130)/b≤p := hN.le.trans hpNr
    have hm := (div_le_iff₀ hb).mp hs
    nlinarith only [hm]
  let G := mobiusDivisorParityGoodEnergy (12*p) {p}
  let D := mobiusDivisorParityDefectEnergy (12*p) {p}
  have hg0 : 0≤G := mobiusDivisorParityGoodEnergy_nonneg _ _
  have hd0 : 0≤D := mobiusDivisorParityDefectEnergy_nonneg _ _
  have hrelease := twelve_release_upper hp
  have hdUpper := twelve_defect_upper hp
  have hdLower := hD p hpD hp
  have hbase := hB p hpB
  have henergy := mobiusDivisorParityGoodEnergy_add_defect (12*p) {p}
  change G+D=_ at henergy
  change D≤_ at hdUpper
  change _≤D at hdLower
  have hgLower : 2000000*K^(2 : ℕ)*(p:ℝ)≤G := by
    have hs := mul_le_mul_of_nonneg_right hsize hpp.le
    nlinarith only [hs,hbase,hrelease,hdUpper,henergy]
  have hprod : K^(2 : ℕ)*(p:ℝ)^(2 : ℕ)≤G*D := by
    calc
      _ = (2000000*K^(2 : ℕ)*(p:ℝ))*((p:ℝ)/2000000) := by ring
      _ ≤ G*D := mul_le_mul hgLower hdLower (by positivity) hg0
  have hroots : K*(p:ℝ)≤Real.sqrt G*Real.sqrt D := by
    have hs : (Real.sqrt G*Real.sqrt D)^(2 : ℕ)=G*D := by
      rw [mul_pow,Real.sq_sqrt hg0,Real.sq_sqrt hd0]
    have hn : 0≤Real.sqrt G*Real.sqrt D := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    nlinarith [mul_pos hK hpp]
  have hLp := mul_le_mul_of_nonneg_right (le_abs_self L) hpp.le
  have hAp := mul_nonneg (abs_nonneg L) hpp.le
  dsimp [K] at hroots
  change L*(p:ℝ)< mobiusDivisorSelectionEnergy (12*p) {p}+2*Real.sqrt G*Real.sqrt D-_
  nlinarith only [hroots,hrelease,hLp,hAp,hpp]

/-- Arbitrarily large primes contract the actual initial energy but fail its
geometric parity certificate at twelve times the prime. -/
theorem exists_firstPrime_contracting_energy_failed_certificate (n : ℕ) :
    ∃ p : ℕ, n≤p ∧ p.Prime ∧
      mobiusDivisorSelectionEnergy (12*p) {p} ≤ mobiusDivisorSelectionEnergy (12*p) ∅ ∧
      mobiusDivisorSelectionEnergy (12*p) ∅ < mobiusDivisorSelectionEnergy (12*p) {p}+
        2*Real.sqrt (mobiusDivisorParityGoodEnergy (12*p) {p})*
          Real.sqrt (mobiusDivisorParityDefectEnergy (12*p) {p}) := by
  obtain ⟨T,hT⟩ := exists_firstPrime_twelve_geometric_excess 0
  obtain ⟨p,hp,hpprime⟩ := Nat.exists_infinite_primes (max n T)
  have hfail := hT p ((le_max_right _ _).trans hp) hpprime
  have hcontract := sum_mobiusDivisorPrimePair_sq_le hpprime (12*p)
  rw [← mobiusDivisorSelectionEnergy_singleton_eq_primePair (12*p) hpprime,
    ← mobiusDivisorSelectionEnergy_empty] at hcontract
  refine ⟨p,(le_max_left _ _).trans hp,hpprime,hcontract,?_⟩
  linarith only [hfail]
end RHTower
