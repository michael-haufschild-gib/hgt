import GaloisForLFunctions.RHTower.MobiusDivisorFirstPrimeReserve
import GaloisForLFunctions.RHTower.MobiusDivisorElevenChannelBounds

/-!
# Quadratic sign-defect energy after the first prime

The analytic cutoff-seven channel gap persists on a clipped dilation interval.
A positive density of odd squarefree cofactors occupies that interval at every
sufficiently large cutoff. Their distinct prime-factor labels force a quadratic
lower bound on the literal reversed-parity energy after selecting prime two.
Initial parity contraction supplies the matching quadratic upper bound.

Thus this first-prime defect is not lower order than the original quadratic
energy budget. Comparing its geometric cost with the released reserve remains
a separate arithmetic estimate. No numerical data enters these proofs.
-/

noncomputable section
open Finset Filter Topology
open scoped ArithmeticFunction.Moebius
namespace RHTower

private lemma prime_two_seven_gap :
    (3/125:ℝ) ≤ divisorUnsignedDilationChannel 7 2-divisorUnsignedDilationChannel 7 1 := by
  obtain ⟨h1,h2,_⟩ := mobiusDivisorDilationChannel_seven_box
  rw [mobiusDivisorDilationChannel_eq_moebius_unsigned] at h1 h2
  norm_num [ArithmeticFunction.moebius_apply_prime (show Nat.Prime 2 by norm_num)] at h1 h2
  linarith

/-- The cutoff-seven reversal persists throughout a fixed relative dilation interval. -/
theorem divisorUnsignedDilationChannel_two_clipped_reversal
    {M d : ℕ} (hd : 0<d) (hbase : 7*d≤M) (hclip : 10000*(M-7*d)≤d) :
    Real.sqrt d/100 ≤ divisorUnsignedDilationChannel M (2*d)-divisorUnsignedDilationChannel M d := by
  let t := M-7*d
  have ht : t≤d := by dsimp [t]; omega
  have heM : d*7+t=M := by dsimp [t]; omega
  have h1 := divisorUnsignedDilationChannel_mul_add d 7 t 1 hd ht
  have h2 := divisorUnsignedDilationChannel_mul_add d 7 t 2 hd ht
  rw [heM] at h1 h2
  norm_num only [Nat.mul_one, Nat.reduceDiv] at h1 h2
  rw [Nat.mul_comm d 2] at h2
  let w : ℝ := Real.sqrt M-Real.sqrt (d*7:ℕ)
  have hw0 : 0≤w := sub_nonneg.mpr (Real.sqrt_le_sqrt (by exact_mod_cast (show d*7≤M by omega)))
  have hs0 : 0<Real.sqrt (d:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hs : (Real.sqrt (d:ℝ))^(2 : ℕ)=d := Real.sq_sqrt (Nat.cast_nonneg d)
  have hsM := Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) M)
  have hs7 := Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) (d*7))
  have hclock : w*(Real.sqrt M+Real.sqrt (d*7:ℕ))=(t:ℝ) := by
    have hm := congrArg (fun n : ℕ => (n:ℝ)) heM
    dsimp [w]
    push_cast at hm hs7 ⊢
    nlinarith only [hsM,hs7,hm]
  have hrootle : Real.sqrt (d:ℝ) ≤ Real.sqrt M+Real.sqrt (d*7:ℕ) := by
    have h := Real.sqrt_le_sqrt (show (d:ℝ)≤(d*7:ℕ) by exact_mod_cast (show d≤d*7 by omega))
    linarith [Real.sqrt_nonneg (M:ℝ)]
  have hw : w ≤ Real.sqrt (d:ℝ)/10000 := by
    have hp := mul_le_mul_of_nonneg_left hrootle hw0
    rw [hclock] at hp
    have htR : (10000:ℝ)*(t:ℝ)≤d := by exact_mod_cast hclip
    nlinarith only [hp,htR,hs,hs0]
  have hD3 := abs_primeFreeDivisorDefect_le (N:=3) (by norm_num)
  have hD7 := abs_primeFreeDivisorDefect_le (N:=7) (by norm_num)
  norm_num only [Nat.cast_ofNat] at hD3 hD7
  have hs3 : Real.sqrt (3:ℝ)≤2 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤3), Real.sqrt_nonneg (3:ℝ)]
  have hs7' : Real.sqrt (7:ℝ)≤3 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤7), Real.sqrt_nonneg (7:ℝ)]
  have hD : -(120:ℝ) ≤ primeFreeDivisorDefect 3-primeFreeDivisorDefect 7 := by
    have h3 := (abs_le.mp hD3).1
    have h7 := (abs_le.mp hD7).2
    linarith
  have hbirth := mul_le_mul_of_nonneg_left prime_two_seven_gap hs0.le
  have hrem := mul_le_mul_of_nonneg_left hD hw0
  change _ = _+w*_ at h1 h2
  nlinarith only [h1,h2,hbirth,hrem,hw,hs0]

private lemma odd_squarefree_narrow_window {N : ℕ} (hN : 20480000000000≤N) :
    let L := N/100000
    (L:ℝ)/8 ≤ ∑ d ∈ Ioc (N-L) N, if 2∣d then 0 else (((μ d : ℤ):ℝ))^(2 : ℕ) := by
  let L := N/100000
  let R := L/32+1
  have hL : 204800000≤L := by dsimp [L]; omega
  have hLN : L≤N := Nat.div_le_self _ _
  have hNR : N≤6400000*R := by dsimp [L,R] at *; omega
  have hR : 6400000≤R := by dsimp [R]; omega
  have hNsq : N≤R^(2 : ℕ) := by
    calc
      N ≤ 6400000*R := hNR
      _ ≤ R*R := Nat.mul_le_mul_right R hR
      _ = R^(2 : ℕ) := by ring
  have hcount := Sieve.abs_window_coprime_squarefree_sub_le
    (p:=2) (t:=N-L) (L:=L) (R:=R) (by norm_num) (by omega) (by omega)
  rw [Nat.sub_add_cancel hLN] at hcount
  have hRpos : (0:ℝ)<R := by exact_mod_cast (show 0<R by omega)
  have hRupper : (R:ℝ)≤(L:ℝ)/32+1 := by
    have hdiv : ((L/32:ℕ):ℝ)*32≤L := by exact_mod_cast Nat.div_mul_le_self L 32
    dsimp [R]
    push_cast
    linarith
  have hquot : (L:ℝ)/(R:ℝ)≤32 := by
    apply (div_le_iff₀ hRpos).mpr
    exact_mod_cast (show L≤32*R by dsimp [R]; omega)
  have herror : 2*(R:ℝ)+(L:ℝ)/(R:ℝ)≤(L:ℝ)/8 := by
    have hLreal : (1024:ℝ)≤L := by exact_mod_cast (show 1024≤L by omega)
    linarith
  have hdensity : (1/4:ℝ)≤(1-1/(2:ℝ))*Sieve.coprimeSquarefreeSum 2 := by
    have heq := Sieve.coprime_density_eq (by norm_num : Nat.Prime 2)
    norm_num only [Nat.cast_ofNat] at heq
    norm_num only [show (1:ℝ)-1/2=1/2 by norm_num]
    rw [heq, Sieve.squarefreeDensity_eq]
    have hpi : 0<Real.pi^(2 : ℕ) := sq_pos_of_pos Real.pi_pos
    have hpi16 : Real.pi^(2 : ℕ)≤16 := by nlinarith only [Real.pi_pos, Real.pi_lt_four]
    have h : (1/4:ℝ)≤4/Real.pi^(2 : ℕ) := (le_div_iff₀ hpi).mpr (by nlinarith only [hpi16])
    convert h using 1
    ring
  have hmass := mul_le_mul_of_nonneg_left hdensity (Nat.cast_nonneg (α:=ℝ) L)
  have hlower := (abs_le.mp hcount).1
  change (L:ℝ)/8≤_
  norm_num only [Nat.cast_ofNat] at hlower
  nlinarith only [hlower,hmass,herror]

private lemma prime_two_defect_at_squarefree_label {M d : ℕ}
    (hds : Squarefree d) (hodd : ¬2∣d) (hd : 0<d)
    (hbase : 7*d≤M) (hclip : 10000*(M-7*d)≤d) :
    (d:ℝ)/10000 ≤ (max (-mobiusDivisorOrientedFibre M {2} d.primeFactors) 0)^(2 : ℕ) := by
  have hnot : 2 ∉ d.primeFactors := fun h => hodd (Nat.mem_primeFactors.mp h).2.1
  have hpr : ∀ p ∈ d.primeFactors, Nat.Prime p := fun _ h => (Nat.mem_primeFactors.mp h).1
  have hfield : mobiusDivisorOrientedFibre M {2} d.primeFactors =
      divisorUnsignedDilationChannel M d-divisorUnsignedDilationChannel M (2*d) := by
    change mobiusDivisorOrientedFibre M (insert 2 ∅) d.primeFactors = _
    rw [mobiusDivisorOrientedFibre_insert M ∅ d.primeFactors 2 hnot,
      mobiusDivisorOrientedFibre_empty_eq_unsigned_product _ hpr M,
      mobiusDivisorOrientedFibre_empty_eq_unsigned_product (insert 2 d.primeFactors)
        (by simpa using And.intro (show Nat.Prime 2 by norm_num) hpr) M,
      prod_insert hnot, Nat.prod_primeFactors_of_squarefree hds]
  have hgap := divisorUnsignedDilationChannel_two_clipped_reversal hd hbase hclip
  have hle : Real.sqrt (d:ℝ)/100 ≤ max (-mobiusDivisorOrientedFibre M {2} d.primeFactors) 0 := by
    calc
      _ ≤ -mobiusDivisorOrientedFibre M {2} d.primeFactors := by rw [hfield]; linarith only [hgap]
      _ ≤ _ := le_max_left _ _
  have hsq := mul_self_le_mul_self (by positivity : 0≤Real.sqrt (d:ℝ)/100) hle
  have hsqrt := Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) d)
  nlinarith only [hsq,hsqrt]

private lemma prime_two_defect_window_lower {M : ℕ} (hM : 143360000000000≤M) :
    let N := M/7
    let L := N/100000
    (N:ℝ)*(L:ℝ)/160000 ≤ mobiusDivisorParityDefectEnergy M {2} := by
  classical
  let N := M/7
  let L := N/100000
  let W := (Ioc (N-L) N).filter (fun d => Squarefree d ∧ ¬2∣d)
  let f := fun R => (max (-mobiusDivisorOrientedFibre M {2} R) 0)^(2 : ℕ)
  have hN : 20480000000000≤N := by dsimp [N]; omega
  have hL : 204800000≤L := by dsimp [L]; omega
  have hwindow (d : ℕ) (hd : d ∈ W) :
      Squarefree d ∧ ¬2∣d ∧ 0<d ∧ 7*d≤M ∧ 10000*(M-7*d)≤d ∧ N≤2*d ∧ d<M := by
    obtain ⟨hdI,hs,ho⟩ := mem_filter.mp hd
    obtain ⟨hdlo,hdhi⟩ := mem_Ioc.mp hdI
    refine ⟨hs,ho,?_,?_,?_,?_,?_⟩ <;> dsimp [N,L] at * <;> omega
  have hterm (d : ℕ) : (if 2∣d then (0:ℝ) else (((μ d:ℤ):ℝ))^(2 : ℕ)) =
      if Squarefree d ∧ ¬2∣d then 1 else 0 := by
    by_cases hs : Squarefree d
    · have hm : (((μ d:ℤ):ℝ))^(2 : ℕ)=1 := by
        exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hs
      by_cases ho : 2∣d
      · rw [if_pos ho, if_neg (fun h => h.2 ho)]
      · simp only [if_neg ho, if_pos (And.intro hs ho), hm]
    · simp [hs,ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]
  have hmass : (L:ℝ)/8 ≤ (W.card:ℝ) := by
    have h := odd_squarefree_narrow_window hN
    change (L:ℝ)/8≤_ at h
    simp_rw [hterm] at h
    simpa only [← sum_filter, sum_const, nsmul_eq_mul, mul_one] using h
  have hinj : Set.InjOn Nat.primeFactors (W: Set ℕ) := by
    intro d hd e he hde
    have hds := (hwindow d hd).1
    have hes := (hwindow e he).1
    rw [← Nat.prod_primeFactors_of_squarefree hds,
      ← Nat.prod_primeFactors_of_squarefree hes, hde]
  have hsub : W.image Nat.primeFactors ⊆ (mobiusDivisorSelectionPrimes M).powerset := by
    intro R hR
    obtain ⟨d,hd,rfl⟩ := mem_image.mp hR
    apply mem_powerset.mpr
    intro p hp
    apply mem_filter.mpr
    exact ⟨mem_range.mpr ((Nat.le_of_mem_primeFactors hp).trans_lt (hwindow d hd).2.2.2.2.2.2),
      (Nat.mem_primeFactors.mp hp).1⟩
  have hsum : (∑ d ∈ W, f d.primeFactors) ≤ mobiusDivisorParityDefectEnergy M {2} := by
    calc
      _ = ∑ R ∈ W.image Nat.primeFactors, f R := (sum_image hinj).symm
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
  have hbound : (W.card:ℝ)*((N:ℝ)/20000) ≤ ∑ d ∈ W, f d.primeFactors := by
    calc
      _ = ∑ _ ∈ W, (N:ℝ)/20000 := by simp
      _ ≤ _ := by
        apply sum_le_sum
        intro d hd
        obtain ⟨hs,ho,hpos,hbase,hclip,hhalf,_⟩ := hwindow d hd
        have h := prime_two_defect_at_squarefree_label hs ho hpos hbase hclip
        have hh : (N:ℝ)≤2*(d:ℝ) := by exact_mod_cast hhalf
        dsimp [f]
        linarith only [h,hh]
  have hscaled := mul_le_mul_of_nonneg_right hmass (by positivity : (0:ℝ)≤(N:ℝ)/20000)
  change (N:ℝ)*(L:ℝ)/160000≤_
  nlinarith only [hscaled,hbound,hsum]

/-- The literal sign-defect energy after selecting prime two has quadratic order.
The lower bound uses an interval of odd squarefree cofactors on which the
cutoff-seven reversal persists; the upper bound is the complete original diagonal. -/
theorem mobiusDivisorParityDefectEnergy_two_quadratic_bounds
    (M : ℕ) (hM : 143360000000000≤M) :
    (M:ℝ)^(2 : ℕ)/2048000000000 ≤ mobiusDivisorParityDefectEnergy M {2} ∧
    mobiusDivisorParityDefectEnergy M {2} ≤ 722*(M:ℝ)^(2 : ℕ) := by
  constructor
  · let N := M/7
    let L := N/100000
    have hwindow := prime_two_defect_window_lower hM
    change (N:ℝ)*(L:ℝ)/160000≤_ at hwindow
    have hNL : (N:ℝ)≤200000*(L:ℝ) := by
      exact_mod_cast (show N≤200000*L by dsimp [N,L]; omega)
    have hMN : (M:ℝ)≤8*(N:ℝ) := by
      exact_mod_cast (show M≤8*N by dsimp [N]; omega)
    have hprod := mul_le_mul_of_nonneg_left hNL (Nat.cast_nonneg (α:=ℝ) N)
    have hsq := mul_self_le_mul_self (Nat.cast_nonneg (α:=ℝ) M) hMN
    nlinarith only [hwindow,hprod,hsq]
  · have hfirst := mobiusDivisorSelectionEnergy_insert_le_of_parity_nonneg M ∅
      (show Nat.Prime 2 by norm_num) (by omega) (by simp)
      (fun R => mobiusDivisorSelectionFibre_empty_parity_nonneg M R)
    simp only [insert_empty_eq,mobiusDivisorSelectionEnergy_empty] at hfirst
    have hsplit := mobiusDivisorParityGoodEnergy_add_defect M {2}
    have hgood := mobiusDivisorParityGoodEnergy_nonneg M {2}
    have hdiag := sum_mobiusDivisorDilationChannel_sq_le_quadratic M
    linarith only [hfirst,hsplit,hgood,hdiag]

end RHTower
