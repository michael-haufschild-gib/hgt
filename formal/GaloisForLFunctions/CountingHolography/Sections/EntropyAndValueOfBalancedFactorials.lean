import GaloisForLFunctions.Core
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup

/-! # Stirling entropy at a fixed factorial value

The balanced factorial identities at four and six change the linear
Stirling term by two rationally independent logarithms. Their integer
multiples preserve the rational value and approximate any entropy.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

/-- The three linear readings of an integer presentation by factorials. -/
def factorialBalance := Finsupp.linearCombination ℤ (fun k : ℕ => (k : ℝ))
def factorialLogValue := Finsupp.linearCombination ℤ (fun k : ℕ => Real.log k.factorial)
def factorialEntropy := Finsupp.linearCombination ℤ (fun k : ℕ => (k:ℝ)*Real.log k)

private def moveFour : ℕ →₀ ℤ :=
  Finsupp.single 4 1 + Finsupp.single 1 3 - Finsupp.single 3 1 - Finsupp.single 2 2

private def moveSix : ℕ →₀ ℤ :=
  Finsupp.single 6 1 + Finsupp.single 1 2 - Finsupp.single 5 1 - Finsupp.single 3 1

private def U := 4*Real.log 2-3*Real.log 3
private def V := 6*Real.log 2+3*Real.log 3-5*Real.log 5

private theorem move_values :
    factorialBalance moveFour = 0 ∧ factorialBalance moveSix = 0 ∧
    factorialLogValue moveFour = 0 ∧ factorialLogValue moveSix = 0 ∧
    factorialEntropy moveFour = U ∧ factorialEntropy moveSix = V := by
  have step (k : ℕ) : Real.log (k+1).factorial =
      Real.log ((k+1:ℕ):ℝ)+Real.log k.factorial := by
    rw [Nat.factorial_succ,Nat.cast_mul,Real.log_mul (by positivity) (by positivity)]
  have h4 : Real.log 4=2*Real.log 2 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]; norm_num
  have h6 : Real.log 6=Real.log 2+Real.log 3 := by
    rw [show (6:ℝ)=2*3 by norm_num,Real.log_mul (by norm_num) (by norm_num)]
  have h4f := step 3
  have h6f := step 5
  norm_num only [Nat.reduceAdd,Nat.cast_ofNat] at h4f h6f
  refine ⟨?_,?_,?_,?_,?_,?_⟩ <;>
    norm_num [factorialBalance,factorialLogValue,factorialEntropy,moveFour,moveSix,zsmul_eq_mul,U,V]
  all_goals linarith only [h4f,h6f,h4,h6]

private theorem independent {i j : ℤ} (h : (i:ℝ)*U+(j:ℝ)*V=0) : i=0 ∧ j=0 := by
  let p : Nat.Primes := ⟨2,Nat.prime_two⟩
  let q : Nat.Primes := ⟨3,Nat.prime_three⟩
  let r : Nat.Primes := ⟨5,by norm_num⟩
  let a := Finsupp.single p (4*i+6*j) + Finsupp.single q (-3*i+3*j) + Finsupp.single r (-5*j)
  have hind := logPrime_linearIndependent_int
  rw [linearIndependent_iff] at hind
  have hz : a = 0 := hind a (by
    simp only [a,map_add,Finsupp.linearCombination_single,zsmul_eq_mul]
    change ((4*i+6*j:ℤ):ℝ)*Real.log 2 + ((-3*i+3*j:ℤ):ℝ)*Real.log 3 +
        ((-5*j:ℤ):ℝ)*Real.log 5 = 0
    dsimp only [U,V] at h
    push_cast
    linarith only [h])
  have hq := congrArg (fun v : Nat.Primes →₀ ℤ => v r) hz
  have hp := congrArg (fun v : Nat.Primes →₀ ℤ => v p) hz
  simp only [a,Finsupp.add_apply,Finsupp.single_apply,Finsupp.zero_apply,
    show p ≠ r by decide, show q ≠ r by decide,show q ≠ p by decide,show r ≠ p by decide,
    if_false,if_true,zero_add,add_zero] at hq hp
  omega

private theorem dense_entropy_moves :
    Dense ((AddSubgroup.closure {U,V} : AddSubgroup ℝ) : Set ℝ) := by
  rcases AddSubgroup.dense_or_cyclic (AddSubgroup.closure {U,V}) with hd | ⟨v,hv⟩
  · exact hd
  have hu : U ∈ AddSubgroup.closure {v} := by
    rw [← hv]; exact AddSubgroup.subset_closure (by simp)
  have hw : V ∈ AddSubgroup.closure {v} := by
    rw [← hv]; exact AddSubgroup.subset_closure (by simp)
  obtain ⟨i,hi⟩ := AddSubgroup.mem_closure_singleton.mp hu
  obtain ⟨j,hj⟩ := AddSubgroup.mem_closure_singleton.mp hw
  have he : (j:ℝ)*U+((-i:ℤ):ℝ)*V=0 := by
    rw [← hi,← hj,zsmul_eq_mul,zsmul_eq_mul,Int.cast_neg]
    ring
  obtain ⟨hj0,hi0⟩ := independent he
  have hi0' : i=0 := by omega
  rw [hi0',zero_zsmul] at hi
  have hh := independent (i := 1) (j := 0) (by rw [← hi]; norm_num)
  exact (one_ne_zero hh.1).elim

/-- At fixed degree and factorial value, changing only degrees at most six
can put the entropy within any positive tolerance of any prescribed value. -/
theorem factorial_entropy_dense_at_fixed_value (c : ℕ →₀ ℤ) (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ d : ℕ →₀ ℤ, (∀ k, 6 < k → d k = c k) ∧ factorialBalance d = factorialBalance c ∧
      factorialLogValue d = factorialLogValue c ∧ |factorialEntropy d-t| < ε := by
  obtain ⟨z,hnear,hz⟩ := (Metric.dense_iff.mp dense_entropy_moves) (t-factorialEntropy c) ε hε
  obtain ⟨i,j,hij⟩ := AddSubgroup.mem_closure_pair.mp hz
  let d := c+i • moveFour+j • moveSix
  obtain ⟨h4,h6,p4,p6,e4,e6⟩ := move_values
  refine ⟨d,?_,?_,?_,?_⟩
  · intro k hk
    have hzero : moveFour k=0 ∧ moveSix k=0 := by
      simp [moveFour,moveSix,show 1≠k by omega,show 2≠k by omega,
        show 3≠k by omega,show 4≠k by omega,show 5≠k by omega,show 6≠k by omega]
    simp [d,hzero.1,hzero.2]
  · simp [d,h4,h6]
  · simp [d,p4,p6]
  · simp only [d,map_add,map_smul,e4,e6,zsmul_eq_mul]
    rw [Metric.mem_ball,← hij,zsmul_eq_mul,zsmul_eq_mul,Real.dist_eq] at hnear
    rw [show factorialEntropy c+(i:ℝ)*U+(j:ℝ)*V-t =
      (i:ℝ)*U+(j:ℝ)*V-(t-factorialEntropy c) by ring]
    exact hnear

/-- Both absolute Stirling terms can simultaneously approach half the
absolute signed value. Their maximum is always at least that large. -/
theorem factorial_entropy_remainder_minimax (c : ℕ →₀ ℤ) :
    (∀ d : ℕ →₀ ℤ, factorialLogValue d = factorialLogValue c →
      |factorialLogValue c|/2 ≤ max |factorialEntropy d| |factorialLogValue c-factorialEntropy d|) ∧
    ∀ ε : ℝ, 0 < ε → ∃ d : ℕ →₀ ℤ, (∀ k, 6 < k → d k=c k) ∧
      factorialBalance d=factorialBalance c ∧ factorialLogValue d=factorialLogValue c ∧
      max |factorialEntropy d| |factorialLogValue c-factorialEntropy d| < |factorialLogValue c|/2+ε := by
  let p := factorialLogValue c
  constructor
  · intro d _
    have h := abs_add_le (p-factorialEntropy d) (factorialEntropy d)
    rw [sub_add_cancel] at h
    linarith only [h,le_max_left |factorialEntropy d| |p-factorialEntropy d|,
      le_max_right |factorialEntropy d| |p-factorialEntropy d|]
  · intro ε hε
    obtain ⟨d,hs,hb,hv,h⟩ := factorial_entropy_dense_at_fixed_value c (p/2) hε
    have h₀ : |p/2|=|p|/2 := by rw [abs_div,abs_two]
    have h₁ := abs_add_le (factorialEntropy d-p/2) (p/2)
    rw [sub_add_cancel,h₀] at h₁
    refine ⟨d,hs,hb,hv,max_lt ?_ ?_⟩
    · linarith only [h,h₁]
    · have h₂ := abs_sub (p/2) (factorialEntropy d-p/2)
      rw [show p/2-(factorialEntropy d-p/2)=p-factorialEntropy d by ring,h₀] at h₂
      linarith only [h,h₂]

#print axioms factorial_entropy_dense_at_fixed_value
#print axioms factorial_entropy_remainder_minimax

/-- Logarithmic values of balanced factorial products with entropy zero and
all degrees at most L. -/
def zeroEntropyPrices (L : ℕ) : AddSubgroup ℝ where
  carrier := {x | ∃ c : ℕ →₀ ℤ, (∀ k, L < k → c k=0) ∧ factorialBalance c=0 ∧
    factorialEntropy c=0 ∧ factorialLogValue c=x}
  zero_mem' := ⟨0,fun _ _ => rfl,map_zero _,map_zero _,map_zero _⟩
  add_mem' := by
    rintro x y ⟨c,hc,hb,he,hv⟩ ⟨d,hd,hb',he',hv'⟩
    exact ⟨c+d,fun k hk => by simp only [Finsupp.add_apply,hc k hk,hd k hk,add_zero],
      by rw [map_add,hb,hb',add_zero],by rw [map_add,he,he',add_zero],by rw [map_add,hv,hv']⟩
  neg_mem' := by
    rintro x ⟨c,hc,hb,he,hv⟩
    exact ⟨-c,fun k hk => by simp [hc k hk],by rw [map_neg,hb,neg_zero],
      by rw [map_neg,he,neg_zero],by rw [map_neg,hv]⟩

private def logFac (k : ℕ) := Real.log (k.factorial : ℝ)

private theorem logFac_step (k : ℕ) : logFac (k+1) = Real.log ((k+1:ℕ):ℝ)+logFac k := by
  unfold logFac
  rw [Nat.factorial_succ,Nat.cast_mul,Real.log_mul (by positivity) (by positivity)]

private def splitPrice (a b : ℕ) := logFac (a*b) - (b:ℝ)*logFac a - (a:ℝ)*logFac b

private theorem splitPrice_mem {L a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hh : a*b ≤ L) :
    splitPrice a b ∈ zeroEntropyPrices L := by
  let d := Finsupp.single (a*b) (1:ℤ) + Finsupp.single 1 ((a*b:ℕ):ℤ) -
    Finsupp.single a (b:ℤ) - Finsupp.single b (a:ℤ)
  have ha' : a ≤ L := (Nat.le_mul_of_pos_right a hb).trans hh
  have hb' : b ≤ L := (Nat.le_mul_of_pos_left b ha).trans hh
  refine ⟨d,fun k hk => ?_,?_,?_,?_⟩
  · simp [d,show a*b≠k by omega,show 1≠k by omega,
      show a≠k by omega,show b≠k by omega]
  · simp only [d,factorialBalance,map_sub,map_add,Finsupp.linearCombination_single,zsmul_eq_mul,
      Nat.cast_mul,Int.cast_mul,Int.cast_one,one_mul,Int.cast_natCast,Nat.cast_one,mul_one]
    ring
  · simp only [d,factorialEntropy,map_sub,map_add,Finsupp.linearCombination_single,zsmul_eq_mul,
      Nat.cast_mul,Int.cast_one,one_mul,Int.cast_natCast,Nat.cast_one,Real.log_one,mul_zero,add_zero,
      Real.log_mul (Nat.cast_pos.mpr ha).ne' (Nat.cast_pos.mpr hb).ne']
    ring
  · simp [d,factorialLogValue,splitPrice,logFac,zsmul_eq_mul]

private theorem log_two_mem {L : ℕ} (hL : 10 ≤ L) : Real.log 2 ∈ zeroEntropyPrices L := by
  let H := zeroEntropyPrices L
  have m4 : splitPrice 2 2 ∈ H := splitPrice_mem (by decide) (by decide) (by omega)
  have m6 : splitPrice 2 3 ∈ H := splitPrice_mem (by decide) (by decide) (by omega)
  have m9 : splitPrice 3 3 ∈ H := splitPrice_mem (by decide) (by decide) (by omega)
  have m10 : splitPrice 2 5 ∈ H := splitPrice_mem (by decide) (by decide) (by omega)
  have hm := H.sub_mem (H.sub_mem (H.add_mem m9 (H.nsmul_mem m4 4)) m10) m6
  rw [nsmul_eq_mul] at hm
  convert hm using 1
  have h4 : Real.log 4=2*Real.log 2 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]; norm_num
  have h6 : Real.log 6=Real.log 2+Real.log 3 := by
    rw [show (6:ℝ)=2*3 by norm_num,Real.log_mul (by norm_num) (by norm_num)]
  have h10 : Real.log 10=Real.log 2+Real.log 5 := by
    rw [show (10:ℝ)=2*5 by norm_num,Real.log_mul (by norm_num) (by norm_num)]
  have s10 := logFac_step 9
  have s6 := logFac_step 5
  have s5 := logFac_step 4
  have s4 := logFac_step 3
  have s3 := logFac_step 2
  norm_num only [Nat.reduceAdd,Nat.cast_ofNat] at s10 s6 s5 s4 s3
  have s2 : logFac 2=Real.log 2 := by norm_num [logFac]
  norm_num only [splitPrice,Nat.reduceMul,Nat.cast_ofNat]
  linarith only [s10,s6,s5,s4,s3,s2,h4,h6,h10]

private theorem factorial_log_mem_of_logs {H : AddSubgroup ℝ} {n : ℕ}
    (hl : ∀ j, 0 < j → j ≤ n → Real.log (j:ℝ) ∈ H) : logFac n ∈ H := by
  induction n with
  | zero => simp [logFac]
  | succ n ih =>
    rw [logFac_step]
    exact H.add_mem (hl _ (Nat.succ_pos _) le_rfl) (ih fun j hj hjn => hl j hj (Nat.le_succ_of_le hjn))

/-- Every positive integer n admits a balanced factorial presentation of entropy
zero, using only degrees through max(10,n+1). -/
theorem log_nat_mem_zeroEntropyPrices {L : ℕ} (hL : 10 ≤ L) (n : ℕ) (hn : n < L) :
    Real.log (n:ℝ) ∈ zeroEntropyPrices L := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    let H := zeroEntropyPrices L
    by_cases hsmall : n ≤ 2
    · interval_cases n
      · simp
      · simp
      · exact log_two_mem hL
    by_cases he : n%2=0
    · let k := n/2
      have hk : 0 < k := by dsimp only [k]; omega
      have hkn : k < n := by dsimp only [k]; omega
      have hnk : n=2*k := by dsimp only [k]; omega
      have hlog := H.add_mem (log_two_mem hL) (ih k hkn (hkn.trans hn))
      rwa [hnk,Nat.cast_mul,Nat.cast_ofNat,Real.log_mul (by norm_num) (Nat.cast_pos.mpr hk).ne']
    · let k := (n+1)/2
      have hk : 0 < k := by dsimp only [k]; omega
      have hkn : k < n := by dsimp only [k]; omega
      have hnk : 2*k=n+1 := by dsimp only [k]; omega
      have hq : splitPrice 2 k ∈ H := splitPrice_mem (by decide) hk (by omega)
      have hlog := H.add_mem (log_two_mem hL) (ih k hkn (hkn.trans hn))
      have hs : Real.log ((n+1:ℕ):ℝ) ∈ H := by
        rwa [← hnk,Nat.cast_mul,Nat.cast_ofNat,Real.log_mul (by norm_num) (Nat.cast_pos.mpr hk).ne']
      have hfac (a : ℕ) (ha : a < n) : logFac a ∈ H :=
        factorial_log_mem_of_logs fun j _ hja => ih j (hja.trans_lt ha) ((hja.trans_lt ha).trans hn)
      have hprice : logFac (2*k) ∈ H := by
        have hh := H.add_mem (H.add_mem hq (H.nsmul_mem (hfac 2 (by omega)) k)) (H.nsmul_mem (hfac k hkn) 2)
        simp only [nsmul_eq_mul,Nat.cast_ofNat,splitPrice] at hh
        convert hh using 1
        ring
      rw [hnk,logFac_step] at hprice
      have hfn := H.sub_mem hprice hs
      rw [add_sub_cancel_left] at hfn
      obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
      have hf := hfac m (by omega)
      rw [hm,logFac_step] at hfn
      simpa only [hm,add_sub_cancel_right] using H.sub_mem hfn hf

/-- The positive rational represented by the integer factorial exponents. -/
def factorialValue (c : ℕ →₀ ℤ) : ℚ :=
  ∏ k ∈ c.support, (k.factorial:ℚ)^(c k)

theorem factorialValue_pos (c : ℕ →₀ ℤ) : 0 < factorialValue c :=
  Finset.prod_pos fun k _ => zpow_pos (Nat.cast_pos.mpr (Nat.factorial_pos k)) _

theorem log_factorialValue (c : ℕ →₀ ℤ) : Real.log (factorialValue c:ℝ) = factorialLogValue c := by
  unfold factorialValue factorialLogValue
  push_cast
  rw [Real.log_prod fun k _ => (zpow_pos (Nat.cast_pos.mpr (Nat.factorial_pos k) : (0:ℝ)<_) _).ne',
    Finsupp.linearCombination_apply]
  simp only [Real.log_zpow,Finsupp.sum,zsmul_eq_mul]

/-- Every positive rational A/B occurs exactly as a balanced factorial
product of entropy zero. The largest allowed degree is max(10,max(A,B)+1). -/
theorem zeroEntropy_factorial_ratio {A B : ℕ} (hA : 0 < A) (hB : 0 < B) :
    ∃ c : ℕ →₀ ℤ, (∀ j, max 10 (max A B+1) < j → c j=0) ∧
      factorialBalance c=0 ∧ factorialEntropy c=0 ∧ factorialValue c=(A:ℚ)/B := by
  let L := max 10 (max A B+1)
  have hL : 10 ≤ L := le_max_left _ _
  have hAL : A < L := (Nat.lt_succ_of_le (le_max_left _ _)).trans_le (le_max_right _ _)
  have hBL : B < L := (Nat.lt_succ_of_le (le_max_right _ _)).trans_le (le_max_right _ _)
  have hm := (zeroEntropyPrices L).sub_mem (log_nat_mem_zeroEntropyPrices hL A hAL)
    (log_nat_mem_zeroEntropyPrices hL B hBL)
  obtain ⟨c,hc,hb,he,hv⟩ := hm
  refine ⟨c,hc,hb,he,?_⟩
  have hlog : Real.log (factorialValue c:ℝ)=Real.log ((A:ℝ)/B) := by
    rw [log_factorialValue,Real.log_div (Nat.cast_pos.mpr hA).ne' (Nat.cast_pos.mpr hB).ne']
    exact hv
  have hcpos : (0:ℝ) < factorialValue c := Rat.cast_pos.mpr (factorialValue_pos c)
  have hab : (0:ℝ) < (A:ℝ)/B := div_pos (Nat.cast_pos.mpr hA) (Nat.cast_pos.mpr hB)
  have hh : (factorialValue c:ℝ)=(A:ℝ)/B := Real.log_injOn_pos hcpos hab hlog
  apply Rat.cast_injective (α := ℝ)
  simpa only [Rat.cast_div,Rat.cast_natCast] using hh

#print axioms log_nat_mem_zeroEntropyPrices
#print axioms zeroEntropy_factorial_ratio

end GaloisForLFunctions.CountingHolography.Sections
