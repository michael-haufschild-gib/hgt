import GaloisForLFunctions.RHTower.MobiusDivisorPrescribedClockBlock
import GaloisForLFunctions.RHTower.MobiusDivisorInheritedPrimeInsertionProducer
import GaloisForLFunctions.RHTower.Sieve.MertensIntervalShell

/-!
# Actual omitted-prime debt under simultaneous clock and helper changes

An actual omitted-prime debt persists after one cutoff threshold, uniformly
in every sufficiently late helper set with small reciprocal-prime mass.
In particular one threshold works for all short logarithmic prime windows,
even when window position, helper cardinality and child depth change with
the original action cutoff.

The proof retains old squarefree cofactors outside an explicitly counted
exceptional set. Their source heads and logarithmic weights are unchanged.
Only small cofactors and multiples of actual helpers can be lost. This gives
a uniform finite-counting bound before taking any fixed-core source limit.

The exported theorems produce actual debt witnesses and cutoff thresholds;
no payment or source-sign premise is assumed. They exclude this restricted
repayment construction. They do not prove paid exhaustive continuation or RH.
-/

noncomputable section
open Finset Filter Topology
namespace RHTower

private def movingClockAffected (M B : ℕ) (S : Finset ℕ) : Finset ℕ :=
  Icc 1 (M/B) ∪ S.biUnion (fun p => (Ioc 0 M).filter (fun r => p ∣ r))

private lemma movingClockAffected_card (M B : ℕ) (S : Finset ℕ) :
    (movingClockAffected M B S).card ≤ M/B + ∑p∈S,M/p := by
  calc
    _ ≤ (Icc 1 (M/B)).card +
        ∑p∈S,((Ioc 0 M).filter (fun r => p ∣ r)).card :=
      (card_union_le _ _).trans (Nat.add_le_add_left card_biUnion_le _)
    _ = _ := by simp [Nat.Ioc_filter_dvd_card_eq_div]

private lemma movingClock_sample_preserved (M B : ℕ) (P S : Finset ℕ)
    (hB : 0 < B) (hS : ∀p∈S,B ≤ p) {r : ℕ}
    (hr : r∈fixedCoreSquarefreeIndices P M)
    (hgood : r∉movingClockAffected M B S) :
    r∈fixedCoreSquarefreeIndices (P∪S) M ∧
      mobiusDivisorInterpolatedFibre M r (P∪S) ∅ =
        mobiusDivisorInterpolatedFibre M r P ∅ := by
  obtain ⟨hr,hsf,hd⟩ := mem_filter.mp hr
  obtain ⟨hr0,hrM⟩ := mem_Icc.mp hr
  have hrB : M/B < r := by
    by_contra hn
    exact hgood (mem_union_left _ (mem_Icc.mpr ⟨hr0,le_of_not_gt hn⟩))
  have hnotdiv : ∀p∈S,¬p∣r := by
    intro p hp hpr
    exact hgood (mem_union_right _ (mem_biUnion.mpr
      ⟨p,hp,mem_filter.mpr ⟨mem_Ioc.mpr ⟨hr0,hrM⟩,hpr⟩⟩))
  have hlow : ∀p∈S,M/r+1 ≤ p := by
    intro p hp
    have hMB := (Nat.div_lt_iff_lt_mul hB).mp hrB
    have hMB' : M < B*r := by simpa only [Nat.mul_comm] using hMB
    have hMr := (Nat.div_lt_iff_lt_mul hr0).mpr hMB'
    have hpB := hS p hp
    omega
  constructor
  · apply mem_filter.mpr
    refine ⟨mem_Icc.mpr ⟨hr0,hrM⟩,hsf,disjoint_left.mpr ?_⟩
    intro p hpr hp
    rcases mem_union.mp hp with hp|hp
    · exact disjoint_left.mp hd hpr hp
    · exact hnotdiv p hp (Nat.mem_primeFactors.mp hpr).2.1
  · rw [mobiusDivisorInterpolatedFibre,
      mobiusDivisorSelectionFibre_union_inactive (M/r) P S ∅
        (fun p hp => by have := hlow p hp; omega),
      mobiusDivisorSelectionFibre_union_inactive (M/r+1) P S ∅ hlow]
    rfl

private lemma source_term_bound (P : Finset ℕ) (hP : ∀p∈P,p.Prime)
    (M : ℕ) {r : ℕ} (hr : r∈fixedCoreSquarefreeIndices P M) :
    (r:ℝ)*(mobiusDivisorInterpolatedFibre M r P ∅)^(2 : ℕ) ≤
      ((3/5:ℝ)*2^(P.card-1))^(2 : ℕ)*(M:ℝ) := by
  obtain ⟨_,hsf,hd⟩ := mem_filter.mp hr
  have he := mobiusDivisorSelectionFibre_product_interpolation M P r.primeFactors
    (fun p hp => (Nat.mem_primeFactors.mp hp).1) hd
  rw [Nat.prod_primeFactors_of_squarefree hsf] at he
  have hm : (((ArithmeticFunction.moebius r : ℤ):ℝ))^(2 : ℕ)=1 := by
    exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsf
  have hs := congrArg (fun x : ℝ => x^(2 : ℕ)) he
  simp only [mul_pow,Real.sq_sqrt (Nat.cast_nonneg r),hm,mul_one] at hs
  rw [← hs]
  have hb := abs_mobiusDivisorSelectionFibre_le_source_amplitude M P r.primeFactors hP
    (fun p hp => (Nat.mem_primeFactors.mp hp).1)
  have hsq := Real.sq_sqrt (Nat.cast_nonneg M)
  have hab := abs_nonneg (mobiusDivisorSelectionFibre M P r.primeFactors)
  have ha := sq_abs (mobiusDivisorSelectionFibre M P r.primeFactors)
  nlinarith [sq_nonneg (((3/5:ℝ)*2^(P.card-1))*Real.sqrt M-
    |mobiusDivisorSelectionFibre M P r.primeFactors|)]

/-- A moving helper set preserves all but the actual small or divisible
cofactors. The original weighted source is retained at every cutoff. -/
private lemma movingClock_helper_loss
    (P : Finset ℕ) (hP : ∀p∈P,p.Prime) (M B : ℕ) (hM : 1 ≤ M)
    (hB : 0 < B) (S : Finset ℕ) (hS : ∀p∈S,B ≤ p) :
    mobiusDivisorFiniteClockEnergy 1 M P-
      mobiusDivisorFiniteClockEnergy 1 M (P∪S) ≤
        ((3/5:ℝ)*2^(P.card-1))^(2 : ℕ) * (M:ℝ)^(2 : ℕ) * (1+Real.log M) *
          (1/(B:ℝ)+∑p∈S,1/(p:ℝ)) := by
  let F := fixedCoreSquarefreeIndices P M
  let A := movingClockAffected M B S
  let f := fun r : ℕ => (1+Real.log r)*(r:ℝ)*(mobiusDivisorInterpolatedFibre M r P ∅)^(2 : ℕ)
  let C : ℝ := ((3/5:ℝ)*2^(P.card-1))^(2 : ℕ)
  let H : ℝ := C*M*(1+Real.log M)
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg (by exact_mod_cast hM)
  have hH : 0 ≤ H := by dsimp [H,C]; positivity
  have hsplit : mobiusDivisorFiniteClockEnergy 1 M P =
      (∑r∈F.filter (fun r => r∉A),f r)+(∑r∈F.filter (fun r => r∈A),f r) := by
    exact (sum_filter_not_add_sum_filter F (fun r => r∈A) f).symm
  have hkept : (∑r∈F.filter (fun r => r∉A),f r) ≤
      mobiusDivisorFiniteClockEnergy 1 M (P∪S) := by
    have hsub : F.filter (fun r => r∉A) ⊆ fixedCoreSquarefreeIndices (P∪S) M :=
      fun r hr => (movingClock_sample_preserved M B P S hB hS
        (mem_filter.mp hr).1 (mem_filter.mp hr).2).1
    calc
      _ = ∑r∈F.filter (fun r => r∉A),
          (1+Real.log r)*(r:ℝ)*(mobiusDivisorInterpolatedFibre M r (P∪S) ∅)^(2 : ℕ) := by
        apply sum_congr rfl
        intro r hr
        rw [(movingClock_sample_preserved M B P S hB hS
          (mem_filter.mp hr).1 (mem_filter.mp hr).2).2]
      _ ≤ _ := by
        apply sum_le_sum_of_subset_of_nonneg hsub
        intro r hr _
        have hr1 : (1:ℝ) ≤ r := by exact_mod_cast (mem_Icc.mp (mem_filter.mp hr).1).1
        have := Real.log_nonneg hr1
        positivity
  have hdiscard : (∑r∈F.filter (fun r => r∈A),f r) ≤
      H*((M:ℝ)*(1/(B:ℝ)+∑p∈S,1/(p:ℝ))) := by
    have hpoint : ∀r∈F,f r ≤ H := by
      intro r hr
      have hrN := mem_Icc.mp (mem_filter.mp hr).1
      have hrpos : (0:ℝ) < r := by exact_mod_cast hrN.1
      have hlog := Real.log_le_log hrpos (show (r:ℝ) ≤ M by exact_mod_cast hrN.2)
      have hs := source_term_bound P hP M hr
      have hh := mul_le_mul (show 1+Real.log r ≤ 1+Real.log M by linarith) hs
        (by positivity) (by linarith : 0 ≤ 1+Real.log M)
      simpa only [f,H,C,mul_assoc,mul_left_comm,mul_comm] using hh
    have hcard : (F.filter (fun r => r∈A)).card ≤ M/B+∑p∈S,M/p :=
      (card_le_card (fun r hr => (mem_filter.mp hr).2)).trans
        (movingClockAffected_card M B S)
    have hcast : ((M/B+∑p∈S,M/p : ℕ):ℝ) ≤
        (M:ℝ)*(1/(B:ℝ)+∑p∈S,1/(p:ℝ)) := by
      push_cast
      calc
        _ ≤ (M:ℝ)/(B:ℝ)+∑p∈S,(M:ℝ)/(p:ℝ) :=
          add_le_add Nat.cast_div_le (sum_le_sum (fun p _ => Nat.cast_div_le))
        _ = _ := by simp only [mul_add,mul_sum,div_eq_mul_inv,one_mul]
    calc
      _ ≤ ∑_r∈F.filter (fun r => r∈A),H :=
        sum_le_sum (fun r hr => hpoint r (mem_filter.mp hr).1)
      _ = H*((F.filter (fun r => r∈A)).card:ℝ) := by simp [mul_comm]
      _ ≤ H*((M/B+∑p∈S,M/p : ℕ):ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) hH
      _ ≤ _ := mul_le_mul_of_nonneg_left hcast hH
  have he : H*((M:ℝ)*(1/(B:ℝ)+∑p∈S,1/(p:ℝ))) =
      C*(M:ℝ)^(2 : ℕ)*(1+Real.log M)*(1/(B:ℝ)+∑p∈S,1/(p:ℝ)) := by
    dsimp [H]
    ring
  rw [he] at hdiscard
  dsimp only [C] at hdiscard
  linarith only [hsplit,hkept,hdiscard]

/-- Actual omitted-prime debt persists uniformly over changing helper sets
of small reciprocal mass. The cutoff onset precedes the helper set: no
fixed-window limit or assumed payment estimate is used. -/
theorem exists_mobiusDivisorUniformMovingHelperDebt :
    ∀P : Finset ℕ,P.Nonempty → (∀p∈P,p.Prime) → Even P.card → ∀N : ℕ,
      ∃r : ℕ,∃δ η : ℝ,∃B M₀ : ℕ,
        r.Prime ∧ N < r ∧ r∉P ∧ 0 < δ ∧ 0 < η ∧ 0 < B ∧
        (∑'n,mobiusDivisorFixedCoreBlockMass P n)+2*δ=
          ∑'n,mobiusDivisorFixedCoreBlockMass (insert r P) n ∧
        ∀M : ℕ,M₀ ≤ M → ∀S : Finset ℕ,
          (∀p∈S,p.Prime ∧ B ≤ p) → (∑p∈S,1/(p:ℝ)) ≤ η →
          δ*(M:ℝ)^(2 : ℕ)*(1+Real.log M) ≤
            mobiusDivisorFiniteClockEnergy 1 M (insert r (P∪S))-
              mobiusDivisorFiniteClockEnergy 1 M P := by
  classical
  intro P hP hprime heven N
  obtain ⟨r,δ,η₀,W,K,τ₀,hr,hNr,hrP,hδ,_hη₀,_hW,_hK,hgap,_hcost,_hprep⟩ :=
    exists_mobiusDivisorClockDelayedInsertionProducer P hP hprime heven N
  let R := insert r P
  have hR : ∀p∈R,p.Prime := by
    intro p hp
    rcases mem_insert.mp hp with rfl|hp
    · exact hr
    · exact hprime p hp
  let C : ℝ := ((3/5:ℝ)*2^(R.card-1))^(2 : ℕ)
  have hC : 0 < C := by dsimp [C]; positivity
  let η := δ/(4*C)
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨B,hBbig⟩ := exists_nat_gt (4*C/δ)
  have hBR : (0:ℝ) < B := (by positivity : (0:ℝ) < 4*C/δ).trans hBbig
  have hB : 0 < B := by exact_mod_cast hBR
  have hBcost : C/(B:ℝ) ≤ δ/4 := by
    apply (div_le_iff₀ hBR).mpr
    have hh := (div_lt_iff₀ hδ).mp hBbig
    nlinarith only [hh]
  have hηcost : C*η=δ/4 := by
    dsimp [η]
    field_simp
  have hlim := (tendsto_mobiusDivisorFiniteClockEnergy_div_sq_log R hR).sub
    (tendsto_mobiusDivisorFiniteClockEnergy_div_sq_log P hprime)
  have hstrict : 3*δ/2 < (∑'n,mobiusDivisorFixedCoreBlockMass R n)-
      (∑'n,mobiusDivisorFixedCoreBlockMass P n) := by
    change (∑'n,mobiusDivisorFixedCoreBlockMass P n)+2*δ=
      ∑'n,mobiusDivisorFixedCoreBlockMass R n at hgap
    linarith only [hgap,hδ]
  have hevent : ∀ᶠ M : ℕ in atTop,1 ≤ M ∧
      (3*δ/2)*((M:ℝ)^(2 : ℕ)*(1+Real.log M)) ≤
        mobiusDivisorFiniteClockEnergy 1 M R-mobiusDivisorFiniteClockEnergy 1 M P := by
    filter_upwards [hlim.eventually (eventually_gt_nhds hstrict),
      eventually_ge_atTop (1:ℕ)] with M hM hM1
    refine ⟨hM1,?_⟩
    have hMR : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
    have hlog : 0 ≤ Real.log (M:ℝ) := Real.log_nonneg (by exact_mod_cast hM1)
    have hden : 0 < (M:ℝ)^(2 : ℕ)*(1+Real.log M) := by positivity
    simp only [← sub_div] at hM
    exact (le_div_iff₀ hden).mp hM.le
  obtain ⟨M₀,hM₀⟩ := eventually_atTop.mp hevent
  refine ⟨r,δ,η,B,M₀,hr,hNr,hrP,hδ,hη,hB,hgap,?_⟩
  intro M hM S hS hmass
  obtain ⟨hM1,hbase⟩ := hM₀ M hM
  have hlog : 0 ≤ Real.log (M:ℝ) := Real.log_nonneg (by exact_mod_cast hM1)
  have hden : 0 ≤ (M:ℝ)^(2 : ℕ)*(1+Real.log M) := by positivity
  have hcost : C*(1/(B:ℝ)+∑p∈S,1/(p:ℝ)) ≤ δ/2 := by
    have hm := mul_le_mul_of_nonneg_left hmass hC.le
    rw [hηcost] at hm
    have he : C*(1/(B:ℝ)+∑p∈S,1/(p:ℝ)) =
        C/(B:ℝ)+C*(∑p∈S,1/(p:ℝ)) := by ring
    rw [he]
    linarith only [hBcost,hm]
  have hpay := movingClock_helper_loss
    R hR M B hM1 hB S (fun p hp => (hS p hp).2)
  have hpay' : mobiusDivisorFiniteClockEnergy 1 M R-
      mobiusDivisorFiniteClockEnergy 1 M (R∪S) ≤
        (δ/2)*((M:ℝ)^(2 : ℕ)*(1+Real.log M)) := by
    calc
      _ ≤ C*(M:ℝ)^(2 : ℕ)*(1+Real.log M)*(1/(B:ℝ)+∑p∈S,1/(p:ℝ)) := hpay
      _ = (C*(1/(B:ℝ)+∑p∈S,1/(p:ℝ)))*((M:ℝ)^(2 : ℕ)*(1+Real.log M)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcost hden
  have he : R∪S=insert r (P∪S) := by exact insert_union r P S
  rw [he] at hpay'
  nlinarith only [hbase,hpay']

private lemma moving_window_reciprocal_mass (S : Finset ℕ) {τ κ : ℝ}
    (hτ : 0 < τ) (hκ : 0 ≤ κ)
    (hS : ∀p∈S,p.Prime ∧ τ < Real.log p ∧ Real.log p ≤ (1+κ)*τ) :
    τ*(∑p∈S,1/(p:ℝ)) ≤ 
      κ*τ+Real.log 2+Sieve.mertensIntervalConst := by
  classical
  by_cases hne : S.Nonempty
  · let m := S.min' hne
    let a := m-1
    let b := S.max' hne
    have hm : m∈S := S.min'_mem hne
    have hb : b∈S := S.max'_mem hne
    have hm2 : 2 ≤ m := (hS m hm).1.two_le
    have ha1 : 1 ≤ a := by dsimp [a]; omega
    have hab : a ≤ b := (Nat.sub_le m 1).trans (S.min'_le_max' hne)
    have ha0 : (0:ℝ) < a := by exact_mod_cast ha1
    have hm0 : (0:ℝ) < m := by exact_mod_cast (hS m hm).1.pos
    have hme : (a:ℝ)=(m:ℝ)-1 := by
      dsimp [a]
      rw [Nat.cast_sub (by omega : 1 ≤ m)]
      norm_num
    have hmle : (m:ℝ) ≤ 2*(a:ℝ) := by
      have hm2R : (2:ℝ) ≤ m := by exact_mod_cast hm2
      linarith only [hme,hm2R]
    have hlogm := Real.log_le_log hm0 hmle
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) ha0.ne'] at hlogm
    have hloga : τ-Real.log 2 ≤ Real.log (a:ℝ) := by
      have h := (hS m hm).2.1
      linarith only [h,hlogm]
    have hlogb := (hS b hb).2.2
    have hsub : S⊆Nat.primesLE b \ Nat.primesLE a := by
      intro p hp
      apply Finset.mem_sdiff.mpr
      refine ⟨Nat.mem_primesLE.mpr ⟨S.le_max' p hp,(hS p hp).1⟩,?_⟩
      intro hpa
      have hle := (Nat.mem_primesLE.mp hpa).1
      have hmin : m ≤ p := S.min'_le p hp
      dsimp [a] at hle
      omega
    have hM := Sieve.sum_log_div_prime_interval_le ha1 hab hsub
    have hterm (p : ℕ) (hp : p∈S) : τ*(1/(p:ℝ)) ≤ Real.log p/(p:ℝ) := by
      have hp0 : (0:ℝ) < p := by exact_mod_cast (hS p hp).1.pos
      calc
        _ = τ/(p:ℝ) := by ring
        _ ≤ _ := div_le_div_of_nonneg_right (hS p hp).2.1.le hp0.le
    have hs := sum_le_sum hterm
    rw [← mul_sum] at hs
    linarith only [hs,hM,hloga,hlogb]
  · have he : S=∅ := not_nonempty_iff_eq_empty.mp hne
    rw [he]
    simp only [sum_empty,mul_zero]
    exact add_nonneg (add_nonneg (mul_nonneg hκ hτ.le)
      (Real.log_nonneg (by norm_num))) Sieve.mertensIntervalConst_nonneg

/-- One actual debt and one cutoff threshold work for ALL sufficiently
late short logarithmic helper windows, even when their position, cardinality
and child depth change with the cutoff. -/
theorem exists_mobiusDivisorMovingClockSpanDebt :
    ∀P : Finset ℕ,P.Nonempty → (∀p∈P,p.Prime) → Even P.card → ∀N : ℕ,
      ∃r : ℕ,∃δ κ T : ℝ,∃M₀ : ℕ,
        r.Prime ∧ N < r ∧ r∉P ∧ 0 < δ ∧ 0 < κ ∧ 0 < T ∧
        (∑'n,mobiusDivisorFixedCoreBlockMass P n)+2*δ=
          ∑'n,mobiusDivisorFixedCoreBlockMass (insert r P) n ∧
        ∀M : ℕ,M₀ ≤ M → ∀τ : ℝ,T ≤ τ → ∀S : Finset ℕ,
          (∀p∈S,p.Prime ∧ τ < Real.log p ∧ Real.log p ≤ (1+κ)*τ) →
          δ*(M:ℝ)^(2 : ℕ)*(1+Real.log M) ≤
            mobiusDivisorFiniteClockEnergy 1 M (insert r (P∪S))-
              mobiusDivisorFiniteClockEnergy 1 M P := by
  classical
  intro P hP hprime heven N
  obtain ⟨r,δ,η,B,M₀,hr,hNr,hrP,hδ,hη,hB,hgap,hdebt⟩ :=
    exists_mobiusDivisorUniformMovingHelperDebt P hP hprime heven N
  let κ := η/4
  let C := Real.log 2+Sieve.mertensIntervalConst
  let T := max (Real.log B) (max 1 (4*(C+1)/η))
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one
    ((le_max_left 1 _).trans (le_max_right (Real.log B) _))
  refine ⟨r,δ,κ,T,M₀,hr,hNr,hrP,hδ,hκ,hT,hgap,?_⟩
  intro M hM τ hTτ S hS
  have hτ : 0 < τ := hT.trans_le hTτ
  have hBT : Real.log B ≤ τ := (le_max_left _ _).trans hTτ
  have hsize : 4*(C+1) ≤ η*τ := by
    have h : 4*(C+1)/η ≤ τ :=
      (le_max_right 1 _).trans ((le_max_right (Real.log B) _).trans hTτ)
    have hm := (div_le_iff₀ hη).mp h
    simpa only [mul_comm] using hm
  have hmass := moving_window_reciprocal_mass S hτ hκ.le hS
  have hupper : (∑p∈S,1/(p:ℝ)) ≤ η := by
    by_contra hn
    have hh := mul_lt_mul_of_pos_left (lt_of_not_ge hn) hτ
    rw [add_assoc] at hmass
    change τ*(∑p∈S,1/(p:ℝ)) ≤ κ*τ+C at hmass
    dsimp [κ] at hmass
    nlinarith only [hmass,hh,hsize,hη,hτ]
  apply hdebt M hM S _ hupper
  intro p hp
  refine ⟨(hS p hp).1,?_⟩
  by_contra hn
  have hpB : (p:ℝ) ≤ B := by exact_mod_cast (le_of_lt (lt_of_not_ge hn))
  have hlog := Real.log_le_log (by exact_mod_cast (hS p hp).1.pos) hpB
  exact (not_lt_of_ge (hlog.trans hBT)) (hS p hp).2.1

end RHTower