import GaloisForLFunctions.RestrictedFactorizationCalculus.ThePrimeErrorInTheCenteredUnitWindow
import GaloisForLFunctions.RestrictedFactorizationCalculus.PerfectCompletionAtEverySharpCutoff
import GaloisForLFunctions.RHTower.CreaseBudgetPrimeMass
import GaloisForLFunctions.WorldsOfTheZeroConfiguration.PrimesRoundAnOscillatingDensity

/-!
# The compensating sign below a growing quotient cut

For quotients from one through the first permitted prime wall, the
rough Möbius prefix consists of the unit. Their arithmetic contribution
is a positive prime interval for the ordinary reading. The remaining
quotients carry the opposite main term up to the signed head price.
-/

noncomputable section
open Finset Filter ArithmeticFunction RHTower.CoprimeMobius
open scoped Classical Topology
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.QuantitativeFactorizationMatching
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

/-- All large quotient indices sharing a unit rough prefix contribute
their ordinary arithmetic weight. Their signed compensation is entirely
supported on the lower indices, at the same sharp endpoint. -/
theorem quotient_cells_with_unit_rough_prefix (a : ArithmeticFunction ℝ) (y T J : ℕ) (range : J ≤ y) :
    (∑ q ∈ Icc 1 (T/(J+1)),a q*coprimeMoebiusSum (primorial y) (T/q))+
      (∑ q ∈ Ioc (T/(J+1)) T,a q)=quotientReading (roughFloorCoefficient y a) T := by
  let k := T/(J+1)
  let f := fun q : ℕ => a q*coprimeMoebiusSum (primorial y) (T/q)
  have eq : (∑ q ∈ Ioc k T,a q)=∑ q ∈ Ioc k T,f q := by
    apply sum_congr rfl
    intro q hq
    have hi := mem_Ioc.mp hq
    have pos : 0<q := (Nat.zero_le k).trans_lt hi.1
    have floor : T/q<J+1 := (Nat.div_lt_iff_lt_mul pos).mpr (by
      simpa only [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul (Nat.succ_pos J)).mp hi.1)
    have unit : 1 ≤ T/q := (Nat.le_div_iff_mul_le pos).mpr (by simpa only [Nat.one_mul] using hi.2)
    simp only [f,rough_prefix_through_the_unit unit ((Nat.le_of_lt_succ floor).trans range),mul_one]
  have part : Icc 1 T \ Icc 1 k=Ioc k T := by
    ext n; simp only [Finset.mem_sdiff,mem_Icc,mem_Ioc]; omega
  rw [coefficient_head_as_quotient_sum,eq,←part,sum_sdiff_eq_sub (Icc_subset_Icc_right (Nat.div_le_self T (J+1)))]
  change (∑ q ∈ Icc 1 k,f q)+((∑ q ∈ Icc 1 T,f q)-(∑ q ∈ Icc 1 k,f q))=_
  ring

private theorem prime_interval {y k T : ℕ} (h : k ≤ T) :
    (∑ q ∈ Ioc k T,roughOrdinaryPrimeWeight y q)=
      Chebyshev.theta T-Chebyshev.theta (min T (max y k)) := by
  rw [GaloisForLFunctions.WorldsOfTheZeroConfiguration.PrimeEdits.theta_sub_theta (min_le_left ..)]
  have sets : Ioc (min T (max y k)) T=(Ioc k T).filter (y<·) := by
    ext n; simp only [mem_filter,mem_Ioc]; omega
  rw [sets,sum_filter]
  apply sum_congr rfl
  intro q _
  change (if q.Prime ∧ y<q then Real.log q else 0)=_
  by_cases p : q.Prime <;> by_cases lo : y<q <;> simp [p,lo]

/-- For ordinary primes the compensating quantity is the actual prime
interval above the quotient cut, keeping both of its arithmetic walls. -/
theorem compensating_prime_interval (y T J : ℕ) (hj : J ≤ y) :
    (∑ q ∈ Icc 1 (T/(J+1)),roughOrdinaryPrimeWeight y q*coprimeMoebiusSum (primorial y) (T/q))+
      (Chebyshev.theta T-Chebyshev.theta (min T (max y (T/(J+1)))))=
      quotientReading (roughFloorCoefficient y (roughOrdinaryPrimeWeight y)) T := by
  rw [←prime_interval (Nat.div_le_self T (J+1))]
  exact quotient_cells_with_unit_rough_prefix _ y T J hj

private abbrev primeWindow (K X : ℕ) := (Nat.primesLE X).filter (K<·)

/-- A perfect matching has only the positive unit fixed. At a quotient
below the prime wall every integer is smooth, so the fixed lift counts
the entire quotient. -/
private theorem lift_of_the_unit_before_the_prime_wall {G : ℕ → ℕ}
    (unit : ∀ n,fixedSignedPrefix G n=if n=0 then 0 else 1) {y t : ℕ} (small : t ≤ y) :
    smoothLiftedPrefix (fixedSignedPrefix G) y t=t := by
  have seteq : RHTower.Sieve.smoothUpTo (Nat.primesLE y) t=Icc 1 t := by
    apply filter_eq_self.mpr
    intro d hd p hp
    exact Nat.mem_primesLE.mpr ⟨(Nat.le_of_dvd (mem_Icc.mp hd).1
      (Nat.dvd_of_mem_primeFactors hp)).trans ((mem_Icc.mp hd).2.trans small),Nat.prime_of_mem_primeFactors hp⟩
  rw [smoothLiftedPrefix,seteq]
  calc _ = ∑ _d ∈ Icc 1 t,(1:ℝ) := by
             apply sum_congr rfl
             intro d hd
             have h := mem_Icc.mp hd
             exact (unit (t/d)).trans (if_neg (Nat.ne_of_gt (show 0<t/d from
               (Nat.le_div_iff_mul_le h.1).mpr (by simpa using h.2))))
       _ = _ := by simp

private theorem sharp_floor_in_a_prime_window {K X : ℕ} (kp : 1 ≤ K) (size : K ≤ X) :
    |(∑ p ∈ primeWindow K X,Real.log p*((X/p:ℕ):ℝ))-(X:ℝ)*(Real.log X-Real.log K)| ≤
      X*(9+2*Real.log 4) := by
  let S := primeWindow K X
  let A := fun N : ℕ => ∑ p ∈ Nat.primesLE N,Real.log p/p
  have span : (∑ p ∈ S,Real.log p/p)=A X-A K := by
    have sub : Nat.primesLE K ⊆ Nat.primesLE X := fun p hp =>
      Nat.mem_primesLE.mpr ⟨(Nat.mem_primesLE.mp hp).1.trans size,(Nat.mem_primesLE.mp hp).2⟩
    have eq : S=Nat.primesLE X \ Nat.primesLE K := by
      ext p
      simp only [S,primeWindow,mem_filter,mem_sdiff,Nat.mem_primesLE,lt_iff_not_ge]
      tauto
    rw [eq,sum_sdiff_eq_sub sub]
  have pos := kp.trans size
  have hi : A X ≤ Real.log X+Real.log 4 := RHTower.mertens_first_upper pos
  have lo : Real.log X-9 ≤ A X := RHTower.mertens_first_lower pos
  have hk : A K ≤ Real.log K+Real.log 4 := RHTower.mertens_first_upper kp
  have lk : Real.log K-9 ≤ A K := RHTower.mertens_first_lower kp
  have up (p : ℕ) (hp : p ∈ S) :
      Real.log p*((X/p:ℕ):ℝ) ≤ (X:ℝ)*(Real.log p/p) := by
    have pp := (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2.pos
    have floor : ((X/p:ℕ):ℝ) ≤ (X:ℝ)/p := (le_div_iff₀ (Nat.cast_pos.mpr pp)).mpr
      (by exact_mod_cast Nat.div_mul_le_self X p)
    exact (mul_le_mul_of_nonneg_left floor (Real.log_natCast_nonneg _)).trans_eq (by ring)
  have down (p : ℕ) (hp : p ∈ S) :
      (X:ℝ)*(Real.log p/p)-Real.log p ≤ Real.log p*((X/p:ℕ):ℝ) := by
    have floor := (RHTower.cast_div_lt (n := X) (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2.pos).le
    have cost := mul_le_mul_of_nonneg_left floor (Real.log_natCast_nonneg p)
    exact (by ring : (X:ℝ)*(Real.log p/p)-Real.log p=Real.log p*((X:ℝ)/p-1)).le.trans cost
  have ceil := sum_le_sum up
  have base := sum_le_sum down
  rw [←mul_sum,span] at ceil
  rw [sum_sub_distrib,←mul_sum,span] at base
  have th := (sum_le_sum_of_subset_of_nonneg (filter_subset (K<·) (Nat.primesLE X))
    (fun p _ _ => Real.log_natCast_nonneg p)).trans (RHTower.sum_primesBelow_log_le X)
  have high := mul_le_mul_of_nonneg_left (sub_le_sub hi lk) (Nat.cast_nonneg X)
  have low := mul_le_mul_of_nonneg_left (sub_le_sub lo hk) (Nat.cast_nonneg X)
  have cpos := mul_nonneg (Nat.cast_nonneg (α := ℝ) X) (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4))
  change |_-(X:ℝ)*(Real.log X-Real.log K)| ≤ _
  exact abs_le.mpr ⟨by linarith only [base,th,low],by linarith only [ceil,high,cpos]⟩

/-- A single actual matching with a logarithmic saving in unpaid
vertices has fixed and crossing charges of opposite logarithmic size
on the unit-cofactor prime window. Their sum counts only that prime
window. Both estimates include the final sharp quotient floor. -/
theorem opposite_prime_window_flux_for_one_perfect_matching :
    ∃ G : ℕ → ℕ,Function.Involutive G ∧ (∀ n,G n=n ∨ GlobalDyadicOneTwoRel n (G n)) ∧
    (∃ c A : ℝ,0<c ∧ 0<A ∧ ∀ᶠ X : ℕ in atTop,((prefixUnpaid G X).card:ℝ) ≤ A*X/(Real.log X)^c) ∧
    ∀ y X : ℕ,1 ≤ X/(y+1) →
      let K := X/(y+1)
      let S := primeWindow K X
      let D := quotientBoundary (smoothLiftedPrefix (fixedSignedPrefix G) y) S (fun p => Real.log p) 0 X
      let C := quotientBoundary (smoothLiftedPrefix (crossingSignedPrefix G) y) S (fun p => Real.log p) 0 X
      D=(∑ p ∈ S,Real.log p*((X/p:ℕ):ℝ)) ∧ D+C=∑ p ∈ S,Real.log p ∧
      |D-X*(Real.log X-Real.log K)| ≤ X*(9+2*Real.log 4) ∧
      |C+X*(Real.log X-Real.log K)| ≤ X*(9+3*Real.log 4) := by
  obtain ⟨G,back,legal,cover,_,_,_,cheap⟩ := logarithmic_saving_with_only_crossing_edges (fun _ => 0)
  refine ⟨G,back,legal,cheap,fun y X kp => ?_⟩
  let K := X/(y+1)
  let S := primeWindow K X
  let D := quotientBoundary (smoothLiftedPrefix (fixedSignedPrefix G) y) S (fun p => Real.log p) 0 X
  let C := quotientBoundary (smoothLiftedPrefix (crossingSignedPrefix G) y) S (fun p => Real.log p) 0 X
  have limits (p : ℕ) (hp : p ∈ S) : 1 ≤ X/p ∧ X/p ≤ y := by
    obtain ⟨hi,lo⟩ := mem_filter.mp hp
    obtain ⟨px,pr⟩ := Nat.mem_primesLE.mp hi
    refine ⟨(Nat.le_div_iff_mul_le pr.pos).mpr (by simpa using px),Nat.le_of_lt_succ ?_⟩
    exact (Nat.div_lt_iff_lt_mul pr.pos).mpr (by
      simpa only [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul (Nat.succ_pos y)).mp lo)
  have fixed {t : ℕ} (low : t ≤ y) : smoothLiftedPrefix (fixedSignedPrefix G) y t=t :=
    lift_of_the_unit_before_the_prime_wall (only_unit_charge (restricted_unit_is_fixed G legal) cover) low
  have dex : D=∑ p ∈ S,Real.log p*((X/p:ℕ):ℝ) := by
    unfold D quotientBoundary
    simp only [Nat.zero_div,fixed (Nat.zero_le y),Nat.cast_zero,sub_zero]
    exact sum_congr rfl (fun p hp => congrArg (fun u : ℝ => Real.log p*u) (fixed (limits p hp).2))
  have add : D+C=∑ p ∈ S,Real.log p := by
    rw [show D+C=quotientBoundary (coprimeMoebiusSum (primorial y)) S (fun p => Real.log p) 0 X from
      (two_cutoff_rough_quotient_flux G (fun n _ => ⟨back n,legal n⟩) y S _ 0 X).symm]
    unfold quotientBoundary
    have z : coprimeMoebiusSum (primorial y) 0=0 := by simp [coprimeMoebiusSum]
    simp only [Nat.zero_div,z,sub_zero]
    exact sum_congr rfl (fun p hp => by rw [rough_prefix_through_the_unit (limits p hp).1 (limits p hp).2,mul_one])
  have cost := sharp_floor_in_a_prime_window kp (Nat.div_le_self X (y+1))
  rw [←dex] at cost
  refine ⟨dex,add,cost,?_⟩
  have th := (sum_le_sum_of_subset_of_nonneg (filter_subset (K<·) (Nat.primesLE X))
    (fun p _ _ => Real.log_natCast_nonneg p)).trans (RHTower.sum_primesBelow_log_le X)
  have pos : 0 ≤ ∑ p ∈ S,Real.log p := sum_nonneg (fun p _ => Real.log_natCast_nonneg p)
  exact abs_le.mpr ⟨by linarith only [add,(abs_le.mp cost).2,pos,th],
    by linarith only [add,(abs_le.mp cost).1,th]⟩

#print axioms opposite_prime_window_flux_for_one_perfect_matching
#print axioms compensating_prime_interval
end GaloisForLFunctions.RestrictedFactorizationCalculus
