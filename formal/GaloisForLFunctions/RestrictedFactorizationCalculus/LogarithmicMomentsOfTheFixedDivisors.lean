import GaloisForLFunctions.RestrictedFactorizationCalculus.DensityOneForRestrictedPrimeExchanges
import GaloisForLFunctions.RestrictedFactorizationCalculus.DetectingPowerBoundsByOneExchange
import GaloisForLFunctions.RHTower.LocalizedHalfDensityCurvature
import GaloisForLFunctions.RHTower.PrimeSquareMobiusDensityFracture
import GaloisForLFunctions.ArithmeticElectrostatics.TheSelfIntersectionOfATorsionOrbit

/-!
# Logarithmic cancellation on the fixed divisors

Each active prime range leaves a signed divisor measure with zero total
mass and a nonzero first logarithmic moment. Coprime ranges convolve
these measures. Their first surviving moment has degree exactly the
number of ranges.
-/

noncomputable section

open Finset RHTower
open ArithmeticFunction hiding id
open scoped Classical ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticElectrostatics GaloisForLFunctions.QuantitativeFactorizationMatching

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

/-- The signed moment of the fixed local divisors. -/
def fixedMoment (J : ℕ) (I : Finset ℕ) (m : ℕ) :=
  ∑ d ∈ (exchangePeriod I).divisors, if (activeBands J I d).Nonempty then 0
    else (μ d:ℝ)*(Real.log d)^m

private theorem count_prime_factors_prod {W : Finset ℕ} {g : ℕ → ℕ} (h : ∀ w ∈ W, g w ≠ 0) :
    cardFactors (∏ w ∈ W,g w) = ∑ w ∈ W,cardFactors (g w) := by
  induction W using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have hS : ∀ w ∈ S, g w ≠ 0 := fun w hw => h w (mem_insert_of_mem hw)
    rw [prod_insert ha,sum_insert ha,cardFactors_mul (h _ (mem_insert_self ..)) (prod_ne_zero_iff.mpr hS),ih hS]

private theorem local_facts {J k : ℕ} (h : bandReady J k) {w : ℕ} (hw : w ∈ switchProducts k) :
    w ∣ switchModulus k ∧ bandPartner J k w ∣ switchModulus k ∧
      μ w=1 ∧ μ (bandPartner J k w) = -1 ∧ cardFactors w=2 ∧ cardFactors (bandPartner J k w)=1 := by
  obtain ⟨hdw,hdp,hμw,hμp⟩ := table_pair_divisors_and_signs h hw
  obtain ⟨hp,⟨q,hq,r,hr,_,he⟩,_,_⟩ := h.1.2 w hw
  have hq' := (mem_switchPrimes.mp hq).1
  have hr' := (mem_switchPrimes.mp hr).1
  refine ⟨hdw,hdp,hμw,hμp,?_,cardFactors_apply_prime (mem_switchPrimes.mp hp).1⟩
  rw [he,cardFactors_mul hq'.ne_zero hr'.ne_zero,cardFactors_apply_prime hq',cardFactors_apply_prime hr']

private theorem products_nonempty {J k : ℕ} (h : bandReady J k) : (switchProducts k).Nonempty := by
  by_contra hn
  have hz : switchProducts k=∅ := not_nonempty_iff_eq_empty.mp hn
  have hm := h.2
  rw [hz,image_empty,sum_empty] at hm
  norm_num at hm

/-- First signed logarithmic moment left in one range. -/
def logExchangeMoment (J k : ℕ) :=
  ∑ w ∈ switchProducts k, (Real.log (bandPartner J k w)-Real.log w)

theorem logExchangeMoment_ne_zero {J k : ℕ} (h : bandReady J k) : logExchangeMoment J k ≠ 0 := by
  let W := switchProducts k
  let f := bandPartner J k
  have hM := (switchModulus_spec k).2.2
  have hp (w : ℕ) (hw : w ∈ W) : 0 < f w := Nat.pos_of_dvd_of_pos (local_facts h hw).2.1 hM
  have hw (w : ℕ) (hm : w ∈ W) : 0 < w := Nat.pos_of_dvd_of_pos (local_facts h hm).1 hM
  have primes : cardFactors (∏ w ∈ W,f w)=W.card := by
    rw [count_prime_factors_prod (fun w hm => (hp w hm).ne')]
    calc _ = ∑ _w ∈ W, 1 := sum_congr rfl fun _ hm => (local_facts h hm).2.2.2.2.2
         _ = _ := by simp
  have pairs : cardFactors (∏ w ∈ W,w)=W.card*2 := by
    rw [count_prime_factors_prod (fun w hm => (hw w hm).ne')]
    calc _ = ∑ _w ∈ W, 2 := sum_congr rfl fun _ hm => (local_facts h hm).2.2.2.2.1
         _ = _ := by simp
  intro he
  change (∑ w ∈ W, (Real.log (f w)-Real.log w))=0 at he
  rw [sum_sub_distrib,sub_eq_zero,←Real.log_prod (fun w hm => (Nat.cast_ne_zero.mpr (hp w hm).ne')),
    ←Real.log_prod (fun w hm => (Nat.cast_ne_zero.mpr (hw w hm).ne'))] at he
  have hprod := Real.log_injOn_pos (prod_pos fun w hm => Nat.cast_pos.mpr (hp w hm))
    (prod_pos fun w hm => Nat.cast_pos.mpr (hw w hm)) he
  have heq : (∏ w ∈ W, f w) = ∏ w ∈ W, w := by exact_mod_cast hprod
  rw [heq,pairs] at primes
  have hcard : 0 < W.card := card_pos.mpr (products_nonempty h)
  omega

private theorem fixed_single {J k : ℕ} (h : bandReady J k) :
    fixedMoment J {k} 0=0 ∧ fixedMoment J {k} 1=logExchangeMoment J k := by
  let M := switchModulus k
  let W := switchProducts k
  let f := bandPartner J k
  have hM := (switchModulus_spec k).2.2
  obtain ⟨w,hw⟩ := products_nonempty h
  obtain ⟨_,⟨q,hq,r,hr,hqr,_⟩,_,_⟩ := h.1.2 w hw
  have pdiv {a : ℕ} (ha : a ∈ switchPrimes k) : a ∣ M :=
    Nat.dvd_of_mem_primeFactors ((switchModulus_spec k).2.1 ▸ ha)
  have hq' := (mem_switchPrimes.mp hq).1
  have hr' := (mem_switchPrimes.mp hr).1
  have hM1 : M ≠ 1 := fun he => hq'.not_dvd_one (he ▸ pdiv hq)
  have hpr : ¬M.Prime := fun hp => hqr.ne
    (((Nat.prime_dvd_prime_iff_eq hq' hp).1 (pdiv hq)).trans
      ((Nat.prime_dvd_prime_iff_eq hr' hp).1 (pdiv hr)).symm)
  have hzero : (∑ d ∈ M.divisors,(μ d:ℝ))=0 := by
    rw [sum_divisors_moebiusCast hM.ne',ArithmeticFunction.one_apply_ne hM1]
  have hfirst : (∑ d ∈ M.divisors,(μ d:ℝ)*Real.log d)=0 := by
    rw [sum_divisors_moebius_mul_log hM.ne',vonMangoldt_eq_zero_iff.mpr
      (fun hv => hpr (Nat.squarefree_and_prime_pow_iff_prime.mp ⟨(switchModulus_spec k).1,hv⟩)),neg_zero]
  have hdis : Disjoint W (W.image f) := by
    refine disjoint_left.mpr fun a ha hh => ?_
    obtain ⟨b,hb,he⟩ := mem_image.mp hh
    have h₁ := (local_facts h ha).2.2.1
    have h₂ := (local_facts h hb).2.2.2.1
    change μ (f b) = -1 at h₂
    rw [he] at h₂
    omega
  have hsub : bandEndpoints J k ⊆ M.divisors := by
    intro d hd
    rcases mem_union.mp hd with ha|hb
    · exact Nat.mem_divisors.mpr ⟨(local_facts h ha).1,hM.ne'⟩
    · obtain ⟨w,hw,rfl⟩ := mem_image.mp hb
      exact Nat.mem_divisors.mpr ⟨(local_facts h hw).2.1,hM.ne'⟩
  have split (j : ℕ) :
      fixedMoment J {k} j=(∑ d ∈ M.divisors,(μ d:ℝ)*(Real.log d)^j) +
        ∑ w ∈ W, ((Real.log (f w))^j-(Real.log w)^j) := by
    let v := fun d : ℕ => (μ d:ℝ)*(Real.log d)^j
    have hx : fixedMoment J {k} j=∑ d ∈ M.divisors \ bandEndpoints J k, v d := by
      unfold fixedMoment
      simp only [exchangePeriod,prod_singleton]
      change (∑ d ∈ M.divisors, if (activeBands J {k} d).Nonempty then 0 else v d) =
        ∑ d ∈ M.divisors \ bandEndpoints J k, v d
      rw [sdiff_eq_filter,sum_filter]
      apply sum_congr rfl
      intro d hd
      have hg := Nat.gcd_eq_left (Nat.dvd_of_mem_divisors hd)
      have ha : (activeBands J {k} d).Nonempty ↔ d ∈ bandEndpoints J k := by
        simp only [activeBands,filter_nonempty_iff,mem_singleton]
        change (∃ i, i=k ∧ d.gcd (switchModulus i) ∈ bandEndpoints J i) ↔ _
        simp only [exists_eq_left',show d.gcd (switchModulus k)=d from hg]
      by_cases hm : d ∈ bandEndpoints J k <;> simp [ha,hm]
    rw [hx,sum_sdiff_eq_sub hsub]
    change _ - (∑ d ∈ W ∪ W.image f, v d) = _
    rw [sum_union hdis,sum_image h.1.1,sum_sub_distrib]
    have hs : ∑ d ∈ W, v d = ∑ d ∈ W,(Real.log d)^j := sum_congr rfl (fun d hd => by
      dsimp only [v]; rw [(local_facts h hd).2.2.1]; simp)
    have ht : ∑ d ∈ W,v (f d) = -∑ d ∈ W,(Real.log (f d))^j := by
      rw [←sum_neg_distrib]
      apply sum_congr rfl
      intro d hd
      dsimp only [v]; rw [show μ (f d) = -1 from (local_facts h hd).2.2.2.1]; simp
    rw [hs,ht]
    ring
  constructor
  · simpa only [split,pow_zero,mul_one,sub_self,sum_const_zero,add_zero] using hzero
  · rw [split]
    simpa only [pow_one,hfirst,zero_add] using (rfl : (∑ d ∈ W, (Real.log (f d)-Real.log d))=logExchangeMoment J k)

/-- Möbius sign on a fixed local divisor, zero on eligible divisors. -/
def fixedDivisorCharge (J : ℕ) (I : Finset ℕ) (d : ℕ) : ℝ :=
  if (activeBands J I d).Nonempty then 0 else μ d

private theorem moment_as_sum (J : ℕ) (I : Finset ℕ) (m : ℕ) :
    fixedMoment J I m=∑ d ∈ (exchangePeriod I).divisors, fixedDivisorCharge J I d*(Real.log d)^m := by
  apply sum_congr rfl
  intro d _
  by_cases h : (activeBands J I d).Nonempty <;> simp only [fixedDivisorCharge,h,if_false,if_true,zero_mul]

private theorem local_charge_mul {J k a b : ℕ} {I : Finset ℕ}
    (hc : (switchModulus k).Coprime (exchangePeriod I)) (ha : a ∣ switchModulus k) (hb : b ∣ exchangePeriod I) :
    fixedDivisorCharge J (insert k I) (a*b)=fixedDivisorCharge J {k} a*fixedDivisorCharge J I b := by
  have hcoA := Nat.Coprime.coprime_dvd_left ha hc
  have hcoB := Nat.Coprime.coprime_dvd_left hb hc.symm
  have hab := Nat.Coprime.coprime_dvd_right hb hcoA
  have hak : (a*b).gcd (switchModulus k)=a.gcd (switchModulus k) :=
    Nat.Coprime.gcd_mul_right_cancel a hcoB
  have hbi (i : ℕ) (hi : i ∈ I) : (a*b).gcd (switchModulus i)=b.gcd (switchModulus i) :=
    Nat.Coprime.gcd_mul_left_cancel b (Nat.Coprime.coprime_dvd_right (divides_period hi) hcoA)
  have he : (activeBands J (insert k I) (a*b)).Nonempty ↔
      (activeBands J {k} a).Nonempty ∨ (activeBands J I b).Nonempty := by
    simp only [activeBands,filter_nonempty_iff,mem_insert,mem_singleton,exists_eq_left']
    constructor
    · rintro ⟨i,hi,hm⟩
      rcases hi with rfl | hi
      · exact Or.inl (by rwa [hak] at hm)
      · exact Or.inr ⟨i,hi,by rwa [hbi i hi] at hm⟩
    · rintro (hk | ⟨i,hi,hm⟩)
      · exact ⟨k,Or.inl rfl,by rw [hak]; exact hk⟩
      · exact ⟨i,Or.inr hi,by rw [hbi i hi]; exact hm⟩
  unfold fixedDivisorCharge
  rcases em (activeBands J {k} a).Nonempty with h|h <;>
    rcases em (activeBands J I b).Nonempty with e|e <;>
    simp [he,h,e,isMultiplicative_moebius.map_mul_of_coprime hab]

private theorem moment_insert {J k m : ℕ} {I : Finset ℕ} (hk : k ∉ I)
    (hc : (switchModulus k).Coprime (exchangePeriod I)) :
    fixedMoment J (insert k I) m = ∑ i ∈ range (m+1),
      (m.choose i:ℝ)*fixedMoment J {k} i*fixedMoment J I (m-i) := by
  let P := switchModulus k
  let Q := exchangePeriod I
  have he : exchangePeriod (insert k I)=P*Q := prod_insert hk
  have hi : exchangePeriod {k}=P := prod_singleton _ _
  rw [moment_as_sum,he,sum_divisors_mul_of_coprime hc]
  let u := fun i a => fixedDivisorCharge J {k} a*(Real.log a)^i
  let v := fun i b => fixedDivisorCharge J I b*(Real.log b)^i
  have row (a : ℕ) (ha : a ∈ P.divisors) (b : ℕ) (hb : b ∈ Q.divisors) :
      fixedDivisorCharge J (insert k I) (a*b)*(Real.log (a*b:ℕ))^m =
        ∑ i ∈ range (m+1), (m.choose i:ℝ)*u i a*v (m-i) b := by
    rw [local_charge_mul hc (Nat.dvd_of_mem_divisors ha) (Nat.dvd_of_mem_divisors hb),Nat.cast_mul,
      Real.log_mul (Nat.cast_ne_zero.mpr (Nat.pos_of_mem_divisors ha).ne')
        (Nat.cast_ne_zero.mpr (Nat.pos_of_mem_divisors hb).ne'),add_pow,mul_sum]
    exact sum_congr rfl fun _ _ => by dsimp only [u,v]; ring
  have summand (a : ℕ) (ha : a ∈ P.divisors) :
      (∑ b ∈ Q.divisors, fixedDivisorCharge J (insert k I) (a*b)*(Real.log (a*b:ℕ))^m) =
        ∑ i ∈ range (m+1), (m.choose i:ℝ)*u i a*fixedMoment J I (m-i) := by
    rw [sum_congr rfl (row a ha),sum_comm]
    refine sum_congr rfl fun i _ => ?_
    rw [←mul_sum,moment_as_sum]
  rw [sum_congr rfl summand,sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [←sum_mul,←mul_sum,moment_as_sum J {k},hi]

/-- All moments below the number of active disjoint ranges vanish; the
next moment equals the factorial times the product of their nonzero
logarithmic biases. This holds for arbitrarily many ranges. -/
theorem first_fixed_divisor_moment {J : ℕ} (I : Finset ℕ) (hI : ∀ k ∈ I, bandReady J k)
    (hco : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (switchModulus i).Coprime (switchModulus j)) :
    (∀ m < I.card, fixedMoment J I m=0) ∧
      fixedMoment J I I.card=(I.card.factorial:ℝ)*∏ k ∈ I,logExchangeMoment J k ∧
      fixedMoment J I I.card ≠ 0 := by
  have claim : (∀ m < I.card, fixedMoment J I m=0) ∧
      fixedMoment J I I.card=(I.card.factorial:ℝ)*∏ k ∈ I,logExchangeMoment J k := by
    induction I using Finset.induction_on with
    | empty =>
      refine ⟨by simp,?_⟩
      simp [fixedMoment,exchangePeriod,activeBands]
    | @insert k I hk ih =>
      have h₁ (j : ℕ) (hj : j ∈ I) := hI j (mem_insert_of_mem hj)
      have h₂ (i : ℕ) (hi : i ∈ I) (j : ℕ) (hj : j ∈ I) (hn : i ≠ j) :=
        hco i (mem_insert_of_mem hi) j (mem_insert_of_mem hj) hn
      have hp : (switchModulus k).Coprime (exchangePeriod I) := Nat.Coprime.prod_right fun j hj =>
        hco _ (mem_insert_self ..) _ (mem_insert_of_mem hj) (fun h => hk (h ▸ hj))
      obtain ⟨hl,hmain⟩ := ih h₁ h₂
      have here := fixed_single (hI k (mem_insert_self ..))
      rw [card_insert_of_notMem hk]
      constructor
      · intro m hm
        rw [moment_insert hk hp]
        apply sum_eq_zero
        intro i hi
        by_cases he : i=0
        · simp [he,here.1]
        · rw [hl (m-i) (by have hi' := mem_range.mp hi; omega),mul_zero]
      · rw [moment_insert hk hp,sum_eq_single 1]
        · rw [here.2,Nat.add_sub_cancel,hmain,Nat.factorial_succ,Nat.cast_mul,prod_insert hk,Nat.choose_one_right]
          ring
        · intro i hi hne
          by_cases he : i=0
          · simp [he,here.1]
          · have hi' := mem_range.mp hi
            have hl' : I.card+1-i < I.card := by omega
            rw [hl _ hl',mul_zero]
        · simp
  refine ⟨claim.1,claim.2,?_⟩
  rw [claim.2]
  exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
    (prod_ne_zero_iff.mpr fun k hk => logExchangeMoment_ne_zero (hI k hk))

private theorem gcd_fixed_pattern (J : ℕ) (I : Finset ℕ) (n : ℕ) :
    activeBands J I (n.gcd (exchangePeriod I)) = activeBands J I n := by
  ext k
  simp only [activeBands,mem_filter]
  by_cases hk : k ∈ I
  · simp only [hk,true_and,Nat.gcd_assoc,Nat.gcd_eq_right (divides_period hk)]
  · simp [hk]

/-- The sharp prefix on the actual fixed integers is a signed sum of
coprime prefixes evaluated at the distinct integer quotients X/d. -/
theorem fixed_prefix_as_coprime_quotients (J X : ℕ) (I : Finset ℕ)
    (hI : ∀ k ∈ I, bandReady J k)
    (hco : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (switchModulus i).Coprime (switchModulus j)) :
    let Q := exchangePeriod I
    ∑ n ∈ (squarefreeOf (Icc 1 X)).filter (fun n => rangeSwitch J I n=n), (μ n:ℝ) =
      ∑ d ∈ Q.divisors, fixedDivisorCharge J I d *
        ∑ a ∈ (Icc 1 (X/d)).filter (fun a => a.Coprime Q), (μ a:ℝ) := by
  let Q := exchangePeriod I
  let E := Q.divisors.filter (fun d => ¬(activeBands J I d).Nonempty)
  let V := (Icc 1 X).filter (fun n => n.gcd Q ∈ E)
  have hc (n : ℕ) : n.gcd Q ∈ E ↔ ¬(activeBands J I n).Nonempty := by
    have hd : n.gcd Q ∈ Q.divisors := Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right ..,(period_pos I).ne'⟩
    simp only [E,mem_filter,hd,true_and,Q,gcd_fixed_pattern]
  have heq : (squarefreeOf (Icc 1 X)).filter (fun n => rangeSwitch J I n=n)=V.filter Squarefree := by
    ext n
    simp only [squarefreeOf,V,mem_filter,hc]
    constructor
    · rintro ⟨⟨hi,hs⟩,hh⟩
      exact ⟨⟨hi,(rangeSwitch_involution J I hI hco hs).2.2.1.mp hh⟩,hs⟩
    · rintro ⟨⟨hi,ha⟩,hs⟩
      exact ⟨⟨hi,hs⟩,(rangeSwitch_involution J I hI hco hs).2.2.1.mpr ha⟩
  have hzero : (∑ n ∈ V.filter Squarefree,(μ n:ℝ))=∑ n ∈ V,(μ n:ℝ) := by
    apply sum_subset (filter_subset _ _)
    intro n hn hns
    rw [moebius_eq_zero_of_not_squarefree (fun h => hns (mem_filter.mpr ⟨hn,h⟩)),Int.cast_zero]
  rw [heq,hzero,signed_prefix_of_gcd_classes (Q := Q) (E := E) (filter_subset _ _) X]
  unfold divisorPrefix
  rw [sum_filter]
  apply sum_congr rfl
  intro d _
  by_cases h : (activeBands J I d).Nonempty
  · simp only [h,not_true_eq_false,if_false,fixedDivisorCharge,if_true,zero_mul]
  · rw [if_pos h,fixedDivisorCharge,if_neg h]
    congr 1
    rw [coprimeMoebiusSum,sum_filter]
    exact sum_congr rfl fun a _ => by simp only [coprimeMoebiusIndicator,Nat.coprime_comm Q a]

/-- Every requested order of exact fixed-divisor cancellation is realized
by disjoint prime exchanges at any prescribed resolution. The same ranges
give the signed quotient identity at every sharp prefix. -/
theorem arbitrarily_high_fixed_divisor_cancellation (J : ℕ) (hJ : 0 < J) (m : ℕ) :
    ∃ I : Finset ℕ, I.card=m ∧ (∀ k ∈ I, bandReady J k) ∧
      (∀ j < m, fixedMoment J I j=0) ∧ fixedMoment J I m ≠ 0 ∧
      ∀ X : ℕ, ∑ n ∈ (squarefreeOf (Icc 1 X)).filter (fun n => rangeSwitch J I n=n), (μ n:ℝ) =
        ∑ d ∈ (exchangePeriod I).divisors, fixedDivisorCharge J I d *
          ∑ a ∈ (Icc 1 (X/d)).filter (fun a => a.Coprime (exchangePeriod I)), (μ a:ℝ) := by
  obtain ⟨H,hH⟩ := Filter.eventually_atTop.mp (eventually_bandReady J hJ)
  obtain ⟨I,hi,_,hr,hco,_⟩ := packing_within J (H+1) (Nat.succ_pos _)
    (fun k hk => hH k (by omega)) m
  obtain ⟨hl,_,hn⟩ := first_fixed_divisor_moment I hr hco
  rw [hi] at hl hn
  exact ⟨I,hi,hr,hl,hn,fun X => fixed_prefix_as_coprime_quotients J X I hr hco⟩

end GaloisForLFunctions.RestrictedFactorizationCalculus
