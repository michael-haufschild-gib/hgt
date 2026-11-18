import GaloisForLFunctions.BezoutValuationIncidence.GcdOrbitProjectionAndExactTranslationPeriods
import GaloisForLFunctions.BiScaleUncertainty.FiniteSieveRealization
import GaloisForLFunctions.RHTower.Sieve.PrimeCountRelativeWindow
import GaloisForLFunctions.RHTower.RVCumulantAverage
import GaloisForLFunctions.RHTower.ZetaStandardTwistDichotomy
import GaloisForLFunctions.RHTower.EulerDeletionQuasiShuffleConvergence

/-!
# Rational-grid jumps of finite floor sums

A floor with real slope jumps at a positive integer exactly when that integer
annihilates the slope modulo one. Its positive integer jumps thus form one
divisor row, possibly empty. Periodicity retains only divisors of the period.
-/

noncomputable section

open Classical Finset Filter Topology
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.BiScaleUncertainty.FiniteHorizon

namespace GaloisForLFunctions.ExceptionalLayerTheory

private theorem positive_row_eq_at_zero {q N : ℕ} (hq : 0 < q) {J : ℕ → ℝ}
    (hper : Function.Periodic J q) (c : ℕ → ℝ)
    (he : ∀ n : ℕ, 0 < n → J n = sieveSeq N c n) : J 0 = sieveSeq N c 0 := by
  have hm (k : ℕ) : J (k*q)=J 0 := by
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.succ_mul,hper,ih]
  rw [← hm N.factorial,he _ (Nat.mul_pos (Nat.factorial_pos _) hq)]
  unfold sieveSeq
  apply sum_congr _ (fun _ _ => rfl)
  apply filter_congr
  intro d hd
  have hd' := (Nat.dvd_factorial (mem_Icc.mp hd).1 (mem_Icc.mp hd).2).trans
    (dvd_mul_right N.factorial q)
  simp [hd']

/-- A periodic sequence of real jumps is a finite divisor sum on the positive
integers exactly when each value depends only on its gcd with the period. -/
theorem periodic_divisor_sum_iff_gcd {q : ℕ} (hq : 0 < q) {J : ℕ → ℝ}
    (hper : Function.Periodic J q) :
    (∃ (N : ℕ) (c : ℕ → ℝ), ∀ n : ℕ, 0 < n → J n = sieveSeq N c n) ↔
      ∀ n : ℕ, J n = J (n.gcd q) := by
  constructor
  · rintro ⟨N,c,h⟩
    have he : J=sieveSeq N c := funext fun n => by
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · exact positive_row_eq_at_zero hq hper c h
      · exact h n hpos
    rw [he] at hper ⊢
    have ha := (sieveSeq_periodic_iff_active_divisors N q c).mp hper
    intro n
    simp only [sieveSeq,sum_filter]
    refine sum_congr rfl fun d hd => ?_
    by_cases hz : c d=0
    · simp [hz]
    · simp only [Nat.dvd_gcd_iff,and_iff_left (ha d hd hz)]
  · intro h
    let c := fun d => if d ∣ q then integerSignalMobiusCoefficient J d else 0
    refine ⟨q,c,fun n _ => ?_⟩
    have hg := Nat.gcd_pos_of_pos_right n hq
    rw [h n,← sum_divisors_integerSignalMobiusCoefficient J _ hg,sieveSeq]
    simp only [c]
    rw [← sum_filter]
    refine sum_congr ?_ fun _ _ => rfl
    ext d
    simp only [Nat.mem_divisors,mem_filter,mem_Icc,Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨⟨hn,hq'⟩,_⟩
      exact ⟨⟨⟨Nat.pos_of_dvd_of_pos hq' hq,Nat.le_of_dvd hq hq'⟩,hn⟩,hq'⟩
    · rintro ⟨⟨_,hn⟩,hq'⟩
      exact ⟨⟨hn,hq'⟩,hg.ne'⟩

/-- Piecewise constant profile with prescribed positive-integer jumps. -/
def integerGridProfile (J : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 ⌊t⌋₊, J n

private theorem floor_on_left {a u : ℝ} (ha : 0 < a) {k : ℤ}
    (hl : (k:ℝ) < a*u) (hu : a*u ≤ (k:ℝ)+1) :
    ∀ᶠ t in 𝓝[<] u, ⌊a*t⌋=k := by
  have hlow : (k:ℝ)/a < u := (div_lt_iff₀ ha).mpr (by simpa only [mul_comm] using hl)
  filter_upwards [nhdsWithin_le_nhds (lt_mem_nhds hlow),self_mem_nhdsWithin] with t ht hu'
  apply Int.floor_eq_iff.mpr
  constructor
  · simpa only [mul_comm] using ((div_lt_iff₀ ha).mp ht).le
  · exact (mul_lt_mul_of_pos_left (show t < u from hu') ha).trans_le hu

private theorem floor_left_jump {a : ℝ} (ha : 0 < a) (u : ℝ) :
    ∀ᶠ t in 𝓝[<] u, (⌊a*u⌋:ℝ)-(⌊a*t⌋:ℝ) =
      (if ((a*u : ℝ) : UnitAddCircle)=0 then (1:ℝ) else 0) := by
  by_cases h : ((a*u : ℝ) : UnitAddCircle)=0
  · obtain ⟨k,hk⟩ := (_root_.RHTower.coe_unitAddCircle_eq_zero_iff _).mp h
    have hl : ((k-1:ℤ):ℝ) < a*u := by rw [← hk,Int.cast_sub,Int.cast_one]; linarith
    have hu : a*u ≤ ((k-1:ℤ):ℝ)+1 := by rw [← hk,Int.cast_sub,Int.cast_one]; linarith
    filter_upwards [floor_on_left ha hl hu] with t ht
    rw [if_pos h,ht,← hk,Int.floor_intCast,Int.cast_sub,Int.cast_one]
    ring
  · have hl : (⌊a*u⌋:ℝ) < a*u := lt_of_le_of_ne (Int.floor_le _) (fun e =>
      h ((_root_.RHTower.coe_unitAddCircle_eq_zero_iff _).mpr ⟨_,e⟩))
    filter_upwards [floor_on_left ha hl (Int.lt_floor_add_one _).le] with t ht
    rw [if_neg h,ht,sub_self]

private theorem profile_left_jump (J : ℕ → ℝ) (n : ℕ) :
    ∀ᶠ t in 𝓝[<] ((n:ℝ)+1), integerGridProfile J ((n:ℝ)+1)-integerGridProfile J t=J (n+1) := by
  filter_upwards [nhdsWithin_le_nhds (lt_mem_nhds (lt_add_one (n:ℝ))),self_mem_nhdsWithin]
    with t hl hu
  have he : ⌊t⌋₊=n := Nat.floor_eq_iff (Nat.cast_nonneg n |>.trans hl.le) |>.mpr ⟨hl.le,hu⟩
  rw [integerGridProfile,integerGridProfile,he,← Nat.cast_succ,Nat.floor_natCast,
    sum_Icc_succ_top (by omega : 1≤n+1),add_sub_cancel_left]

private theorem integer_jump_order (a : ℝ) (n : ℕ) :
    (((a*(n:ℝ):ℝ) : UnitAddCircle)=0) ↔ addOrderOf (a : UnitAddCircle) ∣ n := by
  rw [mul_comm,← nsmul_eq_mul,AddCircle.coe_nsmul]
  exact addOrderOf_dvd_iff_nsmul_eq_zero.symm

private theorem floor_sum_jump {ι : Type*} (s : Finset ι) (w a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 < a i) {J : ℕ → ℝ}
    (h : ∀ t : ℝ, 0 ≤ t → integerGridProfile J t = ∑ i ∈ s, w i*(⌊a i*t⌋:ℝ))
    {n : ℕ} (hn : 0 < n) :
    J n = ∑ i ∈ s, if addOrderOf (a i : UnitAddCircle) ∣ n then w i else 0 := by
  classical
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  let u : ℝ := (m:ℝ)+1
  have hu : 0 < u := by dsimp only [u]; positivity
  have hrow : ∀ᶠ t in 𝓝[<] u, ∀ i ∈ s, (⌊a i*u⌋:ℝ)-(⌊a i*t⌋:ℝ) =
      (if ((a i*u : ℝ) : UnitAddCircle)=0 then (1:ℝ) else 0) :=
    (Filter.eventually_all_finset s).mpr fun i hi => floor_left_jump (ha i hi) u
  obtain ⟨t,ht,hp,ht0⟩ := (hrow.and ((profile_left_jump J m).and
    (nhdsWithin_le_nhds (lt_mem_nhds hu)))).exists
  rw [h u hu.le,h t ht0.le,← sum_sub_distrib] at hp
  rw [← hp]
  refine sum_congr rfl fun i hi => ?_
  rw [← mul_sub,ht i hi]
  have he : u = (m.succ:ℝ) := (Nat.cast_succ m).symm
  rw [he]
  simp only [integer_jump_order]
  split <;> simp

private theorem divisor_rows_of_orders {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (d : ι → ℕ) :
    ∃ (N : ℕ) (c : ℕ → ℝ), ∀ n : ℕ, 0 < n →
      (∑ i ∈ s, if d i ∣ n then w i else 0) = sieveSeq N c n := by
  classical
  let N := ∑ i ∈ s, d i
  let c := fun k => ∑ i ∈ s, if k=d i then w i else 0
  refine ⟨N,c,fun n hn => ?_⟩
  unfold sieveSeq
  dsimp only [c]
  rw [sum_comm]
  refine sum_congr rfl fun i hi => ?_
  rw [sum_ite_eq']
  have hN : d i ≤ N := single_le_sum (f := d) (fun _ _ => Nat.zero_le _) hi
  by_cases hd : d i ∣ n
  · have hp : 1≤d i := Nat.pos_of_dvd_of_pos hd hn
    simp [hp,hN,hd]
  · simp [hd]

/-- On an integer grid every periodic sequence of jumps produced by real floor
slopes is constant on each gcd class of the period. -/
theorem finite_floor_sum_jumps_depend_on_gcd {ι : Type*} (s : Finset ι) (w a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 < a i) {q : ℕ} (hq : 0 < q) {J : ℕ → ℝ}
    (hper : Function.Periodic J q)
    (h : ∀ t : ℝ, 0 ≤ t → integerGridProfile J t = ∑ i ∈ s, w i*(⌊a i*t⌋:ℝ)) :
    ∀ n : ℕ, J n = J (n.gcd q) := by
  apply (periodic_divisor_sum_iff_gcd hq hper).mp
  obtain ⟨N,c,hc⟩ := divisor_rows_of_orders s w (fun i => addOrderOf (a i : UnitAddCircle))
  exact ⟨N,c,fun n hn => (floor_sum_jump s w a ha h hn).trans (hc n hn)⟩

/-- The converse gives the rational slopes and their coefficients explicitly.
They are the reciprocal divisors and the Möbius transform of the grid jumps. -/
theorem integerGridProfile_eq_divisor_floors {q : ℕ} (hq : 0 < q) {J : ℕ → ℝ}
    (h : ∀ n : ℕ, J n=J (n.gcd q)) (t : ℝ) :
    integerGridProfile J t =
      ∑ d ∈ q.divisors, integerSignalMobiusCoefficient J d*(⌊t/(d:ℝ)⌋₊:ℝ) := by
  have hj (n : ℕ) : J n = ∑ d ∈ q.divisors,
      if d ∣ n then integerSignalMobiusCoefficient J d else 0 := by
    rw [h n,← sum_divisors_integerSignalMobiusCoefficient J _ (Nat.gcd_pos_of_pos_right n hq),← sum_filter]
    refine sum_congr ?_ fun _ _ => rfl
    ext d
    simp only [Nat.mem_divisors,mem_filter,Nat.dvd_gcd_iff]
    exact ⟨fun h => ⟨⟨h.1.2,hq.ne'⟩,h.1.1⟩,fun h => ⟨⟨h.2,h.1.1⟩,(Nat.gcd_pos_of_pos_right n hq).ne'⟩⟩
  rw [integerGridProfile]
  conv_lhs => arg 2; intro n; rw [hj n]
  rw [sum_comm]
  refine sum_congr rfl fun d hd => ?_
  rw [← sum_filter,_root_.RHTower.sum_Icc_filter_dvd_reindex d _ (Nat.pos_of_mem_divisors hd),
    sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul,Nat.floor_div_natCast,mul_comm]

private def lastJump (q n : ℕ) : ℝ :=
  (if q ∣ n+1 then 1 else 0)-(if q ∣ n then 1 else 0)

private theorem lastJump_periodic (q : ℕ) : Function.Periodic (lastJump q) q := by
  intro n
  simp only [lastJump,show n+q+1=n+1+q by omega,← Nat.dvd_add_iff_left (dvd_refl q)]

private theorem lastJump_prefix {q : ℕ} (hq : 2≤q) (n : ℕ) :
    (∑ k ∈ Icc 1 n, lastJump q k) = if q ∣ n+1 then 1 else 0 := by
  induction n with
  | zero =>
    have he : ¬q ∣ 1 := fun hd => (by have := Nat.le_of_dvd one_pos hd; omega)
    simp [he]
  | succ n ih =>
    rw [sum_Icc_succ_top (by omega : 1≤n+1),ih,lastJump]
    ring

/-- No finite collection of factorials with positive real slopes has the last
quotient class as its carry profile when the period is at least three. -/
theorem last_quotient_class_not_finite_real_floors {ι : Type*} (s : Finset ι) (w a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 < a i) {q : ℕ} (hq : 3≤q) :
    ¬∀ t : ℝ, 0≤t → (if q ∣ ⌊t⌋₊+1 then (1:ℝ) else 0) =
      ∑ i ∈ s, w i*(⌊a i*t⌋:ℝ) := by
  intro hf
  have h := finite_floor_sum_jumps_depend_on_gcd s w a ha (by omega : 0 < q) (lastJump_periodic q)
    (fun t ht => (lastJump_prefix (by omega : 2≤q) ⌊t⌋₊).trans (hf t ht)) (q-1)
  have hg : (q-1).gcd q=1 := by
    rw [← Nat.gcd_sub_self_right (Nat.sub_le q 1),show q-(q-1)=1 by omega,Nat.gcd_one_right]
  have h₂ : ¬q ∣ 2 := fun hd => (by have := Nat.le_of_dvd (by omega : 0<2) hd; omega)
  have h₁ : ¬q ∣ 1 := fun hd => (by have := Nat.le_of_dvd one_pos hd; omega)
  have hpre : ¬q ∣ q-1 := fun hd => (by have := Nat.le_of_dvd (by omega : 0<q-1) hd; omega)
  norm_num [hg,lastJump,show q-1+1=q by omega,h₂,h₁,hpre] at h

/-- Period two is attained by the single central-binomial carry. -/
theorem last_quotient_class_two_floor_identity (t : ℝ) :
    (if 2 ∣ ⌊t⌋₊+1 then (1:ℝ) else 0) = (⌊t⌋₊:ℝ)-2*(⌊t/2⌋₊:ℝ) := by
  let n := ⌊t⌋₊
  have he : ⌊t/2⌋₊ = n/2 := Nat.floor_div_natCast t 2
  rw [he]
  change (if 2 ∣ n+1 then (1:ℝ) else 0) = (n:ℝ)-2*((n/2:ℕ):ℝ)
  by_cases h : 2 ∣ n+1
  · rw [if_pos h,eq_sub_iff_add_eq]
    exact_mod_cast (by omega : 1+2*(n/2)=n)
  · rw [if_neg h,eq_sub_iff_add_eq,zero_add]
    exact_mod_cast (by omega : 2*(n/2)=n)

private theorem floors_constant_to_right {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0<a i) (t : ℝ) :
    ∃ v : ℝ, t<v ∧ ∀ x : ℝ, t≤x → x<v → ∀ i ∈ s, ⌊a i*x⌋=⌊a i*t⌋ := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨t+1,lt_add_one _,by simp⟩
  | @insert i s hi ih =>
    have hp := ha i (mem_insert_self ..)
    obtain ⟨v,hv,h⟩ := ih (fun k hk => ha k (mem_insert_of_mem hk))
    let z := ((⌊a i*t⌋:ℝ)+1)/(a i)
    have hz : t<z := (lt_div_iff₀ hp).mpr (by rw [mul_comm]; exact Int.lt_floor_add_one _)
    refine ⟨min v z,lt_min hv hz,fun x hl hu k hk => ?_⟩
    rcases mem_insert.mp hk with rfl | hk
    · apply Int.floor_eq_iff.mpr
      exact ⟨(Int.floor_le _).trans (mul_le_mul_of_nonneg_left hl hp.le),
        by simpa only [mul_comm x] using (lt_div_iff₀ hp).mp (lt_of_lt_of_le hu (min_le_right v z))⟩
    · exact h x hl (hu.trans_le (min_le_left v z)) k hk

/-- Discrepancy of a finite real factorial comparison against the last quotient class. -/
def floorClassDifference {ι : Type*} (s : Finset ι) (w a : ι → ℝ) (q : ℕ) (t : ℝ) : ℝ :=
  (if q∣⌊t⌋₊+1 then 1 else 0) - ∑ i ∈ s, w i*(⌊a i*t⌋:ℝ)

/-- Each comparison at period at least three misses a whole interval of positive ratios. -/
theorem floorClassDifference_interval {ι : Type*} (s : Finset ι) (w a : ι → ℝ)
    (ha : ∀ i ∈ s, 0<a i) {q : ℕ} (hq : 3≤q) :
    ∃ u v e : ℝ, 0<u ∧ u<v ∧ 0<e ∧ ∀ x : ℝ, u≤x → x<v → |floorClassDifference s w a q x|=e := by
  have hf := last_quotient_class_not_finite_real_floors s w a ha hq
  push Not at hf
  obtain ⟨t,ht,hh⟩ := hf
  obtain ⟨v,hv,h⟩ := floors_constant_to_right s a ha t
  let z := min v ((⌊t⌋₊:ℝ)+1)
  have hz : t<z := lt_min hv (Nat.lt_floor_add_one _)
  obtain ⟨u,hu,hu'⟩ := exists_between hz
  refine ⟨u,z,|floorClassDifference s w a q t|,ht.trans_lt hu,hu',abs_pos.mpr (sub_ne_zero.mpr hh),
    fun x hux hx => ?_⟩
  have ht' := hu.le.trans hux
  have hfloor : ⌊x⌋₊=⌊t⌋₊ := (Nat.floor_eq_iff (ht.trans ht')).mpr
    ⟨(Nat.floor_le ht).trans ht',hx.trans_le (min_le_right ..)⟩
  have hsum : ∑ i ∈ s, w i*(⌊a i*x⌋:ℝ)=∑ i ∈ s, w i*(⌊a i*t⌋:ℝ) := by
    refine sum_congr rfl fun i hi => ?_
    rw [h x ht' (hx.trans_le (min_le_left ..)) i hi]
  rw [floorClassDifference,floorClassDifference,hfloor,hsum]

/-- At every sufficiently large base a fixed relative interval of ordinary
primes supplies positive linear logarithmic discrepancy for the comparison. -/
theorem floorClassDifference_prime_mass {ι : Type*} (s : Finset ι) (w a : ι → ℝ)
    (ha : ∀ i ∈ s, 0<a i) {q : ℕ} (hq : 3≤q) :
    ∃ l r c : ℝ, 0<l ∧ l<r ∧ 0<c ∧ ∀ᶠ X : ℝ in atTop,
      c*X ≤ ∑ p ∈ _root_.RHTower.Sieve.primesIn (l*X) (r*X),
        Real.log p * |floorClassDifference s w a q (X/p)| := by
  obtain ⟨u,v,e,hu,huv,he,hw⟩ := floorClassDifference_interval s w a ha hq
  have hv := hu.trans huv
  have hlr := inv_lt_inv₀ hv hu |>.mpr huv
  have ht := ((_root_.RHTower.tendsto_chebyshevTheta_div (inv_pos.mpr hu)).sub
    (_root_.RHTower.tendsto_chebyshevTheta_div (inv_pos.mpr hv))).eventually_const_lt
      (show (u⁻¹-v⁻¹)/2<u⁻¹-v⁻¹ by linarith only [hlr])
  refine ⟨v⁻¹,u⁻¹,((u⁻¹-v⁻¹)/2)*e,inv_pos.mpr hv,hlr,mul_pos (half_pos (sub_pos.mpr hlr)) he,?_⟩
  filter_upwards [ht,eventually_gt_atTop (0:ℝ)] with X hX hx
  change (u⁻¹-v⁻¹)/2 < Chebyshev.theta (u⁻¹*X)/X-Chebyshev.theta (v⁻¹*X)/X at hX
  rw [← sub_div,lt_div_iff₀ hx,_root_.RHTower.Sieve.theta_sub_theta_eq_sum_primesIn
    (mul_le_mul_of_nonneg_right hlr.le hx.le)] at hX
  have hh (p : ℕ) (hp : p∈_root_.RHTower.Sieve.primesIn (v⁻¹*X) (u⁻¹*X)) :
      |floorClassDifference s w a q (X/p)|=e := by
    obtain ⟨hpr,hl,hr⟩ := _root_.RHTower.Sieve.mem_primesIn (mul_nonneg (inv_pos.mpr hv).le hx.le) hp
    have hpos : 0<(p:ℝ) := by exact_mod_cast hpr.pos
    rw [inv_mul_eq_div] at hl hr
    exact hw _ ((le_div_iff₀ hpos).mpr (by simpa only [mul_comm] using (le_div_iff₀ hu).mp hr))
      ((div_lt_iff₀ hpos).mpr (by simpa only [mul_comm] using (div_lt_iff₀ hv).mp hl))
  calc
    _ = ((u⁻¹-v⁻¹)/2*X)*e := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_right hX.le he.le).trans_eq (by
      rw [sum_mul]
      exact sum_congr rfl fun p hp => by rw [hh p hp])

end GaloisForLFunctions.ExceptionalLayerTheory
