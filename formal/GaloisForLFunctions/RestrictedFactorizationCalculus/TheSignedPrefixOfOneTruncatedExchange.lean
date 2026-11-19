import GaloisForLFunctions.RestrictedFactorizationCalculus.DetectingPowerBoundsByOneExchange
import GaloisForLFunctions.RestrictedFactorizationCalculus.ReversibleSwitchesOnPrimeRanges

/-!
# Uniform sharp truncation of one primitive exchange

Deleting finitely many primes costs a finite Euler product in the positive
power norm. With a bounded number of deleted primes the cost is uniform in
their size. Cutting off the external cofactor of a single exchange preserves
this uniformity at both endpoints.
-/

noncomputable section

open Finset Filter
open ArithmeticFunction hiding id
open scoped Classical ArithmeticFunction.Moebius
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.QuantitativeFactorizationMatching

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private def deletionFactor (θ : ℝ) (p : ℕ) := (1-(1/(p:ℝ))^θ)⁻¹

private theorem prime_contraction {θ : ℝ} (hθ : 0<θ) {p : ℕ} (hp : p.Prime) :
    (1/(p:ℝ))^θ < 1 := by
  have hp1 : (1:ℝ)<p := by exact_mod_cast hp.one_lt
  exact Real.rpow_lt_one (by positivity) ((div_lt_one (zero_lt_one.trans hp1)).2 hp1) hθ

private theorem one_deletion_bound {θ C : ℝ} (hθ : 0<θ) (hC : 0 ≤ C) {p Q : ℕ}
    (hp : p.Prime) (hnd : ¬p ∣ Q)
    (h : ∀ n : ℕ, |coprimeMoebiusSum Q n| ≤ C*(n:ℝ)^θ) (n : ℕ) :
    |coprimeMoebiusSum (p*Q) n| ≤ (C*deletionFactor θ p)*(n:ℝ)^θ := by
  let r := 1/(p:ℝ)
  let B := C*deletionFactor θ p
  have hgap : 0<1-r^θ := sub_pos.mpr (prime_contraction hθ hp)
  have hB : 0 ≤ B := mul_nonneg hC (inv_nonneg.mpr hgap.le)
  have hprice : B*(1-r^θ)=C := by dsimp only [B,r,deletionFactor]; rw [mul_assoc,inv_mul_cancel₀ hgap.ne',mul_one]
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n=0
    · subst n
      simp [coprimeMoebiusSum,Real.zero_rpow hθ.ne']
    have hn0 := Nat.pos_of_ne_zero hn
    have hnp : n/p<n := Nat.div_lt_self hn0 hp.one_lt
    have hp0 : (0:ℝ)<p := Nat.cast_pos.mpr hp.pos
    have hfloor : ((n/p:ℕ):ℝ) ≤ r*n := by
      rw [show r*(n:ℝ)=(n:ℝ)/p by dsimp only [r]; ring]
      exact (le_div_iff₀ hp0).2 (by exact_mod_cast Nat.div_mul_le_self n p)
    have hpow := Real.rpow_le_rpow (Nat.cast_nonneg _) hfloor hθ.le
    rw [Real.mul_rpow (by dsimp only [r]; positivity) (Nat.cast_nonneg _)] at hpow
    have hsmall := (ih _ hnp).trans (mul_le_mul_of_nonneg_left hpow hB)
    have he := coprimeMoebiusSum_prime_relation hp hnd n
    have split : coprimeMoebiusSum (p*Q) n=coprimeMoebiusSum Q n+coprimeMoebiusSum (p*Q) (n/p) := by
      linarith only [he]
    change |coprimeMoebiusSum (p*Q) n| ≤ B*(n:ℝ)^θ
    calc _ ≤ |coprimeMoebiusSum Q n|+|coprimeMoebiusSum (p*Q) (n/p)| := by rw [split]; exact abs_add_le ..
         _ ≤ _ := by
           have hb := congrArg (fun x : ℝ => x*(n:ℝ)^θ) hprice
           change |coprimeMoebiusSum (p*Q) (n/p)| ≤ B*(r^θ*(n:ℝ)^θ) at hsmall
           linarith only [h n,hsmall,hb]

/-- Quantitative deletion of an arbitrary finite set of primes at sharp
integer cutoffs. The multiplicative constant retains each prime separately. -/
theorem sharp_prime_deletion_bound {θ C : ℝ} (hθ : 0<θ) (hC : 0 ≤ C)
    (h : ∀ n : ℕ, |coprimeMoebiusSum 1 n| ≤ C*(n:ℝ)^θ)
    (S : Finset ℕ) (hS : ∀ p ∈ S,p.Prime) (n : ℕ) :
    |coprimeMoebiusSum (∏ p ∈ S,p) n| ≤
      (C*∏ p ∈ S,(1-(1/(p:ℝ))^θ)⁻¹)*(n:ℝ)^θ := by
  induction S using Finset.induction_on generalizing n with
  | empty => simpa using h n
  | @insert p S hp ih =>
    have hP := hS p (mem_insert_self ..)
    have hpr (q : ℕ) (hq : q ∈ S) := hS q (mem_insert_of_mem hq)
    have hQ : p.Coprime (∏ q ∈ S,q) := Nat.Coprime.prod_right
      (fun q hq => (Nat.coprime_primes hP (hpr q hq)).2 (fun he => hp (he ▸ hq)))
    have hcost : 0 ≤ C*∏ q ∈ S,deletionFactor θ q := mul_nonneg hC (prod_nonneg
      (fun q hq => inv_nonneg.mpr (sub_nonneg.mpr (prime_contraction hθ (hpr q hq)).le)))
    have hh := one_deletion_bound hθ hcost hP (hP.coprime_iff_not_dvd.mp hQ) (ih hpr) n
    rw [prod_insert hp,prod_insert hp]
    exact hh.trans_eq (by dsimp only [deletionFactor]; ring)

/-- When the number of prime factors is fixed, the power bound for all
coprime prefixes is uniform in both the modulus and the cutoff. -/
theorem uniform_coprime_power_bound {θ : ℝ} (hθ : 0<θ) (h : PrefixPower θ (coprimeMoebiusSum 1)) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ S : Finset ℕ, S.card ≤ k → (∀ p ∈ S,p.Prime) →
      ∀ n : ℕ, |coprimeMoebiusSum (∏ q ∈ S,q) n| ≤ C*(n:ℝ)^θ := by
  obtain ⟨A,hA,ha⟩ := h
  let K := deletionFactor θ 2
  have hsmall := prime_contraction hθ Nat.prime_two
  have hK : 1 ≤ K := by
    change 1 ≤ (1-(1/(2:ℝ))^θ)⁻¹
    rw [←one_div]
    exact (one_le_div (sub_pos.mpr hsmall)).2 (sub_le_self _ (Real.rpow_nonneg (by norm_num) θ))
  refine ⟨A*K^k,mul_nonneg hA (pow_nonneg (zero_le_one.trans hK) _),?_⟩
  intro S hk hP n
  have bound (p : ℕ) (hp : p ∈ S) : deletionFactor θ p ≤ K := by
    have hp2 : (2:ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
    have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ 1/(p:ℝ))
      (one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) hp2) hθ.le
    exact inv_anti₀ (sub_pos.mpr hsmall) (sub_le_sub_left hpow 1)
  have hprod : (∏ p ∈ S,deletionFactor θ p) ≤ K^k := by
    calc _ ≤ ∏ _p ∈ S,K := prod_le_prod
           (fun p hp => inv_nonneg.mpr (sub_nonneg.mpr (prime_contraction hθ (hP p hp)).le)) bound
         _ = K^S.card := prod_const _
         _ ≤ _ := pow_le_pow_right₀ hK hk
  exact (sharp_prime_deletion_bound hθ hA ha S hP n).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod hA) (Real.rpow_nonneg (Nat.cast_nonneg _) _))

/-- A primitive exchange changes one prime to two distinct primes. -/
structure PrimitiveExchange where
  p : ℕ
  q : ℕ
  r : ℕ
  prime_p : p.Prime
  prime_q : q.Prime
  prime_r : r.Prime
  lt : q<r

namespace PrimitiveExchange

def w (e : PrimitiveExchange) := e.q*e.r
def primes (e : PrimitiveExchange) : Finset ℕ := {e.p,e.q,e.r}
def modulus (e : PrimitiveExchange) := ∏ p ∈ e.primes,p

theorem primes_spec (e : PrimitiveExchange) : ∀ p ∈ e.primes,p.Prime := by
  intro p hp
  rcases (show p=e.p ∨ p=e.q ∨ p=e.r by simpa only [primes,mem_insert,mem_singleton] using hp) with h | h | h
  · exact h ▸ e.prime_p
  · exact h ▸ e.prime_q
  · exact h ▸ e.prime_r

theorem primitives (e : PrimitiveExchange) :
    e.p ∣ e.modulus ∧ e.w ∣ e.modulus ∧ μ e.p= -1 ∧ μ e.w=1 ∧ e.w ≠ e.p := by
  have hq : e.q ∣ e.modulus := dvd_prod_of_mem _ (by simp [primes])
  have hr : e.r ∣ e.modulus := dvd_prod_of_mem _ (by simp [primes])
  have hc := (Nat.coprime_primes e.prime_q e.prime_r).2 e.lt.ne
  have hw : μ e.w=1 := by
    rw [w,isMultiplicative_moebius.map_mul_of_coprime hc,moebius_apply_prime e.prime_q,moebius_apply_prime e.prime_r]
    decide
  have hp := moebius_apply_prime e.prime_p
  exact ⟨dvd_prod_of_mem _ (by simp [primes]),hc.mul_dvd_of_dvd_of_dvd hq hr,hp,hw,
    fun h => by rw [h] at hw; omega⟩

theorem modulus_sq (e : PrimitiveExchange) : Squarefree e.modulus := _root_.Sieve.prodDistinctPrimes_squarefree _ e.primes_spec

/-- Cut off the unchanged cofactor on both sides of the exchange. -/
def cofactors (e : PrimitiveExchange) (A B : ℕ) :=
  (Ioc A B).filter (fun c => Squarefree c ∧ e.modulus.Coprime c)

def row (e : PrimitiveExchange) (A B a : ℕ) := (e.cofactors A B).image (·*a)
def moved (e : PrimitiveExchange) (A B : ℕ) := e.row A B e.p ∪ e.row A B e.w

theorem rows_disjoint (e : PrimitiveExchange) (A B : ℕ) :
    Disjoint (e.row A B e.p) (e.row A B e.w) := by
  apply disjoint_left.mpr
  intro n hp hw
  obtain ⟨c,hc,hn⟩ := mem_image.mp hp
  obtain ⟨d,hd,hm⟩ := mem_image.mp hw
  have h {v t : ℕ} (hv : v ∣ e.modulus) (ht : t ∈ e.cofactors A B) :
      (t*v).gcd e.modulus=v := (Nat.Coprime.gcd_mul_left_cancel _ (mem_filter.mp ht).2.2.symm).trans (Nat.gcd_eq_left hv)
  have h₁ := h e.primitives.1 hc
  have h₂ := h e.primitives.2.1 hd
  rw [hn] at h₁
  rw [hm] at h₂
  exact e.primitives.2.2.2.2 (h₂.symm.trans h₁)

/-- Exact contribution of one truncated cofactor row. -/
private theorem row_prefix (e : PrimitiveExchange) (A B X d : ℕ) (hd : d ∣ e.modulus) (hd0 : 0<d) :
    ∑ n ∈ (e.row A B d).filter (· ≤ X),(μ n:ℝ) =
      (μ d:ℝ)*(coprimeMoebiusSum e.modulus (min B (X/d))-
        coprimeMoebiusSum e.modulus (min A (min B (X/d)))) := by
  let V := min B (X/d)
  let f := coprimeMoebiusIndicator e.modulus
  have he : ((e.row A B d).filter (· ≤ X))=
      (((Ioc A V).filter (fun c => Squarefree c ∧ e.modulus.Coprime c)).image (·*d)) := by
    ext n
    constructor
    · intro hn
      obtain ⟨hm,hX⟩ := mem_filter.mp hn
      obtain ⟨c,hc,rfl⟩ := mem_image.mp hm
      obtain ⟨hI,hs⟩ := mem_filter.mp hc
      exact mem_image.mpr ⟨c,mem_filter.mpr ⟨mem_Ioc.mpr ⟨(mem_Ioc.mp hI).1,
        le_min (mem_Ioc.mp hI).2 ((Nat.le_div_iff_mul_le hd0).2 hX)⟩,hs⟩,rfl⟩
    · intro hn
      obtain ⟨c,hc,rfl⟩ := mem_image.mp hn
      obtain ⟨hI,hs⟩ := mem_filter.mp hc
      obtain ⟨hl,hu⟩ := mem_Ioc.mp hI
      exact mem_filter.mpr ⟨mem_image.mpr ⟨c,mem_filter.mpr ⟨mem_Ioc.mpr ⟨hl,hu.trans (min_le_left ..)⟩,hs⟩,rfl⟩,
        (Nat.le_div_iff_mul_le hd0).1 (hu.trans (min_le_right ..))⟩
  have hinj : Function.Injective ((·*d) : ℕ → ℕ) := fun _ _ hh => Nat.eq_of_mul_eq_mul_right hd0 hh
  rw [he,sum_image hinj.injOn]
  have hsum : ∑ c ∈ (Ioc A V).filter (fun c => Squarefree c ∧ e.modulus.Coprime c),(μ (c*d):ℝ) =
      (μ d:ℝ)*∑ c ∈ Ioc A V,f c := by
    rw [mul_sum,sum_filter]
    apply sum_congr rfl
    intro c _
    dsimp only [f,coprimeMoebiusIndicator]
    by_cases hc : e.modulus.Coprime c
    · rw [if_pos hc]
      by_cases hsq : Squarefree c
      · rw [if_pos ⟨hsq,hc⟩,isMultiplicative_moebius.map_mul_of_coprime (Nat.Coprime.coprime_dvd_right hd hc.symm),
          Int.cast_mul,mul_comm (μ c:ℝ)]
      · rw [if_neg (fun h => hsq h.1),moebius_eq_zero_of_not_squarefree hsq,Int.cast_zero,mul_zero]
    · rw [if_neg hc,if_neg (fun h => hc h.2),mul_zero]
  rw [hsum]
  congr 1
  have hi : Ioc A V=Icc 1 V \ Icc 1 (min A V) := by
    ext c
    simp only [mem_Ioc,Finset.mem_sdiff,mem_Icc,le_min_iff]
    omega
  have hs : Icc 1 (min A V) ⊆ Icc 1 V := Icc_subset_Icc le_rfl (min_le_right ..)
  rw [hi,sum_sdiff_eq_sub hs]
  rfl

/-- Throughout this cofactor interval the signed mass is exactly a
difference of two sharp, clipped coprime prefixes. -/
theorem moved_prefix (e : PrimitiveExchange) (A B X : ℕ) :
    ∑ n ∈ (e.moved A B).filter (· ≤ X),(μ n:ℝ) =
      (coprimeMoebiusSum e.modulus (min B (X/e.w))-coprimeMoebiusSum e.modulus (min A (min B (X/e.w)))) -
      (coprimeMoebiusSum e.modulus (min B (X/e.p))-coprimeMoebiusSum e.modulus (min A (min B (X/e.p)))) := by
  rw [moved,filter_union,sum_union ((e.rows_disjoint A B).mono (filter_subset ..) (filter_subset ..)),
    row_prefix e A B X e.p e.primitives.1 e.prime_p.pos,
    row_prefix e A B X e.w e.primitives.2.1 (Nat.mul_pos e.prime_q.pos e.prime_r.pos),
    e.primitives.2.2.1,e.primitives.2.2.2.1]
  push_cast
  ring

/-- In the interior of the stage, neither quotient hits a truncation and
the unrestricted sharp dilation difference is recovered exactly. -/
theorem interior_moved_prefix (e : PrimitiveExchange) {A B X : ℕ}
    (hl : A ≤ X/e.p ∧ A ≤ X/e.w) (hu : X/e.p ≤ B ∧ X/e.w ≤ B) :
    ∑ n ∈ (e.moved A B).filter (· ≤ X),(μ n:ℝ) =
      dilationDifference e.w e.p (coprimeMoebiusSum e.modulus) X := by
  rw [e.moved_prefix,min_eq_right hu.1,min_eq_right hu.2,min_eq_left hl.1,min_eq_left hl.2]
  dsimp only [dilationDifference]
  ring

/-- Uniform bound for every cofactor interval, including cutoffs at which
only one of the two exchanged rows has started. -/
theorem moved_power_bound {θ : ℝ} (hθ : 0<θ) (h : PrefixPower θ (coprimeMoebiusSum 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ e : PrimitiveExchange, ∀ A B X : ℕ,
      |∑ n ∈ (e.moved A B).filter (· ≤ X),(μ n:ℝ)| ≤ C*(X:ℝ)^θ := by
  obtain ⟨K,hK,hbound⟩ := uniform_coprime_power_bound hθ h 3
  refine ⟨4*K,by positivity,fun e A B X => ?_⟩
  have hcard : e.primes.card ≤ 3 := by
    apply (card_insert_le ..).trans
    have hh := card_insert_le e.q ({e.r}:Finset ℕ)
    simp only [card_singleton] at hh
    omega
  have bound {a : ℕ} (ha : a ≤ X) : |coprimeMoebiusSum e.modulus a| ≤ K*(X:ℝ)^θ :=
    (hbound e.primes hcard e.primes_spec a).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr ha) hθ.le) hK)
  have hmin (d : ℕ) : min B (X/d) ≤ X := (min_le_right ..).trans (Nat.div_le_self ..)
  have two (d : ℕ) : |coprimeMoebiusSum e.modulus (min B (X/d))-
      coprimeMoebiusSum e.modulus (min A (min B (X/d)))| ≤ 2*K*(X:ℝ)^θ := by
    apply (abs_sub ..).trans
    linarith only [bound (hmin d),bound ((min_le_right ..).trans (hmin d))]
  rw [e.moved_prefix]
  apply (abs_sub ..).trans
  linarith only [two e.w,two e.p]

/-- Actual exchange on one cofactor interval. The row of the given integer
determines its inverse. -/
def act (e : PrimitiveExchange) (A B n : ℕ) :=
  if n ∈ e.row A B e.p then n/e.p*e.w else if n ∈ e.row A B e.w then n/e.w*e.p else n

theorem act_rows (e : PrimitiveExchange) {A B c : ℕ} (hc : c ∈ e.cofactors A B) :
    e.act A B (c*e.p)=c*e.w ∧ e.act A B (c*e.w)=c*e.p := by
  have hp : c*e.p ∈ e.row A B e.p := mem_image_of_mem _ hc
  have hw : c*e.w ∈ e.row A B e.w := mem_image_of_mem _ hc
  have hno : c*e.w ∉ e.row A B e.p := fun hn => disjoint_left.mp (e.rows_disjoint A B) hn hw
  exact ⟨by rw [act,if_pos hp,Nat.mul_div_cancel _ e.prime_p.pos],
    by rw [act,if_neg hno,if_pos hw,Nat.mul_div_cancel _ (Nat.mul_pos e.prime_q.pos e.prime_r.pos)]⟩

theorem act_fixed_off (e : PrimitiveExchange) {A B n : ℕ} (h : n ∉ e.moved A B) : e.act A B n=n := by
  rw [act,if_neg (fun h' => h (mem_union_left _ h')),if_neg (fun h' => h (mem_union_right _ h'))]

private theorem actual_edge (e : PrimitiveExchange) {A B c : ℕ} (hc : c ∈ e.cofactors A B) :
    GlobalDyadicOneTwoRel (c*e.p) (c*e.w) := by
  obtain ⟨_,hs,hQ⟩ := mem_filter.mp hc
  have hp := Nat.Coprime.coprime_dvd_right e.primitives.1 hQ.symm
  have hw := Nat.Coprime.coprime_dvd_right e.primitives.2.1 hQ.symm
  refine ⟨Nat.squarefree_mul_iff.mpr ⟨hp,hs,Irreducible.squarefree e.prime_p⟩,
    Nat.squarefree_mul_iff.mpr ⟨hw,hs,e.modulus_sq.squarefree_of_dvd e.primitives.2.1⟩,?_,
    c,e.p,e.q,e.r,e.prime_p,e.prime_q,e.prime_r,e.lt,Or.inl ⟨rfl,rfl⟩⟩
  rw [isMultiplicative_moebius.map_mul_of_coprime hp,isMultiplicative_moebius.map_mul_of_coprime hw,
    e.primitives.2.2.1,e.primitives.2.2.2.1]
  ring

/-- A moved endpoint always stays in this same cofactor interval. -/
theorem act_on (e : PrimitiveExchange) {A B n : ℕ} (hn : n ∈ e.moved A B) :
    e.act A B n ∈ e.moved A B ∧ e.act A B (e.act A B n)=n ∧
      GlobalDyadicOneTwoRel n (e.act A B n) := by
  rcases mem_union.mp hn with hp | hw
  · obtain ⟨c,hc,rfl⟩ := mem_image.mp hp
    rw [(e.act_rows hc).1]
    exact ⟨mem_union_right _ (mem_image_of_mem _ hc),(e.act_rows hc).2,e.actual_edge hc⟩
  · obtain ⟨c,hc,rfl⟩ := mem_image.mp hw
    rw [(e.act_rows hc).2]
    exact ⟨mem_union_left _ (mem_image_of_mem _ hc),(e.act_rows hc).1,(e.actual_edge hc).symm⟩

theorem moved_bounds (e : PrimitiveExchange) {A B n : ℕ} (hn : n ∈ e.moved A B) :
    A*min e.p e.w<n ∧ n ≤ B*max e.p e.w := by
  have rowBound {d : ℕ} (hd0 : 0<d) (hl : min e.p e.w ≤ d) (hu : d ≤ max e.p e.w) (h : n ∈ e.row A B d) :
      A*min e.p e.w<n ∧ n ≤ B*max e.p e.w := by
    obtain ⟨c,hc,rfl⟩ := mem_image.mp h
    obtain ⟨hA,hB⟩ := mem_Ioc.mp (mem_filter.mp hc).1
    exact ⟨(Nat.mul_le_mul_left A hl).trans_lt (Nat.mul_lt_mul_of_pos_right hA hd0),Nat.mul_le_mul hB hu⟩
  exact (mem_union.mp hn).elim (rowBound e.prime_p.pos (min_le_left ..) (le_max_left ..))
    (rowBound (Nat.mul_pos e.prime_q.pos e.prime_r.pos) (min_le_right ..) (le_max_right ..))

theorem moved_count (e : PrimitiveExchange) (A B X : ℕ) :
    ((e.moved A B).filter (· ≤ X)).card ≤ X/e.p+X/e.w := by
  have rowCount (d : ℕ) (hd : 0<d) : ((e.row A B d).filter (· ≤ X)).card ≤ X/d := by
    have hh : ((e.row A B d).filter (· ≤ X)).card ≤ (Icc 1 (X/d)).card := by
      apply card_le_card_of_injOn (fun n => n/d)
      · intro n hn
        obtain ⟨h,hX⟩ := mem_filter.mp hn
        obtain ⟨c,hc,rfl⟩ := mem_image.mp h
        rw [Nat.mul_div_cancel _ hd]
        exact mem_Icc.mpr ⟨(Nat.zero_le A).trans_lt (mem_Ioc.mp (mem_filter.mp hc).1).1,
          (Nat.le_div_iff_mul_le hd).2 hX⟩
      · intro n hn m hm he
        obtain ⟨c,_,rfl⟩ := mem_image.mp (mem_filter.mp hn).1
        obtain ⟨t,_,rfl⟩ := mem_image.mp (mem_filter.mp hm).1
        rw [Nat.mul_div_cancel _ hd,Nat.mul_div_cancel _ hd] at he
        rw [he]
    simpa only [Nat.card_Icc,Nat.add_sub_cancel] using hh
  rw [moved,filter_union]
  exact (card_union_le ..).trans (Nat.add_le_add (rowCount _ e.prime_p.pos)
    (rowCount _ (Nat.mul_pos e.prime_q.pos e.prime_r.pos)))

theorem act_distance (e : PrimitiveExchange) {J : ℕ}
    (h₁ : |(e.p:ℝ)-e.w| ≤ (e.p:ℝ)/J) (h₂ : |(e.p:ℝ)-e.w| ≤ (e.w:ℝ)/J)
    (A B n : ℕ) : |(e.act A B n:ℝ)-n| ≤ (n:ℝ)/J := by
  have scale {a b c : ℕ} (h : |(a:ℝ)-b| ≤ (b:ℝ)/J) :
      |((c*a:ℕ):ℝ)-(c*b:ℕ)| ≤ ((c*b:ℕ):ℝ)/J := by
    push_cast
    rw [←mul_sub,abs_mul,abs_of_nonneg (Nat.cast_nonneg c),mul_div_assoc]
    exact mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)
  by_cases h : n ∈ e.moved A B
  · rcases mem_union.mp h with hn | hn
    · obtain ⟨c,hc,rfl⟩ := mem_image.mp hn
      rw [(e.act_rows hc).1]; exact scale (by rwa [abs_sub_comm])
    · obtain ⟨c,hc,rfl⟩ := mem_image.mp hn
      rw [(e.act_rows hc).2]; exact scale h₂
  · rw [e.act_fixed_off h,sub_self,abs_zero]; positivity

end PrimitiveExchange
/-- A single sufficiently high primitive exchange can be arbitrarily short
relative to either endpoint. -/
theorem exists_short_primitive_exchange_above (J V : ℕ) (hJ : 0<J) :
    ∃ e : PrimitiveExchange, V<e.p ∧ V<e.q ∧ V<e.r ∧
      |(e.p:ℝ)-e.w| ≤ (e.p:ℝ)/J ∧ |(e.p:ℝ)-e.w| ≤ (e.w:ℝ)/J := by
  obtain ⟨H,hH⟩ := eventually_atTop.mp (eventually_bandReady J hJ)
  let k := max H V
  have ready := hH k (le_max_left ..)
  have many : (switchProducts k).Nonempty := by
    by_contra hn
    have mass := ready.2
    rw [not_nonempty_iff_eq_empty.mp hn,image_empty,sum_empty] at mass
    norm_num at mass
  obtain ⟨w,hw⟩ := many
  obtain ⟨hp,⟨q,hq,r,hr,hqr,hform⟩,hnear,hnear'⟩ := ready.1.2 w hw
  have high {v : ℕ} (hv : v ∈ switchPrimes k) : V<v :=
    (le_max_right H V).trans_lt ((Nat.lt_two_pow_self (n := k)).trans (mem_switchPrimes.mp hv).2.1)
  let e : PrimitiveExchange := ⟨bandPartner J k w,q,r,(mem_switchPrimes.mp hp).1,
    (mem_switchPrimes.mp hq).1,(mem_switchPrimes.mp hr).1,hqr⟩
  have he : e.w=w := hform.symm
  exact ⟨e,high hp,high hq,high hr,
    he ▸ hnear',he ▸ hnear⟩

/-- A single sufficiently high primitive exchange can be arbitrarily short
relative to either endpoint. -/
theorem exists_short_primitive_exchange (J V : ℕ) (hJ : 0<J) :
    ∃ e : PrimitiveExchange, V<e.p ∧ V<e.w ∧
      |(e.p:ℝ)-e.w| ≤ (e.p:ℝ)/J ∧ |(e.p:ℝ)-e.w| ≤ (e.w:ℝ)/J := by
  obtain ⟨e,p,q,_,near,near'⟩ := exists_short_primitive_exchange_above J V hJ
  exact ⟨e,p,q.trans_le (Nat.le_mul_of_pos_right e.q e.prime_r.pos),near,near'⟩

/-- On the complete cofactor line, this one pair already has the entire
Mertens power spectrum. -/
theorem PrimitiveExchange.difference_power_iff (e : PrimitiveExchange) {θ : ℝ} (hθ : 0<θ) :
    PrefixPower θ (dilationDifference e.w e.p (coprimeMoebiusSum e.modulus)) ↔
      PrefixPower θ (coprimeMoebiusSum 1) := by
  have hw : 0<e.w := Nat.mul_pos e.prime_q.pos e.prime_r.pos
  have h0 : coprimeMoebiusSum e.modulus 0=0 := by simp [coprimeMoebiusSum]
  apply Iff.trans _ (coprime_prefix_preserves_every_power e.modulus_sq hθ)
  rcases lt_or_gt_of_ne e.primitives.2.2.2.2 with h | h
  · exact prefixPower_dilationDifference_iff hw h hθ _ h0
  · have swap {a b : ℕ} {F : ℕ → ℝ} (h : PrefixPower θ (dilationDifference a b F)) :
        PrefixPower θ (dilationDifference b a F) := by
      obtain ⟨C,hC,h⟩ := h
      exact ⟨C,hC,fun n => (abs_sub_comm (F (n/b)) _).le.trans (h n)⟩
    exact (Iff.intro swap swap).trans (prefixPower_dilationDifference_iff e.prime_p.pos h hθ _ h0)

#print axioms sharp_prime_deletion_bound
#print axioms PrimitiveExchange.moved_power_bound
#print axioms exists_short_primitive_exchange
#print axioms PrimitiveExchange.difference_power_iff

end GaloisForLFunctions.RestrictedFactorizationCalculus

