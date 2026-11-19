import GaloisForLFunctions.RestrictedFactorizationCalculus.DensityOneForRestrictedPrimeExchanges
import GaloisForLFunctions.BezoutValuationIncidence.CoprimeSquarefreeDensityAndMobiusDilationMeans
import GaloisForLFunctions.RHTower.Sieve.MainTerm
import GaloisForLFunctions.RHTower.PrimeSquareMobiusDensityFracture

/-!
# The parity cost of restricting only the smaller split prime

The Möbius sign of the gcd with a fixed squarefree modulus has a positive
mean on squarefree integers. A short exchange flips this second sign exactly
when the smaller split prime divides the modulus. Consequently a positive
fraction of the edges of a density-one matching must escape every finite
set of smaller split primes.
-/

noncomputable section

open Finset Filter
open ArithmeticFunction hiding id
open scoped Classical Topology ArithmeticFunction.Moebius
open GaloisForLFunctions.QuantitativeFactorizationMatching GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private def localPrefix (Q X : ℕ) := ∑ n ∈ squarefreeOf (Icc 1 X),(μ (n.gcd Q):ℝ)

private theorem squarefree_gcd_row {Q d : ℕ} (hsQ : Squarefree Q) (hd : d ∈ Q.divisors) (X : ℕ) :
    (((squarefreeOf (Icc 1 X)).filter (fun n => n.gcd Q=d)).card:ℝ) = coprimeSquarefreeCount Q (X/d) := by
  let f (n : ℕ) : ℝ := if Squarefree n ∧ n.gcd Q=d then 1 else 0
  have hdQ := Nat.dvd_of_mem_divisors hd
  have hds := hsQ.squarefree_of_dvd hdQ
  have hc (a : ℕ) : (Squarefree (d*a) ∧ (d*a).gcd Q=d) ↔ Q.Coprime a ∧ Squarefree a := by
    constructor
    · rintro ⟨hs,he⟩
      obtain ⟨hda,_,ha⟩ := Nat.squarefree_mul_iff.mp hs
      have hh : a.gcd ((d*a).gcd Q)=a.gcd Q := by rw [←Nat.gcd_assoc,Nat.gcd_eq_left (Nat.dvd_mul_left a d)]
      rw [he] at hh
      exact ⟨(show a.Coprime Q from hh.symm.trans hda.symm.gcd_eq_one).symm,ha⟩
    · rintro ⟨h,ha⟩
      exact ⟨Nat.squarefree_mul_iff.mpr ⟨Nat.Coprime.coprime_dvd_left hdQ h,hds,ha⟩,
        (Nat.Coprime.gcd_mul_right_cancel d h.symm).trans (Nat.gcd_eq_left hdQ)⟩
  have hin : (squarefreeOf (Icc 1 X)).filter (fun n => n.gcd Q=d) =
      (Icc 1 X).filter (fun n => Squarefree n ∧ n.gcd Q=d) := by ext n; simp [squarefreeOf,and_assoc]
  rw [hin]
  have hsum : (∑ n ∈ (Icc 1 X).filter (d ∣ ·),f n)=(∑ n ∈ Icc 1 X,f n) := by
    apply sum_subset (filter_subset _ _)
    intro n hn hnot
    apply if_neg
    exact fun h => hnot (mem_filter.mpr ⟨hn,h.2 ▸ Nat.gcd_dvd_left n Q⟩)
  have he : (((Icc 1 X).filter (fun n => Squarefree n ∧ n.gcd Q=d)).card:ℝ) =
      ∑ n ∈ Icc 1 X,f n := by rw [←sum_filter]; simp
  rw [he,←hsum,RHTower.sum_Icc_dvd_reindex d X (Nat.pos_of_mem_divisors hd),coprimeSquarefreeCount]
  apply sum_congr rfl
  intro a _
  dsimp only [f,coprimeSquarefreeIndicator]
  rw [propext (hc a)]
  by_cases h : Q.Coprime a <;> simp only [h,true_and,false_and,if_false,if_true]
  by_cases hs : Squarefree a
  · rw [if_pos hs]
    rcases moebius_eq_one_or_neg_one_of_squarefree hs with hm | hm <;> rw [hm] <;> norm_num
  · rw [if_neg hs,moebius_eq_zero_of_not_squarefree hs]; norm_num

private theorem local_prefix_expansion {Q : ℕ} (hQ : Squarefree Q) (X : ℕ) :
    localPrefix Q X = ∑ d ∈ Q.divisors,(μ d:ℝ)*coprimeSquarefreeCount Q (X/d) := by
  let S := squarefreeOf (Icc 1 X)
  have maps (n : ℕ) (_ : n ∈ S) : n.gcd Q ∈ Q.divisors :=
    Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right ..,hQ.ne_zero⟩
  rw [localPrefix,←sum_fiberwise_of_maps_to maps (fun n => (μ (n.gcd Q):ℝ))]
  apply sum_congr rfl
  intro d hd
  calc _ = ∑ _n ∈ S.filter (fun n => n.gcd Q=d),(μ d:ℝ) :=
             sum_congr rfl (fun n h => by rw [(mem_filter.mp h).2])
       _ = _ := by rw [sum_const,nsmul_eq_mul,squarefree_gcd_row hQ hd,mul_comm]

/-- Mean of the second sign among all integer locations, counting only
squarefree vertices. -/
def smallerPrimeBias (Q : ℕ) := coprimeSquarefreeDensity Q *
  (∑ d ∈ Q.divisors,(μ d:ℝ)/d)

private theorem local_mean {Q : ℕ} (hQ : Squarefree Q) :
    Tendsto (fun x : ℝ => localPrefix Q ⌊x⌋₊/x) atTop (𝓝 (smallerPrimeBias Q)) := by
  have hr (d : ℕ) (hd : d ∈ Q.divisors) :
      Tendsto (fun x : ℝ => (μ d:ℝ)/d * coprimeSquarefreeMean Q (x/d))
        atTop (𝓝 ((μ d:ℝ)/d*coprimeSquarefreeDensity Q)) :=
    ((tendsto_coprimeSquarefreeMean_of_squarefree Q hQ).comp
      (tendsto_id.atTop_div_const (by exact_mod_cast Nat.pos_of_mem_divisors hd : (0:ℝ)<d))).const_mul _
  have hsum := tendsto_finset_sum _ hr
  rw [←sum_mul,mul_comm] at hsum
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  rw [local_prefix_expansion hQ,sum_div]
  apply sum_congr rfl
  intro d hd
  have hd0 : (0:ℝ)<d := by exact_mod_cast Nat.pos_of_mem_divisors hd
  rw [coprimeSquarefreeMean,Nat.floor_div_natCast]
  field_simp [hd0.ne',hx.ne']

/-- The limiting second-sign imbalance on the sharp natural octave. -/
theorem smaller_prime_bias_on_octaves {Q : ℕ} (hQ : Squarefree Q) :
    Tendsto (fun X : ℕ => (∑ n ∈ squarefreeOf (Ioc X (2*X)),(μ (n.gcd Q):ℝ))/X)
      atTop (𝓝 (smallerPrimeBias Q)) := by
  have ht := (local_mean hQ).comp tendsto_natCast_atTop_atTop
  have htwo : Tendsto (fun X : ℕ => 2*(X:ℝ)) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (by norm_num : (0:ℝ)<2)).mpr tendsto_natCast_atTop_atTop
  have h2 := ((local_mean hQ).comp htwo).const_mul 2
  have h := h2.sub ht
  rw [show 2*smallerPrimeBias Q-smallerPrimeBias Q=smallerPrimeBias Q by ring] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with X hX
  have hx : (0:ℝ)<X := by exact_mod_cast hX
  have he : squarefreeOf (Icc 1 (2*X))=squarefreeOf (Icc 1 X) ∪ squarefreeOf (Ioc X (2*X)) := by
    ext n
    simp only [squarefreeOf,mem_filter,mem_union,mem_Icc,mem_Ioc]
    by_cases hn : Squarefree n <;> simp only [hn,and_true,and_false,false_or] <;> omega
  have hd : Disjoint (squarefreeOf (Icc 1 X)) (squarefreeOf (Ioc X (2*X))) :=
    disjoint_left.mpr (fun n hv hw => (mem_Ioc.mp (mem_filter.mp hw).1).1.not_ge (mem_Icc.mp (mem_filter.mp hv).1).2)
  change 2*(localPrefix Q ⌊2*(X:ℝ)⌋₊/(2*(X:ℝ)))-localPrefix Q ⌊(X:ℝ)⌋₊/X=_
  rw [show 2*(X:ℝ)=((2*X:ℕ):ℝ) by push_cast; rfl,Nat.floor_natCast,Nat.floor_natCast,
    localPrefix Q (2*X),localPrefix Q X,he,sum_union hd,Nat.cast_mul,Nat.cast_ofNat]
  field_simp [hx.ne']
  ring


/-- The product formula is strictly positive even if all other prime
factors of the endpoints are allowed to vary without bound. -/
theorem smallerPrimeBias_eq {Q : ℕ} (hQ : Squarefree Q) :
    smallerPrimeBias Q = RHTower.Sieve.squarefreeDensity *
      ∏ p ∈ Q.primeFactors, ((p:ℝ)-1)/(p+1) := by
  rw [smallerPrimeBias,coprimeSquarefreeDensity,RHTower.Sieve.sum_divisors_moebius_div_eq_prod hQ,
    mul_assoc,←prod_mul_distrib]
  congr 1
  apply prod_congr rfl
  intro p hp
  have h0 : (0:ℝ)<p := Nat.cast_pos.mpr (Nat.prime_of_mem_primeFactors hp).pos
  field_simp
  ring

/-- The smaller split prime is one of the prescribed primes. -/
def usesSmallSplit (S : Finset ℕ) (a b : ℕ) :=
  ∃ c p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ q<r ∧ q ∈ S ∧
    ((a=c*p ∧ b=c*(q*r)) ∨ (b=c*p ∧ a=c*(q*r)))

private theorem gcd_charge_mul_prime {Q c q : ℕ} (hq : q.Prime) (hcop : c.Coprime q) (hd : q ∣ Q) :
    μ ((c*q).gcd Q)= -μ (c.gcd Q) := by
  have he : Q/q*q=Q := Nat.div_mul_cancel hd
  have hc : c.gcd (Q/q)=c.gcd Q := by
    calc _ = (Q/q).gcd c := Nat.gcd_comm ..
         _ = ((Q/q)*q).gcd c := (Nat.Coprime.gcd_mul_right_cancel _ hcop.symm).symm
         _ = _ := by rw [he,Nat.gcd_comm]
  have hg : (c*q).gcd Q=c.gcd Q*q := by
    calc _ = (c*q).gcd ((Q/q)*q) := by rw [he]
         _ = c.gcd (Q/q)*q := Nat.gcd_mul_right ..
         _ = _ := by rw [hc]
  rw [hg,isMultiplicative_moebius.map_mul_of_coprime
    (Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left c Q) hcop),moebius_apply_prime hq,mul_neg_one]

private theorem short_edge_charge {S : Finset ℕ} (hS : ∀ s ∈ S,Nat.Prime s)
    {Y X a b : ℕ} (hY : ∀ s ∈ S,s ≤ Y) (hY1 : 1 ≤ Y) (ha : a ∈ Ioc X (2*X)) (hb : b ∈ Ioc X (2*X))
    (hsqa : Squarefree a) (hsqb : Squarefree b) (hshort : |(a:ℝ)-b| *(Y:ℝ)^2 ≤ X)
    (he : usesSmallSplit S a b) :
    let Q := ∏ s ∈ S,s
    μ (a.gcd Q) = -μ (b.gcd Q) := by
  let Q := ∏ s ∈ S,s
  obtain ⟨c,p,q,r,hp,hq,hr,hqr,hqs,hor⟩ := he
  have hpne : p ≠ q*r := fun h => Nat.not_prime_mul hq.one_lt.ne' hr.one_lt.ne' (h ▸ hp)
  have hdiff : 1 ≤ |(p:ℝ)-(q*r:ℕ)| := by
    rcases lt_or_gt_of_ne hpne with h | h
    · have hv : (p:ℝ)+1 ≤ (q*r:ℕ) := by exact_mod_cast Nat.succ_le_of_lt h
      linarith only [hv,neg_le_abs ((p:ℝ)-(q*r:ℕ))]
    · have hv : ((q*r:ℕ):ℝ)+1 ≤ p := by exact_mod_cast Nat.succ_le_of_lt h
      linarith only [hv,le_abs_self ((p:ℝ)-(q*r:ℕ))]
  have cost : |(c:ℝ)*p-c*(q*r:ℕ)| *(Y:ℝ)^2 ≤ X := by
    rcases hor with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · push_cast at hshort ⊢; exact hshort
    · rw [abs_sub_comm] at hshort; push_cast at hshort ⊢; exact hshort
  rw [←mul_sub,abs_mul,abs_of_nonneg (Nat.cast_nonneg _)] at cost
  have hcap : c*Y^2 ≤ X := by
    exact_mod_cast (mul_le_mul_of_nonneg_right (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hdiff (Nat.cast_nonneg (α := ℝ) c)) (sq_nonneg (Y:ℝ))).trans cost
  have ends : X<c*p ∧ X<c*(q*r) ∧ Squarefree (c*(q*r)) := by
    rcases hor with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨(mem_Ioc.mp ha).1,(mem_Ioc.mp hb).1,hsqb⟩
    · exact ⟨(mem_Ioc.mp hb).1,(mem_Ioc.mp ha).1,hsqa⟩
  have high (u : ℕ) (hu : X<c*u) : Y^2 < u := by
    by_contra! h
    exact hu.not_ge ((Nat.mul_le_mul_left c h).trans hcap)
  have hpY : Y<p := (by simpa only [pow_one] using Nat.pow_le_pow_right hY1 (by decide : 1 ≤ 2) : Y ≤ Y^2).trans_lt
    (high p ends.1)
  have hrY : Y<r := by
    by_contra! h
    exact (high _ ends.2.1).not_ge (by rw [pow_two]; exact Nat.mul_le_mul (hqr.le.trans h) h)
  have prime_free {s : ℕ} (hs : s.Prime) (hh : Y<s) : s.Coprime Q := Nat.Coprime.prod_right
    (fun t ht => (Nat.coprime_primes hs (hS t ht)).2 (fun he => (he ▸ hh).not_ge (hY t ht)))
  have hpQ : (c*p).gcd Q=c.gcd Q := Nat.Coprime.gcd_mul_right_cancel _ (prime_free hp hpY)
  have hrQ : (c*(q*r)).gcd Q=(c*q).gcd Q := by
    rw [←Nat.mul_assoc]
    exact Nat.Coprime.gcd_mul_right_cancel _ (prime_free hr hrY)
  have hc := Nat.Coprime.coprime_dvd_right (Nat.dvd_mul_right q r) (Nat.squarefree_mul_iff.mp ends.2.2).1
  have hμ := gcd_charge_mul_prime hq hc (show q ∣ Q from dvd_prod_of_mem _ hqs)
  rcases hor with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> dsimp only <;> rw [hpQ,hrQ,hμ] <;> simp

private theorem paired_charge {S : Finset ℕ} (hS : ∀ p ∈ S,Nat.Prime p) {Y X : ℕ}
    (hY : ∀ p ∈ S,p ≤ Y) (hY1 : 1 ≤ Y)
    (M : OppositeParityMatching GlobalDyadicOneTwoRel (Ioc X (2*X)))
    (hshort : ∀ n ∈ M.sources, |(M.partner n:ℝ)-n| *(Y:ℝ)^2 ≤ X) :
    let Q := ∏ p ∈ S,p
    (∑ n ∈ squarefreeOf (Ioc X (2*X)), (μ (n.gcd Q):ℝ)) ≤
      (M.unmatchedSet.card:ℝ)+2*((M.sources.filter (fun n => ¬usesSmallSplit S n (M.partner n))).card:ℝ) := by
  let Q := ∏ p ∈ S,p
  let f := fun n : ℕ => (μ (n.gcd Q):ℝ)
  let O := M.sources.filter (fun n => ¬usesSmallSplit S n (M.partner n))
  have hf (n : ℕ) : f n ≤ 1 := (le_abs_self _).trans (by exact_mod_cast
    ArithmeticFunction.abs_moebius_le_one (n := n.gcd Q))
  have hsum : ∑ n ∈ M.matchedSet,f n=∑ n ∈ M.sources,(f n+f (M.partner n)) := by
    have hdis : Disjoint M.sources M.targets :=
      (disjoint_posParity_negParity _).mono M.sources_subset M.targets_subset
    rw [OppositeParityMatching.matchedSet,sum_union hdis,OppositeParityMatching.targets,
      sum_image M.injOn, sum_add_distrib]
  have hbound : ∑ n ∈ M.sources,(f n+f (M.partner n)) ≤ ∑ _n ∈ O,(2:ℝ) := by
    rw [sum_filter]
    apply sum_le_sum
    intro n hn
    by_cases h : usesSmallSplit S n (M.partner n)
    · rw [if_neg (not_not.mpr h)]
      have he := M.adj n hn
      have hd := short_edge_charge hS hY hY1 (mem_filter.mp (M.sources_subset hn)).1
        (mem_filter.mp (M.partner_mem n hn)).1 he.1 he.2.1
        (by rw [abs_sub_comm]; exact hshort n hn) h
      change (μ (n.gcd Q):ℝ)+(μ ((M.partner n).gcd Q):ℝ) ≤ 0
      rw [hd,Int.cast_neg]; linarith
    · rw [if_pos h]; linarith only [hf n,hf (M.partner n)]
  have hU : ∑ n ∈ M.unmatchedSet,f n ≤ (M.unmatchedSet.card:ℝ) :=
    (sum_le_sum (fun n (_ : n ∈ M.unmatchedSet) => hf n)).trans_eq (by simp)
  have hb : (∑ n ∈ M.matchedSet,f n) ≤ 2*O.card := hsum ▸ hbound.trans_eq (by simp [mul_comm])
  have htot := sum_sdiff_eq_sub (f := f) M.matchedSet_subset
  change (∑ n ∈ M.unmatchedSet,f n)=(∑ n ∈ squarefreeOf (Ioc X (2*X)),f n)-∑ n ∈ M.matchedSet,f n at htot
  dsimp only
  linarith only [htot,hU,hb]

/-- A fixed finite set of smaller split primes can pay only a bounded
fraction of the octave. Every remaining pair outside that set can absorb at
most two units of the second-sign surplus. -/
theorem smaller_primes_must_escape (S : Finset ℕ) (hS : ∀ p ∈ S,Nat.Prime p)
    (Y : ℕ) (hY1 : 1 ≤ Y) (hY : ∀ p ∈ S,p ≤ Y) {ε : ℝ} (hε : 0<ε) :
    let Q := ∏ p ∈ S,p
    ∀ᶠ X : ℕ in atTop, ∀ M : OppositeParityMatching GlobalDyadicOneTwoRel (Ioc X (2*X)),
      (∀ n ∈ M.sources, |(M.partner n:ℝ)-n| *(Y:ℝ)^2 ≤ X) →
      (smallerPrimeBias Q-ε)*X ≤ (M.unmatchedSet.card:ℝ)+
        2*((M.sources.filter (fun n => ¬usesSmallSplit S n (M.partner n))).card:ℝ) := by
  let Q := ∏ p ∈ S,p
  have hs : Squarefree Q := _root_.Sieve.prodDistinctPrimes_squarefree S hS
  have hl := (smaller_prime_bias_on_octaves hs).eventually
    (lt_mem_nhds (show smallerPrimeBias Q-ε<smallerPrimeBias Q by linarith only [hε]))
  filter_upwards [hl,eventually_ge_atTop 1] with X hbound hX
  intro M hm
  exact ((lt_div_iff₀ (show (0:ℝ)<X by exact_mod_cast hX)).1 hbound).le.trans
    (paired_charge hS hY hY1 M hm)

end GaloisForLFunctions.RestrictedFactorizationCalculus
