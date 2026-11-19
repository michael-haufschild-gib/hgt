import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic
import GaloisForLFunctions.RHTower.PrimeWindowLogPowerCount

/-!
# The volumes and matching of the two prime-triple boxes

Coordinates are normalized by the cube root of the shared endpoint.
Reflection carries matched upper factors to lower factors whose product
stays above two thirds. A fixed closed subbox has no upper preimage.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Leading coefficient of the lower-minus-upper ordered triple volume,
including the normalization by the logarithm of the product scale. -/
def lowerTripleSurplusConstant : ℝ :=
  (27/2)*∫ v in (0:ℝ)..(1/3),Real.log (1-v)^2-Real.log (1+v)^2

/-- The lower volume is strictly larger since its logarithmic
displacement is larger at every positive reflected distance. -/
theorem lower_triple_surplus_constant_pos : 0 < lowerTripleSurplusConstant := by
  have hpos {v : ℝ} (hv : 0 < v) (hb : v ≤ 1/3) :
      0 < Real.log (1-v)^2-Real.log (1+v)^2 := by
    have hl : 0 < 1-v := by linarith
    have hr : 0 < 1+v := by linarith
    have hm := Real.log_lt_log (mul_pos hl hr) (by nlinarith only [sq_pos_of_pos hv] :
      (1-v)*(1+v)<1)
    rw [Real.log_mul hl.ne' hr.ne',Real.log_one] at hm
    have hlog := Real.log_pos (by linarith only [hv] : 1 < 1+v)
    have hmul := mul_pos (by linarith only [hm] : 0 < -Real.log (1-v)-Real.log (1+v))
      (by linarith only [hm,hlog] : 0 < -Real.log (1-v)+Real.log (1+v))
    linarith only [hmul]
  have hcont : ContinuousOn (fun v : ℝ => Real.log (1-v)^2-Real.log (1+v)^2)
      (Set.Icc 0 (1/3)) := by
    apply ContinuousOn.sub <;> apply ContinuousOn.pow <;> apply ContinuousOn.log
    · fun_prop
    · intro x hx; exact ne_of_gt (by linarith only [hx.2] : 0 < 1-x)
    · fun_prop
    · intro x hx; exact ne_of_gt (by linarith only [hx.1] : 0 < 1+x)
  exact mul_pos (by norm_num : (0:ℝ)<27/2)
    (intervalIntegral.integral_pos (by norm_num) hcont (fun _ h => (hpos h.1 h.2).le)
      ⟨1/6,by norm_num, hpos (by norm_num) (by norm_num)⟩)

/-- Reflection of each matched prime factor suffices for the whole
product, with a strict lower endpoint even when the upper product equals four thirds. -/
theorem reflected_upper_triple_is_lower {a b c x y z : ℝ}
    (ha : 1<a) (hb : 1<b) (hc : 1<c) (hu : a*b*c ≤ 4/3)
    (hx : 2-a ≤ x) (hy : 2-b ≤ y) (hz : 2-c ≤ z)
    (hx' : x ≤ 1) (hy' : y ≤ 1) (hz' : z ≤ 1) :
    2/3 < x*y*z ∧ x*y*z ≤ 1 := by
  have ha0 := zero_lt_one.trans ha
  have hb0 := zero_lt_one.trans hb
  have hc0 := zero_lt_one.trans hc
  have ha' := (le_mul_of_one_le_right ha0.le hb.le).trans
    (le_mul_of_one_le_right (mul_nonneg ha0.le hb0.le) hc.le)
  have hb' := (le_mul_of_one_le_left hb0.le ha.le).trans
    (le_mul_of_one_le_right (mul_nonneg ha0.le hb0.le) hc.le)
  have hc' := le_mul_of_one_le_left hc0.le (one_le_mul_of_one_le_of_one_le ha.le hb.le)
  have ax : 0 ≤ 2-a := by linarith only [ha',hu]
  have by' : 0 ≤ 2-b := by linarith only [hb',hu]
  have cz : 0 ≤ 2-c := by linarith only [hc',hu]
  have hab := mul_pos (sub_pos.mpr ha) (sub_pos.mpr hb)
  have hbc := mul_pos (sub_pos.mpr hb) (sub_pos.mpr hc)
  have hac := mul_pos (sub_pos.mpr ha) (sub_pos.mpr hc)
  have hprod := mul_le_mul (mul_le_mul hx hy by' (ax.trans hx)) hz cz
    (mul_nonneg (ax.trans hx) (by'.trans hy))
  constructor
  · linarith only [hu,hab,hbc,hac,hprod]
  · simpa only [one_mul] using mul_le_mul (mul_le_mul hx' hy' (by'.trans hy) zero_le_one)
      hz' (cz.trans hz) (by norm_num : (0:ℝ) ≤ 1*1)

/-- The fixed subbox lies inside the lower population and none of its
triples can be matched from the upper population by additive reflection. -/
theorem unmatched_lower_triple_box {x y z : ℝ}
    (hx : x ∈ Set.Icc (7/8) (8/9)) (hy : y ∈ Set.Icc (7/8) (8/9))
    (hz : z ∈ Set.Icc (7/8) (8/9)) :
    2/3 < x*y*z ∧ x*y*z ≤ 1 ∧
      ∀ a b c : ℝ, 2-a ≤ x → 2-b ≤ y → 2-c ≤ z → 4/3 < a*b*c := by
  have lo {u v w s : ℝ} (hs : 0 ≤ s) (hu : s ≤ u) (hv : s ≤ v) (hw : s ≤ w) :
      s*s*s ≤ u*v*w := mul_le_mul (mul_le_mul hu hv hs (hs.trans hu)) hw hs
        (mul_nonneg (hs.trans hu) (hs.trans hv))
  have hy0 := (by norm_num : (0:ℝ) ≤ 7/8).trans hy.1
  have hz0 := (by norm_num : (0:ℝ) ≤ 7/8).trans hz.1
  refine ⟨(by norm_num : (2/3:ℝ) < (7/8)*(7/8)*(7/8)).trans_le
    (lo (by norm_num) hx.1 hy.1 hz.1),?_,?_⟩
  · exact (mul_le_mul (mul_le_mul hx.2 hy.2 hy0 (by norm_num)) hz.2 hz0
      (by norm_num : (0:ℝ) ≤ (8/9)*(8/9))).trans (by norm_num)
  · intro a b c ha hb hc
    exact (by norm_num : (4/3:ℝ) < (10/9)*(10/9)*(10/9)).trans_le
      (lo (by norm_num) (by linarith only [hx.2,ha]) (by linarith only [hy.2,hb])
        (by linarith only [hz.2,hc]))

#print axioms lower_triple_surplus_constant_pos
#print axioms reflected_upper_triple_is_lower
#print axioms unmatched_lower_triple_box

private theorem rank_prefix {α : Type*} [LinearOrder α] (S : Finset α) (i : Fin S.card) :
    (S.filter (· ≤ S.orderEmbOfFin rfl i)).card=i.val+1 ∧
      (S.filter (· < S.orderEmbOfFin rfl i)).card=i.val := by
  let e := S.orderEmbOfFin rfl
  have hs : univ.map e.toEmbedding=S := map_orderEmbOfFin_univ S rfl
  have he (P : α → Prop) [DecidablePred P] :
      (S.filter P).card=(univ.filter (fun j : Fin S.card => P (e j))).card := by
    conv_lhs => rw [←hs,filter_map,card_map]
  have hle : univ.filter (fun j : Fin S.card => e j ≤ e i)=Iic i := by
    ext j; simp only [mem_filter,mem_univ,true_and,mem_Iic,e.le_iff_le]
  have hlt : univ.filter (fun j : Fin S.card => e j < e i)=Iio i := by
    ext j; simp only [mem_filter,mem_univ,true_and,mem_Iio,e.lt_iff_lt]
  exact ⟨(he _).trans ((congrArg card hle).trans Fin.card_Iic),
    (he _).trans ((congrArg card hlt).trans Fin.card_Iio)⟩

/-- Maximum excess of upper counts over lower counts at a common displacement. -/
def triplePairingDeficit (U L : Finset ℝ) : ℕ :=
  U.sup fun u => (U.filter (· ≤ u)).card-(L.filter (· ≤ u)).card

private theorem matched_displacements (U L : Finset ℝ) :
    ∃ u v : Fin (U.card-triplePairingDeficit U L) → ℝ, StrictMono u ∧ StrictMono v ∧
      ∀ i, u i ∈ U ∧ v i ∈ L ∧ v i ≤ u i ∧
        (U.filter (· ≤ u i)).card=i.val+triplePairingDeficit U L+1 ∧
        (L.filter (· ≤ v i)).card=i.val+1 := by
  let E := triplePairingDeficit U L
  let pick (i : Fin (U.card-E)) : Fin U.card := ⟨i.val+E,by have := i.isLt; omega⟩
  let u (i : Fin (U.card-E)) := U.orderEmbOfFin rfl (pick i)
  have hu i : (U.filter (· ≤ u i)).card=i.val+E+1 := (rank_prefix U (pick i)).1
  have hgap (i : Fin (U.card-E)) : i.val < (L.filter (· ≤ u i)).card := by
    have he : (U.filter (· ≤ u i)).card-(L.filter (· ≤ u i)).card ≤ E :=
      le_sup (f:=fun a => (U.filter (· ≤ a)).card-(L.filter (· ≤ a)).card)
        (U.orderEmbOfFin_mem rfl (pick i))
    rw [hu] at he
    omega
  let li (i : Fin (U.card-E)) : Fin L.card :=
    ⟨i.val,(hgap i).trans_le (card_le_card (filter_subset _ _))⟩
  let v (i : Fin (U.card-E)) := L.orderEmbOfFin rfl (li i)
  refine ⟨u,v,?_,?_,?_⟩
  · intro i j hij
    apply (U.orderEmbOfFin rfl).strictMono
    exact Nat.add_lt_add_right (show i.val<j.val from hij) E
  · intro i j hij
    exact (L.orderEmbOfFin rfl).strictMono (show li i < li j from hij)
  · intro i
    refine ⟨U.orderEmbOfFin_mem rfl _,L.orderEmbOfFin_mem rfl _,?_,hu i,(rank_prefix L (li i)).1⟩
    by_contra! hv
    have hs : L.filter (· ≤ u i) ⊆ L.filter (· < v i) := by
      intro x hx
      exact mem_filter.mpr ⟨(mem_filter.mp hx).1,(mem_filter.mp hx).2.trans_lt hv⟩
    have hl := card_le_card hs
    have hlt := (rank_prefix L (li i)).2
    change (L.filter (· < v i)).card=i.val at hlt
    have hg := hgap i
    omega

/-- Displacements of ordinary primes above the cube root, up to one third of its size. -/
def upperTripleDistances (y : ℝ) : Finset ℝ :=
  (((Icc 1 ⌊4*y/3⌋₊).filter (fun p : ℕ => p.Prime ∧ y<p)).image (fun p : ℕ => (p:ℝ)-y))

/-- Displacements of ordinary primes below the cube root, including the center if prime. -/
def lowerTripleDistances (y : ℝ) : Finset ℝ :=
  (((Icc 1 ⌊y⌋₊).filter (fun p : ℕ => p.Prime ∧ 2*y/3≤p)).image (fun p : ℕ => y-(p:ℝ)))

/-- Discard the first excess upper primes and pair the rest in order.
The lower partner lies at or above the reflection of the upper prime. -/
theorem actual_prime_triple_pairing (y : ℝ) :
    let U := upperTripleDistances y
    let L := lowerTripleDistances y
    let E := triplePairingDeficit U L
    ∃ p q : Fin (U.card-E) → ℕ, StrictMono p ∧ StrictAnti q ∧
      ∀ i, (p i).Prime ∧ (q i).Prime ∧ y<p i ∧ (q i:ℝ) ≤ y ∧ 2*y-p i ≤ q i ∧
        (U.filter (· ≤ (p i:ℝ)-y)).card=i.val+E+1 ∧
        (L.filter (· ≤ y-(q i:ℝ))).card=i.val+1 := by
  dsimp only
  obtain ⟨u,v,hmu,hmv,hs⟩ := matched_displacements (upperTripleDistances y) (lowerTripleDistances y)
  have up (i) := mem_image.mp (hs i).1
  have down (i) := mem_image.mp (hs i).2.1
  choose p hp hpv using up
  choose q hq hqv using down
  refine ⟨p,q,?_,?_,?_⟩
  · intro i j hij
    have h := hmu hij
    rw [←hpv i,←hpv j] at h
    exact_mod_cast (sub_lt_sub_iff_right y).mp h
  · intro i j hij
    have h := hmv hij
    rw [←hqv i,←hqv j] at h
    exact_mod_cast (sub_lt_sub_iff_left y).mp h
  · intro i
    obtain ⟨_,hpi,hy⟩ := mem_filter.mp (hp i)
    obtain ⟨hqI,hqi,_⟩ := mem_filter.mp (hq i)
    have hy0 : 0 ≤ y := by
      by_contra! hneg
      have ht := (mem_Icc.mp hqI).2
      rw [Nat.floor_of_nonpos hneg.le] at ht
      have hh := hqi.two_le
      omega
    refine ⟨hpi,hqi,hy,((Nat.cast_le (α:=ℝ)).mpr (mem_Icc.mp hqI).2).trans (Nat.floor_le hy0),?_,
      by simpa only [hpv i] using (hs i).2.2.2.1,
      by simpa only [hqv i] using (hs i).2.2.2.2⟩
    linarith only [(hs i).2.2.1,hpv i,hqv i]

#print axioms actual_prime_triple_pairing

open Filter RHTower RHTower.PrimeCells in
/-- Uniform prime counting discrepancy for every slice of a triple box,
including slices whose length tends to zero. -/
theorem triple_box_prime_window_discrepancy :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ y : ℝ in atTop, ∀ a b : ℝ, y/2 ≤ a → a ≤ b → b ≤ 2*y →
      |((windowPrimes a b).card:ℝ)*Real.log y-(b-a)| ≤ K*y/Real.log y := by
  obtain ⟨C,hC,T,hT,hθ⟩ := exists_abs_theta_sub_le 1
  have h2 := Real.log_pos (by norm_num : (1:ℝ)<2)
  refine ⟨8*C+6*Real.log 2,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (2*T),Real.tendsto_log_atTop.eventually_ge_atTop 1,
    Real.tendsto_log_atTop.eventually_ge_atTop (2*Real.log 2),
    Real.tendsto_log_atTop.eventually_ge_atTop (8*C)] with y hy hlog hlarge hC'
  intro a b ha hab hb
  have hTa : T ≤ a := by linarith only [hy,ha]
  have ha1 : 1 ≤ a := by linarith only [hTa,hT]
  have hy0 : 0 < y := by linarith only [hy,hT]
  have hL : 0 < Real.log y := by linarith only [hlog]
  have hlow := Real.log_le_log (div_pos hy0 (by norm_num : (0:ℝ)<2)) ha
  rw [Real.log_div hy0.ne' (by norm_num)] at hlow
  have hla : 0 < Real.log a := by linarith only [hlow,hlarge,hL]
  have hhigh := Real.log_le_log (by linarith only [ha1,hab] : 0 < b) hb
  rw [Real.log_mul (by norm_num) hy0.ne'] at hhigh
  have hΔ := abs_theta_increment_le hC.le hT hθ hTa hab
  rw [pow_one] at hΔ
  have hden : Real.log y/2 ≤ Real.log a := by linarith only [hlow,hlarge]
  have herr : |Chebyshev.theta b-Chebyshev.theta a-(b-a)| ≤ 8*C*y/Real.log y := by
    apply hΔ.trans
    calc 2*C*b/Real.log a ≤ 2*C*(2*y)/(Real.log y/2) :=
           div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hb (by positivity))
             (by positivity) hden
         _ = _ := by ring
  let N : ℝ := (windowPrimes a b).card
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hNlo := card_windowPrimes_mul_log_le ha1 hab
  have hNhi := theta_sub_le_card_mul_log (by linarith only [ha1]) hab
  change N*Real.log a ≤ _ at hNlo
  change _ ≤ N*Real.log b at hNhi
  have hyerr : 8*C*y/Real.log y ≤ y := (div_le_iff₀ hL).mpr
    (by linarith only [mul_le_mul_of_nonneg_right hC' hy0.le])
  have hprice : N ≤ 6*y/Real.log y := (le_div_iff₀ hL).mpr (by
    linarith only [mul_le_mul_of_nonneg_left hden hN,hNlo,(abs_le.mp herr).2,hyerr,hb,ha1])
  have hprice' := mul_le_mul_of_nonneg_right hprice h2.le
  have hu := mul_le_mul_of_nonneg_left hlow hN
  have hl := mul_le_mul_of_nonneg_left hhigh hN
  change |N*Real.log y-(b-a)| ≤ _
  rw [show (8*C+6*Real.log 2)*y/Real.log y=
    8*C*y/Real.log y+(6*y/Real.log y)*Real.log 2 by ring]
  apply abs_le.mpr
  constructor <;> linarith only [(abs_le.mp herr).1,(abs_le.mp herr).2,hprice',hu,hl,hNlo,hNhi]

#print axioms triple_box_prime_window_discrepancy

open RHTower in
private theorem reflected_prime_counts {y t : ℝ} (hy : 0 < y) (ht : 0 ≤ t) (hcap : t ≤ y/3) :
    ((upperTripleDistances y).filter (· ≤ t)).card=(windowPrimes y (y+t)).card ∧
      (windowPrimes (y-t) y).card ≤ ((lowerTripleDistances y).filter (· ≤ t)).card := by
  classical
  have hi : Function.Injective (fun p : ℕ => (p:ℝ)-y) := by
    intro a b h; exact_mod_cast (sub_left_injective h)
  have hj : Function.Injective (fun p : ℕ => y-(p:ℝ)) := by
    intro a b h; exact_mod_cast (sub_right_injective h)
  have hY : 0 ≤ 4*y/3 := by positivity
  have hu : (upperTripleDistances y).filter (· ≤ t)=
      (windowPrimes y (y+t)).image (fun p : ℕ => (p:ℝ)-y) := by
    ext u
    constructor
    · intro h
      obtain ⟨p,hp,rfl⟩ := mem_image.mp (mem_filter.mp h).1
      obtain ⟨_,hpr,hpy⟩ := mem_filter.mp hp
      exact mem_image.mpr ⟨p,(mem_windowPrimes hy.le (by linarith)).mpr
        ⟨hpr,hpy,by linarith only [(mem_filter.mp h).2]⟩,rfl⟩
    · intro h
      obtain ⟨p,hp,rfl⟩ := mem_image.mp h
      obtain ⟨hp,hyp,hpu⟩ := (mem_windowPrimes hy.le (by linarith)).mp hp
      exact mem_filter.mpr ⟨mem_image.mpr ⟨p,mem_filter.mpr
        ⟨mem_Icc.mpr ⟨hp.one_le,Nat.le_floor (by linarith only [hpu,hcap])⟩,hp,hyp⟩,rfl⟩,
          by linarith only [hpu]⟩
  have hl : (windowPrimes (y-t) y).image (fun p : ℕ => y-(p:ℝ)) ⊆ (lowerTripleDistances y).filter (· ≤ t) := by
    intro v hv
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hv
    obtain ⟨hp,hyp,hpy⟩ := (mem_windowPrimes (by linarith) hy.le).mp hp
    exact mem_filter.mpr ⟨mem_image.mpr ⟨p,mem_filter.mpr
      ⟨mem_Icc.mpr ⟨hp.one_le,Nat.le_floor hpy⟩,hp,by linarith only [hyp,hcap]⟩,rfl⟩,
        by linarith only [hyp]⟩
  exact ⟨hu ▸ card_image_of_injective _ hi,(card_image_of_injective _ hj).symm.le.trans (card_le_card hl)⟩

open Filter RHTower in
/-- The number of discarded upper primes is little-o of the prime
counting scale, uniformly across all displacements used by the pairing. -/
theorem negligible_prime_triple_pairing_deficit :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ y : ℝ in atTop,
      (triplePairingDeficit (upperTripleDistances y) (lowerTripleDistances y):ℝ)*Real.log y ≤ ε*y := by
  intro ε hε
  obtain ⟨K,hK,hwin⟩ := triple_box_prime_window_discrepancy
  filter_upwards [hwin,eventually_ge_atTop 2,Real.tendsto_log_atTop.eventually_ge_atTop (2*K/ε)]
    with y hy hy2 hlog
  have hy0 : 0<y := by linarith only [hy2]
  have hL := Real.log_pos (by linarith only [hy2] : 1<y)
  have hbound : 2*(K*y/Real.log y) ≤ ε*y := by
    have he := (div_le_iff₀ hε).mp hlog
    have hf := mul_le_mul_of_nonneg_right he hy0.le
    rw [←mul_div_assoc,le_div_iff₀] <;> first | positivity | linarith
  rcases (upperTripleDistances y).eq_empty_or_nonempty with hU | hU
  · simp only [triplePairingDeficit,hU,sup_empty,Nat.bot_eq_zero,Nat.cast_zero,zero_mul]
    exact mul_nonneg hε.le hy0.le
  · obtain ⟨t,ht,he⟩ := exists_mem_eq_sup _ hU
      (fun t => ((upperTripleDistances y).filter (· ≤ t)).card-((lowerTripleDistances y).filter (· ≤ t)).card)
    obtain ⟨p,hp,hpt⟩ := mem_image.mp ht
    have hpI := mem_Icc.mp (mem_filter.mp hp).1
    have hpy := (mem_filter.mp hp).2.2
    have hpu := ((Nat.cast_le (α:=ℝ)).mpr hpI.2).trans (Nat.floor_le (by positivity))
    have ht0 : 0 ≤ t := by linarith only [hpt,hpy]
    have ht1 : t ≤ y/3 := by linarith only [hpt,hpu]
    obtain ⟨hu,hl⟩ := reflected_prime_counts hy0 ht0 ht1
    have eup := abs_le.mp (hy y (y+t) (by linarith) (by linarith) (by linarith))
    have elo := abs_le.mp (hy (y-t) y (by linarith) (by linarith) (by linarith))
    rw [triplePairingDeficit,he,hu]
    by_cases hc : ((lowerTripleDistances y).filter (· ≤ t)).card ≤ (windowPrimes y (y+t)).card
    · rw [Nat.cast_sub hc]
      have hlow := mul_le_mul_of_nonneg_right ((Nat.cast_le (α:=ℝ)).mpr hl) hL.le
      linarith only [eup.2,elo.1,hlow,hbound]
    · rw [Nat.sub_eq_zero_of_le (le_of_not_ge hc),Nat.cast_zero,zero_mul]
      exact mul_nonneg hε.le hy0.le

#print axioms negligible_prime_triple_pairing_deficit

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
