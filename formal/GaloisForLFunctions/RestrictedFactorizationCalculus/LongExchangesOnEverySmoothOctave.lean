import GaloisForLFunctions.RestrictedFactorizationCalculus.BothSignsOnEverySmoothOctave
import GaloisForLFunctions.RestrictedFactorizationCalculus.TheTwoCutoffsAroundASmoothVertex

/-!
# Positive-density long exchanges and the mean unpaid prefix

A smooth squarefree vertex has a large common cofactor with any genuine
partner. On every octave a positive fraction of either sign is fixed or
moves farther than any prescribed power below one. An edge charges every
cutoff between its endpoints.
-/

noncomputable section

open Finset Filter
open ArithmeticFunction hiding id
open scoped Classical Topology ArithmeticFunction.Moebius
open GaloisForLFunctions.QuantitativeFactorizationMatching

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private theorem smooth_edge_cost {n m : ℕ} {y : ℝ} (hy : 1 ≤ y)
    (smooth : ∀ q ∈ n.primeFactors,(q:ℝ) ≤ y) (edge : GlobalDyadicOneTwoRel n m) :
    (n:ℝ) ≤ |(m:ℝ)-n|*y^2 := by
  obtain ⟨hs,_,_,c,p,q,r,hp,hq,hr,_,he⟩ := edge
  have hne : p ≠ q*r := by
    intro h
    have hq' : q=p := (Nat.prime_dvd_prime_iff_eq hq hp).1 (h ▸ Nat.dvd_mul_right q r)
    have hlt : q<q*r := by simpa only [Nat.mul_one] using Nat.mul_lt_mul_of_pos_left hr.one_lt hq.pos
    exact hlt.ne (hq'.trans h)
  have gap {a b : ℕ} (hne : a ≠ b) : (1:ℝ) ≤ |(b:ℝ)-a| := by
    rcases lt_or_gt_of_ne hne with h | h
    · rw [abs_of_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr h.le))]
      have hl : (a:ℝ)+1 ≤ b := by exact_mod_cast h
      linarith only [hl]
    · rw [abs_of_nonpos (sub_nonpos.mpr (Nat.cast_le.mpr h.le))]
      have hl : (b:ℝ)+1 ≤ a := by exact_mod_cast h
      linarith only [hl]
  have bound {a b : ℕ} (hn : n=c*a) (hm : m=c*b) (hu : (a:ℝ) ≤ y^2) (hab : a ≠ b) :
      (n:ℝ) ≤ |(m:ℝ)-n|*y^2 := by
    rw [hn,hm,Nat.cast_mul,Nat.cast_mul,←mul_sub,abs_mul,abs_of_nonneg (Nat.cast_nonneg c)]
    have hh : (c:ℝ) ≤ c*|(b:ℝ)-a| := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (gap hab) (Nat.cast_nonneg c)
    exact (mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg c)).trans (mul_le_mul_of_nonneg_right hh (sq_nonneg _))
  have pf {q : ℕ} (hp : q.Prime) (hd : q ∣ n) := smooth q (Nat.mem_primeFactors.mpr ⟨hp,hd,hs.ne_zero⟩)
  rcases he with ⟨hn,hm⟩ | ⟨hm,hn⟩
  · have hdiv : p ∣ n := hn ▸ Nat.dvd_mul_left p c
    have hyy : y ≤ y^2 := by simpa only [pow_two,one_mul] using mul_le_mul_of_nonneg_right hy (zero_le_one.trans hy)
    exact bound hn hm ((pf hp hdiv).trans hyy) hne
  · have hdiv : q*r ∣ n := hn ▸ Nat.dvd_mul_left (q*r) c
    have hq' := pf hq ((Nat.dvd_mul_right q r).trans hdiv)
    have hr' := pf hr ((Nat.dvd_mul_left r q).trans hdiv)
    exact bound hn hm (by rw [Nat.cast_mul,pow_two]; exact mul_le_mul hq' hr' (Nat.cast_nonneg r) (zero_le_one.trans hy)) hne.symm

/-- Each Möbius sign contains a positive density of squarefree vertices
on which every permitted change exceeds the prescribed displacement. -/
theorem positive_density_of_forced_long_moves {γ : ℝ} (hγ : γ<1) (b : Bool) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ X : ℕ in atTop,
      c*X ≤ (((Ioc X (2*X)).filter (fun n =>
        μ n=(if b then 1 else -1) ∧ ∀ m : ℕ,GlobalDyadicOneTwoRel n m →
          (X:ℝ)^γ < |(m:ℝ)-n|)).card:ℝ) := by
  let δ := (1-γ)/4
  have hd : 0<δ := by dsimp only [δ]; linarith only [hγ]
  obtain ⟨c,hc,hcnt⟩ := both_signs_at_every_smoothness_exponent hd b
  have grow := ((tendsto_rpow_atTop (show 0<1-(γ+2*δ) by dsimp only [δ]; linarith only [hγ])).comp
    tendsto_natCast_atTop_atTop).eventually_gt_atTop ((2:ℝ)^(2*δ))
  have twice : Tendsto (fun X : ℕ => 2*(X:ℝ)) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (by norm_num)).mpr tendsto_natCast_atTop_atTop
  refine ⟨2*c,by positivity,?_⟩
  filter_upwards [twice.eventually hcnt,grow,eventually_ge_atTop (1:ℕ)] with X hX hg hx
  have hx0 : (0:ℝ)<X := Nat.cast_pos.mpr hx
  have hx1 : (1:ℝ) ≤ 2*(X:ℝ) := by have hh : (1:ℝ) ≤ X := by exact_mod_cast hx; linarith
  let y := (2*(X:ℝ))^δ
  have hy : 1 ≤ y := Real.one_le_rpow hx1 hd.le
  have hsmall : (X:ℝ)^γ*y^2 < X := by
    have h2δ : y^2=(2:ℝ)^(2*δ)*(X:ℝ)^(2*δ) := by
      dsimp only [y]
      rw [←Real.rpow_natCast,←Real.rpow_mul (by positivity),Real.mul_rpow (by norm_num) hx0.le]
      norm_num; ring_nf
    rw [h2δ]
    calc _ = (2:ℝ)^(2*δ)*(X:ℝ)^(γ+2*δ) := by rw [Real.rpow_add hx0]; ring
         _ < (X:ℝ)^(1-(γ+2*δ))*(X:ℝ)^(γ+2*δ) := mul_lt_mul_of_pos_right hg (Real.rpow_pos_of_pos hx0 _)
         _ = X := by rw [←Real.rpow_add hx0,sub_add_cancel,Real.rpow_one]
  have sub : smoothSignOctave b δ (2*(X:ℝ)) ⊆ (Ioc X (2*X)).filter (fun n =>
        μ n=(if b then 1 else -1) ∧ ∀ m : ℕ,GlobalDyadicOneTwoRel n m → (X:ℝ)^γ < |(m:ℝ)-n|) := by
    intro n hn
    obtain ⟨hi,hl,hm,hs⟩ := mem_filter.mp hn
    have hlo : X<n := by exact_mod_cast (show (X:ℝ)<n by linarith only [hl])
    have hhi : n ≤ 2*X := by
      exact_mod_cast (Nat.cast_le.mpr (mem_Icc.mp hi).2).trans (Nat.floor_le (by positivity : 0 ≤ 2*(X:ℝ)))
    refine mem_filter.mpr ⟨mem_Ioc.mpr ⟨hlo,hhi⟩,hm,fun m edge => ?_⟩
    have price := smooth_edge_cost hy hs edge
    by_contra! hh
    have imp := mul_le_mul_of_nonneg_right hh (sq_nonneg y)
    linarith only [price,imp,hsmall,Nat.cast_lt.mpr hlo]
  calc (2*c)*(X:ℝ) = c*(2*X) := by ring
       _ ≤ _ := hX
       _ ≤ _ := Nat.cast_le.mpr (card_le_card sub)

/-- A block of H consecutive observation points on the side of a vertex
where its edge remains unpaid. Fixed vertices charge to the right. -/
private def chargedCutoffs (F : ℕ → ℕ) (H n : ℕ) :=
  if F n<n then Ico (n-H) n else Ico n (n+H)

private theorem traffic_interior {F : ℕ → ℕ} (law : ∀ n,Squarefree n →
    F (F n)=n ∧ (F n=n ∨ GlobalDyadicOneTwoRel n (F n))) {S : Finset ℕ} {X H : ℕ}
    (hs : ∀ n ∈ S,Squarefree n ∧ X+H ≤ n ∧ n+H ≤ 2*X ∧
      (F n=n ∨ F n+H ≤ n ∨ n+H ≤ F n)) :
    S.card*H ≤ 2*∑ x ∈ Icc X (2*X),(prefixUnpaid F x).card := by
  let V := Icc X (2*X)
  let cut := chargedCutoffs F H
  have spec {n : ℕ} (hn : n ∈ S) :
      (cut n).card=H ∧ cut n ⊆ V ∧ ∀ x ∈ cut n,
        n ∈ prefixUnpaid F x ∨ n ∈ (prefixUnpaid F x).image F := by
    obtain ⟨hsq,hlo,hhi,hgap⟩ := hs n hn
    obtain ⟨hback,hedge⟩ := law n hsq
    have hn0 : 1 ≤ n := Nat.pos_of_ne_zero hsq.ne_zero
    by_cases h : F n<n
    · have he := hedge.resolve_left h.ne
      have cutEq : cut n=Ico (n-H) n := if_pos h
      rw [cutEq]
      refine ⟨by rw [Nat.card_Ico]; omega,fun x hx => ?_,fun x hx => ?_⟩
      · obtain ⟨h1,h2⟩ := mem_Ico.mp hx
        exact mem_Icc.mpr ⟨by omega,by omega⟩
      · obtain ⟨h1,h2⟩ := mem_Ico.mp hx
        apply Or.inr (mem_image.mpr ⟨F n,?_,hback⟩)
        refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.pos_of_ne_zero he.2.1.ne_zero,by omega⟩,he.2.1⟩,?_⟩
        exact Or.inr (by rw [hback]; exact h2)
    · have cutEq : cut n=Ico n (n+H) := if_neg h
      rw [cutEq]
      refine ⟨by rw [Nat.card_Ico]; omega,fun x hx => ?_,fun x hx => ?_⟩
      · obtain ⟨h1,h2⟩ := mem_Ico.mp hx
        exact mem_Icc.mpr ⟨by omega,by omega⟩
      · obtain ⟨h1,h2⟩ := mem_Ico.mp hx
        exact Or.inl (mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨hn0,h1⟩,hsq⟩,by omega⟩)
  have load (x : ℕ) : (S.filter (fun n => x ∈ cut n)).card ≤ 2*(prefixUnpaid F x).card := by
    have sub : S.filter (fun n => x ∈ cut n) ⊆ prefixUnpaid F x ∪ (prefixUnpaid F x).image F := by
      intro n hn
      obtain ⟨h,hx⟩ := mem_filter.mp hn
      exact mem_union.mpr ((spec h).2.2 _ hx)
    exact (card_le_card sub).trans ((card_union_le ..).trans
      ((Nat.add_le_add_left card_image_le _).trans_eq (two_mul _).symm))
  calc S.card*H = ∑ n ∈ S,(cut n).card := by
         rw [sum_congr rfl (fun n hn => (spec hn).1),sum_const,nsmul_eq_mul]
       _ = ∑ n ∈ S,∑ x ∈ V,if x ∈ cut n then 1 else 0 := by
         apply sum_congr rfl
         intro n hn
         rw [←sum_filter]
         simp only [sum_const,nsmul_eq_mul,mul_one]
         congr 1
         ext x
         simp only [mem_filter]
         exact ⟨fun h => ⟨(spec hn).2.1 h,h⟩,And.right⟩
       _ = ∑ x ∈ V,(S.filter (fun n => x ∈ cut n)).card := by
         rw [sum_comm]
         apply sum_congr rfl
         intro x _
         rw [←sum_filter]; simp
       _ ≤ _ := by rw [mul_sum]; exact sum_le_sum fun x _ => load x

/-- On every large octave the total unsigned charge over its cutoffs is
at least a fixed multiple of X^(1+γ), uniformly over all involutions. -/
theorem unsigned_traffic_on_every_octave {γ : ℝ} (hγ : 0<γ) (hsub : γ<1) :
    ∃ A : ℝ,0<A ∧ ∀ᶠ X : ℕ in atTop, ∀ F : ℕ → ℕ,
      (∀ n,Squarefree n → F (F n)=n ∧ (F n=n ∨ GlobalDyadicOneTwoRel n (F n))) →
      A*(X:ℝ)^(1+γ) ≤ (∑ x ∈ Icc X (2*X),(prefixUnpaid F x).card:ℕ) := by
  obtain ⟨c,hc,h⟩ := positive_density_of_forced_long_moves hsub true
  refine ⟨c/8,by positivity,?_⟩
  filter_upwards [h,eventually_ge_atTop (1:ℕ),
    ((tendsto_rpow_atTop (sub_pos.mpr hsub)).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (4/c),
    ((tendsto_rpow_atTop hγ).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2] with X hX hx hroom hlarge
  intro F law
  let H := ⌊(X:ℝ)^γ⌋₊
  let P := (Ioc X (2*X)).filter (fun n => μ n=1 ∧
    ∀ m : ℕ,GlobalDyadicOneTwoRel n m → (X:ℝ)^γ < |(m:ℝ)-n|)
  let S := P.filter (fun n => X+H ≤ n ∧ n+H ≤ 2*X)
  have hx0 : (0:ℝ)<X := Nat.cast_pos.mpr hx
  have grow := Real.rpow_pos_of_pos hx0 γ
  have hup : (H:ℝ) ≤ (X:ℝ)^γ := Nat.floor_le grow.le
  have hdown : (X:ℝ)^γ/2 ≤ (H:ℝ) := by linarith only [Nat.lt_floor_add_one ((X:ℝ)^γ),hlarge]
  have hH : H ≤ X := Nat.cast_le.mp (hup.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hx : (1:ℝ) ≤ X) hsub.le))
  have hbudget : 4*(H:ℝ) ≤ c*X := by
    change 4/c ≤ (X:ℝ)^(1-γ) at hroom
    rw [Real.rpow_sub hx0,Real.rpow_one] at hroom
    have hh := (div_le_div_iff₀ hc grow).1 hroom
    linarith only [hh,hup]
  have sub : P ⊆ (S ∪ Ioc X (X+H)) ∪ Ioc (2*X-H) (2*X) := by
    intro n hn
    obtain ⟨hl,hu⟩ := mem_Ioc.mp (mem_filter.mp hn).1
    by_cases low : X+H ≤ n
    · by_cases high : n+H ≤ 2*X
      · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hn,low,high⟩))
      · exact mem_union_right _ (mem_Ioc.mpr ⟨by omega,hu⟩)
    · exact mem_union_left _ (mem_union_right _ (mem_Ioc.mpr ⟨hl,by omega⟩))
  have hmiss := (card_le_card sub).trans ((card_union_le ..).trans (Nat.add_le_add_right (card_union_le ..) _))
  rw [Nat.card_Ioc,Nat.card_Ioc] at hmiss
  have hdiff : P.card ≤ S.card+H+H := by omega
  have hdiffR := (Nat.cast_le (α := ℝ)).mpr hdiff
  push_cast only [Nat.cast_add] at hdiffR
  change c*X ≤ (P.card:ℝ) at hX
  have hs : c*X/2 ≤ (S.card:ℝ) := by linarith only [hX,hdiffR,hbudget]
  have hflow := traffic_interior (H := H) (X := X) (S := S) law (by
    intro n hn
    obtain ⟨hp,hl,hu⟩ := mem_filter.mp hn
    obtain ⟨_,hm,hedge⟩ := mem_filter.mp hp
    have hsq : Squarefree n := by
      by_contra h
      rw [moebius_eq_zero_of_not_squarefree h] at hm
      contradiction
    refine ⟨hsq,hl,hu,?_⟩
    rcases (law n hsq).2 with he | he
    · exact Or.inl he
    have hd := hup.trans_lt (hedge (F n) he)
    rcases le_total (F n) n with down | up
    · rw [abs_of_nonpos (sub_nonpos.mpr (Nat.cast_le.mpr down))] at hd
      right; left
      exact_mod_cast (show (F n:ℝ)+H ≤ n by linarith only [hd])
    · rw [abs_of_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr up))] at hd
      right; right
      exact_mod_cast (show (n:ℝ)+H ≤ F n by linarith only [hd]))
  have harea := (Nat.cast_le (α := ℝ)).mpr hflow
  push_cast only [Nat.cast_mul,Nat.cast_ofNat] at harea
  have hrect := mul_le_mul hs hdown (by positivity) (Nat.cast_nonneg S.card)
  rw [Real.rpow_add hx0,Real.rpow_one]
  linarith only [hrect,harea]

#print axioms positive_density_of_forced_long_moves
#print axioms unsigned_traffic_on_every_octave

end GaloisForLFunctions.RestrictedFactorizationCalculus
