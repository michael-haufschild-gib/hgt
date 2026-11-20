import GaloisForLFunctions.RestrictedFactorizationCalculus.UniformSurvivorsOfSparseDivisors
import GaloisForLFunctions.RestrictedFactorizationCalculus.DensityOneForRestrictedPrimeExchanges
import GaloisForLFunctions.RHTower.WeilFullConeThreeHalvesLacunaryRigidity

/-!
# Positive density of isolated integers for bounded exchange tables

A cofactor may be used arbitrarily often. The relevant restriction is how
many primitive pairs a given smaller split prime can use. When this number
is bounded, the divisors which can appear at an endpoint have uniformly
summable tails. A positive fraction of every large block consists of
squarefree integers outside every possible exchange.
-/

noncomputable section

open Finset Filter
open scoped Classical
open GaloisForLFunctions.QuantitativeFactorizationMatching

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private theorem square_tail (K : ℕ) (hK : 0<K) (S : Finset ℕ) (hS : ∀ q ∈ S,K<q) :
    ∑ q ∈ S,1/(q:ℝ)^2 ≤ 1/(K:ℝ) := by
  let H := K+1
  obtain ⟨hs,h⟩ := RHTower.tsum_inv_nat_add_sq_le H (by dsimp [H]; omega)
  have hq (q : ℕ) (hq : q ∈ S) : q-H+H=q := Nat.sub_add_cancel (hS q hq)
  have hin : Set.InjOn (·-H) (S:Set ℕ) := fun q h₁ r h₂ he =>
    (hq q h₁).symm.trans ((congrArg (·+H) he).trans (hq r h₂))
  have hh := hs.sum_le_tsum (S.image (·-H)) (fun i _ => by positivity)
  rw [sum_image hin] at hh
  calc _ = ∑ q ∈ S,1/((q-H+H:ℕ):ℝ)^2 := sum_congr rfl fun q h => by rw [hq q h]
       _ ≤ _ := (hh.trans h).trans_eq (by dsimp [H]; push_cast; ring_nf)

/-- Finite lists of divisors assigned to rows, with at most D entries per row.
A divisor in row q is at least half the square of q. -/
private def divisorRows (D : ℕ) : Set (Finset ℕ) := {B | ∃ L : ℕ, ∃ rows : ℕ → Finset ℕ,
  B=(Icc 1 L).biUnion rows ∧ ∀ q ∈ Icc 1 L, (rows q).card ≤ D ∧
    ∀ b ∈ rows q, 1<b ∧ q^2 ≤ 2*b}

private theorem rows_tail {D : ℕ} {B : Finset ℕ} (hB : B ∈ divisorRows D)
    (K : ℕ) (hK : 0<K) : reciprocalTail B (K^2) ≤ 3*D/(K:ℝ) := by
  obtain ⟨L,rows,rfl,hr⟩ := hB
  let I := Icc 1 L
  let B := (I.biUnion rows).filter (K^2<·)
  let owner (b : ℕ) := if h : b ∈ I.biUnion rows then (mem_biUnion.mp h).choose else 0
  have owns (b : ℕ) (hb : b ∈ B) : owner b ∈ I ∧ b ∈ rows (owner b) := by
    have h := (mem_filter.mp hb).1
    simpa only [owner,dif_pos h] using (mem_biUnion.mp h).choose_spec
  let weight (q : ℕ) := if q ≤ K then 1/(K:ℝ)^2 else 2/(q:ℝ)^2
  have hw (q : ℕ) : 0 ≤ weight q := by dsimp [weight]; split <;> positivity
  have fibre (q : ℕ) (hq : q ∈ I) :
      ∑ b ∈ B.filter (owner · = q),1/(b:ℝ) ≤ (D:ℝ)*weight q := by
    let V := B.filter (owner · = q)
    have sub : V ⊆ rows q := by
      intro b hb
      obtain ⟨h,he⟩ := mem_filter.mp hb
      exact he ▸ (owns b h).2
    have hc := (card_le_card sub).trans (hr q hq).1
    calc _ ≤ ∑ _b ∈ V,weight q := by
             apply sum_le_sum
             intro b hb
             have hb0 := (hr q hq).2 b (sub hb)
             have hbR : (0:ℝ)<b := Nat.cast_pos.mpr (zero_lt_one.trans hb0.1)
             dsimp only [weight]
             split_ifs
             · have hh := (mem_filter.mp (mem_filter.mp hb).1).2
               exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hh.le)
             · have hqR : (0:ℝ) < q := Nat.cast_pos.mpr (mem_Icc.mp hq).1
               apply (div_le_div_iff₀ hbR (sq_pos_of_pos hqR)).2
               simpa only [one_mul] using (show (q:ℝ)^2 ≤ 2*b by exact_mod_cast hb0.2)
         _ = (V.card:ℝ)*weight q := by simp
         _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hc) (hw q)
  let small := I.filter (· ≤ K)
  let large := I.filter (fun q => ¬q ≤ K)
  have hsmall : small ⊆ Icc 1 K := fun q h => mem_Icc.mpr
    ⟨(mem_Icc.mp (mem_filter.mp h).1).1,(mem_filter.mp h).2⟩
  have hcard : small.card ≤ K := by simpa using card_le_card hsmall
  have hp : (0:ℝ)<K := Nat.cast_pos.mpr hK
  have hs : ∑ q ∈ small,weight q ≤ 1/(K:ℝ) := by
    calc _ = (small.card:ℝ)*(1/(K:ℝ)^2) := by
             rw [←nsmul_eq_mul,←sum_const]
             exact sum_congr rfl (fun q h => if_pos (mem_filter.mp h).2)
         _ ≤ (K:ℝ)*(1/(K:ℝ)^2) := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) (by positivity)
         _ = _ := by field_simp
  have hl : ∑ q ∈ large, weight q ≤ 2*(1/(K:ℝ)) := by
    calc _ = ∑ q ∈ large,2*(1/(q:ℝ)^2) := sum_congr rfl (fun q h => by
             dsimp only [weight]; rw [if_neg (mem_filter.mp h).2]; ring)
         _ ≤ _ := by rw [←mul_sum]; exact mul_le_mul_of_nonneg_left
                        (square_tail K hK large fun q h => Nat.lt_of_not_ge (mem_filter.mp h).2) (by norm_num)
  have hall := sum_filter_add_sum_filter_not I (· ≤ K) weight
  have hcost : ∑ q ∈ I,weight q ≤ 3/(K:ℝ) := by
    change (∑ q ∈ small, weight q)+(∑ q ∈ large,weight q)=_ at hall
    rw [← hall]
    exact (add_le_add hs hl).trans_eq (by ring)
  change (∑ b ∈ B,1/(b:ℝ)) ≤ _
  rw [←sum_fiberwise_of_maps_to (fun b hb => (owns b hb).1) (fun b => 1/(b:ℝ))]
  calc _ ≤ ∑ q ∈ I,(D:ℝ)*weight q := sum_le_sum fibre
       _ ≤ _ := by rw [←mul_sum]; exact (mul_le_mul_of_nonneg_left hcost (Nat.cast_nonneg D)).trans_eq (by ring)

private theorem rows_density (D : ℕ) :
    ∃ δ : ℝ, 0<δ ∧ ∀ᶠ X : ℕ in atTop, ∀ B ∈ divisorRows D,
      δ*X ≤ (((Ioc X (2*X)).filter (fun n => ∀ b ∈ B, ¬b ∣ n)).card:ℝ) := by
  apply uniform_density_outside_sparse_divisors
  · rintro B ⟨L,A,rfl,hA⟩ b hb
    obtain ⟨q,hq,hb⟩ := mem_biUnion.mp hb
    exact ((hA q hq).2 b hb).1
  · intro ε hε
    let K := ⌈3*(D:ℝ)/ε⌉₊+1
    have hK : 0<K := Nat.succ_pos _
    refine ⟨K^2,fun B hb => (rows_tail hb K hK).trans ?_⟩
    apply (div_le_iff₀ (Nat.cast_pos.mpr hK)).2
    have hk : 3*(D:ℝ)/ε ≤ K := (Nat.le_ceil _).trans (Nat.cast_le.mpr (Nat.le_succ _))
    linarith only [(div_le_iff₀ hε).1 hk]

/-- A primitive table records the possible pairs (p,r) for each smaller
split prime q. The cofactor multiplying p and qr is unrestricted. -/
def primitiveIsolated (table : ℕ → Finset (ℕ × ℕ)) (X : ℕ) :=
  (squarefreeOf (Ioc X (2*X))).filter (fun n =>
    ∀ q : ℕ, ∀ a ∈ table q, ¬a.1 ∣ n ∧ ¬q*a.2 ∣ n)

/-- Every sufficiently large octave has a positive proportion of squarefree
vertices incident to no exchange whenever each smaller split prime allows
at most D distinct primitive types, even for tables varying with X. -/
theorem positive_density_isolated_of_bounded_types (D : ℕ) :
    ∃ δ : ℝ, 0<δ ∧ ∀ᶠ X : ℕ in atTop, ∀ table : ℕ → Finset (ℕ × ℕ),
      (∀ q, (table q).card ≤ D ∧ ∀ a ∈ table q,
        q.Prime ∧ a.1.Prime ∧ a.2.Prime ∧ q<a.2 ∧ q*a.2 ≤ 2*a.1) →
      δ*X ≤ ((primitiveIsolated table X).card:ℝ) := by
  obtain ⟨δ,hδ,h⟩ := rows_density (2*D+1)
  refine ⟨δ,hδ,?_⟩
  filter_upwards [h] with X hX
  intro table ht
  let single (q : ℕ) := (table q).image Prod.fst
  let product (q : ℕ) := (table q).image (fun a => q*a.2)
  let squares (q : ℕ) : Finset ℕ := if 1<q then {q*q} else ∅
  let rows (q : ℕ) := (single q ∪ product q) ∪ squares q
  let S := Icc 1 (2*X)
  let B := S.biUnion rows
  have square_le {q : ℕ} {a : ℕ × ℕ} (ha : a ∈ table q) :
      q^2 ≤ q*a.2 ∧ q^2 ≤ 2*a.1 := by
    obtain ⟨_,_,_,hh,hprice⟩ := (ht q).2 a ha
    have hle : q^2 ≤ q*a.2 := by rw [pow_two]; exact Nat.mul_le_mul_left _ hh.le
    exact ⟨hle,hle.trans hprice⟩
  have hB : B ∈ divisorRows (2*D+1) := by
    refine ⟨2*X,rows,rfl,fun q _ => ⟨?_,?_⟩⟩
    · have hc : (squares q).card ≤ 1 := by dsimp [squares]; split_ifs <;> simp
      have hp : (single q).card ≤ D := card_image_le.trans (ht q).1
      have hw : (product q).card ≤ D := card_image_le.trans (ht q).1
      exact (card_union_le ..).trans (by have := card_union_le (single q) (product q); omega)
    · intro b hb
      rcases mem_union.mp hb with he | hsq
      · rcases mem_union.mp he with hp | hw
        · obtain ⟨a,ha,rfl⟩ := mem_image.mp hp
          exact ⟨((ht q).2 a ha).2.1.one_lt,(square_le ha).2⟩
        · obtain ⟨a,ha,rfl⟩ := mem_image.mp hw
          obtain ⟨hq,_,hr,_,_⟩ := (ht q).2 a ha
          have hpos := Nat.le_mul_of_pos_right q hr.pos
          exact ⟨hq.one_lt.trans_le hpos,(square_le ha).1.trans (by omega)⟩
      · change b ∈ (if 1<q then {q*q} else ∅ : Finset ℕ) at hsq
        split_ifs at hsq with hq
        · obtain rfl := mem_singleton.mp hsq
          have hbig := Nat.le_mul_of_pos_right q (zero_lt_one.trans hq)
          exact ⟨hq.trans_le hbig,by rw [pow_two]; omega⟩
        · exact (notMem_empty _ hsq).elim
  apply (hX B hB).trans
  apply Nat.cast_le.mpr (card_le_card ?_)
  intro n hn
  obtain ⟨hV,hfree⟩ := mem_filter.mp hn
  obtain ⟨hnL,hnU⟩ := mem_Ioc.mp hV
  have hn0 : 0<n := by omega
  have hs : Squarefree n := Nat.squarefree_iff_prime_squarefree.mpr fun q hq hd => by
    have hle := (Nat.le_mul_of_pos_right q hq.pos).trans ((Nat.le_of_dvd hn0 hd).trans hnU)
    have hmem : q*q ∈ squares q := by simp [squares,hq.one_lt]
    exact hfree _ (mem_biUnion.mpr ⟨q,mem_Icc.mpr ⟨hq.pos,hle⟩,mem_union_right _ hmem⟩) hd
  refine mem_filter.mpr ⟨mem_filter.mpr ⟨hV,hs⟩,fun q a ha => ?_⟩
  obtain ⟨hq,_,hr,_,_⟩ := (ht q).2 a ha
  have hsmall : q ≤ a.1 := by
    have hl : 2*q ≤ q^2 := by rw [pow_two]; exact Nat.mul_le_mul_right q hq.two_le
    have hh := hl.trans (square_le ha).2
    omega
  have inB {b : ℕ} (hqb : q ≤ b) (hb : b ∈ rows q) (hd : b ∣ n) : False :=
    hfree b (mem_biUnion.mpr ⟨q,mem_Icc.mpr ⟨hq.pos,hqb.trans ((Nat.le_of_dvd hn0 hd).trans hnU)⟩,hb⟩) hd
  exact ⟨inB hsmall (mem_union_left _ (mem_union_left _ (mem_image_of_mem _ ha))),
    inB (Nat.le_mul_of_pos_right _ hr.pos) (mem_union_left _ (mem_union_right _ (mem_image_of_mem _ ha)))⟩

/-- On each large octave, one short matching escapes every table with the
prescribed bound on the number of primitive types per smaller split prime.
The table is allowed to be chosen after the matching. -/
theorem density_one_requires_growing_type_multiplicity (D : ℕ) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ X : ℕ in atTop, ∃ M : OppositeParityMatching GlobalDyadicOneTwoRel (Ioc X (2*X)),
      (M.unmatchedSet.card:ℝ) ≤ ε*X ∧ (∀ n ∈ M.sources, |(M.partner n:ℝ)-n| ≤ ε*X) ∧
      ∀ table : ℕ → Finset (ℕ × ℕ), (∀ q, (table q).card ≤ D ∧ ∀ a ∈ table q,
        q.Prime ∧ a.1.Prime ∧ a.2.Prime ∧ q<a.2 ∧ q*a.2 ≤ 2*a.1) →
        ∃ n ∈ primitiveIsolated table X,n ∈ M.sources ∪ M.targets := by
  obtain ⟨δ,hδ,h⟩ := positive_density_isolated_of_bounded_types D
  let η := min ε (δ/2)
  have hη : 0<η := lt_min hε (half_pos hδ)
  filter_upwards [h,density_one_restricted_matching hη,eventually_ge_atTop 1] with X hx hm hX
  obtain ⟨M,hM,hd⟩ := hm
  have hh : η*X ≤ ε*X := mul_le_mul_of_nonneg_right (min_le_left ..) (Nat.cast_nonneg X)
  refine ⟨M,hM.trans hh,fun n hn => (hd n hn).trans hh,fun table ht => ?_⟩
  by_contra! hbad
  have sub : primitiveIsolated table X ⊆ M.unmatchedSet := fun n hn =>
    Finset.mem_sdiff.mpr ⟨(mem_filter.mp hn).1,hbad n hn⟩
  have upper := (Nat.cast_le (α := ℝ)).mpr (card_le_card sub)
  have lower := hx table ht
  have hlt := mul_lt_mul_of_pos_right (lt_of_le_of_lt (min_le_right ε (δ/2)) (half_lt_self hδ))
    (show (0:ℝ)<X by exact_mod_cast hX)
  exact (hlt.not_ge (lower.trans (upper.trans hM)))

end GaloisForLFunctions.RestrictedFactorizationCalculus
