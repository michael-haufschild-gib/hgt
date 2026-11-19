import GaloisForLFunctions.RestrictedFactorizationCalculus.PrescribingTheSquarefreeFixedVertices
import GaloisForLFunctions.RestrictedFactorizationCalculus.ArbitrarilySlowSignedCrossingsOnOneDenseMatching
import GaloisForLFunctions.RestrictedFactorizationCalculus.TheExplicitLogSquareRoughSet

/-!
# The signed charge of arbitrarily long exchanges

A perfect matching can carry the Mertens growth exponent on the crossing
edges whose upper endpoints exceed any prescribed growth law. The lower
endpoints of these edges have density zero. The comparison with the fixed
charge before completion loses at most the changed old crossings and a
finite set of old long edges.
-/

noncomputable section

open Finset Filter
open ArithmeticFunction hiding id
open scoped Classical ArithmeticFunction.Moebius
open GaloisForLFunctions.QuantitativeFactorizationMatching GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

/-- Charge of the crossing lower endpoints whose partners exceed D(n). -/
def longCrossingCharge (D G : ℕ → ℕ) (X : ℕ) :=
  ∑ n ∈ (Icc 1 X).filter (fun n => max X (D n)<G n),(μ n:ℝ)

private def crossingRow (F : ℕ → ℕ) (X : ℕ) := (Icc 1 X).filter (fun n => X<F n)
private def shortRow (D G : ℕ → ℕ) (X : ℕ) :=
  (crossingRow G X).filter (fun n => G n ≤ D n)

private theorem split_crossing (D G : ℕ → ℕ) (X : ℕ) :
    longCrossingCharge D G X+(∑ n ∈ shortRow D G X,(μ n:ℝ))=crossingSignedPrefix G X := by
  let S := crossingRow G X
  have h : (Icc 1 X).filter (fun n => max X (D n)<G n)=S.filter (fun n => ¬G n ≤ D n) := by
    ext n
    simp only [S,crossingRow,mem_filter,max_lt_iff,not_le,and_assoc]
  unfold longCrossingCharge
  rw [h,add_comm]
  exact sum_filter_add_sum_filter_not S (fun n => G n ≤ D n) _

private theorem retained_short {F G D : ℕ → ℕ} (sep : ∀ n,n<G n → G n=F n ∨ D n<G n)
    (X : ℕ) : shortRow D G X ⊆ crossingRow F X := by
  intro n hn
  obtain ⟨hc,hs⟩ := mem_filter.mp hn
  obtain ⟨hi,hup⟩ := mem_filter.mp hc
  rcases sep n ((mem_Icc.mp hi).2.trans_lt hup) with he | hl
  · exact mem_filter.mpr ⟨hi,by rwa [←he]⟩
  · exact (hs.not_gt hl).elim

/-- Lost original crossings give the exact signed error when the old fixed
population is transferred to the long edges of a perfect completion. -/
theorem fixed_charge_transferred_to_long_edges (F G D : ℕ → ℕ)
    (lawF : ∀ n, F (F n)=n ∧ (F n=n ∨ GlobalDyadicOneTwoRel n (F n)))
    (lawG : ∀ n, G (G n)=n ∧ (G n=n ∨ GlobalDyadicOneTwoRel n (G n)))
    (cover : ∀ n,Squarefree n → 1<n → G n ≠ n)
    (sep : ∀ n,n<G n → G n=F n ∨ D n<G n) (X : ℕ) :
    longCrossingCharge D G X=fixedSignedPrefix F X-(if X=0 then 0 else 1)+
      ∑ n ∈ ((Icc 1 X).filter (fun n => X<F n)) \
        (((Icc 1 X).filter (fun n => X<G n)).filter (fun n => G n ≤ D n)),(μ n:ℝ) := by
  have hF := fixed_add_crossing F (fun n _ => lawF n) X
  have hG := fixed_add_crossing G (fun n _ => lawG n) X
  rw [only_unit_charge (restricted_unit_is_fixed G (fun n => (lawG n).2)) cover] at hG
  have hs := split_crossing D G X
  have hd := sum_sdiff (f := fun n => (μ n:ℝ)) (retained_short sep X)
  change (∑ n ∈ crossingRow F X \ shortRow D G X,(μ n:ℝ))+
      (∑ n ∈ shortRow D G X,(μ n:ℝ))=crossingSignedPrefix F X at hd
  change _=_+∑ n ∈ crossingRow F X \ shortRow D G X,(μ n:ℝ)
  linarith only [hF,hG,hs,hd]

private def changedOld (F G : ℕ → ℕ) (X : ℕ) :=
  (Icc 1 X).filter (fun n => F n ≠ n ∧ G n ≠ F n)

private theorem lost_count {F G D : ℕ → ℕ} {A : ℕ} (short : ∀ n,A ≤ n → F n ≤ D n) (X : ℕ) :
    (crossingRow F X \ shortRow D G X).card ≤ (changedOld F G X).card+A := by
  have sub : crossingRow F X \ shortRow D G X ⊆ changedOld F G X ∪ range A := by
    intro n hn
    obtain ⟨hc,hnc⟩ := mem_sdiff.mp hn
    obtain ⟨hi,hup⟩ := mem_filter.mp hc
    by_cases hnA : n<A
    · exact mem_union_right _ (mem_range.mpr hnA)
    apply mem_union_left
    refine mem_filter.mpr ⟨hi,((mem_Icc.mp hi).2.trans_lt hup).ne',?_⟩
    intro eq
    exact hnc (mem_filter.mpr ⟨mem_filter.mpr ⟨hi,by rwa [eq]⟩,by rw [eq]; exact short n (le_of_not_gt hnA)⟩)
  simpa only [card_range] using (card_le_card sub).trans (card_union_le ..)

private theorem long_population {F G D : ℕ → ℕ} {A : ℕ} (short : ∀ n,A ≤ n → F n ≤ D n)
    (hnD : ∀ n,n ≤ D n) (law : ∀ n,G n=n ∨ GlobalDyadicOneTwoRel n (G n)) (X : ℕ) :
    ((Icc 1 X).filter (fun n => D n<G n)).card ≤
      (prefixUnpaid F X).card+(changedOld F G X).card+A := by
  have sub : (Icc 1 X).filter (fun n => D n<G n) ⊆
      (prefixUnpaid F X ∪ changedOld F G X) ∪ range A := by
    intro n hn
    obtain ⟨hi,hl⟩ := mem_filter.mp hn
    by_cases early : n<A
    · exact mem_union_right _ (mem_range.mpr early)
    have hm := (hnD n).trans_lt hl
    have hs := (law n).resolve_left hm.ne'
    apply mem_union_left
    by_cases hf : F n=n
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_filter.mpr ⟨hi,hs.1⟩,Or.inl hf⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hi,hf,fun he => hl.not_ge (he.trans_le (short n (le_of_not_gt early)))⟩)
  simpa only [card_range] using (card_le_card sub).trans
    ((card_union_le ..).trans (Nat.add_le_add_right (card_union_le ..) _))

private theorem power_congr {t : ℝ} {f g : ℕ → ℝ} (err : PrefixPower t (fun X => f X-g X)) :
    PrefixPower t f ↔ PrefixPower t g := by
  obtain ⟨K,hK,he⟩ := err
  constructor
  · rintro ⟨C,hC,h⟩
    refine ⟨C+K,add_nonneg hC hK,fun X => ?_⟩
    have hh := abs_sub (f X) (f X-g X)
    rw [show f X-(f X-g X)=g X by ring] at hh
    rw [add_mul]; exact hh.trans (add_le_add (h X) (he X))
  · rintro ⟨C,hC,h⟩
    refine ⟨C+K,add_nonneg hC hK,fun X => ?_⟩
    have hh := abs_add_le (g X) (f X-g X)
    rw [show g X+(f X-g X)=f X by ring] at hh
    rw [add_mul]; exact hh.trans (add_le_add (h X) (he X))

/-- Prefix of the union of the full orbits with upper endpoint above the
prescribed threshold at the lower endpoint. -/
def longEndpoints (D G : ℕ → ℕ) (X : ℕ) :=
  (Icc 1 X).filter (fun n => D n<G n ∨ D (G n)<n)

/-- The signed population of long orbits is exactly their sharp crossing
charge. Both endpoints of every completed edge cancel. -/
theorem long_orbit_prefix (D G : ℕ → ℕ) (hnD : ∀ n,n ≤ D n)
    (hG : ∀ n,G (G n)=n ∧ (G n=n ∨ GlobalDyadicOneTwoRel n (G n))) (X : ℕ) :
    (∑ n ∈ longEndpoints D G X,(μ n:ℝ))=longCrossingCharge D G X ∧
    (longEndpoints D G X).card ≤ 2*((Icc 1 X).filter (fun n => D n<G n)).card := by
  let A := (Icc 1 X).filter (fun n => D n<G n)
  let P := A.filter (fun n => G n ≤ X)
  have back := fun n => (hG n).1
  have upper (n : ℕ) (h : n ∈ P) : G n ∈ Icc 1 X ∧ D (G (G n))<G n := by
    obtain ⟨ha,hx⟩ := mem_filter.mp h
    obtain ⟨hi,hl⟩ := mem_filter.mp ha
    exact ⟨mem_Icc.mpr ⟨(mem_Icc.mp hi).1.trans ((hnD n).trans hl.le),hx⟩,by rwa [back]⟩
  have he : longEndpoints D G X=A ∪ P.image G := by
    ext n
    constructor
    · intro h
      obtain ⟨hi,hl | hu⟩ := mem_filter.mp h
      · exact mem_union_left _ (mem_filter.mpr ⟨hi,hl⟩)
      · have hdown := (hnD (G n)).trans_lt hu
        have edge := (hG n).2.resolve_left hdown.ne
        apply mem_union_right
        refine mem_image.mpr ⟨G n,mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr
          ⟨Nat.pos_of_ne_zero edge.2.1.ne_zero,hdown.le.trans (mem_Icc.mp hi).2⟩,?_⟩,?_⟩,back n⟩
        · rwa [back]
        · rw [back]; exact (mem_Icc.mp hi).2
    · intro h
      rcases mem_union.mp h with ha | hb
      · exact mem_filter.mpr ⟨(mem_filter.mp ha).1,Or.inl (mem_filter.mp ha).2⟩
      obtain ⟨m,hm,rfl⟩ := mem_image.mp hb
      exact mem_filter.mpr ⟨(upper m hm).1,Or.inr (upper m hm).2⟩
  have dis : Disjoint A (P.image G) := by
    apply disjoint_left.mpr
    intro n hn h
    obtain ⟨m,hm,rfl⟩ := mem_image.mp h
    have h1 := (hnD (G m)).trans_lt (mem_filter.mp hn).2
    rw [back] at h1
    exact h1.not_ge ((hnD m).trans (mem_filter.mp (mem_filter.mp hm).1).2.le)
  have inj : Function.Injective G := (show Function.Involutive G from back).injective
  have hsign : (∑ n ∈ P.image G,(μ n:ℝ))= -(∑ n ∈ P,(μ n:ℝ)) := by
    rw [sum_image (fun _ _ _ _ h => inj h),←sum_neg_distrib]
    apply sum_congr rfl
    intro n hn
    have hup := (hnD n).trans_lt (mem_filter.mp (mem_filter.mp hn).1).2
    have edge := (hG n).2.resolve_left hup.ne'
    have hh := edge.2.2.1
    exact_mod_cast (show μ (G n)= -μ n by omega)
  have hset : (Icc 1 X).filter (fun n => max X (D n)<G n)=A \ P := by
    ext n
    simp only [A,P,mem_filter,max_lt_iff,mem_sdiff,not_and,not_le]
    omega
  rw [he]
  constructor
  · rw [sum_union dis,hsign,longCrossingCharge,hset,sum_sdiff_eq_sub (filter_subset ..)]
    ring
  · exact (card_union_le ..).trans ((Nat.add_le_add_left
      (card_image_le.trans (card_le_card (filter_subset ..))) _).trans_eq (two_mul _).symm)

private theorem close_charges {F G D : ℕ → ℕ} {A : ℕ}
    (hs : ∀ n,A ≤ n → F n ≤ D n)
    (hf : ∀ n,F (F n)=n ∧ (F n=n ∨ GlobalDyadicOneTwoRel n (F n)))
    (hg : ∀ n,G (G n)=n ∧ (G n=n ∨ GlobalDyadicOneTwoRel n (G n)))
    (cover : ∀ n,Squarefree n → 1<n → G n ≠ n)
    (sep : ∀ n,n<G n → G n=F n ∨ D n<G n)
    (X : ℕ) : |longCrossingCharge D G X-fixedSignedPrefix F X| ≤
      1+(changedOld F G X).card+A := by
  have he := fixed_charge_transferred_to_long_edges F G D hf hg cover sep X
  let S := crossingRow F X \ shortRow D G X
  have hsum : |∑ n ∈ S,(μ n:ℝ)| ≤ (S.card:ℝ) := calc
    _ ≤ ∑ n ∈ S,|(μ n:ℝ)| := abs_sum_le_sum_abs ..
    _ ≤ ∑ _n ∈ S,(1:ℝ) := sum_le_sum fun n _ => by exact_mod_cast abs_moebius_le_one (n := n)
    _ = _ := by simp
  have hcap : (S.card:ℝ) ≤ (changedOld F G X).card+(A:ℝ) := by exact_mod_cast lost_count (G := G) hs X
  let u : ℝ := if X=0 then 0 else 1
  have hu : |u| ≤ 1 := by dsimp only [u]; split <;> norm_num
  change longCrossingCharge D G X=fixedSignedPrefix F X-u+∑ n ∈ S,(μ n:ℝ) at he
  rw [show longCrossingCharge D G X-fixedSignedPrefix F X=(∑ n ∈ S,(μ n:ℝ))-u by linarith only [he]]
  exact (abs_sub ..).trans (by linarith only [hu,hsum,hcap])

/-- For any required separation T, one perfect matching carries the
Mertens prefix on the complete orbits with upper endpoint exceeding
max(2n,T(n)) at the lower endpoint n. Every growing error envelope is
attainable, and both these orbits and the unpaid vertices have density zero. -/
theorem arbitrarily_slow_error_on_arbitrarily_long_orbits (T : ℕ → ℕ) (w : ℕ → ℝ)
    (pos : ∀ n,0 ≤ w n) (top : Tendsto w atTop atTop) :
    let D := fun n => max (2*n) (T n)
    ∃ G : ℕ → ℕ,(∀ n,G (G n)=n ∧ (G n=n ∨ GlobalDyadicOneTwoRel n (G n))) ∧
      (∀ n,Squarefree n → 1<n → G n ≠ n) ∧
      (∀ ε : ℝ,0<ε → ∀ᶠ X : ℕ in atTop,((prefixUnpaid G X).card:ℝ) ≤ ε*X ∧
        ((longEndpoints D G X).card:ℝ) ≤ ε*X) ∧
      ∀ᶠ X : ℕ in atTop,|longCrossingCharge D G X-coprimeMoebiusSum 1 X| ≤ w X := by
  let D := fun n : ℕ => max (2*n) (T n)
  have hD (n : ℕ) : n ≤ D n := (by omega : n ≤ 2*n).trans (le_max_left ..)
  let v := fun n : ℕ => w n/4
  have vt : Tendsto v atTop atTop := tendsto_atTop.mpr (fun c =>
    (top.eventually_ge_atTop (4*c)).mono (fun n hn => by dsimp only [v]; linarith only [hn]))
  obtain ⟨F,hF,small,track⟩ := arbitrarily_slow_signed_crossings v (fun n => div_nonneg (pos n) (by norm_num)) vt
  obtain ⟨V,price⟩ := separation_threshold_within_envelope w pos top
  let B := fun n => max (D n) (V n)
  obtain ⟨A,hA⟩ := eventually_atTop.mp (small 1 zero_lt_one)
  have short (n : ℕ) (hn : A ≤ n) : F n ≤ D n := by
    have hh := (le_abs_self _).trans (hA n hn).2
    exact (show F n ≤ 2*n by exact_mod_cast (show (F n:ℝ) ≤ 2*n by linarith only [hh])).trans (le_max_left ..)
  obtain ⟨G,back,legal,cover,paid,separate,changed⟩ := perfect_completion_with_separated_edges F
    (fun n => (hF n).1) (fun n => (hF n).2) B
  have law := fun n => And.intro (back n) (legal n)
  have sep (n : ℕ) (h : n<G n) : G n=F n ∨ D n<G n :=
    (separate n h).imp_right (fun z => (le_max_left ..).trans_lt z)
  let cost := fun X => ((range (X+1)).filter (fun k => V k<X)).card
  have repairs (X : ℕ) : (changedOld F G X).card ≤ 2*cost X := by
    apply (changed X).trans (Nat.mul_le_mul_left 2 (card_le_card ?_))
    intro n hn
    exact mem_filter.mpr ⟨(mem_filter.mp hn).1,(le_max_right ..).trans_lt (mem_filter.mp hn).2⟩
  refine ⟨G,law,cover,?_,?_⟩
  · intro ε hε
    have ht : 0<ε/10 := div_pos hε (by norm_num)
    filter_upwards [small (ε/10) ht,square_root_repair_cost_is_sublinear ht,
      tendsto_natCast_atTop_atTop.eventually_ge_atTop ((A:ℝ)/(ε/10))] with X hsmall hs ha
    have early := (div_le_iff₀ ht).mp ha
    have costX := (Nat.cast_le (α := ℝ)).mpr ((repairs X).trans (Nat.mul_le_mul_left 2 (price X).2))
    have pop := (Nat.cast_le (α := ℝ)).mpr ((long_orbit_prefix D G hD law X).2.trans
      (Nat.mul_le_mul_left 2 (long_population short hD legal X)))
    push_cast only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at costX pop
    have paidX := (Nat.cast_le (α := ℝ)).mpr (paid X)
    have nn := mul_nonneg hε.le (Nat.cast_nonneg (α := ℝ) X)
    exact ⟨by linarith only [paidX,hsmall.1,nn],by linarith only [pop,costX,hsmall.1,hs,early,nn]⟩
  filter_upwards [top.eventually_ge_atTop (4*((A:ℝ)+1))] with X enough
  have near := close_charges short hF law cover sep X
  have costX := (Nat.cast_le (α := ℝ)).mpr (repairs X)
  push_cast only [Nat.cast_mul,Nat.cast_ofNat] at costX
  have old := (track X).2
  rw [abs_sub_comm] at old
  have tri := abs_sub_le (longCrossingCharge D G X) (fixedSignedPrefix F X) (coprimeMoebiusSum 1 X)
  change |fixedSignedPrefix F X-coprimeMoebiusSum 1 X| ≤ w X/4 at old
  linarith only [tri,near,old,costX,(price X).1,enough]

/-- One choice detects every positive power, including the exact
endpoint whenever attained. -/
theorem the_mertens_abscissa_on_arbitrarily_long_edges (T : ℕ → ℕ) :
    let D := fun n => max (2*n) (T n)
    ∃ G : ℕ → ℕ,(∀ n,G (G n)=n ∧ (G n=n ∨ GlobalDyadicOneTwoRel n (G n))) ∧
      (∀ n,Squarefree n → 1<n → G n ≠ n) ∧
      (∀ ε : ℝ,0<ε → ∀ᶠ X : ℕ in atTop,((prefixUnpaid G X).card:ℝ) ≤ ε*X ∧
        ((longEndpoints D G X).card:ℝ) ≤ ε*X) ∧
      ∀ t : ℝ,0<t → (PrefixPower t (longCrossingCharge D G) ↔ PrefixPower t (coprimeMoebiusSum 1)) := by
  let D := fun n : ℕ => max (2*n) (T n)
  let w := fun X : ℕ => Real.log X
  have pos (X : ℕ) : 0 ≤ w X := by
    rcases Nat.eq_zero_or_pos X with z | h
    · simp [w,z]
    · exact Real.log_nonneg (Nat.one_le_cast.mpr h)
  obtain ⟨G,law,cover,small,err⟩ := arbitrarily_slow_error_on_arbitrarily_long_orbits T w pos
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  refine ⟨G,law,cover,small,?_⟩
  intro t ht
  apply power_congr
  apply prefixPower_of_eventual (C := 1/t) (by simp [longCrossingCharge,coprimeMoebiusSum]) ht
  filter_upwards [err] with X e
  exact e.trans ((Real.log_le_rpow_div (Nat.cast_nonneg _) ht).trans_eq (by ring))

/-- The square-root-plus-epsilon criterion on one density-zero union of
arbitrarily long two-cycles, using every sharp prefix of their endpoints. -/
theorem square_root_on_arbitrarily_long_exchanges (T : ℕ → ℕ) :
    let D := fun n => max (2*n) (T n)
    ∃ G : ℕ → ℕ, (∀ n,G (G n)=n ∧ (G n=n ∨ GlobalDyadicOneTwoRel n (G n))) ∧
      (∀ n,Squarefree n → 1<n → G n ≠ n) ∧
      (∀ ε : ℝ,0<ε → ∀ᶠ X : ℕ in atTop, ((prefixUnpaid G X).card:ℝ) ≤ ε*X ∧
        ((longEndpoints D G X).card:ℝ) ≤ ε*X) ∧
      ((∀ ε : ℝ,0<ε → PrefixPower (1/2+ε) (fun X => ∑ n ∈ longEndpoints D G X,(μ n:ℝ))) ↔
       ∀ ε : ℝ,0<ε → PrefixPower (1/2+ε) (coprimeMoebiusSum 1)) := by
  let D := fun n : ℕ => max (2*n) (T n)
  obtain ⟨G,hG,hcover,hcount,h⟩ := the_mertens_abscissa_on_arbitrarily_long_edges T
  have eq : (fun X => ∑ n ∈ longEndpoints D G X,(μ n:ℝ))=longCrossingCharge D G :=
    funext (fun X => (long_orbit_prefix D G (fun n => (by omega : n ≤ 2*n).trans (le_max_left ..)) hG X).1)
  refine ⟨G,hG,hcover,hcount,?_⟩
  change (∀ ε : ℝ,0<ε → PrefixPower (1/2+ε) (fun X => ∑ n ∈ longEndpoints D G X,(μ n:ℝ))) ↔ _
  rw [eq]
  constructor
  · exact fun hh ε hε => (h _ (by linarith only [hε] : (0:ℝ)<1/2+ε)).1 (hh ε hε)
  · exact fun hh ε hε => (h _ (by linarith only [hε] : (0:ℝ)<1/2+ε)).2 (hh ε hε)

#print axioms arbitrarily_slow_error_on_arbitrarily_long_orbits
#print axioms fixed_charge_transferred_to_long_edges
#print axioms long_orbit_prefix
#print axioms the_mertens_abscissa_on_arbitrarily_long_edges
#print axioms square_root_on_arbitrarily_long_exchanges

end GaloisForLFunctions.RestrictedFactorizationCalculus
