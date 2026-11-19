import GaloisForLFunctions.RestrictedFactorizationCalculus.TheSignedCrossingsBetweenTwoWalls

/-!
# The Mertens abscissa on the fixed set of one involution

Successive blocks retain an entire divisor table between two walls. The
crossing charge localizes to the block containing the observation point.
A protected interior cutoff preserves a large signed witness exactly.
-/

noncomputable section

open Finset Filter
open ArithmeticFunction hiding id
open scoped Classical ArithmeticFunction.Moebius
open GaloisForLFunctions.QuantitativeFactorizationMatching GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

/-- The interval between two consecutive integer walls, open on the left. -/
def InBlock (L : ℕ → ℕ) (j n : ℕ) := L j<n ∧ n ≤ L (j+1)

private theorem block_unique {L : ℕ → ℕ} (hL : Monotone L) {n i j : ℕ}
    (hi : InBlock L i n) (hj : InBlock L j n) : i=j := by
  rcases lt_trichotomy i j with h | h | h
  · exact False.elim (hj.1.not_ge (hi.2.trans (hL h)))
  · exact h
  · exact False.elim (hi.1.not_ge (hj.2.trans (hL h)))

/-- Apply the table of the containing interval when the partner lies in the same interval. -/
def blockSwitch (L : ℕ → ℕ) (F : ℕ → ℕ → ℕ) (n : ℕ) : ℕ :=
  if h : ∃ j,InBlock L j n then
    if InBlock L h.choose (F h.choose n) then F h.choose n else n
  else n

/-- On an occupied block the global switch reads only its own table. -/
theorem block_eval {L : ℕ → ℕ} (hL : Monotone L) (F : ℕ → ℕ → ℕ)
    {j n : ℕ} (hn : InBlock L j n) :
    blockSwitch L F n=if InBlock L j (F j n) then F j n else n := by
  have h : ∃ i,InBlock L i n := ⟨j,hn⟩
  rw [blockSwitch,dif_pos h,block_unique hL h.choose_spec hn]

/-- Clipping both ends of a restricted involution preserves its involution law. -/
theorem block_law {L : ℕ → ℕ} (hL : Monotone L) {F : ℕ → ℕ → ℕ}
    (law : ∀ j n,Squarefree n → F j (F j n)=n ∧ (F j n=n ∨ GlobalDyadicOneTwoRel n (F j n)))
    (n : ℕ) (hs : Squarefree n) :
    blockSwitch L F (blockSwitch L F n)=n ∧
      (blockSwitch L F n=n ∨ GlobalDyadicOneTwoRel n (blockSwitch L F n)) := by
  by_cases h : ∃ j,InBlock L j n
  · obtain ⟨j,hj⟩ := h
    by_cases hn : InBlock L j (F j n)
    · obtain ⟨hback,hedge⟩ := law j n hs
      rw [block_eval hL F hj,if_pos hn,block_eval hL F hn,hback,if_pos hj]
      exact ⟨rfl,hedge⟩
    · have he := (block_eval hL F hj).trans (if_neg hn)
      exact ⟨(congrArg _ he).trans he,Or.inl he⟩
  · have he : blockSwitch L F n=n := dif_neg h
    exact ⟨(congrArg _ he).trans he,Or.inl he⟩

/-- Only the block containing the cutoff can supply a crossing. -/
theorem block_crossings {L : ℕ → ℕ} (hL : Monotone L) (F : ℕ → ℕ → ℕ)
    {j X : ℕ} (hx : InBlock L j X) :
    (Icc 1 X).filter (fun n => X<blockSwitch L F n)=wallCrossings (F j) (L j) (L (j+1)) X := by
  ext n
  constructor
  · intro hn
    obtain ⟨hi,hedge⟩ := mem_filter.mp hn
    have hcap := (mem_Icc.mp hi).2
    by_cases hm : ∃ k,InBlock L k n
    · obtain ⟨k,hk⟩ := hm
      rw [block_eval hL F hk] at hedge
      split at hedge
      next hp =>
        have hkX : InBlock L k X := ⟨hk.1.trans_le hcap,hedge.le.trans hp.2⟩
        obtain rfl := block_unique hL hkX hx
        exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hk.1,hcap⟩,hedge,hp.2⟩
      next => exact False.elim (hcap.not_gt hedge)
    · rw [blockSwitch,dif_neg hm] at hedge
      exact False.elim (hcap.not_gt hedge)
  · intro hn
    obtain ⟨hi,hedge,hstop⟩ := mem_filter.mp hn
    obtain ⟨hl,hcap⟩ := mem_Ioc.mp hi
    have hnb : InBlock L j n := ⟨hl,hcap.trans hx.2⟩
    have hpb : InBlock L j (F j n) := ⟨hx.1.trans hedge,hstop⟩
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(Nat.zero_le _).trans_lt hl,hcap⟩,by
      rw [block_eval hL F hnb,if_pos hpb]; exact hedge⟩

/-- A left-wall loss can be charged injectively to its partner at that wall.
Every other unpaid vertex of the new block is already unpaid at the observation point. -/
private theorem block_unpaid {L : ℕ → ℕ} (hL : Monotone L) {F : ℕ → ℕ → ℕ}
    (law : ∀ j n,Squarefree n → F j (F j n)=n ∧ (F j n=n ∨ GlobalDyadicOneTwoRel n (F j n)))
    {j X : ℕ} (hx : InBlock L j X) :
    (prefixUnpaid (blockSwitch L F) X).card ≤
      (prefixUnpaid (blockSwitch L F) (L j)).card+(prefixUnpaid (F j) X).card+
      (prefixUnpaid (F j) (L j)).card := by
  let H := blockSwitch L F
  let A := prefixUnpaid H (L j)
  let B := prefixUnpaid (F j) X
  let C := prefixUnpaid (F j) (L j)
  have sub : prefixUnpaid H X ⊆ (A ∪ B) ∪ C.image (F j) := by
    intro n hn
    obtain ⟨hs,hu⟩ := mem_filter.mp hn
    obtain ⟨hi,hsq⟩ := mem_filter.mp hs
    obtain ⟨hp,hcap⟩ := mem_Icc.mp hi
    by_cases hlow : n ≤ L j
    · apply mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨hp,hlow⟩,hsq⟩,?_⟩))
      exact hu.imp_right (fun h => hx.1.trans h)
    have hblock : InBlock L j n := ⟨lt_of_not_ge hlow,hcap.trans hx.2⟩
    by_cases hfull : F j n=n ∨ X<F j n
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hs,hfull⟩))
    have hd := fun h => hfull (Or.inl h)
    have hcut : F j n ≤ X := le_of_not_gt (fun h => hfull (Or.inr h))
    obtain ⟨hr,he⟩ := law j n hsq
    have edge := he.resolve_left hd
    have hbottom : F j n ≤ L j := by
      by_contra! h
      have hm : InBlock L j (F j n) := ⟨h,hcut.trans hx.2⟩
      have eval : H n=F j n := (block_eval hL F hblock).trans (if_pos hm)
      exact hfull (eval ▸ hu)
    apply mem_union_right _ (mem_image.mpr ⟨F j n,?_,hr⟩)
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr edge.2.1.ne_zero,hbottom⟩,edge.2.1⟩,
      Or.inr (by rw [hr]; exact hblock.1)⟩
  exact (card_le_card sub).trans ((card_union_le ..).trans (Nat.add_le_add (card_union_le ..) card_image_le))

private theorem protected_fixed {L : ℕ → ℕ} (hL : Monotone L) {F : ℕ → ℕ → ℕ}
    (law : ∀ j n,Squarefree n → F j (F j n)=n ∧ (F j n=n ∨ GlobalDyadicOneTwoRel n (F j n)))
    {j X : ℕ} (left : 2*L j<X) (right : 2*X ≤ L (j+1))
    (short : ∀ n,Squarefree n → F j n ≤ 2*n) :
    fixedSignedPrefix (blockSwitch L F) X=fixedSignedPrefix (F j) X := by
  have hx : InBlock L j X := ⟨by omega,by omega⟩
  have eqc : crossingSignedPrefix (blockSwitch L F) X=crossingSignedPrefix (F j) X := by
    unfold crossingSignedPrefix
    rw [block_crossings hL F hx]
    apply sum_subset
    · intro n hn
      obtain ⟨hi,h,_⟩ := mem_filter.mp hn
      obtain ⟨hl,hu⟩ := mem_Ioc.mp hi
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(Nat.zero_le _).trans_lt hl,hu⟩,h⟩
    · intro n hn hno
      obtain ⟨hi,h⟩ := mem_filter.mp hn
      have hu := (mem_Icc.mp hi).2
      have hns : ¬Squarefree n := by
        intro hs
        have hnear := short n hs
        exact hno (mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega,hu⟩,h,by omega⟩)
      rw [moebius_eq_zero_of_not_squarefree hns,Int.cast_zero]
  have h1 := fixed_add_crossing _ (block_law hL law) X
  have h2 := fixed_add_crossing _ (law j) X
  linarith only [h1,h2,eqc]

/-- Failure of a power bound gives witnesses above any finite threshold. -/
theorem arbitrarily_large_power_witness {F : ℕ → ℝ} (h0 : F 0=0) {s : ℝ}
    (hs : 0<s) (h : ¬PrefixPower s F) (R K : ℕ) :
    ∃ n : ℕ,R<n ∧ (K:ℝ)*(n:ℝ)^s < |F n| := by
  by_contra! ht
  let C := (K:ℝ)+∑ i ∈ range (R+1),|F i|
  have hK : (K:ℝ) ≤ C := le_add_of_nonneg_right (sum_nonneg (fun _ _ => abs_nonneg _))
  have hC := (Nat.cast_nonneg K).trans hK
  apply h
  refine ⟨C,hC,fun n => ?_⟩
  by_cases hR : R<n
  · exact (ht n hR).trans (mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg (Nat.cast_nonneg n) s))
  by_cases hn : n=0
  · rw [hn,h0,abs_zero]; positivity
  have hnR := le_of_not_gt hR
  have value := single_le_sum (fun i (_ : i ∈ range (R+1)) => abs_nonneg (F i)) (mem_range.mpr (Nat.lt_succ_of_le hnR))
  have hc : |F n| ≤ C := value.trans (le_add_of_nonneg_left (Nat.cast_nonneg K))
  have hpow := Real.one_le_rpow (by exact_mod_cast Nat.pos_of_ne_zero hn : (1:ℝ) ≤ n) hs.le
  have hstep := mul_le_mul_of_nonneg_left hpow hC
  rw [mul_one] at hstep
  exact hc.trans hstep

/-- A sequence eventually dominates each member of a bounded nonempty set
of real exponents, including its largest member when it exists. -/
theorem cofinal_exponents (S : Set ℝ) (hb : BddAbove S) (hs : S.Nonempty) :
    ∃ s : ℕ → ℝ, (∀ i,s i ∈ S) ∧ ∀ t ∈ S, ∀ᶠ i : ℕ in atTop,t ≤ s i := by
  by_cases htop : ∃ m ∈ S, ∀ x ∈ S,x ≤ m
  · obtain ⟨m,hm,hM⟩ := htop
    exact ⟨fun _ => m,fun _ => hm,fun x hx => Filter.Eventually.of_forall (fun _ => hM x hx)⟩
  let b := sSup S
  have ex (i : ℕ) : ∃ x ∈ S,b-1/((i:ℝ)+1)<x := by
    by_contra! hx
    have hh : b ≤ b-1/((i:ℝ)+1) := csSup_le hs hx
    linarith only [hh,show (0:ℝ)<1/((i:ℝ)+1) by positivity]
  let s (i : ℕ) := (ex i).choose
  refine ⟨s,fun i => (ex i).choose_spec.1,?_⟩
  intro t ht
  have ht' : t<b := lt_of_le_of_ne (le_csSup hb ht) (fun h => htop ⟨t,ht,fun x hx => h ▸ le_csSup hb hx⟩)
  obtain ⟨N,hN⟩ := exists_nat_gt (1/(b-t))
  filter_upwards [eventually_ge_atTop N] with i hi
  have gap := sub_pos.mpr ht'
  have hh := (div_lt_iff₀ gap).1 (hN.trans_le (Nat.cast_le.mpr hi))
  have small : 1/((i:ℝ)+1) < b-t := (div_lt_iff₀ (by positivity)).2 (by nlinarith only [hh,gap])
  linarith only [small,(ex i).choose_spec.2]

private abbrev Mertens := coprimeMoebiusSum 1

private theorem mertens_sum (X : ℕ) : coprimeMoebiusSum 1 X=∑ n ∈ Icc 1 X,(μ n:ℝ) := by
  simp [coprimeMoebiusSum,coprimeMoebiusIndicator]

/-- The trivial absolute estimate at all exponents at least one. -/
theorem mertens_prefix_power_of_one_le {θ : ℝ} (hθ : 1 ≤ θ) : PrefixPower θ (coprimeMoebiusSum 1) := by
  refine ⟨1,zero_le_one,fun X => ?_⟩
  rw [mertens_sum,one_mul]
  by_cases h : X=0
  · rw [h]; simp only [Icc_eq_empty_of_lt Nat.zero_lt_one,sum_empty,abs_zero]; positivity
  calc |∑ n ∈ Icc 1 X,(μ n:ℝ)| ≤ ∑ n ∈ Icc 1 X,|(μ n:ℝ)| := abs_sum_le_sum_abs ..
       _ ≤ ∑ _n ∈ Icc 1 X,(1:ℝ) := sum_le_sum (fun n _ => by exact_mod_cast abs_moebius_le_one (n := n))
       _ = (X:ℝ)^((1:ℝ)) := by simp
       _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.pos_of_ne_zero h) hθ

private def failedPowers : Set ℝ := {t | t=0 ∨ 0<t ∧ ¬PrefixPower t Mertens}

private theorem fails_nonempty : failedPowers.Nonempty := ⟨0,Or.inl rfl⟩

private theorem fails_bounded : BddAbove failedPowers := by
  refine ⟨1,fun t ht => ?_⟩
  rcases ht with rfl | ⟨_,h⟩
  · exact zero_le_one
  · exact le_of_not_gt (fun hle => h (mertens_prefix_power_of_one_le hle.le))

private abbrev abscissa := sSup failedPowers

private theorem abscissa_nonneg : 0 ≤ abscissa := le_csSup fails_bounded (Or.inl rfl : 0 ∈ failedPowers)

private theorem above_abscissa {s : ℝ} (hs : abscissa<s) : PrefixPower s Mertens := by
  by_contra h
  exact hs.not_ge (le_csSup fails_bounded (Or.inr ⟨abscissa_nonneg.trans_lt hs,h⟩ : s ∈ failedPowers))

private def tolerance (j : ℕ) : ℝ := 1/((j:ℝ)+2)

private theorem tol_pos (j : ℕ) : 0<tolerance j := by dsimp [tolerance]; positivity

private theorem tol_le_one (j : ℕ) : tolerance j ≤ 1 := by
  apply (div_le_iff₀ (by positivity : (0:ℝ)<(j:ℝ)+2)).2
  linarith only [Nat.cast_nonneg (α := ℝ) j]

private theorem tol_small {ε : ℝ} (hε : 0<ε) : ∀ᶠ j : ℕ in atTop,tolerance j ≤ ε := by
  obtain ⟨N,hN⟩ := exists_nat_gt (1/ε)
  filter_upwards [eventually_ge_atTop N] with j hj
  apply (div_le_iff₀ (by positivity : (0:ℝ)<(j:ℝ)+2)).2
  have hh := (div_lt_iff₀ hε).1 (hN.trans_le (Nat.cast_le.mpr hj))
  linarith only [hh,hε]

private structure LocalTable (j : ℕ) where
  swap : ℕ → ℕ
  onset : ℕ
  law : ∀ n,Squarefree n → swap (swap n)=n ∧ (swap n=n ∨ GlobalDyadicOneTwoRel n (swap n))
  near : ∀ n,Squarefree n → |(swap n:ℝ)-n| ≤ tolerance j*n
  count : ∀ X,onset ≤ X → ((prefixUnpaid swap X).card:ℝ) ≤ tolerance j*X
  signed : ∀ L U X,onset ≤ X →
    |∑ n ∈ wallCrossings swap L U X,(μ n:ℝ)| ≤ (X:ℝ)^(abscissa+2*tolerance j)
  detect : ∀ s,0<s → (PrefixPower s (fixedSignedPrefix swap) ↔ PrefixPower s Mertens)

private theorem local_table_exists (j : ℕ) : Nonempty (LocalTable j) := by
  obtain ⟨Q,hQ,F,scale,hF,_,hcount,hdetect⟩ := finite_divisor_table_detecting_every_mertens_power (tol_pos j)
  let s := abscissa+tolerance j
  have hs : abscissa<s := lt_add_of_pos_right _ (tol_pos j)
  obtain ⟨K,_,hK⟩ := uniform_power_of_clipped_crossings F hQ scale (abscissa_nonneg.trans_lt hs) (above_abscissa hs)
  have grow := ((tendsto_rpow_atTop (tol_pos j)).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop K
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hcount.and (grow.and (eventually_ge_atTop (1:ℕ))))
  refine ⟨⟨F,N,fun n hn => ⟨(hF n hn).1,(hF n hn).2.1⟩,fun n hn => (hF n hn).2.2,
    fun X hX => (hN X hX).1,?_,?_⟩⟩
  · intro L U X hX
    obtain ⟨_,hg,hx⟩ := hN X hX
    have hx0 : (0:ℝ)<X := Nat.cast_pos.mpr hx
    calc _ ≤ K*(X:ℝ)^s := hK L U X
         _ ≤ (X:ℝ)^(tolerance j)*(X:ℝ)^s :=
           mul_le_mul_of_nonneg_right hg (Real.rpow_nonneg hx0.le _)
         _ = _ := by rw [←Real.rpow_add hx0]; congr 1; dsimp only [s]; ring
  · intro t ht
    change PrefixPower t (fixedSignedPrefix F) ↔ PrefixPower t (coprimeMoebiusSum 1)
    rw [funext mertens_sum]
    exact hdetect t ht

private def table (j : ℕ) := (local_table_exists j).some

private theorem interior_witness {s : ℝ} (hs : s ∈ failedPowers) (j L : ℕ) :
    ∃ x : ℕ,2*L<x ∧ (0<s → (j:ℝ)*(x:ℝ)^s < |fixedSignedPrefix (table j).swap x|) := by
  rcases hs with rfl | ⟨hs,hbad⟩
  · exact ⟨2*L+1,Nat.lt_succ_self _,fun h => False.elim (lt_irrefl _ h)⟩
  · have h0 : fixedSignedPrefix (table j).swap 0=0 := by simp [fixedSignedPrefix,squarefreeOf]
    obtain ⟨x,hx,hl⟩ := arbitrarily_large_power_witness h0 hs (fun h => hbad (((table j).detect s hs).1 h)) (2*L) j
    exact ⟨x,hx,fun _ => hl⟩

private def witness (s : ℕ → ℝ) (hs : ∀ j,s j ∈ failedPowers) (j L : ℕ) :=
  (interior_witness (hs j) j L).choose

private def walls (s : ℕ → ℝ) (hs : ∀ j,s j ∈ failedPowers) : ℕ → ℕ
  | 0 => (table 0).onset+1
  | j+1 =>
    let L := walls s hs j
    max (max ((j+2)*L) (2*witness s hs j L)) (table (j+1)).onset+1

private theorem wall_onset (s : ℕ → ℝ) (hs : ∀ j,s j ∈ failedPowers) (j : ℕ) :
    (table j).onset ≤ walls s hs j := by
  cases j with
  | zero => exact Nat.le_succ _
  | succ j => exact (le_max_right ..).trans (Nat.le_succ _)

private theorem wall_spacing (s : ℕ → ℝ) (hs : ∀ j,s j ∈ failedPowers) (j : ℕ) :
    (j+2)*walls s hs j<walls s hs (j+1) :=
  Nat.lt_succ_of_le ((le_max_left ..).trans (le_max_left ..))

private theorem wall_strict (s : ℕ → ℝ) (hs : ∀ j,s j ∈ failedPowers) : StrictMono (walls s hs) :=
  strictMono_nat_of_lt_succ (fun j => (Nat.le_mul_of_pos_left _ (by omega : 0<j+2)).trans_lt (wall_spacing s hs j))

/-- Every integer beyond a strictly increasing wall lies in a unique later block. -/
theorem block_above {L : ℕ → ℕ} (hL : StrictMono L) {N X : ℕ} (hx : L N<X) :
    ∃ j,N ≤ j ∧ InBlock L j X := by
  have he : ∃ k,X ≤ L k := ⟨X,hL.id_le X⟩
  let k := Nat.find he
  have hk : X ≤ L k := Nat.find_spec he
  have hNk : N<k := lt_of_not_ge (fun h => hx.not_ge (hk.trans (hL.monotone h)))
  obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hjk : j<k := by omega
  exact ⟨j,by omega,lt_of_not_ge (Nat.find_min he hjk),by simpa only [hj] using hk⟩

private theorem all_unpaid_le (F : ℕ → ℕ) (X : ℕ) : (prefixUnpaid F X).card ≤ X := by
  have hsub : prefixUnpaid F X ⊆ Icc 1 X := fun _ hn => (mem_filter.mp (mem_filter.mp hn).1).1
  simpa using card_le_card hsub

/-- Widely spaced walls preserve density one and sublinear displacement
when each local table attains its tolerance beyond its left endpoint. -/
theorem dense_blocks_of_spaced_walls (L : ℕ → ℕ) (F : ℕ → ℕ → ℕ) (hL : StrictMono L)
    (spacing : ∀ j,(j+2)*L j<L (j+1))
    (law : ∀ j n,Squarefree n → F j (F j n)=n ∧ (F j n=n ∨ GlobalDyadicOneTwoRel n (F j n)))
    (count : ∀ j n,L j ≤ n → ((prefixUnpaid (F j) n).card:ℝ) ≤ (1/((j:ℝ)+2))*n)
    (near : ∀ j n,Squarefree n → |(F j n:ℝ)-n| ≤ (1/((j:ℝ)+2))*n) :
    ∀ ε : ℝ,0<ε → ∀ᶠ X : ℕ in atTop, ((prefixUnpaid (blockSwitch L F) X).card:ℝ) ≤ ε*X ∧
      (Squarefree X → |(blockSwitch L F X:ℝ)-X| ≤ ε*X) := by
  let H := blockSwitch L F
  intro ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp (tol_small (show 0<ε/5 by positivity))
  filter_upwards [eventually_ge_atTop (L (N+1)+1)] with X hX
  obtain ⟨k,hNk,hk⟩ := block_above hL (Nat.lt_of_succ_le hX)
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have prev : InBlock L j (L (j+1)) := ⟨hL (Nat.lt_succ_self _),le_rfl⟩
  have cap (i n : ℕ) (hi : L i ≤ n) (hn : n ≤ X) :
      ((prefixUnpaid (F i) n).card:ℝ) ≤ tolerance i*X :=
    (count i n hi).trans
      (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hn) (tol_pos i).le)
  have old : ((prefixUnpaid H (L j)).card:ℝ) ≤ tolerance j*X := by
    have hd : (j+2)*L j ≤ X := (spacing j).le.trans hk.1.le
    have hm : (L j:ℝ)*((j:ℝ)+2) ≤ X := by rw [Nat.mul_comm] at hd; exact_mod_cast hd
    have ha : (L j:ℝ) ≤ (X:ℝ)/((j:ℝ)+2) := (le_div_iff₀ (by positivity)).2 hm
    exact ((Nat.cast_le (α := ℝ)).mpr (all_unpaid_le H (L j))).trans (by simpa [tolerance,div_eq_mul_inv,mul_comm] using ha)
  have h1 := (Nat.cast_le (α := ℝ)).mpr (block_unpaid hL.monotone law prev)
  have h2 := (Nat.cast_le (α := ℝ)).mpr (block_unpaid hL.monotone law hk)
  push_cast only [Nat.cast_add] at h1 h2
  have hprice (i : ℕ) (hi : N ≤ i) :=
    mul_le_mul_of_nonneg_right (hN i hi) (Nat.cast_nonneg (α := ℝ) X)
  have hjX := prev.1.le.trans hk.1.le
  change ((prefixUnpaid H X).card:ℝ) ≤ _ ∧ _
  constructor
  · linarith only [h1,h2,old,cap j _ prev.1.le hk.1.le,cap j _ le_rfl hjX,
      cap (j+1) X hk.1.le le_rfl,cap (j+1) _ le_rfl hk.1.le,
      hprice j (by omega),hprice (j+1) (by omega)]
  · intro hsq
    rw [block_eval hL.monotone F hk]
    split
    next =>
      have h := near (j+1) X hsq
      change |(F (j+1) X:ℝ)-X| ≤ tolerance (j+1)*X at h
      have hh := hprice (j+1) (by omega)
      linarith only [h,hh,mul_nonneg hε.le (Nat.cast_nonneg (α := ℝ) X)]
    next => simp only [sub_self,abs_zero]; positivity

private theorem dense_blocks (s : ℕ → ℝ) (hs : ∀ j,s j ∈ failedPowers) :
    let H := blockSwitch (walls s hs) (fun j => (table j).swap)
    ∀ ε : ℝ,0<ε → ∀ᶠ X : ℕ in atTop,
      ((prefixUnpaid H X).card:ℝ) ≤ ε*X ∧ (Squarefree X → |(H X:ℝ)-X| ≤ ε*X) := by
  exact dense_blocks_of_spaced_walls _ _ (wall_strict s hs) (wall_spacing s hs)
    (fun j => (table j).law) (fun j n h => (table j).count n ((wall_onset s hs j).trans h))
    (fun j => (table j).near)

private theorem blocks_above_abscissa (s : ℕ → ℝ) (hs : ∀ j,s j ∈ failedPowers)
    {t : ℝ} (ht : abscissa<t) :
    PrefixPower t (fixedSignedPrefix (blockSwitch (walls s hs) (fun j => (table j).swap))) := by
  let L := walls s hs
  let F := fun j => (table j).swap
  let H := blockSwitch L F
  have hL := (wall_strict s hs).monotone
  obtain ⟨C,hC,hM⟩ := above_abscissa ht
  obtain ⟨N,hN⟩ := eventually_atTop.mp (tol_small (show 0<(t-abscissa)/2 by linarith only [ht]))
  have h0 : fixedSignedPrefix H 0=0 := by simp [fixedSignedPrefix,squarefreeOf]
  by_contra bad
  obtain ⟨K,hK⟩ := exists_nat_gt (C+1)
  obtain ⟨X,hx,hbig⟩ := arbitrarily_large_power_witness h0 (abscissa_nonneg.trans_lt ht) bad (L N) K
  obtain ⟨j,hj,hb⟩ := block_above (wall_strict s hs) hx
  have hc : |crossingSignedPrefix H X| ≤ (X:ℝ)^t := by
    change |∑ n ∈ (Icc 1 X).filter (fun n => X<blockSwitch L F n),(μ n:ℝ)| ≤ _
    rw [block_crossings hL F hb]
    apply ((table j).signed _ _ _ ((wall_onset s hs j).trans hb.1.le)).trans
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (Nat.zero_le _).trans_lt hx)
      (by linarith only [hN j hj])
  have together := fixed_add_crossing H (block_law hL (fun j => (table j).law)) X
  have he : fixedSignedPrefix H X=Mertens X-crossingSignedPrefix H X := by linarith only [together]
  rw [he] at hbig
  have hprice := mul_le_mul_of_nonneg_right hK.le (Real.rpow_nonneg (Nat.cast_nonneg X) t)
  linarith only [hbig,hprice,hM X,hc,abs_sub (Mertens X) (crossingSignedPrefix H X)]

private theorem blocks_detect {s : ℕ → ℝ} (hs : ∀ j,s j ∈ failedPowers)
    (cofinal : ∀ t ∈ failedPowers,∀ᶠ j : ℕ in atTop,t ≤ s j) {t : ℝ} (ht : 0<t)
    (power : PrefixPower t (fixedSignedPrefix (blockSwitch (walls s hs) (fun j => (table j).swap)))) :
    PrefixPower t Mertens := by
  by_contra bad
  let L := walls s hs
  let F := fun j => (table j).swap
  obtain ⟨C,_,hC⟩ := power
  have ev := cofinal t (Or.inr ⟨ht,bad⟩)
  obtain ⟨j,hj,hlarge⟩ := (ev.and (tendsto_natCast_atTop_atTop.eventually_gt_atTop C)).exists
  let x := witness s hs j (L j)
  obtain ⟨hx,hbig⟩ := (interior_witness (hs j) j (L j)).choose_spec
  change 2*L j<x at hx
  change 0<s j → (j:ℝ)*(x:ℝ)^(s j) < |fixedSignedPrefix (table j).swap x| at hbig
  have hr : 2*x ≤ L (j+1) := (le_max_right ..).trans ((le_max_left ..).trans (Nat.le_succ _))
  have interior := protected_fixed (wall_strict s hs).monotone (fun i => (table i).law) hx hr (by
    intro n hn
    have hnear := (table j).near n hn
    have htol := mul_le_mul_of_nonneg_right (tol_le_one j) (Nat.cast_nonneg (α := ℝ) n)
    have hh := le_abs_self (((table j).swap n:ℝ)-n)
    have bound : ((table j).swap n:ℝ) ≤ 2*(n:ℝ) := by linarith only [hnear,htol,hh]
    exact_mod_cast bound)
  have upper := hC x
  rw [interior] at upper
  have hx1 : 1 ≤ x := (Nat.zero_le _).trans_lt hx
  have hmono := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hx1 : (1:ℝ) ≤ x) hj
  have hprice := mul_le_mul_of_nonneg_left hmono (Nat.cast_nonneg (α := ℝ) j)
  have hx0 : (0:ℝ)<x := Nat.cast_pos.mpr hx1
  have hstrict := mul_lt_mul_of_pos_right hlarge (Real.rpow_pos_of_pos hx0 t)
  exact (hbig (ht.trans_le hj)).not_ge (upper.trans (hstrict.le.trans hprice))

private theorem abscissa_le_of_power {t : ℝ} (ht : 0<t) (power : PrefixPower t Mertens) :
    abscissa ≤ t := by
  apply csSup_le fails_nonempty
  intro q hq
  rcases hq with rfl | ⟨_,h⟩
  · exact ht.le
  apply le_of_not_gt
  intro hbig
  apply h
  obtain ⟨C,hC,hc⟩ := power
  refine ⟨C,hC,fun n => ?_⟩
  by_cases hn : n=0
  · simp [hn,mertens_sum,Real.zero_rpow (ht.trans hbig).ne']
  exact (hc n).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast Nat.pos_of_ne_zero hn : (1:ℝ) ≤ n) hbig.le) hC)

/-- One restricted involution has sublinear displacement and a density-zero
unpaid set. Its entire fixed signed prefix retains every failing positive
Mertens exponent and satisfies every power strictly above the abscissa. -/
theorem one_density_zero_fixed_set_detects_the_mertens_abscissa :
    ∃ G : ℕ → ℕ, (∀ n,G (G n)=n ∧ (G n=n ∨ GlobalDyadicOneTwoRel n (G n))) ∧
      (∀ ε : ℝ,0<ε → ∀ᶠ X : ℕ in atTop,
        ((prefixUnpaid G X).card:ℝ) ≤ ε*X ∧ |(G X:ℝ)-X| ≤ ε*X) ∧
      ∀ t : ℝ,0<t →
        (PrefixPower t (fixedSignedPrefix G) → PrefixPower t (coprimeMoebiusSum 1)) ∧
        (PrefixPower t (coprimeMoebiusSum 1) → ∀ η : ℝ,0<η → PrefixPower (t+η) (fixedSignedPrefix G)) := by
  obtain ⟨s,hs,hco⟩ := cofinal_exponents failedPowers fails_bounded fails_nonempty
  let H := blockSwitch (walls s hs) (fun i => (table i).swap)
  let G := fun n : ℕ => if Squarefree n then H n else n
  have hlaw := block_law (wall_strict s hs).monotone (fun j => (table j).law)
  have he {n : ℕ} (hn : Squarefree n) : G n=H n := if_pos hn
  have hfix : fixedSignedPrefix G=fixedSignedPrefix H := by
    funext X
    unfold fixedSignedPrefix
    congr 1
    ext n
    simp only [mem_filter]
    exact and_congr_right (fun h => by rw [he (mem_filter.mp h).2])
  have hcnt (X : ℕ) : prefixUnpaid G X=prefixUnpaid H X := by
    ext n
    simp only [prefixUnpaid,mem_filter]
    exact and_congr_right (fun h => by rw [he (mem_filter.mp h).2])
  refine ⟨G,?_,?_,?_⟩
  · intro n
    by_cases hn : Squarefree n
    · obtain ⟨hback,hedge⟩ := hlaw n hn
      have hnew : Squarefree (H n) := hedge.elim (fun h => by rw [show H n=n from h]; exact hn) (fun h => h.2.1)
      rw [he hn,he hnew]
      exact ⟨hback,hedge⟩
    · have hg : G n=n := if_neg hn
      exact ⟨(congrArg G hg).trans hg,Or.inl hg⟩
  · intro ε hε
    filter_upwards [dense_blocks s hs ε hε] with X hX
    rw [hcnt]
    refine ⟨hX.1,?_⟩
    by_cases hn : Squarefree X
    · rw [he hn]; exact hX.2 hn
    · simp only [G,if_neg hn,sub_self,abs_zero]; positivity
  · intro t ht
    rw [hfix]
    exact ⟨blocks_detect hs hco ht,fun h η hη => blocks_above_abscissa s hs
      ((abscissa_le_of_power ht h).trans_lt (lt_add_of_pos_right t hη))⟩

/-- On the entire fixed set of one density-one restricted matching, the
square-root-plus-epsilon estimates are equivalent to the full estimates. -/
theorem square_root_on_one_density_zero_fixed_set :
    ∃ G : ℕ → ℕ, (∀ n,G (G n)=n ∧ (G n=n ∨ GlobalDyadicOneTwoRel n (G n))) ∧
      (∀ ε : ℝ,0<ε → ∀ᶠ X : ℕ in atTop,
        ((prefixUnpaid G X).card:ℝ) ≤ ε*X ∧ |(G X:ℝ)-X| ≤ ε*X) ∧
      ((∀ ε : ℝ,0<ε → PrefixPower (1/2+ε) (fixedSignedPrefix G)) ↔
       ∀ ε : ℝ,0<ε → PrefixPower (1/2+ε) (coprimeMoebiusSum 1)) := by
  obtain ⟨G,hG,hd,h⟩ := one_density_zero_fixed_set_detects_the_mertens_abscissa
  refine ⟨G,hG,hd,fun H ε hε => (h _ (by linarith only [hε] : (0:ℝ)<1/2+ε)).1 (H ε hε),?_⟩
  intro H ε hε
  have half : 0<ε/2 := by positivity
  have hh := (h _ (by linarith only [half] : (0:ℝ)<1/2+ε/2)).2 (H _ half) _ half
  rwa [show (1:ℝ)/2+ε/2+ε/2=1/2+ε by ring] at hh

#print axioms one_density_zero_fixed_set_detects_the_mertens_abscissa
#print axioms square_root_on_one_density_zero_fixed_set

end GaloisForLFunctions.RestrictedFactorizationCalculus
