import GaloisForLFunctions.RestrictedFactorizationCalculus.TheMertensAbscissaOnOneDensityZeroFixedSet
import GaloisForLFunctions.RestrictedFactorizationCalculus.TheSignedPrefixOfOneTruncatedExchange
import GaloisForLFunctions.RestrictedFactorizationCalculus.PrescribingExchangesOnADensityZeroSet
import GaloisForLFunctions.RHTower.MertensSquareRootOmega

/-!
# One density-zero family detecting every sharp Mertens exponent

Each cofactor stage contains a single primitive exchange. A stage ends after
a witness for a failing exponent and the next one begins beyond a witness
for the full prefix. Uniform prime deletion controls the converse, including
the endpoint. All moves may be prescribed within a density-one matching.
-/

noncomputable section

open Finset Filter
open ArithmeticFunction hiding id
open scoped Classical ArithmeticFunction.Moebius
open GaloisForLFunctions.QuantitativeFactorizationMatching GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private theorem mertens_positive_power_fails : ¬PrefixPower (1/4) (coprimeMoebiusSum 1) := by
  rintro ⟨C,hC,h⟩
  obtain ⟨c,hc,large,_⟩ := RHTower.mertens_omega_pm_sqrt
  have hg := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/4)).eventually_gt_atTop (C/c)
  obtain ⟨x,hx,hbig,hx1⟩ := (large.and_eventually (hg.and (eventually_ge_atTop (1:ℝ)))).exists
  have hx0 := zero_lt_one.trans_le hx1
  have he : RHTower.mertensFunctionReal x=coprimeMoebiusSum 1 ⌊x⌋₊ := by
    simp [RHTower.mertensFunctionReal,coprimeMoebiusSum,coprimeMoebiusIndicator]
  have hpow := Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le hx0.le) (by norm_num : (0:ℝ) ≤ 1/4)
  have hu := (h ⌊x⌋₊).trans (mul_le_mul_of_nonneg_left hpow hC)
  rw [←he] at hu
  have hsqrt : Real.sqrt x=x^(1/4:ℝ)*x^(1/4:ℝ) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_add hx0]; norm_num
  rw [hsqrt] at hx
  have hab := (div_lt_iff₀ hc).1 hbig
  have hstrict := mul_lt_mul_of_pos_right hab (Real.rpow_pos_of_pos hx0 (1/4))
  linarith only [hx,hu,le_abs_self (RHTower.mertensFunctionReal x),hstrict]

private structure ExchangeStage where
  pair : PrimitiveExchange
  A : ℕ
  B : ℕ
  gapWitness : ℕ
  crossingWitness : ℕ

private def ExchangeStage.left (s : ExchangeStage) := s.A*min s.pair.p s.pair.w
private def ExchangeStage.right (s : ExchangeStage) := s.B*max s.pair.p s.pair.w
private def ExchangeStage.vertices (s : ExchangeStage) := s.pair.moved s.A s.B
private def ExchangeStage.swap (s : ExchangeStage) := s.pair.act s.A s.B

private structure StageWitness (s : ExchangeStage) (j Z : ℕ) (θ : ℝ) : Prop where
  spacing : (j+2)*Z < s.left
  index_lt : j<s.left
  gap_after : Z<s.gapWitness
  gap_before : s.gapWitness<s.left
  witness_after : s.left<s.crossingWitness
  witness_before : s.crossingWitness<s.right
  mertens_large : (j:ℝ)*(s.gapWitness:ℝ)^θ < |coprimeMoebiusSum 1 s.gapWitness|
  moving_large : (j:ℝ)*(s.crossingWitness:ℝ)^θ < |∑ n ∈ s.vertices.filter (· ≤ s.crossingWitness),(μ n:ℝ)|
  prime_large : j+1<s.pair.p
  product_large : j+1<s.pair.w
  prime_near : |(s.pair.p:ℝ)-s.pair.w| ≤ (s.pair.p:ℝ)/(j+1:ℕ)
  product_near : |(s.pair.p:ℝ)-s.pair.w| ≤ (s.pair.w:ℝ)/(j+1:ℕ)

private theorem stage_witness_exists (j Z : ℕ) {θ : ℝ} (hθ : 0<θ)
    (bad : ¬PrefixPower θ (coprimeMoebiusSum 1)) : ∃ s,StageWitness s j Z θ := by
  obtain ⟨e,hp,hw,nearP,nearW⟩ := exists_short_primitive_exchange (j+1) (j+1) (Nat.succ_pos _)
  have h0 : coprimeMoebiusSum 1 0=0 := by simp [coprimeMoebiusSum]
  obtain ⟨g,hg,hMg⟩ := arbitrarily_large_power_witness h0 hθ bad Z j
  let A := (j+2)*(Z+g+1)+j+1
  let u := max e.p e.w
  let l := min e.p e.w
  have hl0 : 0<l := lt_min e.prime_p.pos (Nat.mul_pos e.prime_q.pos e.prime_r.pos)
  have hu0 : 0<u := e.prime_p.pos.trans_le (le_max_left ..)
  have hsmall : l ≤ u := (min_le_left ..).trans (le_max_left ..)
  have hF0 : dilationDifference e.w e.p (coprimeMoebiusSum e.modulus) 0=0 := by simp [dilationDifference]
  have badF := fun h => bad ((e.difference_power_iff hθ).1 h)
  obtain ⟨x,hX,hMx⟩ := arbitrarily_large_power_witness hF0 hθ badF (A*u) j
  let B := x+1
  let s : ExchangeStage := ⟨e,A,B,g,x⟩
  have hleft : A ≤ s.left := Nat.le_mul_of_pos_right A hl0
  have hAZ : (j+2)*Z<A := by dsimp [A]; nlinarith only [Nat.zero_le (j*g),Nat.zero_le j,Nat.zero_le g]
  have hAg : g<A := by dsimp [A]; nlinarith only [Nat.zero_le (j*g),Nat.zero_le (j*Z),Nat.zero_le Z,Nat.zero_le j,Nat.zero_le g]
  have hAj : j<A := by dsimp [A]; omega
  have hxp : A ≤ x/e.p := (Nat.le_div_iff_mul_le e.prime_p.pos).2 ((Nat.mul_le_mul_left A (le_max_left ..)).trans hX.le)
  have hxw : A ≤ x/e.w := (Nat.le_div_iff_mul_le (Nat.mul_pos e.prime_q.pos e.prime_r.pos)).2
    ((Nat.mul_le_mul_left A (le_max_right ..)).trans hX.le)
  have inside := e.interior_moved_prefix ⟨hxp,hxw⟩
    (And.intro ((Nat.div_le_self x _).trans (Nat.le_succ _)) ((Nat.div_le_self x _).trans (Nat.le_succ _)))
  refine ⟨s,hAZ.trans_le hleft,hAj.trans_le hleft,hg,hAg.trans_le hleft,
    (Nat.mul_le_mul_left A hsmall).trans_lt hX,(Nat.lt_succ_self x).trans_le (Nat.le_mul_of_pos_right _ hu0),
    hMg,?_,hp,hw,nearP,nearW⟩
  change (j:ℝ)*(x:ℝ)^θ < |∑ n ∈ (e.moved A (x+1)).filter (· ≤ x),(μ n:ℝ)|
  rwa [inside]

private def buildStages (s : ℕ → ℝ) (hs : ∀ j,0<s j ∧ ¬PrefixPower (s j) (coprimeMoebiusSum 1)) :
    ℕ → ExchangeStage
  | 0 => (stage_witness_exists 0 0 (hs 0).1 (hs 0).2).choose
  | j+1 => (stage_witness_exists (j+1) (buildStages s hs j).right (hs _).1 (hs _).2).choose

private theorem stages_spec (s : ℕ → ℝ) (hs : ∀ j,0<s j ∧ ¬PrefixPower (s j) (coprimeMoebiusSum 1)) (j : ℕ) :
    StageWitness (buildStages s hs j) j (if j=0 then 0 else (buildStages s hs (j-1)).right) (s j) := by
  cases j with
  | zero => exact (stage_witness_exists 0 0 (hs 0).1 (hs 0).2).choose_spec
  | succ j =>
    simpa only [Nat.succ_ne_zero,if_false,Nat.succ_sub_one,buildStages] using
      (stage_witness_exists (j+1) (buildStages s hs j).right (hs _).1 (hs _).2).choose_spec

private def SparseSupport (S : ℕ → ExchangeStage) : Set ℕ := {n | ∃ j,n ∈ (S j).vertices}
private def sparseSwitch (S : ℕ → ExchangeStage) (n : ℕ) :=
  if h : n ∈ SparseSupport S then (S h.choose).swap n else n

private theorem level_separation {S : ℕ → ExchangeStage}
    (hLR : ∀ j,(S j).left<(S j).right) (hstep : ∀ j,(S j).right<(S (j+1)).left) :
    ∀ {i j : ℕ},i<j → (S i).right < (S j).left := by
  intro i j h
  have mono : StrictMono (fun j => (S j).left) := strictMono_nat_of_lt_succ (fun j => (hLR j).trans (hstep j))
  exact (hstep i).trans_le (mono.monotone (Nat.succ_le_of_lt h))

private theorem same_stage {S : ℕ → ExchangeStage}
    (sep : ∀ {i j : ℕ},i<j → (S i).right<(S j).left) {i j n : ℕ}
    (hi : n ∈ (S i).vertices) (hj : n ∈ (S j).vertices) : i=j := by
  obtain ⟨il,iu⟩ := (S i).pair.moved_bounds hi
  obtain ⟨jl,ju⟩ := (S j).pair.moved_bounds hj
  rcases lt_trichotomy i j with h | h | h
  · exact (jl.not_ge (iu.trans (sep h).le)).elim
  · exact h
  · exact (il.not_ge (ju.trans (sep h).le)).elim

private theorem sparse_eval {S : ℕ → ExchangeStage}
    (sep : ∀ {i j : ℕ},i<j → (S i).right<(S j).left) {i n : ℕ}
    (hn : n ∈ (S i).vertices) : sparseSwitch S n=(S i).swap n := by
  have hv : n ∈ SparseSupport S := ⟨i,hn⟩
  rw [sparseSwitch,dif_pos hv,same_stage sep hv.choose_spec hn]

private theorem sparse_law {S : ℕ → ExchangeStage}
    (sep : ∀ {i j : ℕ},i<j → (S i).right<(S j).left) (n : ℕ) :
    sparseSwitch S (sparseSwitch S n)=n ∧ (sparseSwitch S n=n ∨ GlobalDyadicOneTwoRel n (sparseSwitch S n)) := by
  by_cases hn : n ∈ SparseSupport S
  · obtain ⟨j,hj⟩ := hn
    have h := (S j).pair.act_on hj
    rw [sparse_eval sep hj,sparse_eval sep h.1]
    exact ⟨h.2.1,Or.inr h.2.2⟩
  · have he : sparseSwitch S n=n := dif_neg hn
    exact ⟨(congrArg _ he).trans he,Or.inl he⟩

private def latestCandidates (S : ℕ → ExchangeStage) (X : ℕ) :=
  (range (X+1)).filter (fun j => (S j).left<X)

private theorem latest_spec {S : ℕ → ExchangeStage} (hindex : ∀ j,j<(S j).left)
    {X : ℕ} (hn : (latestCandidates S X).Nonempty) :
    let k := (latestCandidates S X).max' hn
    (S k).left < X ∧ ∀ j,(S j).left < X → j ≤ k := by
  refine ⟨(mem_filter.mp (max'_mem _ hn)).2,?_⟩
  intro j hj
  exact le_max' _ _ (mem_filter.mpr ⟨mem_range.mpr (by have := hindex j; omega),hj⟩)

private theorem sparse_count {S : ℕ → ExchangeStage} (hindex : ∀ j,j<(S j).left)
    (sep : ∀ {i j : ℕ},i<j → (S i).right<(S j).left)
    (hLR : ∀ j,(S j).left<(S j).right)
    (hsp : ∀ j,(j+1+2)*(S j).right < (S (j+1)).left)
    (hp : ∀ j,j+1<(S j).pair.p ∧ j+1<(S j).pair.w) :
    ∀ ε : ℝ,0<ε → ∀ᶠ X : ℕ in atTop,(prescribedCount (SparseSupport S) X:ℝ) ≤ ε*X := by
  intro ε hε
  obtain ⟨N,hN⟩ := exists_nat_gt (3/ε)
  filter_upwards [eventually_ge_atTop ((S (N+1)).left+1)] with X hx
  have hlX : (S (N+1)).left<X := by omega
  have hin : (latestCandidates S X).Nonempty :=
    ⟨N+1,mem_filter.mpr ⟨mem_range.mpr (by have := hindex (N+1); omega),hlX⟩⟩
  let k := (latestCandidates S X).max' hin
  obtain ⟨hkX,hlast⟩ := latest_spec hindex hin
  have hNk : N+1 ≤ k := hlast _ hlX
  obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hsub : (Icc 0 X).filter (· ∈ SparseSupport S) ⊆
      Icc 1 (S j).right ∪ ((S k).vertices.filter (· ≤ X)) := by
    intro n hn
    obtain ⟨hI,i,hi⟩ := mem_filter.mp hn
    have bounds := (S i).pair.moved_bounds hi
    have hu := (mem_Icc.mp hI).2
    have hik := hlast i (bounds.1.trans_le hu)
    rcases eq_or_lt_of_le hik with eq | small
    · exact mem_union_right _ (mem_filter.mpr ⟨eq ▸ hi,hu⟩)
    · have hij : i ≤ j := by omega
      have hr : (S i).right ≤ (S j).right := by
        rcases lt_or_eq_of_le hij with before | equal
        · exact ((sep before).trans (hLR j)).le
        · rw [equal]
      exact mem_union_left _ (mem_Icc.mpr ⟨(Nat.zero_le _).trans_lt bounds.1,bounds.2.trans hr⟩)
  have hn := (card_le_card hsub).trans ((card_union_le ..).trans
    (Nat.add_le_add_left ((S k).pair.moved_count (S k).A (S k).B X) _))
  rw [Nat.card_Icc,Nat.add_sub_cancel] at hn
  have hpay : (k+1)*(S j).right ≤ X := by
    rw [hj] at hkX ⊢
    exact ((Nat.mul_le_mul_right _ (by omega : j.succ+1 ≤ j+1+2)).trans (hsp j).le).trans hkX.le
  have per {d : ℕ} (hd : k+1 ≤ d) : ((X/d:ℕ):ℝ)*((k:ℝ)+1) ≤ X := by
    have hh := (Nat.mul_le_mul_left (X/d) hd).trans (Nat.div_mul_le_self ..)
    exact_mod_cast hh
  have hold : ((S j).right:ℝ)*((k:ℝ)+1) ≤ X := by exact_mod_cast (Nat.mul_comm ..) ▸ hpay
  have all := (Nat.cast_le (α := ℝ)).mpr hn
  push_cast only [Nat.cast_add] at all
  change (prescribedCount (SparseSupport S) X:ℝ) ≤ _ at all
  have hk0 : (0:ℝ)<(k:ℝ)+1 := by positivity
  have hprice : 3/((k:ℝ)+1) ≤ ε := (div_le_iff₀ hk0).2 (by
    have hh := (div_lt_iff₀ hε).1 hN
    have hnk : (N:ℝ) ≤ k := by exact_mod_cast (Nat.le_succ N).trans hNk
    nlinarith only [hh,mul_le_mul_of_nonneg_right hnk hε.le,hε])
  calc (prescribedCount (SparseSupport S) X:ℝ) ≤ 3*(X:ℝ)/((k:ℝ)+1) := by
          apply (le_div_iff₀ hk0).2
          have hh := mul_le_mul_of_nonneg_right all hk0.le
          linarith only [hh,hold,per (hp k).1.le,per (hp k).2.le]
       _ = (3/((k:ℝ)+1))*X := by ring
       _ ≤ _ := mul_le_mul_of_nonneg_right hprice (Nat.cast_nonneg _)

private def crossingAt (F : ℕ → ℕ) (X : ℕ) := (Icc 1 X).filter (fun n => X<F n)
private def changingAt (F : ℕ → ℕ) (X : ℕ) := (Icc 1 X).filter (fun n => F n ≠ n)

private theorem changing_eq_crossing (F : ℕ → ℕ) (hF : ∀ n,F (F n)=n ∧
    (F n=n ∨ GlobalDyadicOneTwoRel n (F n))) (X : ℕ) :
    ∑ n ∈ changingAt F X,(μ n:ℝ)=∑ n ∈ crossingAt F X,(μ n:ℝ) := by
  let V := changingAt F X
  let W := crossingAt F X
  let D := V \ W
  have sub : W ⊆ V := by
    intro n hn
    obtain ⟨hi,hc⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨hi,fun h => (mem_Icc.mp hi).2.not_gt (h ▸ hc)⟩
  have inner {n : ℕ} (hn : n ∈ D) : F n ∈ D ∧ (μ (F n):ℝ)= -(μ n:ℝ) := by
    obtain ⟨hm,hw⟩ := Finset.mem_sdiff.mp hn
    obtain ⟨hi,hd⟩ := mem_filter.mp hm
    obtain ⟨_,hX⟩ := mem_Icc.mp hi
    have hcap := le_of_not_gt (fun h => hw (mem_filter.mpr ⟨hi,h⟩))
    have edge := (hF n).2.resolve_left hd
    have hI : F n ∈ Icc 1 X := mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr edge.2.1.ne_zero,hcap⟩
    have back := (hF n).1
    refine ⟨Finset.mem_sdiff.mpr ⟨mem_filter.mpr ⟨hI,by rw [back]; exact hd.symm⟩,fun h => ?_⟩,?_⟩
    · have hh := (mem_filter.mp h).2
      rw [back] at hh; exact hX.not_gt hh
    · have hh := edge.2.2.1
      exact_mod_cast (show μ (F n)= -μ n by omega)
  have imageEq : D.image F=D := by
    ext n
    exact ⟨fun h => by obtain ⟨a,ha,rfl⟩ := mem_image.mp h; exact (inner ha).1,
      fun h => mem_image.mpr ⟨F n,(inner h).1,(hF n).1⟩⟩
  have hinj : Function.Injective F := (show Function.Involutive F from fun n => (hF n).1).injective
  have he : ∑ n ∈ D,(μ (F n):ℝ)=∑ n ∈ D,(μ n:ℝ) := by rw [←sum_image hinj.injOn,imageEq]
  have neg : ∑ n ∈ D,(μ (F n):ℝ)= -∑ n ∈ D,(μ n:ℝ) := by
    rw [←sum_neg_distrib]; exact sum_congr rfl (fun _ h => (inner h).2)
  have price := sum_sdiff_eq_sub (f := fun n => (μ n:ℝ)) sub
  change (∑ n ∈ D,(μ n:ℝ))=(∑ n ∈ V,(μ n:ℝ))-(∑ n ∈ W,(μ n:ℝ)) at price
  change (∑ n ∈ V,(μ n:ℝ))=∑ n ∈ W,(μ n:ℝ)
  linarith only [he,neg,price]

private theorem stage_law (s : ExchangeStage) (n : ℕ) :
    s.swap (s.swap n)=n ∧ (s.swap n=n ∨ GlobalDyadicOneTwoRel n (s.swap n)) := by
  by_cases hn : n ∈ s.vertices
  · have h := s.pair.act_on hn
    exact ⟨h.2.1,Or.inr h.2.2⟩
  · have he := s.pair.act_fixed_off hn
    exact ⟨(congrArg s.swap he).trans he,Or.inl he⟩

private theorem stage_changing (s : ExchangeStage) (X : ℕ) :
    changingAt s.swap X=s.vertices.filter (· ≤ X) := by
  ext n
  constructor
  · intro h
    obtain ⟨hi,hn⟩ := mem_filter.mp h
    have hv : n ∈ s.vertices := by by_contra hh; exact hn (s.pair.act_fixed_off hh)
    exact mem_filter.mpr ⟨hv,(mem_Icc.mp hi).2⟩
  · intro h
    obtain ⟨hv,hu⟩ := mem_filter.mp h
    have e := (s.pair.act_on hv).2.2
    have hs := e.2.2.1
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr e.1.ne_zero,hu⟩,fun he => ?_⟩
    rw [he] at hs
    rcases moebius_eq_one_or_neg_one_of_squarefree e.1 with h | h <;> omega

private theorem crosses_own_stage {s : ExchangeStage} {n X : ℕ} (hn : n ∈ crossingAt s.swap X) :
    n ∈ s.vertices ∧ s.left<X ∧ X<s.right := by
  obtain ⟨hi,hx⟩ := mem_filter.mp hn
  have hle := (mem_Icc.mp hi).2
  have hv : n ∈ s.vertices := by
    by_contra h
    have hh : s.swap n=n := s.pair.act_fixed_off h
    rw [hh] at hx
    exact hle.not_gt hx
  exact ⟨hv,(s.pair.moved_bounds hv).1.trans_le hle,hx.trans_le (s.pair.moved_bounds (s.pair.act_on hv).1).2⟩

private theorem local_crossings {S : ℕ → ExchangeStage} {X k : ℕ}
    (sep : ∀ {i j : ℕ},i<j → (S i).right<(S j).left)
    (hleft : (S k).left<X) (last : ∀ j,(S j).left<X → j ≤ k) :
    crossingAt (sparseSwitch S) X=crossingAt (S k).swap X := by
  ext n
  constructor
  · intro hn
    obtain ⟨hi,hx⟩ := mem_filter.mp hn
    have hv : n ∈ SparseSupport S := by
      by_contra h
      rw [sparseSwitch,dif_neg h] at hx
      exact (mem_Icc.mp hi).2.not_gt hx
    obtain ⟨j,hj⟩ := hv
    rw [sparse_eval sep hj] at hx
    have hc : n ∈ crossingAt (S j).swap X := mem_filter.mpr ⟨hi,hx⟩
    have ht := crosses_own_stage hc
    have he : j=k := le_antisymm (last j ht.2.1) (Nat.le_of_not_gt (fun h =>
      hleft.not_ge (ht.2.2.trans (sep h)).le))
    exact he ▸ hc
  · intro hn
    have hv := (crosses_own_stage hn).1
    exact mem_filter.mpr ⟨(mem_filter.mp hn).1,by rw [sparse_eval sep hv]; exact (mem_filter.mp hn).2⟩

private theorem latest_charge {S : ℕ → ExchangeStage} {X k : ℕ}
    (sep : ∀ {i j : ℕ},i<j → (S i).right<(S j).left)
    (hleft : (S k).left<X) (last : ∀ j,(S j).left<X → j ≤ k) :
    ∑ n ∈ crossingAt (sparseSwitch S) X,(μ n:ℝ) = ∑ n ∈ (S k).vertices.filter (· ≤ X),(μ n:ℝ) := by
  rw [local_crossings sep hleft last,←changing_eq_crossing _ (stage_law _) X,stage_changing]

private theorem no_crossings_before {S : ℕ → ExchangeStage} {X : ℕ}
    (sep : ∀ {i j : ℕ},i<j → (S i).right<(S j).left)
    (stop : ∀ j,¬((S j).left<X ∧ X<(S j).right)) : crossingAt (sparseSwitch S) X=∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro n hn
  obtain ⟨hi,hx⟩ := mem_filter.mp hn
  by_cases h : n ∈ SparseSupport S
  · obtain ⟨j,hj⟩ := h
    rw [sparse_eval sep hj] at hx
    exact stop j (crosses_own_stage (s := S j) (mem_filter.mpr ⟨hi,hx⟩)).2
  · rw [sparseSwitch,dif_neg h] at hx
    exact (mem_Icc.mp hi).2.not_gt hx

/-- Signed Möbius prefix of all members of a designated set. -/
def markedSignedPrefix (T : Set ℕ) (X : ℕ) := ∑ n ∈ (Icc 1 X).filter (· ∈ T),(μ n:ℝ)

private theorem support_moves {S : ℕ → ExchangeStage}
    (sep : ∀ {i j : ℕ},i<j → (S i).right<(S j).left) {n : ℕ} :
    n ∈ SparseSupport S ↔ sparseSwitch S n ≠ n := by
  constructor
  · rintro ⟨j,hj⟩
    rw [sparse_eval sep hj]
    have h := (S j).pair.act_on hj
    intro he
    have hneg := h.2.2.2.2.1
    rw [he] at hneg
    rcases moebius_eq_one_or_neg_one_of_squarefree h.2.2.1 with hm | hm <;> omega
  · intro h
    by_contra hn
    exact h (dif_neg hn)

private theorem marked_crossings {S : ℕ → ExchangeStage}
    (sep : ∀ {i j : ℕ},i<j → (S i).right<(S j).left) (X : ℕ) :
    markedSignedPrefix (SparseSupport S) X=∑ n ∈ crossingAt (sparseSwitch S) X,(μ n:ℝ) := by
  rw [←changing_eq_crossing _ (sparse_law sep)]
  have hset : (Icc 1 X).filter (· ∈ SparseSupport S)=changingAt (sparseSwitch S) X := by
    ext n
    simp only [changingAt,mem_filter,support_moves sep]
  rw [markedSignedPrefix,hset]

private theorem marked_complement (T : Set ℕ) (X : ℕ) :
    markedSignedPrefix T X+markedSignedPrefix Tᶜ X=coprimeMoebiusSum 1 X := by
  have h := sum_filter_add_sum_filter_not (s := Icc 1 X) (fun n => n ∈ T) (fun n => (μ n:ℝ))
  simpa [markedSignedPrefix,coprimeMoebiusSum,coprimeMoebiusIndicator] using h

private theorem sparse_upper {S : ℕ → ExchangeStage}
    (sep : ∀ {i j : ℕ},i<j → (S i).right<(S j).left) (idx : ∀ j,j<(S j).left)
    {t : ℝ} (ht : 0<t) (power : PrefixPower t (coprimeMoebiusSum 1)) :
    PrefixPower t (markedSignedPrefix (SparseSupport S)) ∧
    PrefixPower t (markedSignedPrefix (SparseSupport S)ᶜ) := by
  obtain ⟨K,hK,h⟩ := PrimitiveExchange.moved_power_bound ht power
  have within (X : ℕ) : |markedSignedPrefix (SparseSupport S) X| ≤ K*(X:ℝ)^t := by
    rw [marked_crossings sep]
    by_cases hn : (latestCandidates S X).Nonempty
    · obtain ⟨hk,hj⟩ := latest_spec idx hn
      rw [latest_charge sep hk hj]
      exact h _ _ _ _
    have no (j : ℕ) : ¬((S j).left<X ∧ X<(S j).right) := fun h =>
      hn ⟨j,mem_filter.mpr ⟨mem_range.mpr (by have hj := idx j; omega),h.1⟩⟩
    rw [no_crossings_before sep no,sum_empty,abs_zero]
    exact mul_nonneg hK (Real.rpow_nonneg (Nat.cast_nonneg X) t)
  obtain ⟨B,hB,hM⟩ := power
  refine ⟨⟨K,hK,within⟩,B+K,add_nonneg hB hK,fun X => ?_⟩
  have he := marked_complement (SparseSupport S) X
  have diff : markedSignedPrefix (SparseSupport S)ᶜ X=coprimeMoebiusSum 1 X-markedSignedPrefix (SparseSupport S) X := by
    linarith only [he]
  rw [diff,add_mul]
  exact (abs_sub ..).trans (add_le_add (hM X) (within X))

private theorem lower_at_stages {s : ℕ → ℝ} {S : ℕ → ExchangeStage}
    (spec : ∀ j,StageWitness (S j) j (if j=0 then 0 else (S (j-1)).right) (s j))
    (sep : ∀ {i j : ℕ},i<j → (S i).right<(S j).left)
    (hLR : ∀ j,(S j).left<(S j).right) (j : ℕ) :
    (j:ℝ)*((S j).crossingWitness:ℝ)^(s j) < |markedSignedPrefix (SparseSupport S) (S j).crossingWitness| ∧
    (j:ℝ)*((S j).gapWitness:ℝ)^(s j) < |markedSignedPrefix (SparseSupport S)ᶜ (S j).gapWitness| := by
  have hj := spec j
  have mono : StrictMono (fun i => (S i).left) := strictMono_nat_of_lt_succ
    (fun i => (hLR i).trans (sep (Nat.lt_succ_self i)))
  have last (i : ℕ) (hi : (S i).left<(S j).crossingWitness) : i ≤ j :=
    le_of_not_gt (fun hh => hi.not_ge (hj.witness_before.trans (sep hh)).le)
  constructor
  · rw [marked_crossings sep,latest_charge sep hj.witness_after last]
    exact hj.moving_large
  have before (i : ℕ) : ¬((S i).left<(S j).gapWitness ∧ (S j).gapWitness<(S i).right) := by
    intro h
    rcases lt_or_ge i j with prev | post
    · obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
      have hr : (S k).right<(S (k+1)).gapWitness := by simpa only [Nat.succ_ne_zero,if_false,Nat.succ_sub_one] using (spec (k+1)).gap_after
      have hi : i ≤ k := Nat.le_of_lt_succ prev
      rcases lt_or_eq_of_le hi with earlier | rfl
      · exact h.2.not_ge (((sep earlier).trans (hLR k)).le.trans hr.le)
      · exact h.2.not_ge hr.le
    · exact h.1.not_ge (hj.gap_before.le.trans (mono.monotone post))
  have hz : markedSignedPrefix (SparseSupport S) (S j).gapWitness=0 := by
    rw [marked_crossings sep,no_crossings_before sep before,sum_empty]
  have hm := marked_complement (SparseSupport S) (S j).gapWitness
  rw [hz,zero_add] at hm
  rw [hm]
  exact hj.mertens_large

private theorem detect_from_witnesses {s : ℕ → ℝ} {t : ℝ} {f : ℕ → ℝ} {w : ℕ → ℕ}
    (hs : ∀ᶠ j : ℕ in atTop,t ≤ s j) (hw : ∀ j,0<w j)
    (large : ∀ j,(j:ℝ)*(w j:ℝ)^(s j) < |f (w j)|) : ¬PrefixPower t f := by
  rintro ⟨C,_,bound⟩
  obtain ⟨j,hj,hC⟩ := (hs.and (tendsto_natCast_atTop_atTop.eventually_gt_atTop C)).exists
  have base : (1:ℝ) ≤ w j := by exact_mod_cast hw j
  have hi := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le base hj) (Nat.cast_nonneg (α := ℝ) j)
  have lo := mul_lt_mul_of_pos_right hC (Real.rpow_pos_of_pos (zero_lt_one.trans_le base) t)
  exact (large j).not_ge ((bound _).trans (lo.le.trans hi))

private theorem sparse_near {S : ℕ → ExchangeStage} {s : ℕ → ℝ}
    (spec : ∀ j,StageWitness (S j) j (if j=0 then 0 else (S (j-1)).right) (s j))
    (sep : ∀ {i j : ℕ},i<j → (S i).right<(S j).left) (hLR : ∀ j,(S j).left<(S j).right) :
    ∀ ε : ℝ,0<ε → ∀ᶠ X : ℕ in atTop,X ∈ SparseSupport S → |(sparseSwitch S X:ℝ)-X| ≤ ε*X := by
  intro ε hε
  obtain ⟨N,hN⟩ := exists_nat_gt (1/ε)
  filter_upwards [eventually_ge_atTop ((S N).right+1)] with X hx hmem
  obtain ⟨j,hj⟩ := hmem
  have xr := ((S j).pair.moved_bounds hj).2
  have hNj : N ≤ j := le_of_not_gt (fun h => (Nat.lt_of_succ_le hx).not_ge
    (xr.trans ((sep h).trans (hLR N)).le))
  rw [sparse_eval sep hj]
  refine ((S j).pair.act_distance (spec j).prime_near (spec j).product_near _ _ _).trans ?_
  have hi : (1:ℝ)/(j+1:ℕ) ≤ ε := (div_le_iff₀ (by positivity)).2 (by
    push_cast
    have hh := (div_lt_iff₀ hε).1 (hN.trans_le (Nat.cast_le.mpr hNj))
    linarith only [hh,hε])
  simpa only [mul_one_div,mul_comm (X:ℝ)] using mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg X)

/-- Inside one density-one matching there is a density-zero union of its
actual edges on which the signed prefix detects every positive power,
including the endpoint. Its complementary signed prefix does the same. -/
theorem a_density_zero_family_of_exchanges_detects_every_mertens_power :
    ∃ (H : ℕ → ℕ) (T : Set ℕ), Function.Involutive H ∧
      (∀ n,H n=n ∨ GlobalDyadicOneTwoRel n (H n)) ∧
      (∀ n ∈ T,H n ∈ T ∧ GlobalDyadicOneTwoRel n (H n)) ∧
      (∀ ε : ℝ,0<ε → ∀ᶠ X : ℕ in atTop,
        (prescribedCount T X:ℝ) ≤ ε*X ∧ ((prefixUnpaid H X).card:ℝ) ≤ ε*X ∧
        |(H X:ℝ)-X| ≤ ε*X) ∧
      (∀ X : ℕ,markedSignedPrefix T X=
        ∑ n ∈ (Icc 1 X).filter (fun n => n ∈ T ∧ X<H n),(μ n:ℝ)) ∧
      ∀ θ : ℝ,0<θ →
        (PrefixPower θ (markedSignedPrefix T) ↔ PrefixPower θ (coprimeMoebiusSum 1)) ∧
        (PrefixPower θ (markedSignedPrefix Tᶜ) ↔ PrefixPower θ (coprimeMoebiusSum 1)) := by
  let Bad : Set ℝ := {t | 0<t ∧ ¬PrefixPower t (coprimeMoebiusSum 1)}
  have hne : Bad.Nonempty := ⟨1/4,by norm_num,mertens_positive_power_fails⟩
  have bdd : BddAbove Bad := ⟨1,fun t ht => le_of_not_gt (fun h => ht.2 (mertens_prefix_power_of_one_le h.le))⟩
  obtain ⟨s,hs,hco⟩ := cofinal_exponents Bad bdd hne
  let S := buildStages s hs
  have spec := stages_spec s hs
  have hLR (j : ℕ) : (S j).left<(S j).right := (spec j).witness_after.trans (spec j).witness_before
  have hsp (j : ℕ) : (j+1+2)*(S j).right < (S (j+1)).left := by
    simpa only [Nat.succ_ne_zero,if_false,Nat.succ_sub_one] using (spec (j+1)).spacing
  have sep := level_separation hLR (fun j => (Nat.le_mul_of_pos_left _ (by omega : 0<j+1+2)).trans_lt (hsp j))
  let T := SparseSupport S
  let G := sparseSwitch S
  have hcount := sparse_count (fun i => (spec i).index_lt) sep hLR hsp
    (fun i => ⟨(spec i).prime_large,(spec i).product_large⟩)
  have onT (n : ℕ) (hn : n ∈ T) : G n ∈ T ∧ G (G n)=n ∧ GlobalDyadicOneTwoRel n (G n) := by
    obtain ⟨j,hj⟩ := hn
    have he := (S j).pair.act_on hj
    have hh : G n=(S j).swap n := sparse_eval sep hj
    exact ⟨⟨j,hh ▸ he.1⟩,(sparse_law sep n).1,hh ▸ he.2.2⟩
  obtain ⟨H,hH,hI,hlegal,_,hd,hm⟩ := density_one_with_prescribed_exchanges T G hcount
    (fun n hn => ⟨(onT n hn).1,(onT n hn).2.1,Or.inr (onT n hn).2.2⟩)
  have hnear := hm (sparse_near spec sep hLR)
  refine ⟨H,T,hI,hlegal,fun n hn => ?_,?_,?_,?_⟩
  · rw [hH n hn]; exact ⟨(onT n hn).1,(onT n hn).2.2⟩
  · intro ε hε
    filter_upwards [hcount ε hε,hd ε hε,hnear ε hε] with X ht hu hx
    exact ⟨ht,hu,hx⟩
  · intro X
    rw [marked_crossings sep]
    have he : crossingAt G X=(Icc 1 X).filter (fun n => n ∈ T ∧ X<H n) := by
      ext n
      constructor
      · intro h
        obtain ⟨hi,hc⟩ := mem_filter.mp h
        have hn : n ∈ T := (support_moves sep).2 (fun he => (mem_Icc.mp hi).2.not_gt (he ▸ hc))
        exact mem_filter.mpr ⟨hi,hn,by rw [hH n hn]; exact hc⟩
      · intro h
        obtain ⟨hi,hn,hx⟩ := mem_filter.mp h
        exact mem_filter.mpr ⟨hi,by rwa [hH n hn] at hx⟩
    rw [he]
  · intro θ hθ
    have upper := sparse_upper sep (fun j => (spec j).index_lt) hθ
    by_cases h : PrefixPower θ (coprimeMoebiusSum 1)
    · exact ⟨⟨fun _ => h,fun _ => (upper h).1⟩,⟨fun _ => h,fun _ => (upper h).2⟩⟩
    have ev := hco θ (show θ ∈ Bad from ⟨hθ,h⟩)
    have lower := fun j => lower_at_stages spec sep hLR j
    have hf := detect_from_witnesses ev
      (fun j => (Nat.zero_le _).trans_lt (spec j).witness_after) (fun j => (lower j).1)
    have hg := detect_from_witnesses ev (fun j => (Nat.zero_le _).trans_lt (spec j).gap_after) (fun j => (lower j).2)
    exact ⟨iff_of_false hf h,iff_of_false hg h⟩

#print axioms a_density_zero_family_of_exchanges_detects_every_mertens_power

end GaloisForLFunctions.RestrictedFactorizationCalculus
