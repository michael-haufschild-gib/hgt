import GaloisForLFunctions.RestrictedFactorizationCalculus.DensityOneForRestrictedPrimeExchanges
import GaloisForLFunctions.QuantitativeFactorizationMatching.FactorizationInvolutionAndDoubleUseBookkeeping

/-!
# One restricted factorization involution with sublinear remainder

Minimize the joint cost of fixed vertices and edge lengths on each complete
dyadic block. Each integer then has a single partner independent of every
tolerance and cutoff. Only the block containing a cutoff can send edges
across it.
-/

noncomputable section

open Finset Filter
open scoped Classical ArithmeticFunction.Moebius
open GaloisForLFunctions.QuantitativeFactorizationMatching

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private abbrev BlockMap (X : ℕ) := FactorizationInvolution GlobalDyadicOneTwoRel (Ioc X (2*X))

private def affordable (X d : ℕ) : Prop :=
  ∃ F : BlockMap X, F.unmatchedSet.card ≤ d ∧ ∀ n : ℕ, |(F n:ℝ)-n| ≤ d

private theorem some_cost (X : ℕ) : ∃ d : ℕ, affordable X d := by
  let F : BlockMap X := {
    toFun := id
    involutive := fun _ => rfl
    fixed_outside := fun _ _ => rfl
    sign_flip := fun _ h => (h rfl).elim
    adj_pos := fun _ h => (h rfl).elim }
  exact ⟨F.unmatchedSet.card,F,le_rfl,fun _ => by simp [F]⟩

/-- Minimum of the joint integer bound on unmatched population and maximum edge length. -/
def blockCost (X : ℕ) := Nat.find (some_cost X)

private def blockMap (X : ℕ) : BlockMap X := (Nat.find_spec (some_cost X)).choose

private theorem block_control (X : ℕ) : (blockMap X).unmatchedSet.card ≤ blockCost X ∧
    ∀ n : ℕ, |(blockMap X n:ℝ)-n| ≤ blockCost X :=
  (Nat.find_spec (some_cost X)).choose_spec

/-- Any matching meeting both bounds controls the chosen integer optimum. -/
theorem blockCost_le_of_matching {X : ℕ} {t : ℝ}
    (M : OppositeParityMatching GlobalDyadicOneTwoRel (Ioc X (2*X)))
    (hcard : (M.unmatchedSet.card:ℝ) ≤ t) (hdist : ∀ n ∈ M.sources, |(M.partner n:ℝ)-n| ≤ t) :
    blockCost X ≤ ⌈t⌉₊ := by
  let F := FactorizationInvolution.ofMatching M
  let d := ⌈t⌉₊
  have hd : t ≤ (d:ℝ) := Nat.le_ceil _
  have hcost : affordable X d := by
    refine ⟨F,?_,fun n => ?_⟩
    · rw [FactorizationInvolution.ofMatching_unmatchedSet]
      exact Nat.cast_le.mp (hcard.trans hd)
    · by_cases he : F n=n
      · rw [he,sub_self,abs_zero]; positivity
      have hm := F.mem_movedSet.mpr he
      rw [FactorizationInvolution.ofMatching_movedSet] at hm
      rcases mem_union.mp hm with hs | ht
      · rw [FactorizationInvolution.ofMatching_apply_source hs]
        exact (hdist n hs).trans hd
      · obtain ⟨a,ha,hh⟩ := mem_image.mp ht
        have hF : F a=n := (FactorizationInvolution.ofMatching_apply_source ha).trans hh
        have hr : F n=a := (congrArg F hF).symm.trans (F.involutive a)
        rw [hr,←hh,abs_sub_comm]
        exact (hdist a ha).trans hd
  exact Nat.find_min' (some_cost X) hcost
private theorem cost_small {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ X : ℕ in atTop, (blockCost X:ℝ) ≤ δ*X := by
  filter_upwards [density_one_restricted_matching (half_pos hδ),
    eventually_ge_atTop ⌈2/δ⌉₊] with X hM hX
  obtain ⟨M,hcard,hdist⟩ := hM
  let d := ⌈(δ/2)*X⌉₊
  have hc : (blockCost X:ℝ) ≤ d := Nat.cast_le.mpr (blockCost_le_of_matching M hcard hdist)
  have hceil : (d:ℝ) < (δ/2)*X+1 := Nat.ceil_lt_add_one (by positivity)
  have hx := (div_le_iff₀ hδ).1 ((Nat.le_ceil (2/δ)).trans (Nat.cast_le.mpr hX))
  linarith only [hc,hceil,hx]

private def base (j : ℕ) : ℕ := 2^j

private theorem base_step (j : ℕ) : base (j+1)=2*base j := by simp [base,pow_succ,mul_comm]
private theorem base_mono {i j : ℕ} (h : i ≤ j) : base i ≤ base j :=
  Nat.pow_le_pow_right (by decide : 0 < 2) h
private theorem base_pos (j : ℕ) : 0 < base j := Nat.two_pow_pos j

private theorem some_block (n : ℕ) : ∃ j : ℕ, n ≤ 2*base j :=
  ⟨n,(Nat.lt_two_pow_self (n := n)).le.trans (by change 2^n ≤ 2*2^n; omega)⟩

private def level (n : ℕ) := Nat.find (some_block n)

private theorem level_bounds {n : ℕ} (hn : 1 < n) :
    base (level n) < n ∧ n ≤ 2*base (level n) := by
  refine ⟨?_,Nat.find_spec (some_block n)⟩
  cases hj : level n with
  | zero => exact hn
  | succ j =>
    rw [base_step]
    exact lt_of_not_ge (Nat.find_min (some_block n) (show j < level n by omega))

private theorem level_of_block {n j : ℕ} (hl : base j < n) (hu : n ≤ 2*base j) :
    level n=j := by
  apply Nat.le_antisymm (Nat.find_min' (some_block n) hu)
  by_contra! h
  have hr := base_mono (Nat.succ_le_of_lt h)
  rw [base_step] at hr
  exact hl.not_ge ((Nat.find_spec (some_block n)).trans hr)

/-- An optimal local involution on each disjoint dyadic block, fixing zero and the unit. -/
def dyadicPrimeSwitch (n : ℕ) := blockMap (base (level n)) n

private theorem block_eval {n j : ℕ} (hn : n ∈ Ioc (base j) (2*base j)) :
    dyadicPrimeSwitch n = blockMap (base j) n := by
  rw [dyadicPrimeSwitch,level_of_block (mem_Ioc.mp hn).1 (mem_Ioc.mp hn).2]

private theorem block_image {X n : ℕ} (h : n ∈ Ioc X (2*X)) :
    blockMap X n ∈ Ioc X (2*X) := by
  by_cases he : blockMap X n=n
  · rw [he]; exact h
  exact (mem_filter.mp ((blockMap X).moved_mem_squarefreeOf ((blockMap X).moved_apply he))).1

private theorem block_edge {X n : ℕ} (he : blockMap X n ≠ n) :
    GlobalDyadicOneTwoRel n (blockMap X n) := by
  let F := blockMap X
  have hsq := (mem_filter.mp (F.moved_mem_squarefreeOf he)).2
  rcases moebius_eq_one_or_neg_one_of_squarefree hsq with hp | hm
  · exact F.adj_pos n he hp
  · have hp : μ (F n)=1 := by rw [F.sign_flip n he,hm]; norm_num
    have h := (F.adj_pos _ (F.moved_apply he) hp).symm
    simpa only [F.apply_apply] using h

private theorem fixed_small {n : ℕ} (hn : n ≤ 1) : dyadicPrimeSwitch n=n := by
  apply (blockMap _).fixed_outside
  intro hm
  have h := (mem_Ioc.mp (mem_filter.mp hm).1).1
  have hp := base_pos (level n)
  omega

private theorem switch_law (n : ℕ) : dyadicPrimeSwitch (dyadicPrimeSwitch n)=n ∧
    (dyadicPrimeSwitch n=n ∨ GlobalDyadicOneTwoRel n (dyadicPrimeSwitch n)) := by
  by_cases hn : 1 < n
  · have hb := mem_Ioc.mpr (level_bounds hn)
    have hi := block_image hb
    have hr := block_eval hi
    change dyadicPrimeSwitch (blockMap (base (level n)) n)=n ∧ _
    exact ⟨hr.trans ((blockMap _).involutive n),or_iff_not_imp_left.mpr block_edge⟩
  · have hr := fixed_small (Nat.le_of_not_gt hn)
    exact ⟨by rw [hr,hr],Or.inl hr⟩

private def fixedUpto (X : ℕ) := (squarefreeOf (Icc 1 X)).filter (fun n => dyadicPrimeSwitch n=n)

private theorem fixed_mono {a b : ℕ} (h : a ≤ b) : fixedUpto a ⊆ fixedUpto b := by
  intro n hn
  obtain ⟨hs,he⟩ := mem_filter.mp hn
  obtain ⟨hi,hq⟩ := mem_filter.mp hs
  exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp hi).1,(mem_Icc.mp hi).2.trans h⟩,hq⟩,he⟩

private theorem fixed_step (j : ℕ) :
    (fixedUpto (base (j+1))).card ≤ (fixedUpto (base j)).card+blockCost (base j) := by
  let X := base j
  have hsub : fixedUpto (base (j+1)) ⊆ fixedUpto X ∪ (blockMap X).unmatchedSet := by
    intro n hn
    obtain ⟨hs,he⟩ := mem_filter.mp hn
    obtain ⟨hi,hq⟩ := mem_filter.mp hs
    by_cases h : n ≤ X
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp hi).1,h⟩,hq⟩,he⟩)
    · have hb : n ∈ Ioc X (2*X) := mem_Ioc.mpr ⟨Nat.lt_of_not_ge h,by rw [←base_step]; exact (mem_Icc.mp hi).2⟩
      exact mem_union_right _ (mem_filter.mpr ⟨mem_filter.mpr ⟨hb,hq⟩,(block_eval hb).symm.trans he⟩)
  exact (card_le_card hsub).trans ((card_union_le ..).trans (Nat.add_le_add_left (block_control X).1 _))

private theorem accumulated {δ : ℝ} (hδ : 0 ≤ δ) {K : ℕ}
    (hc : ∀ j ≥ K, (blockCost (base j):ℝ) ≤ δ*base j) :
    ∀ j ≥ K, ((fixedUpto (base j)).card:ℝ) ≤ base K+δ*base j := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base =>
    have hsub : fixedUpto (base K) ⊆ Icc 1 (base K) :=
      fun _ hn => (mem_filter.mp (mem_filter.mp hn).1).1
    have hcard : (fixedUpto (base K)).card ≤ base K := by
      simpa only [Nat.card_Icc,Nat.add_sub_cancel] using card_le_card hsub
    exact (Nat.cast_le.mpr hcard).trans (le_add_of_nonneg_right (mul_nonneg hδ (Nat.cast_nonneg _)))
  | succ j hj ih =>
    have h := (Nat.cast_le.mpr (fixed_step j) :
      ((fixedUpto (base (j+1))).card:ℝ) ≤ ((fixedUpto (base j)).card+blockCost (base j):ℕ))
    rw [Nat.cast_add,base_step] at h
    rw [base_step,Nat.cast_mul,Nat.cast_ofNat]
    linarith only [h,ih,hc j hj]

private theorem large_level {X K : ℕ} (hX : 2*base K < X) : K ≤ level X := by
  by_contra! h
  have hu := (Nat.find_spec (some_block X)).trans (Nat.mul_le_mul_left 2 (base_mono h.le))
  exact hX.not_ge hu

private theorem crossing_cost {n X : ℕ} (hn : n ≤ X) (hx : X < dyadicPrimeSwitch n) :
    X < n+blockCost (base (level X)) := by
  have hn1 : 1 < n := by
    by_contra! h
    rw [fixed_small h] at hx
    omega
  have hb := mem_Ioc.mpr (level_bounds hn1)
  have hi := (mem_Ioc.mp (block_image hb)).2
  have hlevel : level X = level n := level_of_block ((level_bounds hn1).1.trans_le hn) (hx.le.trans hi)
  have hd := (abs_le.mp ((block_control (base (level n))).2 n)).2
  have hh : (X:ℝ) < blockMap (base (level n)) n := by exact_mod_cast hx
  rw [hlevel]
  exact_mod_cast (show (X:ℝ) < n+(blockCost (base (level n)):ℝ) by linarith only [hh,hd])

private theorem prefix_card (X : ℕ) :
    (prefixUnpaid dyadicPrimeSwitch X).card ≤ (fixedUpto X).card+blockCost (base (level X)) := by
  let d := blockCost (base (level X))
  have hsub : prefixUnpaid dyadicPrimeSwitch X ⊆ fixedUpto X ∪ Ioc (X-d) X := by
    intro n hn
    obtain ⟨hs,h⟩ := mem_filter.mp hn
    rcases h with he | hx
    · exact mem_union_left _ (mem_filter.mpr ⟨hs,he⟩)
    · obtain ⟨hl,hu⟩ := mem_Icc.mp (mem_filter.mp hs).1
      have hgap : X < n+d := crossing_cost hu hx
      exact mem_union_right _ (mem_Ioc.mpr ⟨by omega,hu⟩)
  have hright : (Ioc (X-d) X).card ≤ d := by rw [Nat.card_Ioc]; omega
  exact (card_le_card hsub).trans ((card_union_le ..).trans (Nat.add_le_add_left hright _))

/-- Geometric summation above an arbitrary starting block and the cost of
edges crossing the sharp cutoff. -/
theorem dyadic_switch_prefix_bound {δ : ℝ} (hδ : 0 ≤ δ) {K X : ℕ} (hx : 2*2^K+2 ≤ X)
    (hc : ∀ j ≥ K, (blockCost (2^j):ℝ) ≤ δ*(2:ℝ)^j) :
    ((prefixUnpaid dyadicPrimeSwitch X).card:ℝ) ≤ (2:ℝ)^K+3*δ*X ∧
      |(dyadicPrimeSwitch X:ℝ)-X| ≤ δ*X := by
  have hx' : 2*base K+2 ≤ X := hx
  have hc' (j : ℕ) (hj : K ≤ j) : (blockCost (base j):ℝ) ≤ δ*base j := by
    simpa only [base,Nat.cast_pow,Nat.cast_ofNat] using hc j hj
  have hj := large_level (K := K) (X := X) (by omega)
  obtain ⟨hl,hu⟩ := level_bounds (n := X) (by omega)
  let j := level X
  have hdist := (block_control (base j)).2 X
  have hbase : (base j:ℝ) ≤ X := Nat.cast_le.mpr hl.le
  have hcost := (hc' j hj).trans (mul_le_mul_of_nonneg_left hbase hδ)
  have hfixed := accumulated hδ hc' (j+1) (Nat.le_succ_of_le hj)
  rw [base_step,Nat.cast_mul,Nat.cast_ofNat] at hfixed
  have hsub := card_le_card (fixed_mono (hu.trans_eq (base_step j).symm))
  have hcard := (Nat.cast_le.mpr ((prefix_card X).trans (Nat.add_le_add_right hsub _)) :
    ((prefixUnpaid dyadicPrimeSwitch X).card:ℝ) ≤ ((fixedUpto (base (j+1))).card+blockCost (base j):ℕ))
  rw [Nat.cast_add,base_step] at hcard
  have hscale := mul_le_mul_of_nonneg_left hbase hδ
  change _ ∧ |(blockMap (base j) X:ℝ)-X| ≤ _
  have hkCast : (base K:ℝ)=(2:ℝ)^K := by simp [base]
  rw [hkCast] at hfixed
  constructor <;> linarith only [hcard,hfixed,hcost,hscale,hdist]

/-- A single involution on all integers, fixing nonsquarefree integers, with
genuine prime exchanges on every two-cycle. Its unpaid vertices recover
every exact Möbius prefix. Both the unpaid fraction and the relative
displacement tend to zero for this same involution. -/
theorem one_involution_with_sublinear_unpaid_prefix :
    Function.Involutive dyadicPrimeSwitch ∧
      (∀ n : ℕ, dyadicPrimeSwitch n=n ∨ GlobalDyadicOneTwoRel n (dyadicPrimeSwitch n)) ∧
      (∀ X : ℕ, ∑ n ∈ Icc 1 X, μ n = ∑ n ∈ prefixUnpaid dyadicPrimeSwitch X, μ n) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℕ in atTop,
        ((prefixUnpaid dyadicPrimeSwitch X).card:ℝ) ≤ ε*X ∧ |(dyadicPrimeSwitch X:ℝ)-X| ≤ ε*X := by
  refine ⟨fun n => (switch_law n).1,fun n => (switch_law n).2,
    prefix_switch_balance _ (fun n _ => switch_law n),?_⟩
  intro ε hε
  let δ := ε/8
  have hδ : 0 < δ := div_pos hε (by norm_num)
  obtain ⟨K,hK⟩ := eventually_atTop.mp (cost_small hδ)
  have hc (j : ℕ) (hj : K ≤ j) : (blockCost (base j):ℝ) ≤ δ*base j :=
    hK _ (hj.trans (Nat.lt_two_pow_self (n := j)).le)
  filter_upwards [eventually_ge_atTop (2*base K+2),eventually_ge_atTop ⌈(base K:ℝ)/δ⌉₊] with X hx hbig
  have hb := dyadic_switch_prefix_bound (K := K) (X := X) hδ.le hx (fun j hj => by
    simpa only [base,Nat.cast_pow,Nat.cast_ofNat] using hc j hj)
  have hinit := (div_le_iff₀ hδ).1 ((Nat.le_ceil ((base K:ℝ)/δ)).trans (Nat.cast_le.mpr hbig))
  simp only [base,Nat.cast_pow,Nat.cast_ofNat] at hinit
  dsimp only [δ] at hb hinit
  constructor <;> linarith only [hb.1,hb.2,hinit,mul_nonneg hε.le (Nat.cast_nonneg X)]

#print axioms one_involution_with_sublinear_unpaid_prefix

end GaloisForLFunctions.RestrictedFactorizationCalculus
