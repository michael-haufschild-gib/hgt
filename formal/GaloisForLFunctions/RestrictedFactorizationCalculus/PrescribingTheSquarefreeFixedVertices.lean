import GaloisForLFunctions.RestrictedFactorizationCalculus.PerfectCompletionAtEverySharpCutoff

/-!
# Prescribing which fixed vertices survive completion

After a separated perfect completion, restore an edge if its lower
endpoint was a requested fixed vertex. Every incorrectly classified
vertex is an upper endpoint of a changed edge. The threshold on those
edges gives a simultaneous count at every sharp cutoff.
-/

noncomputable section

open Finset Filter ArithmeticFunction
open scoped Classical ArithmeticFunction.Moebius
open GaloisForLFunctions.QuantitativeFactorizationMatching GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

/-- Requested squarefree fixed vertices, always including the unit. -/
def requestedFixed (F : ℕ → ℕ) (S : Set ℕ) (X : ℕ) :=
  (squarefreeOf (Icc 1 X)).filter (fun n => n=1 ∨ n ∈ S ∧ F n=n)

/-- Classification errors through the cutoff. -/
def fixedErrors (F G : ℕ → ℕ) (S : Set ℕ) (X : ℕ) := (squarefreeOf (Icc 1 X)).filter
  (fun n => ¬ (G n=n ↔ n=1 ∨ n ∈ S ∧ F n=n))

private def restored (F P : ℕ → ℕ) (S : Set ℕ) (n : ℕ) :=
  1<n ∧ Squarefree n ∧ n ∈ S ∧ F n=n ∧ n<P n

private def restoreEdges (F P : ℕ → ℕ) (S : Set ℕ) (n : ℕ) :=
  if restored F P S n ∨ restored F P S (P n) then n else P n

private theorem restore_law {F P : ℕ → ℕ} (back : Function.Involutive P)
    (legal : ∀ n,P n=n ∨ GlobalDyadicOneTwoRel n (P n)) (S : Set ℕ) (n : ℕ) :
    restoreEdges F P S (restoreEdges F P S n)=n ∧
      (restoreEdges F P S n=n ∨ GlobalDyadicOneTwoRel n (restoreEdges F P S n)) := by
  by_cases h : restored F P S n ∨ restored F P S (P n)
  · have he : restoreEdges F P S n=n := if_pos h
    exact ⟨(congrArg (restoreEdges F P S) he).trans he,Or.inl he⟩
  · have hy : ¬(restored F P S (P n) ∨ restored F P S (P (P n))) := by
      rw [back n,or_comm]; exact h
    simpa only [restoreEdges,if_neg h,if_neg hy] using And.intro (back n) (legal n)

/-- Every subset of the old fixed vertices can be retained up to
arbitrarily sparse classification errors. Each error is a distinct
upper endpoint, and only completed restored edges can increase the
unpaid population. -/
theorem prescribe_fixed_vertices_at_all_cutoffs (F : ℕ → ℕ) (back : Function.Involutive F)
    (legal : ∀ n,F n=n ∨ GlobalDyadicOneTwoRel n (F n)) (S : Set ℕ) (B : ℕ → ℕ) :
    ∃ G : ℕ → ℕ,Function.Involutive G ∧ (∀ n,G n=n ∨ GlobalDyadicOneTwoRel n (G n)) ∧
      ∀ X : ℕ, let D := ((range (X+1)).filter (fun k => B k<X)).card
        (fixedErrors F G S X).card ≤ D ∧ (prefixUnpaid G X).card ≤ (prefixUnpaid F X).card+2*D := by
  classical
  obtain ⟨P,bk,lp,covers,paid,separate,_⟩ := perfect_completion_with_separated_edges F back legal B
  let G := restoreEdges F P S
  have glaw := restore_law (F := F) bk lp S
  refine ⟨G,fun n => (glaw n).1,fun n => (glaw n).2,?_⟩
  intro X
  let I := (range (X+1)).filter (fun k => B k<X)
  have upper {k : ℕ} (hk : restored F P S k) : B k<P k :=
    (separate k hk.2.2.2.2).resolve_left (fun e => hk.2.2.2.2.ne' (e.trans hk.2.2.2.1))
  have ib {k : ℕ} (hk : k ≤ X) (hfar : B k<X) : k ∈ I :=
    mem_filter.mpr ⟨mem_range.mpr (by omega),hfar⟩
  have errs : fixedErrors F G S X ⊆ I.image P := by
    intro n hn
    obtain ⟨hs,wrong⟩ := mem_filter.mp hn
    obtain ⟨hi,sq⟩ := mem_filter.mp hs
    obtain ⟨hpos,hx⟩ := mem_Icc.mp hi
    have n1 : 1<n := by
      by_contra! hle
      obtain rfl : n=1 := by omega
      apply wrong
      have g1 := restricted_unit_is_fixed G (fun m => (glaw m).2)
      exact ⟨fun _ => Or.inl rfl,fun _ => g1⟩
    have nP := covers n sq n1
    by_cases kept : restored F P S n ∨ restored F P S (P n)
    · have fixed : G n=n := if_pos kept
      have hno : ¬(n=1 ∨ n ∈ S ∧ F n=n) := fun ha => wrong ⟨fun _ => ha,fun _ => fixed⟩
      have hnrest : ¬restored F P S n := fun h => hno (Or.inr ⟨h.2.2.1,h.2.2.2.1⟩)
      have h := kept.resolve_left hnrest
      have lt := h.2.2.2.2
      have far := upper h
      rw [bk n] at lt far
      exact mem_image.mpr ⟨P n,ib (lt.le.trans hx) (far.trans_le hx),bk n⟩
    · have moved : G n ≠ n := by change restoreEdges F P S n ≠ n; rwa [restoreEdges,if_neg kept]
      have want : n=1 ∨ n ∈ S ∧ F n=n := by
        by_contra bad
        exact wrong ⟨fun e => (moved e).elim,fun h => (bad h).elim⟩
      obtain ⟨selected,formerly⟩ := want.resolve_left n1.ne'
      have low : P n<n := lt_of_le_of_ne (le_of_not_gt (fun higher =>
        kept (Or.inl ⟨n1,sq,selected,formerly,higher⟩))) nP
      have old : P (P n) ≠ F (P n) := by
        rw [bk n]
        intro e
        have hh := (congrArg F e).trans (back (P n))
        exact nP (hh.symm.trans formerly)
      have far := (separate (P n) (by rwa [bk n])).resolve_left old
      rw [bk n] at far
      exact mem_image.mpr ⟨P n,ib (low.le.trans hx) (far.trans_le hx),bk n⟩
  have enlarged : prefixUnpaid G X ⊆ prefixUnpaid P X ∪ (I ∪ I.image P) := by
    intro n hn
    obtain ⟨hs,hu⟩ := mem_filter.mp hn
    have hx := (mem_Icc.mp (mem_filter.mp hs).1).2
    by_cases old : P n=n ∨ X<P n
    · exact mem_union_left _ (mem_filter.mpr ⟨hs,old⟩)
    have py := le_of_not_gt (fun e => old (Or.inr e))
    have pick : restored F P S n ∨ restored F P S (P n) := by
      by_contra bad
      have eq : G n=P n := if_neg bad
      rw [eq] at hu; exact old hu
    apply mem_union_right _
    rcases pick with hl | hr
    · exact mem_union_left _ (ib hx ((upper hl).trans_le py))
    · have far := upper hr
      rw [bk n] at far
      exact mem_union_right _ (mem_image.mpr ⟨P n,ib py (far.trans_le hx),bk n⟩)
  refine ⟨(card_le_card errs).trans card_image_le,?_⟩
  apply (card_le_card enlarged).trans ((card_union_le ..).trans _)
  have hh : (I ∪ I.image P).card ≤ 2*I.card := by
    have h1 := card_union_le I (I.image P)
    have h2 : (I.image P).card ≤ I.card := card_image_le
    omega
  exact Nat.add_le_add (paid X) hh

/-- Fix both endpoints of each edge meeting the requested set. -/
private def reserve (F : ℕ → ℕ) (S : Set ℕ) (n : ℕ) :=
  if n ∈ S ∨ F n ∈ S then n else F n

private theorem reserve_law {F : ℕ → ℕ} (back : Function.Involutive F)
    (legal : ∀ n,F n=n ∨ GlobalDyadicOneTwoRel n (F n)) (S : Set ℕ) (n : ℕ) :
    reserve F S (reserve F S n)=n ∧ (reserve F S n=n ∨ GlobalDyadicOneTwoRel n (reserve F S n)) := by
  by_cases h : n ∈ S ∨ F n ∈ S
  · have eq : reserve F S n=n := if_pos h
    exact ⟨(congrArg _ eq).trans eq,Or.inl eq⟩
  · have reverse : ¬(F n ∈ S ∨ F (F n) ∈ S) := by rw [back n,or_comm]; exact h
    simpa only [reserve,if_neg h,if_neg reverse] using And.intro (back n) (legal n)

private theorem cost_of_reserving (F : ℕ → ℕ) (back : Function.Involutive F)
    (legal : ∀ n,F n=n ∨ GlobalDyadicOneTwoRel n (F n)) (S : Set ℕ) (X : ℕ) :
    (prefixUnpaid (reserve F S) X).card ≤ (prefixUnpaid F X).card+
      2*((Icc 1 X).filter (· ∈ S)).card := by
  let A := (Icc 1 X).filter (· ∈ S)
  have sub : prefixUnpaid (reserve F S) X ⊆ prefixUnpaid F X ∪ (A ∪ A.image F) := by
    intro n hn
    obtain ⟨sf,unpaid⟩ := mem_filter.mp hn
    have inputs := mem_filter.mp sf
    by_cases old : F n=n ∨ X<F n
    · exact mem_union_left _ (mem_filter.mpr ⟨sf,old⟩)
    have closed : F n ≤ X := le_of_not_gt (fun bad => old (Or.inr bad))
    have touched : n ∈ S ∨ F n ∈ S := by
      by_contra no
      rw [reserve,if_neg no] at unpaid
      exact old unpaid
    apply mem_union_right
    rcases touched with chosen | chosen
    · exact mem_union_left _ (mem_filter.mpr ⟨inputs.1,chosen⟩)
    · have moved := (legal n).resolve_left (fun eq => old (Or.inl eq))
      exact mem_union_right _ (mem_image.mpr ⟨F n,mem_filter.mpr
        ⟨mem_Icc.mpr ⟨Nat.pos_of_ne_zero moved.2.1.ne_zero,closed⟩,chosen⟩,back n⟩)
  have count : (A ∪ A.image F).card ≤ 2*A.card := by
    have h := card_union_le A (A.image F)
    have hi : (A.image F).card ≤ A.card := card_image_le
    omega
  exact (card_le_card sub).trans ((card_union_le ..).trans (Nat.add_le_add_left count _))

/-- Errors against a prescribed squarefree support, including the unit. -/
def supportErrors (G : ℕ → ℕ) (S : Set ℕ) (X : ℕ) := (squarefreeOf (Icc 1 X)).filter
  (fun n => ¬(G n=n ↔ n=1 ∨ n ∈ S))

/-- Signed charge changes by at most the number of incorrectly
classified squarefree vertices, simultaneously at both signs. -/
theorem fixed_charge_error_le_support_errors (G : ℕ → ℕ) (S : Set ℕ) (X : ℕ) :
    |fixedSignedPrefix G X-
      (∑ n ∈ (squarefreeOf (Icc 1 X)).filter (fun n => n=1 ∨ n ∈ S),(μ n:ℝ))| ≤
      (supportErrors G S X).card := by
  let I := squarefreeOf (Icc 1 X)
  let want := fun n : ℕ => n=1 ∨ n ∈ S
  change |(∑ n ∈ I.filter (fun n => G n=n),(μ n:ℝ))-(∑ n ∈ I.filter want,(μ n:ℝ))| ≤
    ((I.filter (fun n => ¬(G n=n ↔ want n))).card:ℝ)
  rw [sum_filter,sum_filter,←sum_sub_distrib]
  apply (abs_sum_le_sum_abs ..).trans
  rw [←sum_boole]
  apply sum_le_sum
  intro n _
  have one : |(μ n:ℝ)| ≤ 1 := by exact_mod_cast (abs_moebius_le_one (n := n))
  by_cases fixed : G n=n <;> by_cases selected : want n <;> simp [fixed,selected,one]

/-- Any set can be prescribed, whether or not its vertices were
originally fixed. Only already-closed edges incident with the target
cost additional unpaid vertices; upper endpoints of repaired edges
account for every classification error. -/
theorem prescribe_any_squarefree_support (F : ℕ → ℕ) (back : Function.Involutive F)
    (legal : ∀ n,F n=n ∨ GlobalDyadicOneTwoRel n (F n)) (S : Set ℕ) (B : ℕ → ℕ) :
    ∃ G : ℕ → ℕ,Function.Involutive G ∧ (∀ n,G n=n ∨ GlobalDyadicOneTwoRel n (G n)) ∧
      ∀ X : ℕ,let D := ((range (X+1)).filter (fun k => B k<X)).card
        (supportErrors G S X).card ≤ D ∧
        (prefixUnpaid G X).card ≤ (prefixUnpaid F X).card+2*((Icc 1 X).filter (· ∈ S)).card+2*D := by
  let R := reserve F S
  have law := reserve_law back legal S
  obtain ⟨G,invol,rel,estimate⟩ := prescribe_fixed_vertices_at_all_cutoffs R
    (fun n => (law n).1) (fun n => (law n).2) S B
  refine ⟨G,invol,rel,fun X => ⟨?_,?_⟩⟩
  · have eq : supportErrors G S X=fixedErrors R G S X := by
      ext n
      by_cases selected : n ∈ S
      · have held : R n=n := if_pos (Or.inl selected)
        simp [supportErrors,fixedErrors,selected,held]
      · simp [supportErrors,fixedErrors,selected]
    rw [eq]; exact (estimate X).1
  · exact (estimate X).2.trans (Nat.add_le_add_right (cost_of_reserving F back legal S X) _)

/-- A separation threshold can make the count of visible repairs smaller
than both the square root and a prescribed diverging envelope. -/
theorem separation_threshold_within_envelope (w : ℕ → ℝ) (pos : ∀ n,0 ≤ w n) (top : Tendsto w atTop atTop) :
    ∃ B : ℕ → ℕ,∀ X : ℕ,let D := ((range (X+1)).filter (fun n => B n<X)).card
      (D:ℝ) ≤ w X/4 ∧ D ≤ Nat.sqrt X := by
  let b := fun k : ℕ => (eventually_atTop.mp (top.eventually_ge_atTop (4*((k:ℝ)+1)))).choose
  let B := fun k : ℕ => max (b k) ((k+1)^2)
  refine ⟨B,?_⟩
  intro X
  let S := (range (X+1)).filter (fun n => B n<X)
  have sub : S ⊆ range ⌊w X/4⌋₊ := by
    intro k hk
    have hs := (le_max_left ..).trans (mem_filter.mp hk).2.le
    have hh := (eventually_atTop.mp (top.eventually_ge_atTop (4*((k:ℝ)+1)))).choose_spec X hs
    exact mem_range.mpr (Nat.le_floor (by push_cast; linarith only [hh] : ((k+1:ℕ):ℝ) ≤ w X/4))
  have bound : S.card ≤ ⌊w X/4⌋₊ := (card_le_card sub).trans_eq (card_range _)
  have sub' : S ⊆ range (Nat.sqrt X) := by
    intro k hk
    have hz := (le_max_right ..).trans (mem_filter.mp hk).2.le
    exact mem_range.mpr (Nat.le_sqrt.mpr (by simpa only [pow_two] using hz))
  exact ⟨(Nat.cast_le.mpr bound).trans (Nat.floor_le (div_nonneg (pos X) (by norm_num))),
    (card_le_card sub').trans_eq (card_range _)⟩

/-- The number of possible lower endpoints below the square-root
threshold has zero natural density. -/
theorem square_root_repair_cost_is_sublinear {c : ℝ} (hc : 0<c) :
    ∀ᶠ X : ℕ in atTop,(Nat.sqrt X:ℝ) ≤ c*X := by
  let J := ⌈1/c⌉₊
  filter_upwards [eventually_ge_atTop (J^2)] with X late
  have bound : J ≤ Nat.sqrt X := Nat.le_sqrt.mpr (by simpa only [pow_two] using late)
  have one := (div_le_iff₀ hc).mp ((Nat.le_ceil (1/c)).trans (Nat.cast_le.mpr bound))
  have square : ((Nat.sqrt X:ℕ):ℝ)^2 ≤ X := by exact_mod_cast Nat.sqrt_le' X
  have lo := mul_le_mul_of_nonneg_right one (Nat.cast_nonneg (α := ℝ) (Nat.sqrt X))
  linarith only [lo,mul_le_mul_of_nonneg_left square hc.le]

/-- The squarefree supports realizable by a matching with sublinear
unpaid count, up to arbitrarily slowly growing classification error,
are exactly the supports of density zero. -/
theorem realizable_sparse_squarefree_supports (S : Set ℕ) (sq : ∀ n ∈ S,Squarefree n) :
    (∀ ε : ℝ,0<ε → ∀ᶠ X : ℕ in atTop,(((Icc 1 X).filter (· ∈ S)).card:ℝ) ≤ ε*X) ↔
    ∀ w : ℕ → ℝ,(∀ n,0 ≤ w n) → Tendsto w atTop atTop →
      ∃ G : ℕ → ℕ,Function.Involutive G ∧ (∀ n,G n=n ∨ GlobalDyadicOneTwoRel n (G n)) ∧
        (∀ ε : ℝ,0<ε → ∀ᶠ X : ℕ in atTop,((prefixUnpaid G X).card:ℝ) ≤ ε*X) ∧
        ∀ X : ℕ,((supportErrors G S X).card:ℝ) ≤ w X ∧
          (supportErrors G S X).card ≤ Nat.sqrt X := by
  constructor
  · intro sparse w pos top
    obtain ⟨B,cost⟩ := separation_threshold_within_envelope w pos top
    obtain ⟨back,legal,_,density⟩ := one_involution_with_sublinear_unpaid_prefix
    obtain ⟨G,bk,lg,estimate⟩ := prescribe_any_squarefree_support _ back legal S B
    refine ⟨G,bk,lg,?_,fun X => ⟨?_,(estimate X).1.trans (cost X).2⟩⟩
    · intro ε he
      have hh : 0<ε/6 := div_pos he (by norm_num)
      filter_upwards [density (ε/6) hh,sparse (ε/6) hh,square_root_repair_cost_is_sublinear hh] with X h1 h2 h3
      have charge := (Nat.cast_le (α := ℝ)).mpr (estimate X).2
      have bound := (Nat.cast_le (α := ℝ)).mpr (cost X).2
      push_cast only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at charge
      linarith only [charge,h1.1,h2,h3,bound,mul_nonneg he.le (Nat.cast_nonneg (α := ℝ) X)]
    · have hh := (Nat.cast_le (α := ℝ)).mpr (estimate X).1
      exact (hh.trans (cost X).1).trans (by linarith only [pos X])
  · intro realize ε he
    obtain ⟨G,_,_,density,err⟩ := realize (fun n => (n:ℝ)) (fun n => Nat.cast_nonneg _) tendsto_natCast_atTop_atTop
    filter_upwards [density (ε/2) (half_pos he),square_root_repair_cost_is_sublinear (half_pos he)] with X h1 h2
    have sub : (Icc 1 X).filter (· ∈ S) ⊆ prefixUnpaid G X ∪ supportErrors G S X := by
      intro n hn
      obtain ⟨hi,sel⟩ := mem_filter.mp hn
      have sf : n ∈ squarefreeOf (Icc 1 X) := mem_filter.mpr ⟨hi,sq n sel⟩
      by_cases fixed : G n=n
      · exact mem_union_left _ (mem_filter.mpr ⟨sf,Or.inl fixed⟩)
      · exact mem_union_right _ (mem_filter.mpr ⟨sf,fun h => fixed (h.mpr (Or.inr sel))⟩)
    have whole := (Nat.cast_le (α := ℝ)).mpr ((card_le_card sub).trans (card_union_le ..))
    rw [Nat.cast_add] at whole
    linarith only [whole,h1,h2,(Nat.cast_le (α := ℝ)).mpr (err X).2]

#print axioms realizable_sparse_squarefree_supports

#print axioms prescribe_any_squarefree_support

#print axioms prescribe_fixed_vertices_at_all_cutoffs

end GaloisForLFunctions.RestrictedFactorizationCalculus
