import GaloisForLFunctions.HTGeometry.ApartmentClassMono
import Mathlib.GroupTheory.Perm.Sign

/-!
# The chains of a Boolean apartment are the orderings of the frame

A top chain of the apartment of a frame has one vertex of every size between one and `N - 1`: the
sizes strictly increase, start at one and end below `N`, and there is no room for anything else.  So
a top chain is a nested family of initial segments, and every ordering of the frame produces one.

This is the combinatorial skeleton of the Coxeter sphere of a frame — the indexing an explicit
fundamental cycle needs.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Simplicial Opposite

universe u

/-! ## Strictly monotone families of naturals on a finite interval -/

section StrictMonoBounds

/-- **A strictly monotone family of naturals grows by at least one per step.** -/
theorem strictMono_add_le {m : ℕ} {g : Fin (m + 1) → ℕ} (hg : StrictMono g) (i : Fin (m + 1)) :
    ∀ (j : Fin (m + 1)), i ≤ j → g i + ((j : ℕ) - (i : ℕ)) ≤ g j := by
  intro j
  induction j using Fin.induction with
  | zero =>
      intro hij
      have h0 : i = 0 := le_antisymm hij (Fin.zero_le i)
      subst h0
      simp
  | succ j ih =>
      intro hij
      rcases eq_or_lt_of_le hij with heq | hlt
      · subst heq
        simp
      · have hle : i ≤ j.castSucc := Fin.le_castSucc_iff.2 hlt
        have hih := ih hle
        have hstep : g j.castSucc < g j.succ := hg Fin.castSucc_lt_succ
        have hc : ((j.castSucc : Fin (m + 1)) : ℕ) = (j : ℕ) := Fin.val_castSucc j
        have hs : ((j.succ : Fin (m + 1)) : ℕ) = (j : ℕ) + 1 := Fin.val_succ j
        have hij' : (i : ℕ) ≤ (j : ℕ) := by
          have := Fin.le_iff_val_le_val.1 hle
          omega
        omega

theorem strictMono_zero_add_le {m : ℕ} {g : Fin (m + 1) → ℕ} (hg : StrictMono g)
    (i : Fin (m + 1)) : g 0 + (i : ℕ) ≤ g i := by
  have h := strictMono_add_le hg 0 i (Fin.zero_le i)
  simpa using h

theorem strictMono_le_last {m : ℕ} {g : Fin (m + 1) → ℕ} (hg : StrictMono g) (i : Fin (m + 1)) :
    g i + (m - (i : ℕ)) ≤ g (Fin.last m) := by
  have h := strictMono_add_le hg i (Fin.last m) (Fin.le_last i)
  simpa using h

end StrictMonoBounds

/-! ## The sizes along a top chain -/

section Chains

variable {ι : Type u}

/-- **Along a top chain of a Boolean apartment the `i`-th vertex has `i + 1` frame vectors.** -/
theorem apartment_chain_ncard [Finite ι] {N m : ℕ} (hN : Nat.card ι = N) (hm : m + 1 = N - 1)
    {f : Fin (m + 1) → properPart (Set ι)} (hf : StrictMono f) (i : Fin (m + 1)) :
    ((f i : Set ι)).ncard = (i : ℕ) + 1 := by
  have hmono : StrictMono fun j : Fin (m + 1) => ((f j : Set ι)).ncard := fun j j' hjj' =>
    Set.ncard_lt_ncard (hf hjj') (Set.toFinite _)
  have hzero : 1 ≤ ((f 0 : Set ι)).ncard :=
    Set.ncard_pos (Set.toFinite _) |>.2 (Set.nonempty_iff_ne_empty.2 (ne_of_gt (f 0).2.1))
  have hlast : ((f (Fin.last m) : Set ι)).ncard ≤ N - 1 := by
    have h : ((f (Fin.last m) : Set ι)).ncard < (Set.univ : Set ι).ncard :=
      Set.ncard_lt_ncard (f (Fin.last m)).2.2 (Set.toFinite _)
    rw [Set.ncard_univ, hN] at h
    omega
  have h1 := strictMono_zero_add_le hmono i
  have h2 := strictMono_le_last hmono i
  have hi : (i : ℕ) < m + 1 := i.isLt
  omega

/-! ## Orderings give chains -/

/-- The initial segment of an ordering of the frame. -/
def initialSegSet {N : ℕ} (e : Fin N ≃ ι) (i : Fin N) : Set ι := e '' {j | j ≤ i}

theorem ncard_initialSegSet {N : ℕ} (e : Fin N ≃ ι) (i : Fin N) :
    (initialSegSet e i).ncard = (i : ℕ) + 1 := by
  classical
  rw [initialSegSet, Set.ncard_image_of_injective _ e.injective]
  have hset : {j : Fin N | j ≤ i} = ((Finset.Iic i : Finset (Fin N)) : Set (Fin N)) := by
    ext j
    simp
  rw [hset, Set.ncard_coe_finset, Fin.card_Iic]

theorem initialSegSet_mono {N : ℕ} (e : Fin N ≃ ι) : Monotone (initialSegSet e) := by
  intro i j hij
  exact Set.image_mono fun k hk => le_trans hk hij

theorem initialSegSet_strictMono {N : ℕ} (e : Fin N ≃ ι) : StrictMono (initialSegSet e) := by
  intro i j hij
  refine lt_of_le_of_ne (initialSegSet_mono e (le_of_lt hij)) fun hcon => ?_
  have h := ncard_initialSegSet e i
  rw [hcon, ncard_initialSegSet e j] at h
  omega

/-- **The top chain of the apartment attached to an ordering of the frame.**  Its `i`-th vertex is
the set of the first `i + 1` frame vectors. -/
def chainOfOrdering {n : ℕ} (e : Fin (n + 2) ≃ ι) (i : Fin (n + 1)) : properPart (Set ι) :=
  ⟨initialSegSet e i.castSucc, by
    refine Set.empty_ssubset.2 (Set.nonempty_of_ncard_ne_zero ?_)
    rw [ncard_initialSegSet]
    omega, by
    refine Set.ssubset_univ_iff.2 fun hcon => ?_
    have hcard : (initialSegSet e i.castSucc).ncard = (i : ℕ) + 1 := ncard_initialSegSet e _
    have huniv : (Set.univ : Set ι).ncard = n + 2 := by
      rw [Set.ncard_univ, ← Nat.card_congr e, Nat.card_fin]
    rw [hcon, huniv] at hcard
    have : (i : ℕ) < n + 1 := i.isLt
    omega⟩

theorem chainOfOrdering_strictMono {n : ℕ} (e : Fin (n + 2) ≃ ι) :
    StrictMono (chainOfOrdering e) := by
  intro i j hij
  exact initialSegSet_strictMono e (Fin.castSucc_lt_castSucc_iff.2 hij)

/-- **An ordering of a frame gives a top simplex of its apartment.** -/
theorem chainOfOrdering_nonDegenerate {n : ℕ} (e : Fin (n + 2) ≃ ι) :
    (Monotone.functor (chainOfOrdering_strictMono e).monotone :
        (nerve (properPart (Set ι))) _⦋n⦌) ∈ (nerve (properPart (Set ι))).nonDegenerate n :=
  (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono _).2 (chainOfOrdering_strictMono e)

theorem initialSegSet_last {n : ℕ} (e : Fin (n + 2) ≃ ι) :
    initialSegSet e (Fin.last (n + 1)) = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  exact ⟨e.symm x, Fin.le_last _, by simp⟩

theorem initialSegSet_succ {n : ℕ} (e : Fin (n + 2) ≃ ι) (j : Fin (n + 1)) :
    initialSegSet e j.succ = insert (e j.succ) (initialSegSet e j.castSucc) := by
  ext x
  simp only [initialSegSet, Set.mem_image, Set.mem_setOf_eq, Set.mem_insert_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    rcases eq_or_lt_of_le hk with rfl | hlt
    · exact Or.inl rfl
    · exact Or.inr ⟨k, Fin.le_castSucc_iff.2 hlt, rfl⟩
  · rintro (rfl | ⟨k, hk, rfl⟩)
    · exact ⟨j.succ, le_rfl, rfl⟩
    · exact ⟨k, le_trans hk (Fin.castSucc_le_succ j), rfl⟩

theorem notMem_initialSegSet_succ {n : ℕ} (e : Fin (n + 2) ≃ ι) (j : Fin (n + 1)) :
    e j.succ ∉ initialSegSet e j.castSucc := by
  rintro ⟨k, hk, hke⟩
  have : k = j.succ := e.injective hke
  subst this
  exact absurd (Fin.le_castSucc_iff.1 hk) (lt_irrefl _)

theorem initialSegSet_zero {n : ℕ} (e : Fin (n + 2) ≃ ι) : initialSegSet e 0 = {e 0} := by
  ext x
  simp only [initialSegSet, Set.mem_image, Set.mem_setOf_eq, Set.mem_singleton_iff]
  exact ⟨fun ⟨k, hk, hkx⟩ => by rw [← hkx, le_antisymm hk (Fin.zero_le k)],
    fun hx => ⟨0, le_rfl, hx.symm⟩⟩

/-- An ordering's first vector is read off its first initial segment. -/
theorem ordering_eq_zero_of_seg {n : ℕ} (e e' : Fin (n + 2) ≃ ι)
    (h : initialSegSet e' 0 = initialSegSet e 0) : e' 0 = e 0 := by
  rw [initialSegSet_zero, initialSegSet_zero] at h
  exact Set.singleton_eq_singleton_iff.1 h

/-- An ordering's later vectors are read off consecutive initial segments. -/
theorem ordering_eq_succ_of_segs {n : ℕ} (e e' : Fin (n + 2) ≃ ι) (j : Fin (n + 1))
    (h1 : initialSegSet e' j.castSucc = initialSegSet e j.castSucc)
    (h2 : initialSegSet e' j.succ = initialSegSet e j.succ) : e' j.succ = e j.succ := by
  rw [initialSegSet_succ, initialSegSet_succ, h1] at h2
  have hmem : e' j.succ ∈ insert (e j.succ) (initialSegSet e j.castSucc) := by
    rw [← h2]
    exact Set.mem_insert _ _
  rcases hmem with hx | hx
  · exact hx
  · exact absurd (h1 ▸ hx) (notMem_initialSegSet_succ e' j)

/-- **Distinct orderings of a frame give distinct top chains.**  An ordering is read off its chain of
initial segments one vector at a time. -/
theorem chainOfOrdering_injective {n : ℕ} :
    Function.Injective (chainOfOrdering (ι := ι) (n := n)) := by
  intro e e' heq
  have hseg : ∀ j : Fin (n + 2), initialSegSet e j = initialSegSet e' j := by
    intro j
    rcases eq_or_lt_of_le (Fin.le_last j) with rfl | hlt
    · rw [initialSegSet_last, initialSegSet_last]
    · obtain ⟨i, rfl⟩ : ∃ i : Fin (n + 1), i.castSucc = j :=
        ⟨⟨(j : ℕ), by have := Fin.lt_last_iff_ne_last.2 (ne_of_lt hlt); omega⟩, by
          refine Fin.ext ?_
          simp⟩
      exact congrArg (fun c : Fin (n + 1) → properPart (Set ι) => ((c i : properPart (Set ι)) :
        Set ι)) heq
  refine Equiv.ext fun j => ?_
  induction j using Fin.induction with
  | zero => exact ordering_eq_zero_of_seg e' e (hseg 0)
  | succ j _ => exact ordering_eq_succ_of_segs e' e j (hseg _) (hseg _)

/-- The last proper initial segment of an ordering is the complement of its last vector. -/
theorem initialSegSet_castSucc_last {n : ℕ} (e : Fin (n + 2) ≃ ι) :
    initialSegSet e (Fin.last n).castSucc = Set.univ \ {e (Fin.last (n + 1))} := by
  ext x
  simp only [initialSegSet, Set.mem_image, Set.mem_setOf_eq, Set.mem_sdiff, Set.mem_univ,
    Set.mem_singleton_iff, true_and]
  constructor
  · rintro ⟨j, hj, rfl⟩
    intro hcon
    have hjl : j = Fin.last (n + 1) := e.injective hcon
    rw [hjl, Fin.le_def] at hj
    simp only [Fin.val_last, Fin.val_castSucc] at hj
    omega
  · intro hx
    refine ⟨e.symm x, ?_, by simp⟩
    rw [Fin.le_def]
    simp only [Fin.val_castSucc, Fin.val_last]
    have hne : e.symm x ≠ Fin.last (n + 1) := fun hcon => hx (by rw [← hcon]; simp)
    have := (e.symm x).isLt
    have hval : (e.symm x : ℕ) ≠ n + 1 := fun hcon => hne (Fin.ext (by simpa using hcon))
    omega

/-! ## Bijections that agree off a pair -/

/-- **Two bijections that agree outside a two-element set are equal or differ by the transposition
of that set.** -/
theorem eq_or_swap_of_agree_off_two {α β : Type*} [DecidableEq α] (e e' : α ≃ β) {a b : α}
    (hab : a ≠ b) (h : ∀ x, x ≠ a → x ≠ b → e' x = e x) :
    e' = e ∨ e' = (Equiv.swap a b).trans e := by
  have hmem : ∀ x : α, (x = a ∨ x = b) → (e' x = e a ∨ e' x = e b) := by
    intro x hx
    obtain ⟨y, hy⟩ := e.surjective (e' x)
    by_cases hya : y = a
    · exact Or.inl (by rw [← hy, hya])
    · by_cases hyb : y = b
      · exact Or.inr (by rw [← hy, hyb])
      · exfalso
        have : e' x = e' y := by rw [← hy, h y hya hyb]
        have hxy : x = y := e'.injective this
        rcases hx with rfl | rfl
        · exact hya hxy.symm
        · exact hyb hxy.symm
  rcases hmem a (Or.inl rfl) with ha | ha
  · refine Or.inl (Equiv.ext fun x => ?_)
    by_cases hxa : x = a
    · rw [hxa, ha]
    · by_cases hxb : x = b
      · subst hxb
        rcases hmem x (Or.inr rfl) with hb | hb
        · exact absurd (e'.injective (hb.trans ha.symm)) hab.symm
        · exact hb
      · exact h x hxa hxb
  · refine Or.inr (Equiv.ext fun x => ?_)
    by_cases hxa : x = a
    · subst hxa
      rw [Equiv.trans_apply, Equiv.swap_apply_left, ha]
    · by_cases hxb : x = b
      · subst hxb
        rw [Equiv.trans_apply, Equiv.swap_apply_right]
        rcases hmem x (Or.inr rfl) with hb | hb
        · exact hb
        · exact absurd (e'.injective (hb.trans ha.symm)) hab.symm
      · rw [Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne hxa hxb]
        exact h x hxa hxb

/-! ## The two orderings that fill a face -/

/-- An initial segment is unchanged by a transposition of two vectors that are both inside it or
both outside it. -/
theorem image_swap_Iic {n : ℕ} (a b : Fin (n + 2)) (i : Fin (n + 2))
    (h : (a ≤ i ∧ b ≤ i) ∨ (i < a ∧ i < b)) :
    (Equiv.swap a b) '' {j : Fin (n + 2) | j ≤ i} = {j : Fin (n + 2) | j ≤ i} := by
  have hmem : ∀ j : Fin (n + 2), (Equiv.swap a b j ≤ i ↔ j ≤ i) := by
    intro j
    by_cases hja : j = a
    · subst hja
      rw [Equiv.swap_apply_left]
      rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact ⟨fun _ => ha, fun _ => hb⟩
      · exact ⟨fun hcon => absurd hcon (not_le_of_gt hb), fun hcon => absurd hcon (not_le_of_gt ha)⟩
    · by_cases hjb : j = b
      · subst hjb
        rw [Equiv.swap_apply_right]
        rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · exact ⟨fun _ => hb, fun _ => ha⟩
        · exact ⟨fun hcon => absurd hcon (not_le_of_gt ha),
            fun hcon => absurd hcon (not_le_of_gt hb)⟩
      · rw [Equiv.swap_apply_of_ne_of_ne hja hjb]
  ext x
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact (hmem j).2 hj
  · intro hx
    exact ⟨Equiv.swap a b x, (hmem x).2 hx, Equiv.swap_apply_self a b x⟩

theorem initialSegSet_swap {n : ℕ} (e : Fin (n + 2) ≃ ι) (a b i : Fin (n + 2))
    (h : (a ≤ i ∧ b ≤ i) ∨ (i < a ∧ i < b)) :
    initialSegSet ((Equiv.swap a b).trans e) i = initialSegSet e i := by
  rw [initialSegSet, initialSegSet]
  rw [show ⇑((Equiv.swap a b).trans e) = ⇑e ∘ ⇑(Equiv.swap a b) from rfl, Set.image_comp,
    image_swap_Iic a b i h]

/-- **Swapping two adjacent vectors of an ordering changes its chain only at the index between
them.**  So the two orderings related by an adjacent transposition fill the same face. -/
theorem chainOfOrdering_swap_eq {n : ℕ} (e : Fin (n + 2) ≃ ι) (k : Fin (n + 1))
    (i : Fin (n + 1)) (hik : i ≠ k) :
    chainOfOrdering ((Equiv.swap k.castSucc k.succ).trans e) i = chainOfOrdering e i := by
  refine Subtype.ext ?_
  refine initialSegSet_swap e _ _ _ ?_
  rcases lt_or_gt_of_ne hik with hlt | hlt
  · refine Or.inr ⟨?_, ?_⟩
    · rw [Fin.lt_def]
      simp only [Fin.val_castSucc]
      exact Fin.lt_def.1 hlt
    · rw [Fin.lt_def]
      simp only [Fin.val_castSucc, Fin.val_succ]
      have := Fin.lt_def.1 hlt
      omega
  · refine Or.inl ⟨?_, ?_⟩
    · rw [Fin.le_def]
      simp only [Fin.val_castSucc]
      have := Fin.lt_def.1 hlt
      omega
    · rw [Fin.le_def]
      simp only [Fin.val_castSucc, Fin.val_succ]
      have := Fin.lt_def.1 hlt
      omega

/-- **And it does change it there.** -/
theorem chainOfOrdering_swap_ne {n : ℕ} (e : Fin (n + 2) ≃ ι) (k : Fin (n + 1)) :
    chainOfOrdering ((Equiv.swap k.castSucc k.succ).trans e) k ≠ chainOfOrdering e k := by
  intro hcon
  have hval : initialSegSet ((Equiv.swap k.castSucc k.succ).trans e) k.castSucc
      = initialSegSet e k.castSucc :=
    congrArg (fun s : properPart (Set ι) => (s : Set ι)) hcon
  have hmem : e k.succ ∈ initialSegSet e k.castSucc := by
    rw [← hval]
    refine ⟨k.castSucc, ?_, ?_⟩
    · show k.castSucc ≤ k.castSucc
      exact le_rfl
    · rw [Equiv.trans_apply, Equiv.swap_apply_left]
  exact notMem_initialSegSet_succ e k hmem

/-- **The two orderings that fill a face.**  If the chains of two orderings agree at every index but
one, the orderings are equal or differ by the transposition at that place. -/
theorem eq_or_swap_of_chainOfOrdering_agree {n : ℕ} (e e' : Fin (n + 2) ≃ ι) (k : Fin (n + 1))
    (h : ∀ i : Fin (n + 1), i ≠ k → chainOfOrdering e' i = chainOfOrdering e i) :
    e' = e ∨ e' = (Equiv.swap k.castSucc k.succ).trans e := by
  have hseg : ∀ j : Fin (n + 2), j ≠ k.castSucc → initialSegSet e' j = initialSegSet e j := by
    intro j hj
    rcases eq_or_lt_of_le (Fin.le_last j) with rfl | hlt
    · rw [initialSegSet_last, initialSegSet_last]
    · obtain ⟨i, rfl⟩ : ∃ i : Fin (n + 1), i.castSucc = j :=
        ⟨⟨(j : ℕ), by have := Fin.lt_def.1 hlt; simp at this; omega⟩, by
          refine Fin.ext ?_
          simp⟩
      have hik : i ≠ k := fun hcon => hj (by rw [hcon])
      exact congrArg (fun s : properPart (Set ι) => (s : Set ι)) (h i hik)
  refine eq_or_swap_of_agree_off_two e e'
    (Fin.ne_of_lt (Fin.castSucc_lt_succ (i := k))) fun x hxa hxb => ?_
  induction x using Fin.cases with
  | zero => exact ordering_eq_zero_of_seg e e' (hseg 0 hxa)
  | succ j =>
      refine ordering_eq_succ_of_segs e e' j ?_ (hseg j.succ hxa)
      refine hseg j.castSucc fun hcon => hxb ?_
      have hjk : j = k := by
        have := congrArg Fin.val hcon
        simp only [Fin.val_castSucc] at this
        exact Fin.ext this
      rw [hjk]

/-- The vertices of a face of a simplex of a nerve. -/
theorem nerve_delta_obj {P : Type u} [PartialOrder P] {m : ℕ} (x : (nerve P) _⦋m + 1⦌)
    (i : Fin (m + 2)) (a : Fin (m + 1)) :
    (((nerve P).δ i x : (nerve P) _⦋m⦌)).obj a = x.obj (i.succAbove a) := rfl

/-- **A face of a nondegenerate simplex of a nerve is nondegenerate.** -/
theorem nerve_delta_nonDegenerate {P : Type u} [PartialOrder P] {m : ℕ} (x : (nerve P) _⦋m + 1⦌)
    (hx : x ∈ (nerve P).nonDegenerate (m + 1)) (i : Fin (m + 2)) :
    (nerve P).δ i x ∈ (nerve P).nonDegenerate m := by
  refine (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono _).2 fun a b hab => ?_
  rw [nerve_delta_obj, nerve_delta_obj]
  exact (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono x).1 hx
    (Fin.strictMono_succAbove i hab)

/-! ## The fundamental chain of the Coxeter sphere -/

/-- The top simplex of the apartment attached to an ordering of the frame. -/
noncomputable def apartmentChainSimplex {n : ℕ} (e : Fin (n + 2) ≃ ι) :
    (nerve (properPart (Set ι))) _⦋n⦌ :=
  Monotone.functor (chainOfOrdering_strictMono e).monotone

theorem apartmentChainSimplex_obj {n : ℕ} (e : Fin (n + 2) ≃ ι) (i : Fin (n + 1)) :
    (apartmentChainSimplex e).obj i = chainOfOrdering e i := rfl

theorem delta_apartmentChainSimplex_obj {n : ℕ} (e : Fin (n + 3) ≃ ι) (i : Fin (n + 2))
    (j : Fin (n + 1)) :
    (((nerve (properPart (Set ι))).δ i (apartmentChainSimplex e) :
      (nerve (properPart (Set ι))) _⦋n⦌)).obj j = chainOfOrdering e (i.succAbove j) := rfl

/-- **The two orderings related by an adjacent transposition have the same face.** -/
theorem delta_apartmentChainSimplex_swap {n : ℕ} (e : Fin (n + 3) ≃ ι) (i : Fin (n + 2)) :
    (nerve (properPart (Set ι))).δ i
        (apartmentChainSimplex ((Equiv.swap i.castSucc i.succ).trans e))
      = (nerve (properPart (Set ι))).δ i (apartmentChainSimplex e) := by
  refine nerve_simplex_ext fun j => ?_
  rw [delta_apartmentChainSimplex_obj, delta_apartmentChainSimplex_obj]
  exact chainOfOrdering_swap_eq e i (i.succAbove j) (Fin.succAbove_ne i j)

/-- The vertex sizes along a chain of initial segments. -/
theorem ncard_chainOfOrdering {n : ℕ} (e : Fin (n + 2) ≃ ι) (i : Fin (n + 1)) :
    ((chainOfOrdering e i : properPart (Set ι)) : Set ι).ncard = (i : ℕ) + 1 := by
  show (initialSegSet e i.castSucc).ncard = (i : ℕ) + 1
  rw [ncard_initialSegSet]
  simp

/-- **The index of a face is determined by the face.**  Two faces of chambers of an apartment agree
only if they are faces at the same place. -/
theorem face_index_eq {n : ℕ} (e e' : Fin (n + 3) ≃ ι) (i j : Fin (n + 2))
    (h : (nerve (properPart (Set ι))).δ i (apartmentChainSimplex e)
      = (nerve (properPart (Set ι))).δ j (apartmentChainSimplex e')) : i = j := by
  refine Fin.succAbove_left_injective (funext fun l => ?_)
  have hobj : chainOfOrdering e (i.succAbove l) = chainOfOrdering e' (j.succAbove l) := by
    have := congrArg (fun s : (nerve (properPart (Set ι))) _⦋n⦌ => s.obj l) h
    rw [delta_apartmentChainSimplex_obj, delta_apartmentChainSimplex_obj] at this
    exact this
  have hcard := congrArg (fun s : properPart (Set ι) => (s : Set ι).ncard) hobj
  rw [ncard_chainOfOrdering, ncard_chainOfOrdering] at hcard
  exact Fin.ext (by omega)

/-- **Thinness of the Coxeter complex.**  A face of a chamber lies in exactly two chambers: the one
it came from, and its partner under the transposition at that place. -/
theorem face_eq_iff {n : ℕ} (e₀ : Fin (n + 3) ≃ ι) (σ τ : Equiv.Perm (Fin (n + 3)))
    (i j : Fin (n + 2)) :
    (nerve (properPart (Set ι))).δ j (apartmentChainSimplex (τ.trans e₀))
        = (nerve (properPart (Set ι))).δ i (apartmentChainSimplex (σ.trans e₀))
      ↔ j = i ∧ (τ = σ ∨ τ = (Equiv.swap i.castSucc i.succ).trans σ) := by
  constructor
  · intro hface
    have hij : j = i := face_index_eq (τ.trans e₀) (σ.trans e₀) j i hface
    subst hij
    refine ⟨rfl, ?_⟩
    have hagree : ∀ k : Fin (n + 2), k ≠ j →
        chainOfOrdering (τ.trans e₀) k = chainOfOrdering (σ.trans e₀) k := by
      intro k hk
      obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hk
      have := congrArg (fun s : (nerve (properPart (Set ι))) _⦋n⦌ => s.obj l) hface
      rw [delta_apartmentChainSimplex_obj, delta_apartmentChainSimplex_obj] at this
      exact this
    rcases eq_or_swap_of_chainOfOrdering_agree (σ.trans e₀) (τ.trans e₀) j hagree with heq | heq
    · refine Or.inl (Equiv.ext fun x => e₀.injective ?_)
      exact congrArg (fun t : Fin (n + 3) ≃ ι => t x) heq
    · refine Or.inr (Equiv.ext fun x => e₀.injective ?_)
      have := congrArg (fun t : Fin (n + 3) ≃ ι => t x) heq
      simpa [Equiv.trans_apply] using this
  · rintro ⟨rfl, hτ | hτ⟩
    · rw [hτ]
    · subst hτ
      rw [Equiv.trans_assoc]
      exact delta_apartmentChainSimplex_swap (σ.trans e₀) j

/-- **A chamber of an apartment contains the line of a frame vector exactly when its ordering starts
with that vector.**  This is the splitting of the chambers of an apartment into those inside the
star of a vertex and those outside it. -/
theorem chainOfOrdering_eq_singleton_iff {n : ℕ} [Finite ι] (e : Fin (n + 2) ≃ ι) (a : ι)
    (i : Fin (n + 1)) :
    ((chainOfOrdering e i : properPart (Set ι)) : Set ι) = {a} ↔ ((i : ℕ) = 0 ∧ e 0 = a) := by
  constructor
  · intro h
    have hcard := ncard_chainOfOrdering e i
    rw [h, Set.ncard_singleton] at hcard
    have hi : (i : ℕ) = 0 := by omega
    refine ⟨hi, ?_⟩
    have hzero : ((chainOfOrdering e i : properPart (Set ι)) : Set ι) = initialSegSet e 0 := by
      have : i = 0 := Fin.ext hi
      rw [this]
      rfl
    rw [hzero, initialSegSet_zero] at h
    exact Set.singleton_eq_singleton_iff.1 h
  · rintro ⟨hi, rfl⟩
    have : i = 0 := Fin.ext hi
    rw [this]
    show initialSegSet e 0 = {e 0}
    exact initialSegSet_zero e

/-- **A chamber of an apartment contains the coatom opposite a frame vector exactly when its
ordering ends with that vector.**  This is the splitting of the chambers of an apartment into those
inside the star of the spanning coatom and those outside it. -/
theorem chainOfOrdering_eq_compl_singleton_iff {n : ℕ} [Finite ι] (hN : Nat.card ι = n + 2)
    (e : Fin (n + 2) ≃ ι) (a : ι) (i : Fin (n + 1)) :
    ((chainOfOrdering e i : properPart (Set ι)) : Set ι) = Set.univ \ {a}
      ↔ ((i : ℕ) = n ∧ e (Fin.last (n + 1)) = a) := by
  have hcompl : (Set.univ \ {a} : Set ι).ncard = n + 1 := by
    rw [Set.ncard_sdiff_singleton_of_mem (Set.mem_univ a), Set.ncard_univ, hN]
    omega
  have hlast : ∀ e' : Fin (n + 2) ≃ ι,
      ((chainOfOrdering e' (Fin.last n) : properPart (Set ι)) : Set ι)
        = Set.univ \ {e' (Fin.last (n + 1))} := fun e' => initialSegSet_castSucc_last e'
  constructor
  · intro h
    have hcard := ncard_chainOfOrdering e i
    rw [h, hcompl] at hcard
    have hi : (i : ℕ) = n := by omega
    refine ⟨hi, ?_⟩
    have hie : i = Fin.last n := Fin.ext (by simpa using hi)
    rw [hie, hlast e] at h
    by_contra hne
    have hmem : a ∈ Set.univ \ ({e (Fin.last (n + 1))} : Set ι) :=
      ⟨Set.mem_univ a, fun hcon => hne (Set.mem_singleton_iff.1 hcon).symm⟩
    rw [h] at hmem
    exact hmem.2 rfl
  · rintro ⟨hi, rfl⟩
    have hie : i = Fin.last n := Fin.ext (by simpa using hi)
    rw [hie]
    exact hlast e

/-- **The only vertex of an apartment that spans with a frame vector is the coatom opposite it.**
So every vertex of a chamber that misses that coatom is a non-spanning vertex, and such a chamber
lies in the base of the cover. -/
theorem apartment_not_spanning_of_ne {a : ι} (U : properPart (Set ι))
    (h : (U : Set ι) ≠ Set.univ \ {a}) : (U : Set ι) ∪ {a} ≠ Set.univ := by
  intro hcon
  refine h (Set.Subset.antisymm (fun x hx => ⟨Set.mem_univ x, fun hxa => ?_⟩) fun x hx => ?_)
  · refine absurd (Set.Subset.antisymm (Set.subset_univ _) fun y _ => ?_) (ne_of_lt U.2.2)
    have hy : y ∈ (U : Set ι) ∪ {a} := by rw [hcon]; trivial
    rcases hy with hy | hy
    · exact hy
    · rw [Set.mem_singleton_iff.1 hy, ← Set.mem_singleton_iff.1 hxa]
      exact hx
  · have hxu : x ∈ (U : Set ι) ∪ {a} := by rw [hcon]; exact Set.mem_univ x
    exact hxu.resolve_right hx.2

section Coefficients

variable {C : Type u} [Category.{v} C] [Preadditive C] [Limits.HasCoproducts.{u} C]

/-- **The fundamental chain of the Coxeter sphere of a frame**: the signed sum of the top simplices
of the apartment, one for each ordering of the frame. -/
noncomputable def apartmentFundamentalChain {n : ℕ} (e₀ : Fin (n + 2) ≃ ι) (R : C) :
    R ⟶ ((nerve (properPart (Set ι))).normalizedChainComplex R).X n :=
  ∑ σ : Equiv.Perm (Fin (n + 2)), (Equiv.Perm.sign σ : ℤ) •
    (nerve (properPart (Set ι))).ιNormalizedChainComplex (R := R) (apartmentChainSimplex (σ.trans e₀))

/-- **The fundamental chain is a cycle.**  Each face is shared by the two orderings that differ by
the transposition at that place, and they enter with opposite signs. -/
theorem apartmentFundamentalChain_comp_d {n : ℕ} (e₀ : Fin (n + 3) ≃ ι) (R : C) :
    apartmentFundamentalChain e₀ R
        ≫ ((nerve (properPart (Set ι))).normalizedChainComplex R).d (n + 1) n = 0 := by
  classical
  rw [apartmentFundamentalChain, Preadditive.sum_comp]
  have hterm : ∀ σ : Equiv.Perm (Fin (n + 3)),
      ((Equiv.Perm.sign σ : ℤ) • (nerve (properPart (Set ι))).ιNormalizedChainComplex (R := R)
          (apartmentChainSimplex (σ.trans e₀)))
        ≫ ((nerve (properPart (Set ι))).normalizedChainComplex R).d (n + 1) n
      = ∑ i : Fin (n + 2), ((Equiv.Perm.sign σ : ℤ) * (-1) ^ (i : ℕ)) •
          (nerve (properPart (Set ι))).ιNormalizedChainComplex (R := R)
            ((nerve (properPart (Set ι))).δ i (apartmentChainSimplex (σ.trans e₀))) := by
    intro σ
    rw [Preadditive.zsmul_comp, SSet.ιNormalizedChainComplex_d, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_smul]
  rw [Finset.sum_congr rfl fun σ _ => hterm σ, ← Finset.sum_product']
  refine Finset.sum_involution
    (fun p _ => ((Equiv.swap p.2.castSucc p.2.succ).trans p.1, p.2)) ?_ ?_ ?_ ?_
  · rintro ⟨σ, i⟩ -
    have hface : (nerve (properPart (Set ι))).δ i
        (apartmentChainSimplex ((((Equiv.swap i.castSucc i.succ).trans σ)).trans e₀))
        = (nerve (properPart (Set ι))).δ i (apartmentChainSimplex (σ.trans e₀)) := by
      rw [Equiv.trans_assoc]
      exact delta_apartmentChainSimplex_swap (σ.trans e₀) i
    have hsign : (Equiv.Perm.sign ((Equiv.swap i.castSucc i.succ).trans σ) : ℤ)
        = -(Equiv.Perm.sign σ : ℤ) := by
      have hne : i.castSucc ≠ i.succ := Fin.ne_of_lt Fin.castSucc_lt_succ
      rw [show (Equiv.swap i.castSucc i.succ).trans σ = σ * Equiv.swap i.castSucc i.succ from rfl,
        map_mul, Equiv.Perm.sign_swap hne]
      simp
    rw [hface, hsign, ← add_smul]
    simp
  · rintro ⟨σ, i⟩ - -
    intro hcon
    have h1 : (Equiv.swap i.castSucc i.succ).trans σ = σ := congrArg Prod.fst hcon
    have h2 := congrArg (fun t : Equiv.Perm (Fin (n + 3)) => t i.castSucc) h1
    simp only [Equiv.trans_apply, Equiv.swap_apply_left] at h2
    exact Fin.ne_of_lt Fin.castSucc_lt_succ (σ.injective h2).symm
  · rintro ⟨σ, i⟩ -
    exact Finset.mem_univ _
  · rintro ⟨σ, i⟩ -
    refine Prod.ext ?_ rfl
    show (Equiv.swap i.castSucc i.succ).trans ((Equiv.swap i.castSucc i.succ).trans σ) = σ
    refine Equiv.ext fun x => ?_
    simp [Equiv.swap_apply_self]

open scoped Classical in
/-- The coefficient of a normalized chain at one nondegenerate simplex. -/
noncomputable def chamberCoefficient {n : ℕ}
    (y₀ : (nerve (properPart (Set ι))).nonDegenerate n) (R : C) :
    ((nerve (properPart (Set ι))).normalizedChainComplex R).X n ⟶ R :=
  ((nerve (properPart (Set ι))).isColimitCofanNormalizedChainComplex R n).desc
    (Limits.Cofan.mk R fun y => if y = y₀ then 𝟙 R else 0)

open scoped Classical in
theorem ι_chamberCoefficient {n : ℕ} (y₀ y : (nerve (properPart (Set ι))).nonDegenerate n)
    (R : C) :
    (nerve (properPart (Set ι))).ιNormalizedChainComplex (R := R) (y : (nerve _) _⦋n⦌)
        ≫ chamberCoefficient y₀ R
      = if y = y₀ then 𝟙 R else 0 := by
  classical
  exact ((nerve (properPart (Set ι))).isColimitCofanNormalizedChainComplex R n).fac
    (Limits.Cofan.mk R fun y => if y = y₀ then 𝟙 R else 0) ⟨y⟩

open scoped Classical in
theorem ι_chamberCoefficient' {n : ℕ} (y₀ : (nerve (properPart (Set ι))).nonDegenerate n)
    (x : (nerve (properPart (Set ι))) _⦋n⦌)
    (hx : x ∈ (nerve (properPart (Set ι))).nonDegenerate n) (R : C) :
    (nerve (properPart (Set ι))).ιNormalizedChainComplex (R := R) x ≫ chamberCoefficient y₀ R
      = if (⟨x, hx⟩ : (nerve (properPart (Set ι))).nonDegenerate n) = y₀ then 𝟙 R else 0 :=
  ι_chamberCoefficient y₀ ⟨x, hx⟩ R

/-- The chamber of an ordering, as a nondegenerate simplex. -/
noncomputable def apartmentChamber {n : ℕ} (e : Fin (n + 2) ≃ ι) :
    (nerve (properPart (Set ι))).nonDegenerate n :=
  ⟨apartmentChainSimplex e, chainOfOrdering_nonDegenerate e⟩

theorem apartmentChamber_injective {n : ℕ} (e₀ : Fin (n + 2) ≃ ι) :
    Function.Injective fun σ : Equiv.Perm (Fin (n + 2)) => apartmentChamber (σ.trans e₀) := by
  intro σ σ' h
  have h1 : chainOfOrdering (σ.trans e₀) = chainOfOrdering (σ'.trans e₀) := by
    funext i
    exact congrArg (fun s : (nerve (properPart (Set ι))).nonDegenerate n =>
      ((s : (nerve (properPart (Set ι))) _⦋n⦌)).obj i) h
  have h2 : σ.trans e₀ = σ'.trans e₀ := chainOfOrdering_injective h1
  refine Equiv.ext fun x => ?_
  have := congrArg (fun t : Fin (n + 2) ≃ ι => e₀.symm (t x)) h2
  simpa using this

/-- **The fundamental chain has coefficient the sign of the ordering at each chamber.** -/
theorem apartmentFundamentalChain_coefficient {n : ℕ} (e₀ : Fin (n + 2) ≃ ι) (R : C)
    (σ₀ : Equiv.Perm (Fin (n + 2))) :
    apartmentFundamentalChain e₀ R ≫ chamberCoefficient (apartmentChamber (σ₀.trans e₀)) R
      = (Equiv.Perm.sign σ₀ : ℤ) • 𝟙 R := by
  classical
  have hcoe : ∀ σ : Equiv.Perm (Fin (n + 2)), apartmentChainSimplex (σ.trans e₀)
      = ((apartmentChamber (σ.trans e₀) : (nerve (properPart (Set ι))).nonDegenerate n) :
        (nerve (properPart (Set ι))) _⦋n⦌) := fun _ => rfl
  rw [apartmentFundamentalChain, Preadditive.sum_comp]
  rw [Finset.sum_eq_single_of_mem σ₀ (Finset.mem_univ σ₀) (fun σ _ hne => by
    rw [Preadditive.zsmul_comp, hcoe σ, ι_chamberCoefficient,
      if_neg (fun hcon => hne (apartmentChamber_injective e₀ hcon)), smul_zero])]
  rw [Preadditive.zsmul_comp, hcoe σ₀, ι_chamberCoefficient, if_pos rfl]

/-- **The fundamental chain is a split monomorphism**: the coefficient at one chamber retracts
it. -/
theorem isSplitMono_apartmentFundamentalChain {n : ℕ} (e₀ : Fin (n + 2) ≃ ι) (R : C) :
    IsSplitMono (apartmentFundamentalChain e₀ R) := by
  refine ⟨⟨(Equiv.Perm.sign (1 : Equiv.Perm (Fin (n + 2))) : ℤ) •
    chamberCoefficient (apartmentChamber ((1 : Equiv.Perm (Fin (n + 2))).trans e₀)) R, ?_⟩⟩
  rw [Preadditive.comp_zsmul, apartmentFundamentalChain_coefficient, smul_smul]
  simp

/-! ## A chain is determined by its coefficients -/

/-- The simplices of the nerve of a finite poset are finite: a simplex is determined by its
vertices. -/
instance finite_nerve_simplices {P : Type u} [PartialOrder P] [Finite P] (n : ℕ) :
    Finite ((nerve P) _⦋n⦌) :=
  Finite.of_injective (fun x : (nerve P) _⦋n⦌ => x.obj)
    fun _ _ h => nerve_simplex_ext fun i => congrFun h i

/-- **The coefficients at the chambers add up to the identity.**  For a finite apartment the
normalized top chains are a biproduct, and this is its total identity. -/
theorem chamberCoefficient_total {n : ℕ}
    [Fintype ((nerve (properPart (Set ι))).nonDegenerate n)] (R : C) :
    ∑ y : (nerve (properPart (Set ι))).nonDegenerate n,
        chamberCoefficient y R
          ≫ (nerve (properPart (Set ι))).ιNormalizedChainComplex (R := R)
            (y : (nerve (properPart (Set ι))) _⦋n⦌) = 𝟙 _ := by
  classical
  ext x hx
  rw [Preadditive.comp_sum, Category.comp_id]
  rw [Finset.sum_eq_single_of_mem (⟨x, hx⟩ : (nerve (properPart (Set ι))).nonDegenerate n)
    (Finset.mem_univ _) (fun y _ hne => by
      rw [← Category.assoc, ι_chamberCoefficient' y x hx R,
        if_neg (fun hcon => hne (by rw [← hcon])), Limits.zero_comp])]
  rw [← Category.assoc, ι_chamberCoefficient' _ x hx R, if_pos rfl, Category.id_comp]

/-- **A normalized chain with all chamber coefficients zero is zero.** -/
theorem eq_zero_of_chamberCoefficient {n : ℕ} [Finite ι] (R : C) {T : C}
    (x : T ⟶ ((nerve (properPart (Set ι))).normalizedChainComplex R).X n)
    (h : ∀ y : (nerve (properPart (Set ι))).nonDegenerate n, x ≫ chamberCoefficient y R = 0) :
    x = 0 := by
  classical
  haveI := Fintype.ofFinite ((nerve (properPart (Set ι))).nonDegenerate n)
  have htotal := chamberCoefficient_total (ι := ι) (n := n) R
  calc x = x ≫ 𝟙 _ := (Category.comp_id x).symm
    _ = x ≫ ∑ y : (nerve (properPart (Set ι))).nonDegenerate n,
          chamberCoefficient y R
            ≫ (nerve (properPart (Set ι))).ιNormalizedChainComplex (R := R)
              (y : (nerve (properPart (Set ι))) _⦋n⦌) := by rw [htotal]
    _ = 0 := by
        rw [Preadditive.comp_sum]
        refine Finset.sum_eq_zero fun y _ => ?_
        rw [← Category.assoc, h y, Limits.zero_comp]

/-- **The fundamental cycle of the Coxeter sphere of a frame**, as a map into the cycles of the
normalized chains. -/
noncomputable def apartmentFundamentalCycle {n : ℕ} [CategoryWithHomology C]
    (e₀ : Fin (n + 3) ≃ ι) (R : C) :
    R ⟶ ((nerve (properPart (Set ι))).normalizedChainComplex R).cycles (n + 1) :=
  ((nerve (properPart (Set ι))).normalizedChainComplex R).liftCycles
    (apartmentFundamentalChain e₀ R) n (by simp) (apartmentFundamentalChain_comp_d e₀ R)

@[reassoc (attr := simp)]
theorem apartmentFundamentalCycle_i {n : ℕ} [CategoryWithHomology C] (e₀ : Fin (n + 3) ≃ ι)
    (R : C) :
    apartmentFundamentalCycle e₀ R
        ≫ ((nerve (properPart (Set ι))).normalizedChainComplex R).iCycles (n + 1)
      = apartmentFundamentalChain e₀ R :=
  HomologicalComplex.liftCycles_i _ _ _ _ _

/-- **A normalized chain is the sum of its chamber coordinates.** -/
theorem expand_in_chambers {n : ℕ}
    [Fintype ((nerve (properPart (Set ι))).nonDegenerate n)] (R : C) {T : C}
    (z : T ⟶ ((nerve (properPart (Set ι))).normalizedChainComplex R).X n) :
    z = ∑ y : (nerve (properPart (Set ι))).nonDegenerate n, (z ≫ chamberCoefficient y R)
      ≫ (nerve (properPart (Set ι))).ιNormalizedChainComplex (R := R)
        (y : (nerve (properPart (Set ι))) _⦋n⦌) := by
  conv_lhs => rw [← Category.comp_id z, ← chamberCoefficient_total (ι := ι) (n := n) R]
  rw [Preadditive.comp_sum]
  exact Finset.sum_congr rfl fun y _ => by simp only [Category.assoc]

/-- The coefficient of a cycle at the chamber of an ordering. -/
noncomputable def cycleCoefficient {n : ℕ} [CategoryWithHomology C] (e₀ : Fin (n + 3) ≃ ι) (R : C)
    {T : C} (x : T ⟶ ((nerve (properPart (Set ι))).normalizedChainComplex R).cycles (n + 1))
    (σ : Equiv.Perm (Fin (n + 3))) : T ⟶ R :=
  x ≫ ((nerve (properPart (Set ι))).normalizedChainComplex R).iCycles (n + 1)
    ≫ chamberCoefficient (apartmentChamber (σ.trans e₀)) R

theorem isSplitMono_apartmentFundamentalCycle {n : ℕ} [CategoryWithHomology C]
    (e₀ : Fin (n + 3) ≃ ι) (R : C) : IsSplitMono (apartmentFundamentalCycle e₀ R) := by
  obtain ⟨⟨r, hr⟩⟩ := isSplitMono_apartmentFundamentalChain (n := n + 1) e₀ R
  refine ⟨⟨((nerve (properPart (Set ι))).normalizedChainComplex R).iCycles (n + 1) ≫ r, ?_⟩⟩
  rw [← Category.assoc, apartmentFundamentalCycle_i, hr]

end Coefficients

/-! ## Every top chain comes from an ordering -/

section Surjectivity

variable {ι : Type u}

/-- The predecessor of a chain vertex, with the empty set below the first one. -/
def prevSet {n : ℕ} (f : Fin (n + 1) → properPart (Set ι)) (i : Fin (n + 1)) : Set ι :=
  Fin.cases ∅ (fun j : Fin n => (f j.castSucc : Set ι)) i

@[simp] theorem prevSet_zero {n : ℕ} (f : Fin (n + 1) → properPart (Set ι)) :
    prevSet f 0 = ∅ := rfl

@[simp] theorem prevSet_succ {n : ℕ} (f : Fin (n + 1) → properPart (Set ι)) (j : Fin n) :
    prevSet f j.succ = (f j.castSucc : Set ι) := by
  rw [prevSet, Fin.cases_succ]

theorem prevSet_ssubset {n : ℕ} {f : Fin (n + 1) → properPart (Set ι)} (hf : StrictMono f)
    (i : Fin (n + 1)) : prevSet f i ⊂ (f i : Set ι) := by
  induction i using Fin.cases with
  | zero =>
      rw [prevSet_zero]
      exact Set.empty_ssubset.2 (Set.nonempty_iff_ne_empty.2 (ne_of_gt (f 0).2.1))
  | succ j =>
      rw [prevSet_succ]
      exact hf (Fin.castSucc_lt_succ)

theorem subset_prevSet {n : ℕ} {f : Fin (n + 1) → properPart (Set ι)} (hf : StrictMono f)
    {i j : Fin (n + 1)} (hij : j < i) : (f j : Set ι) ⊆ prevSet f i := by
  induction i using Fin.cases with
  | zero => exact absurd hij (not_lt_of_ge (Fin.zero_le j))
  | succ k =>
      rw [prevSet_succ]
      exact hf.monotone (Fin.le_castSucc_iff.2 hij)

/-- The vector a chain acquires at one step. -/
noncomputable def chainNewElt {n : ℕ} {f : Fin (n + 1) → properPart (Set ι)} (hf : StrictMono f)
    (i : Fin (n + 1)) : ι :=
  (Set.nonempty_of_ssubset (prevSet_ssubset hf i)).choose

theorem chainNewElt_mem {n : ℕ} {f : Fin (n + 1) → properPart (Set ι)} (hf : StrictMono f)
    (i : Fin (n + 1)) : chainNewElt hf i ∈ (f i : Set ι) :=
  ((Set.nonempty_of_ssubset (prevSet_ssubset hf i)).choose_spec).1

theorem chainNewElt_notMem {n : ℕ} {f : Fin (n + 1) → properPart (Set ι)} (hf : StrictMono f)
    (i : Fin (n + 1)) : chainNewElt hf i ∉ prevSet f i :=
  ((Set.nonempty_of_ssubset (prevSet_ssubset hf i)).choose_spec).2

theorem chainNewElt_injective {n : ℕ} {f : Fin (n + 1) → properPart (Set ι)} (hf : StrictMono f) :
    Function.Injective (chainNewElt hf) := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact chainNewElt_notMem hf j (hij ▸ subset_prevSet hf hlt (chainNewElt_mem hf i))
  · exact chainNewElt_notMem hf i (hij ▸ subset_prevSet hf hlt (chainNewElt_mem hf j))

/-- The last vector of the ordering: the one outside every vertex of the chain. -/
noncomputable def chainLastElt {n : ℕ} {f : Fin (n + 1) → properPart (Set ι)}
    (_hf : StrictMono f) : ι :=
  (Set.nonempty_of_ssubset (show (f (Fin.last n) : Set ι) ⊂ Set.univ from
    (f (Fin.last n)).2.2)).choose

theorem chainLastElt_notMem {n : ℕ} {f : Fin (n + 1) → properPart (Set ι)} (hf : StrictMono f) :
    chainLastElt hf ∉ (f (Fin.last n) : Set ι) :=
  ((Set.nonempty_of_ssubset (show (f (Fin.last n) : Set ι) ⊂ Set.univ from
    (f (Fin.last n)).2.2)).choose_spec).2

/-- **The ordering of the frame that a top chain determines.** -/
noncomputable def chainOrdering {n : ℕ} {f : Fin (n + 1) → properPart (Set ι)} (hf : StrictMono f)
    (i : Fin (n + 2)) : ι :=
  Fin.lastCases (chainLastElt hf) (fun j : Fin (n + 1) => chainNewElt hf j) i

@[simp] theorem chainOrdering_castSucc {n : ℕ} {f : Fin (n + 1) → properPart (Set ι)}
    (hf : StrictMono f) (j : Fin (n + 1)) : chainOrdering hf j.castSucc = chainNewElt hf j := by
  rw [chainOrdering, Fin.lastCases_castSucc]

@[simp] theorem chainOrdering_last {n : ℕ} {f : Fin (n + 1) → properPart (Set ι)}
    (hf : StrictMono f) : chainOrdering hf (Fin.last (n + 1)) = chainLastElt hf := by
  rw [chainOrdering, Fin.lastCases_last]

theorem chainOrdering_injective {n : ℕ} {f : Fin (n + 1) → properPart (Set ι)}
    (hf : StrictMono f) : Function.Injective (chainOrdering hf) := by
  intro i j hij
  induction i using Fin.lastCases with
  | last =>
      induction j using Fin.lastCases with
      | last => rfl
      | cast k =>
          rw [chainOrdering_last, chainOrdering_castSucc] at hij
          exact absurd (hij ▸ chainNewElt_mem hf k) (fun hmem =>
            chainLastElt_notMem hf (hf.monotone (Fin.le_last k) hmem))
  | cast k =>
      induction j using Fin.lastCases with
      | last =>
          rw [chainOrdering_last, chainOrdering_castSucc] at hij
          exact absurd (hij ▸ chainNewElt_mem hf k) (fun hmem =>
            chainLastElt_notMem hf (hf.monotone (Fin.le_last k) hmem))
      | cast k' =>
          rw [chainOrdering_castSucc, chainOrdering_castSucc] at hij
          rw [chainNewElt_injective hf hij]

/-- **Every top chain of a Boolean apartment is the chain of initial segments of an ordering.** -/
theorem exists_ordering_chainOfOrdering [Finite ι] {n : ℕ} (hN : Nat.card ι = n + 2)
    {f : Fin (n + 1) → properPart (Set ι)} (hf : StrictMono f) :
    ∃ e : Fin (n + 2) ≃ ι, chainOfOrdering e = f := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  have hcardι : Fintype.card ι = n + 2 := by
    rw [← Nat.card_eq_fintype_card, hN]
  have hbij : Function.Bijective (chainOrdering hf) := by
    refine (Fintype.bijective_iff_injective_and_card _).2 ⟨chainOrdering_injective hf, ?_⟩
    rw [Fintype.card_fin, hcardι]
  refine ⟨Equiv.ofBijective _ hbij, funext fun i => Subtype.ext ?_⟩
  show initialSegSet (Equiv.ofBijective _ hbij) i.castSucc = (f i : Set ι)
  have hsub : initialSegSet (Equiv.ofBijective _ hbij) i.castSucc ⊆ (f i : Set ι) := by
    rintro x ⟨j, hj, rfl⟩
    induction j using Fin.lastCases with
    | last => exact absurd hj (not_le_of_gt (Fin.castSucc_lt_last i))
    | cast k =>
        show chainOrdering hf k.castSucc ∈ (f i : Set ι)
        rw [chainOrdering_castSucc]
        exact hf.monotone (by simpa using hj) (chainNewElt_mem hf k)
  have hcard1 : (initialSegSet (Equiv.ofBijective _ hbij) i.castSucc).ncard = (i : ℕ) + 1 := by
    have := ncard_initialSegSet (Equiv.ofBijective _ hbij) i.castSucc
    simpa using this
  have hcard2 : ((f i : Set ι)).ncard = (i : ℕ) + 1 :=
    apartment_chain_ncard hN (by omega) hf i
  exact Set.eq_of_subset_of_ncard_le hsub (by omega) (Set.toFinite _)

/-- The ordering of the frame that a chamber determines. -/
noncomputable def chamberOrdering [Finite ι] {n : ℕ} (hN : Nat.card ι = n + 2)
    (y : (nerve (properPart (Set ι))).nonDegenerate n) : Fin (n + 2) ≃ ι :=
  (exists_ordering_chainOfOrdering hN
    ((PartialOrder.mem_nerve_nonDegenerate_iff_strictMono
      (y : (nerve (properPart (Set ι))) _⦋n⦌)).1 y.2)).choose

theorem chainOfOrdering_chamberOrdering [Finite ι] {n : ℕ} (hN : Nat.card ι = n + 2)
    (y : (nerve (properPart (Set ι))).nonDegenerate n) :
    chainOfOrdering (chamberOrdering hN y) = (y : (nerve (properPart (Set ι))) _⦋n⦌).obj :=
  (exists_ordering_chainOfOrdering hN
    ((PartialOrder.mem_nerve_nonDegenerate_iff_strictMono
      (y : (nerve (properPart (Set ι))) _⦋n⦌)).1 y.2)).choose_spec

/-- **The chambers of an apartment are exactly the orderings of the frame.** -/
noncomputable def apartmentChamberEquiv [Finite ι] {n : ℕ} (hN : Nat.card ι = n + 2) :
    (Fin (n + 2) ≃ ι) ≃ (nerve (properPart (Set ι))).nonDegenerate n where
  toFun e := apartmentChamber e
  invFun y := chamberOrdering hN y
  left_inv e :=
    chainOfOrdering_injective (chainOfOrdering_chamberOrdering hN (apartmentChamber e))
  right_inv y :=
    Subtype.ext (nerve_simplex_ext fun i =>
      congrFun (chainOfOrdering_chamberOrdering hN y) i)

end Surjectivity

section Homology

variable {C : Type u} [Category.{v} C] [Abelian C] [Limits.HasCoproducts.{u} C]

/-- **The apartment of a frame with `N` vectors has dimension below `N - 1`.** -/
theorem apartmentHasDimensionLT_of_card {ι : Type u} [Finite ι] {N : ℕ} (hN : Nat.card ι = N) :
    SSet.HasDimensionLT (nerveFunctor.obj (Cat.of (properPart (Set ι)))) (N - 1) := by
  refine hasDimensionLT_nerve_of_chain_bound _ fun n f hf => ?_
  have hmono : StrictMono fun j : Fin (n + 1) => ((f j : Set ι)).ncard := fun j j' hjj' =>
    Set.ncard_lt_ncard (hf hjj') (Set.toFinite _)
  have hzero : 1 ≤ ((f 0 : Set ι)).ncard :=
    Set.ncard_pos (Set.toFinite _) |>.2 (Set.nonempty_iff_ne_empty.2 (ne_of_gt (f 0).2.1))
  have hlast : ((f (Fin.last n) : Set ι)).ncard ≤ N - 1 := by
    have h : ((f (Fin.last n) : Set ι)).ncard < (Set.univ : Set ι).ncard :=
      Set.ncard_lt_ncard (f (Fin.last n)).2.2 (Set.toFinite _)
    rw [Set.ncard_univ, hN] at h
    omega
  have h1 := strictMono_zero_add_le hmono (Fin.last n)
  simp only [Fin.val_last] at h1
  omega

/-- **The fundamental class of the Coxeter sphere of a frame**, an explicit split monomorphism into
the top homology of the apartment. -/
noncomputable def apartmentFundamentalClass {n : ℕ} {ι : Type u} [Finite ι]
    (hN : Nat.card ι = n + 3) (e₀ : Fin (n + 3) ≃ ι) (R : C) :
    R ⟶ (nerveFunctor.obj (Cat.of (properPart (Set ι)))).homology R (n + 1) := by
  haveI : SSet.HasDimensionLT (nerve (properPart (Set ι))) (n + 1 + 1) := by
    rw [show n + 1 + 1 = (n + 3) - 1 by omega]
    exact apartmentHasDimensionLT_of_card hN
  exact apartmentFundamentalCycle e₀ R ≫ (topHomologyIsoCycles (X := nerve (properPart (Set ι)))
    (R := R) (n := n + 1)).inv

theorem isSplitMono_apartmentFundamentalClass {n : ℕ} {ι : Type u} [Finite ι]
    (hN : Nat.card ι = n + 3) (e₀ : Fin (n + 3) ≃ ι) (R : C) :
    IsSplitMono (apartmentFundamentalClass hN e₀ R) := by
  haveI : SSet.HasDimensionLT (nerve (properPart (Set ι))) (n + 1 + 1) := by
    rw [show n + 1 + 1 = (n + 3) - 1 by omega]
    exact apartmentHasDimensionLT_of_card hN
  haveI := isSplitMono_apartmentFundamentalCycle (n := n) e₀ R
  rw [apartmentFundamentalClass]
  infer_instance

end Homology

end Chains

end GaloisForLFunctions.HTGeometry
