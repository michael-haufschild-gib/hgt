import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# The sign of a block shuffle

For `S ⊆ Fin N` with `|S| = m`, the *block shuffle* `ρ_S` sends `0, …, m−1` increasingly onto `S`
and `m, …, N−1` increasingly onto the complement of `S` (`blockShuffle`).

**Theorem** (`sign_blockShuffle`).  `sign ρ_S = (−1)^{ΣS + Σ_{k<m} k}`.

Corollary (`sign_blockEnum_symm_trans`): the permutation matching the increasing enumerations of
`S` and `T`, and of their complements, has sign `(−1)^{ΣS + ΣT}`.

Proof by induction on `ΣS`.  For `S = {0, …, m−1}` the shuffle is the identity.  Otherwise `S`
contains some `x ≥ 1` with `x − 1 ∉ S`.  Moving `x` to `x − 1` composes `ρ_S` with the
transposition `(x−1 x)`, because that transposition maps `S` and its complement monotonically.
It also lowers `ΣS` by one.
-/

open Finset Equiv

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {N : ℕ}

theorem card_compl_fin {S : Finset (Fin N)} {m : ℕ} (hS : S.card = m) : Sᶜ.card = N - m := by
  rw [Finset.card_compl, Fintype.card_fin, hS]

theorem le_of_card_eq_fin {S : Finset (Fin N)} {m : ℕ} (hS : S.card = m) : m ≤ N := by
  rw [← hS]
  exact (Finset.card_le_univ S).trans (by simp)

/-- The sum `ΣS` of the elements of `S`. -/
def idxSum (S : Finset (Fin N)) : ℕ := ∑ y ∈ S, (y : ℕ)

/-- `S` enumerated increasingly on the left block, its complement on the right block. -/
def blockEnum (S : Finset (Fin N)) {m : ℕ} (hS : S.card = m) : Fin m ⊕ Fin (N - m) ≃ Fin N :=
  Equiv.ofBijective (Sum.elim (S.orderEmbOfFin hS) (Sᶜ.orderEmbOfFin (card_compl_fin hS))) (by
    constructor
    · rintro (a | a) (b | b) h
      · simp only [Sum.elim_inl] at h
        rw [(S.orderEmbOfFin hS).injective h]
      · exfalso
        simp only [Sum.elim_inl, Sum.elim_inr] at h
        have h1 := S.orderEmbOfFin_mem hS a
        have h2 := Sᶜ.orderEmbOfFin_mem (card_compl_fin hS) b
        rw [h] at h1
        exact (Finset.mem_compl.mp h2) h1
      · exfalso
        simp only [Sum.elim_inl, Sum.elim_inr] at h
        have h1 := Sᶜ.orderEmbOfFin_mem (card_compl_fin hS) a
        have h2 := S.orderEmbOfFin_mem hS b
        rw [h] at h1
        exact (Finset.mem_compl.mp h1) h2
      · simp only [Sum.elim_inr] at h
        rw [(Sᶜ.orderEmbOfFin _).injective h]
    · intro p
      by_cases hp : p ∈ S
      · have : p ∈ Set.range (S.orderEmbOfFin hS) := by
          rw [Finset.range_orderEmbOfFin]
          exact hp
        obtain ⟨a, ha⟩ := this
        exact ⟨Sum.inl a, ha⟩
      · have : p ∈ Set.range (Sᶜ.orderEmbOfFin (card_compl_fin hS)) := by
          rw [Finset.range_orderEmbOfFin]
          simpa using hp
        obtain ⟨a, ha⟩ := this
        exact ⟨Sum.inr a, ha⟩)

@[simp] theorem blockEnum_inl (S : Finset (Fin N)) {m : ℕ} (hS : S.card = m) (a : Fin m) :
    blockEnum S hS (Sum.inl a) = S.orderEmbOfFin hS a := rfl

@[simp] theorem blockEnum_inr (S : Finset (Fin N)) {m : ℕ} (hS : S.card = m) (a : Fin (N - m)) :
    blockEnum S hS (Sum.inr a) = Sᶜ.orderEmbOfFin (card_compl_fin hS) a := rfl

/-- The standard block decomposition `Fin m ⊕ Fin (N − m) ≃ Fin N`. -/
def stdBlock {m : ℕ} (hm : m ≤ N) : Fin m ⊕ Fin (N - m) ≃ Fin N :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' hm))

/-- The block shuffle `ρ_S`. -/
def blockShuffle (S : Finset (Fin N)) {m : ℕ} (hS : S.card = m) : Perm (Fin N) :=
  (stdBlock (le_of_card_eq_fin hS)).symm.trans (blockEnum S hS)

theorem blockShuffle_stdBlock (S : Finset (Fin N)) {m : ℕ} (hS : S.card = m)
    (z : Fin m ⊕ Fin (N - m)) :
    blockShuffle S hS (stdBlock (le_of_card_eq_fin hS) z) = blockEnum S hS z := by
  simp [blockShuffle]

/-- The initial segment `{0, …, m−1}`. -/
def initSeg (N m : ℕ) : Finset (Fin N) := Finset.univ.filter fun x => (x : ℕ) < m

theorem card_initSeg {m : ℕ} (hm : m ≤ N) : (initSeg N m).card = m := by
  have : initSeg N m = (Finset.univ : Finset (Fin m)).map (Fin.castLEEmb hm) := by
    ext x
    simp only [initSeg, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Fin.castLEEmb_apply]
    constructor
    · intro hx
      exact ⟨⟨x, hx⟩, Fin.ext rfl⟩
    · rintro ⟨y, rfl⟩
      exact y.isLt
  rw [this, Finset.card_map, Finset.card_univ, Fintype.card_fin]

theorem blockEnum_initSeg {m : ℕ} (hm : m ≤ N) :
    blockEnum (initSeg N m) (card_initSeg hm) = stdBlock hm := by
  ext z
  rcases z with a | a
  · have h := Finset.orderEmbOfFin_unique (card_initSeg hm) (f := fun a : Fin m => Fin.castLE hm a)
      (fun a => by simp [initSeg]) (fun a b hab => by simpa using hab)
    rw [blockEnum_inl, ← congrFun h a]
    simp [stdBlock]
  · have h := Finset.orderEmbOfFin_unique (card_compl_fin (card_initSeg hm))
      (f := fun a : Fin (N - m) => (⟨m + a, by omega⟩ : Fin N))
      (fun a => by simp [initSeg]) (fun a b hab => by
        simp only [Fin.mk_lt_mk]
        exact Nat.add_lt_add_left hab m)
    rw [blockEnum_inr, ← congrFun h a]
    simp [stdBlock]

theorem blockShuffle_initSeg {m : ℕ} (hm : m ≤ N) :
    blockShuffle (initSeg N m) (card_initSeg hm) = 1 := by
  ext q
  simp only [blockShuffle, blockEnum_initSeg hm, Equiv.symm_trans_self, Perm.coe_one, id_eq]
  rfl

/-- A set other than the initial segment has an element `x ≥ 1` with `x − 1` outside it. -/
theorem exists_mem_pred_not_mem {S : Finset (Fin N)} {m : ℕ} (hS : S.card = m)
    (hne : S ≠ initSeg N m) :
    ∃ x ∈ S, ∃ h : 1 ≤ (x : ℕ), (⟨(x : ℕ) - 1, by omega⟩ : Fin N) ∉ S := by
  have hm := le_of_card_eq_fin hS
  obtain ⟨z, hzm, hzS⟩ : ∃ z : Fin N, (z : ℕ) < m ∧ z ∉ S := by
    by_contra hcon
    push Not at hcon
    apply hne
    refine (Finset.eq_of_subset_of_card_le (fun y hy => ?_) ?_).symm
    · simp only [initSeg, Finset.mem_filter, Finset.mem_univ, true_and] at hy
      exact hcon y hy
    · rw [hS, card_initSeg hm]
  set T := S.filter fun y => z < y with hT
  have hTne : T.Nonempty := by
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty] at hcon
    have hsub : S ⊆ initSeg N z := by
      intro y hy
      simp only [initSeg, Finset.mem_filter, Finset.mem_univ, true_and]
      have hyT : y ∉ T := by rw [hcon]; exact Finset.notMem_empty y
      simp only [hT, Finset.mem_filter, hy, true_and, not_lt] at hyT
      have hyz : y ≠ z := fun h => hzS (h ▸ hy)
      exact lt_of_le_of_ne (Fin.le_iff_val_le_val.mp hyT) (fun h => hyz (Fin.ext h))
    have := Finset.card_le_card hsub
    rw [hS, card_initSeg (by omega : (z : ℕ) ≤ N)] at this
    omega
  set x := T.min' hTne
  have hxT : x ∈ T := T.min'_mem hTne
  simp only [hT, Finset.mem_filter] at hxT
  obtain ⟨hxS, hzx⟩ := hxT
  have hx1 : 1 ≤ (x : ℕ) := by
    have : (z : ℕ) < x := hzx
    omega
  refine ⟨x, hxS, hx1, fun hx' => ?_⟩
  by_cases heq : (x : ℕ) - 1 = z
  · exact hzS (by convert hx' using 1; exact Fin.ext heq.symm)
  · have hzx' : z < (⟨(x : ℕ) - 1, by omega⟩ : Fin N) := by
      rw [Fin.lt_def]
      have : (z : ℕ) < x := hzx
      simp only
      omega
    have hmem : (⟨(x : ℕ) - 1, by omega⟩ : Fin N) ∈ T := by
      simp only [hT, Finset.mem_filter]
      exact ⟨hx', hzx'⟩
    have := T.min'_le _ hmem
    rw [Fin.le_iff_val_le_val] at this
    simp only at this
    omega

/-- Moving `x` down to `x − 1` composes the block shuffle with the transposition `(x−1 x)`. -/
theorem blockShuffle_move {S : Finset (Fin N)} {m : ℕ} (hS : S.card = m) {x : Fin N} (hxS : x ∈ S)
    (hx1 : 1 ≤ (x : ℕ)) (hx' : (⟨(x : ℕ) - 1, by omega⟩ : Fin N) ∉ S)
    (hS' : (insert (⟨(x : ℕ) - 1, by omega⟩ : Fin N) (S.erase x)).card = m) :
    blockShuffle (insert (⟨(x : ℕ) - 1, by omega⟩ : Fin N) (S.erase x)) hS' =
      swap (⟨(x : ℕ) - 1, by omega⟩ : Fin N) x * blockShuffle S hS := by
  set x' : Fin N := ⟨(x : ℕ) - 1, by omega⟩ with hx'def
  set S' := insert x' (S.erase x) with hS'def
  have hxx' : x' ≠ x := by
    intro h
    have := congrArg Fin.val h
    simp only [hx'def] at this
    omega
  have hx'lt : x' < x := by
    rw [Fin.lt_def]
    simp only [hx'def]
    omega
  have hm := le_of_card_eq_fin hS
  ext q
  obtain ⟨z, rfl⟩ := (stdBlock hm).surjective q
  rw [Perm.coe_mul, Function.comp_apply, blockShuffle_stdBlock S hS z]
  rw [show stdBlock hm z = stdBlock (le_of_card_eq_fin hS') z from rfl, blockShuffle_stdBlock]
  rcases z with a | a
  · rw [blockEnum_inl, blockEnum_inl]
    have h := Finset.orderEmbOfFin_unique hS'
      (f := fun a => swap x' x (S.orderEmbOfFin hS a)) (fun a => ?_) (fun a b hab => ?_)
    · rw [← congrFun h a]
    · set y := S.orderEmbOfFin hS a
      have hy : y ∈ S := S.orderEmbOfFin_mem hS a
      by_cases hyx : y = x
      · rw [hyx, swap_apply_right]
        exact Finset.mem_insert_self _ _
      · have hyx' : y ≠ x' := fun h => hx' (h ▸ hy)
        rw [swap_apply_of_ne_of_ne hyx' hyx]
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hyx, hy⟩)
    · show swap x' x (S.orderEmbOfFin hS a) < swap x' x (S.orderEmbOfFin hS b)
      have hlt := (S.orderEmbOfFin hS).strictMono hab
      set u := S.orderEmbOfFin hS a
      set v := S.orderEmbOfFin hS b
      have hu : u ∈ S := S.orderEmbOfFin_mem hS a
      have hv : v ∈ S := S.orderEmbOfFin_mem hS b
      have hux' : u ≠ x' := fun h => hx' (h ▸ hu)
      have hvx' : v ≠ x' := fun h => hx' (h ▸ hv)
      by_cases hvx : v = x
      · have hux : u ≠ x := fun h => (lt_irrefl _) (h ▸ hvx ▸ hlt)
        rw [hvx, swap_apply_right, swap_apply_of_ne_of_ne hux' hux]
        rw [hvx] at hlt
        rw [Fin.lt_def] at hlt ⊢
        have : (u : ℕ) ≠ (x : ℕ) - 1 := fun h => hux' (Fin.ext h)
        simp only [hx'def]
        omega
      · rw [swap_apply_of_ne_of_ne hvx' hvx]
        by_cases hux : u = x
        · rw [hux, swap_apply_right]
          exact hx'lt.trans (hux ▸ hlt)
        · rw [swap_apply_of_ne_of_ne hux' hux]
          exact hlt
  · rw [blockEnum_inr, blockEnum_inr]
    have h := Finset.orderEmbOfFin_unique (card_compl_fin hS')
      (f := fun a => swap x' x (Sᶜ.orderEmbOfFin (card_compl_fin hS) a)) (fun a => ?_)
      (fun a b hab => ?_)
    · rw [← congrFun h a]
    · set y := Sᶜ.orderEmbOfFin (card_compl_fin hS) a
      have hy : y ∉ S := Finset.mem_compl.mp (Sᶜ.orderEmbOfFin_mem _ a)
      have hyx : y ≠ x := fun h => hy (h ▸ hxS)
      rw [Finset.mem_compl]
      by_cases hyx' : y = x'
      · rw [hyx', swap_apply_left]
        intro hmem
        rcases Finset.mem_insert.mp hmem with h | h
        · exact hxx' h.symm
        · exact (Finset.mem_erase.mp h).1 rfl
      · rw [swap_apply_of_ne_of_ne hyx' hyx]
        intro hmem
        rcases Finset.mem_insert.mp hmem with h | h
        · exact hyx' h
        · exact hy (Finset.mem_erase.mp h).2
    · show swap x' x (Sᶜ.orderEmbOfFin (card_compl_fin hS) a) <
        swap x' x (Sᶜ.orderEmbOfFin (card_compl_fin hS) b)
      have hlt := (Sᶜ.orderEmbOfFin (card_compl_fin hS)).strictMono hab
      set u := Sᶜ.orderEmbOfFin (card_compl_fin hS) a
      set v := Sᶜ.orderEmbOfFin (card_compl_fin hS) b
      have hu : u ∉ S := Finset.mem_compl.mp (Sᶜ.orderEmbOfFin_mem _ a)
      have hv : v ∉ S := Finset.mem_compl.mp (Sᶜ.orderEmbOfFin_mem _ b)
      have hux : u ≠ x := fun h => hu (h ▸ hxS)
      have hvx : v ≠ x := fun h => hv (h ▸ hxS)
      by_cases hux' : u = x'
      · have hvx'' : v ≠ x' := fun h => (lt_irrefl _) (h ▸ hux' ▸ hlt)
        rw [hux', swap_apply_left, swap_apply_of_ne_of_ne hvx'' hvx]
        rw [hux'] at hlt
        rw [Fin.lt_def] at hlt ⊢
        have : (v : ℕ) ≠ x := fun h => hvx (Fin.ext h)
        simp only [hx'def] at hlt
        omega
      · rw [swap_apply_of_ne_of_ne hux' hux]
        by_cases hvx' : v = x'
        · rw [hvx', swap_apply_left]
          exact (hvx' ▸ hlt).trans hx'lt
        · rw [swap_apply_of_ne_of_ne hvx' hvx]
          exact hlt

theorem card_move {S : Finset (Fin N)} {m : ℕ} (hS : S.card = m) {x : Fin N} (hxS : x ∈ S)
    (hx1 : 1 ≤ (x : ℕ)) (hx' : (⟨(x : ℕ) - 1, by omega⟩ : Fin N) ∉ S) :
    (insert (⟨(x : ℕ) - 1, by omega⟩ : Fin N) (S.erase x)).card = m := by
  rw [Finset.card_insert_of_notMem (fun h => hx' (Finset.mem_of_mem_erase h)),
    Finset.card_erase_of_mem hxS, hS]
  have : 1 ≤ m := by
    rw [← hS]
    exact Finset.card_pos.mpr ⟨x, hxS⟩
  omega

theorem sum_move {S : Finset (Fin N)} {x : Fin N} (hxS : x ∈ S) (hx1 : 1 ≤ (x : ℕ))
    (hx' : (⟨(x : ℕ) - 1, by omega⟩ : Fin N) ∉ S) :
    idxSum (insert (⟨(x : ℕ) - 1, by omega⟩ : Fin N) (S.erase x)) + 1 = idxSum S := by
  unfold idxSum
  rw [Finset.sum_insert (fun h => hx' (Finset.mem_of_mem_erase h)), ← Finset.add_sum_erase S _ hxS]
  simp only
  omega

/-- **The sign of a block shuffle.** -/
theorem sign_blockShuffle : ∀ (n : ℕ) (S : Finset (Fin N)) {m : ℕ} (hS : S.card = m),
    idxSum S = n →
      (Perm.sign (blockShuffle S hS) : ℤ) = (-1) ^ (idxSum S + ∑ k ∈ Finset.range m, k) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S m hS hn
    have hm := le_of_card_eq_fin hS
    by_cases h0 : S = initSeg N m
    · subst h0
      rw [blockShuffle_initSeg hm, Perm.sign_one]
      have hsum : idxSum (initSeg N m) = ∑ k ∈ Finset.range m, k := by
        unfold idxSum
        rw [show initSeg N m = (Finset.range m).attach.map
            ⟨fun k => (⟨k.1, (Finset.mem_range.mp k.2).trans_le hm⟩ : Fin N), fun a b h => by
              simp only [Fin.mk.injEq] at h
              exact Subtype.ext h⟩ by
          ext y
          simp only [initSeg, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
            Finset.mem_attach, Function.Embedding.coeFn_mk]
          constructor
          · intro hy
            exact ⟨⟨y, Finset.mem_range.mpr hy⟩, Fin.ext rfl⟩
          · rintro ⟨k, rfl⟩
            exact Finset.mem_range.mp k.2]
        rw [Finset.sum_map]
        simp only [Function.Embedding.coeFn_mk]
        exact Finset.sum_attach (Finset.range m) (fun k => k)
      rw [hsum, ← two_mul, pow_mul]
      simp
    · obtain ⟨x, hxS, hx1, hx'⟩ := exists_mem_pred_not_mem hS h0
      set S' := insert (⟨(x : ℕ) - 1, by omega⟩ : Fin N) (S.erase x) with hS'def
      have hS' : S'.card = m := card_move hS hxS hx1 hx'
      have hsum : idxSum S' + 1 = idxSum S := sum_move hxS hx1 hx'
      have hlt : idxSum S' < n := by omega
      have hrec := ih _ hlt S' hS' rfl
      have hne : (⟨(x : ℕ) - 1, by omega⟩ : Fin N) ≠ x := by
        intro h
        have := congrArg Fin.val h
        simp only at this
        omega
      rw [blockShuffle_move hS hxS hx1 hx' hS', Perm.sign_mul, Perm.sign_swap hne] at hrec
      push_cast at hrec
      set c := ∑ k ∈ Finset.range m, k with hc
      have e : idxSum S + c = (idxSum S' + c) + 1 := by omega
      have key : (-1 : ℤ) ^ (idxSum S + c) = -(-1) ^ (idxSum S' + c) := by
        rw [e, pow_succ]
        ring
      rw [key]
      linear_combination -hrec

/-- **The sign of the matching of two enumerations.**  The permutation sending the increasing
enumerations of `S` and of its complement to those of `T` and of its complement has sign
`(−1)^{ΣS + ΣT}`. -/
theorem sign_blockEnum_symm_trans (S T : Finset (Fin N)) {m : ℕ} (hS : S.card = m)
    (hT : T.card = m) :
    (Perm.sign ((blockEnum S hS).symm.trans (blockEnum T hT)) : ℤ) =
      (-1) ^ (idxSum S + idxSum T) := by
  have hfac : (blockEnum S hS).symm.trans (blockEnum T hT) =
      blockShuffle T hT * (blockShuffle S hS)⁻¹ := by
    ext q
    simp [blockShuffle]
  rw [hfac, Perm.sign_mul, Perm.sign_inv]
  push_cast
  rw [sign_blockShuffle _ T hT rfl, sign_blockShuffle _ S hS rfl, ← pow_add]
  set c := ∑ k ∈ Finset.range m, k with hc
  have e : idxSum T + c + (idxSum S + c) = (idxSum S + idxSum T) + 2 * c := by ring
  rw [e, pow_add, pow_mul]
  simp

end

end GaloisForLFunctions.HTGeometry
