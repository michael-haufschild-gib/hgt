import Mathlib

/-!
# The symmetric first-failure identity

For survival probabilities `s_1, …, s_k` and a schedule `σ ∈ S_k`, the first failure occurs at
position `r` (`0`-indexed here) with weight `F_{σ,r} = (∏_{j<r} s_{σ(j)}) (1 - s_{σ(r)})`.
Averaging over all schedules,

* the prefix products average to `e_m / C(k,m)`: `∑_σ ∏_{j<m} s_{σ(j)} = m! (k-m)! e_m(s)`, because
  exactly `m! (k-m)!` permutations carry the first `m` positions onto a given `m`-set;
* **Theorem 3.1, `(PFF.5)`**: `W_r = ((k-r+1) e_{r-1} - r e_r) / (k C(k-1, r-1))` in the
  `1`-indexed position `r`;
* **`(PFF.6)`**: `∑_r W_r = 1 - e_k`;
* **`(PFF.7)`**: `e_r = ((k-r+1) e_{r-1} - k C(k-1,r-1) W_r) / r`, so the averaged ledger recovers
  every elementary symmetric coefficient.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.HTGeometry.FirstFailure

variable {k : ℕ}

/-- The elementary symmetric polynomial `e_r(s) = ∑_{|A| = r} ∏_{i ∈ A} s_i`. -/
def esymm {R : Type*} [CommRing R] (s : Fin k → R) (r : ℕ) : R :=
  ∑ A ∈ (univ : Finset (Fin k)).powersetCard r, ∏ i ∈ A, s i

/-- The first `m` positions `{0, …, m - 1}`. -/
def prefixSet (k m : ℕ) : Finset (Fin k) := univ.filter fun j => (j : ℕ) < m

theorem card_prefixSet {m : ℕ} (hm : m ≤ k) : (prefixSet k m).card = m := by
  rw [prefixSet, Fin.card_filter_val_lt, min_eq_right hm]

theorem esymm_zero {R : Type*} [CommRing R] (s : Fin k → R) : esymm s 0 = 1 := by
  simp [esymm]

theorem esymm_card {R : Type*} [CommRing R] (s : Fin k → R) :
    esymm s k = ∏ i, s i := by
  have h := powersetCard_self (univ : Finset (Fin k))
  rw [card_univ, Fintype.card_fin] at h
  rw [esymm, h, sum_singleton]

/-- A permutation carries the first `m` positions onto `A` iff it maps membership in the prefix to
membership in `A`. -/
theorem map_prefixSet_eq_iff {m : ℕ} (σ : Equiv.Perm (Fin k)) (A : Finset (Fin k)) :
    (prefixSet k m).map σ.toEmbedding = A ↔ ∀ x, x ∈ prefixSet k m ↔ σ x ∈ A := by
  constructor
  · intro h x
    constructor
    · intro hx; rw [← h]; exact mem_map_of_mem _ hx
    · intro hx
      rw [← h] at hx
      obtain ⟨y, hy, hyx⟩ := mem_map.1 hx
      have := σ.injective hyx
      rwa [← this]
  · intro h
    ext y
    rw [mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact (h x).1 hx
    · intro hy
      exact ⟨σ.symm y, (h _).2 (by simpa using hy), by simp⟩

theorem subtypeCongr_apply_pos {α : Type*} {p q : α → Prop} [DecidablePred p] [DecidablePred q]
    (e : {x // p x} ≃ {x // q x}) (f : {x // ¬p x} ≃ {x // ¬q x}) {a : α} (h : p a) :
    Equiv.subtypeCongr e f a = e ⟨a, h⟩ := by
  simp [Equiv.subtypeCongr, Equiv.sumCompl_symm_apply_of_pos h]

theorem subtypeCongr_apply_neg {α : Type*} {p q : α → Prop} [DecidablePred p] [DecidablePred q]
    (e : {x // p x} ≃ {x // q x}) (f : {x // ¬p x} ≃ {x // ¬q x}) {a : α} (h : ¬p a) :
    Equiv.subtypeCongr e f a = f ⟨a, h⟩ := by
  simp [Equiv.subtypeCongr, Equiv.sumCompl_symm_apply_of_neg h]

/-- Exactly `m! (k - m)!` permutations carry the first `m` positions onto a given `m`-set. -/
theorem card_perm_map_prefixSet {m : ℕ} (hm : m ≤ k) {A : Finset (Fin k)} (hA : A.card = m) :
    (univ.filter fun σ : Equiv.Perm (Fin k) => (prefixSet k m).map σ.toEmbedding = A).card =
      m.factorial * (k - m).factorial := by
  classical
  set P := prefixSet k m
  let e : {σ : Equiv.Perm (Fin k) // ∀ x, x ∈ P ↔ σ x ∈ A} ≃
      ({x // x ∈ P} ≃ {x // x ∈ A}) × ({x // x ∉ P} ≃ {x // x ∉ A}) :=
    { toFun := fun σ => (σ.1.subtypeEquiv σ.2, σ.1.subtypeEquiv fun x => not_congr (σ.2 x))
      invFun := fun p => ⟨Equiv.subtypeCongr p.1 p.2, fun x => by
        by_cases hx : x ∈ P
        · rw [subtypeCongr_apply_pos _ _ hx]
          exact ⟨fun _ => (p.1 ⟨x, hx⟩).2, fun _ => hx⟩
        · rw [subtypeCongr_apply_neg _ _ hx]
          exact ⟨fun h => absurd h hx, fun h => absurd h (p.2 ⟨x, hx⟩).2⟩⟩
      left_inv := fun σ => by
        apply Subtype.ext
        ext x
        by_cases hx : x ∈ P
        · rw [subtypeCongr_apply_pos _ _ hx]; rfl
        · rw [subtypeCongr_apply_neg _ _ hx]; rfl
      right_inv := fun p => by
        refine Prod.ext (Equiv.ext fun x => Subtype.ext ?_) (Equiv.ext fun x => Subtype.ext ?_)
        · change Equiv.subtypeCongr p.1 p.2 x = (p.1 x : Fin k)
          rw [subtypeCongr_apply_pos _ _ x.2]
        · change Equiv.subtypeCongr p.1 p.2 x = (p.2 x : Fin k)
          rw [subtypeCongr_apply_neg _ _ x.2] }
  have hcardP : Fintype.card {x // x ∈ P} = m := by rw [Fintype.card_coe, card_prefixSet hm]
  have hcardA : Fintype.card {x // x ∈ A} = m := by rw [Fintype.card_coe, hA]
  have hcardPc : Fintype.card {x // x ∉ P} = k - m := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe, card_prefixSet hm, Fintype.card_fin]
  have hcardAc : Fintype.card {x // x ∉ A} = k - m := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe, hA, Fintype.card_fin]
  have h1 : Fintype.card ({x // x ∈ P} ≃ {x // x ∈ A}) = m.factorial := by
    rw [Fintype.card_equiv (Fintype.equivOfCardEq (hcardP.trans hcardA.symm)), hcardP]
  have h2 : Fintype.card ({x // x ∉ P} ≃ {x // x ∉ A}) = (k - m).factorial := by
    rw [Fintype.card_equiv (Fintype.equivOfCardEq (hcardPc.trans hcardAc.symm)), hcardPc]
  have hfilter : (univ.filter fun σ : Equiv.Perm (Fin k) => P.map σ.toEmbedding = A) =
      univ.filter fun σ : Equiv.Perm (Fin k) => ∀ x, x ∈ P ↔ σ x ∈ A := by
    ext σ; simp only [mem_filter, mem_univ, true_and]; exact map_prefixSet_eq_iff σ A
  rw [hfilter, ← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_prod, h1, h2]

/-- **Prefix averages**: `∑_σ ∏_{j<m} s_{σ(j)} = m! (k - m)! e_m(s)`. -/
theorem sum_prod_prefixSet {R : Type*} [CommRing R] (s : Fin k → R) {m : ℕ} (hm : m ≤ k) :
    ∑ σ : Equiv.Perm (Fin k), ∏ j ∈ prefixSet k m, s (σ j) =
      ((m.factorial * (k - m).factorial : ℕ) : R) * esymm s m := by
  classical
  have hmaps : ∀ σ ∈ (univ : Finset (Equiv.Perm (Fin k))),
      (prefixSet k m).map σ.toEmbedding ∈ (univ : Finset (Fin k)).powersetCard m := by
    intro σ _
    rw [mem_powersetCard, card_map, card_prefixSet hm]
    exact ⟨subset_univ _, rfl⟩
  rw [← sum_fiberwise_of_maps_to hmaps, esymm, mul_sum]
  refine sum_congr rfl fun A hA => ?_
  have hconst : ∀ σ ∈ univ.filter fun σ : Equiv.Perm (Fin k) =>
      (prefixSet k m).map σ.toEmbedding = A, ∏ j ∈ prefixSet k m, s (σ j) = ∏ i ∈ A, s i := by
    intro σ hσ
    rw [← (mem_filter.1 hσ).2, prod_map]
    rfl
  rw [sum_congr rfl hconst, sum_const, card_perm_map_prefixSet hm (mem_powersetCard.1 hA).2,
    nsmul_eq_mul]

/-! ### First failure -/

/-- The weight `F_{σ,r} = (∏_{j<r} s_{σ(j)}) (1 - s_{σ(r)})` of a first failure at position `r`
(`0`-indexed) of the schedule `σ`. -/
def firstFailure {R : Type*} [CommRing R] (s : Fin k → R) (σ : Equiv.Perm (Fin k)) (r : Fin k) :
    R :=
  (∏ j ∈ prefixSet k r, s (σ j)) * (1 - s (σ r))

theorem prefixSet_succ (r : Fin k) : prefixSet k (r + 1) = insert r (prefixSet k r) := by
  ext j
  simp only [prefixSet, mem_filter, mem_univ, true_and, mem_insert]
  constructor
  · intro h
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | h
    · exact Or.inr h
    · exact Or.inl (Fin.ext h)
  · rintro (rfl | h)
    · exact Nat.lt_succ_self _
    · exact Nat.lt_succ_of_lt h

theorem firstFailure_eq {R : Type*} [CommRing R] (s : Fin k → R) (σ : Equiv.Perm (Fin k))
    (r : Fin k) :
    firstFailure s σ r = ∏ j ∈ prefixSet k r, s (σ j) - ∏ j ∈ prefixSet k (r + 1), s (σ j) := by
  rw [firstFailure, prefixSet_succ, prod_insert (by simp [prefixSet])]
  ring

/-- The ring form of `(PFF.5)`:
`∑_σ F_{σ,r} = r! (k-r)! e_r - (r+1)! (k-r-1)! e_{r+1}`. -/
theorem sum_firstFailure {R : Type*} [CommRing R] (s : Fin k → R) (r : Fin k) :
    ∑ σ, firstFailure s σ r =
      (((r : ℕ).factorial * (k - r).factorial : ℕ) : R) * esymm s r -
        ((((r : ℕ) + 1).factorial * (k - ((r : ℕ) + 1)).factorial : ℕ) : R) *
          esymm s ((r : ℕ) + 1) := by
  simp_rw [firstFailure_eq]
  rw [sum_sub_distrib, sum_prod_prefixSet s r.2.le, sum_prod_prefixSet s r.2]

/-- The schedule-averaged first-failure coordinate `W_r = (1/k!) ∑_σ F_{σ,r}`. -/
def averagedFirstFailure {R : Type*} [Field R] (s : Fin k → R) (r : Fin k) : R :=
  ((k.factorial : ℕ) : R)⁻¹ * ∑ σ, firstFailure s σ r

theorem averagedFirstFailure_eq_div_choose {R : Type*} [Field R] [CharZero R] (s : Fin k → R)
    (r : Fin k) :
    averagedFirstFailure s r =
      esymm s r / (k.choose r : R) - esymm s ((r : ℕ) + 1) / (k.choose ((r : ℕ) + 1) : R) := by
  have hK : ((k.factorial : ℕ) : R) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  have hca : ((k.choose r : ℕ) : R) ≠ 0 := by exact_mod_cast (Nat.choose_pos r.2.le).ne'
  have hcb : ((k.choose ((r : ℕ) + 1) : ℕ) : R) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (Nat.succ_le_of_lt r.2)).ne'
  have h1 : ((k.choose r : ℕ) : R) * (((r : ℕ).factorial * (k - r).factorial : ℕ) : R) =
      (k.factorial : R) := by
    have := Nat.choose_mul_factorial_mul_factorial r.2.le
    rw [mul_assoc] at this
    exact_mod_cast this
  have h2 : ((k.choose ((r : ℕ) + 1) : ℕ) : R) *
      ((((r : ℕ) + 1).factorial * (k - ((r : ℕ) + 1)).factorial : ℕ) : R) = (k.factorial : R) := by
    have := Nat.choose_mul_factorial_mul_factorial (Nat.succ_le_of_lt r.2)
    rw [mul_assoc] at this
    exact_mod_cast this
  have ha : (((r : ℕ).factorial * (k - r).factorial : ℕ) : R) / (k.factorial : R) =
      1 / (k.choose r : R) := by
    rw [div_eq_div_iff hK hca, one_mul, ← h1, mul_comm]
  have hb : ((((r : ℕ) + 1).factorial * (k - ((r : ℕ) + 1)).factorial : ℕ) : R) /
      (k.factorial : R) = 1 / (k.choose ((r : ℕ) + 1) : R) := by
    rw [div_eq_div_iff hK hcb, one_mul, ← h2, mul_comm]
  rw [averagedFirstFailure, sum_firstFailure]
  calc ((k.factorial : ℕ) : R)⁻¹ * ((((r : ℕ).factorial * (k - r).factorial : ℕ) : R) *
          esymm s r - ((((r : ℕ) + 1).factorial * (k - ((r : ℕ) + 1)).factorial : ℕ) : R) *
            esymm s ((r : ℕ) + 1))
      = (((r : ℕ).factorial * (k - r).factorial : ℕ) : R) / (k.factorial : R) * esymm s r -
          ((((r : ℕ) + 1).factorial * (k - ((r : ℕ) + 1)).factorial : ℕ) : R) /
            (k.factorial : R) * esymm s ((r : ℕ) + 1) := by ring
    _ = _ := by rw [ha, hb]; ring

/-- **Theorem 3.1, `(PFF.5)`** in the `1`-indexed position `r + 1`:
`W_{r+1} = ((k - r) e_r - (r + 1) e_{r+1}) / (k C(k-1, r))`. -/
theorem averagedFirstFailure_eq {R : Type*} [Field R] [CharZero R] (s : Fin k → R) (r : Fin k) :
    averagedFirstFailure s r =
      (((k : R) - r) * esymm s r - ((r : R) + 1) * esymm s ((r : ℕ) + 1)) /
        ((k : R) * ((k - 1).choose r : R)) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by have := r.2; omega⟩
  have hrn : (r : ℕ) ≤ n := Nat.lt_succ_iff.1 r.2
  rw [averagedFirstFailure_eq_div_choose, Nat.add_sub_cancel]
  have hca : ((n + 1).choose r : R) ≠ 0 := by exact_mod_cast (Nat.choose_pos r.2.le).ne'
  have hcb : ((n + 1).choose ((r : ℕ) + 1) : R) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (Nat.succ_le_of_lt r.2)).ne'
  have hD : ((n + 1 : ℕ) : R) * (n.choose r : R) ≠ 0 := by
    have : 0 < (n + 1) * n.choose r := Nat.mul_pos (Nat.succ_pos n) (Nat.choose_pos hrn)
    exact_mod_cast this.ne'
  have hc1 : ((n + 1 : ℕ) : R) * (n.choose r : R) = ((n + 1).choose r : R) * ((n : R) + 1 - r) := by
    have := Nat.choose_mul_succ_eq n r
    have hsub : ((n + 1 - (r : ℕ) : ℕ) : R) = (n : R) + 1 - r := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [← hsub, mul_comm (((n + 1 : ℕ) : R))]
    exact_mod_cast this
  have hc2 : ((n + 1 : ℕ) : R) * (n.choose r : R) =
      ((n + 1).choose ((r : ℕ) + 1) : R) * ((r : R) + 1) := by
    have := Nat.add_one_mul_choose_eq n r
    exact_mod_cast this
  rw [div_sub_div _ _ hca hcb, div_eq_div_iff (mul_ne_zero hca hcb) hD]
  push_cast at hc1 hc2 ⊢
  linear_combination (esymm (fun i => s i) r * ((n + 1).choose ((r : ℕ) + 1) : R)) * hc1 -
    (((n + 1).choose r : R) * esymm s ((r : ℕ) + 1)) * hc2

/-- **`(PFF.6)`** the full failure ledger conserves the failed mass: `∑_r W_r = 1 - e_k`. -/
theorem sum_averagedFirstFailure {R : Type*} [Field R] [CharZero R] (s : Fin k → R) :
    ∑ r, averagedFirstFailure s r = 1 - esymm s k := by
  simp_rw [averagedFirstFailure_eq_div_choose]
  rw [Fin.sum_univ_eq_sum_range (fun r => esymm s r / (k.choose r : R) -
    esymm s (r + 1) / (k.choose (r + 1) : R)), sum_range_sub', esymm_zero, Nat.choose_zero_right,
    Nat.choose_self, Nat.cast_one, div_one, div_one]

/-- **`(PFF.7)`** the averaged ledger recovers the elementary coefficients recursively:
`e_{r+1} = ((k - r) e_r - k C(k-1, r) W_{r+1}) / (r + 1)`. -/
theorem esymm_succ_eq {R : Type*} [Field R] [CharZero R] (s : Fin k → R) (r : Fin k) :
    esymm s ((r : ℕ) + 1) =
      (((k : R) - r) * esymm s r - (k : R) * ((k - 1).choose r : R) * averagedFirstFailure s r) /
        ((r : R) + 1) := by
  have hden : (k : R) * ((k - 1).choose r : R) ≠ 0 := by
    have : 0 < k * (k - 1).choose r := Nat.mul_pos (by have := r.2; omega)
      (Nat.choose_pos (by have := r.2; omega))
    exact_mod_cast this.ne'
  have hr : (r : R) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (r : ℕ)
  have hW : (k : R) * ((k - 1).choose r : R) * averagedFirstFailure s r =
      ((k : R) - r) * esymm s r - ((r : R) + 1) * esymm s ((r : ℕ) + 1) := by
    rw [averagedFirstFailure_eq, ← mul_div_assoc]
    exact mul_div_cancel_left₀ _ hden
  rw [hW, eq_div_iff hr]
  ring

/-- **`(PFF.7)`** two schedule-averaged ledgers that agree have the same elementary coefficients. -/
theorem esymm_eq_of_averagedFirstFailure_eq {R : Type*} [Field R] [CharZero R]
    {s t : Fin k → R} (h : ∀ r, averagedFirstFailure s r = averagedFirstFailure t r) :
    ∀ r ≤ k, esymm s r = esymm t r := by
  intro r hr
  induction r with
  | zero => rw [esymm_zero, esymm_zero]
  | succ r ih =>
    have hrk : r < k := hr
    rw [esymm_succ_eq s ⟨r, hrk⟩, esymm_succ_eq t ⟨r, hrk⟩, ih hrk.le, h]

/-! ### The prefix-set form `(PFF.8)` -/

/-- Each `(m+1)`-set arises from exactly `m + 1` pairs (an `m`-set, an outside index):
`∑_{|A| = m} ∑_{i ∉ A} s_A s_i = (m + 1) e_{m+1}`. -/
theorem sum_sum_compl_prod_mul {R : Type*} [CommRing R] (s : Fin k → R) (m : ℕ) :
    ∑ A ∈ (univ : Finset (Fin k)).powersetCard m, ∑ i ∈ univ \ A, (∏ j ∈ A, s j) * s i =
      ((m : R) + 1) * esymm s (m + 1) := by
  classical
  have hins : ∀ A ∈ (univ : Finset (Fin k)).powersetCard m,
      ∑ i ∈ univ \ A, (∏ j ∈ A, s j) * s i = ∑ i ∈ univ \ A, ∏ j ∈ insert i A, s j := by
    intro A _
    refine sum_congr rfl fun i hi => ?_
    rw [prod_insert (by simpa using hi)]
    ring
  have hcard : ∀ B ∈ (univ : Finset (Fin k)).powersetCard (m + 1),
      ((m : R) + 1) * ∏ j ∈ B, s j = ∑ _i ∈ B, ∏ j ∈ B, s j := by
    intro B hB
    rw [sum_const, (mem_powersetCard.1 hB).2, nsmul_eq_mul]
    push_cast
    ring
  rw [sum_congr rfl hins, esymm, mul_sum, sum_congr rfl hcard, sum_sigma', sum_sigma']
  refine sum_bij' (fun p _ => ⟨insert p.2 p.1, p.2⟩) (fun q _ => ⟨q.1.erase q.2, q.2⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨A, i⟩ hp
    simp only [mem_sigma, mem_powersetCard, subset_univ, true_and, mem_sdiff, mem_univ] at hp ⊢
    exact ⟨by rw [card_insert_of_notMem hp.2, hp.1], mem_insert_self _ _⟩
  · rintro ⟨B, i⟩ hq
    simp only [mem_sigma, mem_powersetCard, subset_univ, true_and, mem_sdiff, mem_univ] at hq ⊢
    exact ⟨by rw [card_erase_of_mem hq.2, hq.1]; rfl, notMem_erase _ _⟩
  · rintro ⟨A, i⟩ hp
    simp only [mem_sigma, mem_sdiff, mem_univ, true_and] at hp
    simp [erase_insert hp.2]
  · rintro ⟨B, i⟩ hq
    simp only [mem_sigma] at hq
    simp [insert_erase hq.2]
  · rintro ⟨A, i⟩ _
    rfl

/-- **`(PFF.8)`**: `W_{r+1} = (r! (k-r-1)!/k!) ∑_{|A| = r} ∑_{i ∉ A} s_A (1 - s_i)`. -/
theorem averagedFirstFailure_eq_prefix_sum {R : Type*} [Field R] [CharZero R] (s : Fin k → R)
    (r : Fin k) :
    averagedFirstFailure s r =
      (((r : ℕ).factorial * (k - (r + 1)).factorial : ℕ) : R) / (k.factorial : R) *
        ∑ A ∈ (univ : Finset (Fin k)).powersetCard r, ∑ i ∈ univ \ A,
          (∏ j ∈ A, s j) * (1 - s i) := by
  have hsplit : ∑ A ∈ (univ : Finset (Fin k)).powersetCard r, ∑ i ∈ univ \ A,
      (∏ j ∈ A, s j) * (1 - s i) = ((k : R) - r) * esymm s r - ((r : R) + 1) * esymm s (r + 1) := by
    have h1 : ∑ A ∈ (univ : Finset (Fin k)).powersetCard r, ∑ i ∈ univ \ A, (∏ j ∈ A, s j) =
        ((k : R) - r) * esymm s r := by
      rw [esymm, mul_sum]
      refine sum_congr rfl fun A hA => ?_
      rw [sum_const, card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin,
        (mem_powersetCard.1 hA).2, nsmul_eq_mul, Nat.cast_sub r.2.le]
    rw [← h1, ← sum_sum_compl_prod_mul, ← sum_sub_distrib]
    refine sum_congr rfl fun A _ => ?_
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by ring
  rw [hsplit, averagedFirstFailure_eq]
  have hk : ((k.factorial : ℕ) : R) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  have hden : (k : R) * ((k - 1).choose r : R) ≠ 0 := by
    have : 0 < k * (k - 1).choose r := Nat.mul_pos (by have := r.2; omega)
      (Nat.choose_pos (by have := r.2; omega))
    exact_mod_cast this.ne'
  have hfac : (k : ℕ) * (k - 1).choose r * ((r : ℕ).factorial * (k - (r + 1)).factorial) =
      k.factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (show (r : ℕ) ≤ k - 1 by have := r.2; omega)
    rw [show k - 1 - r = k - (r + 1) by omega] at h
    calc (k : ℕ) * (k - 1).choose r * ((r : ℕ).factorial * (k - (r + 1)).factorial) =
          k * ((k - 1).choose r * (r : ℕ).factorial * (k - (r + 1)).factorial) := by ring
      _ = k * (k - 1).factorial := by rw [h]
      _ = k.factorial := Nat.mul_factorial_pred (by have := r.2; omega)
  have hfacR : (k : R) * ((k - 1).choose r : R) *
      (((r : ℕ).factorial * (k - (r + 1)).factorial : ℕ) : R) = (k.factorial : R) := by
    exact_mod_cast hfac
  have hF : (((r : ℕ).factorial * (k - (r + 1)).factorial : ℕ) : R) ≠ 0 := by
    exact_mod_cast (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)).ne'
  rw [← hfacR]
  field_simp

end GaloisForLFunctions.HTGeometry.FirstFailure
