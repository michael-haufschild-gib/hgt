import GaloisForLFunctions.HTGeometry.FamilyDilatedMagnitude

/-!
# Square-free atom keys

An atom key is the order-blind multiset of source-coefficient indices consumed by a jet split.  The
keys that separate a differential relation are the *square-free* ones: `D` pairwise distinct
indices, each used once.  Such a key is realized by a slot-order tuple exactly when that tuple is a
permutation of the chosen index tuple, so the splits realizing it are indexed by permutations.

* `key_apply` — the key counts slots by consumed index;
* `key_eq_iff_exists_perm` — a tuple has the same key as an injective tuple exactly when it is a
  permutation of it.
-/

open Finset

namespace GaloisForLFunctions

noncomputable section

theorem key_apply {D : ℕ} (h : Fin D → ℕ) (ν : ℕ) :
    key h ν = (Finset.univ.filter (fun t => h t = ν)).card := by
  classical
  rw [key, Finsupp.finsetSum_apply]
  rw [Finset.sum_congr rfl (fun t (_ : t ∈ Finset.univ) => Finsupp.single_apply (a := h t)
    (b := (1 : ℕ)) (a' := ν))]
  exact (Finset.card_filter _ _).symm

/-- A tuple realizes the key of an injective tuple exactly when it is a permutation of it. -/
theorem key_eq_iff_exists_perm {D : ℕ} {h k : Fin D → ℕ} (hk : Function.Injective k) :
    key h = key k ↔ ∃ σ : Equiv.Perm (Fin D), h = k ∘ σ := by
  classical
  constructor
  · intro hkey
    -- every value of `k` is attained exactly once by `h`
    have hcount : ∀ s : Fin D,
        (Finset.univ.filter (fun t => h t = k s)).card = 1 := by
      intro s
      have h1 := congrArg (fun f : ℕ →₀ ℕ => f (k s)) hkey
      rw [key_apply, key_apply] at h1
      rw [h1]
      refine Finset.card_eq_one.mpr ⟨s, ?_⟩
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun ht => hk ht, fun ht => by rw [ht]⟩
    -- so `h` hits `range k` and is injective
    have hmemrange : ∀ t : Fin D, ∃ s : Fin D, h t = k s := by
      intro t
      by_contra hcon0
      have hcon := not_exists.mp hcon0
      have hzero : (Finset.univ.filter (fun u => k u = h t)).card = 0 := by
        refine Finset.card_eq_zero.mpr (Finset.eq_empty_iff_forall_notMem.mpr fun u hu => ?_)
        exact hcon u ((Finset.mem_filter.mp hu).2).symm
      have h1 := congrArg (fun f : ℕ →₀ ℕ => f (h t)) hkey
      rw [key_apply, key_apply, hzero] at h1
      have hpos : 0 < (Finset.univ.filter (fun u => h u = h t)).card :=
        Finset.card_pos.mpr ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ t, rfl⟩⟩
      omega
    have hinj : Function.Injective h := by
      intro t u htu
      obtain ⟨s, hs⟩ := hmemrange t
      have hcard := hcount s
      obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hcard
      have ht : t ∈ Finset.univ.filter (fun v => h v = k s) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ t, hs⟩
      have hu : u ∈ Finset.univ.filter (fun v => h v = k s) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ u, htu.symm.trans hs⟩
      rw [hw, Finset.mem_singleton] at ht hu
      rw [ht, hu]
    -- the permutation carrying `k` to `h`
    choose sel hsel using hmemrange
    have hσinj : Function.Injective sel := by
      intro t u htu
      refine hinj ?_
      rw [hsel t, hsel u, htu]
    refine ⟨Equiv.ofBijective sel ⟨hσinj, Finite.injective_iff_surjective.mp hσinj⟩, ?_⟩
    funext t
    exact hsel t
  · rintro ⟨σ, rfl⟩
    rw [key, key]
    exact Fintype.sum_equiv σ _ _ (fun t => rfl)

/-! ### The splits realizing a square-free key -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The split realizing the square-free key of `k` through the permutation `σ`. -/
noncomputable def keySplit (n : ℕ) (m : Option (ι × Fin (n + 1)) →₀ ℕ)
    (k : Fin (∑ p : ι × Fin (n + 1), m (some p)) → ℕ)
    (σ : Equiv.Perm (Fin (∑ p : ι × Fin (n + 1), m (some p)))) :
    Fin (∑ p : ι × Fin (n + 1), m (some p)) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun t => k (σ t) - ((famSlot n m t).2 : ℕ))

omit [DecidableEq ι] in
@[simp] theorem keySplit_apply (n : ℕ) (m : Option (ι × Fin (n + 1)) →₀ ℕ)
    (k : Fin (∑ p : ι × Fin (n + 1), m (some p)) → ℕ)
    (σ : Equiv.Perm (Fin (∑ p : ι × Fin (n + 1), m (some p))))
    (t : Fin (∑ p : ι × Fin (n + 1), m (some p))) :
    keySplit n m k σ t = k (σ t) - ((famSlot n m t).2 : ℕ) := rfl

omit [DecidableEq ι] in
theorem famSlot_snd_le (n : ℕ) (m : Option (ι × Fin (n + 1)) →₀ ℕ)
    (t : Fin (∑ p : ι × Fin (n + 1), m (some p))) : ((famSlot n m t).2 : ℕ) ≤ n :=
  Nat.lt_succ_iff.mp (famSlot n m t).2.isLt

omit [DecidableEq ι] in
theorem famOrder_keySplit (n : ℕ) (m : Option (ι × Fin (n + 1)) →₀ ℕ)
    {k : Fin (∑ p : ι × Fin (n + 1), m (some p)) → ℕ} (hkn : ∀ s, n < k s)
    (σ : Equiv.Perm (Fin (∑ p : ι × Fin (n + 1), m (some p))))
    (t : Fin (∑ p : ι × Fin (n + 1), m (some p))) :
    famOrder n m (keySplit n m k σ) t = k (σ t) := by
  rw [famOrder, keySplit_apply]
  have h1 := famSlot_snd_le n m t
  have h2 := hkn (σ t)
  omega

omit [DecidableEq ι] in
theorem key_famOrder_keySplit (n : ℕ) (m : Option (ι × Fin (n + 1)) →₀ ℕ)
    {k : Fin (∑ p : ι × Fin (n + 1), m (some p)) → ℕ} (hkn : ∀ s, n < k s)
    (σ : Equiv.Perm (Fin (∑ p : ι × Fin (n + 1), m (some p)))) :
    key (famOrder n m (keySplit n m k σ)) = key k := by
  have hfun : famOrder n m (keySplit n m k σ) = k ∘ σ :=
    funext fun t => famOrder_keySplit n m hkn σ t
  rw [hfun, key, key]
  exact Fintype.sum_equiv σ _ _ (fun t => rfl)

omit [DecidableEq ι] in
theorem sum_keySplit (n : ℕ) (m : Option (ι × Fin (n + 1)) →₀ ℕ)
    {k : Fin (∑ p : ι × Fin (n + 1), m (some p)) → ℕ} (hkn : ∀ s, n < k s)
    (σ : Equiv.Perm (Fin (∑ p : ι × Fin (n + 1), m (some p)))) :
    ∑ t, keySplit n m k σ t
      = (∑ s, k s) - (∑ t, ((famSlot n m t).2 : ℕ)) := by
  have hle : ∀ t ∈ (Finset.univ : Finset (Fin (∑ p : ι × Fin (n + 1), m (some p)))),
      ((famSlot n m t).2 : ℕ) ≤ k (σ t) := by
    intro t _
    have h1 := famSlot_snd_le n m t
    have h2 := hkn (σ t)
    omega
  have hsplit : ∑ t, keySplit n m k σ t
      = (∑ t, k (σ t)) - (∑ t, ((famSlot n m t).2 : ℕ)) := by
    simp only [keySplit_apply]
    exact Finset.sum_tsub_distrib _ hle
  rw [hsplit]
  congr 1
  exact Fintype.sum_equiv σ _ _ (fun t => rfl)

omit [DecidableEq ι] in
/-- The weight of the split attached to `σ`, read off along the chosen index tuple. -/
theorem famWeight_keySplit (q : ι → ℂ) (n : ℕ) (m : Option (ι × Fin (n + 1)) →₀ ℕ)
    {k : Fin (∑ p : ι × Fin (n + 1), m (some p)) → ℕ} (hkn : ∀ s, n < k s)
    (σ : Equiv.Perm (Fin (∑ p : ι × Fin (n + 1), m (some p)))) :
    famWeight q n m (keySplit n m k σ)
      = ∏ s, ((((k s).descFactorial ((famSlot n m (σ.symm s)).2 : ℕ)) : ℂ)
              * (q (famSlot n m (σ.symm s)).1) ^ (k s)) := by
  rw [famWeight]
  rw [Finset.prod_congr rfl (fun t (_ : t ∈ Finset.univ) => by
    rw [famOrder_keySplit n m hkn σ t])]
  refine (Equiv.prod_comp σ.symm (fun s => (((k (σ s)).descFactorial
    ((famSlot n m s).2 : ℕ) : ℂ) * (q (famSlot n m s).1) ^ (k (σ s)))) ).symm.trans ?_
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [Equiv.apply_symm_apply]

omit [DecidableEq ι] in
/-- **The splits realizing a square-free key are the permutations.** -/
theorem sum_famWeight_over_squareFreeKey (q : ι → ℂ) (n : ℕ)
    (m : Option (ι × Fin (n + 1)) →₀ ℕ)
    {k : Fin (∑ p : ι × Fin (n + 1), m (some p)) → ℕ}
    (hkinj : Function.Injective k) (hkn : ∀ s, n < k s) :
    ∑ σ : Equiv.Perm (Fin (∑ p : ι × Fin (n + 1), m (some p))),
        famWeight q n m (keySplit n m k σ)
      = ∑ l ∈ (((Finset.univ : Finset (Fin (∑ p : ι × Fin (n + 1), m (some p)))).finsuppAntidiag
          ((∑ s, k s) - (∑ t, ((famSlot n m t).2 : ℕ)))).filter
          (fun l => key (famOrder n m l) = key k)),
        famWeight q n m l := by
  classical
  refine Finset.sum_bij (fun σ _ => keySplit n m k σ) ?_ ?_ ?_ (fun σ _ => rfl)
  · intro σ _
    refine Finset.mem_filter.mpr ⟨?_, key_famOrder_keySplit n m hkn σ⟩
    refine Finset.mem_finsuppAntidiag.mpr ⟨?_, Finset.subset_univ _⟩
    exact sum_keySplit n m hkn σ
  · intro σ _ σ' _ hσ
    refine Equiv.ext fun t => ?_
    have ht := congrFun (congrArg (fun l : Fin (∑ p : ι × Fin (n + 1), m (some p)) →₀ ℕ =>
      (l : Fin (∑ p : ι × Fin (n + 1), m (some p)) → ℕ)) hσ) t
    rw [keySplit_apply, keySplit_apply] at ht
    have h1 := famSlot_snd_le n m t
    have h2 := hkn (σ t)
    have h3 := hkn (σ' t)
    exact hkinj (by omega)
  · intro l hl
    obtain ⟨hlanti, hlkey⟩ := Finset.mem_filter.mp hl
    obtain ⟨σ, hσ⟩ := (key_eq_iff_exists_perm hkinj).mp hlkey
    refine ⟨σ, Finset.mem_univ σ, ?_⟩
    refine Finsupp.ext fun t => ?_
    have ht : l t + ((famSlot n m t).2 : ℕ) = k (σ t) := congrFun hσ t
    rw [keySplit_apply]
    omega

omit [DecidableEq ι] in
/-- **Node factorization at a shifted key.**  When the square-free key is a large common parameter
`K` shifted by bounded offsets, every split weight factors as the monomial's *node product* — the
product of the dilations over its slots, independent of the permutation — raised to `K`, times a
factor depending only on the offsets. -/
theorem famWeight_keySplit_shift (q : ι → ℂ) (n : ℕ) (m : Option (ι × Fin (n + 1)) →₀ ℕ)
    (K : ℕ) {δ : Fin (∑ p : ι × Fin (n + 1), m (some p)) → ℕ}
    (hkn : ∀ s, n < K + δ s)
    (σ : Equiv.Perm (Fin (∑ p : ι × Fin (n + 1), m (some p)))) :
    famWeight q n m (keySplit n m (fun s => K + δ s) σ)
      = (∏ t, q (famSlot n m t).1) ^ K
        * ∏ s, ((((K + δ s).descFactorial ((famSlot n m (σ.symm s)).2 : ℕ)) : ℂ)
                * (q (famSlot n m (σ.symm s)).1) ^ (δ s)) := by
  rw [famWeight_keySplit q n m hkn σ]
  have hfac : ∀ s, ((((K + δ s).descFactorial ((famSlot n m (σ.symm s)).2 : ℕ)) : ℂ)
        * (q (famSlot n m (σ.symm s)).1) ^ (K + δ s))
      = (q (famSlot n m (σ.symm s)).1) ^ K
        * ((((K + δ s).descFactorial ((famSlot n m (σ.symm s)).2 : ℕ)) : ℂ)
            * (q (famSlot n m (σ.symm s)).1) ^ (δ s)) := by
    intro s
    rw [pow_add]
    ring
  rw [Finset.prod_congr rfl (fun s (_ : s ∈ Finset.univ) => hfac s), Finset.prod_mul_distrib]
  congr 1
  rw [← Finset.prod_pow]
  exact Equiv.prod_comp σ.symm (fun t => q (famSlot n m t).1 ^ K)

end

end GaloisForLFunctions
