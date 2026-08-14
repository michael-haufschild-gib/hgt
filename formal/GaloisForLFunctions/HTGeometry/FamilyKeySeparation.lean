import GaloisForLFunctions.HTGeometry.FamilyKeyInnerSum

/-!
# A monomial is seen by the square-free keys of its own slot count

The weight of a square-free atom key couples the truncation degree to the key: a split realizing the
key of `k` has `∑ l = ∑ k − ord m`, while the truncation forces `∑ l = N − m none`.  So a fixed `N`
selects a different family of monomials for every key.  Letting `N` follow the key,

```text
N(k) = m₀ none + ∑ k − ord m₀ ,
```

selects instead the *fixed* class of monomials with the slot count of `m₀` and the same value of
`m none − ord m`.  Over that class the key weight is a sum of slot-sequence contributions indexed by
pairs (monomial, ordering) — an index set independent of the key — so the slot-sequence separation
applies and returns the coefficient of `m₀`.
-/

open Finset

namespace GaloisForLFunctions

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-! ### Reading a monomial off its slot sequence -/

omit [DecidableEq ι] in
theorem slotOrderSum_eq_sum_slotSeq {n D : ℕ} {m : Option (ι × Fin (n + 1)) →₀ ℕ}
    (h : (∑ p : ι × Fin (n + 1), m (some p)) = D) (σ : Equiv.Perm (Fin D)) :
    slotOrderSum n m = ∑ s, (slotSeqOf n D m σ s).2 := by
  classical
  rw [slotOrderSum]
  refine (Equiv.sum_comp (σ.trans (finCongr h).symm)
    (fun t => ((famSlot n m t).2 : ℕ))).symm.trans ?_
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [slotSeqOf_apply h, slotLabel]
  rfl

theorem slotSeqOf_card_filter {n D : ℕ} {m : Option (ι × Fin (n + 1)) →₀ ℕ}
    (h : (∑ p : ι × Fin (n + 1), m (some p)) = D) (σ : Equiv.Perm (Fin D))
    (p : ι × Fin (n + 1)) :
    (Finset.univ.filter (fun s => slotSeqOf n D m σ s = slotLabel p)).card = m (some p) := by
  classical
  have hiff : ∀ s : Fin D,
      (slotSeqOf n D m σ s = slotLabel p)
        ↔ (famSlot n m ((finCongr h).symm (σ s)) = p) := by
    intro s
    rw [slotSeqOf_apply h]
    exact ⟨fun hh => slotLabel_injective hh, fun hh => by rw [hh]⟩
  have hset : (Finset.univ.filter (fun s : Fin D => slotSeqOf n D m σ s = slotLabel p))
      = (Finset.univ.filter (fun s : Fin D =>
          famSlot n m ((finCongr h).symm (σ s)) = p)) :=
    Finset.filter_congr (fun s _ => hiff s)
  have hsum : (∑ s : Fin D,
        if famSlot n m ((finCongr h).symm (σ s)) = p then (1 : ℕ) else 0)
      = ∑ t : Fin (∑ p' : ι × Fin (n + 1), m (some p')),
          if famSlot n m t = p then (1 : ℕ) else 0 :=
    Equiv.sum_comp (σ.trans (finCongr h).symm)
      (fun t => if famSlot n m t = p then (1 : ℕ) else 0)
  rw [hset, Finset.card_filter, hsum, ← Finset.card_filter]
  exact card_filter_flatIndex (fun p' : ι × Fin (n + 1) => m (some p')) p

/-! ### The class selected by a key-following truncation -/

/-- The monomials a key-following truncation exposes: those of the reference slot count and the same
excess of point degree over jet order. -/
def keyClass (n D : ℕ) (m₀ : Option (ι × Fin (n + 1)) →₀ ℕ)
    (Q : MvPolynomial (Option (ι × Fin (n + 1))) ℂ) :
    Finset (Option (ι × Fin (n + 1)) →₀ ℕ) := by
  classical
  exact Q.support.filter (fun m => (∑ p : ι × Fin (n + 1), m (some p)) = D
    ∧ m none + slotOrderSum n m₀ = m₀ none + slotOrderSum n m)

omit [DecidableEq ι] [Nonempty ι] in
theorem slotOrderSum_le {n : ℕ} (m : Option (ι × Fin (n + 1)) →₀ ℕ) :
    slotOrderSum n m ≤ (∑ p : ι × Fin (n + 1), m (some p)) * n := by
  rw [slotOrderSum]
  calc ∑ t : Fin (∑ p : ι × Fin (n + 1), m (some p)), ((famSlot n m t).2 : ℕ)
      ≤ ∑ _t : Fin (∑ p : ι × Fin (n + 1), m (some p)), n :=
        Finset.sum_le_sum fun t _ => famSlot_snd_le n m t
    _ = (∑ p : ι × Fin (n + 1), m (some p)) * n := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

omit [DecidableEq ι] [Nonempty ι] in
theorem slotOrderSum_le_sum {n D : ℕ} (m : Option (ι × Fin (n + 1)) →₀ ℕ)
    (hcnt : (∑ p : ι × Fin (n + 1), m (some p)) = D) {k : Fin D → ℕ} (hkn : ∀ s, n < k s) :
    slotOrderSum n m ≤ ∑ s, k s := by
  have h1 : slotOrderSum n m ≤ D * n := by
    have := slotOrderSum_le (n := n) m
    rw [hcnt] at this
    exact this
  have h2 : ∑ _s : Fin D, (n + 1) ≤ ∑ s, k s :=
    Finset.sum_le_sum fun s _ => hkn s
  have h3 : ∑ _s : Fin D, (n + 1) = D * (n + 1) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [h3] at h2
  have h4 : D * n ≤ D * (n + 1) := Nat.mul_le_mul_left D (Nat.le_succ n)
  omega

/-! ### The key weight over the class -/

/-- The truncation degree that follows a key. -/
def keyTrunc (n : ℕ) (m₀ : Option (ι × Fin (n + 1)) →₀ ℕ) {D : ℕ} (k : Fin D → ℕ) : ℕ :=
  m₀ none + (∑ s, k s) - slotOrderSum n m₀

omit [DecidableEq ι] [Nonempty ι] in
/-- The key weight expanded over monomials. -/
theorem famAevalWeight_expand (q : ι → ℂ) {n : ℕ} (N : ℕ)
    (Q : MvPolynomial (Option (ι × Fin (n + 1))) ℂ) (ν : ℕ →₀ ℕ) :
    famAevalWeight q n N Q ν
      = ∑ m ∈ Q.support.filter (fun m => m none ≤ N),
          MvPolynomial.coeff m Q *
            ∑ l ∈ (((Finset.univ :
                Finset (Fin (∑ p : ι × Fin (n + 1), m (some p)))).finsuppAntidiag
                  (N - m none)).filter
              (fun l => key (famOrder n m l) = ν)), famWeight q n m l := by
  classical
  rw [famAevalWeight, Finset.sum_filter, famSigmaIdx, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_ite, mul_zero]
  rfl

omit [DecidableEq ι] [Nonempty ι] in
/-- A split contributing at a key-following truncation forces its monomial into the class. -/
theorem mem_keyClass_of_contributes {n D : ℕ}
    {m₀ m : Option (ι × Fin (n + 1)) →₀ ℕ}
    {k : Fin D → ℕ} (hkn : ∀ s, n < k s)
    (hcnt₀ : (∑ p : ι × Fin (n + 1), m₀ (some p)) = D)
    {l : Fin (∑ p : ι × Fin (n + 1), m (some p)) →₀ ℕ}
    (hl : ∑ t, l t = keyTrunc n m₀ k - m none)
    (hle : m none ≤ keyTrunc n m₀ k)
    (hkey : key (famOrder n m l) = key k) :
    (∑ p : ι × Fin (n + 1), m (some p)) = D
      ∧ m none + slotOrderSum n m₀ = m₀ none + slotOrderSum n m := by
  classical
  have hcnt : (∑ p : ι × Fin (n + 1), m (some p)) = D := slotCount_eq_of_key m l hkey
  have hw : (∑ t, famOrder n m l t) = ∑ s, k s := by
    have h1 := key_weighted_sum (famOrder n m l)
    have h2 := key_weighted_sum k
    rw [hkey, h2] at h1
    exact h1.symm
  have hsplit : (∑ t, famOrder n m l t) = (∑ t, l t) + slotOrderSum n m := by
    rw [slotOrderSum, ← Finset.sum_add_distrib]
    rfl
  have h0 : slotOrderSum n m ≤ ∑ s, k s := slotOrderSum_le_sum m hcnt hkn
  have h0' : slotOrderSum n m₀ ≤ ∑ s, k s := slotOrderSum_le_sum m₀ hcnt₀ hkn
  rw [hsplit, hl] at hw
  rw [keyTrunc] at hle hw
  exact ⟨hcnt, by omega⟩

omit [DecidableEq ι] in
/-- **The key weight is a class sum of slot-sequence contributions.** -/
theorem famAevalWeight_key_eq_class_sum (q : ι → ℂ) {n D : ℕ}
    (Q : MvPolynomial (Option (ι × Fin (n + 1))) ℂ)
    (m₀ : Option (ι × Fin (n + 1)) →₀ ℕ)
    (hcnt₀ : (∑ p : ι × Fin (n + 1), m₀ (some p)) = D)
    {k : Fin D → ℕ} (hkinj : Function.Injective k) (hkn : ∀ s, n < k s) :
    famAevalWeight q n (keyTrunc n m₀ k) Q (key k)
      = ∑ m ∈ keyClass n D m₀ Q, MvPolynomial.coeff m Q *
          ∑ σ : Equiv.Perm (Fin D), HTGeometry.slotTerm q (slotSeqOf n D m σ) k := by
  classical
  have h0' : slotOrderSum n m₀ ≤ ∑ s, k s := slotOrderSum_le_sum m₀ hcnt₀ hkn
  have hmemclass : ∀ m, m ∈ keyClass n D m₀ Q ↔ (m ∈ Q.support
      ∧ (∑ p : ι × Fin (n + 1), m (some p)) = D
      ∧ m none + slotOrderSum n m₀ = m₀ none + slotOrderSum n m) := by
    intro m
    rw [keyClass, Finset.mem_filter]
  have hsub : keyClass n D m₀ Q
      ⊆ Q.support.filter (fun m => m none ≤ keyTrunc n m₀ k) := by
    intro m hm
    obtain ⟨hmQ, hcnt, hrel⟩ := (hmemclass m).mp hm
    have h0 : slotOrderSum n m ≤ ∑ s, k s := slotOrderSum_le_sum m hcnt hkn
    refine Finset.mem_filter.mpr ⟨hmQ, ?_⟩
    rw [keyTrunc]
    omega
  rw [famAevalWeight_expand]
  refine (Finset.sum_subset hsub ?_).symm.trans ?_
  · intro m hm hnot
    obtain ⟨hmQ, hmle⟩ := Finset.mem_filter.mp hm
    refine mul_eq_zero_of_right _ ?_
    refine Finset.sum_eq_zero fun l hl => ?_
    obtain ⟨hlanti, hlkey⟩ := Finset.mem_filter.mp hl
    obtain ⟨hlsum, -⟩ := Finset.mem_finsuppAntidiag.mp hlanti
    obtain ⟨hcnt, hrel⟩ := mem_keyClass_of_contributes hkn hcnt₀ hlsum hmle hlkey
    exact absurd ((hmemclass m).mpr ⟨hmQ, hcnt, hrel⟩) hnot
  · refine Finset.sum_congr rfl fun m hm => ?_
    obtain ⟨hmQ, hcnt, hrel⟩ := (hmemclass m).mp hm
    have h0 : slotOrderSum n m ≤ ∑ s, k s := slotOrderSum_le_sum m hcnt hkn
    have hpar : keyTrunc n m₀ k - m none = (∑ s, k s) - slotOrderSum n m := by
      rw [keyTrunc]
      omega
    rw [hpar, sum_famWeight_key_eq_slotSeq q m hcnt hkinj hkn]

/-- **A monomial's coefficient is read by the square-free keys of its own slot count.**  If the
square-free key weights at every injective key above the jet order, taken at the truncation that
follows the key, all vanish, then the coefficient of the reference monomial vanishes. -/
theorem coeff_eq_zero_of_famAevalWeight_key_vanishing (q : ι → ℂ) (hq0 : ∀ i, q i ≠ 0)
    (hqinj : Function.Injective q) {n : ℕ} {K₀ : ℕ} (hK₀ : n ≤ K₀)
    (Q : MvPolynomial (Option (ι × Fin (n + 1))) ℂ)
    (m₀ : Option (ι × Fin (n + 1)) →₀ ℕ)
    (h : ∀ k : Fin (∑ p : ι × Fin (n + 1), m₀ (some p)) → ℕ, (∀ s, K₀ < k s) →
      Function.Injective k → famAevalWeight q n (keyTrunc n m₀ k) Q (key k) = 0) :
    MvPolynomial.coeff m₀ Q = 0 := by
  classical
  set D : ℕ := ∑ p : ι × Fin (n + 1), m₀ (some p) with hD
  by_cases hm₀ : m₀ ∈ Q.support
  · set T : Finset ((Option (ι × Fin (n + 1)) →₀ ℕ) × Equiv.Perm (Fin D)) :=
      (keyClass n D m₀ Q) ×ˢ (Finset.univ : Finset (Equiv.Perm (Fin D))) with hT
    have hTsum : ∀ k : Fin D → ℕ, (∀ s, K₀ < k s) → Function.Injective k →
        ∑ a ∈ T, MvPolynomial.coeff a.1 Q
            * HTGeometry.slotTerm q (slotSeqOf n D a.1 a.2) k = 0 := by
      intro k hkn hkinj
      have hkn' : ∀ s, n < k s := fun s => lt_of_le_of_lt hK₀ (hkn s)
      rw [hT, Finset.sum_product]
      have hb := famAevalWeight_key_eq_class_sum q Q m₀ rfl hkinj hkn'
      rw [h k hkn hkinj] at hb
      refine Eq.trans ?_ hb.symm
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Finset.mul_sum]
    have hgrouped := HTGeometry.slotSequence_grouped_eq_zero q hq0 hqinj K₀ T
      (fun a => slotSeqOf n D a.1 a.2) (fun a => MvPolynomial.coeff a.1 Q) hTsum
      (slotSeqOf n D m₀ 1)
    have hm₀class : m₀ ∈ keyClass n D m₀ Q := by
      rw [keyClass, Finset.mem_filter]
      exact ⟨hm₀, rfl, rfl⟩
    have hfib : ∀ a ∈ T.filter (fun a => slotSeqOf n D a.1 a.2 = slotSeqOf n D m₀ 1),
        a.1 = m₀ := by
      intro a ha
      obtain ⟨haT, haw⟩ := Finset.mem_filter.mp ha
      obtain ⟨haclass, -⟩ := Finset.mem_product.mp haT
      obtain ⟨-, hcnt, hrel⟩ := (by
        rw [keyClass, Finset.mem_filter] at haclass
        exact ⟨haclass.1, haclass.2.1, haclass.2.2⟩ :
        a.1 ∈ Q.support ∧ (∑ p : ι × Fin (n + 1), a.1 (some p)) = D
          ∧ a.1 none + slotOrderSum n m₀ = m₀ none + slotOrderSum n (a.1))
      have hmult : ∀ p : ι × Fin (n + 1), a.1 (some p) = m₀ (some p) := by
        intro p
        have h1 := slotSeqOf_card_filter hcnt a.2 p
        have h2 := slotSeqOf_card_filter (D := D) (m := m₀) rfl 1 p
        rw [haw] at h1
        rw [← h1, ← h2]
      have hord : slotOrderSum n a.1 = slotOrderSum n m₀ := by
        have h1 := slotOrderSum_eq_sum_slotSeq hcnt a.2
        have h2 := slotOrderSum_eq_sum_slotSeq (D := D) (m := m₀) rfl 1
        rw [haw] at h1
        rw [h1, h2]
      refine Finsupp.ext fun x => ?_
      cases x with
      | none =>
          rw [hord] at hrel
          omega
      | some p => exact hmult p
    have hcard : ∑ a ∈ T.filter (fun a => slotSeqOf n D a.1 a.2 = slotSeqOf n D m₀ 1),
        MvPolynomial.coeff a.1 Q
        = ((T.filter (fun a => slotSeqOf n D a.1 a.2 = slotSeqOf n D m₀ 1)).card : ℂ)
          * MvPolynomial.coeff m₀ Q := by
      rw [Finset.sum_congr rfl (fun a ha => by rw [hfib a ha]), Finset.sum_const, nsmul_eq_mul]
    have hne : (m₀, (1 : Equiv.Perm (Fin D)))
        ∈ T.filter (fun a => slotSeqOf n D a.1 a.2 = slotSeqOf n D m₀ 1) :=
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hm₀class, Finset.mem_univ _⟩, rfl⟩
    have hpos : 0 < (T.filter (fun a => slotSeqOf n D a.1 a.2 = slotSeqOf n D m₀ 1)).card :=
      Finset.card_pos.mpr ⟨_, hne⟩
    rw [hcard] at hgrouped
    have hcne : ((T.filter (fun a => slotSeqOf n D a.1 a.2 = slotSeqOf n D m₀ 1)).card : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr hpos.ne'
    rcases mul_eq_zero.mp hgrouped with hc | hc
    · exact absurd hc hcne
    · exact hc
  · exact MvPolynomial.notMem_support_iff.mp hm₀

/-- **A nonzero jet polynomial is seen by some square-free key.**  There is a monomial and an
injective key above the jet order whose weight, at the truncation following that key, is nonzero. -/
theorem exists_key_famAevalWeight_ne_zero (q : ι → ℂ) (hq0 : ∀ i, q i ≠ 0)
    (hqinj : Function.Injective q) {n : ℕ} {K₀ : ℕ} (hK₀ : n ≤ K₀)
    (Q : MvPolynomial (Option (ι × Fin (n + 1))) ℂ) (hQ : Q ≠ 0) :
    ∃ (m₀ : Option (ι × Fin (n + 1)) →₀ ℕ)
      (k : Fin (∑ p : ι × Fin (n + 1), m₀ (some p)) → ℕ),
      (∀ s, K₀ < k s) ∧ Function.Injective k
        ∧ famAevalWeight q n (keyTrunc n m₀ k) Q (key k) ≠ 0 := by
  classical
  obtain ⟨m₀, hm₀⟩ := MvPolynomial.support_nonempty.mpr hQ
  have hcoeff : MvPolynomial.coeff m₀ Q ≠ 0 := MvPolynomial.mem_support_iff.mp hm₀
  by_contra hcon
  refine hcoeff (coeff_eq_zero_of_famAevalWeight_key_vanishing q hq0 hqinj hK₀ Q m₀ ?_)
  intro k hkn hkinj
  by_contra hne
  exact hcon ⟨m₀, k, hkn, hkinj, hne⟩

end

end GaloisForLFunctions
