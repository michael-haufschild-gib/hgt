import Mathlib

/-!
# Free cyclic orbits of a finite permutation

A permutation `σ` of a finite type is *free of order `a`* when `σ ^ a = 1` and no power
`σ ^ k` with `0 < k < a` fixes a point.  Geometrically this is the unramified condition on a
covering: the deck transformation of order `a` acts without fixed points, so every orbit has
exactly `a` elements.

The file proves the two facts every fibre count of an orbifold covering needs:

* `IsFreeOfOrder.card_eq_mul_cycleType_card` — `card S = a * (number of orbits)`, with the orbit
  count realised as `σ.cycleType.card`;
* `IsFreeOfOrder.sign_eq` — `sign σ = (-1) ^ ((a + 1) * (number of orbits))`, the orientation
  constraint that forces the covering surface to have an integral genus;
* `IsFreeOfOrder.exists_transversal` — an explicit set of orbit representatives, of cardinality
  the orbit count, whose translates exhaust the underlying type.  This is the spanning set used
  in the rank estimate for voltage lifts.
-/

namespace GaloisForLFunctions.HTGeometry

open Equiv Equiv.Perm Finset

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- `σ` is a fixed-point-free deck transformation of order `a`: `σ ^ a = 1` and no intermediate
power fixes a point.  Every `⟨σ⟩`-orbit then has exactly `a` elements. -/
structure IsFreeOfOrder (σ : Perm S) (a : ℕ) : Prop where
  pow_eq_one : σ ^ a = 1
  free : ∀ k, 0 < k → k < a → ∀ s : S, (σ ^ k) s ≠ s

namespace IsFreeOfOrder

variable {σ : Perm S} {a : ℕ}

omit [Fintype S] [DecidableEq S] in
theorem apply_ne_self (h : IsFreeOfOrder σ a) (ha : 1 < a) (s : S) : σ s ≠ s := by
  have := h.free 1 one_pos ha s
  simpa using this

theorem support_eq_univ (h : IsFreeOfOrder σ a) (ha : 1 < a) : σ.support = Finset.univ := by
  ext s
  simp [Equiv.Perm.mem_support, h.apply_ne_self ha s]

omit [Fintype S] [DecidableEq S] in
/-- Distinct exponents below `a` move a point to distinct places. -/
theorem pow_apply_injOn (h : IsFreeOfOrder σ a) (s : S) {k j : ℕ} (hk : k < a) (hj : j < a)
    (hkj : (σ ^ k) s = (σ ^ j) s) : k = j := by
  by_contra hne
  -- reduce to the case `j < k`
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · -- `k < j`
    have hpow : (σ ^ k) ((σ ^ (j - k)) s) = (σ ^ k) s := by
      rw [← Equiv.Perm.mul_apply, ← pow_add]
      rw [Nat.add_sub_cancel' hlt.le]
      exact hkj.symm
    have : (σ ^ (j - k)) s = s := (σ ^ k).injective hpow
    exact h.free (j - k) (Nat.sub_pos_of_lt hlt) (lt_of_le_of_lt (Nat.sub_le _ _) hj) s this
  · -- `j < k`
    have hpow : (σ ^ j) ((σ ^ (k - j)) s) = (σ ^ j) s := by
      rw [← Equiv.Perm.mul_apply, ← pow_add]
      rw [Nat.add_sub_cancel' hlt.le]
      exact hkj
    have : (σ ^ (k - j)) s = s := (σ ^ j).injective hpow
    exact h.free (k - j) (Nat.sub_pos_of_lt hlt) (lt_of_le_of_lt (Nat.sub_le _ _) hk) s this

/-- Every cycle of a free permutation of order `a` has length exactly `a`. -/
theorem mem_cycleType (h : IsFreeOfOrder σ a) (ha : 2 ≤ a) {n : ℕ} (hn : n ∈ σ.cycleType) :
    n = a := by
  have hn0 : n ∈ σ.cycleType := hn
  rw [Equiv.Perm.cycleType_def] at hn
  obtain ⟨c, hc, hcn⟩ := Multiset.mem_map.mp hn
  rw [Finset.mem_val] at hc
  obtain ⟨hcyc, hceq⟩ := Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc
  have hn' : n = c.support.card := hcn.symm
  -- on the support of a cycle factor, the factor and the permutation have the same powers
  have key : ∀ x ∈ c.support, ∀ m : ℕ, (c ^ m) x = (σ ^ m) x := by
    intro x hx m
    have hmem : ∀ j : ℕ, (c ^ j) x ∈ c.support := by
      intro j
      induction j with
      | zero => simpa using hx
      | succ j ih =>
          have hstep : (c ^ (j + 1)) x = c ((c ^ j) x) := by rw [pow_succ']; rfl
          rw [hstep]
          exact Equiv.Perm.apply_mem_support.mpr ih
    induction m with
    | zero => simp
    | succ m ih =>
        have h1 : (c ^ (m + 1)) x = c ((c ^ m) x) := by rw [pow_succ']; rfl
        have h2 : (σ ^ (m + 1)) x = σ ((σ ^ m) x) := by rw [pow_succ']; rfl
        rw [h1, h2, hceq _ (hmem m), ih]
  -- `c ^ a = 1`
  have hca : c ^ a = 1 := by
    ext x
    by_cases hx : x ∈ c.support
    · have := key x hx a
      rw [h.pow_eq_one] at this
      simpa using this
    · have hcx : c x = x := by
        simpa [Equiv.Perm.mem_support] using hx
      have hall : ∀ m : ℕ, (c ^ m) x = x := by
        intro m
        induction m with
        | zero => simp
        | succ m ih =>
            have h1 : (c ^ (m + 1)) x = c ((c ^ m) x) := by rw [pow_succ']; rfl
            rw [h1, ih, hcx]
      simpa using hall a
  have horder : orderOf c = n := by rw [hn', hcyc.orderOf]
  have hdvd : n ∣ a := by
    rw [← horder]
    exact orderOf_dvd_of_pow_eq_one hca
  have hle : n ≤ a := Nat.le_of_dvd (by omega) hdvd
  -- a point of the cycle is fixed by `σ ^ n`
  obtain ⟨x, hx⟩ := hcyc.nonempty_support
  have hfix : (σ ^ n) x = x := by
    have hcn1 : (c ^ n) x = x := by
      have hc1 : c ^ n = 1 := by rw [← horder]; exact pow_orderOf_eq_one c
      simp [hc1]
    rw [← key x hx n, hcn1]
  have hn2 : 2 ≤ n := Equiv.Perm.two_le_of_mem_cycleType hn0
  by_contra hne
  exact h.free n (by omega) (by omega) x hfix

theorem cycleType_eq_replicate (h : IsFreeOfOrder σ a) (ha : 2 ≤ a) :
    σ.cycleType = Multiset.replicate σ.cycleType.card a :=
  Multiset.eq_replicate_card.mpr fun _ hb => h.mem_cycleType ha hb

/-- **Fibre count.**  The underlying type splits into `σ.cycleType.card` orbits of size `a`. -/
theorem card_eq_mul_cycleType_card (h : IsFreeOfOrder σ a) (ha : 2 ≤ a) :
    Fintype.card S = a * σ.cycleType.card := by
  have hsum : σ.cycleType.sum = σ.support.card := Equiv.Perm.sum_cycleType σ
  rw [h.support_eq_univ (by omega), Finset.card_univ] at hsum
  rw [← hsum, h.cycleType_eq_replicate ha, Multiset.sum_replicate]
  simp [Multiset.card_replicate, mul_comm]

/-- **Orientation constraint.**  The sign of a free permutation of order `a` with `f` orbits is
`(-1) ^ ((a + 1) * f)`. -/
theorem sign_eq (h : IsFreeOfOrder σ a) (ha : 2 ≤ a) :
    Equiv.Perm.sign σ = (-1) ^ ((a + 1) * σ.cycleType.card) := by
  rw [Equiv.Perm.sign_of_cycleType]
  congr 1
  rw [h.cycleType_eq_replicate ha, Multiset.sum_replicate]
  simp [Multiset.card_replicate]
  ring

end IsFreeOfOrder

section Transversal

variable {σ : Perm S} {a : ℕ}

/-- **Orbit transversal.**  A free permutation of order `a` admits a set of orbit representatives
whose `a` translates exhaust the type; its cardinality is the orbit count. -/
theorem IsFreeOfOrder.exists_transversal (h : IsFreeOfOrder σ a) (ha : 2 ≤ a) :
    ∃ T : Finset S, Fintype.card S = a * T.card ∧
      ∀ s : S, ∃ t ∈ T, ∃ k, k < a ∧ (σ ^ k) t = s := by
  classical
  letI : LinearOrder S := LinearOrder.lift' (Fintype.equivFin S) (Equiv.injective _)
  have ha0 : 0 < a := by omega
  -- the orbit of `s`
  set orb : S → Finset S := fun s => (Finset.range a).image (fun k => (σ ^ k) s) with horb
  have horb_ne : ∀ s, (orb s).Nonempty := by
    intro s
    refine ⟨s, ?_⟩
    simp only [horb, Finset.mem_image, Finset.mem_range]
    exact ⟨0, ha0, by simp⟩
  have hmem_orb : ∀ s t, t ∈ orb s ↔ ∃ k, k < a ∧ (σ ^ k) s = t := by
    intro s t
    simp only [horb, Finset.mem_image, Finset.mem_range]
  -- the orbit is stable under `σ`
  have horb_stable : ∀ s, ∀ t ∈ orb s, ∀ j, (σ ^ j) t ∈ orb s := by
    intro s t ht j
    obtain ⟨k, hk, rfl⟩ := (hmem_orb s t).mp ht
    refine (hmem_orb s _).mpr ⟨(j + k) % a, Nat.mod_lt _ ha0, ?_⟩
    have hcycle : σ ^ ((j + k) % a) = σ ^ (j + k) := by
      conv_rhs => rw [← Nat.div_add_mod (j + k) a]
      rw [pow_add, pow_mul, h.pow_eq_one, one_pow, one_mul]
    rw [hcycle, pow_add, Equiv.Perm.mul_apply]
  set T : Finset S := Finset.univ.filter (fun s => ∀ k, 0 < k → k < a → s < (σ ^ k) s) with hT
  have hmin_mem : ∀ s : S, (orb s).min' (horb_ne s) ∈ T := by
    intro s
    have hmem := Finset.min'_mem (orb s) (horb_ne s)
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and]
    intro k hk0 hka
    have h1 : (σ ^ k) ((orb s).min' (horb_ne s)) ∈ orb s := horb_stable s _ hmem k
    have h2 : (orb s).min' (horb_ne s) ≤ (σ ^ k) ((orb s).min' (horb_ne s)) :=
      Finset.min'_le _ _ h1
    exact lt_of_le_of_ne h2 (Ne.symm (h.free k hk0 hka _))
  -- distinct representatives lie in distinct orbits
  have hT_unique : ∀ t ∈ T, ∀ t' ∈ T, ∀ m, m < a → (σ ^ m) t = t' → t = t' := by
    intro t ht t' ht' m hm hmt
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · simpa using hmt
    · exfalso
      simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at ht ht'
      have hlt1 : t < t' := by rw [← hmt]; exact ht m hm0 hm
      have hback : (σ ^ (a - m)) t' = t := by
        rw [← hmt, ← Equiv.Perm.mul_apply, ← pow_add]
        rw [Nat.sub_add_cancel hm.le, h.pow_eq_one]
        rfl
      have hlt2 : t' < t := by
        rw [← hback]
        exact ht' (a - m) (by omega) (by omega)
      exact absurd hlt1 (not_lt.mpr hlt2.le)
  -- the map `T × Fin a → S` is a bijection
  have hbij : Function.Bijective (fun p : T × Fin a => (σ ^ (p.2 : ℕ)) (p.1 : S)) := by
    constructor
    · rintro ⟨⟨t, ht⟩, ⟨k, hk⟩⟩ ⟨⟨t', ht'⟩, ⟨j, hj⟩⟩ hEq
      simp only at hEq
      -- `t` and `t'` are in the same orbit
      have hsame : t = t' := by
        rcases le_total k j with hle | hle
        · have : (σ ^ (j - k)) t' = t := by
            have : (σ ^ k) ((σ ^ (j - k)) t') = (σ ^ k) t := by
              rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' hle]
              exact hEq.symm
            exact (σ ^ k).injective this
          exact (hT_unique t' ht' t ht (j - k) (by omega) this).symm
        · have : (σ ^ (k - j)) t = t' := by
            have : (σ ^ j) ((σ ^ (k - j)) t) = (σ ^ j) t' := by
              rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' hle]
              exact hEq
            exact (σ ^ j).injective this
          exact hT_unique t ht t' ht' (k - j) (by omega) this
      subst hsame
      have : k = j := h.pow_apply_injOn t hk hj hEq
      subst this
      rfl
    · intro s
      obtain ⟨k, hk, hks⟩ := (hmem_orb s _).mp (Finset.min'_mem (orb s) (horb_ne s))
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · refine ⟨⟨⟨(orb s).min' (horb_ne s), hmin_mem s⟩, ⟨0, ha0⟩⟩, ?_⟩
        simp only [pow_zero, Equiv.Perm.one_apply] at hks ⊢
        exact hks.symm
      · refine ⟨⟨⟨(orb s).min' (horb_ne s), hmin_mem s⟩, ⟨a - k, by omega⟩⟩, ?_⟩
        show (σ ^ (a - k)) ((orb s).min' (horb_ne s)) = s
        rw [← hks, ← Equiv.Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hk.le,
          h.pow_eq_one]
        rfl
  refine ⟨T, ?_, ?_⟩
  · have := Fintype.card_of_bijective hbij
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe] at this
    rw [← this]
    ring
  · intro s
    obtain ⟨⟨⟨t, ht⟩, ⟨k, hk⟩⟩, hEq⟩ := hbij.2 s
    exact ⟨t, ht, k, hk, hEq⟩

end Transversal

end GaloisForLFunctions.HTGeometry
