import Mathlib.Data.Finset.Interval
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Module.Multilinear.Basic
import Mathlib.Data.Fintype.Perm

/-!
# Polarization of symmetric continuous multilinear maps

The signed finite-difference of the diagonal of an order-`n` multilinear map retains exactly the
surjective slot selections.  For an endomap of `Fin n`, surjectivity is equivalent to being a
permutation.  Consequently a symmetric multilinear map is recovered from its diagonal after
division by `n!`.

This is the all-orders polarization infrastructure used to turn continuous directional jets into
ordinary ordered mixed jets.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The alternating sum over all supersets of `r` vanishes unless `r` is the whole finite type. -/
theorem sum_Icc_neg_one_pow_card_sub
    {α : Type*} [Fintype α] [DecidableEq α] (r : Finset α) :
    (∑ s ∈ Finset.Icc r (Finset.univ : Finset α),
      (-1 : ℂ) ^ (Fintype.card α - s.card)) =
        if r = Finset.univ then 1 else 0 := by
  have hinj : Set.InjOn (fun t : Finset α ↦ r ∪ t)
      ((Finset.univ \ r).powerset : Set (Finset α)) := by
    intro a ha b hb hab
    change r ∪ a = r ∪ b at hab
    rw [Finset.mem_coe, Finset.mem_powerset] at ha hb
    ext x
    constructor
    · intro hxa
      have hxnr : x ∉ r := (Finset.mem_sdiff.mp (ha hxa)).2
      have hxunion : x ∈ r ∪ b := by
        rw [← hab]
        exact Finset.mem_union_right r hxa
      exact (Finset.mem_union.mp hxunion).resolve_left hxnr
    · intro hxb
      have hxnr : x ∉ r := (Finset.mem_sdiff.mp (hb hxb)).2
      have hxunion : x ∈ r ∪ a := by
        rw [hab]
        exact Finset.mem_union_right r hxb
      exact (Finset.mem_union.mp hxunion).resolve_left hxnr
  rw [Finset.Icc_eq_image_powerset (Finset.subset_univ r)]
  rw [Finset.sum_image hinj]
  have hcard (t : Finset α) (ht : t ∈ (Finset.univ \ r).powerset) :
      Fintype.card α - (r ∪ t).card =
        (Finset.univ \ r).card - t.card := by
    have htr : Disjoint r t := by
      exact Finset.disjoint_left.mpr fun x hxr hxt ↦
        (Finset.mem_sdiff.mp (Finset.mem_powerset.mp ht hxt)).2 hxr
    rw [Finset.card_union_of_disjoint htr]
    rw [← Finset.card_univ,
      Finset.card_sdiff_of_subset (Finset.subset_univ r)]
    omega
  trans ∑ t ∈ (Finset.univ \ r).powerset,
      (-1 : ℂ) ^ ((Finset.univ \ r).card - t.card)
  · apply Finset.sum_congr rfl
    intro t ht
    rw [hcard t ht]
  have hsum := Finset.sum_pow_mul_eq_add_pow
    (1 : ℂ) (-1 : ℂ) (Finset.univ \ r)
  by_cases hr : r = Finset.univ
  · subst r
    simp
  · rw [if_neg hr]
    have hc : (Finset.univ \ r : Finset α).Nonempty := by
      rw [Finset.sdiff_nonempty]
      intro hsub
      exact hr (Finset.Subset.antisymm (Finset.subset_univ r) hsub)
    have hcardpos : 0 < (Finset.univ \ r : Finset α).card :=
      Finset.card_pos.mpr hc
    simpa [hcardpos.ne'] using hsum

/-- Expand a diagonal value of a multilinear map as a sum over all slot selections. -/
theorem continuousMultilinearMap_diagonal_sum
    {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℂ E]
    {n : ℕ}
    (B : ContinuousMultilinearMap ℂ (fun _ : Fin n ↦ E) ℂ)
    (dirs : Fin n → E) (s : Finset (Fin n)) :
    B (fun _ ↦ ∑ j ∈ s, dirs j) =
      ∑ r ∈ Fintype.piFinset (fun _ : Fin n ↦ s),
        B (fun i ↦ dirs (r i)) := by
  simpa only using B.map_sum_finset
    (fun _ j ↦ dirs j) (fun _ ↦ s)

/-- Slot selections from a constant finite set are precisely the endomaps whose range lies in
that set. -/
theorem piFinset_const_eq_filter_range
    {n : ℕ} (s : Finset (Fin n)) :
    Fintype.piFinset (fun _ : Fin n ↦ s) =
      (Finset.univ : Finset (Fin n → Fin n)).filter
        (fun r ↦ Finset.univ.image r ⊆ s) := by
  ext r
  simp [Fintype.mem_piFinset, Finset.image_subset_iff]

/-- Inclusion--exclusion in the diagonal polarization sum retains exactly the surjective slot
endomaps.  Symmetry is not used at this stage. -/
theorem continuousMultilinearMap_polarization_sum_eq_surjective
    {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℂ E]
    {n : ℕ}
    (B : ContinuousMultilinearMap ℂ (fun _ : Fin n ↦ E) ℂ)
    (dirs : Fin n → E) :
    (∑ s ∈ (Finset.univ : Finset (Fin n)).powerset,
      (-1 : ℂ) ^ (n - s.card) •
        B (fun _ ↦ ∑ j ∈ s, dirs j)) =
      ∑ r : Fin n → Fin n,
        if Function.Surjective r then B (fun i ↦ dirs (r i)) else 0 := by
  classical
  simp_rw [continuousMultilinearMap_diagonal_sum,
    piFinset_const_eq_filter_range, smul_sum]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  rw [← Finset.sum_filter]
  have hfilter :
      (Finset.univ : Finset (Fin n)).powerset.filter
          (fun s ↦ Finset.univ.image r ⊆ s) =
        Finset.Icc (Finset.univ.image r) Finset.univ := by
    ext s
    simp
  rw [hfilter, ← Finset.sum_smul]
  have hcoeff := sum_Icc_neg_one_pow_card_sub
    (r := Finset.univ.image r)
  simp only [Fintype.card_fin] at hcoeff
  rw [hcoeff]
  have hrange : Finset.univ.image r = (Finset.univ : Finset (Fin n)) ↔
      Function.Surjective r := by
    constructor
    · intro h b
      have hb : b ∈ Finset.univ.image r := by rw [h]; simp
      simpa using hb
    · intro h
      apply Finset.eq_univ_iff_forall.mpr
      intro b
      obtain ⟨a, rfl⟩ := h b
      simp
  by_cases hsurj : Function.Surjective r
  · have himage := hrange.mpr hsurj
    simp [hsurj, himage]
  · have himage : Finset.univ.image r ≠ (Finset.univ : Finset (Fin n)) :=
      fun h ↦ hsurj (hrange.mp h)
    simp [hsurj, himage]

/-- Surjective endomaps of `Fin n` are canonically permutations. -/
noncomputable def surjectiveEndEquivPerm (n : ℕ) :
    {r : Fin n → Fin n // Function.Surjective r} ≃ Equiv.Perm (Fin n) where
  toFun r := Equiv.ofBijective r.1
    ((Fintype.bijective_iff_surjective_and_card r.1).2 ⟨r.2, rfl⟩)
  invFun σ := ⟨σ, σ.surjective⟩
  left_inv r := by
    apply Subtype.ext
    rfl
  right_inv σ := by
    ext x
    rfl

/-- There are exactly `n!` surjective endomaps of `Fin n`. -/
theorem card_surjective_end (n : ℕ) :
    ((Finset.univ : Finset (Fin n → Fin n)).filter Function.Surjective).card =
      n.factorial := by
  rw [← Fintype.card_subtype]
  rw [Fintype.card_congr (surjectiveEndEquivPerm n)]
  simpa using (Fintype.card_perm (α := Fin n))

/-- The unnormalized polarization sum of a symmetric order-`n` multilinear map is `n!` times the
mixed value. -/
theorem continuousMultilinearMap_symmetric_polarization_sum
    {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℂ E]
    {n : ℕ}
    (B : ContinuousMultilinearMap ℂ (fun _ : Fin n ↦ E) ℂ)
    (dirs : Fin n → E)
    (hsymm : ∀ σ : Equiv.Perm (Fin n),
      B (fun i ↦ dirs (σ i)) = B dirs) :
    (∑ s ∈ (Finset.univ : Finset (Fin n)).powerset,
      (-1 : ℂ) ^ (n - s.card) •
        B (fun _ ↦ ∑ j ∈ s, dirs j)) =
      (n.factorial : ℂ) • B dirs := by
  rw [continuousMultilinearMap_polarization_sum_eq_surjective]
  trans ∑ r : Fin n → Fin n,
      if Function.Surjective r then B dirs else 0
  · apply Finset.sum_congr rfl
    intro r hr
    by_cases hsurj : Function.Surjective r
    · let σ : Equiv.Perm (Fin n) := Equiv.ofBijective r
        ((Fintype.bijective_iff_surjective_and_card r).2 ⟨hsurj, rfl⟩)
      simp only [if_pos hsurj]
      simpa [σ] using hsymm σ
    · simp [hsurj]
  · rw [Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const, card_surjective_end]
    simp [nsmul_eq_mul, smul_eq_mul]

/-- **All-orders polarization identity.** A symmetric continuous multilinear map over `ℂ` is
recovered exactly from its diagonal values by the signed finite-difference formula. -/
theorem continuousMultilinearMap_symmetric_polarization
    {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℂ E]
    {n : ℕ}
    (B : ContinuousMultilinearMap ℂ (fun _ : Fin n ↦ E) ℂ)
    (dirs : Fin n → E)
    (hsymm : ∀ σ : Equiv.Perm (Fin n),
      B (fun i ↦ dirs (σ i)) = B dirs) :
    (∑ s ∈ (Finset.univ : Finset (Fin n)).powerset,
      ((-1 : ℂ) ^ (n - s.card) / (n.factorial : ℂ)) •
        B (fun _ ↦ ∑ j ∈ s, dirs j)) =
      B dirs := by
  calc
    _ = (n.factorial : ℂ)⁻¹ •
        (∑ s ∈ (Finset.univ : Finset (Fin n)).powerset,
          (-1 : ℂ) ^ (n - s.card) •
            B (fun _ ↦ ∑ j ∈ s, dirs j)) := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      simp only [div_eq_mul_inv, smul_eq_mul]
      ring
    _ = B dirs := by
      rw [continuousMultilinearMap_symmetric_polarization_sum B dirs hsymm]
      have hfact : (n.factorial : ℂ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero n
      simp only [smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hfact, one_mul]

end

end GaloisForLFunctions.HTGeometry
