import Mathlib
import GaloisForLFunctions.WindowedLandauTheory.TheBalanceIdentity

/-!
# Thick translates and the sign signal

A class `ρ` is *thick* at a translate `u₀ ∈ H` for a set `T₂ ⊆ H` when `ρ = ((0,1), s + u₀)` with
`s ∈ T₂`. The partner of a non-split class `g` at height `t` is thick at `u₀` exactly when
`g = ((1,0), h)` and `h + t - u₀ ∈ T₂`, so averaging over all translates replaces the thick indicator by
the density `|T₂|/|H|` on the coset `((1,0), H)` (`average_sum_thick`).

Summed over that coset, characters see only the *sign characters*, those trivial on `{0} × H`
(`sum_coset_conj`); there are at most four (`card_signCharacters_le`), one of them trivial. The
resulting *sign signal* `Σ_{ψ sign} conj ψ((1,0),0) · G_ψ(y)` is `G_ζ(y)` plus three twisted terms.
-/

open Finset

namespace WindowedLandauTheory

noncomputable section

section Thick

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

/-- `ρ` is thick at `u₀` for `T₂`: `ρ = ((0,1), s + u₀)` with `s ∈ T₂`. -/
def IsThick (T₂ : Finset H) (u₀ : H) (ρ : SignPair × H) : Prop :=
  ρ.1 = (0, 1) ∧ ρ.2 - u₀ ∈ T₂

instance (T₂ : Finset H) (u₀ : H) : DecidablePred (IsThick T₂ u₀) := fun ρ =>
  inferInstanceAs (Decidable (ρ.1 = (0, 1) ∧ ρ.2 - u₀ ∈ T₂))

omit [Fintype H] [DecidableEq H] in
/-- The non-split classes whose partner is thick at `u₀`. -/
theorem isThick_partnerClass_iff (T₂ : Finset H) (u₀ t : H) (g : SignPair × H) :
    IsThick T₂ u₀ (partnerClass t g) ↔ g.1 = (1, 0) ∧ g.2 + t - u₀ ∈ T₂ := by
  have h1 : (partnerClass t g).1 = (1, 1) + g.1 := by
    simp [partnerClass, conjClass, heightClass]
  have h2 : (partnerClass t g).2 = g.2 + t := by
    simp [partnerClass, conjClass, heightClass]
  unfold IsThick
  rw [h1, h2]
  constructor
  · rintro ⟨h, hm⟩
    refine ⟨?_, hm⟩
    have := congrArg (fun z : SignPair => z - (1, 1)) h
    simp only [add_sub_cancel_left] at this
    rw [this]
    decide
  · rintro ⟨h, hm⟩
    refine ⟨?_, hm⟩
    rw [h]
    decide

/-- **Averaging over translates.** The thick indicator averages to the density of `T₂` on the coset
`((1,0), H)`. -/
theorem average_sum_thick (T₂ : Finset H) (t : H) (F : SignPair × H → ℂ) :
    (1 / (Fintype.card H : ℂ)) * ∑ u₀ : H, ∑ g ∈ (nonsplitSet H).filter
        (fun g => IsThick T₂ u₀ (partnerClass t g)), F g =
      ((T₂.card : ℂ) / (Fintype.card H : ℂ)) * ∑ h : H, F (((1, 0), h)) := by
  have hH : (Fintype.card H : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  -- swap the sums and count translates
  have e1 : ∑ u₀ : H, ∑ g ∈ (nonsplitSet H).filter (fun g => IsThick T₂ u₀ (partnerClass t g)),
      F g = ∑ g ∈ nonsplitSet H, ∑ u₀ : H,
        (if IsThick T₂ u₀ (partnerClass t g) then F g else 0) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun g _ => by rw [Finset.sum_filter]
  have e2 : ∀ g ∈ nonsplitSet H, ∑ u₀ : H,
      (if IsThick T₂ u₀ (partnerClass t g) then F g else 0) =
      if g.1 = (1, 0) then (T₂.card : ℂ) * F g else 0 := by
    intro g _
    simp_rw [isThick_partnerClass_iff]
    by_cases hg : g.1 = (1, 0)
    · simp only [hg, true_and, if_true]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      congr 1
      have hc : (univ.filter fun u₀ : H => g.2 + t - u₀ ∈ T₂).card = T₂.card := by
        refine Finset.card_bij (fun u₀ _ => g.2 + t - u₀) ?_ ?_ ?_
        · intro u₀ hu
          exact (Finset.mem_filter.1 hu).2
        · intro u₁ _ u₂ _ h
          have := congrArg (fun z => g.2 + t - z) h
          simpa using this
        · intro s hs
          exact ⟨g.2 + t - s, by simp [hs], by abel⟩
      exact_mod_cast hc
    · simp [hg]
  rw [e1, Finset.sum_congr rfl e2, ← Finset.sum_filter]
  -- the coset ((1,0), H) inside the non-split classes
  have e3 : ∑ g ∈ (nonsplitSet H).filter (fun g => g.1 = (1, 0)), (T₂.card : ℂ) * F g =
      (T₂.card : ℂ) * ∑ h : H, F (((1, 0), h)) := by
    rw [← Finset.mul_sum]
    congr 1
    refine Finset.sum_nbij' (fun g => g.2) (fun h => ((1, 0), h)) ?_ ?_ ?_ ?_ ?_
    · intro g _
      exact Finset.mem_coe.2 (Finset.mem_univ _)
    · intro h _
      have hn : ¬IsSplit (((1, 0), h) : SignPair × H) := by
        rw [not_isSplit_iff]
      simp [nonsplitSet, hn]
    · intro g hg
      have hg1 : g.1 = (1, 0) := (Finset.mem_filter.1 (Finset.mem_coe.1 hg)).2
      exact Prod.ext hg1.symm rfl
    · intro h _
      rfl
    · intro g hg
      have hg1 : g.1 = (1, 0) := (Finset.mem_filter.1 (Finset.mem_coe.1 hg)).2
      rw [show (((1, 0), g.2) : SignPair × H) = g from Prod.ext hg1.symm rfl]
  rw [e3]
  field_simp

/-! ## Sign characters -/

/-- A sign character is trivial on `{0} × H`. -/
def IsSignCharacter (ψ : AddChar (SignPair × H) ℂ) : Prop := ∀ h : H, ψ ((0, 0), h) = 1

omit [DecidableEq H] in
open Classical in
/-- Summing a character over the coset `((1,0), H)` sees only sign characters. -/
theorem sum_coset_conj (ψ : AddChar (SignPair × H) ℂ) :
    ∑ h : H, starRingEnd ℂ (ψ ((1, 0), h)) =
      if IsSignCharacter ψ then (Fintype.card H : ℂ) * starRingEnd ℂ (ψ ramifiedClass) else 0 := by
  let φ : AddChar H ℂ := ψ.compAddMonoidHom (AddMonoidHom.inr SignPair H)
  have hφ : ∀ h, φ h = ψ ((0, 0), h) := fun h => rfl
  have hsplit : ∀ h : H, ψ ((1, 0), h) = ψ ramifiedClass * φ h := by
    intro h
    rw [hφ, ← AddChar.map_add_eq_mul]
    congr 1
    simp [ramifiedClass]
  simp_rw [hsplit, map_mul]
  rw [← Finset.mul_sum]
  have hsum : ∑ h : H, starRingEnd ℂ (φ h) = if φ = 0 then (Fintype.card H : ℂ) else 0 := by
    simp_rw [← AddChar.map_neg_eq_conj]
    rw [Fintype.sum_equiv (Equiv.neg H) (fun h => φ (-h)) (fun h => φ h) (fun h => rfl),
      AddChar.sum_eq_ite]
  have hiff : φ = 0 ↔ IsSignCharacter ψ := by
    constructor
    · intro h0 h
      rw [← hφ, h0, AddChar.zero_apply]
    · intro hs
      ext h
      rw [hφ, hs h, AddChar.zero_apply]
  rw [hsum]
  by_cases hs : IsSignCharacter ψ
  · rw [if_pos (hiff.2 hs), if_pos hs]
    ring
  · rw [if_neg (fun h => hs (hiff.1 h)), if_neg hs, mul_zero]

omit [Fintype H] [DecidableEq H] in
theorem isSignCharacter_zero : IsSignCharacter (0 : AddChar (SignPair × H) ℂ) :=
  fun _ => AddChar.zero_apply _

omit [DecidableEq H] in
open Classical in
/-- At most four sign characters: restriction to `SignPair × {0}` is injective on them. -/
theorem card_signCharacters_le :
    ((univ : Finset (AddChar (SignPair × H) ℂ)).filter IsSignCharacter).card ≤ 4 := by
  let res : AddChar (SignPair × H) ℂ → AddChar SignPair ℂ :=
    fun ψ => ψ.compAddMonoidHom (AddMonoidHom.inl SignPair H)
  have hinj : Set.InjOn res ((univ : Finset (AddChar (SignPair × H) ℂ)).filter IsSignCharacter) := by
    intro ψ hψ φ hφ hres
    have hψ' : IsSignCharacter ψ := (Finset.mem_filter.1 (Finset.mem_coe.1 hψ)).2
    have hφ' : IsSignCharacter φ := (Finset.mem_filter.1 (Finset.mem_coe.1 hφ)).2
    ext g
    have hg : g = (g.1, 0) + ((0, 0), g.2) := by ext <;> simp
    have h1 : ψ (g.1, 0) = φ (g.1, 0) := by
      have := congrArg (fun χ : AddChar SignPair ℂ => χ g.1) hres
      simpa [res] using this
    rw [hg, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, hψ' g.2, hφ' g.2, h1]
  have h := Finset.card_le_card_of_injOn res (fun _ _ => Finset.mem_univ _) hinj
  rw [Finset.card_univ, AddChar.card_eq] at h
  simpa using h

end Thick

end

end WindowedLandauTheory
