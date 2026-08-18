import GaloisForLFunctions.HTGeometry.BohrHullKroneckerHom

/-!
# Realising a character of the frequency group inside the hull

For every finite set of frequencies, a multiplicative unimodular prescription is realised by some
point of the hull.  The sets of points realising a given finite prescription are closed, nonempty,
and directed downwards under union of the finite sets, so compactness of the hull produces a single
point realising the prescription on the whole frequency group.

This is the surjectivity half of the duality between the phase carrier and its frequency group: the
carrier is not merely embedded in the character group of `Γ`, it exhausts it.
-/

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

variable {E : Type*} [NormedAddCommGroup E] {f : ℝ →ᵇ E}

/-- **Every unimodular character of the frequency group is realised by a point of the hull.** -/
theorem exists_bohrHull_char_eq (htb : HasTotallyBoundedOrbit (fun x => f x)) {ω : ℝ → ℂ}
    (hmul : ∀ a b, ω (a + b) = ω a * ω b) (hnorm : ∀ a, ‖ω a‖ = 1) :
    ∃ x : BohrHull f, ∀ γ : ℝ, IsBohrHullFrequency f γ → bohrHullChar f γ x = ω γ := by
  classical
  haveI : CompactSpace (BohrHull f) := compactSpace_bohrHull htb
  set C : Finset ℝ → Set (BohrHull f) := fun F =>
    {x | ∀ γ ∈ F, IsBohrHullFrequency f γ → bohrHullChar f γ x = ω γ} with hCdef
  have hclosed : ∀ F, IsClosed (C F) := by
    intro F
    have hrw : C F = ⋂ γ ∈ F, {x | IsBohrHullFrequency f γ → bohrHullChar f γ x = ω γ} := by
      ext x
      simp [hCdef]
    rw [hrw]
    refine isClosed_biInter fun γ _ => ?_
    by_cases hγ : IsBohrHullFrequency f γ
    · have hset : {x : BohrHull f | IsBohrHullFrequency f γ → bohrHullChar f γ x = ω γ}
          = (bohrHullChar f γ) ⁻¹' {ω γ} := by
        ext x
        simp [hγ]
      rw [hset]
      exact (isClosed_singleton).preimage (continuous_bohrHullChar f γ)
    · have hset : {x : BohrHull f | IsBohrHullFrequency f γ → bohrHullChar f γ x = ω γ}
          = Set.univ := by
        ext x
        simp [hγ]
      rw [hset]
      exact isClosed_univ
  have hne : ∀ F, (C F).Nonempty := by
    intro F
    obtain ⟨x, hx⟩ := exists_bohrHull_char_eq_finset (f := f)
      (F := F.filter (fun γ => IsBohrHullFrequency f γ)) htb
      (fun γ hγ => (Finset.mem_filter.mp hγ).2) hmul hnorm
    exact ⟨x, fun γ hγF hγ => hx γ (Finset.mem_filter.mpr ⟨hγF, hγ⟩)⟩
  have hdir : Directed (· ⊇ ·) C := by
    intro F F'
    refine ⟨F ∪ F', fun x hx γ hγ hfreq => ?_, fun x hx γ hγ hfreq => ?_⟩
    · exact hx γ (Finset.mem_union_left _ hγ) hfreq
    · exact hx γ (Finset.mem_union_right _ hγ) hfreq
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed C hdir hne
    (fun F => (hclosed F).isCompact) hclosed
  refine ⟨x, fun γ hγ => ?_⟩
  exact Set.mem_iInter.mp hx {γ} γ (Finset.mem_singleton_self γ) hγ

end GaloisForLFunctions
