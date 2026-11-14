import GaloisForLFunctions.GaloisTheoryOfZeros.TheForwardMonodromyDeterminesTheReflectionAndTheConjugationOfTheZeros

/-!
# The reflection is the only symmetry of the heat cover over the forward times

`forwardCover` is the set of the points `(τ, z)` with `H_τ(z) = 0` over the forward times `τ` off
the branch times.

* **Deck maps** (`eq_snd_or_eq_neg_snd_of_continuousOn_forwardCover`). A continuous map `f` of
  the forward cover that carries every zero of `H_τ` to a zero of `H_τ` is `z` at every point or
  `−z` at every point: the functional equation is the only symmetry of the cover over its base.
  The map need not be injective, holomorphic, or defined off the cover.
* **Mirror maps** (`eq_conj_or_eq_neg_conj_of_continuousOn_forwardCover`). A continuous map that
  carries every zero of `H_τ` to a zero of `H_τ̄` is `z̄` at every point or `−z̄` at every point:
  the cover has one real structure up to the reflection.
* **No section** (`exists_complexHeat_ne_zero_of_continuousOn`). No zero is a continuous function
  of the forward time off the branch times.

Proof. A continuous map of the cover over its base carries lifts of a path to lifts
(`Transports.map_forwardCover`). On a fibre it therefore commutes with the forward monodromy
group, so it is the identity or the reflection of that fibre, and transport along a path carries
the case of one fibre to every other fibre. A section is a constant deck map on each fibre, and
the fibres are infinite.
-/

open Complex Set
open RHTower Equiv

namespace GaloisForLFunctions.GaloisTheoryOfZeros

set_option autoImplicit false

/-- The heat cover over the forward times off the branch times. -/
def forwardCover : Set (ℂ × ℂ) :=
  {x | 0 < x.1.re ∧ x.1 ∉ branchTimes ∧ complexHeat x.1 x.2 = 0}

variable {f : ℂ × ℂ → ℂ}

/-- **A continuous map of the cover over its base carries lifts to lifts.** -/
theorem Transports.map_forwardCover (hf : ContinuousOn f forwardCover)
    (hzero : ∀ x ∈ forwardCover, complexHeat x.1 (f x) = 0) {γ : ℝ → ℂ} (hγ : IsForwardPath γ)
    {z w : ℂ} (h : Transports γ z w) : Transports γ (f (γ 0, z)) (f (γ 1, w)) := by
  obtain ⟨u, hu, rfl, rfl⟩ := h
  have hmem : ∀ s ∈ Icc (0 : ℝ) 1, (γ s, u s) ∈ forwardCover := fun s hs =>
    ⟨hγ.re_pos s hs, hγ.simple s hs, hu.zero s hs⟩
  exact ⟨fun s => f (γ s, u s),
    ⟨hf.comp (hγ.continuousOn.prodMk hu.continuousOn) hmem, fun s hs => hzero (γ s, u s) (hmem s hs)⟩,
    rfl, rfl⟩

/-- On one fibre a deck map is the identity or the reflection. -/
theorem forall_eq_or_forall_eq_neg_of_continuousOn_forwardCover (hf : ContinuousOn f forwardCover)
    (hzero : ∀ x ∈ forwardCover, complexHeat x.1 (f x) = 0) {b : ℂ} (hb₀ : 0 < b.re)
    (hb : b ∉ branchTimes) :
    (∀ z, complexHeat b z = 0 → f (b, z) = z) ∨ ∀ z, complexHeat b z = 0 → f (b, z) = -z := by
  obtain ⟨P, hP, hG⟩ := exists_pairCoordinate_isWindowedSignedGroup hb₀ hb
  -- the map of the fibre
  obtain ⟨σ, hσ⟩ : ∃ σ : {z : ℂ // complexHeat b z = 0} → {z : ℂ // complexHeat b z = 0},
      ∀ p, (σ p).1 = f (b, p.1) :=
    ⟨fun p => ⟨f (b, p.1), hzero (b, p.1) ⟨hb₀, hb, p.2⟩⟩, fun _ => rfl⟩
  -- it commutes with the forward monodromy
  have hcomm : ∀ g ∈ forwardMonodromy b hb₀ hb, ∀ p, σ (g p) = g (σ p) := by
    rintro g ⟨γ, hγ, h0, h1, hg⟩ p
    have h := (hg p).map_forwardCover hf hzero hγ
    rw [h0, h1, ← hσ p, ← hσ (g p)] at h
    exact Subtype.ext (hγ.transports_unique h (hg (σ p)))
  rcases hG.eq_self_or_eq_flip_of_commute (σ := σ) hcomm with h | h
  · exact Or.inl fun z hz =>
      (hσ ⟨z, hz⟩).symm.trans (congrArg Subtype.val (h ⟨z, hz⟩))
  · exact Or.inr fun z hz =>
      (hσ ⟨z, hz⟩).symm.trans (congrArg Subtype.val ((h ⟨z, hz⟩).trans (hP ⟨z, hz⟩)))

/-- **The deck maps of the forward cover are the identity and the reflection.** A continuous map
of the forward cover that carries every zero of `H_τ` to a zero of `H_τ` is `z` at every point
or `−z` at every point. -/
theorem eq_snd_or_eq_neg_snd_of_continuousOn_forwardCover (hf : ContinuousOn f forwardCover)
    (hzero : ∀ x ∈ forwardCover, complexHeat x.1 (f x) = 0) :
    (∀ x ∈ forwardCover, f x = x.2) ∨ ∀ x ∈ forwardCover, f x = -x.2 := by
  have h8₀ : 0 < (((1 / 8 : ℝ) : ℂ)).re := by
    rw [Complex.ofReal_re]
    norm_num
  have h8 : ((1 / 8 : ℝ) : ℂ) ∉ branchTimes := ofReal_not_mem_branchTimes_of_eighth_le le_rfl
  -- every point of the cover is the transport of a zero over the time `1/8`
  have hsrc : ∀ x ∈ forwardCover, ∃ δ, IsForwardPath δ ∧ δ 0 = ((1 / 8 : ℝ) : ℂ) ∧ δ 1 = x.1 ∧
      ∃ p : ℂ, complexHeat ((1 / 8 : ℝ) : ℂ) p = 0 ∧ Transports δ p x.2 := by
    rintro ⟨τ, z⟩ ⟨hτ, hτb, hz⟩
    obtain ⟨δ, hδ, h0, h1⟩ := exists_isForwardPath h8₀ hτ h8 hτb
    obtain ⟨e, he⟩ := hδ.exists_fibreEquiv h0 h1
    have h := he (e.symm ⟨z, hz⟩)
    rw [e.apply_symm_apply] at h
    exact ⟨δ, hδ, h0, h1, _, (e.symm ⟨z, hz⟩).2, h⟩
  rcases forall_eq_or_forall_eq_neg_of_continuousOn_forwardCover hf hzero h8₀ h8 with h | h
  · refine Or.inl fun x hx => ?_
    obtain ⟨δ, hδ, h0, h1, p, hp, hT⟩ := hsrc x hx
    have hT' := hT.map_forwardCover hf hzero hδ
    rw [h0, h1, h p hp] at hT'
    exact hδ.transports_unique hT' hT
  · refine Or.inr fun x hx => ?_
    obtain ⟨δ, hδ, h0, h1, p, hp, hT⟩ := hsrc x hx
    have hT' := hT.map_forwardCover hf hzero hδ
    rw [h0, h1, h p hp] at hT'
    exact hδ.transports_unique hT' hT.neg

/-- **The mirror maps of the forward cover are the conjugation and the reflected conjugation.** A
continuous map of the forward cover that carries every zero of `H_τ` to a zero of `H_τ̄` is `z̄`
at every point or `−z̄` at every point. -/
theorem eq_conj_or_eq_neg_conj_of_continuousOn_forwardCover (hf : ContinuousOn f forwardCover)
    (hzero : ∀ x ∈ forwardCover, complexHeat (starRingEnd ℂ x.1) (f x) = 0) :
    (∀ x ∈ forwardCover, f x = starRingEnd ℂ x.2) ∨
      ∀ x ∈ forwardCover, f x = -starRingEnd ℂ x.2 := by
  have hzero' : ∀ x ∈ forwardCover, complexHeat x.1 (starRingEnd ℂ (f x)) = 0 := by
    intro x hx
    have e : complexHeat x.1 (starRingEnd ℂ (f x)) =
        starRingEnd ℂ (complexHeat (starRingEnd ℂ x.1) (f x)) := by
      rw [complexHeat_conj, Complex.conj_conj]
    rw [e, hzero x hx, map_zero]
  rcases eq_snd_or_eq_neg_snd_of_continuousOn_forwardCover
    (f := fun x => starRingEnd ℂ (f x)) (Complex.continuous_conj.comp_continuousOn hf) hzero'
    with h | h
  · refine Or.inl fun x hx => ?_
    rw [← Complex.conj_conj (f x), h x hx]
  · refine Or.inr fun x hx => ?_
    rw [← Complex.conj_conj (f x), h x hx, map_neg]

/-- **No zero is a continuous function of the forward time.** For every function `Z` that is
continuous on the forward times off the branch times, `Z(τ)` is not a zero of `H_τ` for some
such time. -/
theorem exists_complexHeat_ne_zero_of_continuousOn {Z : ℂ → ℂ}
    (hZ : ContinuousOn Z {τ : ℂ | 0 < τ.re ∧ τ ∉ branchTimes}) :
    ∃ τ : ℂ, 0 < τ.re ∧ τ ∉ branchTimes ∧ complexHeat τ (Z τ) ≠ 0 := by
  by_contra hcon
  have hall : ∀ τ : ℂ, 0 < τ.re → τ ∉ branchTimes → complexHeat τ (Z τ) = 0 := by
    intro τ hτ hb
    by_contra h
    exact hcon ⟨τ, hτ, hb, h⟩
  -- the section is a deck map that is constant on every fibre
  have hf : ContinuousOn (fun x : ℂ × ℂ => Z x.1) forwardCover :=
    hZ.comp continuous_fst.continuousOn fun x hx => ⟨hx.1, hx.2.1⟩
  have h8₀ : 0 < (((1 / 8 : ℝ) : ℂ)).re := by
    rw [Complex.ofReal_re]
    norm_num
  have h8 : ((1 / 8 : ℝ) : ℂ) ∉ branchTimes := ofReal_not_mem_branchTimes_of_eighth_le le_rfl
  have hinf := infinite_fibre h8₀ h8
  -- three distinct zeros over the time `1/8`
  obtain ⟨p, q, hpq⟩ := exists_pair_ne {z : ℂ // complexHeat ((1 / 8 : ℝ) : ℂ) z = 0}
  obtain ⟨s, hsp, hsq⟩ : ∃ s : {z : ℂ // complexHeat ((1 / 8 : ℝ) : ℂ) z = 0}, s ≠ p ∧ s ≠ q := by
    obtain ⟨s, hs⟩ := Infinite.exists_notMem_finset ({p, q} : Finset _)
    rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hs
    exact ⟨s, hs.1, hs.2⟩
  have hval : ∀ x : {z : ℂ // complexHeat ((1 / 8 : ℝ) : ℂ) z = 0},
      x.1 = Z ((1 / 8 : ℝ) : ℂ) ∨ x.1 = -Z ((1 / 8 : ℝ) : ℂ) := by
    intro x
    rcases eq_snd_or_eq_neg_snd_of_continuousOn_forwardCover hf
      (fun y hy => hall y.1 hy.1 hy.2.1) with h | h
    · exact Or.inl (h (((1 / 8 : ℝ) : ℂ), x.1) ⟨h8₀, h8, x.2⟩).symm
    · refine Or.inr ?_
      have e := h (((1 / 8 : ℝ) : ℂ), x.1) ⟨h8₀, h8, x.2⟩
      have e' : Z ((1 / 8 : ℝ) : ℂ) = -x.1 := e
      rw [e', neg_neg]
  -- three zeros among two values
  rcases hval p with hp | hp <;> rcases hval q with hq | hq <;> rcases hval s with hs | hs
  · exact hpq (Subtype.ext (hp.trans hq.symm))
  · exact hpq (Subtype.ext (hp.trans hq.symm))
  · exact hsp (Subtype.ext (hs.trans hp.symm))
  · exact hsq (Subtype.ext (hs.trans hq.symm))
  · exact hsq (Subtype.ext (hs.trans hq.symm))
  · exact hsp (Subtype.ext (hs.trans hp.symm))
  · exact hpq (Subtype.ext (hp.trans hq.symm))
  · exact hpq (Subtype.ext (hp.trans hq.symm))

end GaloisForLFunctions.GaloisTheoryOfZeros
