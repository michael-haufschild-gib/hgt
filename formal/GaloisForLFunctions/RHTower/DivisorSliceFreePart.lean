import GaloisForLFunctions.RHTower.DivisorSliceFixedPart

/-!
# The free part of a slice, and why every classical invariant misses it

`CANNOT-405` showed that the fixed part of a slice is a subsingleton unconditionally, so the
hypothesis lives entirely in the **free** part.  This module makes the free part concrete.

The reflection sends real part `β` to `1 − β`, so on each slice it exchanges the two open half-slices
`Re < 1/2` and `Re > 1/2` and fixes only `Re = 1/2`.  Hence every slice is the disjoint union of a
subsingleton fixed part and a free part canonically split into two halves exchanged by the
reflection, and

  `RiemannHypothesis ↔ ∀ t, the left half-slice is empty`.

## Why this is the object no classical invariant sees

For a `ℤ/2`-set the Borel equivariant cohomology is `𝔽₂[u]` on each fixed point and `𝔽₂` on each free
orbit, so the free orbits are exactly the `u`-**torsion**.  Inverting `u` — the localization that
produces Tate cohomology, Smith theory, the signature, the index, the Krein inertia, the Witt class,
the spectral flow — kills the torsion by construction (Atiyah–Segal/Quillen localization), leaving
only the fixed part.  That is a theorem, not an accident: **every localized invariant is blind to the
free part**, and the fixed part is the subsingleton of `CANNOT-405`.  So the corpus's universal
blindness has one named cause: every route localizes.  The surviving target is an **unlocalized**
equivariant statement — equivalently, that the action is equivariantly formal, i.e. that the free
part is empty, which is what the left half-slice measures.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- The reflection sends real part `β` to `1 − β`. -/
theorem supportPartner_re (ρ : XiDivisorSupport) :
    ((supportPartner ρ : XiDivisorSupport) : ℂ).re = 1 - (ρ : ℂ).re := by
  rw [supportPartner_coe]
  simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]

/-- The left half-slice: divisor points at height `t` strictly left of the critical line. -/
def xiSliceLeft (t : ℝ) : Set XiDivisorSupport := {ρ | ρ ∈ xiSlice t ∧ (ρ : ℂ).re < 1 / 2}

/-- The right half-slice. -/
def xiSliceRight (t : ℝ) : Set XiDivisorSupport := {ρ | ρ ∈ xiSlice t ∧ 1 / 2 < (ρ : ℂ).re}

theorem xiSliceLeft_subset (t : ℝ) : xiSliceLeft t ⊆ xiSlice t := fun _ h => h.1
theorem xiSliceRight_subset (t : ℝ) : xiSliceRight t ⊆ xiSlice t := fun _ h => h.1

/-- **Trichotomy.**  Every point of a slice is left of, on, or right of the critical line. -/
theorem xiSlice_eq_union (t : ℝ) :
    xiSlice t = xiSliceLeft t ∪ xiSliceFixed t ∪ xiSliceRight t := by
  apply Set.eq_of_subset_of_subset
  · intro ρ hρ
    rcases lt_trichotomy ((ρ : ℂ).re) (1 / 2) with h | h | h
    · exact Or.inl (Or.inl ⟨hρ, h⟩)
    · exact Or.inl (Or.inr ⟨hρ, (supportPartner_eq_self_iff ρ).mpr h⟩)
    · exact Or.inr ⟨hρ, h⟩
  · rintro ρ ((h | h) | h)
    · exact h.1
    · exact h.1
    · exact h.1

/-- The reflection carries the left half-slice into the right half-slice. -/
theorem supportPartner_mapsTo_left {t : ℝ} {ρ : XiDivisorSupport} (h : ρ ∈ xiSliceLeft t) :
    supportPartner ρ ∈ xiSliceRight t := by
  refine ⟨supportPartner_mem_xiSlice h.1, ?_⟩
  rw [supportPartner_re]
  have := h.2
  linarith

/-- The reflection carries the right half-slice into the left half-slice. -/
theorem supportPartner_mapsTo_right {t : ℝ} {ρ : XiDivisorSupport} (h : ρ ∈ xiSliceRight t) :
    supportPartner ρ ∈ xiSliceLeft t := by
  refine ⟨supportPartner_mem_xiSlice h.1, ?_⟩
  rw [supportPartner_re]
  have := h.2
  linarith

/-- **The two halves of the free part are exchanged by the reflection.** -/
theorem xiSliceRight_eq_image (t : ℝ) :
    xiSliceRight t = supportPartner '' (xiSliceLeft t) := by
  apply Set.eq_of_subset_of_subset
  · intro ρ hρ
    exact ⟨supportPartner ρ, supportPartner_mapsTo_right hρ, supportPartner_involutive ρ⟩
  · rintro ρ ⟨σ, hσ, rfl⟩
    exact supportPartner_mapsTo_left hσ

/-- **The hypothesis is the emptiness of every left half-slice** — the vanishing of the free part. -/
theorem riemannHypothesis_iff_xiSliceLeft_empty :
    RiemannHypothesis ↔ ∀ t : ℝ, xiSliceLeft t = ∅ := by
  rw [riemannHypothesis_iff_supportPartner_eq_id]
  constructor
  · intro h t
    apply Set.eq_empty_of_forall_notMem
    intro ρ hρ
    have hre : (ρ : ℂ).re = 1 / 2 := (supportPartner_eq_self_iff ρ).mp (h ρ)
    have := hρ.2
    linarith
  · intro h ρ
    by_contra hne
    have hre : (ρ : ℂ).re ≠ 1 / 2 := fun hc => hne ((supportPartner_eq_self_iff ρ).mpr hc)
    rcases lt_or_gt_of_ne hre with hlt | hgt
    · exact absurd (h ((ρ : ℂ).im) ▸ (⟨self_mem_xiSlice ρ, hlt⟩ : ρ ∈ xiSliceLeft ((ρ : ℂ).im)))
        (Set.notMem_empty ρ)
    · have : supportPartner ρ ∈ xiSliceLeft ((ρ : ℂ).im) :=
        supportPartner_mapsTo_right ⟨self_mem_xiSlice ρ, hgt⟩
      exact absurd (h ((ρ : ℂ).im) ▸ this) (Set.notMem_empty _)

/-- Failure of the hypothesis produces a divisor point strictly left of the critical line, at a
height whose slice therefore has a genuinely free orbit. -/
theorem exists_xiSliceLeft_nonempty_of_not_riemannHypothesis (h : ¬ RiemannHypothesis) :
    ∃ t : ℝ, (xiSliceLeft t).Nonempty := by
  by_contra hc
  push Not at hc
  exact h (riemannHypothesis_iff_xiSliceLeft_empty.mpr hc)

end

end RHTower
