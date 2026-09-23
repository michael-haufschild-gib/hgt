import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicRamareLadderMass

/-!
# The mass split without a prime-gap hypothesis

`setIntegral_normSq_harmonicRamareBilinear_le_blocks_mass` divides by each block's harmonic mass,
so as stated it needs every block of the ladder to be nonempty.  Along Menon's schedule the blocks
have ratio `1 + (log x)^{-10}`, so "every block contains a prime" is a prime-gap theorem — an
arithmetic input that has no business being in a Cauchy--Schwarz.

It is also unnecessary: a block with no prime contributes nothing.  This file restricts the split
to the blocks of positive mass, which is automatic, and proves that the cover and the total mass
are unchanged.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- A prime block of zero harmonic mass is empty. -/
theorem eq_empty_of_harmonicPrimeMass_eq_zero {B : Finset ℕ}
    (hBprime : ∀ p ∈ B, p.Prime) (h : harmonicPrimeMass B = 0) : B = ∅ := by
  classical
  by_contra hne
  obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.2 hne
  have hpos : ∀ q ∈ B, (0 : ℝ) ≤ 1 / (q : ℝ) := fun q _ => by positivity
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hpos).1 h p hp
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hBprime p hp).two_le
  have : (0 : ℝ) < 1 / (p : ℝ) := by positivity
  linarith [hzero]

/-- **The mass split over the blocks of positive mass.**  No block is required to contain a
prime. -/
theorem setIntegral_normSq_harmonicRamareBilinear_le_blocks_mass_filter
    {P s : Finset ℕ} {W : ℝ}
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W)
    {ι : Type*} [DecidableEq ι] (I : Finset ι) (B : ι → Finset ℕ)
    (hdisj : (I : Set ι).PairwiseDisjoint B) (hcover : I.biUnion B = P)
    (hBprime : ∀ i ∈ I, ∀ p ∈ B i, p.Prime) :
    (∫ w in E, ‖harmonicRamareBilinear P s w‖ ^ (2 : ℕ))
      ≤ harmonicPrimeMass P *
          ∑ i ∈ I.filter (fun i => 0 < harmonicPrimeMass (B i)),
            (∫ w in E, ‖harmonicRamareBlock P s (B i) w‖ ^ (2 : ℕ))
              / harmonicPrimeMass (B i) := by
  classical
  set I' : Finset ι := I.filter (fun i => 0 < harmonicPrimeMass (B i)) with hI'def
  have hI'sub : I' ⊆ I := Finset.filter_subset _ _
  have hempty : ∀ i ∈ I, i ∉ I' → B i = ∅ := by
    intro i hi hni
    have hnot : ¬ (0 < harmonicPrimeMass (B i)) := by
      intro hpos
      exact hni (Finset.mem_filter.2 ⟨hi, hpos⟩)
    have hnonneg : (0 : ℝ) ≤ harmonicPrimeMass (B i) :=
      Finset.sum_nonneg fun q _ => by positivity
    exact eq_empty_of_harmonicPrimeMass_eq_zero (hBprime i hi) (le_antisymm (not_lt.1 hnot) hnonneg)
  have hdisj' : (I' : Set ι).PairwiseDisjoint B :=
    hdisj.subset (by exact_mod_cast hI'sub)
  have hcover' : I'.biUnion B = P := by
    rw [← hcover]
    ext p
    simp only [Finset.mem_biUnion]
    constructor
    · rintro ⟨i, hi, hp⟩
      exact ⟨i, hI'sub hi, hp⟩
    · rintro ⟨i, hi, hp⟩
      by_cases hmem : i ∈ I'
      · exact ⟨i, hmem, hp⟩
      · exact absurd (hempty i hi hmem ▸ hp) (Finset.notMem_empty p)
  exact setIntegral_normSq_harmonicRamareBilinear_le_blocks_mass hEm hEs I' B hdisj' hcover'
    (fun i hi => (Finset.mem_filter.1 hi).2)

end

end RHTower.Sieve
