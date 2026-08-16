import GaloisForLFunctions.RHTower.XiMassShellModulusLaw

/-!
# The prime index sets of a moving annulus

The finite true-prime cone at slope `κ` is indexed by

`Pset M = {k : k + 2 ≤ M, k + 2 prime}`,  `M = ⌊e^{κu}⌋₊`,

and the annulus between two slopes is the set difference of two such sets.  This file records the
elementary Finset algebra: nesting, the two-step split of a difference, and the identification of
the innermost shell with the difference of two Chebyshev `θ` values.
-/

open Complex Filter Finset MeasureTheory Set Topology

namespace RHTower

noncomputable section

/-- The prime index set of a finite cone. -/
def conePrimeIndex (M : ℕ) : Finset ℕ :=
  (Finset.range (M - 1)).filter (fun k => Nat.Prime (k + 2))

theorem mem_conePrimeIndex {M k : ℕ} :
    k ∈ conePrimeIndex M ↔ k + 2 ≤ M ∧ Nat.Prime (k + 2) := by
  classical
  rw [conePrimeIndex, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by omega, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by omega, h2⟩

theorem conePrimeIndex_subset {M N : ℕ} (h : M ≤ N) :
    conePrimeIndex M ⊆ conePrimeIndex N := by
  intro k hk
  rw [mem_conePrimeIndex] at hk ⊢
  exact ⟨le_trans hk.1 h, hk.2⟩

/-- The two-step split of an annulus. -/
theorem conePrimeIndex_sdiff_split {M₀ M₁ M₂ : ℕ} (h01 : M₀ ≤ M₁) (h12 : M₁ ≤ M₂)
    {f : ℕ → ℝ} :
    ∑ k ∈ conePrimeIndex M₂ \ conePrimeIndex M₀, f k
      = ∑ k ∈ conePrimeIndex M₁ \ conePrimeIndex M₀, f k
        + ∑ k ∈ conePrimeIndex M₂ \ conePrimeIndex M₁, f k := by
  classical
  have hsub : conePrimeIndex M₁ \ conePrimeIndex M₀ ⊆ conePrimeIndex M₂ \ conePrimeIndex M₀ := by
    intro k hk
    rw [Finset.mem_sdiff] at hk ⊢
    exact ⟨conePrimeIndex_subset h12 hk.1, hk.2⟩
  have hcompl : (conePrimeIndex M₂ \ conePrimeIndex M₀) \
      (conePrimeIndex M₁ \ conePrimeIndex M₀) = conePrimeIndex M₂ \ conePrimeIndex M₁ := by
    ext k
    simp only [Finset.mem_sdiff, mem_conePrimeIndex]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, ?_⟩
      intro hcon
      exact h3 ⟨hcon, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨⟨h1, ?_⟩, ?_⟩
      · intro hcon
        exact h2 ⟨le_trans hcon.1 h01, hcon.2⟩
      · intro hcon
        exact h2 hcon.1
  have := Finset.sum_sdiff (f := f) hsub
  rw [hcompl] at this
  linarith [this]

/-- The innermost shell index set maps onto the primes of a half-open interval. -/
theorem sum_conePrimeIndex_sdiff_eq {M₀ M₁ : ℕ} {g : ℕ → ℝ} :
    ∑ k ∈ conePrimeIndex M₁ \ conePrimeIndex M₀, g (k + 2)
      = ∑ p ∈ (Finset.Ioc M₀ M₁).filter (fun p => Nat.Prime p), g p := by
  classical
  have hinj : ∀ x ∈ conePrimeIndex M₁ \ conePrimeIndex M₀,
      ∀ y ∈ conePrimeIndex M₁ \ conePrimeIndex M₀, x + 2 = y + 2 → x = y := by
    intro x _ y _ hxy
    omega
  have himage : (conePrimeIndex M₁ \ conePrimeIndex M₀).image (fun k => k + 2)
      = (Finset.Ioc M₀ M₁).filter (fun p => Nat.Prime p) := by
    ext p
    simp only [Finset.mem_image, Finset.mem_sdiff, mem_conePrimeIndex, Finset.mem_filter,
      Finset.mem_Ioc]
    constructor
    · rintro ⟨k, ⟨⟨h1, h2⟩, h3⟩, rfl⟩
      refine ⟨⟨?_, h1⟩, h2⟩
      by_contra hcon
      exact h3 ⟨by omega, h2⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨p - 2, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · have := h3.two_le
        omega
      · have := h3.two_le
        have : p - 2 + 2 = p := by omega
        rw [this]
        exact h3
      · intro hcon
        have hp2 := h3.two_le
        have : p - 2 + 2 = p := by omega
        rw [this] at hcon
        omega
      · have := h3.two_le
        omega
  rw [← himage, Finset.sum_image hinj]

end

end RHTower
