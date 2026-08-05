import GaloisForLFunctions.HTGeometry.KleinGordonFloquetDecay

/-!
# The Floquet trichotomy

The pieces built so far say what each Floquet multiplier does. Collecting them at the level of the
spectral radius gives the classical trichotomy for a periodically driven clock:

* `spectralRadius M < 1` — every solution decays to zero;
* `spectralRadius M > 1` — some solution is unbounded in time;
* the clock is stable only if `spectralRadius M ≤ 1`.

The only new ingredient is the passage between the radius and its multipliers, and it is the
contrapositive in both directions: the radius is the supremum of the moduli, so it is at most one
exactly when all of them are, and it exceeds one only if one of them does.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology ENNReal

/-! ## The radius and its multipliers -/

section BanachAlgebra

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]

/-- The spectral radius is at most one exactly when all the spectral values are. -/
theorem spectralRadius_le_one_of_forall {a : A} (h : ∀ k ∈ spectrum ℂ a, ‖k‖ ≤ 1) :
    spectralRadius ℂ a ≤ 1 := by
  show (⨆ k ∈ spectrum ℂ a, (‖k‖₊ : ℝ≥0∞)) ≤ 1
  refine iSup₂_le fun k hk => ?_
  have h1 : ‖k‖ ≤ 1 := h k hk
  have h2 : ‖k‖₊ ≤ 1 := by exact_mod_cast h1
  exact_mod_cast h2

/-- A spectral radius greater than one is witnessed by a spectral value. -/
theorem exists_mem_spectrum_one_lt_norm {a : A} (h : 1 < spectralRadius ℂ a) :
    ∃ k ∈ spectrum ℂ a, 1 < ‖k‖ := by
  by_contra hcon
  push Not at hcon
  exact absurd h (not_lt.mpr (spectralRadius_le_one_of_forall hcon))

end BanachAlgebra

/-! ## The trichotomy -/

section Trichotomy

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

variable {W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b T : ℝ}

/-- **A stable clock has spectral radius at most one.** -/
theorem spectralRadius_le_one_of_pow_bound (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x) {C : ℝ}
    (hC : ∀ n : ℕ, ‖kgMonodromy W b hb0 hWb hWs T ^ n‖ ≤ C) :
    spectralRadius ℂ (kgMonodromy W b hb0 hWb hWs T) ≤ 1 :=
  spectralRadius_le_one_of_forall fun _ hk =>
    norm_le_one_of_mem_spectrum_of_pow_bound hb0 hWb hWs hC hk

/-- **A spectral radius greater than one breaks the clock.** -/
theorem exists_unbounded_of_one_lt_spectralRadius (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hper : ∀ r : ℝ, W (r + T) = W r) (hT : 0 < T)
    (hspec : 1 < spectralRadius ℂ (kgMonodromy W b hb0 hWb hWs T)) :
    ∃ g h : Lp ℂ 2 (volume : Measure E), ∀ C : ℝ, ∃ t : ℝ,
      0 ≤ t ∧ C < ‖kgFieldStateT W g h t‖ := by
  obtain ⟨k, hk, hk1⟩ := exists_mem_spectrum_one_lt_norm hspec
  exact exists_unbounded_of_one_lt_norm_spectrum hb0 hWb hWs hper hT hk hk1

/-- **The Floquet trichotomy for a periodically driven clock.** Inside the unit circle every solution
decays; outside it some solution is unbounded; and stability confines the spectrum to the closed
disc. -/
theorem kgFloquet_trichotomy (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hper : ∀ r : ℝ, W (r + T) = W r) (hT : 0 < T) :
    (spectralRadius ℂ (kgMonodromy W b hb0 hWb hWs T) < 1 →
        ∀ g h : Lp ℂ 2 (volume : Measure E),
          Tendsto (fun t : ℝ => kgFieldStateT W g h t) atTop (𝓝 0))
      ∧ (1 < spectralRadius ℂ (kgMonodromy W b hb0 hWb hWs T) →
        ∃ g h : Lp ℂ 2 (volume : Measure E), ∀ C : ℝ, ∃ t : ℝ,
          0 ≤ t ∧ C < ‖kgFieldStateT W g h t‖)
      ∧ ((∃ C : ℝ, ∀ n : ℕ, ‖kgMonodromy W b hb0 hWb hWs T ^ n‖ ≤ C) →
        spectralRadius ℂ (kgMonodromy W b hb0 hWb hWs T) ≤ 1) := by
  refine ⟨fun hlt g h => ?_, fun hgt => ?_, fun hbdd => ?_⟩
  · exact tendsto_kgFieldStateT_zero_of_spectralRadius hb0 hWb hWs hper hT hlt g h
  · exact exists_unbounded_of_one_lt_spectralRadius hb0 hWb hWs hper hT hgt
  · obtain ⟨C, hC⟩ := hbdd
    exact spectralRadius_le_one_of_pow_bound hb0 hWb hWs hC

end Trichotomy

end GaloisForLFunctions.HTGeometry
