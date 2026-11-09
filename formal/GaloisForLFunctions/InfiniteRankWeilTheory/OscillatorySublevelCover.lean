import GaloisForLFunctions.InfiniteRankWeilTheory.FiniteJetSublevelCover
import GaloisForLFunctions.InfiniteRankWeilTheory.UniformOscillatoryJets

/-!
# Uniform finite covers of oscillatory sublevel sets

For a nonzero sum of `k` distinct real frequencies, every fixed-radius window has a uniformly
nonzero derivative of order less than `k`. Its small values admit a cover by at most `k` balls
whose radii are bounded by a common constant times the `k`-th root of the threshold.
-/

open Set Finset

noncomputable section

namespace GaloisForLFunctions.InfiniteRankWeilTheory

/-- Uniform finite covers control the geometry, rather than only the measure, of small values
of a nonzero finite oscillatory sum. -/
theorem exists_uniform_oscillatory_sublevel_cover {k : ℕ} (γ : Fin k → ℝ)
    (hγ : Function.Injective γ) (c : Fin k → ℂ) (hc : c ≠ 0) :
    ∃ r K : ℝ, 0 < r ∧ 0 < K ∧ ∀ x ε : ℝ, 0 < ε →
      ∃ T : Finset ℝ, T.card ≤ k ∧ ∀ y ∈ Ioo (x - r) (x + r),
        ‖oscillatoryJet γ c 0 y‖ < ε → ∃ z ∈ T, |y - z| ≤ K * ε ^ ((k : ℝ)⁻¹) := by
  classical
  obtain ⟨r, A, hr, hA, hwindow⟩ := exists_uniform_oscillatoryJet_window γ hγ c hc
  have hk : 0 < k := by
    obtain ⟨m, _⟩ := hwindow 0
    exact Nat.zero_lt_of_lt m.isLt
  let D : ℝ := ∑ m ∈ range k, derivativeCoverConstant m A
  have hD : 0 ≤ D := sum_nonneg fun m _ => (derivativeCoverConstant_pos m hA).le
  let K : ℝ := D + r + r / A + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hKr : r ≤ K := by dsimp [K]; linarith only [hD, div_nonneg hr.le hA.le]
  have hKA : r / A ≤ K := by dsimp [K]; linarith only [hD, hr]
  have hKD (m : ℕ) (hm : m < k) : derivativeCoverConstant m A ≤ K := by
    have hmD : derivativeCoverConstant m A ≤ D :=
      single_le_sum (fun j _ => (derivativeCoverConstant_pos j hA).le) (mem_range.mpr hm)
    dsimp [K]
    linarith only [hmD, hr, div_nonneg hr.le hA.le]
  refine ⟨r, K, hr, hK, fun x ε hε => ?_⟩
  have hone (hrad : r ≤ K * ε ^ ((k : ℝ)⁻¹)) :
      ∃ T : Finset ℝ, T.card ≤ k ∧ ∀ y ∈ Ioo (x - r) (x + r),
        ‖oscillatoryJet γ c 0 y‖ < ε → ∃ z ∈ T, |y - z| ≤ K * ε ^ ((k : ℝ)⁻¹) := by
    refine ⟨{x}, by rw [Finset.card_singleton]; exact hk,
      fun y hy _ => ⟨x, mem_singleton_self x, ?_⟩⟩
    exact (abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩).trans hrad
  by_cases hε1 : 1 ≤ ε
  · apply hone
    have hp : 1 ≤ ε ^ ((k : ℝ)⁻¹) := Real.one_le_rpow hε1 (by positivity)
    exact hKr.trans (by nlinarith only [hp, hK])
  have hεsmall : ε ≤ 1 := (lt_of_not_ge hε1).le
  obtain ⟨m, b, hlow⟩ := hwindow x
  by_cases hm : (m : ℕ) = 0
  · by_cases hεA : ε ≤ A
    · refine ⟨∅, by simp, fun y hy hval => ?_⟩
      have hl := hlow y hy
      rw [hm] at hl
      exact (not_lt_of_ge (hεA.trans (hl.trans (abs_traceComponent_le b _))) hval).elim
    · have hAε : A ≤ ε := (lt_of_not_ge hεA).le
      have hp : ε ≤ ε ^ ((k : ℝ)⁻¹) := by
        have hki : (k : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hk)
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_ge hε hεsmall hki
      apply hone
      calc r = (r / A) * A := by field_simp
        _ ≤ (r / A) * ε := mul_le_mul_of_nonneg_left hAε (by positivity)
        _ ≤ K * ε ^ ((k : ℝ)⁻¹) := mul_le_mul hKA hp hε.le hK.le
  · have hmpos : 1 ≤ (m : ℕ) := Nat.one_le_iff_ne_zero.mpr hm
    have hmreal : 0 < (m : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hm)
    have hchain : HTGeometry.KleinbockMargulis.IsDerivChain (m : ℕ)
        (fun j y => traceComponent b (oscillatoryJet γ c j y)) (Ioo (x - r) (x + r)) :=
      fun j _ y _ => hasDerivAt_traceComponent_jet γ c b j y
    obtain ⟨T, hTc, hcover⟩ := exists_sublevel_cover_of_derivative_lower
      ordConnected_Ioo hchain hmpos hA hε hlow
    have hexp : ε ^ ((m : ℝ)⁻¹) ≤ ε ^ ((k : ℝ)⁻¹) := by
      apply Real.rpow_le_rpow_of_exponent_ge hε hεsmall
      exact inv_anti₀ hmreal (by exact_mod_cast m.isLt.le)
    refine ⟨T, hTc.trans m.isLt.le, fun y hy hval => ?_⟩
    obtain ⟨z, hz, hdist⟩ := hcover y hy ((abs_traceComponent_le b _).trans_lt hval)
    exact ⟨z, hz, hdist.trans (mul_le_mul (hKD m m.isLt) hexp (by positivity) hK.le)⟩

#print axioms exists_uniform_oscillatory_sublevel_cover

end GaloisForLFunctions.InfiniteRankWeilTheory
