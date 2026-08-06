import GaloisForLFunctions.HTGeometry.BohrParseval

/-!
# Window averages of uniformly approximated functions

The window average is bounded by the supremum of its integrand and is additive
over finite sums of continuous functions.

Consequently a function whose window averages are uniformly within `ε` of those
of a convergent comparison function, for every `ε`, has convergent window
averages: this is the mean-value form of a uniform approximation, and it needs
no almost periodicity.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-! ### The size of a window average -/

theorem norm_windowAverage_le {h : ℝ → ℂ} {C : ℝ} (hC : ∀ t, ‖h t‖ ≤ C) (T : ℝ) :
    ‖windowAverage h T‖ ≤ C := by
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  rcases eq_or_ne T 0 with hT | hT
  · subst hT
    rw [windowAverage]
    simp only [intervalIntegral.integral_same, smul_zero, norm_zero]
    exact hC0
  · have hint : ‖∫ t in (0 : ℝ)..T, h t‖ ≤ C * |T - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun t _ => hC t
    rw [windowAverage, norm_smul, Real.norm_eq_abs, abs_inv]
    have hTpos : 0 < |T| := abs_pos.2 hT
    calc |T|⁻¹ * ‖∫ t in (0 : ℝ)..T, h t‖ ≤ |T|⁻¹ * (C * |T - 0|) :=
          mul_le_mul_of_nonneg_left hint (le_of_lt (inv_pos.2 hTpos))
      _ = C := by
          rw [sub_zero]
          field_simp

/-! ### Finite sums -/

theorem windowAverage_finset_sum {ι : Type*} (s : Finset ι) {g : ι → ℝ → ℂ}
    (hg : ∀ i ∈ s, Continuous (g i)) (T : ℝ) :
    windowAverage (fun t => ∑ i ∈ s, g i t) T = ∑ i ∈ s, windowAverage (g i) T := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      rw [windowAverage]
      simp
  | insert j S hj ih =>
      have hjc : Continuous (g j) := hg j (Finset.mem_insert_self j S)
      have hSc : ∀ i ∈ S, Continuous (g i) := fun i hi =>
        hg i (Finset.mem_insert_of_mem hi)
      have hsumc : Continuous fun t => ∑ i ∈ S, g i t :=
        continuous_finsetSum S hSc
      have hstep : (fun t => ∑ i ∈ insert j S, g i t)
          = fun t => g j t + ∑ i ∈ S, g i t := by
        funext t
        rw [Finset.sum_insert hj]
      rw [hstep, windowAverage_add hjc hsumc, ih hSc, Finset.sum_insert hj]

/-! ### Convergence from uniform approximation -/

/-- **Uniform approximation of window averages.**  A function whose values are
uniformly within `ε` of those of a convergent comparison function, with limit
within `ε` of a target, for every `ε`, converges to that target. -/
theorem tendsto_of_approx {u : ℝ → ℂ} {A : ℂ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ (v : ℝ → ℂ) (B : ℂ), (∀ T, ‖u T - v T‖ ≤ ε) ∧
      ‖B - A‖ ≤ ε ∧ Tendsto v atTop (nhds B)) :
    Tendsto u atTop (nhds A) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨v, B, huv, hBA, hv⟩ := h (ε / 3) (by linarith)
  rw [Metric.tendsto_atTop] at hv
  obtain ⟨T₀, hT₀⟩ := hv (ε / 3) (by linarith)
  refine ⟨T₀, fun T hT => ?_⟩
  have h1 : ‖u T - v T‖ ≤ ε / 3 := huv T
  have h2 : ‖v T - B‖ < ε / 3 := by
    have := hT₀ T hT
    rwa [dist_eq_norm] at this
  have h3 : ‖B - A‖ ≤ ε / 3 := hBA
  have hsplit : u T - A = (u T - v T) + (v T - B) + (B - A) := by ring
  rw [dist_eq_norm, hsplit]
  calc ‖u T - v T + (v T - B) + (B - A)‖
      ≤ ‖u T - v T + (v T - B)‖ + ‖B - A‖ := norm_add_le _ _
    _ ≤ ‖u T - v T‖ + ‖v T - B‖ + ‖B - A‖ := by
        have hsub := norm_add_le (u T - v T) (v T - B)
        linarith
    _ < ε := by linarith

/-! ### The Bohr mean of a convergent function -/

theorem bohrMean_eq_of_tendsto {g : ℝ → ℂ} {M : ℂ}
    (h : Tendsto (windowAverage g) atTop (nhds M)) : bohrMean g = M := by
  have hex : ∃ M : ℂ, Tendsto (windowAverage g) atTop (nhds M) := ⟨M, h⟩
  rw [bohrMean, dif_pos hex]
  exact tendsto_nhds_unique hex.choose_spec h

end

end GaloisForLFunctions.HTGeometry
