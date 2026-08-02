import GaloisForLFunctions.HTGeometry.SchwartzSeminormOscillator

/-!
# The shifted oscillator seminorms present the Schwartz topology

The `L²` norms of the powers of the shifted number operator form a seminorm family on the Schwartz
space.  Each of them is continuous, hence bounded by finitely many Schwartz seminorms, and
conversely every Schwartz seminorm is bounded by one of them.  Since the family is increasing up to
constants, a finite supremum of Schwartz seminorms is bounded by a single member.

So the two families dominate each other in the form the nuclearity transfer needs: one family is
nuclear exactly when the other is.

* `shiftedPowCLM`, `shiftedSeminorm` : the family `Q_m(f) = ‖Kᵐf‖₂`.
* `shiftedSeminorm_le_of_le` : the family increases up to constants.
* `shiftedSeminorm_le_schwartzSup` : **each `Q_m` is bounded by finitely many Schwartz
  seminorms.**
* `schwartzSup_le_shiftedSeminorm` : **each finite supremum of Schwartz seminorms is bounded by a
  single `Q_m`.**
-/

open scoped Real SchwartzMap NNReal
open Complex MeasureTheory

noncomputable section

namespace GaloisForLFunctions

/-! ## The shifted seminorms -/

/-- The `m`-th power of the shifted number operator, as a continuous linear map. -/
def shiftedPowCLM : ℕ → (𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ))
  | 0 => ContinuousLinearMap.id ℂ _
  | (m + 1) => shiftedNumberCLM.comp (shiftedPowCLM m)

theorem shiftedPowCLM_apply (m : ℕ) (f : 𝓢(ℝ, ℂ)) :
    shiftedPowCLM m f = (shiftedNumberCLM^[m]) f := by
  induction m generalizing f with
  | zero => rfl
  | succ m ih =>
    show shiftedNumberCLM (shiftedPowCLM m f) = _
    rw [ih, Function.iterate_succ_apply']

/-- **The shifted oscillator seminorms** `Q_m(f) = ‖Kᵐf‖₂`. -/
def shiftedSeminorm (m : ℕ) : Seminorm ℂ 𝓢(ℝ, ℂ) :=
  (normSeminorm ℂ (Lp ℂ 2 (volume : Measure ℝ))).comp
    ((SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ)).toLinearMap.comp
      (shiftedPowCLM m).toLinearMap)

theorem shiftedSeminorm_apply (m : ℕ) (f : 𝓢(ℝ, ℂ)) :
    shiftedSeminorm m f = ‖((shiftedNumberCLM^[m]) f).toLp 2 (volume : Measure ℝ)‖ := by
  show ‖SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ) (shiftedPowCLM m f)‖ = _
  rw [SchwartzMap.toLpCLM_apply, shiftedPowCLM_apply]

/-- The family of shifted oscillator seminorms. -/
def shiftedSeminormFamily : SeminormFamily ℂ 𝓢(ℝ, ℂ) ℕ := shiftedSeminorm

/-! ## The family increases up to constants -/

theorem shiftedSeminorm_le_succ (m : ℕ) (f : 𝓢(ℝ, ℂ)) :
    shiftedSeminorm m f ≤ (4 * π)⁻¹ * shiftedSeminorm (m + 1) f := by
  rw [shiftedSeminorm_apply, shiftedSeminorm_apply]
  exact norm_toLp_iterate_le_succ m f

theorem shiftedSeminorm_le_of_le {m m' : ℕ} (hmm : m ≤ m') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : 𝓢(ℝ, ℂ), shiftedSeminorm m f ≤ C * shiftedSeminorm m' f := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmm
  clear hmm
  induction d with
  | zero => exact ⟨1, zero_le_one, fun f => by simp⟩
  | succ d ih =>
    obtain ⟨C, hC, hbound⟩ := ih
    refine ⟨C * (4 * π)⁻¹, by positivity, fun f => ?_⟩
    have hstep := shiftedSeminorm_le_succ (m + d) f
    have hmd : m + d + 1 = m + (d + 1) := by omega
    rw [hmd] at hstep
    calc shiftedSeminorm m f ≤ C * shiftedSeminorm (m + d) f := hbound f
      _ ≤ C * ((4 * π)⁻¹ * shiftedSeminorm (m + (d + 1)) f) :=
          mul_le_mul_of_nonneg_left hstep hC
      _ = C * (4 * π)⁻¹ * shiftedSeminorm (m + (d + 1)) f := by ring

/-! ## The two families dominate each other -/

theorem shiftedSeminorm_continuous (m : ℕ) : Continuous (shiftedSeminorm m) := by
  have hfun : ⇑(shiftedSeminorm m)
      = fun f : 𝓢(ℝ, ℂ) =>
        ‖((SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ)).comp (shiftedPowCLM m)) f‖ := by
    funext f
    rw [shiftedSeminorm_apply]
    show _ = ‖SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ) (shiftedPowCLM m f)‖
    rw [SchwartzMap.toLpCLM_apply, shiftedPowCLM_apply]
  rw [hfun]
  exact (ContinuousLinearMap.continuous _).norm

/-- **Each shifted seminorm is bounded by finitely many Schwartz seminorms.** -/
theorem shiftedSeminorm_le_schwartzSup (m : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ≥0), C ≠ 0 ∧
      shiftedSeminorm m ≤ C • s.sup (schwartzSeminormFamily ℂ ℝ ℂ) :=
  Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ ℝ ℂ) _ (shiftedSeminorm_continuous m)

/-- **Each finite supremum of Schwartz seminorms is bounded by a single shifted seminorm.** -/
theorem schwartzSup_le_shiftedSeminorm (s : Finset (ℕ × ℕ)) :
    ∃ (m : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ f : 𝓢(ℝ, ℂ),
      (s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f ≤ C * shiftedSeminorm m f := by
  classical
  induction s using Finset.induction with
  | empty =>
    refine ⟨0, 0, le_refl 0, fun f => ?_⟩
    simp
  | insert a s ha ih =>
    obtain ⟨m, C, hC, hbound⟩ := ih
    obtain ⟨C', hC', hbound'⟩ := schwartzSeminorm_le_shifted a.1 a.2
    obtain ⟨D, hD, hmono⟩ := shiftedSeminorm_le_of_le (le_max_left m (a.1 + a.2 + 2))
    obtain ⟨D', hD', hmono'⟩ :=
      shiftedSeminorm_le_of_le (le_max_right m (a.1 + a.2 + 2))
    refine ⟨max m (a.1 + a.2 + 2), C * D + C' * D', by positivity, fun f => ?_⟩
    have hsup : (insert a s).sup (schwartzSeminormFamily ℂ ℝ ℂ) f
        = max ((schwartzSeminormFamily ℂ ℝ ℂ a) f) ((s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f) := by
      rw [Finset.sup_insert, Seminorm.sup_apply]
    have ha' : (schwartzSeminormFamily ℂ ℝ ℂ a) f
        ≤ C' * D' * shiftedSeminorm (max m (a.1 + a.2 + 2)) f := by
      have h1 : (schwartzSeminormFamily ℂ ℝ ℂ a) f
          ≤ C' * shiftedSeminorm (a.1 + a.2 + 2) f := by
        rw [shiftedSeminorm_apply]
        exact hbound' f
      calc (schwartzSeminormFamily ℂ ℝ ℂ a) f
          ≤ C' * shiftedSeminorm (a.1 + a.2 + 2) f := h1
        _ ≤ C' * (D' * shiftedSeminorm (max m (a.1 + a.2 + 2)) f) :=
            mul_le_mul_of_nonneg_left (hmono' f) hC'
        _ = C' * D' * shiftedSeminorm (max m (a.1 + a.2 + 2)) f := by ring
    have hs' : (s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f
        ≤ C * D * shiftedSeminorm (max m (a.1 + a.2 + 2)) f := by
      calc (s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f ≤ C * shiftedSeminorm m f := hbound f
        _ ≤ C * (D * shiftedSeminorm (max m (a.1 + a.2 + 2)) f) :=
            mul_le_mul_of_nonneg_left (hmono f) hC
        _ = C * D * shiftedSeminorm (max m (a.1 + a.2 + 2)) f := by ring
    rw [hsup]
    have hnn : 0 ≤ shiftedSeminorm (max m (a.1 + a.2 + 2)) f := apply_nonneg _ _
    refine max_le ?_ ?_
    · calc (schwartzSeminormFamily ℂ ℝ ℂ a) f
          ≤ C' * D' * shiftedSeminorm (max m (a.1 + a.2 + 2)) f := ha'
        _ ≤ (C * D + C' * D') * shiftedSeminorm (max m (a.1 + a.2 + 2)) f := by
            refine mul_le_mul_of_nonneg_right ?_ hnn
            nlinarith [hC, hD]
    · calc (s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f
          ≤ C * D * shiftedSeminorm (max m (a.1 + a.2 + 2)) f := hs'
        _ ≤ (C * D + C' * D') * shiftedSeminorm (max m (a.1 + a.2 + 2)) f := by
            refine mul_le_mul_of_nonneg_right ?_ hnn
            nlinarith [hC', hD']

end GaloisForLFunctions

end
