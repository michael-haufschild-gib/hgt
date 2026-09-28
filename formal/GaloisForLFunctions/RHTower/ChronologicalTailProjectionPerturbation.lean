import GaloisForLFunctions.RHTower.ChronologicalTailUnitNormal
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Unit normals are stable under perturbation of a finite spanning family

Let `e₁, …, e_l` be linearly independent in a complex inner product space and let `ψ` be a unit
vector orthogonal to all of them.  If `e'_j` are within `ε` of `e_j`, then the unit normal `ψ'` of
`ψ` against `span e'` is within `O(ε)` of `ψ`, with a constant depending only on the family `e`.

* The family has a lower frame bound `λ ‖c‖ ≤ ‖Σ c_j e_j‖` (an injective linear map on a
  finite-dimensional space is antilipschitz), which survives the perturbation with `λ/2`.
* The projection `w` of `ψ` onto `span e'` satisfies `‖w‖² = ⟪w, ψ⟫`, and writing
  `w = Σ c_j e'_j` gives `⟪w, ψ⟫ = Σ c̄_j ⟪e'_j - e_j, ψ⟫`, so `‖w‖ ≤ (2 l ε / λ) ‖ψ‖`.
* Normalising `ψ - w` moves it by at most `2 ‖w‖`.
-/

noncomputable section
open Submodule

namespace RHTower

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Lower frame bound** for a linearly independent finite family. -/
theorem exists_frame_lower_bound {l : ℕ} {e : Fin l → E} (he : LinearIndependent ℂ e) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ c : Fin l → ℂ, lam * ‖c‖ ≤ ‖∑ j, c j • e j‖ := by
  set T : (Fin l → ℂ) →ₗ[ℂ] E := Fintype.linearCombination ℂ e with hT
  have hker : LinearMap.ker T = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact linearIndependent_iff_injective_fintypeLinearCombination.mp he
  obtain ⟨K, hK, hanti⟩ := T.exists_antilipschitzWith hker
  refine ⟨(K : ℝ)⁻¹, inv_pos.mpr (by exact_mod_cast hK), fun c => ?_⟩
  have h := hanti.le_mul_dist c 0
  rw [dist_zero_right, map_zero, dist_zero_right] at h
  have hTc : T c = ∑ j, c j • e j := by
    simp [hT, Fintype.linearCombination_apply]
  rw [hTc] at h
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  rw [inv_mul_le_iff₀ hKpos]
  exact h

/-- **The frame bound survives a small perturbation.** -/
theorem frame_lower_bound_of_perturb {l : ℕ} {e e' : Fin l → E} {lam ε : ℝ}
    (hframe : ∀ c : Fin l → ℂ, lam * ‖c‖ ≤ ‖∑ j, c j • e j‖)
    (hclose : ∀ j, ‖e' j - e j‖ ≤ ε) (hsmall : l * ε ≤ lam / 2) :
    ∀ c : Fin l → ℂ, lam / 2 * ‖c‖ ≤ ‖∑ j, c j • e' j‖ := by
  intro c
  have hdiff : ‖∑ j, c j • e' j - ∑ j, c j • e j‖ ≤ l * ε * ‖c‖ := by
    rw [← Finset.sum_sub_distrib]
    calc ‖∑ j, (c j • e' j - c j • e j)‖ ≤ ∑ j, ‖c j • e' j - c j • e j‖ := norm_sum_le _ _
      _ = ∑ j, ‖c j‖ * ‖e' j - e j‖ := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← smul_sub, norm_smul]
      _ ≤ ∑ _j : Fin l, ‖c‖ * ε := by
          refine Finset.sum_le_sum fun j _ => ?_
          exact mul_le_mul (norm_le_pi_norm c j) (hclose j) (norm_nonneg _) (norm_nonneg _)
      _ = l * ε * ‖c‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have h1 := hframe c
  have h2 := norm_sub_norm_le (∑ j, c j • e j) (∑ j, c j • e' j)
  rw [norm_sub_rev] at h2
  have h3 : l * ε * ‖c‖ ≤ lam / 2 * ‖c‖ := mul_le_mul_of_nonneg_right hsmall (norm_nonneg _)
  linarith

/-- **The projection of an orthogonal unit vector onto a perturbed span is small.** -/
theorem norm_starProjection_le_of_perturb {l : ℕ} {e e' : Fin l → E} {lam ε : ℝ}
    (hlam : 0 < lam) (hε : 0 ≤ ε) (hframe' : ∀ c : Fin l → ℂ, lam / 2 * ‖c‖ ≤ ‖∑ j, c j • e' j‖)
    (hclose : ∀ j, ‖e' j - e j‖ ≤ ε) {ψ : E} (hψ : ∀ j, (inner ℂ (e j) ψ : ℂ) = 0)
    (W : Submodule ℂ E) [W.HasOrthogonalProjection] (hW : W = span ℂ (Set.range e')) :
    ‖W.starProjection ψ‖ ≤ 2 * l * ε / lam * ‖ψ‖ := by
  set w := W.starProjection ψ with hw
  have hwmem : w ∈ W := W.starProjection_apply_mem ψ
  obtain ⟨c, hc⟩ := (mem_span_range_iff_exists_fun ℂ).mp (hW ▸ hwmem)
  -- `‖w‖² = ⟪w, ψ⟫`
  have hself : (inner ℂ w ψ : ℂ) = (‖w‖ : ℂ) ^ 2 := by
    have hperp : (inner ℂ (ψ - w) w : ℂ) = 0 := W.starProjection_inner_eq_zero ψ w hwmem
    have hsplit : (inner ℂ w ψ : ℂ) = (inner ℂ w w : ℂ) + (inner ℂ w (ψ - w) : ℂ) := by
      rw [← inner_add_right]; congr 1; abel
    rw [hsplit, inner_self_eq_norm_sq_to_K, ← inner_conj_symm, hperp, map_zero, add_zero]
    rfl
  -- `⟪w, ψ⟫ = Σ c̄_j ⟪e'_j - e_j, ψ⟫`
  have hexpand : (inner ℂ w ψ : ℂ) = ∑ j, (starRingEnd ℂ) (c j) * inner ℂ (e' j - e j) ψ := by
    rw [← hc, sum_inner]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_smul_left, inner_sub_left, hψ j, sub_zero]
  have hbound : ‖(inner ℂ w ψ : ℂ)‖ ≤ l * ε * ‖c‖ * ‖ψ‖ := by
    rw [hexpand]
    calc ‖∑ j, (starRingEnd ℂ) (c j) * inner ℂ (e' j - e j) ψ‖
        ≤ ∑ j, ‖(starRingEnd ℂ) (c j) * inner ℂ (e' j - e j) ψ‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin l, ‖c‖ * (ε * ‖ψ‖) := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [norm_mul, RCLike.norm_conj]
          refine mul_le_mul (norm_le_pi_norm c j) ?_ (norm_nonneg _) (norm_nonneg _)
          exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hclose j)
            (norm_nonneg _))
      _ = l * ε * ‖c‖ * ‖ψ‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hcw : ‖c‖ ≤ 2 / lam * ‖w‖ := by
    have := hframe' c
    rw [hc] at this
    rw [div_mul_eq_mul_div, le_div_iff₀ hlam]
    linarith
  rw [hself, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at hbound
  have hkey : ‖w‖ * ‖w‖ ≤ (2 * l * ε / lam * ‖ψ‖) * ‖w‖ := by
    have hlε : 0 ≤ (l : ℝ) * ε := by positivity
    calc ‖w‖ * ‖w‖ = ‖w‖ ^ 2 := by ring
      _ ≤ l * ε * ‖c‖ * ‖ψ‖ := hbound
      _ ≤ l * ε * (2 / lam * ‖w‖) * ‖ψ‖ := by gcongr
      _ = (2 * l * ε / lam * ‖ψ‖) * ‖w‖ := by ring
  rcases (norm_nonneg w).eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  · exact le_of_mul_le_mul_right hkey hpos

/-- **Normalising a small correction.**  If `ψ` is a unit vector whose projection onto `W` has norm
`η < 1`, then `ψ ∉ W` and the unit normal of `ψ` against `W` is within `2η` of `ψ`. -/
theorem norm_unitNormal_sub_le {W : Submodule ℂ E} [W.HasOrthogonalProjection] {ψ : E}
    (hψ : ‖ψ‖ = 1) (hη : ‖W.starProjection ψ‖ < 1) :
    ψ ∉ W ∧ ‖unitNormal W ψ - ψ‖ ≤ 2 * ‖W.starProjection ψ‖ := by
  set η := ‖W.starProjection ψ‖ with hηdef
  have hnot : ψ ∉ W := by
    intro hmem
    rw [W.starProjection_eq_self_iff.mpr hmem, hψ] at hηdef
    linarith
  refine ⟨hnot, ?_⟩
  set v := ψ - W.starProjection ψ with hv
  have hvψ : ‖v - ψ‖ = η := by rw [hv, sub_sub_cancel_left, norm_neg]
  have hvnorm : |‖v‖ - 1| ≤ η := by
    rw [← hψ, ← hvψ]; exact abs_norm_sub_norm_le v ψ
  have hvpos : 0 < ‖v‖ := by
    have := (abs_le.mp hvnorm).1
    linarith
  have hunit : unitNormal W ψ = ((‖v‖ : ℂ)⁻¹) • v := by
    rw [unitNormal, orthoDefect]
  calc ‖unitNormal W ψ - ψ‖ ≤ ‖unitNormal W ψ - v‖ + ‖v - ψ‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = |1 - ‖v‖| + η := by
        rw [hvψ, hunit]
        congr 1
        have : ((‖v‖ : ℂ)⁻¹) • v - v = (((‖v‖⁻¹ - 1 : ℝ)) : ℂ) • v := by
          rw [Complex.ofReal_sub, Complex.ofReal_inv, Complex.ofReal_one, sub_smul, one_smul]
        have hmul : (‖v‖⁻¹ - 1) * ‖v‖ = 1 - ‖v‖ := by field_simp
        rw [this, norm_smul, Complex.norm_real, Real.norm_eq_abs, ← hmul, abs_mul,
          abs_of_pos hvpos]
    _ ≤ 2 * η := by rw [abs_sub_comm]; linarith

end RHTower
