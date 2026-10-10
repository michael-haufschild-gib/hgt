import GaloisForLFunctions.RHTower.WeilLogShiftQuadraticSurjection

/-! Bounded local preimages give linear control of squared amplitude for every target. -/

open scoped BigOperators
open Filter Topology

noncomputable section
namespace RHTower

variable {J C : Type} [Fintype J] [Fintype C]

theorem finiteWeilQuadraticMap_bounded_realization (K : J → J → C → ℝ)
    (M ε : ℝ) (hM : 0 < M) (hε : 0 < ε)
    (hlocal : ∀ y : C → ℝ, ‖y‖ < ε →
      ∃ t : J → ℝ, finiteWeilQuadraticMap K t = y ∧ ‖t‖ < M) :
    ∀ y : C → ℝ, ∃ t : J → ℝ, finiteWeilQuadraticMap K t = y ∧
      ‖t‖ ^ 2 ≤ (2 * M ^ 2 / ε) * ‖y‖ := by
  intro y
  by_cases hy : y = 0
  · subst y
    refine ⟨0, ?_, by simp⟩
    simp [finiteWeilQuadraticMap]
  have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy
  let c : ℝ := ε / (2 * ‖y‖)
  have hd : 0 < 2 * ‖y‖ := by positivity
  have hc : 0 < c := div_pos hε hd
  have hce : c * (2 * ‖y‖) = ε := div_mul_cancel₀ ε hd.ne'
  have hsmall : ‖c • y‖ < ε := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    nlinarith only [hce, hε]
  obtain ⟨t, ht, htM⟩ := hlocal (c • y) hsmall
  refine ⟨(Real.sqrt c)⁻¹ • t, ?_, ?_⟩
  · rw [finiteWeilQuadraticMap_smul, inv_pow, Real.sq_sqrt hc.le, ht, smul_smul,
      inv_mul_cancel₀ hc.ne', one_smul]
  · have hscale : ‖(Real.sqrt c)⁻¹ • t‖ ^ 2 = ‖t‖ ^ 2 / c := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (Real.sqrt_nonneg c),
        mul_pow, inv_pow, Real.sq_sqrt hc.le]
      ring
    have hD : (2 * M ^ 2 / ε) * ‖y‖ * c = M ^ 2 := by
      calc
        (2 * M ^ 2 / ε) * ‖y‖ * c = (M ^ 2 / ε) * (c * (2 * ‖y‖)) := by ring
        _ = M ^ 2 := by rw [hce, div_mul_cancel₀ _ hε.ne']
    rw [hscale]
    apply (div_le_iff₀ hc).mpr
    rw [hD]
    nlinarith only [htM, hM, norm_nonneg t]

/-- The same amplitude-cost constant works for every kernel in a neighborhood. -/
theorem exists_eventually_controlled_finiteWeilQuadraticMap_diagonal (v : J → C → ℝ)
    (hz : ∑ i, v i = 0)
    (hspan : Function.Surjective (fun t : J → ℝ => ∑ i, t i • v i)) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ K in 𝓝 (finiteWeilQuadraticDiagonal v),
      ∀ y : C → ℝ, ∃ t : J → ℝ, finiteWeilQuadraticMap K t = y ∧ ‖t‖ ^ 2 ≤ D * ‖y‖ := by
  obtain ⟨M, ε, hM, hε, hK⟩ :=
    exists_eventually_bounded_finiteWeilQuadraticMap_diagonal v hz hspan
  refine ⟨2 * M ^ 2 / ε, by positivity, ?_⟩
  filter_upwards [hK] with K hK
  exact finiteWeilQuadraticMap_bounded_realization K M ε hM hε hK

end RHTower
