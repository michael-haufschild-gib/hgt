import GaloisForLFunctions.HTGeometry.LocalExponentialMatrixSignCone

/-!
# The converse of the block-Hankel sign cone

Positivity of every block Hankel section of a bounded Hermitian matrix density forces the density
itself to be positive semidefinite almost everywhere.  This is the converse half of Theorem 3.1 of
the local-exponential complete-order fusion law, and with the forward half it closes the complete
block-Hankel sign-cone equivalence and its finite-witness corollary.

The route is the card's own: test one scalar direction at a time with the rank-one polynomial
family, apply the scalar endgame `ae_nonneg_of_forall_sq_poly_integral_nonneg`, intersect the
resulting full-measure sets over a countable dense set of directions, and extend to all directions
by continuity of the quadratic form.
-/

namespace HTGeometry

open MeasureTheory Complex Filter
open scoped Matrix ComplexOrder

section MatrixSignCone

variable {d : ℕ} {μ : Measure ℝ} [IsFiniteMeasure μ]

/-- The scalar density read by one direction. -/
noncomputable def directionDensity (J : ℝ → Matrix (Fin d) (Fin d) ℂ) (u : Fin d → ℂ)
    (x : ℝ) : ℝ := (matQuad (J x) u).re

theorem aestronglyMeasurable_directionDensity
    {J : ℝ → Matrix (Fin d) (Fin d) ℂ}
    (hmeas : ∀ k l, AEStronglyMeasurable (fun x => J x k l) μ) (u : Fin d → ℂ) :
    AEStronglyMeasurable (directionDensity J u) μ := by
  have h1 : AEStronglyMeasurable
      (∑ k : Fin d, ∑ l : Fin d, fun x => (starRingEnd ℂ) (u k) * J x k l * u l) μ :=
    Finset.aestronglyMeasurable_sum _ fun k _ =>
      Finset.aestronglyMeasurable_sum _ fun l _ =>
        (((hmeas k l).const_mul _).mul_const _)
  have h2 : (∑ k : Fin d, ∑ l : Fin d, fun x => (starRingEnd ℂ) (u k) * J x k l * u l)
      = fun x => matQuad (J x) u := by
    funext x
    simp only [matQuad, Finset.sum_apply]
  rw [h2] at h1
  exact h1.re

/-- The direction density is bounded by the entrywise bound times the squared `ℓ¹` norm. -/
theorem abs_directionDensity_le
    {J : ℝ → Matrix (Fin d) (Fin d) ℂ} {C : ℝ}
    {x : ℝ} (hx : ∀ k l, ‖J x k l‖ ≤ C) (u : Fin d → ℂ) :
    |directionDensity J u x| ≤ C * (∑ k, ‖u k‖) ^ 2 := by
  have hbound : ‖matQuad (J x) u‖ ≤ C * (∑ k, ‖u k‖) ^ 2 := by
    calc ‖matQuad (J x) u‖
        = ‖∑ k, ∑ l, (starRingEnd ℂ) (u k) * J x k l * u l‖ := rfl
      _ ≤ ∑ k, ‖∑ l, (starRingEnd ℂ) (u k) * J x k l * u l‖ := norm_sum_le _ _
      _ ≤ ∑ k, ∑ l, ‖(starRingEnd ℂ) (u k) * J x k l * u l‖ :=
          Finset.sum_le_sum fun k _ => norm_sum_le _ _
      _ ≤ ∑ k, ∑ l, ‖u k‖ * C * ‖u l‖ := by
          refine Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => ?_
          rw [norm_mul, norm_mul, RCLike.norm_conj]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hx k l) (norm_nonneg _)) (norm_nonneg _)
      _ = C * (∑ k, ‖u k‖) ^ 2 := by
          rw [sq, Finset.sum_mul_sum]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun l _ => by ring
  exact le_trans (abs_re_le_norm _) hbound

/-- One direction of the density is nonnegative almost everywhere. -/
theorem ae_nonneg_directionDensity {a : ℝ} (ha : 0 < a)
    (hexp : Integrable (fun x => Real.exp (a * |x|)) μ)
    {J : ℝ → Matrix (Fin d) (Fin d) ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hmeas : ∀ k l, AEStronglyMeasurable (fun x => J x k l) μ)
    (hbdd : ∀ᵐ x ∂μ, ∀ k l, ‖J x k l‖ ≤ C)
    (hH : ∀ (N : ℕ) (v : Fin N × Fin d → ℂ), 0 ≤ (matQuad (blockHankel μ J N) v).re)
    (u : Fin d → ℂ) :
    0 ≤ᵐ[μ] directionDensity J u := by
  refine ae_nonneg_of_forall_sq_poly_integral_nonneg (C := C * (∑ k, ‖u k‖) ^ 2) ha hexp
    (by positivity) (aestronglyMeasurable_directionDensity hmeas u) ?_ ?_
  · filter_upwards [hbdd] with x hx
    exact abs_directionDensity_le hx u
  · intro P
    exact integral_normSq_poly_mul_matQuad_nonneg ha hexp hC hmeas hbdd hH P u

/-- **Theorem 3.1, converse direction.**  Positive block Hankel sections force a positive
semidefinite density almost everywhere. -/
theorem ae_posSemidef_of_forall_blockHankel_nonneg {a : ℝ} (ha : 0 < a)
    (hexp : Integrable (fun x => Real.exp (a * |x|)) μ)
    {J : ℝ → Matrix (Fin d) (Fin d) ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hmeas : ∀ k l, AEStronglyMeasurable (fun x => J x k l) μ)
    (hbdd : ∀ᵐ x ∂μ, ∀ k l, ‖J x k l‖ ≤ C)
    (hherm : ∀ᵐ x ∂μ, (J x).IsHermitian)
    (hH : ∀ (N : ℕ) (v : Fin N × Fin d → ℂ), 0 ≤ (matQuad (blockHankel μ J N) v).re) :
    ∀ᵐ x ∂μ, (J x).PosSemidef := by
  classical
  obtain ⟨D, hDcount, hDdense⟩ :=
    TopologicalSpace.exists_countable_dense (Fin d → ℂ)
  have hall : ∀ᵐ x ∂μ, ∀ u ∈ D, 0 ≤ directionDensity J u x := by
    rw [ae_ball_iff hDcount]
    intro u _
    exact ae_nonneg_directionDensity ha hexp hC hmeas hbdd hH u
  filter_upwards [hall, hherm] with x hx hxherm
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hxherm fun u => ?_
  have hcont : Continuous fun u : Fin d → ℂ => (matQuad (J x) u).re := by
    simp only [matQuad]
    fun_prop
  have hclosed : IsClosed {u : Fin d → ℂ | 0 ≤ (matQuad (J x) u).re} :=
    isClosed_le continuous_const hcont
  have hsub : D ⊆ {u : Fin d → ℂ | 0 ≤ (matQuad (J x) u).re} := fun u hu => hx u hu
  have hre : 0 ≤ (matQuad (J x) u).re := by
    have := hDdense.closure_eq ▸ (hclosed.closure_subset_iff.mpr hsub)
    exact this (Set.mem_univ u)
  have him : (matQuad (J x) u).im = 0 := by
    have hconj : (starRingEnd ℂ) (matQuad (J x) u) = matQuad (J x) u := by
      simp only [matQuad, map_sum, map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      have h1 : (starRingEnd ℂ) (J x l k) = J x k l := by
        have h2 := congrFun (congrFun hxherm k) l
        simpa [Matrix.conjTranspose_apply, Complex.star_def] using h2
      rw [h1]; ring
    have := congrArg Complex.im hconj
    simp only [Complex.conj_im] at this
    linarith
  rw [← matQuad_eq_dotProduct]
  exact Complex.le_def.mpr ⟨by simpa using hre, by simpa using him.symm⟩

/-- **Complete block-Hankel sign-cone equivalence.** -/
theorem ae_posSemidef_iff_forall_blockHankel_nonneg {a : ℝ} (ha : 0 < a)
    (hexp : Integrable (fun x => Real.exp (a * |x|)) μ)
    {J : ℝ → Matrix (Fin d) (Fin d) ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hmeas : ∀ k l, AEStronglyMeasurable (fun x => J x k l) μ)
    (hbdd : ∀ᵐ x ∂μ, ∀ k l, ‖J x k l‖ ≤ C)
    (hherm : ∀ᵐ x ∂μ, (J x).IsHermitian) :
    (∀ᵐ x ∂μ, (J x).PosSemidef) ↔
      ∀ (N : ℕ) (v : Fin N × Fin d → ℂ), 0 ≤ (matQuad (blockHankel μ J N) v).re := by
  constructor
  · intro hpos N v
    exact re_matQuad_blockHankel_nonneg ha hexp hC hmeas hbdd hpos N v
  · intro hH
    exact ae_posSemidef_of_forall_blockHankel_nonneg ha hexp hC hmeas hbdd hherm hH

/-- **Corollary 3.2 — finite negative witness.**  A density that fails positivity on a set of
positive measure is detected by one finite block Hankel section. -/
theorem exists_blockHankel_neg_of_not_ae_posSemidef {a : ℝ} (ha : 0 < a)
    (hexp : Integrable (fun x => Real.exp (a * |x|)) μ)
    {J : ℝ → Matrix (Fin d) (Fin d) ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hmeas : ∀ k l, AEStronglyMeasurable (fun x => J x k l) μ)
    (hbdd : ∀ᵐ x ∂μ, ∀ k l, ‖J x k l‖ ≤ C)
    (hherm : ∀ᵐ x ∂μ, (J x).IsHermitian)
    (hfail : ¬ ∀ᵐ x ∂μ, (J x).PosSemidef) :
    ∃ (N : ℕ) (v : Fin N × Fin d → ℂ), (matQuad (blockHankel μ J N) v).re < 0 := by
  by_contra hcon
  simp only [not_exists, not_lt] at hcon
  exact hfail (ae_posSemidef_of_forall_blockHankel_nonneg ha hexp hC hmeas hbdd hherm hcon)

end MatrixSignCone

end HTGeometry
