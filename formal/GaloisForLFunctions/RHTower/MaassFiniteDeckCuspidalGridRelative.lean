import GaloisForLFunctions.RHTower.MaassFiniteDeckCuspidalGridSplice

/-!
# Homogeneous finite-grid approximation for cuspidal sources

The grid splice is controlled by the completed three-coordinate form norm.
This homogeneous formulation is closed under form-domain completion.
-/

open UpperHalfPlane Set Filter Topology Complex MeasureTheory

namespace GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet

open MaassCongruenceL2 SelbergMaassCongruenceTrace GaloisForLFunctions.HTGeometry
noncomputable section

/-- The source-level finite-grid error is bounded homogeneously by its completed
cuspidal form norm. -/
theorem exists_reciprocal_grid_cuspidal_error_le_formNorm {N M K : ℕ} (hM : 0 < M)
    (hY : 1 ≤ Real.sqrt 3 / 2 + (K : ℝ) * (M : ℝ)⁻¹)
    (F : cuspidalFormPreDomain N) :
    ∃ C : ℕ → ℕ → DeckSpace N,
      ‖toDeckL2 (F : ℍ → DeckSpace N) (cuspidalFormPreDomain.memLp F) -
        deckGridStep (N := N) (M := M) (K := K)
          (-(1 : ℝ) / 2) (Real.sqrt 3 / 2) ((M : ℝ)⁻¹) ((M : ℝ)⁻¹) C‖ ≤
        Real.sqrt
          ((((Real.sqrt 3 / 2) ^ 2)⁻¹ * (16 * ((M : ℝ)⁻¹) ^ 2)) *
            ‖cuspidalFormEmbeddingMap N F‖ ^ 2) +
        Real.sqrt
          ((((N + 1 : ℝ) / (2 * Real.pi)) ^ 2) *
            (Real.sqrt 3 / 2 + (K : ℝ) * (M : ℝ)⁻¹)⁻¹ ^ 2 *
              ‖cuspidalFormEmbeddingMap N F‖ ^ 2) := by
  obtain ⟨C, hC⟩ := exists_reciprocal_grid_cuspidal_error_le hM hY F
  let A : ℝ := ((Real.sqrt 3 / 2) ^ 2)⁻¹ * (16 * ((M : ℝ)⁻¹) ^ 2)
  let B : ℝ := (((N + 1 : ℝ) / (2 * Real.pi)) ^ 2) *
    (Real.sqrt 3 / 2 + (K : ℝ) * (M : ℝ)⁻¹)⁻¹ ^ 2
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hcoord0 : (cuspidalFormEmbeddingMap N F).ofLp 0 =
      toDeckL2 (F : ℍ → DeckSpace N) (cuspidalFormPreDomain.memLp F) := rfl
  have hcoord1 : (cuspidalFormEmbeddingMap N F).ofLp 1 =
      toDeckL2 (hypGradX (F : ℍ → DeckSpace N))
        (cuspidalFormPreDomain.memLp_gradX F) := rfl
  have hcoord2 : (cuspidalFormEmbeddingMap N F).ofLp 2 =
      toDeckL2 (hypGradY (F : ℍ → DeckSpace N))
        (cuspidalFormPreDomain.memLp_gradY F) := rfl
  have hgradSum :
      ‖toDeckL2 (hypGradX (F : ℍ → DeckSpace N))
          (cuspidalFormPreDomain.memLp_gradX F)‖ ^ 2 +
        ‖toDeckL2 (hypGradY (F : ℍ → DeckSpace N))
          (cuspidalFormPreDomain.memLp_gradY F)‖ ^ 2 ≤
        ‖cuspidalFormEmbeddingMap N F‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [Fin.sum_univ_three]
    rw [hcoord0, hcoord1, hcoord2]
    nlinarith [sq_nonneg ‖toDeckL2 (F : ℍ → DeckSpace N)
      (cuspidalFormPreDomain.memLp F)‖]
  have hgradX : ‖toDeckL2 (hypGradX (F : ℍ → DeckSpace N))
      (cuspidalFormPreDomain.memLp_gradX F)‖ ≤ ‖cuspidalFormEmbeddingMap N F‖ := by
    have h := PiLp.norm_apply_le (cuspidalFormEmbeddingMap N F) (1 : Fin 3)
    change ‖toDeckL2 (hypGradX (F : ℍ → DeckSpace N))
      (cuspidalFormPreDomain.memLp_gradX F)‖ ≤ _ at h
    exact h
  have hgradXSq : ‖toDeckL2 (hypGradX (F : ℍ → DeckSpace N))
      (cuspidalFormPreDomain.memLp_gradX F)‖ ^ 2 ≤
      ‖cuspidalFormEmbeddingMap N F‖ ^ 2 := by
    nlinarith [norm_nonneg (toDeckL2 (hypGradX (F : ℍ → DeckSpace N))
      (cuspidalFormPreDomain.memLp_gradX F)),
      norm_nonneg (cuspidalFormEmbeddingMap N F)]
  have hcore : A *
      (‖toDeckL2 (hypGradX (F : ℍ → DeckSpace N))
          (cuspidalFormPreDomain.memLp_gradX F)‖ ^ 2 +
        ‖toDeckL2 (hypGradY (F : ℍ → DeckSpace N))
          (cuspidalFormPreDomain.memLp_gradY F)‖ ^ 2) ≤
      A * ‖cuspidalFormEmbeddingMap N F‖ ^ 2 :=
    mul_le_mul_of_nonneg_left hgradSum hA
  have htail : B * ‖toDeckL2 (hypGradX (F : ℍ → DeckSpace N))
      (cuspidalFormPreDomain.memLp_gradX F)‖ ^ 2 ≤
      B * ‖cuspidalFormEmbeddingMap N F‖ ^ 2 :=
    mul_le_mul_of_nonneg_left hgradXSq hB
  have hcoreRoot : Real.sqrt (A *
      (‖toDeckL2 (hypGradX (F : ℍ → DeckSpace N))
          (cuspidalFormPreDomain.memLp_gradX F)‖ ^ 2 +
        ‖toDeckL2 (hypGradY (F : ℍ → DeckSpace N))
          (cuspidalFormPreDomain.memLp_gradY F)‖ ^ 2)) ≤
      Real.sqrt (A * ‖cuspidalFormEmbeddingMap N F‖ ^ 2) :=
    Real.sqrt_le_sqrt hcore
  have htailRoot : Real.sqrt (B * ‖toDeckL2 (hypGradX (F : ℍ → DeckSpace N))
      (cuspidalFormPreDomain.memLp_gradX F)‖ ^ 2) ≤
      Real.sqrt (B * ‖cuspidalFormEmbeddingMap N F‖ ^ 2) :=
    Real.sqrt_le_sqrt htail
  refine ⟨C, ?_⟩
  calc
    _ ≤ Real.sqrt (A *
        (‖toDeckL2 (hypGradX (F : ℍ → DeckSpace N))
            (cuspidalFormPreDomain.memLp_gradX F)‖ ^ 2 +
          ‖toDeckL2 (hypGradY (F : ℍ → DeckSpace N))
            (cuspidalFormPreDomain.memLp_gradY F)‖ ^ 2)) +
        Real.sqrt (B * ‖toDeckL2 (hypGradX (F : ℍ → DeckSpace N))
          (cuspidalFormPreDomain.memLp_gradX F)‖ ^ 2) := by
      simpa [A, B, mul_assoc] using hC
    _ ≤ Real.sqrt (A * ‖cuspidalFormEmbeddingMap N F‖ ^ 2) +
        Real.sqrt (B * ‖cuspidalFormEmbeddingMap N F‖ ^ 2) :=
      add_le_add hcoreRoot htailRoot
    _ = _ := by rfl

end

end GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet
