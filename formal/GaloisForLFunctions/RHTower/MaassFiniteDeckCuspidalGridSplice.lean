import GaloisForLFunctions.RHTower.MaassFiniteDeckCoreSpecialGrid
import GaloisForLFunctions.RHTower.MaassFiniteDeckCoreTailDecomposition
import GaloisForLFunctions.RHTower.MaassFiniteDeckCuspidalTailPre

/-!
# Quantitative finite-grid splice for cuspidal sources

The reciprocal finite core and cusp cutoff combine into one global finite-grid
approximation.  Its two displayed budgets are the exact core Dirichlet budget
and the cusp Poincaré budget.
-/

open UpperHalfPlane Set Filter Topology Complex MeasureTheory

namespace GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet

open MaassCongruenceL2 SelbergMaassCongruenceTrace GaloisForLFunctions.HTGeometry
noncomputable section

/-- A cusp-zero source has a global finite-grid approximant.  The two square-root
terms are respectively its core mesh error and its cusp-tail error. -/
theorem exists_reciprocal_grid_cuspidal_error_le {N M K : ℕ} (hM : 0 < M)
    (hY : 1 ≤ Real.sqrt 3 / 2 + (K : ℝ) * (M : ℝ)⁻¹)
    (F : cuspidalFormPreDomain N) :
    ∃ C : ℕ → ℕ → DeckSpace N,
      ‖toDeckL2 (F : ℍ → DeckSpace N) (cuspidalFormPreDomain.memLp F) -
        deckGridStep (N := N) (M := M) (K := K)
          (-(1 : ℝ) / 2) (Real.sqrt 3 / 2) ((M : ℝ)⁻¹) ((M : ℝ)⁻¹) C‖ ≤
        Real.sqrt
          (((Real.sqrt 3 / 2) ^ 2)⁻¹ *
            (16 * ((M : ℝ)⁻¹) ^ 2 *
              (‖toDeckL2 (hypGradX (F : ℍ → DeckSpace N))
                  (cuspidalFormPreDomain.memLp_gradX F)‖ ^ 2 +
                ‖toDeckL2 (hypGradY (F : ℍ → DeckSpace N))
                  (cuspidalFormPreDomain.memLp_gradY F)‖ ^ 2))) +
        Real.sqrt
          ((((N + 1 : ℝ) / (2 * Real.pi)) ^ 2) *
            (Real.sqrt 3 / 2 + (K : ℝ) * (M : ℝ)⁻¹)⁻¹ ^ 2 *
              ‖toDeckL2 (hypGradX (F : ℍ → DeckSpace N))
                (cuspidalFormPreDomain.memLp_gradX F)‖ ^ 2) := by
  obtain ⟨C, hcore⟩ := exists_reciprocal_grid_core_error_le_gradNormSq hM
    (cuspidalFormPreDomain.toFormPreDomain N F)
  change ‖finiteGridCoreProjection (N := N) (M := M) (K := K)
      (-(1 : ℝ) / 2) (Real.sqrt 3 / 2) ((M : ℝ)⁻¹) ((M : ℝ)⁻¹)
      (toDeckL2 (F : ℍ → DeckSpace N) (cuspidalFormPreDomain.memLp F)) -
      deckGridStep (N := N) (M := M) (K := K)
        (-(1 : ℝ) / 2) (Real.sqrt 3 / 2) ((M : ℝ)⁻¹) ((M : ℝ)⁻¹) C‖ ^ 2 ≤
    ((Real.sqrt 3 / 2) ^ 2)⁻¹ *
      (16 * ((M : ℝ)⁻¹) ^ 2 *
        (‖toDeckL2 (hypGradX (F : ℍ → DeckSpace N))
            (cuspidalFormPreDomain.memLp_gradX F)‖ ^ 2 +
          ‖toDeckL2 (hypGradY (F : ℍ → DeckSpace N))
            (cuspidalFormPreDomain.memLp_gradY F)‖ ^ 2)) at hcore
  have htail := cuspidalPreDomain_tail_projection_bound hY F
  let B : ℝ := (((N + 1 : ℝ) / (2 * Real.pi)) ^ 2) *
    (Real.sqrt 3 / 2 + (K : ℝ) * (M : ℝ)⁻¹)⁻¹ ^ 2
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have htailgrad := norm_cuspTailProjection_le
    (N := N) (Real.sqrt 3 / 2 + (K : ℝ) * (M : ℝ)⁻¹)
    (toDeckL2 (hypGradX (F : ℍ → DeckSpace N))
      (cuspidalFormPreDomain.memLp_gradX F))
  have htailgradSq :
      ‖cuspTailProjection N (Real.sqrt 3 / 2 + (K : ℝ) * (M : ℝ)⁻¹)
          (toDeckL2 (hypGradX (F : ℍ → DeckSpace N))
            (cuspidalFormPreDomain.memLp_gradX F))‖ ^ 2 ≤
        ‖toDeckL2 (hypGradX (F : ℍ → DeckSpace N))
          (cuspidalFormPreDomain.memLp_gradX F)‖ ^ 2 := by
    nlinarith [norm_nonneg
      (cuspTailProjection N (Real.sqrt 3 / 2 + (K : ℝ) * (M : ℝ)⁻¹)
        (toDeckL2 (hypGradX (F : ℍ → DeckSpace N))
          (cuspidalFormPreDomain.memLp_gradX F))),
      norm_nonneg (toDeckL2 (hypGradX (F : ℍ → DeckSpace N))
        (cuspidalFormPreDomain.memLp_gradX F))]
  change ‖cuspTailProjection N (Real.sqrt 3 / 2 + (K : ℝ) * (M : ℝ)⁻¹)
      (toDeckL2 (F : ℍ → DeckSpace N) (cuspidalFormPreDomain.memLp F))‖ ^ 2 ≤ B *
      ‖cuspTailProjection N (Real.sqrt 3 / 2 + (K : ℝ) * (M : ℝ)⁻¹)
        (toDeckL2 (hypGradX (F : ℍ → DeckSpace N))
          (cuspidalFormPreDomain.memLp_gradX F))‖ ^ 2 at htail
  have htail' : ‖cuspTailProjection N (Real.sqrt 3 / 2 + (K : ℝ) * (M : ℝ)⁻¹)
      (toDeckL2 (F : ℍ → DeckSpace N) (cuspidalFormPreDomain.memLp F))‖ ^ 2 ≤ B *
      ‖toDeckL2 (hypGradX (F : ℍ → DeckSpace N))
        (cuspidalFormPreDomain.memLp_gradX F)‖ ^ 2 :=
    htail.trans (mul_le_mul_of_nonneg_left htailgradSq hB)
  let A : ℝ := ((Real.sqrt 3 / 2) ^ 2)⁻¹ *
      (16 * ((M : ℝ)⁻¹) ^ 2 *
        (‖toDeckL2 (hypGradX (F : ℍ → DeckSpace N))
            (cuspidalFormPreDomain.memLp_gradX F)‖ ^ 2 +
          ‖toDeckL2 (hypGradY (F : ℍ → DeckSpace N))
            (cuspidalFormPreDomain.memLp_gradY F)‖ ^ 2))
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hcoreRoot : ‖finiteGridCoreProjection (N := N) (M := M) (K := K)
      (-(1 : ℝ) / 2) (Real.sqrt 3 / 2) ((M : ℝ)⁻¹) ((M : ℝ)⁻¹)
      (toDeckL2 (F : ℍ → DeckSpace N) (cuspidalFormPreDomain.memLp F)) -
      deckGridStep (N := N) (M := M) (K := K)
        (-(1 : ℝ) / 2) (Real.sqrt 3 / 2) ((M : ℝ)⁻¹) ((M : ℝ)⁻¹) C‖ ≤
      Real.sqrt A := by
    nlinarith [Real.sq_sqrt hA, Real.sqrt_nonneg A]
  have htailRoot : ‖cuspTailProjection N (Real.sqrt 3 / 2 + (K : ℝ) * (M : ℝ)⁻¹)
      (toDeckL2 (F : ℍ → DeckSpace N) (cuspidalFormPreDomain.memLp F))‖ ≤
      Real.sqrt (B * ‖toDeckL2 (hypGradX (F : ℍ → DeckSpace N))
        (cuspidalFormPreDomain.memLp_gradX F)‖ ^ 2) := by
    have hnonneg : 0 ≤ B * ‖toDeckL2 (hypGradX (F : ℍ → DeckSpace N))
        (cuspidalFormPreDomain.memLp_gradX F)‖ ^ 2 := by positivity
    nlinarith [Real.sq_sqrt hnonneg,
      Real.sqrt_nonneg (B * ‖toDeckL2 (hypGradX (F : ℍ → DeckSpace N))
        (cuspidalFormPreDomain.memLp_gradX F)‖ ^ 2)]
  refine ⟨C, ?_⟩
  calc
    ‖toDeckL2 (F : ℍ → DeckSpace N) (cuspidalFormPreDomain.memLp F) -
        deckGridStep (N := N) (M := M) (K := K)
          (-(1 : ℝ) / 2) (Real.sqrt 3 / 2) ((M : ℝ)⁻¹) ((M : ℝ)⁻¹) C‖ ≤
        ‖finiteGridCoreProjection (N := N) (M := M) (K := K)
            (-(1 : ℝ) / 2) (Real.sqrt 3 / 2) ((M : ℝ)⁻¹) ((M : ℝ)⁻¹)
            (toDeckL2 (F : ℍ → DeckSpace N) (cuspidalFormPreDomain.memLp F)) -
          deckGridStep (N := N) (M := M) (K := K)
            (-(1 : ℝ) / 2) (Real.sqrt 3 / 2) ((M : ℝ)⁻¹) ((M : ℝ)⁻¹) C‖ +
          ‖cuspTailProjection N (Real.sqrt 3 / 2 + (K : ℝ) * (M : ℝ)⁻¹)
            (toDeckL2 (F : ℍ → DeckSpace N) (cuspidalFormPreDomain.memLp F))‖ :=
      norm_sub_deckGridStep_le_core_add_tail hM _ C
    _ ≤ Real.sqrt A + Real.sqrt (B * ‖toDeckL2 (hypGradX (F : ℍ → DeckSpace N))
        (cuspidalFormPreDomain.memLp_gradX F)‖ ^ 2) :=
      add_le_add hcoreRoot htailRoot
    _ = _ := by rfl

end

end GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet
