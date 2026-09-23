import GaloisForLFunctions.RHTower.MaassFiniteDeckCoreEnergyNorm
import GaloisForLFunctions.RHTower.MaassFiniteDeckCoreSplice

/-!
# Reciprocal-grid finite core estimate

At the canonical modular core `[-1/2,1/2] × (√3/2, √3/2 + K/M]`, a mesh
`1/M` gives a finite-dimensional grid approximation with its error stated
entirely in the two `DeckL2` derivative coordinates.
-/

open UpperHalfPlane Set Filter Topology Complex MeasureTheory

namespace GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet

open MaassCongruenceL2 SelbergMaassCongruenceTrace GaloisForLFunctions.HTGeometry
noncomputable section

/-- A reciprocal product grid approximates the finite modular core, with a
constant controlled by the two completed `L²` derivative coordinates. -/
theorem exists_reciprocal_grid_core_error_le_gradNormSq {N M K : ℕ} (hM : 0 < M)
    (F : formPreDomain N) :
    ∃ C : ℕ → ℕ → DeckSpace N,
      ‖finiteGridCoreProjection (N := N) (M := M) (K := K)
          (-(1 : ℝ) / 2) (Real.sqrt 3 / 2) ((M : ℝ)⁻¹) ((M : ℝ)⁻¹)
          (toDeckL2 (F : ℍ → DeckSpace N) (formPreDomain.memLp F)) -
        deckGridStep (N := N) (M := M) (K := K)
          (-(1 : ℝ) / 2) (Real.sqrt 3 / 2) ((M : ℝ)⁻¹) ((M : ℝ)⁻¹) C‖ ^ (2 : ℕ) ≤
        ((Real.sqrt 3 / 2) ^ (2 : ℕ))⁻¹ *
          (16 * ((M : ℝ)⁻¹) ^ (2 : ℕ) *
            (‖toDeckL2 (hypGradX (F : ℍ → DeckSpace N))
                (formPreDomain.memLp_gradX F)‖ ^ (2 : ℕ) +
              ‖toDeckL2 (hypGradY (F : ℍ → DeckSpace N))
                (formPreDomain.memLp_gradY F)‖ ^ (2 : ℕ))) := by
  have hM0 : (M : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hM
  have hMh : (M : ℝ) * (M : ℝ)⁻¹ = 1 := by
    simp [hM0]
  have hinv : 0 < (M : ℝ)⁻¹ := by
    exact inv_pos.mpr (by exact_mod_cast hM)
  have hsqrt : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hstripx : ∀ x ∈ Set.Ioc (-(1 : ℝ) / 2)
      (-(1 : ℝ) / 2 + (M : ℝ) * (M : ℝ)⁻¹), |x| ≤ (1 : ℝ) / 2 := by
    intro x hx
    rw [hMh] at hx
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2]
  have hstripy : ∀ y ∈ Set.Ioc (Real.sqrt 3 / 2)
      (Real.sqrt 3 / 2 + (K : ℝ) * (M : ℝ)⁻¹), 3 ≤ 4 * y ^ (2 : ℕ) := by
    intro y hy
    have hsqrt0 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
    have hsquare : (Real.sqrt 3) ^ (2 : ℕ) = 3 := Real.sq_sqrt (by norm_num)
    have hdiff : 0 ≤ 2 * y - Real.sqrt 3 := by linarith [hy.1]
    have hsum : 0 ≤ 2 * y + Real.sqrt 3 := by linarith [hy.1, hsqrt0]
    have hprod : 0 ≤ (2 * y - Real.sqrt 3) * (2 * y + Real.sqrt 3) :=
      mul_nonneg hdiff hsum
    nlinarith
  obtain ⟨C, hC⟩ := exists_grid_fdUpperChartGridCore_hyperbolic_error_le_fd_energy
    M K (ε := Real.sqrt 3 / 2) (a := -(1 : ℝ) / 2) (c := Real.sqrt 3 / 2)
      (hx := (M : ℝ)⁻¹) (hy := (M : ℝ)⁻¹)
      (by positivity) (by positivity) le_rfl hinv hinv (by linarith)
      hstripx hstripy F
  refine ⟨C, ?_⟩
  rw [normSq_finiteGridCoreProjection_sub_deckGridStep]
  rw [integral_hyperbolicChartGradientDensity_eq_gradNormSq] at hC
  exact hC

end

end GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet
