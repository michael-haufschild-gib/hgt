import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaSquareLattice
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

/-!
# Nondegeneracy of Brizard's analytic square-lattice model

This closes the nonvanishing gap left by quarter-turn symmetry alone.  We reindex the square
period lattice by integer pairs and identify its `G₄` and `G₆` sums with mathlib's full Eisenstein
series at `τ = i`.  Since the modular discriminant never vanishes and `E₆(i) = 0`, necessarily
`E₄(i) ≠ 0`.  Therefore the square lattice has `G₄ ≠ 0`, `g₂ ≠ 0`, nonzero curve discriminant,
and exact modular invariant `j = 1728`, matching Brizard's `m = 1/2` family.
-/

open Complex
open UpperHalfPlane hiding I

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

/-- The square-lattice ratio `τ = i` in the upper half-plane. -/
noncomputable def upperI : ℍ := ⟨Complex.I, by simp⟩

/-- Coordinates on the square lattice, ordered to match mathlib's Eisenstein summand. -/
noncomputable def squareLatticeEquivFin :
    squarePeriodPair.lattice ≃ (Fin 2 → ℤ) :=
  (squarePeriodPair.latticeEquivProd.toEquiv.trans (Equiv.prodComm ℤ ℤ)).trans
    (finTwoArrowEquiv ℤ).symm

theorem coe_squareLatticeEquivFin_symm (v : Fin 2 → ℤ) :
    ((squareLatticeEquivFin.symm v : squarePeriodPair.lattice) : ℂ) =
      (v 0 : ℂ) * Complex.I + (v 1 : ℂ) := by
  rw [squareLatticeEquivFin]
  change ((squarePeriodPair.latticeEquivProd.symm
    (((finTwoArrowEquiv ℤ) v).swap) : squarePeriodPair.lattice) : ℂ) = _
  rw [PeriodPair.latticeEquiv_symm_apply]
  simp [squarePeriodPair]
  ring

/-- The analytic square-lattice `G₄` is the full weight-four Eisenstein sum at `i`. -/
theorem square_G_four_eq_full_eisenstein :
    squarePeriodPair.G 4 =
      ∑' v : Fin 2 → ℤ, EisensteinSeries.eisSummand 4 v upperI := by
  rw [PeriodPair.G]
  rw [← squareLatticeEquivFin.symm.tsum_eq]
  apply tsum_congr
  intro v
  rw [coe_squareLatticeEquivFin_symm]
  simp only [EisensteinSeries.eisSummand, upperI, UpperHalfPlane.coe_mk]
  congr 1

/-- The analytic square-lattice `G₆` is the full weight-six Eisenstein sum at `i`. -/
theorem square_G_six_eq_full_eisenstein :
    squarePeriodPair.G 6 =
      ∑' v : Fin 2 → ℤ, EisensteinSeries.eisSummand 6 v upperI := by
  rw [PeriodPair.G]
  rw [← squareLatticeEquivFin.symm.tsum_eq]
  apply tsum_congr
  intro v
  rw [coe_squareLatticeEquivFin_symm]
  simp only [EisensteinSeries.eisSummand, upperI, UpperHalfPlane.coe_mk]
  congr 1

theorem eisensteinSeries_four_eq_two_E₄ :
    eisensteinSeries (N := 1) 0 4 upperI = 2 * ModularForm.E₄ upperI := by
  change eisensteinSeries (N := 1) 0 4 upperI =
    2 * ((1 / 2 : ℂ) * eisensteinSeries (N := 1) 0 4 upperI)
  ring

theorem eisensteinSeries_six_eq_two_E₆ :
    eisensteinSeries (N := 1) 0 6 upperI = 2 * ModularForm.E₆ upperI := by
  change eisensteinSeries (N := 1) 0 6 upperI =
    2 * ((1 / 2 : ℂ) * eisensteinSeries (N := 1) 0 6 upperI)
  ring

theorem square_G_four_eq_E₄ :
    squarePeriodPair.G 4 =
      2 * riemannZeta (4 : ℂ) * ModularForm.E₄ upperI := by
  rw [square_G_four_eq_full_eisenstein]
  have h := tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries
    (k := 4) (by omega) upperI
  norm_num at h
  rw [h, eisensteinSeries_four_eq_two_E₄]
  ring

theorem square_G_six_eq_E₆ :
    squarePeriodPair.G 6 =
      2 * riemannZeta (6 : ℂ) * ModularForm.E₆ upperI := by
  rw [square_G_six_eq_full_eisenstein]
  have h := tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries
    (k := 6) (by omega) upperI
  norm_num at h
  rw [h, eisensteinSeries_six_eq_two_E₆]
  ring

theorem square_G_six_zero : squarePeriodPair.G 6 = 0 := by
  have h := squarePeriodPair_g₃_zero
  rw [PeriodPair.g₃] at h
  exact (mul_eq_zero.mp h).resolve_left (by norm_num)

/-- Weight-six modular symmetry vanishes at the square fixed point. -/
theorem modularForm_E₆_upperI_zero : ModularForm.E₆ upperI = 0 := by
  have hprod : 2 * riemannZeta (6 : ℂ) * ModularForm.E₆ upperI = 0 := by
    rw [← square_G_six_eq_E₆, square_G_six_zero]
  have hzeta : riemannZeta (6 : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  exact (mul_eq_zero.mp hprod).resolve_left (mul_ne_zero (by norm_num) hzeta)

/-- Modular discriminant nonvanishing forces weight four not to vanish at `i`. -/
theorem modularForm_E₄_upperI_ne_zero : ModularForm.E₄ upperI ≠ 0 := by
  intro hfour
  have hdisc := ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq upperI
  rw [hfour, modularForm_E₆_upperI_zero] at hdisc
  norm_num at hdisc
  exact ModularForm.discriminant_ne_zero upperI hdisc

theorem square_G_four_ne_zero : squarePeriodPair.G 4 ≠ 0 := by
  rw [square_G_four_eq_E₄]
  have hzeta : riemannZeta (4 : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  exact mul_ne_zero (mul_ne_zero (by norm_num) hzeta) modularForm_E₄_upperI_ne_zero

/-- The square period lattice has nonzero `g₂`. -/
theorem squarePeriodPair_g₂_ne_zero : squarePeriodPair.g₂ ≠ 0 := by
  rw [PeriodPair.g₂]
  exact mul_ne_zero (by norm_num) square_G_four_ne_zero

/-- The analytic square lattice has the exact modular invariant `1728`. -/
theorem squarePeriodPair_periodJ : periodJ squarePeriodPair = 1728 := by
  rw [periodJ, squarePeriodPair_g₃_zero]
  field_simp [squarePeriodPair_g₂_ne_zero]
  ring

/-- Discriminant of any analytic period-pair curve in short Weierstrass normalization. -/
theorem analyticWeierstrassCurve_discriminant (L : PeriodPair) :
    (analyticWeierstrassCurve L).Δ = L.g₂ ^ 3 - 27 * L.g₃ ^ 2 := by
  rw [analyticWeierstrassCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

/-- The actual analytic square-lattice Weierstrass curve is nonsingular. -/
theorem squareAnalyticCurve_discriminant_ne_zero :
    (analyticWeierstrassCurve squarePeriodPair).Δ ≠ 0 := by
  rw [analyticWeierstrassCurve_discriminant, squarePeriodPair_g₃_zero]
  norm_num
  exact squarePeriodPair_g₂_ne_zero

/-- Every nonzero scale at Brizard modulus `m = 1/2` also has `j = 1728`. -/
theorem brizard_half_modulus_parameterJ (q₀ : ℝˣ) :
    parameterJ { modulus := (1 / 2 : ℝ), q₀ := q₀ } = 1728 := by
  rw [parameterJ_eq_legendreJ, legendreJ]
  norm_num

/-- Exact modular-class match between the analytic square lattice and Brizard's half modulus. -/
theorem square_periodJ_eq_brizard_half (q₀ : ℝˣ) :
    periodJ squarePeriodPair =
      (parameterJ { modulus := (1 / 2 : ℝ), q₀ := q₀ } : ℂ) := by
  rw [squarePeriodPair_periodJ, brizard_half_modulus_parameterJ]
  norm_num

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
