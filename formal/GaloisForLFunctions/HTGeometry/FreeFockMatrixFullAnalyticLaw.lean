import GaloisForLFunctions.HTGeometry.FreeFockMatrixValuedSpectralLaw
import GaloisForLFunctions.HTGeometry.MatrixSemicircleAnalyticLaw

/-!
# Full vector analytic law of a finite matrix semicircle

Every internal-vector moment series is a finite quadratic combination of the algebraic matrix
Dyson branch.  Consequently every vector spectral measure has an algebraic Stieltjes transform.
If the matrix atom mass vanishes, all vector measures are atomless and hence absolutely continuous.
-/

open scoped BigOperators Matrix LaurentSeries RatFunc
open Filter Topology Matrix MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]

/-- Quadratic evaluation of the formal matrix Dyson branch in an arbitrary internal vector. -/
def matrixDysonFormalVectorSeries
    (A : K → Matrix I I ℂ) (x : I → ℂ) : PowerSeries ℂ :=
  ∑ i : I, ∑ j : I,
    PowerSeries.C (star (x i) * x j) * matrixDysonFormalSeries A i j

omit [DecidableEq K] in
theorem matrixDysonFormalVectorSeriesLaurent_isIntegral_ratFunc
    (A : K → Matrix I I ℂ) (x : I → ℂ) :
    IsIntegral (RatFunc ℂ)
      ((matrixDysonFormalVectorSeries A x : PowerSeries ℂ) : LaurentSeries ℂ) := by
  rw [matrixDysonFormalVectorSeries, map_sum]
  apply IsIntegral.sum
  intro i _hi
  rw [map_sum]
  apply IsIntegral.sum
  intro j _hj
  rw [map_mul]
  let c : ℂ := star (x i) * x j
  change IsIntegral (RatFunc ℂ)
    (((PowerSeries.C c : PowerSeries ℂ) : LaurentSeries ℂ) *
      ((matrixDysonFormalSeries A i j : PowerSeries ℂ) : LaurentSeries ℂ))
  have hc : IsIntegral (RatFunc ℂ)
      (algebraMap (RatFunc ℂ) (LaurentSeries ℂ)
        (algebraMap ℂ (RatFunc ℂ) c)) := isIntegral_algebraMap
  have hcTower : IsIntegral (RatFunc ℂ)
      (algebraMap ℂ (LaurentSeries ℂ) c) := by
    rw [IsScalarTower.algebraMap_apply ℂ (RatFunc ℂ) (LaurentSeries ℂ)]
    exact hc
  have hC : ((PowerSeries.C c : PowerSeries ℂ) : LaurentSeries ℂ) =
      algebraMap ℂ (LaurentSeries ℂ) c := by
    rw [← PowerSeries.algebraMap_apply]
    exact (IsScalarTower.algebraMap_apply ℂ (PowerSeries ℂ)
      (LaurentSeries ℂ) c).symm
  have hc' : IsIntegral (RatFunc ℂ)
      (((PowerSeries.C c : PowerSeries ℂ) : LaurentSeries ℂ)) := by
    rw [hC]
    exact hcTower
  exact hc'.mul
    (matrixDysonFormalSeriesLaurent_isIntegral_ratFunc A i j)

omit [DecidableEq K] in
theorem matrixDysonFormalVectorSeries_exists_bivariateRelation
    (A : K → Matrix I I ℂ) (x : I → ℂ) :
    ∃ P : Polynomial (Polynomial ℂ), P.leadingCoeff ≠ 0 ∧
      P.eval₂ Polynomial.coeToPowerSeries.ringHom
        (matrixDysonFormalVectorSeries A x) = 0 :=
  powerSeries_bivariateRelation_of_ratFuncIntegral _
    (matrixDysonFormalVectorSeriesLaurent_isIntegral_ratFunc A x)

theorem freeFockVectorMoment_odd
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (x : I → ℂ) (n : ℕ) :
    freeFockVectorMoment A x (2 * n + 1) = 0 := by
  rw [freeFockVectorMoment]
  simp only [freeFockVacuumSuperposition, freeFockPowerSuperposition,
    freeFockInner_finset_sum_left, freeFockInner_finset_sum_right,
    freeFockInner_smul_left, freeFockInner_smul_right,
    freeFockInner_vacuum_left]
  simp_rw [freeFockPower_vacuumCoefficient_odd A hA]
  simp

theorem coeff_matrixDysonFormalVectorSeries
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (x : I → ℂ) (n : ℕ) :
    PowerSeries.coeff n (matrixDysonFormalVectorSeries A x) =
      (freeFockVectorMoment A x (2 * n) : ℂ) := by
  have hinner :
      freeFockInner (freeFockVacuumSuperposition x)
          (freeFockPowerSuperposition A x (2 * n)) =
        (freeFockVectorMoment A x (2 * n) : ℂ) := by
    have hp := freeFockInner_powerSuperposition A hA x n n
    rw [show n + n = 2 * n by omega] at hp
    calc
      freeFockInner (freeFockVacuumSuperposition x)
          (freeFockPowerSuperposition A x (2 * n)) =
          freeFockInner (freeFockPowerSuperposition A x n)
            (freeFockPowerSuperposition A x n) := hp.symm
      _ = ((freeFockInner (freeFockPowerSuperposition A x n)
            (freeFockPowerSuperposition A x n)).re : ℂ) := by
        simpa only [freeFockInner] using
          freeFockInner_self_eq_ofReal_re (freeFockPowerSuperposition A x n)
      _ = (freeFockVectorMoment A x (2 * n) : ℂ) := by
        rw [freeFockVectorMoment, hp]
  rw [matrixDysonFormalVectorSeries, map_sum]
  simp only [map_sum, PowerSeries.coeff_C_mul, coeff_matrixDysonFormalSeries]
  rw [← hinner]
  simp only [freeFockVacuumSuperposition, freeFockPowerSuperposition,
    freeFockInner_finset_sum_left, freeFockInner_finset_sum_right,
    freeFockInner_smul_left, freeFockInner_smul_right,
    freeFockInner_vacuum_left]
  simp_rw [Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  rw [← freeFockPower_vacuumCoefficient_even A hA n i j]
  ring

theorem matrixDysonFormalVectorSeries_coeff_bound
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (x : I → ℂ) (n : ℕ) :
    ‖PowerSeries.coeff n (matrixDysonFormalVectorSeries A x)‖ ≤
      (∑ i : I, Complex.normSq (x i)) *
        (freeFockMatrixSpectralRadius A ^ 2) ^ n := by
  rw [coeff_matrixDysonFormalVectorSeries A hA]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  have hnonneg : 0 ≤ freeFockVectorMoment A x (2 * n) := by
    rw [freeFockVectorMoment_even_eq_inner A hA]
    exact re_freeFockInner_self_nonneg _
  rw [abs_of_nonneg hnonneg]
  simpa [pow_mul] using freeFockVectorMoment_even_le_matrixRadius A hA x n

theorem matrixDysonFormalVectorSeries_absoluteSummableAt
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (x : I → ℂ) (u : ℂ)
    (hu : freeFockMatrixSpectralRadius A ^ 2 * ‖u‖ < 1) :
    (matrixDysonFormalVectorSeries A x).AbsoluteSummableAt u := by
  let q : ℝ := freeFockMatrixSpectralRadius A ^ 2 * ‖u‖
  let c : ℝ := ∑ i : I, Complex.normSq (x i)
  have hq0 : 0 ≤ q := by positivity
  have hc0 : 0 ≤ c := Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have hqnorm : ‖q‖ < 1 := by
    simpa [q, Real.norm_eq_abs, abs_of_nonneg hq0] using hu
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    ((summable_geometric_of_norm_lt_one hqnorm).mul_left c)
  calc
    ‖PowerSeries.coeff n (matrixDysonFormalVectorSeries A x) * u ^ n‖ ≤
        (c * (freeFockMatrixSpectralRadius A ^ 2) ^ n) * ‖u ^ n‖ := by
      rw [norm_mul]
      gcongr
      exact matrixDysonFormalVectorSeries_coeff_bound A hA x n
    _ = c * q ^ n := by simp [q, norm_pow, mul_pow]; ring

end

end GaloisForLFunctions.HTGeometry
