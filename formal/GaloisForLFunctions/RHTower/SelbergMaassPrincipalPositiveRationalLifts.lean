import GaloisForLFunctions.RHTower.SelbergMaassRationalTrace

/-!
# Positive rational lifts of principal congruence elements

Each target-group element in a principal-congruence trace is the real image of
an orientation-preserving rational matrix. This supplies the exact arithmetic
representative required to apply cusp Fourier transport to each finite trace
summand.
-/

namespace GaloisForLFunctions.RHTower

open Matrix SpecialLinearGroup GeneralLinearGroup
open scoped MatrixGroups

noncomputable section

theorem principalCongruenceGL_hasPositiveRationalLifts (N : ℕ) :
    HasPositiveRationalLifts (principalCongruenceGL N) := by
  intro γ
  obtain ⟨A, hA, hAeq⟩ := γ.2
  refine ⟨mapGL ℚ A, ?_, ?_⟩
  · have hmapA : (mapGL ℚ A).map (algebraMap ℚ ℝ) = mapGL ℝ A := by
      simpa only [one_mul, map_one] using
        rationalGL_mul_integral_real (1 : GL (Fin 2) ℚ) A
    rw [hmapA, hAeq]
  · have hmapA : (mapGL ℚ A).map (algebraMap ℚ ℝ) = mapGL ℝ A := by
      simpa only [one_mul, map_one] using
        rationalGL_mul_integral_real (1 : GL (Fin 2) ℚ) A
    rw [hmapA]
    have hdet : Matrix.GeneralLinearGroup.det (mapGL ℝ A) = 1 :=
      Matrix.SpecialLinearGroup.det_mapGL A
    have hdetval := congrArg Units.val hdet
    change 0 < (Matrix.GeneralLinearGroup.det (mapGL ℝ A)).val
    rw [hdetval]
    norm_num

end

end GaloisForLFunctions.RHTower
