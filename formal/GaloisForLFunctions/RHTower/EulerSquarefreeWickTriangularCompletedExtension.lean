import GaloisForLFunctions.RHTower.EulerSquarefreeWickPrimitiveCompletedInteraction
import GaloisForLFunctions.RHTower.EulerSquarefreeWickFreeCrossedProductDetection

/-!
# Global triangular completion of the Euler--Wick extension

The semisimple completed EWQ eigenmatrix retains orientation through a corrected Euler product
and its inverse, so it is initially confined to the Euler half-plane.  Keeping one oriented
off-diagonal instead gives a global entire matrix without any reciprocal auxiliary channel:

`T(s) = [[Xi(s), J_12(s)], [0, Xi(s)]]`.

Its determinant is exactly `Xi(s)^(2 : ℕ)`, and `T(s)^(2 : ℕ) = 0` is exactly the Xi-divisor condition.  The
same free-orbit grading used by the literal crossed-product source extracts `-2 J_12(s)` from its
commutator.  Thus orientation survives globally, but normality holds exactly where that completed
joint channel vanishes.  This is the sharp analytic orientation--normality tradeoff: a triangular
completion removes the inverse-channel divisor problem but cannot retain Hilbert normality unless
it also erases the EWQ extension.
-/

open Complex Matrix

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Entire upper-triangular extension with Xi on the diagonal and the primitive EWQ carrier in
the single oriented off-diagonal. -/
def eulerWickTriangularCompletedExtension (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![_root_.RHTower.xi s, eulerWickQuadraticPrimitiveCompletedInteraction s;
     0, _root_.RHTower.xi s]

/-- The grading which reads the single surviving EWQ orientation. -/
def eulerWickTriangularCompletedGrading : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, -1]

/-- The completed grading is literally the source free-orbit crossed-product grading after the
two reflection parities are reindexed by `Fin 2`. -/
theorem eulerWickTriangularCompletedGrading_reindexes_freeOrbit
    (p q : ReflectionParity) :
    eulerWickTriangularCompletedGrading
        (reflectionParityToFinTwo p) (reflectionParityToFinTwo q) =
      freeOrbitOrientationMatrix p q := by
  cases p <;> cases q <;>
    simp [eulerWickTriangularCompletedGrading, reflectionParityToFinTwo,
      freeOrbitOrientationMatrix, freeOrbitOrientation]

/-- Every coefficient of the triangular extension is entire. -/
theorem eulerWickTriangularCompletedExtension_entry_differentiable (i j : Fin 2) :
    Differentiable ℂ (fun s => eulerWickTriangularCompletedExtension s i j) := by
  fin_cases i <;> fin_cases j
  · simpa [eulerWickTriangularCompletedExtension] using _root_.RHTower.xi_differentiable
  · simpa [eulerWickTriangularCompletedExtension] using
      eulerWickQuadraticPrimitiveCompletedInteraction_differentiable
  · simp [eulerWickTriangularCompletedExtension]
  · simpa [eulerWickTriangularCompletedExtension] using _root_.RHTower.xi_differentiable

/-- The global triangular landing is coefficient-faithful on the Xi divisor: its determinant is
exactly Xi squared, with no auxiliary inverse or denominator. -/
theorem det_eulerWickTriangularCompletedExtension (s : ℂ) :
    (eulerWickTriangularCompletedExtension s).det = _root_.RHTower.xi s ^ (2 : ℕ) := by
  rw [Matrix.det_fin_two]
  simp [eulerWickTriangularCompletedExtension, pow_two]

/-- The triangular extension becomes square-zero exactly on the Xi divisor. -/
theorem eulerWickTriangularCompletedExtension_sq_eq_zero_iff (s : ℂ) :
    eulerWickTriangularCompletedExtension s * eulerWickTriangularCompletedExtension s = 0 ↔
      _root_.RHTower.xi s = 0 := by
  constructor
  · intro h
    have h00 := congrFun (congrFun h (0 : Fin 2)) (0 : Fin 2)
    simp [eulerWickTriangularCompletedExtension, Matrix.mul_apply,
      Fin.sum_univ_two] at h00
    exact h00
  · intro h
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [eulerWickTriangularCompletedExtension, Matrix.mul_apply,
        Fin.sum_univ_two, h]

/-- The extension itself vanishes only at a common zero of Xi and the primitive EWQ carrier. -/
theorem eulerWickTriangularCompletedExtension_ne_zero_iff (s : ℂ) :
    eulerWickTriangularCompletedExtension s ≠ 0 ↔
      _root_.RHTower.xi s ≠ 0 ∨
        eulerWickQuadraticPrimitiveCompletedInteraction s ≠ 0 := by
  constructor
  · intro h
    by_contra hright
    simp only [not_or, not_not] at hright
    apply h
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [eulerWickTriangularCompletedExtension, hright.1, hright.2]
  · rintro (hxi | hJ) <;> intro hzero
    · have h00 := congrFun (congrFun hzero (0 : Fin 2)) (0 : Fin 2)
      simp [eulerWickTriangularCompletedExtension] at h00
      exact hxi h00
    · have h01 := congrFun (congrFun hzero (0 : Fin 2)) (1 : Fin 2)
      simp [eulerWickTriangularCompletedExtension] at h01
      exact hJ h01

/-- Sharp normality obstruction: the entire triangular landing is normal exactly when its EWQ
joint channel vanishes. -/
theorem eulerWickTriangularCompletedExtension_normal_iff (s : ℂ) :
    (eulerWickTriangularCompletedExtension s)ᴴ * eulerWickTriangularCompletedExtension s =
        eulerWickTriangularCompletedExtension s * (eulerWickTriangularCompletedExtension s)ᴴ ↔
      eulerWickQuadraticPrimitiveCompletedInteraction s = 0 := by
  constructor
  · intro h
    have h00 := congrFun (congrFun h (0 : Fin 2)) (0 : Fin 2)
    simp [eulerWickTriangularCompletedExtension, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.conjTranspose_apply] at h00
    have hprod :
        (starRingEnd ℂ) (eulerWickQuadraticPrimitiveCompletedInteraction s) *
            eulerWickQuadraticPrimitiveCompletedInteraction s = 0 := by
      calc
        (starRingEnd ℂ) (eulerWickQuadraticPrimitiveCompletedInteraction s) *
              eulerWickQuadraticPrimitiveCompletedInteraction s =
            (starRingEnd ℂ) (_root_.RHTower.xi s) * _root_.RHTower.xi s -
              _root_.RHTower.xi s * (starRingEnd ℂ) (_root_.RHTower.xi s) := by
                apply eq_sub_iff_add_eq.mpr
                rw [add_comm]
                simpa only [mul_comm
                  (eulerWickQuadraticPrimitiveCompletedInteraction s)
                  ((starRingEnd ℂ) (eulerWickQuadraticPrimitiveCompletedInteraction s))] using
                    h00.symm
        _ = 0 := sub_eq_zero.mpr (mul_comm _ _)
    rw [← Complex.normSq_eq_conj_mul_self] at hprod
    exact Complex.normSq_eq_zero.mp (ofReal_injective hprod)
  · intro hJ
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [eulerWickTriangularCompletedExtension, Matrix.mul_apply,
        Fin.sum_univ_two, Matrix.conjTranspose_apply, hJ, mul_comm]

/-- The free-orbit grading commutator extracts the global primitive interaction with exact factor
`-2`, just as it does for each literal prime-depth packet. -/
theorem eulerWickTriangularCompletedExtension_orientationCommutator (s : ℂ) :
    eulerWickTriangularCompletedExtension s * eulerWickTriangularCompletedGrading -
        eulerWickTriangularCompletedGrading * eulerWickTriangularCompletedExtension s =
      !![0, -2 * eulerWickQuadraticPrimitiveCompletedInteraction s; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [eulerWickTriangularCompletedExtension, eulerWickTriangularCompletedGrading]
  all_goals ring

/-- The completed orientation detector vanishes exactly when the primitive joint carrier does. -/
theorem eulerWickTriangularCompletedExtension_orientationCommutator_eq_zero_iff (s : ℂ) :
    eulerWickTriangularCompletedExtension s * eulerWickTriangularCompletedGrading -
          eulerWickTriangularCompletedGrading * eulerWickTriangularCompletedExtension s = 0 ↔
      eulerWickQuadraticPrimitiveCompletedInteraction s = 0 := by
  rw [eulerWickTriangularCompletedExtension_orientationCommutator]
  constructor
  · intro h
    have h01 := congrFun (congrFun h (0 : Fin 2)) (1 : Fin 2)
    simpa using h01
  · intro hJ
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hJ]

/-- Normality and loss of the source free-orbit orientation are the same global equation. -/
theorem eulerWickTriangularCompletedExtension_normal_iff_orientationCommutator_zero (s : ℂ) :
    (eulerWickTriangularCompletedExtension s)ᴴ * eulerWickTriangularCompletedExtension s =
          eulerWickTriangularCompletedExtension s * (eulerWickTriangularCompletedExtension s)ᴴ ↔
      eulerWickTriangularCompletedExtension s * eulerWickTriangularCompletedGrading -
          eulerWickTriangularCompletedGrading * eulerWickTriangularCompletedExtension s = 0 := by
  rw [eulerWickTriangularCompletedExtension_normal_iff,
    eulerWickTriangularCompletedExtension_orientationCommutator_eq_zero_iff]

/-- Functional-equation reflection fixes both Xi diagonal entries and multiplies the single
oriented EWQ extension by its constant primitive root number. -/
theorem eulerWickTriangularCompletedExtension_one_sub (s : ℂ) :
    eulerWickTriangularCompletedExtension (1 - s) =
      !![_root_.RHTower.xi s,
          quadraticCharacterTwelve.rootNumber *
            eulerWickQuadraticPrimitiveCompletedInteraction s;
         0, _root_.RHTower.xi s] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eulerWickTriangularCompletedExtension, _root_.RHTower.xi_one_sub,
      eulerWickQuadraticPrimitiveCompletedInteraction_one_sub]

end

end GaloisForLFunctions.RHTower
