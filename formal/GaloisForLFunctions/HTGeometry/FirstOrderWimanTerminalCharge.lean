import GaloisForLFunctions.HTGeometry.HahnDilation
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.LaurentSeries

/-!
# Exact nonzero terminal Wiman charge

The inner Wiman coefficient has rational slope `(M-a)/q`.  Multiplying it by the input-state
monomial adds one to that slope.  After ramification clearing, the Euler grading reads the exact
integer charge `N * (q + M - a)`.  Positivity of the Wiman charge makes its leading graded
coefficient nonzero.
-/

namespace GaloisForLFunctions.HTGeometry

open HahnSeries PowerSeries

noncomputable section

/-- Exact coefficient of the Euler grading on the input state times its prescribed Wiman
coefficient. -/
theorem coeff_hahnGrade_terminalWimanChargedCoefficient
    (M a q N : ℕ) (z₀ : PowerSeries ℂ) :
    let e : ℤ := -((N * q : ℕ) : ℤ) - (N * M : ℕ) + (N * a : ℕ)
    (hahnGrade (Int.castAddHom ℂ)
      (HahnSeries.single (-((N * q : ℕ) : ℤ)) (1 : ℂ) *
        (HahnSeries.single (-((N * M : ℕ) : ℤ)) (1 : ℂ) *
          algebraMap (PowerSeries ℂ) (LaurentSeries ℂ)
            ((PowerSeries.X : PowerSeries ℂ) ^ (N * a) * z₀)))).coeff e =
      Int.castAddHom ℂ e * PowerSeries.constantCoeff z₀ := by
  dsimp only
  rw [coeff_hahnGrade]
  simp only [HahnSeries.coeff_single_mul, one_mul]
  have hindex :
      -((N * q : ℕ) : ℤ) - (N * M : ℕ) + (N * a : ℕ) -
          -((N * q : ℕ) : ℤ) - -((N * M : ℕ) : ℤ) = (N * a : ℕ) := by
    push_cast
    ring
  change (Int.castAddHom ℂ
      (-((N * q : ℕ) : ℤ) - (N * M : ℕ) + (N * a : ℕ)) *
      (((((PowerSeries.X : PowerSeries ℂ) ^ (N * a) * z₀ : PowerSeries ℂ) :
        LaurentSeries ℂ)).coeff
          (-((N * q : ℕ) : ℤ) - (N * M : ℕ) + (N * a : ℕ) -
            -((N * q : ℕ) : ℤ) - -((N * M : ℕ) : ℤ)))) =
    Int.castAddHom ℂ
      (-((N * q : ℕ) : ℤ) - (N * M : ℕ) + (N * a : ℕ)) *
      PowerSeries.constantCoeff z₀
  rw [hindex, PowerSeries.coeff_coe,
    if_neg (not_lt_of_ge (Int.natCast_nonneg _))]
  have hnabs : ((N * a : ℕ) : ℤ).natAbs = N * a := by omega
  rw [hnabs]
  have hcoeffpow : PowerSeries.coeff (N * a)
      ((PowerSeries.X : PowerSeries ℂ) ^ (N * a) * z₀) =
        PowerSeries.constantCoeff z₀ := by
    simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using
      (PowerSeries.coeff_X_pow_mul z₀ (N * a) 0)
  rw [hcoeffpow]

/-- **The Wiman charge survives terminal-inward grading.**  If the cleared charge is positive and
the selected edge coefficient is nonzero, the Euler derivative of the exact input-times-leading
coefficient cannot vanish. -/
theorem hahnGrade_terminalWimanChargedCoefficient_ne_zero
    (M a q N : ℕ) (hN : N ≠ 0) (hcharge : a < M + q)
    (z₀ : PowerSeries ℂ) (hz₀ : PowerSeries.constantCoeff z₀ ≠ 0) :
    hahnGrade (Int.castAddHom ℂ)
      (HahnSeries.single (-((N * q : ℕ) : ℤ)) (1 : ℂ) *
        (HahnSeries.single (-((N * M : ℕ) : ℤ)) (1 : ℂ) *
          algebraMap (PowerSeries ℂ) (LaurentSeries ℂ)
            ((PowerSeries.X : PowerSeries ℂ) ^ (N * a) * z₀))) ≠ 0 := by
  let e : ℤ := -((N * q : ℕ) : ℤ) - (N * M : ℕ) + (N * a : ℕ)
  intro hzero
  have hcoeff := congrArg (fun x : LaurentSeries ℂ => x.coeff e) hzero
  rw [coeff_hahnGrade_terminalWimanChargedCoefficient] at hcoeff
  simp only [HahnSeries.coeff_zero] at hcoeff
  have hlt : N * a < N * (M + q) :=
    (Nat.mul_lt_mul_left (Nat.pos_of_ne_zero hN)).2 hcharge
  have hlt' : N * a < N * M + N * q := by
    simpa [Nat.mul_add] using hlt
  have heInt : e ≠ 0 := by
    have hltInt : ((N * a : ℕ) : ℤ) <
        ((N * M : ℕ) : ℤ) + ((N * q : ℕ) : ℤ) := by
      exact_mod_cast hlt'
    intro heq
    dsimp only [e] at heq
    linarith
  have heComplex : Int.castAddHom ℂ e ≠ 0 := by
    simpa using (Int.cast_ne_zero.mpr heInt : (e : ℂ) ≠ 0)
  exact (mul_ne_zero heComplex hz₀) hcoeff

end

end GaloisForLFunctions.HTGeometry
