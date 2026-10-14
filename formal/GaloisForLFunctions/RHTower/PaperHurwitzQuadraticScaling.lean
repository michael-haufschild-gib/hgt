import GaloisForLFunctions.RHTower.PaperHurwitzFredholmNormEscape

/-! # Quadratic source scaling for native Hurwitz determinants

The prescribed quadratic source index supports every natural coupling index.
Its actual operator determinant separates the normalized index from the
shrinking source spacing, exposing the scale needed for finite limits.
-/

namespace RHTower
noncomputable section
open GaloisForLFunctions GaloisForLFunctions.HTGeometry HilbertSchmidt

/-- Polynomial form of `(N+3)^2-3`. -/
def paperHurwitzQuadraticIndex (N : ℕ) : ℕ := N ^ 2 + 6 * N + 6

theorem paperHurwitzQuadratic_step (N : ℕ) :
    paperHurwitzApproachStep (paperHurwitzQuadraticIndex N) =
      Real.log 2 / ((N : ℝ) + 3) ^ 2 := by
  unfold paperHurwitzApproachStep paperHurwitzQuadraticIndex
  push_cast
  congr 1
  ring

def paperHurwitzQuadraticAngle (N m : ℕ) : ℝ :=
  (m : ℝ) * paperHurwitzApproachStep (paperHurwitzQuadraticIndex N)

theorem paperHurwitzQuadraticAngle_eq (N m : ℕ) :
    paperHurwitzQuadraticAngle N m =
      ((m : ℝ) / ((N : ℝ) + 3)) * paperHurwitzApproachStep N := by
  rw [paperHurwitzQuadraticAngle, paperHurwitzQuadratic_step, paperHurwitzApproachStep]
  field_simp [show (N : ℝ) + 3 ≠ 0 by positivity]

theorem paperHurwitzQuadratic_exponent_eq (N m : ℕ) :
    (m : ℝ) ^ 2 * paperHurwitzApproachStep (paperHurwitzQuadraticIndex N) =
      ((m : ℝ) / ((N : ℝ) + 3)) ^ 2 * Real.log 2 := by
  rw [paperHurwitzQuadratic_step]
  field_simp [show (N : ℝ) + 3 ≠ 0 by positivity]

def paperHurwitzQuadraticPerturbation (t : ℝ) (N m : ℕ) :
    PaperHurwitzHistory →L[ℂ] PaperHurwitzHistory :=
  ((Real.sinh (paperHurwitzQuadraticAngle N m) ^ 2 : ℝ) : ℂ) •
    paperHurwitzResolvent (paperHurwitzApproachPoint t (paperHurwitzQuadraticIndex N))

def paperHurwitzQuadraticFredholmValue (t : ℝ) (N m : ℕ) : ℂ :=
  fredholmDetOp (lpBasis ℕ) (paperHurwitzQuadraticPerturbation t N m)

theorem paperHurwitzQuadraticPerturbation_traceClass (t : ℝ) (N m : ℕ) :
    MemSchattenClass 1 (paperHurwitzQuadraticPerturbation t N m) :=
  memSchattenClass_one_smul
    (paperHurwitzApproach_resolvent_traceClass t (paperHurwitzQuadraticIndex N)) _

theorem paperHurwitzQuadraticPerturbation_compact (t : ℝ) (N m : ℕ) :
    IsCompactOperator (paperHurwitzQuadraticPerturbation t N m) := by
  change IsCompactOperator (fun f : PaperHurwitzHistory =>
    ((Real.sinh (paperHurwitzQuadraticAngle N m) ^ 2 : ℝ) : ℂ) •
      paperHurwitzResolvent (paperHurwitzApproachPoint t (paperHurwitzQuadraticIndex N)) f)
  exact ((paperHurwitzResolvent_compact_iff _).mpr
    (paperHurwitzApproachPoint_off_wall t (paperHurwitzQuadraticIndex N))).smul
      ((Real.sinh (paperHurwitzQuadraticAngle N m) ^ 2 : ℝ) : ℂ)

theorem norm_paperHurwitzQuadraticPerturbation (t : ℝ) (N m : ℕ) :
    ‖paperHurwitzQuadraticPerturbation t N m‖ =
      Real.sinh (paperHurwitzQuadraticAngle N m) ^ 2 := by
  rw [paperHurwitzQuadraticPerturbation, norm_smul, norm_paperHurwitzResolvent, mul_one,
    Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]

theorem paperHurwitzQuadraticFredholmValue_exact (t : ℝ) (N m : ℕ) :
    paperHurwitzQuadraticFredholmValue t N m =
      ((Real.cosh (paperHurwitzQuadraticAngle N m) *
        Real.exp (((m : ℝ) / ((N : ℝ) + 3)) ^ 2 * Real.log 2) : ℝ) : ℂ) := by
  have h := paperHurwitzApproach_fredholmDet_lattice t (paperHurwitzQuadraticIndex N) m
  rw [paperHurwitzQuadratic_exponent_eq] at h
  exact h

theorem paperHurwitzQuadraticFredholmValue_re_ge_one (t : ℝ) (N m : ℕ) :
    1 ≤ (paperHurwitzQuadraticFredholmValue t N m).re := by
  rw [paperHurwitzQuadraticFredholmValue_exact, Complex.ofReal_re]
  have hc := Real.one_le_cosh (paperHurwitzQuadraticAngle N m)
  have he : 1 ≤ Real.exp (((m : ℝ) / ((N : ℝ) + 3)) ^ 2 * Real.log 2) := by
    rw [← Real.exp_zero, Real.exp_le_exp]
    exact mul_nonneg (sq_nonneg _) (Real.log_pos (by norm_num)).le
  nlinarith [mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr he)]

theorem paperHurwitzQuadraticFredholmValue_im (t : ℝ) (N m : ℕ) :
    (paperHurwitzQuadraticFredholmValue t N m).im = 0 := by
  rw [paperHurwitzQuadraticFredholmValue_exact, Complex.ofReal_im]

end
end RHTower
