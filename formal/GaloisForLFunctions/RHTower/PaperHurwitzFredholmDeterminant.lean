import GaloisForLFunctions.RHTower.PaperHurwitzWallApproach
import GaloisForLFunctions.HTGeometry.HyperbolicFredholmProduct
import GaloisForLFunctions.HTGeometry.LpDiagonalFredholmDeterminant

/-! # Exact Fredholm determinants of the native Hurwitz approach

The complete rational-Hurwitz resolvent is trace class at each approaching
source point. A fixed coupling has an exact exponentially growing Fredholm
determinant, obtained from the hyperbolic shift law on its coupling lattice.
-/

namespace RHTower
noncomputable section
open GaloisForLFunctions GaloisForLFunctions.HTGeometry HilbertSchmidt

def paperHurwitzApproachStep (N : ℕ) : ℝ := Real.log 2 / ((N : ℝ) + 3)

theorem paperHurwitzApproachStep_pos (N : ℕ) : 0 < paperHurwitzApproachStep N :=
  div_pos (Real.log_pos (by norm_num)) (by positivity)

theorem paperHurwitzApproach_regularizer_hyperbolic (t : ℝ) (N k : ℕ) :
    paperHurwitzRegularizer (paperHurwitzApproachPoint t N) k =
      hyperbolicResolventWeight (paperHurwitzApproachStep N) k := by
  simp only [paperHurwitzRegularizer, paperHurwitzPowerEnergy_eq_sinh,
    paperHurwitzApproachPoint_re, add_sub_cancel_left, hyperbolicResolventWeight,
    Real.cosh_sq', paperHurwitzApproachStep, div_eq_mul_inv]
  congr 4
  ring

theorem paperHurwitzApproach_resolvent_traceClass (t : ℝ) (N : ℕ) :
    MemSchattenClass 1 (paperHurwitzResolvent (paperHurwitzApproachPoint t N)) := by
  rw [paperHurwitzResolvent_eq_diagonal, memSchattenClass_lpDiagonalCLM_iff _ _ _ zero_lt_one]
  simpa only [Real.rpow_one, paperHurwitzApproach_regularizer_hyperbolic,
    Complex.norm_real, Real.norm_of_nonneg (hyperbolicResolventWeight_pos _ _).le] using
      summable_hyperbolicResolventWeight (paperHurwitzApproachStep_pos N)

private def coefficient (N : ℕ) (b : ℝ) (k : ℕ) : ℂ :=
  ((Real.sinh b ^ 2 * hyperbolicResolventWeight (paperHurwitzApproachStep N) k : ℝ) : ℂ)

private theorem coefficient_bound (N : ℕ) (b : ℝ) (k : ℕ) :
    ‖coefficient N b k‖ ≤ Real.sinh b ^ 2 := by
  rw [coefficient, Complex.norm_real, Real.norm_of_nonneg
    (mul_nonneg (sq_nonneg _) (hyperbolicResolventWeight_pos _ _).le)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (hyperbolicResolventWeight_le_one (paperHurwitzApproachStep N) k) (sq_nonneg (Real.sinh b))

private theorem coefficient_summable (N : ℕ) (b : ℝ) :
    Summable (fun k => ‖coefficient N b k‖) := by
  simpa only [coefficient, Complex.norm_real, Real.norm_of_nonneg
    (mul_nonneg (sq_nonneg _) (hyperbolicResolventWeight_pos _ _).le)] using
      (summable_hyperbolicResolventWeight (paperHurwitzApproachStep_pos N)).mul_left
        (Real.sinh b ^ 2)

private theorem scaled_resolvent_diagonal (t : ℝ) (N : ℕ) (b : ℝ) :
    (((Real.sinh b ^ 2 : ℝ) : ℂ) • paperHurwitzResolvent (paperHurwitzApproachPoint t N)) =
      lpDiagonalCLM (coefficient N b) (sq_nonneg _) (coefficient_bound N b) := by
  ext f k
  change ((Real.sinh b ^ 2 : ℝ) : ℂ) *
      ((paperHurwitzRegularizer (paperHurwitzApproachPoint t N) k : ℂ) * f k) =
    coefficient N b k * f k
  rw [paperHurwitzApproach_regularizer_hyperbolic, coefficient, Complex.ofReal_mul, mul_assoc]

theorem paperHurwitzApproach_fredholmDet_sinh (t : ℝ) (N : ℕ) (b : ℝ) :
    fredholmDetOp (lpBasis ℕ)
      (((Real.sinh b ^ 2 : ℝ) : ℂ) • paperHurwitzResolvent (paperHurwitzApproachPoint t N)) =
        (hyperbolicFredholmProduct (paperHurwitzApproachStep N) b : ℂ) := by
  have hp := (hasProd_hyperbolicFredholmFactor (paperHurwitzApproachStep_pos N) b).map
    Complex.ofRealHom Complex.continuous_ofReal
  have hp' : HasProd (fun k => 1 + coefficient N b k)
      (hyperbolicFredholmProduct (paperHurwitzApproachStep N) b : ℂ) := by
    refine hp.congr_fun fun k => ?_
    change 1 + ((Real.sinh b ^ 2 * hyperbolicResolventWeight (paperHurwitzApproachStep N) k : ℝ) : ℂ) =
      ((1 + Real.sinh b ^ 2 * hyperbolicResolventWeight (paperHurwitzApproachStep N) k : ℝ) : ℂ)
    push_cast
    rfl
  rw [scaled_resolvent_diagonal]
  exact fredholmDetOp_lpDiagonalCLM_of_hasProd _ _ _ (coefficient_summable N b) hp'

theorem paperHurwitzApproach_fredholmDet_lattice (t : ℝ) (N m : ℕ) :
    fredholmDetOp (lpBasis ℕ)
      (((Real.sinh (m * paperHurwitzApproachStep N) ^ 2 : ℝ) : ℂ) •
        paperHurwitzResolvent (paperHurwitzApproachPoint t N)) =
      ((Real.cosh (m * paperHurwitzApproachStep N) *
        Real.exp ((m : ℝ) ^ 2 * paperHurwitzApproachStep N) : ℝ) : ℂ) := by
  rw [paperHurwitzApproach_fredholmDet_sinh,
    hyperbolicFredholmProduct_nat_mul (paperHurwitzApproachStep_pos N)]

theorem paperHurwitzApproach_fredholmDet_exact (t : ℝ) (N : ℕ) :
    fredholmDetOp (lpBasis ℕ)
      ((9 / 16 : ℂ) • paperHurwitzResolvent (paperHurwitzApproachPoint t N)) =
        ((5 / 4 : ℂ) * 2 ^ (N + 3)) := by
  have h := paperHurwitzApproach_fredholmDet_lattice t N (N + 3)
  have ha : ((N + 3 : ℕ) : ℝ) * paperHurwitzApproachStep N = Real.log 2 := by
    dsimp only [paperHurwitzApproachStep]
    push_cast
    field_simp
  have hb : (((N + 3 : ℕ) : ℝ) ^ 2) * paperHurwitzApproachStep N =
      ((N + 3 : ℕ) : ℝ) * Real.log 2 := by
    rw [sq, mul_assoc, ha]
  have hs : Real.sinh (Real.log 2) ^ 2 = 9 / 16 := by
    rw [Real.sinh_log (by norm_num)]
    norm_num
  have hc : Real.cosh (Real.log 2) = 5 / 4 := by
    rw [Real.cosh_log (by norm_num)]
    norm_num
  rw [ha, hs, hc, hb, Real.exp_nat_mul, Real.exp_log (by norm_num)] at h
  simpa only [Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_mul,
    Complex.ofReal_pow] using h

end
end RHTower
