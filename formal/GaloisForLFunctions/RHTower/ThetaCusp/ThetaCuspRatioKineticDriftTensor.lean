import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticDriftMoments2
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticDriftMoments4
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticDriftMoments6
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticDriftMoments8
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticDriftMoments10
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticDriftReader
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity


theorem scalar_coeff_mul (P Q : Polynomial ℂ) (b : ℕ) :
    (P*Q).coeff b=∑ a ∈ Finset.range (b+1),P.coeff a*Q.coeff (b-a) := by
  rw [Polynomial.coeff_mul]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => P.coeff i*Q.coeff j) b

def kineticDriftCell (h : ℂ) (P : KineticPolynomial) (j b : ℕ) : ℂ :=
  (driftReader h (P.coeff j)).coeff b

theorem kineticDriftCell_add (h : ℂ) (P Q : KineticPolynomial) (j b : ℕ) :
    kineticDriftCell h (P+Q) j b=kineticDriftCell h P j b+kineticDriftCell h Q j b := by
  simp only [kineticDriftCell,Polynomial.coeff_add,map_add]

theorem kineticDriftCell_neg (h : ℂ) (P : KineticPolynomial) (j b : ℕ) :
    kineticDriftCell h (-P) j b= -kineticDriftCell h P j b := by
  simp only [kineticDriftCell,Polynomial.coeff_neg,map_neg]

theorem kineticDriftCell_sub (h : ℂ) (P Q : KineticPolynomial) (j b : ℕ) :
    kineticDriftCell h (P-Q) j b=kineticDriftCell h P j b-kineticDriftCell h Q j b := by
  simp only [kineticDriftCell,Polynomial.coeff_sub,map_sub]

theorem kineticDriftCell_nat_mul (h : ℂ) (n : ℕ) (P : KineticPolynomial) (j b : ℕ) :
    kineticDriftCell h ((n:KineticPolynomial)*P) j b=(n:ℂ)*kineticDriftCell h P j b := by
  simp only [kineticDriftCell,Polynomial.coeff_natCast_mul,map_mul,_root_.map_natCast]

theorem kineticDriftCell_mul (h : ℂ) (P Q : KineticPolynomial) (j b : ℕ) :
    kineticDriftCell h (P*Q) j b=
      ∑ a ∈ Finset.range (j+1), ∑ c ∈ Finset.range (b+1),
        kineticDriftCell h P a c*kineticDriftCell h Q (j-a) (b-c) := by
  simp only [kineticDriftCell,kinetic_coeff_mul,map_sum,map_mul,
    Polynomial.finsetSum_coeff,scalar_coeff_mul]

theorem kineticDriftMoment2Coeff0_rows (h : ℂ) (b : ℕ) :
    (driftReader h clearMoment2KineticCoeff0).coeff b=
      (if b=0 then (kineticDriftMoment2Coeff0Row0Norm h).val else 0) + (if b=1 then (kineticDriftMoment2Coeff0Row1Norm h).val else 0) := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h clearMoment2KineticCoeff0)
    (n := 2) (by have := clearMoment2KineticCoeff0_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  simpa only [(kineticDriftMoment2Coeff0Row0Norm h).property,(kineticDriftMoment2Coeff0Row1Norm h).property] using he

theorem kineticDriftMoment2Coeff1_rows (h : ℂ) (b : ℕ) :
    (driftReader h clearMoment2KineticCoeff1).coeff b=
      (if b=0 then (kineticDriftMoment2Coeff1Row0Norm h).val else 0) + (if b=1 then (kineticDriftMoment2Coeff1Row1Norm h).val else 0) := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h clearMoment2KineticCoeff1)
    (n := 2) (by have := clearMoment2KineticCoeff1_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  simpa only [(kineticDriftMoment2Coeff1Row0Norm h).property,(kineticDriftMoment2Coeff1Row1Norm h).property] using he

theorem kineticDriftMoment2Coeff2_rows (h : ℂ) (b : ℕ) :
    (driftReader h clearMoment2KineticCoeff2).coeff b=
      (if b=0 then (kineticDriftMoment2Coeff2Row0Norm h).val else 0) + (if b=1 then (kineticDriftMoment2Coeff2Row1Norm h).val else 0) := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h clearMoment2KineticCoeff2)
    (n := 2) (by have := clearMoment2KineticCoeff2_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  simpa only [(kineticDriftMoment2Coeff2Row0Norm h).property,(kineticDriftMoment2Coeff2Row1Norm h).property] using he


theorem kineticDriftMoment4Coeff0_rows (h : ℂ) (b : ℕ) :
    (driftReader h clearMoment4KineticCoeff0).coeff b=
      (if b=0 then (kineticDriftMoment4Coeff0Row0Norm h).val else 0) + (if b=1 then (kineticDriftMoment4Coeff0Row1Norm h).val else 0) + (if b=2 then (kineticDriftMoment4Coeff0Row2Norm h).val else 0) := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h clearMoment4KineticCoeff0)
    (n := 3) (by have := clearMoment4KineticCoeff0_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  simpa only [(kineticDriftMoment4Coeff0Row0Norm h).property,(kineticDriftMoment4Coeff0Row1Norm h).property,(kineticDriftMoment4Coeff0Row2Norm h).property] using he

theorem kineticDriftMoment4Coeff1_rows (h : ℂ) (b : ℕ) :
    (driftReader h clearMoment4KineticCoeff1).coeff b=
      (if b=0 then (kineticDriftMoment4Coeff1Row0Norm h).val else 0) + (if b=1 then (kineticDriftMoment4Coeff1Row1Norm h).val else 0) + (if b=2 then (kineticDriftMoment4Coeff1Row2Norm h).val else 0) := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h clearMoment4KineticCoeff1)
    (n := 3) (by have := clearMoment4KineticCoeff1_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  simpa only [(kineticDriftMoment4Coeff1Row0Norm h).property,(kineticDriftMoment4Coeff1Row1Norm h).property,(kineticDriftMoment4Coeff1Row2Norm h).property] using he

theorem kineticDriftMoment4Coeff2_rows (h : ℂ) (b : ℕ) :
    (driftReader h clearMoment4KineticCoeff2).coeff b=
      (if b=0 then (kineticDriftMoment4Coeff2Row0Norm h).val else 0) + (if b=1 then (kineticDriftMoment4Coeff2Row1Norm h).val else 0) + (if b=2 then (kineticDriftMoment4Coeff2Row2Norm h).val else 0) := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h clearMoment4KineticCoeff2)
    (n := 3) (by have := clearMoment4KineticCoeff2_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  simpa only [(kineticDriftMoment4Coeff2Row0Norm h).property,(kineticDriftMoment4Coeff2Row1Norm h).property,(kineticDriftMoment4Coeff2Row2Norm h).property] using he

theorem kineticDriftMoment4Coeff3_rows (h : ℂ) (b : ℕ) :
    (driftReader h clearMoment4KineticCoeff3).coeff b=
      (if b=0 then (kineticDriftMoment4Coeff3Row0Norm h).val else 0) + (if b=1 then (kineticDriftMoment4Coeff3Row1Norm h).val else 0) + (if b=2 then (kineticDriftMoment4Coeff3Row2Norm h).val else 0) := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h clearMoment4KineticCoeff3)
    (n := 3) (by have := clearMoment4KineticCoeff3_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  simpa only [(kineticDriftMoment4Coeff3Row0Norm h).property,(kineticDriftMoment4Coeff3Row1Norm h).property,(kineticDriftMoment4Coeff3Row2Norm h).property] using he

theorem kineticDriftMoment4Coeff4_rows (h : ℂ) (b : ℕ) :
    (driftReader h clearMoment4KineticCoeff4).coeff b=
      (if b=0 then (kineticDriftMoment4Coeff4Row0Norm h).val else 0) + (if b=1 then (kineticDriftMoment4Coeff4Row1Norm h).val else 0) + (if b=2 then (kineticDriftMoment4Coeff4Row2Norm h).val else 0) := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h clearMoment4KineticCoeff4)
    (n := 3) (by have := clearMoment4KineticCoeff4_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  simpa only [(kineticDriftMoment4Coeff4Row0Norm h).property,(kineticDriftMoment4Coeff4Row1Norm h).property,(kineticDriftMoment4Coeff4Row2Norm h).property] using he


theorem kineticDriftMoment6Coeff0_rows (h : ℂ) (b : ℕ) :
    (driftReader h clearMoment6KineticCoeff0).coeff b=
      (if b=0 then (kineticDriftMoment6Coeff0Row0Norm h).val else 0) + (if b=1 then (kineticDriftMoment6Coeff0Row1Norm h).val else 0) + (if b=2 then (kineticDriftMoment6Coeff0Row2Norm h).val else 0) + (if b=3 then (kineticDriftMoment6Coeff0Row3Norm h).val else 0) := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h clearMoment6KineticCoeff0)
    (n := 4) (by have := clearMoment6KineticCoeff0_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  simpa only [(kineticDriftMoment6Coeff0Row0Norm h).property,(kineticDriftMoment6Coeff0Row1Norm h).property,(kineticDriftMoment6Coeff0Row2Norm h).property,(kineticDriftMoment6Coeff0Row3Norm h).property] using he

theorem kineticDriftMoment6Coeff1_rows (h : ℂ) (b : ℕ) :
    (driftReader h clearMoment6KineticCoeff1).coeff b=
      (if b=0 then (kineticDriftMoment6Coeff1Row0Norm h).val else 0) + (if b=1 then (kineticDriftMoment6Coeff1Row1Norm h).val else 0) + (if b=2 then (kineticDriftMoment6Coeff1Row2Norm h).val else 0) + (if b=3 then (kineticDriftMoment6Coeff1Row3Norm h).val else 0) := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h clearMoment6KineticCoeff1)
    (n := 4) (by have := clearMoment6KineticCoeff1_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  simpa only [(kineticDriftMoment6Coeff1Row0Norm h).property,(kineticDriftMoment6Coeff1Row1Norm h).property,(kineticDriftMoment6Coeff1Row2Norm h).property,(kineticDriftMoment6Coeff1Row3Norm h).property] using he

theorem kineticDriftMoment6Coeff2_rows (h : ℂ) (b : ℕ) :
    (driftReader h clearMoment6KineticCoeff2).coeff b=
      (if b=0 then (kineticDriftMoment6Coeff2Row0Norm h).val else 0) + (if b=1 then (kineticDriftMoment6Coeff2Row1Norm h).val else 0) + (if b=2 then (kineticDriftMoment6Coeff2Row2Norm h).val else 0) + (if b=3 then (kineticDriftMoment6Coeff2Row3Norm h).val else 0) := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h clearMoment6KineticCoeff2)
    (n := 4) (by have := clearMoment6KineticCoeff2_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  simpa only [(kineticDriftMoment6Coeff2Row0Norm h).property,(kineticDriftMoment6Coeff2Row1Norm h).property,(kineticDriftMoment6Coeff2Row2Norm h).property,(kineticDriftMoment6Coeff2Row3Norm h).property] using he

theorem kineticDriftMoment6Coeff3_rows (h : ℂ) (b : ℕ) :
    (driftReader h clearMoment6KineticCoeff3).coeff b=
      (if b=0 then (kineticDriftMoment6Coeff3Row0Norm h).val else 0) + (if b=1 then (kineticDriftMoment6Coeff3Row1Norm h).val else 0) + (if b=2 then (kineticDriftMoment6Coeff3Row2Norm h).val else 0) + (if b=3 then (kineticDriftMoment6Coeff3Row3Norm h).val else 0) := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h clearMoment6KineticCoeff3)
    (n := 4) (by have := clearMoment6KineticCoeff3_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  simpa only [(kineticDriftMoment6Coeff3Row0Norm h).property,(kineticDriftMoment6Coeff3Row1Norm h).property,(kineticDriftMoment6Coeff3Row2Norm h).property,(kineticDriftMoment6Coeff3Row3Norm h).property] using he

theorem kineticDriftMoment6Coeff4_rows (h : ℂ) (b : ℕ) :
    (driftReader h clearMoment6KineticCoeff4).coeff b=
      (if b=0 then (kineticDriftMoment6Coeff4Row0Norm h).val else 0) + (if b=1 then (kineticDriftMoment6Coeff4Row1Norm h).val else 0) + (if b=2 then (kineticDriftMoment6Coeff4Row2Norm h).val else 0) + (if b=3 then (kineticDriftMoment6Coeff4Row3Norm h).val else 0) := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h clearMoment6KineticCoeff4)
    (n := 4) (by have := clearMoment6KineticCoeff4_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  simpa only [(kineticDriftMoment6Coeff4Row0Norm h).property,(kineticDriftMoment6Coeff4Row1Norm h).property,(kineticDriftMoment6Coeff4Row2Norm h).property,(kineticDriftMoment6Coeff4Row3Norm h).property] using he

theorem kineticDriftMoment6Coeff5_rows (h : ℂ) (b : ℕ) :
    (driftReader h clearMoment6KineticCoeff5).coeff b=
      (if b=0 then (kineticDriftMoment6Coeff5Row0Norm h).val else 0) + (if b=1 then (kineticDriftMoment6Coeff5Row1Norm h).val else 0) + (if b=2 then (kineticDriftMoment6Coeff5Row2Norm h).val else 0) + (if b=3 then (kineticDriftMoment6Coeff5Row3Norm h).val else 0) := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h clearMoment6KineticCoeff5)
    (n := 4) (by have := clearMoment6KineticCoeff5_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  simpa only [(kineticDriftMoment6Coeff5Row0Norm h).property,(kineticDriftMoment6Coeff5Row1Norm h).property,(kineticDriftMoment6Coeff5Row2Norm h).property,(kineticDriftMoment6Coeff5Row3Norm h).property] using he

theorem kineticDriftMoment6Coeff6_rows (h : ℂ) (b : ℕ) :
    (driftReader h clearMoment6KineticCoeff6).coeff b=
      (if b=0 then (kineticDriftMoment6Coeff6Row0Norm h).val else 0) + (if b=1 then (kineticDriftMoment6Coeff6Row1Norm h).val else 0) + (if b=2 then (kineticDriftMoment6Coeff6Row2Norm h).val else 0) + (if b=3 then (kineticDriftMoment6Coeff6Row3Norm h).val else 0) := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h clearMoment6KineticCoeff6)
    (n := 4) (by have := clearMoment6KineticCoeff6_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  simpa only [(kineticDriftMoment6Coeff6Row0Norm h).property,(kineticDriftMoment6Coeff6Row1Norm h).property,(kineticDriftMoment6Coeff6Row2Norm h).property,(kineticDriftMoment6Coeff6Row3Norm h).property] using he


theorem kineticDriftMoment8Coeff0_rows (h : ℂ) (b : ℕ) :
    (driftReader h clearMoment8KineticCoeff0).coeff b=
      (if b=0 then (kineticDriftMoment8Coeff0Row0Norm h).val else 0) + (if b=1 then (kineticDriftMoment8Coeff0Row1Norm h).val else 0) + (if b=2 then (kineticDriftMoment8Coeff0Row2Norm h).val else 0) + (if b=3 then (kineticDriftMoment8Coeff0Row3Norm h).val else 0) + (if b=4 then (kineticDriftMoment8Coeff0Row4Norm h).val else 0) := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h clearMoment8KineticCoeff0)
    (n := 5) (by have := clearMoment8KineticCoeff0_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  simpa only [(kineticDriftMoment8Coeff0Row0Norm h).property,(kineticDriftMoment8Coeff0Row1Norm h).property,(kineticDriftMoment8Coeff0Row2Norm h).property,(kineticDriftMoment8Coeff0Row3Norm h).property,(kineticDriftMoment8Coeff0Row4Norm h).property] using he

theorem kineticDriftMoment8Coeff1_rows (h : ℂ) (b : ℕ) :
    (driftReader h clearMoment8KineticCoeff1).coeff b=
      (if b=0 then (kineticDriftMoment8Coeff1Row0Norm h).val else 0) + (if b=1 then (kineticDriftMoment8Coeff1Row1Norm h).val else 0) + (if b=2 then (kineticDriftMoment8Coeff1Row2Norm h).val else 0) + (if b=3 then (kineticDriftMoment8Coeff1Row3Norm h).val else 0) + (if b=4 then (kineticDriftMoment8Coeff1Row4Norm h).val else 0) := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h clearMoment8KineticCoeff1)
    (n := 5) (by have := clearMoment8KineticCoeff1_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  simpa only [(kineticDriftMoment8Coeff1Row0Norm h).property,(kineticDriftMoment8Coeff1Row1Norm h).property,(kineticDriftMoment8Coeff1Row2Norm h).property,(kineticDriftMoment8Coeff1Row3Norm h).property,(kineticDriftMoment8Coeff1Row4Norm h).property] using he

theorem kineticDriftMoment8Coeff2_rows (h : ℂ) (b : ℕ) :
    (driftReader h clearMoment8KineticCoeff2).coeff b=
      (if b=0 then (kineticDriftMoment8Coeff2Row0Norm h).val else 0) + (if b=1 then (kineticDriftMoment8Coeff2Row1Norm h).val else 0) + (if b=2 then (kineticDriftMoment8Coeff2Row2Norm h).val else 0) + (if b=3 then (kineticDriftMoment8Coeff2Row3Norm h).val else 0) + (if b=4 then (kineticDriftMoment8Coeff2Row4Norm h).val else 0) := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h clearMoment8KineticCoeff2)
    (n := 5) (by have := clearMoment8KineticCoeff2_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  simpa only [(kineticDriftMoment8Coeff2Row0Norm h).property,(kineticDriftMoment8Coeff2Row1Norm h).property,(kineticDriftMoment8Coeff2Row2Norm h).property,(kineticDriftMoment8Coeff2Row3Norm h).property,(kineticDriftMoment8Coeff2Row4Norm h).property] using he

theorem kineticDriftMoment8Coeff3_rows (h : ℂ) (b : ℕ) :
    (driftReader h clearMoment8KineticCoeff3).coeff b=
      (if b=0 then (kineticDriftMoment8Coeff3Row0Norm h).val else 0) + (if b=1 then (kineticDriftMoment8Coeff3Row1Norm h).val else 0) + (if b=2 then (kineticDriftMoment8Coeff3Row2Norm h).val else 0) + (if b=3 then (kineticDriftMoment8Coeff3Row3Norm h).val else 0) + (if b=4 then (kineticDriftMoment8Coeff3Row4Norm h).val else 0) := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h clearMoment8KineticCoeff3)
    (n := 5) (by have := clearMoment8KineticCoeff3_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  simpa only [(kineticDriftMoment8Coeff3Row0Norm h).property,(kineticDriftMoment8Coeff3Row1Norm h).property,(kineticDriftMoment8Coeff3Row2Norm h).property,(kineticDriftMoment8Coeff3Row3Norm h).property,(kineticDriftMoment8Coeff3Row4Norm h).property] using he

theorem kineticDriftMoment8Coeff4_rows (h : ℂ) (b : ℕ) :
    (driftReader h clearMoment8KineticCoeff4).coeff b=
      (if b=0 then (kineticDriftMoment8Coeff4Row0Norm h).val else 0) + (if b=1 then (kineticDriftMoment8Coeff4Row1Norm h).val else 0) + (if b=2 then (kineticDriftMoment8Coeff4Row2Norm h).val else 0) + (if b=3 then (kineticDriftMoment8Coeff4Row3Norm h).val else 0) + (if b=4 then (kineticDriftMoment8Coeff4Row4Norm h).val else 0) := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h clearMoment8KineticCoeff4)
    (n := 5) (by have := clearMoment8KineticCoeff4_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  simpa only [(kineticDriftMoment8Coeff4Row0Norm h).property,(kineticDriftMoment8Coeff4Row1Norm h).property,(kineticDriftMoment8Coeff4Row2Norm h).property,(kineticDriftMoment8Coeff4Row3Norm h).property,(kineticDriftMoment8Coeff4Row4Norm h).property] using he

theorem kineticDriftMoment8Coeff5_rows (h : ℂ) (b : ℕ) :
    (driftReader h clearMoment8KineticCoeff5).coeff b=
      (if b=0 then (kineticDriftMoment8Coeff5Row0Norm h).val else 0) + (if b=1 then (kineticDriftMoment8Coeff5Row1Norm h).val else 0) + (if b=2 then (kineticDriftMoment8Coeff5Row2Norm h).val else 0) + (if b=3 then (kineticDriftMoment8Coeff5Row3Norm h).val else 0) + (if b=4 then (kineticDriftMoment8Coeff5Row4Norm h).val else 0) := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h clearMoment8KineticCoeff5)
    (n := 5) (by have := clearMoment8KineticCoeff5_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  simpa only [(kineticDriftMoment8Coeff5Row0Norm h).property,(kineticDriftMoment8Coeff5Row1Norm h).property,(kineticDriftMoment8Coeff5Row2Norm h).property,(kineticDriftMoment8Coeff5Row3Norm h).property,(kineticDriftMoment8Coeff5Row4Norm h).property] using he

theorem kineticDriftMoment8Coeff6_rows (h : ℂ) (b : ℕ) :
    (driftReader h clearMoment8KineticCoeff6).coeff b=
      (if b=0 then (kineticDriftMoment8Coeff6Row0Norm h).val else 0) + (if b=1 then (kineticDriftMoment8Coeff6Row1Norm h).val else 0) + (if b=2 then (kineticDriftMoment8Coeff6Row2Norm h).val else 0) + (if b=3 then (kineticDriftMoment8Coeff6Row3Norm h).val else 0) + (if b=4 then (kineticDriftMoment8Coeff6Row4Norm h).val else 0) := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h clearMoment8KineticCoeff6)
    (n := 5) (by have := clearMoment8KineticCoeff6_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  simpa only [(kineticDriftMoment8Coeff6Row0Norm h).property,(kineticDriftMoment8Coeff6Row1Norm h).property,(kineticDriftMoment8Coeff6Row2Norm h).property,(kineticDriftMoment8Coeff6Row3Norm h).property,(kineticDriftMoment8Coeff6Row4Norm h).property] using he

theorem kineticDriftMoment8Coeff7_rows (h : ℂ) (b : ℕ) :
    (driftReader h clearMoment8KineticCoeff7).coeff b=
      (if b=0 then (kineticDriftMoment8Coeff7Row0Norm h).val else 0) + (if b=1 then (kineticDriftMoment8Coeff7Row1Norm h).val else 0) + (if b=2 then (kineticDriftMoment8Coeff7Row2Norm h).val else 0) + (if b=3 then (kineticDriftMoment8Coeff7Row3Norm h).val else 0) + (if b=4 then (kineticDriftMoment8Coeff7Row4Norm h).val else 0) := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h clearMoment8KineticCoeff7)
    (n := 5) (by have := clearMoment8KineticCoeff7_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  simpa only [(kineticDriftMoment8Coeff7Row0Norm h).property,(kineticDriftMoment8Coeff7Row1Norm h).property,(kineticDriftMoment8Coeff7Row2Norm h).property,(kineticDriftMoment8Coeff7Row3Norm h).property,(kineticDriftMoment8Coeff7Row4Norm h).property] using he

theorem kineticDriftMoment8Coeff8_rows (h : ℂ) (b : ℕ) :
    (driftReader h clearMoment8KineticCoeff8).coeff b=
      (if b=0 then (kineticDriftMoment8Coeff8Row0Norm h).val else 0) + (if b=1 then (kineticDriftMoment8Coeff8Row1Norm h).val else 0) + (if b=2 then (kineticDriftMoment8Coeff8Row2Norm h).val else 0) + (if b=3 then (kineticDriftMoment8Coeff8Row3Norm h).val else 0) + (if b=4 then (kineticDriftMoment8Coeff8Row4Norm h).val else 0) := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h clearMoment8KineticCoeff8)
    (n := 5) (by have := clearMoment8KineticCoeff8_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  simpa only [(kineticDriftMoment8Coeff8Row0Norm h).property,(kineticDriftMoment8Coeff8Row1Norm h).property,(kineticDriftMoment8Coeff8Row2Norm h).property,(kineticDriftMoment8Coeff8Row3Norm h).property,(kineticDriftMoment8Coeff8Row4Norm h).property] using he


theorem kineticDriftMoment10Coeff0_rows (h : ℂ) (b : ℕ) :
    (driftReader h clearMoment10KineticCoeff0).coeff b=
      (if b=0 then (kineticDriftMoment10Coeff0Row0Norm h).val else 0) + (if b=1 then (kineticDriftMoment10Coeff0Row1Norm h).val else 0) + (if b=2 then (kineticDriftMoment10Coeff0Row2Norm h).val else 0) + (if b=3 then (kineticDriftMoment10Coeff0Row3Norm h).val else 0) + (if b=4 then (kineticDriftMoment10Coeff0Row4Norm h).val else 0) + (if b=5 then (kineticDriftMoment10Coeff0Row5Norm h).val else 0) := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h clearMoment10KineticCoeff0)
    (n := 6) (by have := clearMoment10KineticCoeff0_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  simpa only [(kineticDriftMoment10Coeff0Row0Norm h).property,(kineticDriftMoment10Coeff0Row1Norm h).property,(kineticDriftMoment10Coeff0Row2Norm h).property,(kineticDriftMoment10Coeff0Row3Norm h).property,(kineticDriftMoment10Coeff0Row4Norm h).property,(kineticDriftMoment10Coeff0Row5Norm h).property] using he

theorem kineticDriftMoment10Coeff1_rows (h : ℂ) (b : ℕ) :
    (driftReader h clearMoment10KineticCoeff1).coeff b=
      (if b=0 then (kineticDriftMoment10Coeff1Row0Norm h).val else 0) + (if b=1 then (kineticDriftMoment10Coeff1Row1Norm h).val else 0) + (if b=2 then (kineticDriftMoment10Coeff1Row2Norm h).val else 0) + (if b=3 then (kineticDriftMoment10Coeff1Row3Norm h).val else 0) + (if b=4 then (kineticDriftMoment10Coeff1Row4Norm h).val else 0) + (if b=5 then (kineticDriftMoment10Coeff1Row5Norm h).val else 0) := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h clearMoment10KineticCoeff1)
    (n := 6) (by have := clearMoment10KineticCoeff1_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  simpa only [(kineticDriftMoment10Coeff1Row0Norm h).property,(kineticDriftMoment10Coeff1Row1Norm h).property,(kineticDriftMoment10Coeff1Row2Norm h).property,(kineticDriftMoment10Coeff1Row3Norm h).property,(kineticDriftMoment10Coeff1Row4Norm h).property,(kineticDriftMoment10Coeff1Row5Norm h).property] using he

theorem kineticDriftMoment10Coeff2_rows (h : ℂ) (b : ℕ) :
    (driftReader h clearMoment10KineticCoeff2).coeff b=
      (if b=0 then (kineticDriftMoment10Coeff2Row0Norm h).val else 0) + (if b=1 then (kineticDriftMoment10Coeff2Row1Norm h).val else 0) + (if b=2 then (kineticDriftMoment10Coeff2Row2Norm h).val else 0) + (if b=3 then (kineticDriftMoment10Coeff2Row3Norm h).val else 0) + (if b=4 then (kineticDriftMoment10Coeff2Row4Norm h).val else 0) + (if b=5 then (kineticDriftMoment10Coeff2Row5Norm h).val else 0) := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h clearMoment10KineticCoeff2)
    (n := 6) (by have := clearMoment10KineticCoeff2_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  simpa only [(kineticDriftMoment10Coeff2Row0Norm h).property,(kineticDriftMoment10Coeff2Row1Norm h).property,(kineticDriftMoment10Coeff2Row2Norm h).property,(kineticDriftMoment10Coeff2Row3Norm h).property,(kineticDriftMoment10Coeff2Row4Norm h).property,(kineticDriftMoment10Coeff2Row5Norm h).property] using he

theorem kineticDriftMoment10Coeff3_rows (h : ℂ) (b : ℕ) :
    (driftReader h clearMoment10KineticCoeff3).coeff b=
      (if b=0 then (kineticDriftMoment10Coeff3Row0Norm h).val else 0) + (if b=1 then (kineticDriftMoment10Coeff3Row1Norm h).val else 0) + (if b=2 then (kineticDriftMoment10Coeff3Row2Norm h).val else 0) + (if b=3 then (kineticDriftMoment10Coeff3Row3Norm h).val else 0) + (if b=4 then (kineticDriftMoment10Coeff3Row4Norm h).val else 0) + (if b=5 then (kineticDriftMoment10Coeff3Row5Norm h).val else 0) := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h clearMoment10KineticCoeff3)
    (n := 6) (by have := clearMoment10KineticCoeff3_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  simpa only [(kineticDriftMoment10Coeff3Row0Norm h).property,(kineticDriftMoment10Coeff3Row1Norm h).property,(kineticDriftMoment10Coeff3Row2Norm h).property,(kineticDriftMoment10Coeff3Row3Norm h).property,(kineticDriftMoment10Coeff3Row4Norm h).property,(kineticDriftMoment10Coeff3Row5Norm h).property] using he

theorem kineticDriftMoment10Coeff4_rows (h : ℂ) (b : ℕ) :
    (driftReader h clearMoment10KineticCoeff4).coeff b=
      (if b=0 then (kineticDriftMoment10Coeff4Row0Norm h).val else 0) + (if b=1 then (kineticDriftMoment10Coeff4Row1Norm h).val else 0) + (if b=2 then (kineticDriftMoment10Coeff4Row2Norm h).val else 0) + (if b=3 then (kineticDriftMoment10Coeff4Row3Norm h).val else 0) + (if b=4 then (kineticDriftMoment10Coeff4Row4Norm h).val else 0) + (if b=5 then (kineticDriftMoment10Coeff4Row5Norm h).val else 0) := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h clearMoment10KineticCoeff4)
    (n := 6) (by have := clearMoment10KineticCoeff4_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  simpa only [(kineticDriftMoment10Coeff4Row0Norm h).property,(kineticDriftMoment10Coeff4Row1Norm h).property,(kineticDriftMoment10Coeff4Row2Norm h).property,(kineticDriftMoment10Coeff4Row3Norm h).property,(kineticDriftMoment10Coeff4Row4Norm h).property,(kineticDriftMoment10Coeff4Row5Norm h).property] using he

theorem kineticDriftMoment10Coeff5_rows (h : ℂ) (b : ℕ) :
    (driftReader h clearMoment10KineticCoeff5).coeff b=
      (if b=0 then (kineticDriftMoment10Coeff5Row0Norm h).val else 0) + (if b=1 then (kineticDriftMoment10Coeff5Row1Norm h).val else 0) + (if b=2 then (kineticDriftMoment10Coeff5Row2Norm h).val else 0) + (if b=3 then (kineticDriftMoment10Coeff5Row3Norm h).val else 0) + (if b=4 then (kineticDriftMoment10Coeff5Row4Norm h).val else 0) + (if b=5 then (kineticDriftMoment10Coeff5Row5Norm h).val else 0) := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h clearMoment10KineticCoeff5)
    (n := 6) (by have := clearMoment10KineticCoeff5_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  simpa only [(kineticDriftMoment10Coeff5Row0Norm h).property,(kineticDriftMoment10Coeff5Row1Norm h).property,(kineticDriftMoment10Coeff5Row2Norm h).property,(kineticDriftMoment10Coeff5Row3Norm h).property,(kineticDriftMoment10Coeff5Row4Norm h).property,(kineticDriftMoment10Coeff5Row5Norm h).property] using he

theorem kineticDriftMoment10Coeff6_rows (h : ℂ) (b : ℕ) :
    (driftReader h clearMoment10KineticCoeff6).coeff b=
      (if b=0 then (kineticDriftMoment10Coeff6Row0Norm h).val else 0) + (if b=1 then (kineticDriftMoment10Coeff6Row1Norm h).val else 0) + (if b=2 then (kineticDriftMoment10Coeff6Row2Norm h).val else 0) + (if b=3 then (kineticDriftMoment10Coeff6Row3Norm h).val else 0) + (if b=4 then (kineticDriftMoment10Coeff6Row4Norm h).val else 0) + (if b=5 then (kineticDriftMoment10Coeff6Row5Norm h).val else 0) := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h clearMoment10KineticCoeff6)
    (n := 6) (by have := clearMoment10KineticCoeff6_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  simpa only [(kineticDriftMoment10Coeff6Row0Norm h).property,(kineticDriftMoment10Coeff6Row1Norm h).property,(kineticDriftMoment10Coeff6Row2Norm h).property,(kineticDriftMoment10Coeff6Row3Norm h).property,(kineticDriftMoment10Coeff6Row4Norm h).property,(kineticDriftMoment10Coeff6Row5Norm h).property] using he

theorem kineticDriftMoment10Coeff7_rows (h : ℂ) (b : ℕ) :
    (driftReader h clearMoment10KineticCoeff7).coeff b=
      (if b=0 then (kineticDriftMoment10Coeff7Row0Norm h).val else 0) + (if b=1 then (kineticDriftMoment10Coeff7Row1Norm h).val else 0) + (if b=2 then (kineticDriftMoment10Coeff7Row2Norm h).val else 0) + (if b=3 then (kineticDriftMoment10Coeff7Row3Norm h).val else 0) + (if b=4 then (kineticDriftMoment10Coeff7Row4Norm h).val else 0) + (if b=5 then (kineticDriftMoment10Coeff7Row5Norm h).val else 0) := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h clearMoment10KineticCoeff7)
    (n := 6) (by have := clearMoment10KineticCoeff7_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  simpa only [(kineticDriftMoment10Coeff7Row0Norm h).property,(kineticDriftMoment10Coeff7Row1Norm h).property,(kineticDriftMoment10Coeff7Row2Norm h).property,(kineticDriftMoment10Coeff7Row3Norm h).property,(kineticDriftMoment10Coeff7Row4Norm h).property,(kineticDriftMoment10Coeff7Row5Norm h).property] using he

theorem kineticDriftMoment10Coeff8_rows (h : ℂ) (b : ℕ) :
    (driftReader h clearMoment10KineticCoeff8).coeff b=
      (if b=0 then (kineticDriftMoment10Coeff8Row0Norm h).val else 0) + (if b=1 then (kineticDriftMoment10Coeff8Row1Norm h).val else 0) + (if b=2 then (kineticDriftMoment10Coeff8Row2Norm h).val else 0) + (if b=3 then (kineticDriftMoment10Coeff8Row3Norm h).val else 0) + (if b=4 then (kineticDriftMoment10Coeff8Row4Norm h).val else 0) + (if b=5 then (kineticDriftMoment10Coeff8Row5Norm h).val else 0) := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h clearMoment10KineticCoeff8)
    (n := 6) (by have := clearMoment10KineticCoeff8_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  simpa only [(kineticDriftMoment10Coeff8Row0Norm h).property,(kineticDriftMoment10Coeff8Row1Norm h).property,(kineticDriftMoment10Coeff8Row2Norm h).property,(kineticDriftMoment10Coeff8Row3Norm h).property,(kineticDriftMoment10Coeff8Row4Norm h).property,(kineticDriftMoment10Coeff8Row5Norm h).property] using he

theorem kineticDriftMoment10Coeff9_rows (h : ℂ) (b : ℕ) :
    (driftReader h clearMoment10KineticCoeff9).coeff b=
      (if b=0 then (kineticDriftMoment10Coeff9Row0Norm h).val else 0) + (if b=1 then (kineticDriftMoment10Coeff9Row1Norm h).val else 0) + (if b=2 then (kineticDriftMoment10Coeff9Row2Norm h).val else 0) + (if b=3 then (kineticDriftMoment10Coeff9Row3Norm h).val else 0) + (if b=4 then (kineticDriftMoment10Coeff9Row4Norm h).val else 0) + (if b=5 then (kineticDriftMoment10Coeff9Row5Norm h).val else 0) := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h clearMoment10KineticCoeff9)
    (n := 6) (by have := clearMoment10KineticCoeff9_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  simpa only [(kineticDriftMoment10Coeff9Row0Norm h).property,(kineticDriftMoment10Coeff9Row1Norm h).property,(kineticDriftMoment10Coeff9Row2Norm h).property,(kineticDriftMoment10Coeff9Row3Norm h).property,(kineticDriftMoment10Coeff9Row4Norm h).property,(kineticDriftMoment10Coeff9Row5Norm h).property] using he

theorem kineticDriftMoment10Coeff10_rows (h : ℂ) (b : ℕ) :
    (driftReader h clearMoment10KineticCoeff10).coeff b=
      (if b=0 then (kineticDriftMoment10Coeff10Row0Norm h).val else 0) + (if b=1 then (kineticDriftMoment10Coeff10Row1Norm h).val else 0) + (if b=2 then (kineticDriftMoment10Coeff10Row2Norm h).val else 0) + (if b=3 then (kineticDriftMoment10Coeff10Row3Norm h).val else 0) + (if b=4 then (kineticDriftMoment10Coeff10Row4Norm h).val else 0) + (if b=5 then (kineticDriftMoment10Coeff10Row5Norm h).val else 0) := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h clearMoment10KineticCoeff10)
    (n := 6) (by have := clearMoment10KineticCoeff10_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  simpa only [(kineticDriftMoment10Coeff10Row0Norm h).property,(kineticDriftMoment10Coeff10Row1Norm h).property,(kineticDriftMoment10Coeff10Row2Norm h).property,(kineticDriftMoment10Coeff10Row3Norm h).property,(kineticDriftMoment10Coeff10Row4Norm h).property,(kineticDriftMoment10Coeff10Row5Norm h).property] using he

end
end HTGeometry.ThetaRatioKineticContraction
