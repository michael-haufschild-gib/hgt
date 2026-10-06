import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticFirstTensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity
open HTGeometry.EvenCompactBernstein

theorem kineticBernstein_add (n : ℕ) (f g : ℕ → ℝ) (t : ℝ) :
    kineticBernstein n (fun i => f i+g i) t=kineticBernstein n f t+kineticBernstein n g t := by
  simp only [kineticBernstein,add_mul,Finset.sum_add_distrib]

theorem kineticBernstein_const_mul (n : ℕ) (c : ℝ) (f : ℕ → ℝ) (t : ℝ) :
    kineticBernstein n (fun i => c*f i) t=c*kineticBernstein n f t := by
  simp only [kineticBernstein,mul_assoc,Finset.mul_sum]

theorem kineticBernstein_mul_const (n : ℕ) (f : ℕ → ℝ) (c t : ℝ) :
    kineticBernstein n (fun i => f i*c) t=kineticBernstein n f t*c := by
  simp only [kineticBernstein,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem kineticBernstein_degree (n j : ℕ) (hj : j≤n) (t : ℝ) :
    kineticBernstein n (degreeElevationCoefficient n j) t=t^j :=
  monomial_bernstein_reconstruction n j hj t

theorem firstControlDefectForm4_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => firstControlDefectForm4
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        firstControlDefectRow4 ((361/25)*v) := by
  simp only [firstControlDefectForm4,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega)]
  norm_num [firstControlDefectRow4,Nat.rawCast,Int.rawCast]

theorem firstControlDefectForm5_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => firstControlDefectForm5
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        firstControlDefectRow5 ((361/25)*v) := by
  simp only [firstControlDefectForm5,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega)]
  norm_num [firstControlDefectRow5,Nat.rawCast,Int.rawCast]

theorem firstControlDefectForm6_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => firstControlDefectForm6
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        firstControlDefectRow6 ((361/25)*v) := by
  simp only [firstControlDefectForm6,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega)]
  norm_num [firstControlDefectRow6,Nat.rawCast,Int.rawCast]
  ring

theorem firstControlDefectForm7_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => firstControlDefectForm7
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        firstControlDefectRow7 ((361/25)*v) := by
  simp only [firstControlDefectForm7,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega)]
  norm_num [firstControlDefectRow7,Nat.rawCast,Int.rawCast]
  ring

theorem firstControlDefectForm8_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => firstControlDefectForm8
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        firstControlDefectRow8 ((361/25)*v) := by
  simp only [firstControlDefectForm8,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega)]
  norm_num [firstControlDefectRow8,Nat.rawCast,Int.rawCast]
  ring

theorem firstControlDefectForm9_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => firstControlDefectForm9
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        firstControlDefectRow9 ((361/25)*v) := by
  simp only [firstControlDefectForm9,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega)]
  norm_num [firstControlDefectRow9,Nat.rawCast,Int.rawCast]
  ring

theorem firstControlDefectForm10_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => firstControlDefectForm10
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        firstControlDefectRow10 ((361/25)*v) := by
  simp only [firstControlDefectForm10,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega)]
  norm_num [firstControlDefectRow10,Nat.rawCast,Int.rawCast]
  ring

theorem firstControlDefectForm11_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => firstControlDefectForm11
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        firstControlDefectRow11 ((361/25)*v) := by
  simp only [firstControlDefectForm11,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega)]
  norm_num [firstControlDefectRow11,Nat.rawCast,Int.rawCast]
  ring

theorem firstControlDefectForm12_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => firstControlDefectForm12
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        firstControlDefectRow12 ((361/25)*v) := by
  simp only [firstControlDefectForm12,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega)]
  norm_num [firstControlDefectRow12,Nat.rawCast,Int.rawCast]
  ring

theorem firstControlDefectForm13_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => firstControlDefectForm13
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        firstControlDefectRow13 ((361/25)*v) := by
  simp only [firstControlDefectForm13,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega)]
  norm_num [firstControlDefectRow13,Nat.rawCast,Int.rawCast]
  ring

theorem firstControlDefectForm14_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => firstControlDefectForm14
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        firstControlDefectRow14 ((361/25)*v) := by
  simp only [firstControlDefectForm14,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega)]
  norm_num [firstControlDefectRow14,Nat.rawCast,Int.rawCast]
  ring

theorem firstControlDefectForm15_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => firstControlDefectForm15
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        firstControlDefectRow15 ((361/25)*v) := by
  simp only [firstControlDefectForm15,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega)]
  norm_num [firstControlDefectRow15,Nat.rawCast,Int.rawCast]
  ring

theorem firstControlDefectForm16_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => firstControlDefectForm16
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        firstControlDefectRow16 ((361/25)*v) := by
  simp only [firstControlDefectForm16,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega)]
  norm_num [firstControlDefectRow16,Nat.rawCast,Int.rawCast]
  ring

theorem firstControlDefectForm17_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => firstControlDefectForm17
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        firstControlDefectRow17 ((361/25)*v) := by
  simp only [firstControlDefectForm17,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega)]
  norm_num [firstControlDefectRow17,Nat.rawCast,Int.rawCast]
  ring

theorem firstControlDefectForm18_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => firstControlDefectForm18
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        firstControlDefectRow18 ((361/25)*v) := by
  simp only [firstControlDefectForm18,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega)]
  norm_num [firstControlDefectRow18,Nat.rawCast,Int.rawCast]
  ring

theorem firstControlDefectForm19_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => firstControlDefectForm19
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        firstControlDefectRow19 ((361/25)*v) := by
  simp only [firstControlDefectForm19,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega)]
  norm_num [firstControlDefectRow19,Nat.rawCast,Int.rawCast]
  ring

theorem firstControlDefectForm20_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => firstControlDefectForm20
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        firstControlDefectRow20 ((361/25)*v) := by
  simp only [firstControlDefectForm20,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  norm_num [firstControlDefectRow20,Nat.rawCast,Int.rawCast]
  ring

theorem firstControlDefectForm21_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => firstControlDefectForm21
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        firstControlDefectRow21 ((361/25)*v) := by
  simp only [firstControlDefectForm21,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  norm_num [firstControlDefectRow21,Nat.rawCast,Int.rawCast]
  ring

theorem firstControlDefectForm22_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => firstControlDefectForm22
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        firstControlDefectRow22 ((361/25)*v) := by
  simp only [firstControlDefectForm22,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  norm_num [firstControlDefectRow22,Nat.rawCast,Int.rawCast]
  ring

theorem firstControlDefectForm23_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => firstControlDefectForm23
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        firstControlDefectRow23 ((361/25)*v) := by
  simp only [firstControlDefectForm23,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  norm_num [firstControlDefectRow23,Nat.rawCast,Int.rawCast]
  ring

theorem firstControlDefectForm24_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => firstControlDefectForm24
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        firstControlDefectRow24 ((361/25)*v) := by
  simp only [firstControlDefectForm24,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  norm_num [firstControlDefectRow24,Nat.rawCast,Int.rawCast]
  ring

theorem firstControlDefectForm25_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => firstControlDefectForm25
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        firstControlDefectRow25 ((361/25)*v) := by
  simp only [firstControlDefectForm25,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  norm_num [firstControlDefectRow25,Nat.rawCast,Int.rawCast]
  ring

theorem firstControlDefectForm26_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => firstControlDefectForm26
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        firstControlDefectRow26 ((361/25)*v) := by
  simp only [firstControlDefectForm26,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  norm_num [firstControlDefectRow26,Nat.rawCast,Int.rawCast]
  ring

theorem firstControlDefectForm27_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => firstControlDefectForm27
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        firstControlDefectRow27 ((361/25)*v) := by
  simp only [firstControlDefectForm27,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  norm_num [firstControlDefectRow27,Nat.rawCast,Int.rawCast]
  ring

theorem firstControlDefectForm28_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => firstControlDefectForm28
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        firstControlDefectRow28 ((361/25)*v) := by
  simp only [firstControlDefectForm28,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  norm_num [firstControlDefectRow28,Nat.rawCast,Int.rawCast]
  ring

theorem firstControlDefectForm29_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => firstControlDefectForm29
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        firstControlDefectRow29 ((361/25)*v) := by
  simp only [firstControlDefectForm29,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  norm_num [firstControlDefectRow29,Nat.rawCast,Int.rawCast]
  ring

theorem firstControlDefectForm30_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => firstControlDefectForm30
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        firstControlDefectRow30 ((361/25)*v) := by
  simp only [firstControlDefectForm30,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  norm_num [firstControlDefectRow30,Nat.rawCast,Int.rawCast]
  ring

theorem firstControlDefectForm31_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => firstControlDefectForm31
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        firstControlDefectRow31 ((361/25)*v) := by
  simp only [firstControlDefectForm31,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  norm_num [firstControlDefectRow31,Nat.rawCast,Int.rawCast]
  ring

theorem firstControlDefectForm32_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => firstControlDefectForm32
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        firstControlDefectRow32 ((361/25)*v) := by
  simp only [firstControlDefectForm32,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  norm_num [firstControlDefectRow32,Nat.rawCast,Int.rawCast]
  ring

theorem firstControlDefectForm33_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => firstControlDefectForm33
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        firstControlDefectRow33 ((361/25)*v) := by
  simp only [firstControlDefectForm33,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  norm_num [firstControlDefectRow33,Nat.rawCast,Int.rawCast]
  ring

theorem firstControlDefectForm34_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => firstControlDefectForm34
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        firstControlDefectRow34 ((361/25)*v) := by
  simp only [firstControlDefectForm34,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  norm_num [firstControlDefectRow34,Nat.rawCast,Int.rawCast]
  ring

theorem firstControlDefectForm35_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => firstControlDefectForm35
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        firstControlDefectRow35 ((361/25)*v) := by
  simp only [firstControlDefectForm35,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  norm_num [firstControlDefectRow35,Nat.rawCast,Int.rawCast]
  ring

theorem firstControlDefectForm36_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => firstControlDefectForm36
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        firstControlDefectRow36 ((361/25)*v) := by
  simp only [firstControlDefectForm36,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  norm_num [firstControlDefectRow36,Nat.rawCast,Int.rawCast]
  ring

def firstControlDefectTensorValue (t v : ℝ) : ℝ :=
  kineticBernstein 32 (fun A => kineticBernstein 9 (firstControlDefectTensorCoefficient A) v) t

theorem firstControlDefectTensorValue_reconstruction (t v : ℝ) :
    firstControlDefectTensorValue t v=firstControlDefectQuotient ((4/5)*t) ((361/25)*v) := by
  delta firstControlDefectTensorValue firstControlDefectTensorCoefficient firstControlDefectClockForm
  simp only [kineticBernstein_add,kineticBernstein_mul_const,
    kineticBernstein_const_mul,
    firstControlDefectForm4_reconstruction,firstControlDefectForm5_reconstruction,firstControlDefectForm6_reconstruction,firstControlDefectForm7_reconstruction,firstControlDefectForm8_reconstruction,firstControlDefectForm9_reconstruction,firstControlDefectForm10_reconstruction,firstControlDefectForm11_reconstruction,firstControlDefectForm12_reconstruction,firstControlDefectForm13_reconstruction,firstControlDefectForm14_reconstruction,firstControlDefectForm15_reconstruction,firstControlDefectForm16_reconstruction,firstControlDefectForm17_reconstruction,firstControlDefectForm18_reconstruction,firstControlDefectForm19_reconstruction,firstControlDefectForm20_reconstruction,firstControlDefectForm21_reconstruction,firstControlDefectForm22_reconstruction,firstControlDefectForm23_reconstruction,firstControlDefectForm24_reconstruction,firstControlDefectForm25_reconstruction,firstControlDefectForm26_reconstruction,firstControlDefectForm27_reconstruction,firstControlDefectForm28_reconstruction,firstControlDefectForm29_reconstruction,firstControlDefectForm30_reconstruction,firstControlDefectForm31_reconstruction,firstControlDefectForm32_reconstruction,firstControlDefectForm33_reconstruction,firstControlDefectForm34_reconstruction,firstControlDefectForm35_reconstruction,firstControlDefectForm36_reconstruction]
  rw [kineticBernstein_degree 32 (4-4) (by omega),kineticBernstein_degree 32 (5-4) (by omega),kineticBernstein_degree 32 (6-4) (by omega),kineticBernstein_degree 32 (7-4) (by omega),kineticBernstein_degree 32 (8-4) (by omega),kineticBernstein_degree 32 (9-4) (by omega),kineticBernstein_degree 32 (10-4) (by omega),kineticBernstein_degree 32 (11-4) (by omega),kineticBernstein_degree 32 (12-4) (by omega),kineticBernstein_degree 32 (13-4) (by omega),kineticBernstein_degree 32 (14-4) (by omega),kineticBernstein_degree 32 (15-4) (by omega),kineticBernstein_degree 32 (16-4) (by omega),kineticBernstein_degree 32 (17-4) (by omega),kineticBernstein_degree 32 (18-4) (by omega),kineticBernstein_degree 32 (19-4) (by omega),kineticBernstein_degree 32 (20-4) (by omega),kineticBernstein_degree 32 (21-4) (by omega),kineticBernstein_degree 32 (22-4) (by omega),kineticBernstein_degree 32 (23-4) (by omega),kineticBernstein_degree 32 (24-4) (by omega),kineticBernstein_degree 32 (25-4) (by omega),kineticBernstein_degree 32 (26-4) (by omega),kineticBernstein_degree 32 (27-4) (by omega),kineticBernstein_degree 32 (28-4) (by omega),kineticBernstein_degree 32 (29-4) (by omega),kineticBernstein_degree 32 (30-4) (by omega),kineticBernstein_degree 32 (31-4) (by omega),kineticBernstein_degree 32 (32-4) (by omega),kineticBernstein_degree 32 (33-4) (by omega),kineticBernstein_degree 32 (34-4) (by omega),kineticBernstein_degree 32 (35-4) (by omega),kineticBernstein_degree 32 (36-4) (by omega)]
  simp only [firstControlDefectQuotient,mul_pow,mul_assoc,mul_comm]

end
end HTGeometry.ThetaRatioKineticContraction
