import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerHyperbolicReduction

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Module

/-!
# Positive representatives of integral modular intertwiners

Normalized powers of a positive integral determinant-one matrix converge to
its positive rank-one expanding projection. An integral unimodular intertwiner
maps this projection entirely into one strict sign. Multiplication by high
matrix powers, followed if necessary by a sign change, therefore gives a
strictly positive unimodular intertwiner.
-/

open Matrix Filter Topology
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerHyperbolic
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerConjugacy

abbrev RealMatrix := Matrix (Fin 2) (Fin 2) ℝ

def realMatrix (A : IntMatrix) : RealMatrix := fun i j => (A i j : ℝ)

@[simp] theorem realMatrix_mul (A B : IntMatrix) :
    realMatrix (A*B) = realMatrix A*realMatrix B := by
  ext i j
  simp only [realMatrix,Matrix.mul_apply,Fin.sum_univ_two,Int.cast_add,Int.cast_mul]

@[simp] theorem realMatrix_one : realMatrix 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [realMatrix]

@[simp] theorem realMatrix_pow (A : IntMatrix) (n : ℕ) :
    realMatrix (A^n) = realMatrix A^n := by
  induction n with
  | zero => simp only [pow_zero,realMatrix_one]
  | succ n ih => simp only [pow_succ,realMatrix_mul,ih]

/-- The complementary expanding spectral projection of a determinant-one matrix. -/
def expandingProjection (A : IntMatrix) : RealMatrix :=
  (expandingMultiplier (A 0 0+A 1 1)-(expandingMultiplier (A 0 0+A 1 1))⁻¹)⁻¹ •
    (realMatrix A-(expandingMultiplier (A 0 0+A 1 1))⁻¹ • (1 : RealMatrix))

private theorem positive_trace (A : IntMatrix) (hdet : A.det = 1)
    (hpos : ∀ i j, 0 < A i j) : 2 < A 0 0+A 1 1 := by
  have ha := hpos 0 0
  have hb := hpos 0 1
  have hc := hpos 1 0
  have hd := hpos 1 1
  rw [Matrix.det_fin_two] at hdet
  by_contra hn
  have ha1 : A 0 0 = 1 := by omega
  have hd1 : A 1 1 = 1 := by omega
  rw [ha1,hd1] at hdet
  have hbc := mul_pos hb hc
  nlinarith only [hdet,hbc]

private theorem multiplier_sum (A : IntMatrix) (ht : 2 < A 0 0+A 1 1) :
    expandingMultiplier (A 0 0+A 1 1)+(expandingMultiplier (A 0 0+A 1 1))⁻¹ =
      (A 0 0 : ℝ)+A 1 1 := by
  have hroot := expandingMultiplier_spec ht
  have hne : expandingMultiplier (A 0 0+A 1 1) ≠ 0 := ne_of_gt (by linarith only [hroot.1])
  apply (mul_right_cancel₀ hne)
  rw [add_mul,inv_mul_cancel₀ hne]
  have he := hroot.2
  rw [Int.cast_add] at he
  nlinarith only [he]

/-- Cayley--Hamilton in the literal two-dimensional determinant-one representation. -/
theorem realMatrix_quadratic (A : IntMatrix) (hdet : A.det = 1) :
    realMatrix A*realMatrix A-((A 0 0 : ℝ)+A 1 1) • realMatrix A+1 = 0 := by
  have hd : (A 0 0 : ℝ)*A 1 1-(A 0 1 : ℝ)*A 1 0 = 1 := by
    have hi : A 0 0*A 1 1-A 0 1*A 1 0 = 1 := by simpa only [Matrix.det_fin_two] using hdet
    exact_mod_cast hi
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Fin.sum_univ_two,realMatrix] <;> nlinarith only [hd]

/-- The spectral projection and its complement satisfy the two exact eigenmatrix equations. -/
theorem expandingProjection_eigen (A : IntMatrix) (hdet : A.det = 1)
    (ht : 2 < A 0 0+A 1 1) :
    realMatrix A*expandingProjection A =
      expandingMultiplier (A 0 0+A 1 1) • expandingProjection A ∧
    realMatrix A*(1-expandingProjection A) =
      (expandingMultiplier (A 0 0+A 1 1))⁻¹ • (1-expandingProjection A) := by
  have hsum := multiplier_sum A ht
  have hroot := (expandingMultiplier_spec ht).1
  have hroot0 : 0 < expandingMultiplier (A 0 0+A 1 1) := by linarith only [hroot]
  have hmu : (expandingMultiplier (A 0 0+A 1 1))⁻¹ < 1 := (inv_lt_one₀ hroot0).mpr hroot
  have hgap : expandingMultiplier (A 0 0+A 1 1)-(expandingMultiplier (A 0 0+A 1 1))⁻¹ ≠ 0 := by
    linarith only [hroot,hmu]
  have hquad := realMatrix_quadratic A hdet
  have hpoly : realMatrix A*realMatrix A =
      ((A 0 0 : ℝ)+A 1 1) • realMatrix A-1 := by
    calc
      _ = (realMatrix A*realMatrix A-((A 0 0 : ℝ)+A 1 1) • realMatrix A+1)+
          (((A 0 0 : ℝ)+A 1 1) • realMatrix A-1) := by abel
      _ = _ := by rw [hquad,zero_add]
  have hp : realMatrix A*expandingProjection A =
      expandingMultiplier (A 0 0+A 1 1) • expandingProjection A := by
    rw [expandingProjection,Matrix.mul_smul,Matrix.mul_sub,Matrix.mul_smul,
      Matrix.mul_one,hpoly,← hsum]
    simp only [smul_sub,smul_smul]
    ext i j
    simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
    field_simp [hgap,ne_of_gt hroot0]
    ring
  have hd : (expandingMultiplier (A 0 0+A 1 1)-(expandingMultiplier (A 0 0+A 1 1))⁻¹) •
      expandingProjection A = realMatrix A-(expandingMultiplier (A 0 0+A 1 1))⁻¹ • (1 : RealMatrix) := by
    rw [expandingProjection,smul_smul,mul_inv_cancel₀ hgap,one_smul]
  rw [sub_smul] at hd
  have hsplit : expandingMultiplier (A 0 0+A 1 1) • expandingProjection A =
      (expandingMultiplier (A 0 0+A 1 1))⁻¹ • expandingProjection A+
        (realMatrix A-(expandingMultiplier (A 0 0+A 1 1))⁻¹ • (1 : RealMatrix)) := by
    calc
      _ = (expandingMultiplier (A 0 0+A 1 1))⁻¹ • expandingProjection A+
          (expandingMultiplier (A 0 0+A 1 1) • expandingProjection A-
            (expandingMultiplier (A 0 0+A 1 1))⁻¹ • expandingProjection A) := by abel
      _ = _ := by rw [hd]
  refine ⟨hp,?_⟩
  rw [Matrix.mul_sub,Matrix.mul_one,hp,hsplit,smul_sub]
  abel

#print axioms realMatrix_quadratic
#print axioms expandingProjection_eigen


/-- Every power splits into the expanding and contracting spectral components. -/
theorem realMatrix_pow_spectral (A : IntMatrix) (hdet : A.det = 1)
    (ht : 2 < A 0 0+A 1 1) (n : ℕ) :
    realMatrix A^n = expandingMultiplier (A 0 0+A 1 1)^n • expandingProjection A+
      ((expandingMultiplier (A 0 0+A 1 1))⁻¹)^n • (1-expandingProjection A) := by
  obtain ⟨hp,hq⟩ := expandingProjection_eigen A hdet ht
  induction n with
  | zero => simp only [pow_zero,one_smul]; module
  | succ n ih =>
    rw [pow_succ',ih,Matrix.mul_add,Matrix.mul_smul,Matrix.mul_smul,hp,hq]
    simp only [smul_smul,pow_succ]

/-- Normalized powers of the actual integral matrix converge entrywise to its expanding projection. -/
theorem normalized_power_tendsto (A : IntMatrix) (hdet : A.det = 1)
    (ht : 2 < A 0 0+A 1 1) (i j : Fin 2) :
    Tendsto (fun n : ℕ => ((A^n) i j : ℝ)/expandingMultiplier (A 0 0+A 1 1)^n)
      atTop (𝓝 (expandingProjection A i j)) := by
  have hlam := (expandingMultiplier_spec ht).1
  have hlam0 : 0 < expandingMultiplier (A 0 0+A 1 1) := by linarith only [hlam]
  have hmu0 : 0 < (expandingMultiplier (A 0 0+A 1 1))⁻¹ := inv_pos.mpr hlam0
  have hmu1 : (expandingMultiplier (A 0 0+A 1 1))⁻¹ < 1 := (inv_lt_one₀ hlam0).mpr hlam
  have hratio : |(expandingMultiplier (A 0 0+A 1 1))⁻¹/
      expandingMultiplier (A 0 0+A 1 1)| < 1 := by
    rw [abs_of_pos (div_pos hmu0 hlam0),div_lt_one hlam0]
    exact hmu1.trans hlam
  have hlim := tendsto_pow_atTop_nhds_zero_of_abs_lt_one hratio
  have he (n : ℕ) : ((A^n) i j : ℝ)/expandingMultiplier (A 0 0+A 1 1)^n =
      expandingProjection A i j+
        ((expandingMultiplier (A 0 0+A 1 1))⁻¹/expandingMultiplier (A 0 0+A 1 1))^n *
          ((1 : RealMatrix) i j-expandingProjection A i j) := by
    have hp := congrArg (fun M : RealMatrix => M i j) (realMatrix_pow_spectral A hdet ht n)
    rw [← realMatrix_pow] at hp
    simp only [realMatrix,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Matrix.sub_apply] at hp
    rw [hp,add_div,mul_div_cancel_left₀ _ (pow_ne_zero n (ne_of_gt hlam0)),div_pow]
    ring
  simp_rw [he]
  simpa only [zero_mul,add_zero] using
    tendsto_const_nhds.add (hlim.mul_const ((1 : RealMatrix) i j-expandingProjection A i j))

/-- Strict positivity of the matrix makes every entry of the expanding projection positive. -/
theorem expandingProjection_pos (A : IntMatrix) (hdet : A.det = 1)
    (hpos : ∀ i j, 0 < A i j) (i j : Fin 2) : 0 < expandingProjection A i j := by
  have ht := positive_trace A hdet hpos
  have hlam := (expandingMultiplier_spec ht).1
  have hlam0 : 0 < expandingMultiplier (A 0 0+A 1 1) := by linarith only [hlam]
  have hmu : (expandingMultiplier (A 0 0+A 1 1))⁻¹ < 1 := (inv_lt_one₀ hlam0).mpr hlam
  have hgap : 0 < (expandingMultiplier (A 0 0+A 1 1)-
      (expandingMultiplier (A 0 0+A 1 1))⁻¹)⁻¹ :=
    inv_pos.mpr (sub_pos.mpr (hmu.trans hlam))
  have ha : (1 : ℝ) ≤ A 0 0 := by exact_mod_cast (show (1 : ℤ) ≤ A 0 0 by have h := hpos 0 0; omega)
  have hd : (1 : ℝ) ≤ A 1 1 := by exact_mod_cast (show (1 : ℤ) ≤ A 1 1 by have h := hpos 1 1; omega)
  have hb : (0 : ℝ) < A 0 1 := by exact_mod_cast hpos 0 1
  have hc : (0 : ℝ) < A 1 0 := by exact_mod_cast hpos 1 0
  fin_cases i <;> fin_cases j <;> simp only [expandingProjection,
    Matrix.smul_apply,Matrix.sub_apply,smul_eq_mul,realMatrix,Matrix.one_apply]
  · simp only [ite_true,mul_one]
    exact mul_pos hgap (sub_pos.mpr (hmu.trans_le ha))
  · norm_num
    exact mul_pos hgap hb
  · norm_num
    exact mul_pos hgap hc
  · simp only [ite_true,mul_one]
    exact mul_pos hgap (sub_pos.mpr (hmu.trans_le hd))

/-- Unimodular intertwiners preserve the literal integral trace. -/
theorem intertwiner_trace (A B C : IntMatrix) (hC : C.det = 1) (he : C*A = B*C) :
    A 0 0+A 1 1 = B 0 0+B 1 1 := by
  let D : IntMatrix := !![C 1 1,-C 0 1;-C 1 0,C 0 0]
  have hc : C 0 0*C 1 1-C 0 1*C 1 0 = 1 := by simpa only [Matrix.det_fin_two] using hC
  have hDC : D*C = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [D,Matrix.mul_apply,Fin.sum_univ_two] <;> nlinarith only [hc]
  have hCD : C*D = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [D,Matrix.mul_apply,Fin.sum_univ_two] <;> nlinarith only [hc]
  have hab : (D*(C*A)).trace = (D*(B*C)).trace := congrArg (fun M : IntMatrix => (D*M).trace) he
  rw [← Matrix.mul_assoc,hDC,Matrix.one_mul,← Matrix.mul_assoc,
    Matrix.trace_mul_comm,← Matrix.mul_assoc,hCD,Matrix.one_mul] at hab
  simpa only [Matrix.trace,Matrix.diag,Fin.sum_univ_two] using hab

#print axioms realMatrix_pow_spectral
#print axioms normalized_power_tendsto
#print axioms expandingProjection_pos
#print axioms intertwiner_trace


/-- The expanding spectral projection has rank one, expressed without a rank convention. -/
theorem expandingProjection_minor (A : IntMatrix) (hdet : A.det = 1)
    (ht : 2 < A 0 0+A 1 1) :
    expandingProjection A 0 0*expandingProjection A 1 1-
      expandingProjection A 0 1*expandingProjection A 1 0 = 0 := by
  have hlam := (expandingMultiplier_spec ht).1
  have hlam0 : 0 < expandingMultiplier (A 0 0+A 1 1) := by linarith only [hlam]
  have hsum := multiplier_sum A ht
  have hd : (A 0 0 : ℝ)*A 1 1-(A 0 1 : ℝ)*A 1 0 = 1 := by
    have hi : A 0 0*A 1 1-A 0 1*A 1 0 = 1 := by simpa only [Matrix.det_fin_two] using hdet
    exact_mod_cast hi
  have hm := congrArg (fun z : ℝ => (expandingMultiplier (A 0 0+A 1 1))⁻¹*z) hsum
  have hinv := inv_mul_cancel₀ (ne_of_gt hlam0)
  have hz : ((A 0 0 : ℝ)-(expandingMultiplier (A 0 0+A 1 1))⁻¹)*
      ((A 1 1 : ℝ)-(expandingMultiplier (A 0 0+A 1 1))⁻¹)-
      (A 0 1 : ℝ)*A 1 0 = 0 := by nlinarith only [hd,hm,hinv]
  calc
    _ = (expandingMultiplier (A 0 0+A 1 1)-(expandingMultiplier (A 0 0+A 1 1))⁻¹)⁻¹^2*
        (((A 0 0 : ℝ)-(expandingMultiplier (A 0 0+A 1 1))⁻¹)*
          ((A 1 1 : ℝ)-(expandingMultiplier (A 0 0+A 1 1))⁻¹)-(A 0 1 : ℝ)*A 1 0) := by
      simp only [expandingProjection,Matrix.smul_apply,Matrix.sub_apply,smul_eq_mul,realMatrix,
        show (1 : RealMatrix) 0 0 = 1 from rfl,
        show (1 : RealMatrix) 0 1 = 0 from rfl,
        show (1 : RealMatrix) 1 0 = 0 from rfl,
        show (1 : RealMatrix) 1 1 = 1 from rfl,mul_one,mul_zero,sub_zero]
      ring
    _ = 0 := by rw [hz,mul_zero]

private theorem positive_of_positive_relation {a b x y : ℝ}
    (ha : 0 < a) (hb : 0 < b) (he : a*x = b*y) (hy : 0 < y) : 0 < x := by
  by_contra hn
  have hx : x ≤ 0 := le_of_not_gt hn
  have hl := mul_nonpos_of_nonneg_of_nonpos ha.le hx
  have hr := mul_pos hb hy
  linarith only [he,hl,hr]

private theorem negative_of_positive_relation {a b x y : ℝ}
    (ha : 0 < a) (hb : 0 < b) (he : a*x = b*y) (hy : y < 0) : x < 0 := by
  have h := positive_of_positive_relation ha hb
    (show a*(-x) = b*(-y) by nlinarith only [he]) (neg_pos.mpr hy)
  exact neg_pos.mp h

/-- Every integral unimodular intertwiner sends the positive expanding projection
entirely into one strict sign. -/
theorem intertwiner_projection_sign (A B C : IntMatrix) (hA : A.det = 1)
    (hposA : ∀ i j, 0 < A i j) (hposB : ∀ i j, 0 < B i j)
    (hC : C.det = 1) (he : C*A = B*C) :
    (∀ i j, 0 < (realMatrix C*expandingProjection A) i j) ∨
      (∀ i j, (realMatrix C*expandingProjection A) i j < 0) := by
  have ht := positive_trace A hA hposA
  have hP := expandingProjection_pos A hA hposA
  have hminor := expandingProjection_minor A hA ht
  have htrace := intertwiner_trace A B C hC he
  have hsum := multiplier_sum A ht
  have htr : (A 0 0 : ℝ)+A 1 1 = (B 0 0 : ℝ)+B 1 1 := by exact_mod_cast htrace
  have hlam := (expandingMultiplier_spec ht).1
  have hlam0 : 0 < expandingMultiplier (A 0 0+A 1 1) := by linarith only [hlam]
  have hmu : (expandingMultiplier (A 0 0+A 1 1))⁻¹ < 1 := (inv_lt_one₀ hlam0).mpr hlam
  have hdB : (1 : ℝ) ≤ B 1 1 := by
    exact_mod_cast (show (1 : ℤ) ≤ B 1 1 by have h := hposB 1 1; omega)
  have hcoef : 0 < expandingMultiplier (A 0 0+A 1 1)-(B 0 0 : ℝ) := by
    linarith only [hsum,htr,hmu,hdB]
  have hbB : (0 : ℝ) < B 0 1 := by exact_mod_cast hposB 0 1
  let D : RealMatrix := realMatrix C*expandingProjection A
  have hreal : realMatrix C*realMatrix A = realMatrix B*realMatrix C := by
    simpa only [realMatrix_mul] using congrArg realMatrix he
  have hBD : realMatrix B*D = expandingMultiplier (A 0 0+A 1 1) • D := by
    dsimp [D]
    rw [← Matrix.mul_assoc,← hreal,Matrix.mul_assoc,
      (expandingProjection_eigen A hA ht).1,Matrix.mul_smul]
  have hcol : (expandingMultiplier (A 0 0+A 1 1)-(B 0 0 : ℝ))*D 0 1 =
      (B 0 1 : ℝ)*D 1 1 := by
    have hh := congrArg (fun M : RealMatrix => M 0 1) hBD
    simp only [Matrix.mul_apply,Fin.sum_univ_two,Matrix.smul_apply,smul_eq_mul,realMatrix] at hh
    nlinarith only [hh]
  have hdc : (C 0 0 : ℝ)*C 1 1-(C 0 1 : ℝ)*C 1 0 = 1 := by
    have hi : C 0 0*C 1 1-C 0 1*C 1 0 = 1 := by simpa only [Matrix.det_fin_two] using hC
    exact_mod_cast hi
  have hback : (C 1 1 : ℝ)*D 0 1-(C 0 1 : ℝ)*D 1 1 = expandingProjection A 0 1 := by
    have hm := congrArg (fun z : ℝ => z*expandingProjection A 0 1) hdc
    dsimp [D]
    simp only [Matrix.mul_apply,Fin.sum_univ_two,realMatrix]
    nlinarith only [hm]
  have hne : D 1 1 ≠ 0 := by
    intro hn
    rw [hn,mul_zero] at hcol
    have hd01 : D 0 1 = 0 := (mul_eq_zero.mp hcol).resolve_left (ne_of_gt hcoef)
    rw [hn,hd01,mul_zero,mul_zero,sub_self] at hback
    exact (ne_of_gt (hP 0 1)) hback.symm
  have hrow (i : Fin 2) : expandingProjection A 1 1*D i 0 = expandingProjection A 1 0*D i 1 := by
    have hm := congrArg (fun z : ℝ => (C i 0 : ℝ)*z) hminor
    dsimp [D]
    simp only [Matrix.mul_apply,Fin.sum_univ_two,realMatrix]
    nlinarith only [hm]
  rcases lt_trichotomy 0 (D 1 1) with hp | hz | hn
  · have hp01 := positive_of_positive_relation hcoef hbB hcol hp
    have hp00 := positive_of_positive_relation (hP 1 1) (hP 1 0) (hrow 0) hp01
    have hp10 := positive_of_positive_relation (hP 1 1) (hP 1 0) (hrow 1) hp
    left
    intro i j
    change 0 < D i j
    fin_cases i <;> fin_cases j
    · exact hp00
    · exact hp01
    · exact hp10
    · exact hp
  · exact (hne hz.symm).elim
  · have hn01 := negative_of_positive_relation hcoef hbB hcol hn
    have hn00 := negative_of_positive_relation (hP 1 1) (hP 1 0) (hrow 0) hn01
    have hn10 := negative_of_positive_relation (hP 1 1) (hP 1 0) (hrow 1) hn
    right
    intro i j
    change D i j < 0
    fin_cases i <;> fin_cases j
    · exact hn00
    · exact hn01
    · exact hn10
    · exact hn

/-- Left multiplication preserves the normalized matrix-power limit. -/
theorem normalized_intertwiner_tendsto (A C : IntMatrix) (hA : A.det = 1)
    (ht : 2 < A 0 0+A 1 1) (i j : Fin 2) :
    Tendsto (fun n : ℕ => ((C*A^n) i j : ℝ)/expandingMultiplier (A 0 0+A 1 1)^n)
      atTop (𝓝 ((realMatrix C*expandingProjection A) i j)) := by
  have h0 := (normalized_power_tendsto A hA ht 0 j).const_mul (C i 0 : ℝ)
  have h1 := (normalized_power_tendsto A hA ht 1 j).const_mul (C i 1 : ℝ)
  simpa only [Matrix.mul_apply,Fin.sum_univ_two,Int.cast_add,Int.cast_mul,
    add_div,mul_div_assoc,realMatrix] using h0.add h1

#print axioms expandingProjection_minor
#print axioms intertwiner_projection_sign
#print axioms normalized_intertwiner_tendsto


/-- A unimodular intertwiner between positive matrices has one strict entrywise sign
after multiplication by all sufficiently high powers of the source. -/
theorem eventually_intertwiner_one_sign (A B C : IntMatrix) (hA : A.det = 1)
    (hposA : ∀ i j, 0 < A i j) (hposB : ∀ i j, 0 < B i j)
    (hC : C.det = 1) (he : C*A = B*C) :
    (∀ᶠ n : ℕ in atTop, ∀ i j, 0 < (C*A^n) i j) ∨
      (∀ᶠ n : ℕ in atTop, ∀ i j, (C*A^n) i j < 0) := by
  have ht := positive_trace A hA hposA
  have hlam0 : 0 < expandingMultiplier (A 0 0+A 1 1) :=
    lt_trans (by norm_num) (expandingMultiplier_spec ht).1
  rcases intertwiner_projection_sign A B C hA hposA hposB hC he with hp | hn
  · have hev (i j : Fin 2) : ∀ᶠ n : ℕ in atTop, 0 < (C*A^n) i j := by
      have hh : ∀ᶠ n : ℕ in atTop,
          0 < ((C*A^n) i j : ℝ)/expandingMultiplier (A 0 0+A 1 1)^n :=
        (normalized_intertwiner_tendsto A C hA ht i j).eventually (isOpen_Ioi.mem_nhds (hp i j))
      filter_upwards [hh] with n hn
      have h : (0 : ℝ) < (C*A^n) i j := by
        simpa only [zero_mul] using (lt_div_iff₀ (pow_pos hlam0 n)).mp hn
      exact_mod_cast h
    left
    filter_upwards [hev 0 0,hev 0 1,hev 1 0,hev 1 1] with n h00 h01 h10 h11
    intro i j
    fin_cases i <;> fin_cases j
    · exact h00
    · exact h01
    · exact h10
    · exact h11
  · have hev (i j : Fin 2) : ∀ᶠ n : ℕ in atTop, (C*A^n) i j < 0 := by
      have hh : ∀ᶠ n : ℕ in atTop,
          ((C*A^n) i j : ℝ)/expandingMultiplier (A 0 0+A 1 1)^n < 0 :=
        (normalized_intertwiner_tendsto A C hA ht i j).eventually (isOpen_Iio.mem_nhds (hn i j))
      filter_upwards [hh] with n hn
      have h : ((C*A^n) i j : ℝ) < 0 := by
        simpa only [zero_mul] using (div_lt_iff₀ (pow_pos hlam0 n)).mp hn
      exact_mod_cast h
    right
    filter_upwards [hev 0 0,hev 0 1,hev 1 0,hev 1 1] with n h00 h01 h10 h11
    intro i j
    fin_cases i <;> fin_cases j
    · exact h00
    · exact h01
    · exact h10
    · exact h11

/-- Every integral determinant-one intertwiner between positive determinant-one
matrices can be replaced by a strictly positive determinant-one intertwiner. -/
theorem exists_positive_intertwiner (A B C : IntMatrix) (hA : A.det = 1)
    (hposA : ∀ i j, 0 < A i j) (hposB : ∀ i j, 0 < B i j)
    (hC : C.det = 1) (he : C*A = B*C) :
    ∃ D : IntMatrix, D.det = 1 ∧ D*A = B*D ∧ ∀ i j, 0 < D i j := by
  have hdet (n : ℕ) : (C*A^n).det = 1 := by
    rw [Matrix.det_mul,Matrix.det_pow,hC,hA,one_pow,mul_one]
  have hinter (n : ℕ) : (C*A^n)*A = B*(C*A^n) := by
    calc
      _ = C*(A^n*A) := by rw [Matrix.mul_assoc]
      _ = C*(A*A^n) := by rw [← pow_succ,← pow_succ']
      _ = (C*A)*A^n := by rw [Matrix.mul_assoc]
      _ = _ := by rw [he,Matrix.mul_assoc]
  rcases eventually_intertwiner_one_sign A B C hA hposA hposB hC he with hp | hn
  · obtain ⟨n,hn⟩ := hp.exists
    exact ⟨C*A^n,hdet n,hinter n,hn⟩
  · obtain ⟨n,hn⟩ := hn.exists
    refine ⟨-(C*A^n),?_,?_,?_⟩
    · have hd := hdet n
      rw [Matrix.det_fin_two] at hd ⊢
      simp only [Matrix.neg_apply]
      nlinarith only [hd]
    · rw [Matrix.neg_mul,Matrix.mul_neg,hinter n]
    · intro i j
      exact neg_pos.mpr (hn i j)

#print axioms eventually_intertwiner_one_sign
#print axioms exists_positive_intertwiner

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerConjugacy
