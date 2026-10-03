import GaloisForLFunctions.RHTower.ThetaCuspPairRadialRecurrence
import GaloisForLFunctions.RHTower.ThetaCuspOddCentralTailPayment
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Unequal theta-pair energy in odd central coordinates

The unequal theta pair, with its literal exponential weight, has a
uniform quadratic floor on the entire scale-five ray. A degree-seven
Taylor allowance is paid by the literal exponential weight; its degree
matches the largest normalized mixed entry.
A homogeneous diagonal congruence reduces the exact central-basis
matrix to four polynomial principal-minor certificates. Every mixed
entry through reflection order fourteen is retained.
-/

namespace RHTower.ThetaCuspMixedPairOddFourFloor
noncomputable section
open Polynomial Matrix ThetaCuspOddCentralTail

private def radialHomStep (a b : ℝ) (P : ℝ[X]) : ℝ[X] :=
  -(C 4*((X^2-C (4*a))*(C (b^2)*P.derivative.derivative-C (2*b)*P.derivative+P)+
    X*(C (b^2)*P.derivative-C b*P)))

private def radialHom (a b : ℝ) : ℕ → ℝ[X]
  | 0 => C (4*a+9*b^2)-C (6*b)*X
  | k+1 => radialHomStep a b (radialHom a b k)

private theorem radialHom_one (a : ℝ) (k : ℕ) :
    radialHom a 1 k=thetaPairRadialEvenPolynomial a k := by
  induction k with
  | zero => simp [radialHom, thetaPairRadialEvenPolynomial]
  | succ k ih =>
    simp [radialHom, ih, radialHomStep, thetaPairRadialEvenPolynomial, thetaPairRadialEvenStep]

private def radialNorm0 (a b : ℝ) : {P : ℝ[X] // radialHom a b 0=P} := by
  have h : radialHom a b 0=radialHom a b 0 := rfl
  conv at h =>
    rhs
    norm_num [radialHom, C_add, C_mul, C_pow, C_ofNat]
    ring_nf (config := {mode := .raw})
  exact ⟨_, h⟩

private def radialNorm1 (a b : ℝ) : {P : ℝ[X] // radialHom a b 1=P} := by
  have h : radialHom a b 1=radialHom a b 1 := rfl
  conv at h =>
    rhs
    rw [radialHom, (radialNorm0 a b).property]
    dsimp only [radialNorm0]
    unfold radialHomStep
    norm_num [derivative_sub, derivative_add, derivative_neg, derivative_mul, derivative_pow, derivative_C, derivative_X, C_add, C_mul, C_pow, C_ofNat]
    ring_nf (config := {mode := .raw})
  exact ⟨_, h⟩

private def radialNorm2 (a b : ℝ) : {P : ℝ[X] // radialHom a b 2=P} := by
  have h : radialHom a b 2=radialHom a b 2 := rfl
  conv at h =>
    rhs
    rw [radialHom, (radialNorm1 a b).property]
    dsimp only [radialNorm1]
    unfold radialHomStep
    norm_num [derivative_sub, derivative_add, derivative_neg, derivative_mul, derivative_pow, derivative_C, derivative_X, C_add, C_mul, C_pow, C_ofNat]
    ring_nf (config := {mode := .raw})
  exact ⟨_, h⟩

private def radialNorm3 (a b : ℝ) : {P : ℝ[X] // radialHom a b 3=P} := by
  have h : radialHom a b 3=radialHom a b 3 := rfl
  conv at h =>
    rhs
    rw [radialHom, (radialNorm2 a b).property]
    dsimp only [radialNorm2]
    unfold radialHomStep
    norm_num [derivative_sub, derivative_add, derivative_neg, derivative_mul, derivative_pow, derivative_C, derivative_X, C_add, C_mul, C_pow, C_ofNat]
    ring_nf (config := {mode := .raw})
  exact ⟨_, h⟩

private def radialNorm4 (a b : ℝ) : {P : ℝ[X] // radialHom a b 4=P} := by
  have h : radialHom a b 4=radialHom a b 4 := rfl
  conv at h =>
    rhs
    rw [radialHom, (radialNorm3 a b).property]
    dsimp only [radialNorm3]
    unfold radialHomStep
    norm_num [derivative_sub, derivative_add, derivative_neg, derivative_mul, derivative_pow, derivative_C, derivative_X, C_add, C_mul, C_pow, C_ofNat]
    ring_nf (config := {mode := .raw})
  exact ⟨_, h⟩

private def radialNorm5 (a b : ℝ) : {P : ℝ[X] // radialHom a b 5=P} := by
  have h : radialHom a b 5=radialHom a b 5 := rfl
  conv at h =>
    rhs
    rw [radialHom, (radialNorm4 a b).property]
    dsimp only [radialNorm4]
    unfold radialHomStep
    norm_num [derivative_sub, derivative_add, derivative_neg, derivative_mul, derivative_pow, derivative_C, derivative_X, C_add, C_mul, C_pow, C_ofNat]
    ring_nf (config := {mode := .raw})
  exact ⟨_, h⟩

private def radialNorm6 (a b : ℝ) : {P : ℝ[X] // radialHom a b 6=P} := by
  have h : radialHom a b 6=radialHom a b 6 := rfl
  conv at h =>
    rhs
    rw [radialHom, (radialNorm5 a b).property]
    dsimp only [radialNorm5]
    unfold radialHomStep
    norm_num [derivative_sub, derivative_add, derivative_neg, derivative_mul, derivative_pow, derivative_C, derivative_X, C_add, C_mul, C_pow, C_ofNat]
    ring_nf (config := {mode := .raw})
  exact ⟨_, h⟩

private def radialNorm7 (a b : ℝ) : {P : ℝ[X] // radialHom a b 7=P} := by
  have h : radialHom a b 7=radialHom a b 7 := rfl
  conv at h =>
    rhs
    rw [radialHom, (radialNorm6 a b).property]
    dsimp only [radialNorm6]
    unfold radialHomStep
    norm_num [derivative_sub, derivative_add, derivative_neg, derivative_mul, derivative_pow, derivative_C, derivative_X, C_add, C_mul, C_pow, C_ofNat]
    ring_nf (config := {mode := .raw})
  exact ⟨_, h⟩

private def mixedDenomHom (a b : ℝ) : ℝ :=
  8*a*(2*a-3*b)^2*(43008*a^3)^2*b^7

private def radialValue1 (a b : ℝ) :
    {r : ℝ // (radialHom (4*a^2) b 1).eval (5*a)=r} := by
  have h : (radialHom (4*a^2) b 1).eval (5*a) =
      (radialHom (4*a^2) b 1).eval (5*a) := rfl
  conv at h =>
    rhs
    rw [(radialNorm1 (4*a^2) b).property]
    dsimp only [radialNorm1]
    norm_num
    ring_nf
  exact ⟨_,h⟩

private def radialValue2 (a b : ℝ) :
    {r : ℝ // (radialHom (4*a^2) b 2).eval (5*a)=r} := by
  have h : (radialHom (4*a^2) b 2).eval (5*a) =
      (radialHom (4*a^2) b 2).eval (5*a) := rfl
  conv at h =>
    rhs
    rw [(radialNorm2 (4*a^2) b).property]
    dsimp only [radialNorm2]
    norm_num
    ring_nf
  exact ⟨_,h⟩

private def radialValue3 (a b : ℝ) :
    {r : ℝ // (radialHom (4*a^2) b 3).eval (5*a)=r} := by
  have h : (radialHom (4*a^2) b 3).eval (5*a) =
      (radialHom (4*a^2) b 3).eval (5*a) := rfl
  conv at h =>
    rhs
    rw [(radialNorm3 (4*a^2) b).property]
    dsimp only [radialNorm3]
    norm_num
    ring_nf
  exact ⟨_,h⟩

private def radialValue4 (a b : ℝ) :
    {r : ℝ // (radialHom (4*a^2) b 4).eval (5*a)=r} := by
  have h : (radialHom (4*a^2) b 4).eval (5*a) =
      (radialHom (4*a^2) b 4).eval (5*a) := rfl
  conv at h =>
    rhs
    rw [(radialNorm4 (4*a^2) b).property]
    dsimp only [radialNorm4]
    norm_num
    ring_nf
  exact ⟨_,h⟩

private def radialValue5 (a b : ℝ) :
    {r : ℝ // (radialHom (4*a^2) b 5).eval (5*a)=r} := by
  have h : (radialHom (4*a^2) b 5).eval (5*a) =
      (radialHom (4*a^2) b 5).eval (5*a) := rfl
  conv at h =>
    rhs
    rw [(radialNorm5 (4*a^2) b).property]
    dsimp only [radialNorm5]
    norm_num
    ring_nf
  exact ⟨_,h⟩

private def radialValue6 (a b : ℝ) :
    {r : ℝ // (radialHom (4*a^2) b 6).eval (5*a)=r} := by
  have h : (radialHom (4*a^2) b 6).eval (5*a) =
      (radialHom (4*a^2) b 6).eval (5*a) := rfl
  conv at h =>
    rhs
    rw [(radialNorm6 (4*a^2) b).property]
    dsimp only [radialNorm6]
    norm_num
    ring_nf
  exact ⟨_,h⟩

private def radialValue7 (a b : ℝ) :
    {r : ℝ // (radialHom (4*a^2) b 7).eval (5*a)=r} := by
  have h : (radialHom (4*a^2) b 7).eval (5*a) =
      (radialHom (4*a^2) b 7).eval (5*a) := rfl
  conv at h =>
    rhs
    rw [(radialNorm7 (4*a^2) b).property]
    dsimp only [radialNorm7]
    norm_num
    ring_nf
  exact ⟨_,h⟩

private def homogeneousBasis (a b : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![43008*a^3*b^3, (43008*a^3-7168*a^2*b)*b^3,
      (53760*a^3-17920*a^2*b+3584*a*b^2)*b^3,
      (53760*a^3-26880*a^2*b+10752*a*b^2-2304*b^3)*b^3;
    0, -1792*a^2*b^2, (-4480*a^2+1120*a*b)*b^2,
      (-6720*a^2+3360*a*b-784*b^2)*b^2;
    0, 0, 56*a*b, (168*a-56*b)*b;
    0, 0, 0, -1]

private def mixedHomEntry (a b : ℝ) (i j : Fin 4) : ℝ :=
  ∑ r : Fin 4, ∑ s : Fin 4,
    homogeneousBasis a b r i * homogeneousBasis a b s j *
      (radialHom (4*a^2) b (r.val+s.val+1)).eval (5*a)

private def columnScale (a b : ℝ) : Fin 4 → ℝ := ![(a*b)^3,(a*b)^2,a*b,1]

private def reducedBasis (a b : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![43008, b*(43008*a-7168*b), b^2*(53760*a^2-17920*a*b+3584*b^2),
      b^3*(53760*a^3-26880*a^2*b+10752*a*b^2-2304*b^3);
    0, -1792, b*(-4480*a+1120*b), b^2*(-6720*a^2+3360*a*b-784*b^2);
    0, 0, 56, b*(168*a-56*b);
    0, 0, 0, -1]

private theorem homogeneousBasis_factor (a b : ℝ) (i j : Fin 4) :
    homogeneousBasis a b i j = columnScale a b j*reducedBasis a b i j := by
  fin_cases i <;> fin_cases j <;> norm_num [homogeneousBasis,columnScale,reducedBasis]
  all_goals ring

private def reducedEntry (a b : ℝ) (i j : Fin 4) : ℝ :=
  ∑ r : Fin 4, ∑ s : Fin 4,
    reducedBasis a b r i*reducedBasis a b s j*
      (radialHom (4*a^2) b (r.val+s.val+1)).eval (5*a)

private theorem mixedHomEntry_factor (a b : ℝ) (i j : Fin 4) :
    mixedHomEntry a b i j = columnScale a b i*columnScale a b j*reducedEntry a b i j := by
  unfold mixedHomEntry reducedEntry
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [homogeneousBasis_factor,homogeneousBasis_factor]
  ring

private def reducedEntryNorm00 (a b : ℝ) : {r : ℝ // reducedEntry a b 0 0=r} := by
  have h : reducedEntry a b 0 0=reducedEntry a b 0 0 := rfl
  conv at h =>
    rhs
    norm_num [reducedEntry,reducedBasis,Fin.sum_univ_succ]
    simp only [(radialValue1 a b).property, (radialValue2 a b).property, (radialValue3 a b).property, (radialValue4 a b).property, (radialValue5 a b).property, (radialValue6 a b).property, (radialValue7 a b).property]
    dsimp only [radialValue1, radialValue2, radialValue3, radialValue4, radialValue5, radialValue6, radialValue7]
    ring_nf
  exact ⟨_,h⟩

private def reducedEntryNorm01 (a b : ℝ) : {r : ℝ // reducedEntry a b 0 1=r} := by
  have h : reducedEntry a b 0 1=reducedEntry a b 0 1 := rfl
  conv at h =>
    rhs
    norm_num [reducedEntry,reducedBasis,Fin.sum_univ_succ]
    simp only [(radialValue1 a b).property, (radialValue2 a b).property, (radialValue3 a b).property, (radialValue4 a b).property, (radialValue5 a b).property, (radialValue6 a b).property, (radialValue7 a b).property]
    dsimp only [radialValue1, radialValue2, radialValue3, radialValue4, radialValue5, radialValue6, radialValue7]
    ring_nf
  exact ⟨_,h⟩

private def reducedEntryNorm11 (a b : ℝ) : {r : ℝ // reducedEntry a b 1 1=r} := by
  have h : reducedEntry a b 1 1=reducedEntry a b 1 1 := rfl
  conv at h =>
    rhs
    norm_num [reducedEntry,reducedBasis,Fin.sum_univ_succ]
    simp only [(radialValue1 a b).property, (radialValue2 a b).property, (radialValue3 a b).property, (radialValue4 a b).property, (radialValue5 a b).property, (radialValue6 a b).property, (radialValue7 a b).property]
    dsimp only [radialValue1, radialValue2, radialValue3, radialValue4, radialValue5, radialValue6, radialValue7]
    ring_nf
  exact ⟨_,h⟩

private def scalarEntryNorm00 (a b : ℝ) : {r : ℝ // reducedEntry a b 0 0=r} := reducedEntryNorm00 a b

private def scalarEntryNorm01 (a b : ℝ) : {r : ℝ // reducedEntry a b 0 1=r} := reducedEntryNorm01 a b

private def scalarEntryNorm02 (a b : ℝ) : {r : ℝ // reducedEntry a b 0 2=r} := by
  have h : reducedEntry a b 0 2=reducedEntry a b 0 2 := rfl
  conv at h =>
    rhs
    norm_num [reducedEntry,reducedBasis,Fin.sum_univ_succ,
      Matrix.cons_val_two,Matrix.cons_val_three]
    simp only [(radialValue1 a b).property, (radialValue2 a b).property, (radialValue3 a b).property, (radialValue4 a b).property, (radialValue5 a b).property, (radialValue6 a b).property, (radialValue7 a b).property]
    dsimp only [radialValue1, radialValue2, radialValue3, radialValue4, radialValue5, radialValue6, radialValue7]
    ring_nf
  exact ⟨_,h⟩

private def scalarEntryNorm03 (a b : ℝ) : {r : ℝ // reducedEntry a b 0 3=r} := by
  have h : reducedEntry a b 0 3=reducedEntry a b 0 3 := rfl
  conv at h =>
    rhs
    norm_num [reducedEntry,reducedBasis,Fin.sum_univ_succ,
      Matrix.cons_val_two,Matrix.cons_val_three]
    simp only [(radialValue1 a b).property, (radialValue2 a b).property, (radialValue3 a b).property, (radialValue4 a b).property, (radialValue5 a b).property, (radialValue6 a b).property, (radialValue7 a b).property]
    dsimp only [radialValue1, radialValue2, radialValue3, radialValue4, radialValue5, radialValue6, radialValue7]
    ring_nf
  exact ⟨_,h⟩

private def scalarEntryNorm11 (a b : ℝ) : {r : ℝ // reducedEntry a b 1 1=r} := reducedEntryNorm11 a b

private def scalarEntryNorm12 (a b : ℝ) : {r : ℝ // reducedEntry a b 1 2=r} := by
  have h : reducedEntry a b 1 2=reducedEntry a b 1 2 := rfl
  conv at h =>
    rhs
    norm_num [reducedEntry,reducedBasis,Fin.sum_univ_succ,
      Matrix.cons_val_two,Matrix.cons_val_three]
    simp only [(radialValue1 a b).property, (radialValue2 a b).property, (radialValue3 a b).property, (radialValue4 a b).property, (radialValue5 a b).property, (radialValue6 a b).property, (radialValue7 a b).property]
    dsimp only [radialValue1, radialValue2, radialValue3, radialValue4, radialValue5, radialValue6, radialValue7]
    ring_nf
  exact ⟨_,h⟩

private def scalarEntryNorm13 (a b : ℝ) : {r : ℝ // reducedEntry a b 1 3=r} := by
  have h : reducedEntry a b 1 3=reducedEntry a b 1 3 := rfl
  conv at h =>
    rhs
    norm_num [reducedEntry,reducedBasis,Fin.sum_univ_succ,
      Matrix.cons_val_two,Matrix.cons_val_three]
    simp only [(radialValue1 a b).property, (radialValue2 a b).property, (radialValue3 a b).property, (radialValue4 a b).property, (radialValue5 a b).property, (radialValue6 a b).property, (radialValue7 a b).property]
    dsimp only [radialValue1, radialValue2, radialValue3, radialValue4, radialValue5, radialValue6, radialValue7]
    ring_nf
  exact ⟨_,h⟩

private def scalarEntryNorm22 (a b : ℝ) : {r : ℝ // reducedEntry a b 2 2=r} := by
  have h : reducedEntry a b 2 2=reducedEntry a b 2 2 := rfl
  conv at h =>
    rhs
    norm_num [reducedEntry,reducedBasis,Fin.sum_univ_succ,
      Matrix.cons_val_two,Matrix.cons_val_three]
    simp only [(radialValue1 a b).property, (radialValue2 a b).property, (radialValue3 a b).property, (radialValue4 a b).property, (radialValue5 a b).property, (radialValue6 a b).property, (radialValue7 a b).property]
    dsimp only [radialValue1, radialValue2, radialValue3, radialValue4, radialValue5, radialValue6, radialValue7]
    ring_nf
  exact ⟨_,h⟩

private def scalarEntryNorm23 (a b : ℝ) : {r : ℝ // reducedEntry a b 2 3=r} := by
  have h : reducedEntry a b 2 3=reducedEntry a b 2 3 := rfl
  conv at h =>
    rhs
    norm_num [reducedEntry,reducedBasis,Fin.sum_univ_succ,
      Matrix.cons_val_two,Matrix.cons_val_three]
    simp only [(radialValue1 a b).property, (radialValue2 a b).property, (radialValue3 a b).property, (radialValue4 a b).property, (radialValue5 a b).property, (radialValue6 a b).property, (radialValue7 a b).property]
    dsimp only [radialValue1, radialValue2, radialValue3, radialValue4, radialValue5, radialValue6, radialValue7]
    ring_nf
  exact ⟨_,h⟩

private def scalarEntryNorm33 (a b : ℝ) : {r : ℝ // reducedEntry a b 3 3=r} := by
  have h : reducedEntry a b 3 3=reducedEntry a b 3 3 := rfl
  conv at h =>
    rhs
    norm_num [reducedEntry,reducedBasis,Fin.sum_univ_succ,
      Matrix.cons_val_two,Matrix.cons_val_three]
    simp only [(radialValue1 a b).property, (radialValue2 a b).property, (radialValue3 a b).property, (radialValue4 a b).property, (radialValue5 a b).property, (radialValue6 a b).property, (radialValue7 a b).property]
    dsimp only [radialValue1, radialValue2, radialValue3, radialValue4, radialValue5, radialValue6, radialValue7]
    ring_nf
  exact ⟨_,h⟩

private def reducedDetSym4 (a b c d e f g h i j : ℝ) : ℝ :=
  (a*e*h-a*f^2-b^2*h+2*b*c*f-c^2*e)*j -
  ((e*h-f^2)*d^2+2*(c*f-b*h)*d*g+2*(b*f-c*e)*d*i+
   (a*h-c^2)*g^2+2*(b*c-a*f)*g*i+(a*e-b^2)*i^2)

/-- Mixed first/second-atom radial matrix in the normalized odd central basis. -/
def mixedCentralMatrix (q : ℝ) (i j : Fin 4) : ℝ :=
  ∑ r : Fin 4, ∑ s : Fin 4,
    centralBasis (1/q) r i * centralBasis (1/q) s j *
      (thetaPairRadialEvenPolynomial (4*q^2) (r.val+s.val+1)).eval (5*q) /
        (8*q*(2*q-3)^2)

private theorem homogeneousBasis_one {q : ℝ} (hq : q ≠ 0) (i j : Fin 4) :
    homogeneousBasis q 1 i j = 43008*q^3*centralBasis (1/q) i j := by
  fin_cases i <;> fin_cases j <;> norm_num [homogeneousBasis, centralBasis]
  all_goals field_simp [hq]
  all_goals ring

private theorem scale_division (C u v R d : ℝ) (hd : d ≠ 0) :
    (C*u)*(C*v)*R=(d*C^2)*(u*v*R/d) := by
  field_simp [hd]

private theorem mixedHomEntry_one {q : ℝ} (hq : 5 ≤ q) (i j : Fin 4) :
    mixedHomEntry q 1 i j = mixedDenomHom q 1 * mixedCentralMatrix q i j := by
  have hq0 : q ≠ 0 := by linarith
  have hq3 : 2*q-3 ≠ 0 := by linarith
  unfold mixedHomEntry mixedCentralMatrix
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [homogeneousBasis_one hq0, homogeneousBasis_one hq0, radialHom_one]
  have hD : 8*q*(2*q-3)^2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hq0) (pow_ne_zero 2 hq3)
  simpa only [mixedDenomHom,one_pow,mul_one] using
    scale_division (43008*q^3) (centralBasis (1/q) r i) (centralBasis (1/q) s j)
      ((thetaPairRadialEvenPolynomial (4*q^2) (r.val+s.val+1)).eval (5*q))
      (8*q*(2*q-3)^2) hD

private def symQuadratic (a b c d e f g h i j x y z w : ℝ) : ℝ :=
  a*x^2+2*b*x*y+2*c*x*z+2*d*x*w+e*y^2+2*f*y*z+2*g*y*w+
    h*z^2+2*i*z*w+j*w^2

private theorem symQuadratic_nonneg {a b c d e f g h i j : ℝ}
    (ha : 0 < a) (h2 : 0 < a*e-b^2)
    (h3 : 0 < a*e*h-a*f^2-b^2*h+2*b*c*f-c^2*e)
    (h4 : 0 ≤ reducedDetSym4 a b c d e f g h i j) (x y z w : ℝ) :
    0 ≤ symQuadratic a b c d e f g h i j x y z w := by
  let D2 := a*e-b^2
  let D3 := a*e*h-a*f^2-b^2*h+2*b*c*f-c^2*e
  let E := a*e*i-a*f*g-b^2*i+b*c*g+b*d*f-c*d*e
  have he : a*D2*D3*symQuadratic a b c d e f g h i j x y z w =
      D2*D3*(a*x+b*y+c*z+d*w)^2 +
      D3*(D2*y+(a*f-b*c)*z+(a*g-b*d)*w)^2 +
      a*(D3*z+E*w)^2+a*D2*reducedDetSym4 a b c d e f g h i j*w^2 := by
    dsimp [D2,D3,E,symQuadratic,reducedDetSym4]
    ring
  have hd2 : 0 < D2 := h2
  have hd3 : 0 < D3 := h3
  have hp : 0 ≤ a*D2*D3*symQuadratic a b c d e f g h i j x y z w := by
    rw [he]
    positivity
  exact (mul_nonneg_iff_of_pos_left (mul_pos (mul_pos ha hd2) hd3)).mp hp

private theorem reducedEntry_symm (a b : ℝ) (i j : Fin 4) :
    reducedEntry a b i j = reducedEntry a b j i := by
  unfold reducedEntry
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  rw [Nat.add_comm s.val r.val]
  ring

private theorem symmetric_sum_diagonal_identity (M : Fin 4 → Fin 4 → ℝ)
    (hM : ∀ i j, M i j = M j i) (c y : Fin 4 → ℝ) :
    (∑ i : Fin 4, ∑ j : Fin 4, y i*y j*M i j) + (∑ i : Fin 4, c i*y i^2) =
      symQuadratic (M 0 0+c 0) (M 0 1) (M 0 2) (M 0 3)
        (M 1 1+c 1) (M 1 2) (M 1 3) (M 2 2+c 2) (M 2 3) (M 3 3+c 3)
        (y 0) (y 1) (y 2) (y 3) := by
  norm_num [Fin.sum_univ_succ,symQuadratic]
  simp only [show (Fin.succ (2 : Fin 3) : Fin 4) = 3 by rfl]
  rw [hM 1 0,hM 2 0,hM 3 0,hM 2 1,hM 3 1,hM 3 2]
  ring

private theorem exp_three_lower : (20:ℝ) ≤ Real.exp 3 := by
  have h1 : (2718/1000:ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2718/1000) h1 3
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp
  linarith

private def expCredit7 (q : ℝ) : ℝ :=
  1+3*(q-5)+(3*(q-5))^2/2+(3*(q-5))^3/6+(3*(q-5))^4/24+
    (3*(q-5))^5/120+(3*(q-5))^6/720+(3*(q-5))^7/5040

private def globalShift (q z : ℝ) (i : Fin 4) : ℝ :=
  10000*z*8*43008^2*q^(1+2*i.val)*(2*q-3)^2

private def globalShiftedEntry (q z : ℝ) (i j : Fin 4) : ℝ :=
  reducedEntry q 1 i j+if i=j then globalShift q z i else 0

private theorem globalShift_factor (q z : ℝ) (i : Fin 4) :
    (columnScale q 1 i)^2*globalShift q z i=10000*z*mixedDenomHom q 1 := by
  fin_cases i <;> norm_num [columnScale,globalShift,mixedDenomHom] <;> ring

private def globalMinor1 (q z : ℝ) : ℝ := globalShiftedEntry q z 0 0

private def globalMinor2 (q z : ℝ) : ℝ :=
  globalShiftedEntry q z 0 0*globalShiftedEntry q z 1 1-(globalShiftedEntry q z 0 1)^2

private def globalMinor3 (q z : ℝ) : ℝ :=
  let m := globalShiftedEntry q z
  m 0 0*m 1 1*m 2 2-m 0 0*(m 1 2)^2-(m 0 1)^2*m 2 2+
    2*m 0 1*m 0 2*m 1 2-(m 0 2)^2*m 1 1

private def globalMinor4 (q z : ℝ) : ℝ :=
  let m := globalShiftedEntry q z
  reducedDetSym4 (m 0 0) (m 0 1) (m 0 2) (m 0 3)
    (m 1 1) (m 1 2) (m 1 3) (m 2 2) (m 2 3) (m 3 3)

private def globalMinorNorm1 (q z : ℝ) : {r : ℝ // globalMinor1 q z=r} := by
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have h02 : (0 : Fin 4) ≠ 2 := by decide
  have h12 : (1 : Fin 4) ≠ 2 := by decide
  have h : globalMinor1 q z=globalMinor1 q z := rfl
  conv at h =>
    rhs
    norm_num [globalMinor1,globalShiftedEntry,globalShift,h01,h02,h12]
    simp only [(scalarEntryNorm00 q 1).property, (scalarEntryNorm01 q 1).property, (scalarEntryNorm02 q 1).property, (scalarEntryNorm03 q 1).property, (scalarEntryNorm11 q 1).property, (scalarEntryNorm12 q 1).property, (scalarEntryNorm13 q 1).property, (scalarEntryNorm22 q 1).property, (scalarEntryNorm23 q 1).property, (scalarEntryNorm33 q 1).property]
    dsimp only [scalarEntryNorm00, scalarEntryNorm01, scalarEntryNorm02, scalarEntryNorm03, scalarEntryNorm11, scalarEntryNorm12, scalarEntryNorm13, scalarEntryNorm22, scalarEntryNorm23, scalarEntryNorm33, reducedEntryNorm00,reducedEntryNorm01,reducedEntryNorm11]
    ring_nf
  exact ⟨_,h⟩

private theorem globalMinor1_pos {u : ℝ} (hu : 0 ≤ u) :
    0 < globalMinor1 (5+u) (expCredit7 (5+u)) := by
  rw [(globalMinorNorm1 (5+u) (expCredit7 (5+u))).property]
  dsimp only [globalMinorNorm1,expCredit7]
  ring_nf
  positivity


private def globalMinorNorm2 (q z : ℝ) : {r : ℝ // globalMinor2 q z=r} := by
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have h02 : (0 : Fin 4) ≠ 2 := by decide
  have h12 : (1 : Fin 4) ≠ 2 := by decide
  have h : globalMinor2 q z=globalMinor2 q z := rfl
  conv at h =>
    rhs
    norm_num [globalMinor2,globalShiftedEntry,globalShift,h01,h02,h12]
    simp only [(scalarEntryNorm00 q 1).property, (scalarEntryNorm01 q 1).property, (scalarEntryNorm02 q 1).property, (scalarEntryNorm03 q 1).property, (scalarEntryNorm11 q 1).property, (scalarEntryNorm12 q 1).property, (scalarEntryNorm13 q 1).property, (scalarEntryNorm22 q 1).property, (scalarEntryNorm23 q 1).property, (scalarEntryNorm33 q 1).property]
    dsimp only [scalarEntryNorm00, scalarEntryNorm01, scalarEntryNorm02, scalarEntryNorm03, scalarEntryNorm11, scalarEntryNorm12, scalarEntryNorm13, scalarEntryNorm22, scalarEntryNorm23, scalarEntryNorm33, reducedEntryNorm00,reducedEntryNorm01,reducedEntryNorm11]
    ring_nf
  exact ⟨_,h⟩

private theorem globalMinor2_pos {u : ℝ} (hu : 0 ≤ u) :
    0 < globalMinor2 (5+u) (expCredit7 (5+u)) := by
  rw [(globalMinorNorm2 (5+u) (expCredit7 (5+u))).property]
  dsimp only [globalMinorNorm2,expCredit7]
  ring_nf
  positivity


private def globalMinorNorm3 (q z : ℝ) : {r : ℝ // globalMinor3 q z=r} := by
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have h02 : (0 : Fin 4) ≠ 2 := by decide
  have h12 : (1 : Fin 4) ≠ 2 := by decide
  have h : globalMinor3 q z=globalMinor3 q z := rfl
  conv at h =>
    rhs
    norm_num [globalMinor3,globalShiftedEntry,globalShift,h01,h02,h12]
    simp only [(scalarEntryNorm00 q 1).property, (scalarEntryNorm01 q 1).property, (scalarEntryNorm02 q 1).property, (scalarEntryNorm03 q 1).property, (scalarEntryNorm11 q 1).property, (scalarEntryNorm12 q 1).property, (scalarEntryNorm13 q 1).property, (scalarEntryNorm22 q 1).property, (scalarEntryNorm23 q 1).property, (scalarEntryNorm33 q 1).property]
    dsimp only [scalarEntryNorm00, scalarEntryNorm01, scalarEntryNorm02, scalarEntryNorm03, scalarEntryNorm11, scalarEntryNorm12, scalarEntryNorm13, scalarEntryNorm22, scalarEntryNorm23, scalarEntryNorm33, reducedEntryNorm00,reducedEntryNorm01,reducedEntryNorm11]
    ring_nf
  exact ⟨_,h⟩

private theorem globalMinor3_pos {u : ℝ} (hu : 0 ≤ u) :
    0 < globalMinor3 (5+u) (expCredit7 (5+u)) := by
  rw [(globalMinorNorm3 (5+u) (expCredit7 (5+u))).property]
  dsimp only [globalMinorNorm3,expCredit7]
  ring_nf
  positivity


private theorem expCredit7_le {q : ℝ} (hq : 5 ≤ q) :
    expCredit7 q ≤ Real.exp (3*(q-5)) := by
  have h := Real.sum_le_exp_of_nonneg (show 0 ≤ 3*(q-5) by linarith) 8
  norm_num [Finset.sum_range_succ] at h
  unfold expCredit7
  convert h using 1

private theorem global_exponential_payment {q : ℝ} (hq : 5 ≤ q) :
    8*Real.exp (-3*q)*(10000*expCredit7 q) ≤ (1/40:ℝ) := by
  have h15 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤20) exp_three_lower 5
  rw [← Real.exp_nat_mul] at h15
  norm_num at h15
  have hqm : 0 ≤ q-5 := by linarith
  have hc : 0 ≤ expCredit7 q := by unfold expCredit7; positivity
  have he := mul_le_mul h15 (expCredit7_le hq) hc (Real.exp_pos 15).le
  rw [← Real.exp_add,show 15+3*(q-5)=3*q by ring] at he
  have hpay : 80000*expCredit7 q/Real.exp (3*q) ≤ (1/40:ℝ) := by
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    nlinarith only [he]
  rw [show -3*q=-(3*q) by ring,Real.exp_neg]
  convert hpay using 1
  ring


private def globalCofactor (q z : ℝ) (k : Fin 6) : ℝ :=
  let m := globalShiftedEntry q z
  match k.val with
  | 0 => m 1 1*m 2 2-(m 1 2)^2
  | 1 => m 0 2*m 1 2-m 0 1*m 2 2
  | 2 => m 0 1*m 1 2-m 0 2*m 1 1
  | 3 => m 0 0*m 2 2-(m 0 2)^2
  | 4 => m 0 1*m 0 2-m 0 0*m 1 2
  | _ => m 0 0*m 1 1-(m 0 1)^2

private def globalDetTerm (q z : ℝ) (k : Fin 7) : ℝ :=
  let m := globalShiftedEntry q z
  let C := globalCofactor q z
  match k.val with
  | 0 => globalMinor3 q z*m 3 3
  | 1 => C 0*(m 0 3)^2
  | 2 => 2*C 1*m 0 3*m 1 3
  | 3 => 2*C 2*m 0 3*m 2 3
  | 4 => C 3*(m 1 3)^2
  | 5 => 2*C 4*m 1 3*m 2 3
  | _ => C 5*(m 2 3)^2

private theorem globalMinor4_eq_terms (q z : ℝ) :
    globalMinor4 q z = globalDetTerm q z 0 - globalDetTerm q z 1 -
      globalDetTerm q z 2 - globalDetTerm q z 3 - globalDetTerm q z 4 -
      globalDetTerm q z 5 - globalDetTerm q z 6 := by
  norm_num [globalMinor4, globalDetTerm, globalCofactor, globalMinor3, reducedDetSym4,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  ring

private def globalCofactorNorm0 (q z : ℝ) : {r : ℝ // globalCofactor q z 0=r} := by
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have h02 : (0 : Fin 4) ≠ 2 := by decide
  have h03 : (0 : Fin 4) ≠ 3 := by decide
  have h12 : (1 : Fin 4) ≠ 2 := by decide
  have h13 : (1 : Fin 4) ≠ 3 := by decide
  have h23 : (2 : Fin 4) ≠ 3 := by decide
  have h : globalCofactor q z 0=globalCofactor q z 0 := rfl
  conv at h =>
    rhs
    norm_num [globalCofactor, globalShiftedEntry, globalShift, h01,h02,h03,h12,h13,h23]
    simp only [(scalarEntryNorm00 q 1).property, (scalarEntryNorm01 q 1).property, (scalarEntryNorm02 q 1).property, (scalarEntryNorm03 q 1).property, (scalarEntryNorm11 q 1).property, (scalarEntryNorm12 q 1).property, (scalarEntryNorm13 q 1).property, (scalarEntryNorm22 q 1).property, (scalarEntryNorm23 q 1).property, (scalarEntryNorm33 q 1).property]
    dsimp only [scalarEntryNorm00, scalarEntryNorm01, scalarEntryNorm02, scalarEntryNorm03, scalarEntryNorm11, scalarEntryNorm12, scalarEntryNorm13, scalarEntryNorm22, scalarEntryNorm23, scalarEntryNorm33, reducedEntryNorm00,reducedEntryNorm01,reducedEntryNorm11, globalShift]
    norm_num [h01,h02,h03,h12,h13,h23]
    ring_nf
  exact ⟨_,h⟩

private def globalCofactorNorm1 (q z : ℝ) : {r : ℝ // globalCofactor q z 1=r} := by
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have h02 : (0 : Fin 4) ≠ 2 := by decide
  have h03 : (0 : Fin 4) ≠ 3 := by decide
  have h12 : (1 : Fin 4) ≠ 2 := by decide
  have h13 : (1 : Fin 4) ≠ 3 := by decide
  have h23 : (2 : Fin 4) ≠ 3 := by decide
  have h : globalCofactor q z 1=globalCofactor q z 1 := rfl
  conv at h =>
    rhs
    norm_num [globalCofactor, globalShiftedEntry, globalShift, h01,h02,h03,h12,h13,h23]
    simp only [(scalarEntryNorm00 q 1).property, (scalarEntryNorm01 q 1).property, (scalarEntryNorm02 q 1).property, (scalarEntryNorm03 q 1).property, (scalarEntryNorm11 q 1).property, (scalarEntryNorm12 q 1).property, (scalarEntryNorm13 q 1).property, (scalarEntryNorm22 q 1).property, (scalarEntryNorm23 q 1).property, (scalarEntryNorm33 q 1).property]
    dsimp only [scalarEntryNorm00, scalarEntryNorm01, scalarEntryNorm02, scalarEntryNorm03, scalarEntryNorm11, scalarEntryNorm12, scalarEntryNorm13, scalarEntryNorm22, scalarEntryNorm23, scalarEntryNorm33, reducedEntryNorm00,reducedEntryNorm01,reducedEntryNorm11, globalShift]
    norm_num [h01,h02,h03,h12,h13,h23]
    ring_nf
  exact ⟨_,h⟩

private def globalCofactorNorm2 (q z : ℝ) : {r : ℝ // globalCofactor q z 2=r} := by
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have h02 : (0 : Fin 4) ≠ 2 := by decide
  have h03 : (0 : Fin 4) ≠ 3 := by decide
  have h12 : (1 : Fin 4) ≠ 2 := by decide
  have h13 : (1 : Fin 4) ≠ 3 := by decide
  have h23 : (2 : Fin 4) ≠ 3 := by decide
  have h : globalCofactor q z 2=globalCofactor q z 2 := rfl
  conv at h =>
    rhs
    norm_num [globalCofactor, globalShiftedEntry, globalShift, h01,h02,h03,h12,h13,h23]
    simp only [(scalarEntryNorm00 q 1).property, (scalarEntryNorm01 q 1).property, (scalarEntryNorm02 q 1).property, (scalarEntryNorm03 q 1).property, (scalarEntryNorm11 q 1).property, (scalarEntryNorm12 q 1).property, (scalarEntryNorm13 q 1).property, (scalarEntryNorm22 q 1).property, (scalarEntryNorm23 q 1).property, (scalarEntryNorm33 q 1).property]
    dsimp only [scalarEntryNorm00, scalarEntryNorm01, scalarEntryNorm02, scalarEntryNorm03, scalarEntryNorm11, scalarEntryNorm12, scalarEntryNorm13, scalarEntryNorm22, scalarEntryNorm23, scalarEntryNorm33, reducedEntryNorm00,reducedEntryNorm01,reducedEntryNorm11, globalShift]
    norm_num [h01,h02,h03,h12,h13,h23]
    ring_nf
  exact ⟨_,h⟩

private def globalCofactorNorm3 (q z : ℝ) : {r : ℝ // globalCofactor q z 3=r} := by
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have h02 : (0 : Fin 4) ≠ 2 := by decide
  have h03 : (0 : Fin 4) ≠ 3 := by decide
  have h12 : (1 : Fin 4) ≠ 2 := by decide
  have h13 : (1 : Fin 4) ≠ 3 := by decide
  have h23 : (2 : Fin 4) ≠ 3 := by decide
  have h : globalCofactor q z 3=globalCofactor q z 3 := rfl
  conv at h =>
    rhs
    norm_num [globalCofactor, globalShiftedEntry, globalShift, h01,h02,h03,h12,h13,h23]
    simp only [(scalarEntryNorm00 q 1).property, (scalarEntryNorm01 q 1).property, (scalarEntryNorm02 q 1).property, (scalarEntryNorm03 q 1).property, (scalarEntryNorm11 q 1).property, (scalarEntryNorm12 q 1).property, (scalarEntryNorm13 q 1).property, (scalarEntryNorm22 q 1).property, (scalarEntryNorm23 q 1).property, (scalarEntryNorm33 q 1).property]
    dsimp only [scalarEntryNorm00, scalarEntryNorm01, scalarEntryNorm02, scalarEntryNorm03, scalarEntryNorm11, scalarEntryNorm12, scalarEntryNorm13, scalarEntryNorm22, scalarEntryNorm23, scalarEntryNorm33, reducedEntryNorm00,reducedEntryNorm01,reducedEntryNorm11, globalShift]
    norm_num [h01,h02,h03,h12,h13,h23]
    ring_nf
  exact ⟨_,h⟩

private def globalCofactorNorm4 (q z : ℝ) : {r : ℝ // globalCofactor q z 4=r} := by
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have h02 : (0 : Fin 4) ≠ 2 := by decide
  have h03 : (0 : Fin 4) ≠ 3 := by decide
  have h12 : (1 : Fin 4) ≠ 2 := by decide
  have h13 : (1 : Fin 4) ≠ 3 := by decide
  have h23 : (2 : Fin 4) ≠ 3 := by decide
  have h : globalCofactor q z 4=globalCofactor q z 4 := rfl
  conv at h =>
    rhs
    norm_num [globalCofactor, globalShiftedEntry, globalShift, h01,h02,h03,h12,h13,h23]
    simp only [(scalarEntryNorm00 q 1).property, (scalarEntryNorm01 q 1).property, (scalarEntryNorm02 q 1).property, (scalarEntryNorm03 q 1).property, (scalarEntryNorm11 q 1).property, (scalarEntryNorm12 q 1).property, (scalarEntryNorm13 q 1).property, (scalarEntryNorm22 q 1).property, (scalarEntryNorm23 q 1).property, (scalarEntryNorm33 q 1).property]
    dsimp only [scalarEntryNorm00, scalarEntryNorm01, scalarEntryNorm02, scalarEntryNorm03, scalarEntryNorm11, scalarEntryNorm12, scalarEntryNorm13, scalarEntryNorm22, scalarEntryNorm23, scalarEntryNorm33, reducedEntryNorm00,reducedEntryNorm01,reducedEntryNorm11, globalShift]
    norm_num [h01,h02,h03,h12,h13,h23]
    ring_nf
  exact ⟨_,h⟩

private def globalCofactorNorm5 (q z : ℝ) : {r : ℝ // globalCofactor q z 5=r} := by
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have h02 : (0 : Fin 4) ≠ 2 := by decide
  have h03 : (0 : Fin 4) ≠ 3 := by decide
  have h12 : (1 : Fin 4) ≠ 2 := by decide
  have h13 : (1 : Fin 4) ≠ 3 := by decide
  have h23 : (2 : Fin 4) ≠ 3 := by decide
  have h : globalCofactor q z 5=globalCofactor q z 5 := rfl
  conv at h =>
    rhs
    norm_num [globalCofactor, globalShiftedEntry, globalShift, h01,h02,h03,h12,h13,h23]
    simp only [(scalarEntryNorm00 q 1).property, (scalarEntryNorm01 q 1).property, (scalarEntryNorm02 q 1).property, (scalarEntryNorm03 q 1).property, (scalarEntryNorm11 q 1).property, (scalarEntryNorm12 q 1).property, (scalarEntryNorm13 q 1).property, (scalarEntryNorm22 q 1).property, (scalarEntryNorm23 q 1).property, (scalarEntryNorm33 q 1).property]
    dsimp only [scalarEntryNorm00, scalarEntryNorm01, scalarEntryNorm02, scalarEntryNorm03, scalarEntryNorm11, scalarEntryNorm12, scalarEntryNorm13, scalarEntryNorm22, scalarEntryNorm23, scalarEntryNorm33, reducedEntryNorm00,reducedEntryNorm01,reducedEntryNorm11, globalShift]
    norm_num [h01,h02,h03,h12,h13,h23]
    ring_nf
  exact ⟨_,h⟩

private def globalDetTermNorm0 (q z : ℝ) : {r : ℝ // globalDetTerm q z 0=r} := by
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have h02 : (0 : Fin 4) ≠ 2 := by decide
  have h03 : (0 : Fin 4) ≠ 3 := by decide
  have h12 : (1 : Fin 4) ≠ 2 := by decide
  have h13 : (1 : Fin 4) ≠ 3 := by decide
  have h23 : (2 : Fin 4) ≠ 3 := by decide
  have h : globalDetTerm q z 0=globalDetTerm q z 0 := rfl
  conv at h =>
    rhs
    norm_num [globalDetTerm, globalShiftedEntry, globalShift, h01,h02,h03,h12,h13,h23]
    simp only [(scalarEntryNorm00 q 1).property, (scalarEntryNorm01 q 1).property, (scalarEntryNorm02 q 1).property, (scalarEntryNorm03 q 1).property, (scalarEntryNorm11 q 1).property, (scalarEntryNorm12 q 1).property, (scalarEntryNorm13 q 1).property, (scalarEntryNorm22 q 1).property, (scalarEntryNorm23 q 1).property, (scalarEntryNorm33 q 1).property, (globalCofactorNorm0 q z).property, (globalCofactorNorm1 q z).property, (globalCofactorNorm2 q z).property, (globalCofactorNorm3 q z).property, (globalCofactorNorm4 q z).property, (globalCofactorNorm5 q z).property, (globalMinorNorm3 q z).property]
    dsimp only [scalarEntryNorm00, scalarEntryNorm01, scalarEntryNorm02, scalarEntryNorm03, scalarEntryNorm11, scalarEntryNorm12, scalarEntryNorm13, scalarEntryNorm22, scalarEntryNorm23, scalarEntryNorm33, globalCofactorNorm0, globalCofactorNorm1, globalCofactorNorm2, globalCofactorNorm3, globalCofactorNorm4, globalCofactorNorm5, globalMinorNorm3,reducedEntryNorm00,reducedEntryNorm01,reducedEntryNorm11,globalShift]
    norm_num [h01,h02,h03,h12,h13,h23]
    ring_nf
  exact ⟨_,h⟩

private def globalDetTermNorm1 (q z : ℝ) : {r : ℝ // globalDetTerm q z 1=r} := by
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have h02 : (0 : Fin 4) ≠ 2 := by decide
  have h03 : (0 : Fin 4) ≠ 3 := by decide
  have h12 : (1 : Fin 4) ≠ 2 := by decide
  have h13 : (1 : Fin 4) ≠ 3 := by decide
  have h23 : (2 : Fin 4) ≠ 3 := by decide
  have h : globalDetTerm q z 1=globalDetTerm q z 1 := rfl
  conv at h =>
    rhs
    norm_num [globalDetTerm, globalShiftedEntry, globalShift, h01,h02,h03,h12,h13,h23]
    simp only [(scalarEntryNorm00 q 1).property, (scalarEntryNorm01 q 1).property, (scalarEntryNorm02 q 1).property, (scalarEntryNorm03 q 1).property, (scalarEntryNorm11 q 1).property, (scalarEntryNorm12 q 1).property, (scalarEntryNorm13 q 1).property, (scalarEntryNorm22 q 1).property, (scalarEntryNorm23 q 1).property, (scalarEntryNorm33 q 1).property, (globalCofactorNorm0 q z).property, (globalCofactorNorm1 q z).property, (globalCofactorNorm2 q z).property, (globalCofactorNorm3 q z).property, (globalCofactorNorm4 q z).property, (globalCofactorNorm5 q z).property, (globalMinorNorm3 q z).property]
    dsimp only [scalarEntryNorm00, scalarEntryNorm01, scalarEntryNorm02, scalarEntryNorm03, scalarEntryNorm11, scalarEntryNorm12, scalarEntryNorm13, scalarEntryNorm22, scalarEntryNorm23, scalarEntryNorm33, globalCofactorNorm0, globalCofactorNorm1, globalCofactorNorm2, globalCofactorNorm3, globalCofactorNorm4, globalCofactorNorm5, globalMinorNorm3,reducedEntryNorm00,reducedEntryNorm01,reducedEntryNorm11,globalShift]
    norm_num [h01,h02,h03,h12,h13,h23]
    ring_nf
  exact ⟨_,h⟩

private def globalDetTermNorm2 (q z : ℝ) : {r : ℝ // globalDetTerm q z 2=r} := by
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have h02 : (0 : Fin 4) ≠ 2 := by decide
  have h03 : (0 : Fin 4) ≠ 3 := by decide
  have h12 : (1 : Fin 4) ≠ 2 := by decide
  have h13 : (1 : Fin 4) ≠ 3 := by decide
  have h23 : (2 : Fin 4) ≠ 3 := by decide
  have h : globalDetTerm q z 2=globalDetTerm q z 2 := rfl
  conv at h =>
    rhs
    norm_num [globalDetTerm, globalShiftedEntry, globalShift, h01,h02,h03,h12,h13,h23]
    simp only [(scalarEntryNorm00 q 1).property, (scalarEntryNorm01 q 1).property, (scalarEntryNorm02 q 1).property, (scalarEntryNorm03 q 1).property, (scalarEntryNorm11 q 1).property, (scalarEntryNorm12 q 1).property, (scalarEntryNorm13 q 1).property, (scalarEntryNorm22 q 1).property, (scalarEntryNorm23 q 1).property, (scalarEntryNorm33 q 1).property, (globalCofactorNorm0 q z).property, (globalCofactorNorm1 q z).property, (globalCofactorNorm2 q z).property, (globalCofactorNorm3 q z).property, (globalCofactorNorm4 q z).property, (globalCofactorNorm5 q z).property, (globalMinorNorm3 q z).property]
    dsimp only [scalarEntryNorm00, scalarEntryNorm01, scalarEntryNorm02, scalarEntryNorm03, scalarEntryNorm11, scalarEntryNorm12, scalarEntryNorm13, scalarEntryNorm22, scalarEntryNorm23, scalarEntryNorm33, globalCofactorNorm0, globalCofactorNorm1, globalCofactorNorm2, globalCofactorNorm3, globalCofactorNorm4, globalCofactorNorm5, globalMinorNorm3,reducedEntryNorm00,reducedEntryNorm01,reducedEntryNorm11,globalShift]
    norm_num [h01,h02,h03,h12,h13,h23]
    ring_nf
  exact ⟨_,h⟩

private def globalDetTermNorm3 (q z : ℝ) : {r : ℝ // globalDetTerm q z 3=r} := by
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have h02 : (0 : Fin 4) ≠ 2 := by decide
  have h03 : (0 : Fin 4) ≠ 3 := by decide
  have h12 : (1 : Fin 4) ≠ 2 := by decide
  have h13 : (1 : Fin 4) ≠ 3 := by decide
  have h23 : (2 : Fin 4) ≠ 3 := by decide
  have h : globalDetTerm q z 3=globalDetTerm q z 3 := rfl
  conv at h =>
    rhs
    norm_num [globalDetTerm, globalShiftedEntry, globalShift, h01,h02,h03,h12,h13,h23]
    simp only [(scalarEntryNorm00 q 1).property, (scalarEntryNorm01 q 1).property, (scalarEntryNorm02 q 1).property, (scalarEntryNorm03 q 1).property, (scalarEntryNorm11 q 1).property, (scalarEntryNorm12 q 1).property, (scalarEntryNorm13 q 1).property, (scalarEntryNorm22 q 1).property, (scalarEntryNorm23 q 1).property, (scalarEntryNorm33 q 1).property, (globalCofactorNorm0 q z).property, (globalCofactorNorm1 q z).property, (globalCofactorNorm2 q z).property, (globalCofactorNorm3 q z).property, (globalCofactorNorm4 q z).property, (globalCofactorNorm5 q z).property, (globalMinorNorm3 q z).property]
    dsimp only [scalarEntryNorm00, scalarEntryNorm01, scalarEntryNorm02, scalarEntryNorm03, scalarEntryNorm11, scalarEntryNorm12, scalarEntryNorm13, scalarEntryNorm22, scalarEntryNorm23, scalarEntryNorm33, globalCofactorNorm0, globalCofactorNorm1, globalCofactorNorm2, globalCofactorNorm3, globalCofactorNorm4, globalCofactorNorm5, globalMinorNorm3,reducedEntryNorm00,reducedEntryNorm01,reducedEntryNorm11,globalShift]
    norm_num [h01,h02,h03,h12,h13,h23]
    ring_nf
  exact ⟨_,h⟩

private def globalDetTermNorm4 (q z : ℝ) : {r : ℝ // globalDetTerm q z 4=r} := by
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have h02 : (0 : Fin 4) ≠ 2 := by decide
  have h03 : (0 : Fin 4) ≠ 3 := by decide
  have h12 : (1 : Fin 4) ≠ 2 := by decide
  have h13 : (1 : Fin 4) ≠ 3 := by decide
  have h23 : (2 : Fin 4) ≠ 3 := by decide
  have h : globalDetTerm q z 4=globalDetTerm q z 4 := rfl
  conv at h =>
    rhs
    norm_num [globalDetTerm, globalShiftedEntry, globalShift, h01,h02,h03,h12,h13,h23]
    simp only [(scalarEntryNorm00 q 1).property, (scalarEntryNorm01 q 1).property, (scalarEntryNorm02 q 1).property, (scalarEntryNorm03 q 1).property, (scalarEntryNorm11 q 1).property, (scalarEntryNorm12 q 1).property, (scalarEntryNorm13 q 1).property, (scalarEntryNorm22 q 1).property, (scalarEntryNorm23 q 1).property, (scalarEntryNorm33 q 1).property, (globalCofactorNorm0 q z).property, (globalCofactorNorm1 q z).property, (globalCofactorNorm2 q z).property, (globalCofactorNorm3 q z).property, (globalCofactorNorm4 q z).property, (globalCofactorNorm5 q z).property, (globalMinorNorm3 q z).property]
    dsimp only [scalarEntryNorm00, scalarEntryNorm01, scalarEntryNorm02, scalarEntryNorm03, scalarEntryNorm11, scalarEntryNorm12, scalarEntryNorm13, scalarEntryNorm22, scalarEntryNorm23, scalarEntryNorm33, globalCofactorNorm0, globalCofactorNorm1, globalCofactorNorm2, globalCofactorNorm3, globalCofactorNorm4, globalCofactorNorm5, globalMinorNorm3,reducedEntryNorm00,reducedEntryNorm01,reducedEntryNorm11,globalShift]
    norm_num [h01,h02,h03,h12,h13,h23]
    ring_nf
  exact ⟨_,h⟩

private def globalDetTermNorm5 (q z : ℝ) : {r : ℝ // globalDetTerm q z 5=r} := by
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have h02 : (0 : Fin 4) ≠ 2 := by decide
  have h03 : (0 : Fin 4) ≠ 3 := by decide
  have h12 : (1 : Fin 4) ≠ 2 := by decide
  have h13 : (1 : Fin 4) ≠ 3 := by decide
  have h23 : (2 : Fin 4) ≠ 3 := by decide
  have h : globalDetTerm q z 5=globalDetTerm q z 5 := rfl
  conv at h =>
    rhs
    norm_num [globalDetTerm, globalShiftedEntry, globalShift, h01,h02,h03,h12,h13,h23]
    simp only [(scalarEntryNorm00 q 1).property, (scalarEntryNorm01 q 1).property, (scalarEntryNorm02 q 1).property, (scalarEntryNorm03 q 1).property, (scalarEntryNorm11 q 1).property, (scalarEntryNorm12 q 1).property, (scalarEntryNorm13 q 1).property, (scalarEntryNorm22 q 1).property, (scalarEntryNorm23 q 1).property, (scalarEntryNorm33 q 1).property, (globalCofactorNorm0 q z).property, (globalCofactorNorm1 q z).property, (globalCofactorNorm2 q z).property, (globalCofactorNorm3 q z).property, (globalCofactorNorm4 q z).property, (globalCofactorNorm5 q z).property, (globalMinorNorm3 q z).property]
    dsimp only [scalarEntryNorm00, scalarEntryNorm01, scalarEntryNorm02, scalarEntryNorm03, scalarEntryNorm11, scalarEntryNorm12, scalarEntryNorm13, scalarEntryNorm22, scalarEntryNorm23, scalarEntryNorm33, globalCofactorNorm0, globalCofactorNorm1, globalCofactorNorm2, globalCofactorNorm3, globalCofactorNorm4, globalCofactorNorm5, globalMinorNorm3,reducedEntryNorm00,reducedEntryNorm01,reducedEntryNorm11,globalShift]
    norm_num [h01,h02,h03,h12,h13,h23]
    ring_nf
  exact ⟨_,h⟩

private def globalDetTermNorm6 (q z : ℝ) : {r : ℝ // globalDetTerm q z 6=r} := by
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have h02 : (0 : Fin 4) ≠ 2 := by decide
  have h03 : (0 : Fin 4) ≠ 3 := by decide
  have h12 : (1 : Fin 4) ≠ 2 := by decide
  have h13 : (1 : Fin 4) ≠ 3 := by decide
  have h23 : (2 : Fin 4) ≠ 3 := by decide
  have h : globalDetTerm q z 6=globalDetTerm q z 6 := rfl
  conv at h =>
    rhs
    norm_num [globalDetTerm, globalShiftedEntry, globalShift, h01,h02,h03,h12,h13,h23]
    simp only [(scalarEntryNorm00 q 1).property, (scalarEntryNorm01 q 1).property, (scalarEntryNorm02 q 1).property, (scalarEntryNorm03 q 1).property, (scalarEntryNorm11 q 1).property, (scalarEntryNorm12 q 1).property, (scalarEntryNorm13 q 1).property, (scalarEntryNorm22 q 1).property, (scalarEntryNorm23 q 1).property, (scalarEntryNorm33 q 1).property, (globalCofactorNorm0 q z).property, (globalCofactorNorm1 q z).property, (globalCofactorNorm2 q z).property, (globalCofactorNorm3 q z).property, (globalCofactorNorm4 q z).property, (globalCofactorNorm5 q z).property, (globalMinorNorm3 q z).property]
    dsimp only [scalarEntryNorm00, scalarEntryNorm01, scalarEntryNorm02, scalarEntryNorm03, scalarEntryNorm11, scalarEntryNorm12, scalarEntryNorm13, scalarEntryNorm22, scalarEntryNorm23, scalarEntryNorm33, globalCofactorNorm0, globalCofactorNorm1, globalCofactorNorm2, globalCofactorNorm3, globalCofactorNorm4, globalCofactorNorm5, globalMinorNorm3,reducedEntryNorm00,reducedEntryNorm01,reducedEntryNorm11,globalShift]
    norm_num
    ring_nf
  exact ⟨_,h⟩

private def globalMinorNorm4 (q z : ℝ) : {r : ℝ // globalMinor4 q z=r} := by
  have h : globalMinor4 q z=globalMinor4 q z := rfl
  conv at h =>
    rhs
    rw [globalMinor4_eq_terms]
    simp only [(globalDetTermNorm0 q z).property, (globalDetTermNorm1 q z).property, (globalDetTermNorm2 q z).property, (globalDetTermNorm3 q z).property, (globalDetTermNorm4 q z).property, (globalDetTermNorm5 q z).property, (globalDetTermNorm6 q z).property]
    dsimp only [globalDetTermNorm0, globalDetTermNorm1, globalDetTermNorm2, globalDetTermNorm3, globalDetTermNorm4, globalDetTermNorm5, globalDetTermNorm6]
    norm_num
    ring_nf
  exact ⟨_,h⟩

private theorem globalMinor4_nonneg {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ globalMinor4 (5+u) (expCredit7 (5+u)) := by
  rw [(globalMinorNorm4 (5+u) (expCredit7 (5+u))).property]
  dsimp only [globalMinorNorm4,expCredit7]
  ring_nf
  positivity


private theorem global_reduced_floor {q : ℝ} (hq : 5 ≤ q) (y : Fin 4 → ℝ) :
    0 ≤ (∑ i : Fin 4, ∑ j : Fin 4, y i*y j*reducedEntry q 1 i j) +
      ∑ i : Fin 4, globalShift q (expCredit7 q) i*y i^2 := by
  rw [symmetric_sum_diagonal_identity _ (reducedEntry_symm _ _) _ y]
  let m := globalShiftedEntry q (expCredit7 q)
  have hu : 0 ≤ q-5 := by linarith
  have h1 := globalMinor1_pos hu
  have h2 := globalMinor2_pos hu
  have h3 := globalMinor3_pos hu
  have h4 := globalMinor4_nonneg hu
  rw [show 5+(q-5)=q by ring] at h1 h2 h3 h4
  have h := symQuadratic_nonneg
    (a:=m 0 0) (b:=m 0 1) (c:=m 0 2) (d:=m 0 3)
    (e:=m 1 1) (f:=m 1 2) (g:=m 1 3) (h:=m 2 2) (i:=m 2 3) (j:=m 3 3)
    h1 h2 h3 h4 (y 0) (y 1) (y 2) (y 3)
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have h02 : (0 : Fin 4) ≠ 2 := by decide
  have h03 : (0 : Fin 4) ≠ 3 := by decide
  have h12 : (1 : Fin 4) ≠ 2 := by decide
  have h13 : (1 : Fin 4) ≠ 3 := by decide
  have h23 : (2 : Fin 4) ≠ 3 := by decide
  simpa only [m,globalShiftedEntry,if_pos rfl,if_pos True.intro,if_neg h01,if_neg h02,
    if_neg h03,if_neg h12,if_neg h13,if_neg h23,add_zero] using h

private theorem global_homogeneous_floor {q : ℝ} (hq : 5 ≤ q) (y : Fin 4 → ℝ) :
    0 ≤ (∑ i : Fin 4, ∑ j : Fin 4, y i*y j*mixedHomEntry q 1 i j) +
      10000*expCredit7 q*mixedDenomHom q 1*∑ i : Fin 4, y i^2 := by
  let D := columnScale q 1
  have h := global_reduced_floor hq (fun i => D i*y i)
  have he (i j : Fin 4) : (D i*y i)*(D j*y j)*reducedEntry q 1 i j =
      y i*y j*mixedHomEntry q 1 i j := by
    rw [mixedHomEntry_factor]
    dsimp only [D]
    ring
  have hd (i : Fin 4) : globalShift q (expCredit7 q) i*(D i*y i)^2 =
      10000*expCredit7 q*mixedDenomHom q 1*y i^2 := by
    calc
      _ = (columnScale q 1 i)^2*globalShift q (expCredit7 q) i*y i^2 := by
        dsimp [D]
        ring
      _ = _ := by rw [globalShift_factor]
  simp_rw [he,hd] at h
  rw [← Finset.mul_sum] at h
  exact h

private theorem global_central_floor {q : ℝ} (hq : 5 ≤ q) (y : Fin 4 → ℝ) :
    0 ≤ (∑ i : Fin 4, ∑ j : Fin 4, y i*y j*mixedCentralMatrix q i j) +
      10000*expCredit7 q*∑ i : Fin 4, y i^2 := by
  have h := global_homogeneous_floor hq y
  simp_rw [mixedHomEntry_one hq] at h
  have hq0 : 0 < q := by linarith
  have hq3 : 0 < 2*q-3 := by linarith
  have hK : 0 < mixedDenomHom q 1 := by
    unfold mixedDenomHom
    norm_num only [mul_one,one_pow]
    positivity
  have he : (∑ i : Fin 4, ∑ j : Fin 4,
        y i*y j*(mixedDenomHom q 1*mixedCentralMatrix q i j)) =
      mixedDenomHom q 1*(∑ i : Fin 4, ∑ j : Fin 4,
        y i*y j*mixedCentralMatrix q i j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he] at h
  have he2 : mixedDenomHom q 1*(∑ i : Fin 4, ∑ j : Fin 4,
      y i*y j*mixedCentralMatrix q i j)+
      10000*expCredit7 q*mixedDenomHom q 1*(∑ i : Fin 4,y i^2) =
      mixedDenomHom q 1*((∑ i : Fin 4, ∑ j : Fin 4,
        y i*y j*mixedCentralMatrix q i j)+10000*expCredit7 q*∑ i : Fin 4,y i^2) := by ring
  rw [he2] at h
  exact (mul_nonneg_iff_of_pos_left hK).mp h

/-- The actual exponential-weighted unequal pair has a uniform floor on the entire scale-five ray. -/
theorem mixedPairOddFour_exponential_floor_global {q : ℝ} (hq : 5 ≤ q)
    (y : Fin 4 → ℝ) :
    0 ≤ 8*Real.exp (-3*q)*(∑ i : Fin 4, ∑ j : Fin 4,
      y i*y j*mixedCentralMatrix q i j)+(1/40)*∑ i : Fin 4,y i^2 := by
  have h := mul_nonneg (show 0 ≤ 8*Real.exp (-3*q) by positivity)
    (global_central_floor hq y)
  have hp := mul_le_mul_of_nonneg_right (global_exponential_payment hq)
    (show 0 ≤ ∑ i : Fin 4,y i^2 from Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  nlinarith only [h,hp]


/-- The neutral-interval statement follows from the global unequal-pair floor. -/
theorem mixedPairOddFour_exponential_floor {q : ℝ} (hq : 5 ≤ q) (_hqU : q ≤ 45/8)
    (y : Fin 4 → ℝ) :
    0 ≤ 8*Real.exp (-3*q)*(∑ i : Fin 4, ∑ j : Fin 4,
      y i*y j*mixedCentralMatrix q i j)+(1/40)*∑ i : Fin 4, y i^2 :=
  mixedPairOddFour_exponential_floor_global hq y

end
end RHTower.ThetaCuspMixedPairOddFourFloor
