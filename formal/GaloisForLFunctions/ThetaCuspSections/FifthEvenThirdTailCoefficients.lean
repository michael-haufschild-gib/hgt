import GaloisForLFunctions.ThetaCuspSections.FifthEvenThirdTailData
/-!
# Positive coefficient matrices for the rate-ten tail

Normalize the cleared comparison by setting `q=3*(1+y)` and dividing by
`3^27`. Exact rational Schur signs certify each coefficient through degree
21. Only the constant coefficient distinguishes the two gamma endpoints.
-/
noncomputable section
open Matrix
namespace GaloisForLFunctions.ThetaCuspSections.FifthThirdTail
open FifthAtomTail FifthLeadingPair

/-- Rate-ten gamma endpoint moments after multiplication by the cube of the radial scale. -/
def crossScaled (upper : Bool) : ℕ → ℝ → ℝ
 | 0, q => q^3/10+3*q^2/200+3*q/4000-(if upper then 0 else 3/80000)
 | n+1, q => q^(n+4)/10+((2*n+5:ℕ):ℝ)/20*crossScaled upper n q

/-- The reserve comparison after clearing twenty-seven powers of the radial scale. -/
def clearedMoment (upper : Bool) (q : ℝ) (k : ℕ) : ℝ :=
 (3/8)*q^26*linearMoment (fun n => g n 0 1) k+
  (18*3^24/(20:ℝ)^8)*thirdLinear (fun n => crossScaled upper n q) k

/-- Hankel matrix of the cleared comparison moments. -/
def clearedMatrix (upper : Bool) (q : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
 fun i j => clearedMoment upper q (i.val+j.val)


private theorem choose_as_factorial (n d : ℕ) :
 n.choose d=if d≤n then n.factorial/(d.factorial*(n-d).factorial) else 0 := by
 split_ifs with h
 · exact Nat.choose_eq_factorial_div_factorial h
 · exact Nat.choose_eq_zero_of_lt (by omega)

/-- Coefficient of `y^d` in `(3*(1+y))^n`. -/
def powerCoeff (n d : ℕ) : ℝ := (n.choose d : ℝ)*3^n
/-- Coefficients of the cleared gamma endpoint moments at `q=3*(1+y)`. -/
def crossCoeff (upper : Bool) : ℕ → ℕ → ℝ
 | 0, d => powerCoeff 3 d/10+3*powerCoeff 2 d/200+3*powerCoeff 1 d/4000-
   (if upper then 0 else if d=0 then 3/80000 else 0)
 | n+1, d => powerCoeff (n+4) d/10+((2*n+5:ℕ):ℝ)/20*crossCoeff upper n d

/-- The lower and upper gamma endpoints differ only in the constant coefficient. -/
theorem crossCoeff_endpoints_agree (n d : ℕ) (hd : d≠0) :
 crossCoeff false n d=crossCoeff true n d := by
 induction n with
 | zero => simp only [crossCoeff,Bool.false_eq_true,ite_false,ite_true,hd]
 | succ n ih => simp only [crossCoeff,ih]

/-- Coefficients after dividing the cleared comparison by `3^27`. -/
def momentCoeff (upper : Bool) (d k : ℕ) : ℝ :=
 (1/8)*(Nat.choose 26 d : ℝ)*linearMoment (fun n => g n 0 1) k+
  (18/(27*(20:ℝ)^8))*thirdLinear (fun n => crossCoeff upper n d) k

/-- The fixed Hankel matrix at one coefficient of the normalized comparison. -/
def coefficientMatrix (upper : Bool) (d : ℕ) : Matrix (Fin 5) (Fin 5) ℝ :=
 fun i j => momentCoeff upper d (i.val+j.val)

namespace Lower0
private def a0 : {v : ℝ // momentCoeff false 0 0=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a1 : {v : ℝ // momentCoeff false 0 1=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a2 : {v : ℝ // momentCoeff false 0 2=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a3 : {v : ℝ // momentCoeff false 0 3=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a4 : {v : ℝ // momentCoeff false 0 4=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a5 : {v : ℝ // momentCoeff false 0 5=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a6 : {v : ℝ // momentCoeff false 0 6=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a7 : {v : ℝ // momentCoeff false 0 7=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a8 : {v : ℝ // momentCoeff false 0 8=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def matrix : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
 match i.val+j.val with
 | 0 => a0.val
 | 1 => a1.val
 | 2 => a2.val
 | 3 => a3.val
 | 4 => a4.val
 | 5 => a5.val
 | 6 => a6.val
 | 7 => a7.val
 | _ => a8.val
private theorem positive : matrix.PosDef := by
 apply posDef_of_schur_signs
 · intro i j
   simp only [matrix,Nat.add_comm]
 all_goals norm_num [delta,schur,minor,determinant,tailIndex,matrix,a0,a1,a2,a3,a4,a5,a6,a7,a8]
private theorem matrix_eq : matrix=coefficientMatrix false 0 := by
 ext i j
 fin_cases i <;> fin_cases j <;>
  simp only [matrix,coefficientMatrix,Nat.reduceAdd]
 all_goals first | exact a0.property.symm | exact a1.property.symm |
  exact a2.property.symm | exact a3.property.symm | exact a4.property.symm |
  exact a5.property.symm | exact a6.property.symm | exact a7.property.symm |
  exact a8.property.symm

theorem coefficient_posDef : (coefficientMatrix false 0).PosDef := by
 rw [← matrix_eq]
 exact positive
end Lower0

namespace Lower1
private def a0 : {v : ℝ // momentCoeff false 1 0=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a1 : {v : ℝ // momentCoeff false 1 1=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a2 : {v : ℝ // momentCoeff false 1 2=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a3 : {v : ℝ // momentCoeff false 1 3=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a4 : {v : ℝ // momentCoeff false 1 4=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a5 : {v : ℝ // momentCoeff false 1 5=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a6 : {v : ℝ // momentCoeff false 1 6=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a7 : {v : ℝ // momentCoeff false 1 7=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a8 : {v : ℝ // momentCoeff false 1 8=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def matrix : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
 match i.val+j.val with
 | 0 => a0.val
 | 1 => a1.val
 | 2 => a2.val
 | 3 => a3.val
 | 4 => a4.val
 | 5 => a5.val
 | 6 => a6.val
 | 7 => a7.val
 | _ => a8.val
private theorem positive : matrix.PosDef := by
 apply posDef_of_schur_signs
 · intro i j
   simp only [matrix,Nat.add_comm]
 all_goals norm_num [delta,schur,minor,determinant,tailIndex,matrix,a0,a1,a2,a3,a4,a5,a6,a7,a8]
private theorem matrix_eq : matrix=coefficientMatrix false 1 := by
 ext i j
 fin_cases i <;> fin_cases j <;>
  simp only [matrix,coefficientMatrix,Nat.reduceAdd]
 all_goals first | exact a0.property.symm | exact a1.property.symm |
  exact a2.property.symm | exact a3.property.symm | exact a4.property.symm |
  exact a5.property.symm | exact a6.property.symm | exact a7.property.symm |
  exact a8.property.symm

theorem coefficient_posDef : (coefficientMatrix false 1).PosDef := by
 rw [← matrix_eq]
 exact positive
end Lower1

namespace Lower2
private def a0 : {v : ℝ // momentCoeff false 2 0=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a1 : {v : ℝ // momentCoeff false 2 1=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a2 : {v : ℝ // momentCoeff false 2 2=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a3 : {v : ℝ // momentCoeff false 2 3=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a4 : {v : ℝ // momentCoeff false 2 4=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a5 : {v : ℝ // momentCoeff false 2 5=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a6 : {v : ℝ // momentCoeff false 2 6=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a7 : {v : ℝ // momentCoeff false 2 7=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a8 : {v : ℝ // momentCoeff false 2 8=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def matrix : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
 match i.val+j.val with
 | 0 => a0.val
 | 1 => a1.val
 | 2 => a2.val
 | 3 => a3.val
 | 4 => a4.val
 | 5 => a5.val
 | 6 => a6.val
 | 7 => a7.val
 | _ => a8.val
private theorem positive : matrix.PosDef := by
 apply posDef_of_schur_signs
 · intro i j
   simp only [matrix,Nat.add_comm]
 all_goals norm_num [delta,schur,minor,determinant,tailIndex,matrix,a0,a1,a2,a3,a4,a5,a6,a7,a8]
private theorem matrix_eq : matrix=coefficientMatrix false 2 := by
 ext i j
 fin_cases i <;> fin_cases j <;>
  simp only [matrix,coefficientMatrix,Nat.reduceAdd]
 all_goals first | exact a0.property.symm | exact a1.property.symm |
  exact a2.property.symm | exact a3.property.symm | exact a4.property.symm |
  exact a5.property.symm | exact a6.property.symm | exact a7.property.symm |
  exact a8.property.symm

theorem coefficient_posDef : (coefficientMatrix false 2).PosDef := by
 rw [← matrix_eq]
 exact positive
end Lower2

namespace Lower3
private def a0 : {v : ℝ // momentCoeff false 3 0=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a1 : {v : ℝ // momentCoeff false 3 1=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a2 : {v : ℝ // momentCoeff false 3 2=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a3 : {v : ℝ // momentCoeff false 3 3=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a4 : {v : ℝ // momentCoeff false 3 4=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a5 : {v : ℝ // momentCoeff false 3 5=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a6 : {v : ℝ // momentCoeff false 3 6=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a7 : {v : ℝ // momentCoeff false 3 7=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a8 : {v : ℝ // momentCoeff false 3 8=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def matrix : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
 match i.val+j.val with
 | 0 => a0.val
 | 1 => a1.val
 | 2 => a2.val
 | 3 => a3.val
 | 4 => a4.val
 | 5 => a5.val
 | 6 => a6.val
 | 7 => a7.val
 | _ => a8.val
private theorem positive : matrix.PosDef := by
 apply posDef_of_schur_signs
 · intro i j
   simp only [matrix,Nat.add_comm]
 all_goals norm_num [delta,schur,minor,determinant,tailIndex,matrix,a0,a1,a2,a3,a4,a5,a6,a7,a8]
private theorem matrix_eq : matrix=coefficientMatrix false 3 := by
 ext i j
 fin_cases i <;> fin_cases j <;>
  simp only [matrix,coefficientMatrix,Nat.reduceAdd]
 all_goals first | exact a0.property.symm | exact a1.property.symm |
  exact a2.property.symm | exact a3.property.symm | exact a4.property.symm |
  exact a5.property.symm | exact a6.property.symm | exact a7.property.symm |
  exact a8.property.symm

theorem coefficient_posDef : (coefficientMatrix false 3).PosDef := by
 rw [← matrix_eq]
 exact positive
end Lower3

namespace Lower4
private def a0 : {v : ℝ // momentCoeff false 4 0=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a1 : {v : ℝ // momentCoeff false 4 1=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a2 : {v : ℝ // momentCoeff false 4 2=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a3 : {v : ℝ // momentCoeff false 4 3=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a4 : {v : ℝ // momentCoeff false 4 4=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a5 : {v : ℝ // momentCoeff false 4 5=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a6 : {v : ℝ // momentCoeff false 4 6=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a7 : {v : ℝ // momentCoeff false 4 7=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a8 : {v : ℝ // momentCoeff false 4 8=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def matrix : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
 match i.val+j.val with
 | 0 => a0.val
 | 1 => a1.val
 | 2 => a2.val
 | 3 => a3.val
 | 4 => a4.val
 | 5 => a5.val
 | 6 => a6.val
 | 7 => a7.val
 | _ => a8.val
private theorem positive : matrix.PosDef := by
 apply posDef_of_schur_signs
 · intro i j
   simp only [matrix,Nat.add_comm]
 all_goals norm_num [delta,schur,minor,determinant,tailIndex,matrix,a0,a1,a2,a3,a4,a5,a6,a7,a8]
private theorem matrix_eq : matrix=coefficientMatrix false 4 := by
 ext i j
 fin_cases i <;> fin_cases j <;>
  simp only [matrix,coefficientMatrix,Nat.reduceAdd]
 all_goals first | exact a0.property.symm | exact a1.property.symm |
  exact a2.property.symm | exact a3.property.symm | exact a4.property.symm |
  exact a5.property.symm | exact a6.property.symm | exact a7.property.symm |
  exact a8.property.symm

theorem coefficient_posDef : (coefficientMatrix false 4).PosDef := by
 rw [← matrix_eq]
 exact positive
end Lower4

namespace Lower5
private def a0 : {v : ℝ // momentCoeff false 5 0=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a1 : {v : ℝ // momentCoeff false 5 1=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a2 : {v : ℝ // momentCoeff false 5 2=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a3 : {v : ℝ // momentCoeff false 5 3=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a4 : {v : ℝ // momentCoeff false 5 4=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a5 : {v : ℝ // momentCoeff false 5 5=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a6 : {v : ℝ // momentCoeff false 5 6=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a7 : {v : ℝ // momentCoeff false 5 7=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a8 : {v : ℝ // momentCoeff false 5 8=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def matrix : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
 match i.val+j.val with
 | 0 => a0.val
 | 1 => a1.val
 | 2 => a2.val
 | 3 => a3.val
 | 4 => a4.val
 | 5 => a5.val
 | 6 => a6.val
 | 7 => a7.val
 | _ => a8.val
private theorem positive : matrix.PosDef := by
 apply posDef_of_schur_signs
 · intro i j
   simp only [matrix,Nat.add_comm]
 all_goals norm_num [delta,schur,minor,determinant,tailIndex,matrix,a0,a1,a2,a3,a4,a5,a6,a7,a8]
private theorem matrix_eq : matrix=coefficientMatrix false 5 := by
 ext i j
 fin_cases i <;> fin_cases j <;>
  simp only [matrix,coefficientMatrix,Nat.reduceAdd]
 all_goals first | exact a0.property.symm | exact a1.property.symm |
  exact a2.property.symm | exact a3.property.symm | exact a4.property.symm |
  exact a5.property.symm | exact a6.property.symm | exact a7.property.symm |
  exact a8.property.symm

theorem coefficient_posDef : (coefficientMatrix false 5).PosDef := by
 rw [← matrix_eq]
 exact positive
end Lower5

namespace Lower6
private def a0 : {v : ℝ // momentCoeff false 6 0=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a1 : {v : ℝ // momentCoeff false 6 1=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a2 : {v : ℝ // momentCoeff false 6 2=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a3 : {v : ℝ // momentCoeff false 6 3=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a4 : {v : ℝ // momentCoeff false 6 4=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a5 : {v : ℝ // momentCoeff false 6 5=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a6 : {v : ℝ // momentCoeff false 6 6=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a7 : {v : ℝ // momentCoeff false 6 7=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a8 : {v : ℝ // momentCoeff false 6 8=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def matrix : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
 match i.val+j.val with
 | 0 => a0.val
 | 1 => a1.val
 | 2 => a2.val
 | 3 => a3.val
 | 4 => a4.val
 | 5 => a5.val
 | 6 => a6.val
 | 7 => a7.val
 | _ => a8.val
private theorem positive : matrix.PosDef := by
 apply posDef_of_schur_signs
 · intro i j
   simp only [matrix,Nat.add_comm]
 all_goals norm_num [delta,schur,minor,determinant,tailIndex,matrix,a0,a1,a2,a3,a4,a5,a6,a7,a8]
private theorem matrix_eq : matrix=coefficientMatrix false 6 := by
 ext i j
 fin_cases i <;> fin_cases j <;>
  simp only [matrix,coefficientMatrix,Nat.reduceAdd]
 all_goals first | exact a0.property.symm | exact a1.property.symm |
  exact a2.property.symm | exact a3.property.symm | exact a4.property.symm |
  exact a5.property.symm | exact a6.property.symm | exact a7.property.symm |
  exact a8.property.symm

theorem coefficient_posDef : (coefficientMatrix false 6).PosDef := by
 rw [← matrix_eq]
 exact positive
end Lower6

namespace Lower7
private def a0 : {v : ℝ // momentCoeff false 7 0=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a1 : {v : ℝ // momentCoeff false 7 1=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a2 : {v : ℝ // momentCoeff false 7 2=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a3 : {v : ℝ // momentCoeff false 7 3=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a4 : {v : ℝ // momentCoeff false 7 4=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a5 : {v : ℝ // momentCoeff false 7 5=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a6 : {v : ℝ // momentCoeff false 7 6=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a7 : {v : ℝ // momentCoeff false 7 7=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a8 : {v : ℝ // momentCoeff false 7 8=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def matrix : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
 match i.val+j.val with
 | 0 => a0.val
 | 1 => a1.val
 | 2 => a2.val
 | 3 => a3.val
 | 4 => a4.val
 | 5 => a5.val
 | 6 => a6.val
 | 7 => a7.val
 | _ => a8.val
private theorem positive : matrix.PosDef := by
 apply posDef_of_schur_signs
 · intro i j
   simp only [matrix,Nat.add_comm]
 all_goals norm_num [delta,schur,minor,determinant,tailIndex,matrix,a0,a1,a2,a3,a4,a5,a6,a7,a8]
private theorem matrix_eq : matrix=coefficientMatrix false 7 := by
 ext i j
 fin_cases i <;> fin_cases j <;>
  simp only [matrix,coefficientMatrix,Nat.reduceAdd]
 all_goals first | exact a0.property.symm | exact a1.property.symm |
  exact a2.property.symm | exact a3.property.symm | exact a4.property.symm |
  exact a5.property.symm | exact a6.property.symm | exact a7.property.symm |
  exact a8.property.symm

theorem coefficient_posDef : (coefficientMatrix false 7).PosDef := by
 rw [← matrix_eq]
 exact positive
end Lower7

namespace Lower8
private def a0 : {v : ℝ // momentCoeff false 8 0=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a1 : {v : ℝ // momentCoeff false 8 1=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a2 : {v : ℝ // momentCoeff false 8 2=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a3 : {v : ℝ // momentCoeff false 8 3=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a4 : {v : ℝ // momentCoeff false 8 4=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a5 : {v : ℝ // momentCoeff false 8 5=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a6 : {v : ℝ // momentCoeff false 8 6=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a7 : {v : ℝ // momentCoeff false 8 7=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a8 : {v : ℝ // momentCoeff false 8 8=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def matrix : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
 match i.val+j.val with
 | 0 => a0.val
 | 1 => a1.val
 | 2 => a2.val
 | 3 => a3.val
 | 4 => a4.val
 | 5 => a5.val
 | 6 => a6.val
 | 7 => a7.val
 | _ => a8.val
private theorem positive : matrix.PosDef := by
 apply posDef_of_schur_signs
 · intro i j
   simp only [matrix,Nat.add_comm]
 all_goals norm_num [delta,schur,minor,determinant,tailIndex,matrix,a0,a1,a2,a3,a4,a5,a6,a7,a8]
private theorem matrix_eq : matrix=coefficientMatrix false 8 := by
 ext i j
 fin_cases i <;> fin_cases j <;>
  simp only [matrix,coefficientMatrix,Nat.reduceAdd]
 all_goals first | exact a0.property.symm | exact a1.property.symm |
  exact a2.property.symm | exact a3.property.symm | exact a4.property.symm |
  exact a5.property.symm | exact a6.property.symm | exact a7.property.symm |
  exact a8.property.symm

theorem coefficient_posDef : (coefficientMatrix false 8).PosDef := by
 rw [← matrix_eq]
 exact positive
end Lower8

namespace Lower9
private def a0 : {v : ℝ // momentCoeff false 9 0=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a1 : {v : ℝ // momentCoeff false 9 1=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a2 : {v : ℝ // momentCoeff false 9 2=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a3 : {v : ℝ // momentCoeff false 9 3=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a4 : {v : ℝ // momentCoeff false 9 4=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a5 : {v : ℝ // momentCoeff false 9 5=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a6 : {v : ℝ // momentCoeff false 9 6=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a7 : {v : ℝ // momentCoeff false 9 7=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a8 : {v : ℝ // momentCoeff false 9 8=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def matrix : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
 match i.val+j.val with
 | 0 => a0.val
 | 1 => a1.val
 | 2 => a2.val
 | 3 => a3.val
 | 4 => a4.val
 | 5 => a5.val
 | 6 => a6.val
 | 7 => a7.val
 | _ => a8.val
private theorem positive : matrix.PosDef := by
 apply posDef_of_schur_signs
 · intro i j
   simp only [matrix,Nat.add_comm]
 all_goals norm_num [delta,schur,minor,determinant,tailIndex,matrix,a0,a1,a2,a3,a4,a5,a6,a7,a8]
private theorem matrix_eq : matrix=coefficientMatrix false 9 := by
 ext i j
 fin_cases i <;> fin_cases j <;>
  simp only [matrix,coefficientMatrix,Nat.reduceAdd]
 all_goals first | exact a0.property.symm | exact a1.property.symm |
  exact a2.property.symm | exact a3.property.symm | exact a4.property.symm |
  exact a5.property.symm | exact a6.property.symm | exact a7.property.symm |
  exact a8.property.symm

theorem coefficient_posDef : (coefficientMatrix false 9).PosDef := by
 rw [← matrix_eq]
 exact positive
end Lower9

namespace Lower10
private def a0 : {v : ℝ // momentCoeff false 10 0=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a1 : {v : ℝ // momentCoeff false 10 1=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a2 : {v : ℝ // momentCoeff false 10 2=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a3 : {v : ℝ // momentCoeff false 10 3=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a4 : {v : ℝ // momentCoeff false 10 4=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a5 : {v : ℝ // momentCoeff false 10 5=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a6 : {v : ℝ // momentCoeff false 10 6=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a7 : {v : ℝ // momentCoeff false 10 7=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a8 : {v : ℝ // momentCoeff false 10 8=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def matrix : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
 match i.val+j.val with
 | 0 => a0.val
 | 1 => a1.val
 | 2 => a2.val
 | 3 => a3.val
 | 4 => a4.val
 | 5 => a5.val
 | 6 => a6.val
 | 7 => a7.val
 | _ => a8.val
private theorem positive : matrix.PosDef := by
 apply posDef_of_schur_signs
 · intro i j
   simp only [matrix,Nat.add_comm]
 all_goals norm_num [delta,schur,minor,determinant,tailIndex,matrix,a0,a1,a2,a3,a4,a5,a6,a7,a8]
private theorem matrix_eq : matrix=coefficientMatrix false 10 := by
 ext i j
 fin_cases i <;> fin_cases j <;>
  simp only [matrix,coefficientMatrix,Nat.reduceAdd]
 all_goals first | exact a0.property.symm | exact a1.property.symm |
  exact a2.property.symm | exact a3.property.symm | exact a4.property.symm |
  exact a5.property.symm | exact a6.property.symm | exact a7.property.symm |
  exact a8.property.symm

theorem coefficient_posDef : (coefficientMatrix false 10).PosDef := by
 rw [← matrix_eq]
 exact positive
end Lower10

namespace Lower11
private def a0 : {v : ℝ // momentCoeff false 11 0=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a1 : {v : ℝ // momentCoeff false 11 1=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a2 : {v : ℝ // momentCoeff false 11 2=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a3 : {v : ℝ // momentCoeff false 11 3=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a4 : {v : ℝ // momentCoeff false 11 4=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a5 : {v : ℝ // momentCoeff false 11 5=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a6 : {v : ℝ // momentCoeff false 11 6=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a7 : {v : ℝ // momentCoeff false 11 7=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a8 : {v : ℝ // momentCoeff false 11 8=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def matrix : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
 match i.val+j.val with
 | 0 => a0.val
 | 1 => a1.val
 | 2 => a2.val
 | 3 => a3.val
 | 4 => a4.val
 | 5 => a5.val
 | 6 => a6.val
 | 7 => a7.val
 | _ => a8.val
private theorem positive : matrix.PosDef := by
 apply posDef_of_schur_signs
 · intro i j
   simp only [matrix,Nat.add_comm]
 all_goals norm_num [delta,schur,minor,determinant,tailIndex,matrix,a0,a1,a2,a3,a4,a5,a6,a7,a8]
private theorem matrix_eq : matrix=coefficientMatrix false 11 := by
 ext i j
 fin_cases i <;> fin_cases j <;>
  simp only [matrix,coefficientMatrix,Nat.reduceAdd]
 all_goals first | exact a0.property.symm | exact a1.property.symm |
  exact a2.property.symm | exact a3.property.symm | exact a4.property.symm |
  exact a5.property.symm | exact a6.property.symm | exact a7.property.symm |
  exact a8.property.symm

theorem coefficient_posDef : (coefficientMatrix false 11).PosDef := by
 rw [← matrix_eq]
 exact positive
end Lower11

namespace Lower12
private def a0 : {v : ℝ // momentCoeff false 12 0=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a1 : {v : ℝ // momentCoeff false 12 1=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a2 : {v : ℝ // momentCoeff false 12 2=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a3 : {v : ℝ // momentCoeff false 12 3=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a4 : {v : ℝ // momentCoeff false 12 4=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a5 : {v : ℝ // momentCoeff false 12 5=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a6 : {v : ℝ // momentCoeff false 12 6=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a7 : {v : ℝ // momentCoeff false 12 7=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a8 : {v : ℝ // momentCoeff false 12 8=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def matrix : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
 match i.val+j.val with
 | 0 => a0.val
 | 1 => a1.val
 | 2 => a2.val
 | 3 => a3.val
 | 4 => a4.val
 | 5 => a5.val
 | 6 => a6.val
 | 7 => a7.val
 | _ => a8.val
private theorem positive : matrix.PosDef := by
 apply posDef_of_schur_signs
 · intro i j
   simp only [matrix,Nat.add_comm]
 all_goals norm_num [delta,schur,minor,determinant,tailIndex,matrix,a0,a1,a2,a3,a4,a5,a6,a7,a8]
private theorem matrix_eq : matrix=coefficientMatrix false 12 := by
 ext i j
 fin_cases i <;> fin_cases j <;>
  simp only [matrix,coefficientMatrix,Nat.reduceAdd]
 all_goals first | exact a0.property.symm | exact a1.property.symm |
  exact a2.property.symm | exact a3.property.symm | exact a4.property.symm |
  exact a5.property.symm | exact a6.property.symm | exact a7.property.symm |
  exact a8.property.symm

theorem coefficient_posDef : (coefficientMatrix false 12).PosDef := by
 rw [← matrix_eq]
 exact positive
end Lower12

namespace Lower13
private def a0 : {v : ℝ // momentCoeff false 13 0=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a1 : {v : ℝ // momentCoeff false 13 1=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a2 : {v : ℝ // momentCoeff false 13 2=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a3 : {v : ℝ // momentCoeff false 13 3=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a4 : {v : ℝ // momentCoeff false 13 4=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a5 : {v : ℝ // momentCoeff false 13 5=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a6 : {v : ℝ // momentCoeff false 13 6=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a7 : {v : ℝ // momentCoeff false 13 7=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a8 : {v : ℝ // momentCoeff false 13 8=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def matrix : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
 match i.val+j.val with
 | 0 => a0.val
 | 1 => a1.val
 | 2 => a2.val
 | 3 => a3.val
 | 4 => a4.val
 | 5 => a5.val
 | 6 => a6.val
 | 7 => a7.val
 | _ => a8.val
private theorem positive : matrix.PosDef := by
 apply posDef_of_schur_signs
 · intro i j
   simp only [matrix,Nat.add_comm]
 all_goals norm_num [delta,schur,minor,determinant,tailIndex,matrix,a0,a1,a2,a3,a4,a5,a6,a7,a8]
private theorem matrix_eq : matrix=coefficientMatrix false 13 := by
 ext i j
 fin_cases i <;> fin_cases j <;>
  simp only [matrix,coefficientMatrix,Nat.reduceAdd]
 all_goals first | exact a0.property.symm | exact a1.property.symm |
  exact a2.property.symm | exact a3.property.symm | exact a4.property.symm |
  exact a5.property.symm | exact a6.property.symm | exact a7.property.symm |
  exact a8.property.symm

theorem coefficient_posDef : (coefficientMatrix false 13).PosDef := by
 rw [← matrix_eq]
 exact positive
end Lower13

namespace Lower14
private def a0 : {v : ℝ // momentCoeff false 14 0=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a1 : {v : ℝ // momentCoeff false 14 1=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a2 : {v : ℝ // momentCoeff false 14 2=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a3 : {v : ℝ // momentCoeff false 14 3=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a4 : {v : ℝ // momentCoeff false 14 4=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a5 : {v : ℝ // momentCoeff false 14 5=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a6 : {v : ℝ // momentCoeff false 14 6=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a7 : {v : ℝ // momentCoeff false 14 7=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a8 : {v : ℝ // momentCoeff false 14 8=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def matrix : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
 match i.val+j.val with
 | 0 => a0.val
 | 1 => a1.val
 | 2 => a2.val
 | 3 => a3.val
 | 4 => a4.val
 | 5 => a5.val
 | 6 => a6.val
 | 7 => a7.val
 | _ => a8.val
private theorem positive : matrix.PosDef := by
 apply posDef_of_schur_signs
 · intro i j
   simp only [matrix,Nat.add_comm]
 all_goals norm_num [delta,schur,minor,determinant,tailIndex,matrix,a0,a1,a2,a3,a4,a5,a6,a7,a8]
private theorem matrix_eq : matrix=coefficientMatrix false 14 := by
 ext i j
 fin_cases i <;> fin_cases j <;>
  simp only [matrix,coefficientMatrix,Nat.reduceAdd]
 all_goals first | exact a0.property.symm | exact a1.property.symm |
  exact a2.property.symm | exact a3.property.symm | exact a4.property.symm |
  exact a5.property.symm | exact a6.property.symm | exact a7.property.symm |
  exact a8.property.symm

theorem coefficient_posDef : (coefficientMatrix false 14).PosDef := by
 rw [← matrix_eq]
 exact positive
end Lower14

namespace Lower15
private def a0 : {v : ℝ // momentCoeff false 15 0=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a1 : {v : ℝ // momentCoeff false 15 1=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a2 : {v : ℝ // momentCoeff false 15 2=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a3 : {v : ℝ // momentCoeff false 15 3=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a4 : {v : ℝ // momentCoeff false 15 4=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a5 : {v : ℝ // momentCoeff false 15 5=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a6 : {v : ℝ // momentCoeff false 15 6=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a7 : {v : ℝ // momentCoeff false 15 7=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a8 : {v : ℝ // momentCoeff false 15 8=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def matrix : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
 match i.val+j.val with
 | 0 => a0.val
 | 1 => a1.val
 | 2 => a2.val
 | 3 => a3.val
 | 4 => a4.val
 | 5 => a5.val
 | 6 => a6.val
 | 7 => a7.val
 | _ => a8.val
private theorem positive : matrix.PosDef := by
 apply posDef_of_schur_signs
 · intro i j
   simp only [matrix,Nat.add_comm]
 all_goals norm_num [delta,schur,minor,determinant,tailIndex,matrix,a0,a1,a2,a3,a4,a5,a6,a7,a8]
private theorem matrix_eq : matrix=coefficientMatrix false 15 := by
 ext i j
 fin_cases i <;> fin_cases j <;>
  simp only [matrix,coefficientMatrix,Nat.reduceAdd]
 all_goals first | exact a0.property.symm | exact a1.property.symm |
  exact a2.property.symm | exact a3.property.symm | exact a4.property.symm |
  exact a5.property.symm | exact a6.property.symm | exact a7.property.symm |
  exact a8.property.symm

theorem coefficient_posDef : (coefficientMatrix false 15).PosDef := by
 rw [← matrix_eq]
 exact positive
end Lower15

namespace Lower16
private def a0 : {v : ℝ // momentCoeff false 16 0=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a1 : {v : ℝ // momentCoeff false 16 1=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a2 : {v : ℝ // momentCoeff false 16 2=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a3 : {v : ℝ // momentCoeff false 16 3=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a4 : {v : ℝ // momentCoeff false 16 4=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a5 : {v : ℝ // momentCoeff false 16 5=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a6 : {v : ℝ // momentCoeff false 16 6=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a7 : {v : ℝ // momentCoeff false 16 7=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a8 : {v : ℝ // momentCoeff false 16 8=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def matrix : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
 match i.val+j.val with
 | 0 => a0.val
 | 1 => a1.val
 | 2 => a2.val
 | 3 => a3.val
 | 4 => a4.val
 | 5 => a5.val
 | 6 => a6.val
 | 7 => a7.val
 | _ => a8.val
private theorem positive : matrix.PosDef := by
 apply posDef_of_schur_signs
 · intro i j
   simp only [matrix,Nat.add_comm]
 all_goals norm_num [delta,schur,minor,determinant,tailIndex,matrix,a0,a1,a2,a3,a4,a5,a6,a7,a8]
private theorem matrix_eq : matrix=coefficientMatrix false 16 := by
 ext i j
 fin_cases i <;> fin_cases j <;>
  simp only [matrix,coefficientMatrix,Nat.reduceAdd]
 all_goals first | exact a0.property.symm | exact a1.property.symm |
  exact a2.property.symm | exact a3.property.symm | exact a4.property.symm |
  exact a5.property.symm | exact a6.property.symm | exact a7.property.symm |
  exact a8.property.symm

theorem coefficient_posDef : (coefficientMatrix false 16).PosDef := by
 rw [← matrix_eq]
 exact positive
end Lower16

namespace Lower17
private def a0 : {v : ℝ // momentCoeff false 17 0=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a1 : {v : ℝ // momentCoeff false 17 1=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a2 : {v : ℝ // momentCoeff false 17 2=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a3 : {v : ℝ // momentCoeff false 17 3=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a4 : {v : ℝ // momentCoeff false 17 4=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a5 : {v : ℝ // momentCoeff false 17 5=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a6 : {v : ℝ // momentCoeff false 17 6=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a7 : {v : ℝ // momentCoeff false 17 7=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a8 : {v : ℝ // momentCoeff false 17 8=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def matrix : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
 match i.val+j.val with
 | 0 => a0.val
 | 1 => a1.val
 | 2 => a2.val
 | 3 => a3.val
 | 4 => a4.val
 | 5 => a5.val
 | 6 => a6.val
 | 7 => a7.val
 | _ => a8.val
private theorem positive : matrix.PosDef := by
 apply posDef_of_schur_signs
 · intro i j
   simp only [matrix,Nat.add_comm]
 all_goals norm_num [delta,schur,minor,determinant,tailIndex,matrix,a0,a1,a2,a3,a4,a5,a6,a7,a8]
private theorem matrix_eq : matrix=coefficientMatrix false 17 := by
 ext i j
 fin_cases i <;> fin_cases j <;>
  simp only [matrix,coefficientMatrix,Nat.reduceAdd]
 all_goals first | exact a0.property.symm | exact a1.property.symm |
  exact a2.property.symm | exact a3.property.symm | exact a4.property.symm |
  exact a5.property.symm | exact a6.property.symm | exact a7.property.symm |
  exact a8.property.symm

theorem coefficient_posDef : (coefficientMatrix false 17).PosDef := by
 rw [← matrix_eq]
 exact positive
end Lower17

namespace Lower18
private def a0 : {v : ℝ // momentCoeff false 18 0=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a1 : {v : ℝ // momentCoeff false 18 1=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a2 : {v : ℝ // momentCoeff false 18 2=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a3 : {v : ℝ // momentCoeff false 18 3=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a4 : {v : ℝ // momentCoeff false 18 4=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a5 : {v : ℝ // momentCoeff false 18 5=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a6 : {v : ℝ // momentCoeff false 18 6=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a7 : {v : ℝ // momentCoeff false 18 7=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a8 : {v : ℝ // momentCoeff false 18 8=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def matrix : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
 match i.val+j.val with
 | 0 => a0.val
 | 1 => a1.val
 | 2 => a2.val
 | 3 => a3.val
 | 4 => a4.val
 | 5 => a5.val
 | 6 => a6.val
 | 7 => a7.val
 | _ => a8.val
private theorem positive : matrix.PosDef := by
 apply posDef_of_schur_signs
 · intro i j
   simp only [matrix,Nat.add_comm]
 all_goals norm_num [delta,schur,minor,determinant,tailIndex,matrix,a0,a1,a2,a3,a4,a5,a6,a7,a8]
private theorem matrix_eq : matrix=coefficientMatrix false 18 := by
 ext i j
 fin_cases i <;> fin_cases j <;>
  simp only [matrix,coefficientMatrix,Nat.reduceAdd]
 all_goals first | exact a0.property.symm | exact a1.property.symm |
  exact a2.property.symm | exact a3.property.symm | exact a4.property.symm |
  exact a5.property.symm | exact a6.property.symm | exact a7.property.symm |
  exact a8.property.symm

theorem coefficient_posDef : (coefficientMatrix false 18).PosDef := by
 rw [← matrix_eq]
 exact positive
end Lower18

namespace Lower19
private def a0 : {v : ℝ // momentCoeff false 19 0=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a1 : {v : ℝ // momentCoeff false 19 1=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a2 : {v : ℝ // momentCoeff false 19 2=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a3 : {v : ℝ // momentCoeff false 19 3=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a4 : {v : ℝ // momentCoeff false 19 4=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a5 : {v : ℝ // momentCoeff false 19 5=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a6 : {v : ℝ // momentCoeff false 19 6=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a7 : {v : ℝ // momentCoeff false 19 7=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a8 : {v : ℝ // momentCoeff false 19 8=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def matrix : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
 match i.val+j.val with
 | 0 => a0.val
 | 1 => a1.val
 | 2 => a2.val
 | 3 => a3.val
 | 4 => a4.val
 | 5 => a5.val
 | 6 => a6.val
 | 7 => a7.val
 | _ => a8.val
private theorem positive : matrix.PosDef := by
 apply posDef_of_schur_signs
 · intro i j
   simp only [matrix,Nat.add_comm]
 all_goals norm_num [delta,schur,minor,determinant,tailIndex,matrix,a0,a1,a2,a3,a4,a5,a6,a7,a8]
private theorem matrix_eq : matrix=coefficientMatrix false 19 := by
 ext i j
 fin_cases i <;> fin_cases j <;>
  simp only [matrix,coefficientMatrix,Nat.reduceAdd]
 all_goals first | exact a0.property.symm | exact a1.property.symm |
  exact a2.property.symm | exact a3.property.symm | exact a4.property.symm |
  exact a5.property.symm | exact a6.property.symm | exact a7.property.symm |
  exact a8.property.symm

theorem coefficient_posDef : (coefficientMatrix false 19).PosDef := by
 rw [← matrix_eq]
 exact positive
end Lower19

namespace Lower20
private def a0 : {v : ℝ // momentCoeff false 20 0=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a1 : {v : ℝ // momentCoeff false 20 1=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a2 : {v : ℝ // momentCoeff false 20 2=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a3 : {v : ℝ // momentCoeff false 20 3=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a4 : {v : ℝ // momentCoeff false 20 4=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a5 : {v : ℝ // momentCoeff false 20 5=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a6 : {v : ℝ // momentCoeff false 20 6=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a7 : {v : ℝ // momentCoeff false 20 7=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a8 : {v : ℝ // momentCoeff false 20 8=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def matrix : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
 match i.val+j.val with
 | 0 => a0.val
 | 1 => a1.val
 | 2 => a2.val
 | 3 => a3.val
 | 4 => a4.val
 | 5 => a5.val
 | 6 => a6.val
 | 7 => a7.val
 | _ => a8.val
private theorem positive : matrix.PosDef := by
 apply posDef_of_schur_signs
 · intro i j
   simp only [matrix,Nat.add_comm]
 all_goals norm_num [delta,schur,minor,determinant,tailIndex,matrix,a0,a1,a2,a3,a4,a5,a6,a7,a8]
private theorem matrix_eq : matrix=coefficientMatrix false 20 := by
 ext i j
 fin_cases i <;> fin_cases j <;>
  simp only [matrix,coefficientMatrix,Nat.reduceAdd]
 all_goals first | exact a0.property.symm | exact a1.property.symm |
  exact a2.property.symm | exact a3.property.symm | exact a4.property.symm |
  exact a5.property.symm | exact a6.property.symm | exact a7.property.symm |
  exact a8.property.symm

theorem coefficient_posDef : (coefficientMatrix false 20).PosDef := by
 rw [← matrix_eq]
 exact positive
end Lower20

namespace Lower21
private def a0 : {v : ℝ // momentCoeff false 21 0=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a1 : {v : ℝ // momentCoeff false 21 1=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a2 : {v : ℝ // momentCoeff false 21 2=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a3 : {v : ℝ // momentCoeff false 21 3=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a4 : {v : ℝ // momentCoeff false 21 4=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a5 : {v : ℝ // momentCoeff false 21 5=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a6 : {v : ℝ // momentCoeff false 21 6=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a7 : {v : ℝ // momentCoeff false 21 7=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a8 : {v : ℝ // momentCoeff false 21 8=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def matrix : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
 match i.val+j.val with
 | 0 => a0.val
 | 1 => a1.val
 | 2 => a2.val
 | 3 => a3.val
 | 4 => a4.val
 | 5 => a5.val
 | 6 => a6.val
 | 7 => a7.val
 | _ => a8.val
private theorem positive : matrix.PosDef := by
 apply posDef_of_schur_signs
 · intro i j
   simp only [matrix,Nat.add_comm]
 all_goals norm_num [delta,schur,minor,determinant,tailIndex,matrix,a0,a1,a2,a3,a4,a5,a6,a7,a8]
private theorem matrix_eq : matrix=coefficientMatrix false 21 := by
 ext i j
 fin_cases i <;> fin_cases j <;>
  simp only [matrix,coefficientMatrix,Nat.reduceAdd]
 all_goals first | exact a0.property.symm | exact a1.property.symm |
  exact a2.property.symm | exact a3.property.symm | exact a4.property.symm |
  exact a5.property.symm | exact a6.property.symm | exact a7.property.symm |
  exact a8.property.symm

theorem coefficient_posDef : (coefficientMatrix false 21).PosDef := by
 rw [← matrix_eq]
 exact positive
end Lower21

namespace Upper0
private def a0 : {v : ℝ // momentCoeff true 0 0=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a1 : {v : ℝ // momentCoeff true 0 1=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a2 : {v : ℝ // momentCoeff true 0 2=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a3 : {v : ℝ // momentCoeff true 0 3=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a4 : {v : ℝ // momentCoeff true 0 4=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a5 : {v : ℝ // momentCoeff true 0 5=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a6 : {v : ℝ // momentCoeff true 0 6=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a7 : {v : ℝ // momentCoeff true 0 7=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def a8 : {v : ℝ // momentCoeff true 0 8=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [momentCoeff,powerCoeff,crossCoeff,thirdLinear,linearMoment,g,choose_as_factorial]
private def matrix : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
 match i.val+j.val with
 | 0 => a0.val
 | 1 => a1.val
 | 2 => a2.val
 | 3 => a3.val
 | 4 => a4.val
 | 5 => a5.val
 | 6 => a6.val
 | 7 => a7.val
 | _ => a8.val
private theorem positive : matrix.PosDef := by
 apply posDef_of_schur_signs
 · intro i j
   simp only [matrix,Nat.add_comm]
 all_goals norm_num [delta,schur,minor,determinant,tailIndex,matrix,a0,a1,a2,a3,a4,a5,a6,a7,a8]
private theorem matrix_eq : matrix=coefficientMatrix true 0 := by
 ext i j
 fin_cases i <;> fin_cases j <;>
  simp only [matrix,coefficientMatrix,Nat.reduceAdd]
 all_goals first | exact a0.property.symm | exact a1.property.symm |
  exact a2.property.symm | exact a3.property.symm | exact a4.property.symm |
  exact a5.property.symm | exact a6.property.symm | exact a7.property.symm |
  exact a8.property.symm

theorem coefficient_posDef : (coefficientMatrix true 0).PosDef := by
 rw [← matrix_eq]
 exact positive
end Upper0
end GaloisForLFunctions.ThetaCuspSections.FifthThirdTail
