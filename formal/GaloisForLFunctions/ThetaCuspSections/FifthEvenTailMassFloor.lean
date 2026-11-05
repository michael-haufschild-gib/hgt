import GaloisForLFunctions.ThetaCuspSections.FifthEvenFirstAtomTailModel
/-!
# A fixed diagonal reserve for the fifth integrated theta section

The constant gamma moment matrix dominates a weighted diagonal norm. The
same weights bound every Cauchy factorial through reflection order sixteen,
allowing the remainder to be integrated in fixed coordinates.
-/
noncomputable section
open Matrix
namespace GaloisForLFunctions.ThetaCuspSections.TailMassFloor
open FifthAtomTail FifthLeadingPair

private def a0 : {v : ℝ // linearMoment (fun n => g n 0 1) 0=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [linearMoment,g]

private def a1 : {v : ℝ // linearMoment (fun n => g n 0 1) 1=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [linearMoment,g]

private def a2 : {v : ℝ // linearMoment (fun n => g n 0 1) 2=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [linearMoment,g]

private def a3 : {v : ℝ // linearMoment (fun n => g n 0 1) 3=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [linearMoment,g]

private def a4 : {v : ℝ // linearMoment (fun n => g n 0 1) 4=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [linearMoment,g]

private def a5 : {v : ℝ // linearMoment (fun n => g n 0 1) 5=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [linearMoment,g]

private def a6 : {v : ℝ // linearMoment (fun n => g n 0 1) 6=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [linearMoment,g]

private def a7 : {v : ℝ // linearMoment (fun n => g n 0 1) 7=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [linearMoment,g]

private def a8 : {v : ℝ // linearMoment (fun n => g n 0 1) 8=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [linearMoment,g]

private def mass : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
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

private def reduced : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
 mass i j-(if i=j then (1/100000000000 : ℝ)*1000^(2*i.val) else 0)

private theorem reduced_posDef : reduced.PosDef := by
 apply posDef_of_schur_signs
 · intro i j
   by_cases h : i=j
   · subst j
     rfl
   · simp only [reduced,mass,if_neg h,if_neg (Ne.symm h),Nat.add_comm]
 all_goals norm_num [delta,schur,minor,determinant,tailIndex,reduced,mass,a0,a1,a2,a3,a4,a5,a6,a7,a8]

private theorem mass_eq : mass=model 0 1 := by
 ext i j
 dsimp only [model]
 rw [moment_eq_linearMoment _ _ _ (by omega)]
 fin_cases i <;> fin_cases j <;> simp only [mass,Nat.reduceAdd]
 all_goals first | exact a0.property.symm | exact a1.property.symm |
  exact a2.property.symm | exact a3.property.symm | exact a4.property.symm |
  exact a5.property.symm | exact a6.property.symm | exact a7.property.symm |
  exact a8.property.symm

/-- The constant gamma moment matrix controls a fixed diagonal norm. -/
theorem mass_diagonal_floor :
 (model 0 1-(1/100000000000:ℝ) • Matrix.diagonal
  (fun i : Fin 5 => (1000:ℝ)^(2*i.val))).PosDef := by
 have he : model 0 1-(1/100000000000:ℝ) • Matrix.diagonal
  (fun i : Fin 5 => (1000:ℝ)^(2*i.val))=reduced := by
  rw [← mass_eq]
  ext i j
  simp only [Matrix.sub_apply,Matrix.smul_apply,Matrix.diagonal_apply,smul_eq_mul,reduced]
  split_ifs <;> ring
 rw [he]
 exact reduced_posDef

private theorem dot_smul (c : ℝ) (M : Matrix (Fin 5) (Fin 5) ℝ) (v : Fin 5 → ℝ) :
 v ⬝ᵥ ((c • M) *ᵥ v)=c*(v ⬝ᵥ (M *ᵥ v)) := by
 simp only [dotProduct,Matrix.mulVec,Matrix.smul_apply,smul_eq_mul,Finset.mul_sum]
 exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

private theorem dot_diagonal (d v : Fin 5 → ℝ) :
 v ⬝ᵥ (Matrix.diagonal d *ᵥ v)=∑ i, d i*v i^2 := by
 show ∑ i, v i*(Matrix.diagonal d *ᵥ v) i= _
 refine Finset.sum_congr rfl fun i _ => ?_
 have he : (Matrix.diagonal d *ᵥ v) i=d i*v i := by
  show ∑ j, Matrix.diagonal d i j*v j= _
  rw [Finset.sum_eq_single i
   (fun j _ hj => by rw [Matrix.diagonal_apply_ne _ (Ne.symm hj),zero_mul])
   (fun hi => absurd (Finset.mem_univ i) hi),Matrix.diagonal_apply_eq]
 rw [he]
 ring

/-- The gamma moment quadratic form controls the fixed weighted Euclidean norm. -/
theorem mass_form_lower (v : Fin 5 → ℝ) :
 (1/100000000000:ℝ)*(∑ i, ((1000:ℝ)^i.val*v i)^2)≤v ⬝ᵥ (model 0 1 *ᵥ v) := by
 have h := mass_diagonal_floor.posSemidef.dotProduct_mulVec_nonneg v
 simp only [star_trivial,Matrix.sub_mulVec,dotProduct_sub] at h
 rw [dot_smul,dot_diagonal] at h
 have he : (∑ i : Fin 5, ((1000:ℝ)^i.val*v i)^2)=
   ∑ i : Fin 5, (1000:ℝ)^(2*i.val)*v i^2 := by
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_pow,← pow_mul,Nat.mul_comm i.val 2]
 rw [← he] at h
 linarith only [h]

/-- Every Cauchy coefficient fits the same fixed diagonal scaling. -/
theorem cauchy_coeff_bound (k : ℕ) (hk : k≤8) :
  ((2*k).factorial : ℝ)*(400/9)^k≤1000*(1000:ℝ)^k := by
 interval_cases k <;> norm_num

end GaloisForLFunctions.ThetaCuspSections.TailMassFloor
