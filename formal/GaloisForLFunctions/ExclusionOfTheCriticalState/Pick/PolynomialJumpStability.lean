import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.PolynomialJumpRealization

/-!
# Sharp stability of polynomial jump tomography

Although an individual squared distance table satisfies positivity
constraints, differences of two physical tables exhaust the space of
symmetric hollow matrices. This makes the absolute sum of the
off-diagonal interpolation weights the exact amplification of grid error.
-/

noncomputable section
open Finset Matrix
open scoped NNReal
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk.JumpGrid
variable {n k l : ℕ}

/-- Every signed symmetric hollow table is the difference of two realizable
tables on the same prescribed grid, with a common degree bound. -/
theorem signed_realization (v : Nodes n) (D : Table n) (hD : hollow D) :
    ∃ F G : Fin (n+1) → Channel n, table v F-table v G=D := by
  classical
  let F := fun a => interpolateValues v (fun i => (if a=i then 1 else 0)-D a i)
  let G := fun a => interpolateValues v (fun i => (if a=i then 1 else 0)+D a i)
  refine ⟨F,G,?_⟩
  ext i j
  change rate F (v i) (v j)-rate G (v i) (v j)=D i j
  simp only [rate,F,G,eval_values,← sum_sub_distrib]
  have term (a : Fin (n+1)) :
      gapCost ((if a=i then 1 else 0)-D a i) ((if a=j then 1 else 0)-D a j)-
        gapCost ((if a=i then 1 else 0)+D a i) ((if a=j then 1 else 0)+D a j) =
      ((if a=i then D a j-D a i else 0)-(if a=j then D a j-D a i else 0))/2 := by
    by_cases hi : a=i <;> by_cases hj : a=j <;> simp only [hi,hj,if_true,if_false,gapCost] <;> ring
  simp only [term,← sum_div,sum_sub_distrib,sum_ite_eq',mem_univ,if_true,hD.1,hD.2 j i]
  ring

/-- The absolute off-diagonal interpolation mass. Entries are counted in
both orientations and divided by two. -/
def gain {I : Type*} [Fintype I] [DecidableEq I] (w : I → ℝ) :=
  (∑ i, ∑ j, if i=j then 0 else |w i*w j|)/2

private theorem decode_sub {I : Type*} [Fintype I] (w : I → ℝ) (A B : I → I → ℝ) :
    decode w A-decode w B=decode w (fun i j => A i j-B i j) := by
  simp only [decode,mul_sub,sum_sub_distrib]
  ring

private theorem decode_expanded {I : Type*} [Fintype I] (w : I → ℝ) (D : I → I → ℝ) :
    decode w D= -(∑ i, ∑ j, (w i*w j)*D i j)/2 := by
  simp only [decode,mul_sum,mul_assoc]

private theorem decode_bound {I : Type*} [Fintype I] [DecidableEq I] (w : I → ℝ)
    (D : I → I → ℝ) (diag : ∀ i, D i i=0) (b : ℝ) (hb : ∀ i j, |D i j|≤b) :
    |decode w D|≤b*gain w := by
  rw [decode_expanded,abs_div,abs_neg,show |(2:ℝ)|=2 by norm_num,gain,← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  calc
    _ ≤ ∑ i, |∑ j, (w i*w j)*D i j| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |(w i*w j)*D i j| :=
      sum_le_sum fun _ _ => abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, b*(if i=j then 0 else |w i*w j|) := by
      refine sum_le_sum fun i _ => sum_le_sum fun j _ => ?_
      by_cases h : i=j
      · subst j
        simp [diag]
      · rw [if_neg h,abs_mul,mul_comm b]
        exact mul_le_mul_of_nonneg_left (hb i j) (abs_nonneg _)
    _ = _ := by simp only [mul_sum]

/-- Noise at the grid propagates with the absolute off-diagonal mass,
even when the two models have different numbers of jumps. -/
theorem rate_error_bound (v : Nodes n) (F : Fin k → Channel n) (G : Fin l → Channel n)
    (b x y : ℝ) (h : ∀ i j, |table v F i j-table v G i j|≤b) :
    |rate F x y-rate G x y|≤b*gain (difference v x y) := by
  rw [interpolate_rates v F,interpolate_rates v G,decode_sub]
  exact decode_bound _ _ (fun i => by simp [table,rate,gapCost]) b h

private def extreme {I : Type*} [DecidableEq I] (w : I → ℝ) (b : ℝ) (i j : I) :=
  if i=j then 0 else if 0≤w i*w j then -b else b

private theorem saturated {I : Type*} [Fintype I] [DecidableEq I] (w : I → ℝ) (b : ℝ) :
    decode w (extreme w b)=b*gain w := by
  rw [decode_expanded,gain]
  have term (i j : I) : (w i*w j)*extreme w b i j =
      -b*(if i=j then 0 else |w i*w j|) := by
    by_cases e : i=j
    · simp [extreme,e]
    · by_cases h : 0≤w i*w j
      · simp [extreme,e,h,abs_of_nonneg h,mul_comm]
      · simp [extreme,e,h,abs_of_neg (lt_of_not_ge h),mul_comm]
  simp only [term,← mul_sum]
  ring

/-- For each requested off-grid pair, two physical polynomial banks attain
the entire worst-case amplification at any specified nonnegative noise level. -/
theorem rate_error_sharp (v : Nodes n) (b : ℝ≥0) (x y : ℝ) :
    ∃ F G : Fin (n+1) → Channel n,
      (∀ i j, |table v F i j-table v G i j|≤b.val) ∧
      rate F x y-rate G x y=b.val*gain (difference v x y) := by
  classical
  let w := difference v x y
  let D : Table n := extreme w b.val
  have hd : hollow D := by
    refine ⟨fun i => by simp [D,extreme],fun i j => ?_⟩
    by_cases h : i=j
    · subst j; rfl
    · simp [D,extreme,h,Ne.symm h,mul_comm]
  obtain ⟨F,G,e⟩ := signed_realization v D hd
  have eq (i j : Fin (n+1)) : table v F i j-table v G i j=D i j :=
    congrFun (congrFun e i) j
  refine ⟨F,G,fun i j => ?_,?_⟩
  · rw [eq]
    unfold D extreme
    split_ifs <;> simp [b.property,abs_of_nonneg]
  · rw [interpolate_rates v F,interpolate_rates v G,decode_sub]
    change decode w (fun i j => table v F i j-table v G i j)=_
    simp only [eq]
    exact saturated w b.val

#print axioms signed_realization
#print axioms rate_error_bound
#print axioms rate_error_sharp
end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk.JumpGrid
