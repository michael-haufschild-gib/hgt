import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.WeilGaussianSemigroup
import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.WeilPairScattering
import GaloisForLFunctions.HTGeometry.PolynomialExtrapolationRemez

/-!
# Interpolation of polynomial jump distances from a finite Weil probe

Squared Euclidean distances determine the squared norm of every affine
difference. Lagrange interpolation gives the coefficients of that difference
for a bank of polynomial jumps. Every unordered edge of a grid of degree
plus one nodes is necessary, even for single-channel measurements.
-/

noncomputable section
open Polynomial Finset
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk.JumpGrid

variable {n k l : ℕ}
abbrev Nodes (n : ℕ) := Fin (n+1) ↪ ℝ
abbrev Channel (n : ℕ) := {P : ℝ[X] // P.natDegree ≤ n}

def rate (F : Fin k → Channel n) (x y : ℝ) := ∑ a, gapCost ((F a).val.eval x) ((F a).val.eval y)

/-- The coefficient vector of evaluation at x minus evaluation at y. -/
def difference (v : Nodes n) (x y : ℝ) (i : Fin (n+1)) :=
  (Lagrange.basis univ v i).eval x-(Lagrange.basis univ v i).eval y

private theorem sum_difference (v : Nodes n) (x y : ℝ) : ∑ i, difference v x y i = 0 := by
  have H (t : ℝ) := congrArg (Polynomial.eval t)
    (Lagrange.sum_basis (s:=univ) v.injective.injOn Finset.univ_nonempty)
  simp only [eval_finsetSum,eval_one] at H
  simp only [difference,sum_sub_distrib,H,sub_self]

private theorem eval_difference (v : Nodes n) (P : Channel n) (x y : ℝ) :
    P.val.eval x-P.val.eval y=∑ i, difference v x y i*P.val.eval (v i) := by
  have h := HTGeometry.eval_eq_sum_lagrangeBasis P.val P.property v v.injective
  rw [h x,h y,← sum_sub_distrib]
  exact sum_congr rfl fun i _ => by unfold difference; ring

/-- Contraction of a distance matrix against a zero-mass vector. -/
def decode {I : Type*} [Fintype I] (w : I → ℝ) (D : I → I → ℝ) :=
  -(∑ i, w i*∑ j, w j*D i j)/2

private theorem decode_distance {I : Type*} [Fintype I] (w f : I → ℝ) (hw : ∑ i, w i=0) :
    decode w (fun i j => gapCost (f i) (f j))=(∑ i, w i*f i)^2/8 := by
  let A := ∑ j, w j*f j
  let B := ∑ j, w j*(f j)^2
  have row (i : I) : ∑ j, w j*gapCost (f i) (f j) = (B-2*f i*A)/8 := by
    calc
      _ = ((∑ j, w j)*(f i)^2+B-2*f i*A)/8 := by
        simp only [A,B,sum_mul,mul_sum,← sum_add_distrib,← sum_sub_distrib,sum_div]
        exact sum_congr rfl fun j _ => by unfold gapCost; ring
      _ = _ := by rw [hw]; ring
  unfold decode
  simp only [row]
  have total : ∑ i, w i*((B-2*f i*A)/8) = ((∑ i, w i)*B-2*A*A)/8 := by
    conv_rhs => rw [show 2*A*A=(∑ i, w i*f i)*(2*A) by change 2*A*A=A*(2*A); ring]
    rw [sum_mul,sum_mul,← sum_sub_distrib,sum_div]
    exact sum_congr rfl fun i _ => by ring
  rw [total,hw]
  change _=A^2/8
  ring

private theorem decode_add {I : Type*} [Fintype I] (w : I → ℝ) (A B : I → I → ℝ) :
    decode w (fun i j => A i j+B i j)=decode w A+decode w B := by
  simp only [decode,mul_add,sum_add_distrib,neg_add,add_div]

/-- Every polynomial-bank rate has an explicit linear reconstruction from
the squared jump readings on degree plus one distinct nodes. -/
theorem interpolate_rates (v : Nodes n) (F : Fin k → Channel n) (x y : ℝ) :
    rate F x y = decode (difference v x y) (fun i j => rate F (v i) (v j)) := by
  let w := difference v x y
  have atom (P : Channel n) : gapCost (P.val.eval x) (P.val.eval y) =
      decode w (fun i j => gapCost (P.val.eval (v i)) (P.val.eval (v j))) := by
    rw [decode_distance _ _ (sum_difference v x y)]
    unfold gapCost
    rw [eval_difference v P x y]
  have aux (s : Finset (Fin k)) :
      ∑ a ∈ s, gapCost ((F a).val.eval x) ((F a).val.eval y) =
      decode w (fun i j => ∑ a ∈ s, gapCost ((F a).val.eval (v i)) ((F a).val.eval (v j))) := by
    induction s using Finset.induction_on with
    | empty => simp [decode]
    | insert a s ha ih => simp only [sum_insert ha,decode_add,← ih,← atom]
  exact aux univ

/-- Agreement at one grid is equivalent to agreement of the entire dephasing law. -/
theorem grid_complete (v : Nodes n) (F : Fin k → Channel n) (G : Fin l → Channel n) :
    (∀ i j, rate F (v i) (v j)=rate G (v i) (v j)) ↔ rate F=rate G := by
  refine ⟨fun h => ?_,fun h i j => by rw [h]⟩
  funext x y
  rw [interpolate_rates v F,interpolate_rates v G]
  exact congrArg (decode (difference v x y)) (funext fun i => funext (h i))

private def cardinalWave (v : Nodes n) (i : Fin (n+1)) := Lagrange.basis univ v i

private theorem cardinal_degree (v : Nodes n) (i : Fin (n+1)) : (cardinalWave v i).natDegree ≤ n := by
  simp [cardinalWave,Lagrange.natDegree_basis v.injective.injOn (mem_univ i)]

private theorem cardinal_eval (v : Nodes n) (i j : Fin (n+1)) :
    (cardinalWave v i).eval (v j)=if i=j then 1 else 0 := by
  by_cases h : i=j
  · subst j
    simp [cardinalWave,Lagrange.eval_basis_self v.injective.injOn]
  · simp [cardinalWave,h,Lagrange.eval_basis_of_ne h]

private theorem equal_gaps (x y u w : ℝ) :
    gapCost (x+y) (u+w)=gapCost (x-y) (u-w) ↔ x=u ∨ y=w := by
  have factor : ((x+y)-(u+w))^2-((x-y)-(u-w))^2=4*((x-u)*(y-w)) := by ring
  simp only [gapCost,div_left_inj' (by norm_num : (8:ℝ)≠0)]
  rw [← sub_eq_zero,factor]
  simp only [mul_eq_zero,show (4:ℝ)≠0 by norm_num,false_or,sub_eq_zero]

private theorem cardinal_same (v : Nodes n) (i a b : Fin (n+1)) :
    (cardinalWave v i).eval (v a)=(cardinalWave v i).eval (v b) ↔ (i=a ↔ i=b) := by
  rw [cardinal_eval,cardinal_eval]
  split_ifs <;> simp_all

private theorem off_edge {I : Type*} (i j a b : I) (hij : i≠j) :
    ((i=a ↔ i=b) ∨ (j=a ↔ j=b)) ↔ ¬((a=i ∧ b=j) ∨ (a=j ∧ b=i)) := by
  grind

/-- Omitting any one unoriented edge conceals a genuine rate difference.
The two witnesses use the sum and difference of its cardinal polynomials. -/
theorem every_edge_necessary (v : Nodes n) (i j : Fin (n+1)) (hij : i≠j) :
    ∃ F G : Fin 1 → Channel n, ∀ a b,
      rate F (v a) (v b) = rate G (v a) (v b) ↔ ¬((a=i ∧ b=j) ∨ (a=j ∧ b=i)) := by
  let A := cardinalWave v i
  let B := cardinalWave v j
  let F : Channel n := ⟨A+B,(natDegree_add_le _ _).trans (max_le (cardinal_degree v i) (cardinal_degree v j))⟩
  let G : Channel n := ⟨A-B,(natDegree_sub_le _ _).trans (max_le (cardinal_degree v i) (cardinal_degree v j))⟩
  refine ⟨fun _ => F,fun _ => G,fun a b => ?_⟩
  simp only [rate,Fin.sum_univ_one,F,G,A,B,eval_add,eval_sub,equal_gaps,cardinal_same]
  exact off_edge i j a b hij

/-- The complex signed Weil matrix on a single grid detects every polynomial
bank's rate function, even when the two banks have different sizes. -/
theorem weil_grid_iff (v : Nodes n) (F : Fin k → Channel n) (G : Fin l → Channel n)
    (p : Fin (n+1) → {u : ℝ // 1 ≤ u}) :
    let W := probeGram (fun i => (p i).val)
    jumpEvolution 1 (fun a i => (F a).val.eval (v i)) W =
      jumpEvolution 1 (fun a i => (G a).val.eval (v i)) W ↔ rate F=rate G := by
  intro W
  rw [← grid_complete v F G,← Matrix.ext_iff]
  apply forall_congr' fun i => forall_congr' fun j => ?_
  change (Real.exp (-(1:ℝ)*rate F (v i) (v j)):ℂ)*W i j =
    (Real.exp (-(1:ℝ)*rate G (v i) (v j)):ℂ)*W i j ↔ _
  have nz : W i j≠0 := safe_probeGram_entry_ne_zero p i j
  simp only [neg_one_mul,mul_left_inj' nz,Complex.ofReal_inj,
    Real.exp_injective.eq_iff,neg_inj]

#print axioms interpolate_rates
#print axioms grid_complete
#print axioms every_edge_necessary
#print axioms weil_grid_iff
end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk.JumpGrid
