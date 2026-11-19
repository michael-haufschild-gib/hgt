import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.PolynomialJumpInterpolation
import Mathlib.Analysis.Matrix.PosDef

/-!
# Which polynomial jump readouts are possible?

Double centering at a reference momentum recovers the real Gram matrix
of all jump differences. Its positivity characterizes the admissible
tables. Its rank counts the smallest number of polynomial channels that
produce the full continuum of rates.
-/

noncomputable section
open Polynomial Finset Matrix
open scoped Matrix
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk.JumpGrid
variable {n k : ℕ}
abbrev Table (n : ℕ) := Matrix (Fin (n+1)) (Fin (n+1)) ℝ

def table (v : Nodes n) (F : Fin k → Channel n) : Table n := fun i j => rate F (v i) (v j)

/-- Gram matrix of the differences from the first grid value. -/
def anchored (D : Table n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => 4*(D 0 i.succ+D 0 j.succ-D i.succ j.succ)

/-- A squared distance table has zero diagonal and is symmetric. -/
def hollow (D : Table n) := (∀ i, D i i=0) ∧ ∀ i j, D i j=D j i

private theorem table_hollow (v : Nodes n) (F : Fin k → Channel n) : hollow (table v F) := by
  refine ⟨fun i => by simp [table,rate,gapCost],fun i j => ?_⟩
  simp only [table,rate]
  exact sum_congr rfl fun a _ => by unfold gapCost; ring

private def displacement (v : Nodes n) (F : Fin k → Channel n) : Matrix (Fin n) (Fin k) ℝ :=
  fun i a => (F a).val.eval (v i.succ)-(F a).val.eval (v 0)

private theorem gram_table (v : Nodes n) (F : Fin k → Channel n) :
    anchored (table v F) = displacement v F*(displacement v F)ᵀ := by
  ext i j
  simp only [anchored,table,rate,← sum_add_distrib,← sum_sub_distrib,mul_sum,
    Matrix.mul_apply,Matrix.transpose_apply,displacement]
  exact sum_congr rfl fun a _ => by unfold gapCost; ring

private theorem anchored_injective (D E : Table n) (hd : hollow D) (he : hollow E)
    (h : anchored D=anchored E) : D=E := by
  have values (i j : Fin n) := congrFun (congrFun h i) j
  have first (i : Fin n) : D 0 i.succ=E 0 i.succ := by
    have e := values i i
    simp only [anchored,hd.1,he.1,sub_zero] at e
    linarith only [e]
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i
  · exact Fin.cases ((hd.1 0).trans (he.1 0).symm) first j
  · refine Fin.cases ((hd.2 _ _).trans ((first i).trans (he.2 _ _))) (fun j => ?_) j
    have e := values i j
    change 4*(_+_-_)=4*(_+_-_) at e
    linarith only [e,first i,first j]

/-- The unique degree-bounded channel with the prescribed grid values. -/
def interpolateValues (v : Nodes n) (f : Fin (n+1) → ℝ) : Channel n :=
  ⟨Lagrange.interpolate univ v f,Polynomial.natDegree_le_iff_degree_le.mpr (by
    simpa only [Finset.card_univ,Fintype.card_fin,Nat.add_sub_cancel] using
      Lagrange.degree_interpolate_le (s:=univ) f v.injective.injOn)⟩

theorem eval_values (v : Nodes n) (f : Fin (n+1) → ℝ) (i : Fin (n+1)) :
    (interpolateValues v f).val.eval (v i)=f i := Lagrange.eval_interpolate_at_node f v.injective.injOn (mem_univ _)

private theorem realize_factor (D : Table n) (hd : hollow D) (v : Nodes n)
    (R : Matrix (Fin n) (Fin k) ℝ) (h : anchored D=R*Rᵀ) :
    ∃ F : Fin k → Channel n, table v F=D := by
  let F := fun a => interpolateValues v (Fin.cases 0 fun i => R i a)
  have he : displacement v F=R := by
    ext i a
    simp [F,displacement,eval_values]
  exact ⟨F,anchored_injective _ _ (table_hollow v F) hd (by rw [gram_table,he,h])⟩

/-- Remove the zero eigenspaces before taking square roots. This gives a
real Gram factor with exactly rank-many columns, also at rank zero. -/
private theorem thin_factor (M : Matrix (Fin n) (Fin n) ℝ) (hp : M.PosSemidef) :
    ∃ R : Matrix (Fin n) (Fin M.rank) ℝ, M=R*Rᵀ := by
  classical
  let h := hp.isHermitian
  let L := h.eigenvalues
  let U : Matrix (Fin n) (Fin n) ℝ := h.eigenvectorUnitary
  have spectral : M=U*diagonal L*Uᵀ := by
    simpa only [Unitary.conjStarAlgAut_apply,Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial,RCLike.ofReal_real_eq_id,Function.id_comp] using h.spectral_theorem
  let S := {a : Fin n // L a≠0}
  let e : S ≃ Fin M.rank := Fintype.equivFinOfCardEq h.rank_eq_card_non_zero_eigs.symm
  let R : Matrix (Fin n) (Fin M.rank) ℝ := fun i a => U i (e.symm a).val*Real.sqrt (L (e.symm a).val)
  refine ⟨R,?_⟩
  ext i j
  let f := fun a => U i a*L a*U j a
  have zeros : ∑ a : {a : Fin n // ¬L a≠0}, f a.val=0 := sum_eq_zero fun a _ => by
    simp only [f,not_ne_iff.mp a.property,mul_zero,zero_mul]
  have restricted : (∑ a : S, f a.val)=∑ a, f a := by
    simpa only [zeros,add_zero] using Fintype.sum_subtype_add_sum_subtype (fun a => L a≠0) f
  have eq (a : S) : R i (e a)*R j (e a)=f a.val := by
    simp only [R,e.symm_apply_apply,f]
    have hs := Real.sq_sqrt (hp.eigenvalues_nonneg a.val)
    change Real.sqrt (L a.val)^2=L a.val at hs
    linear_combination U i a.val*U j a.val*hs
  calc
    M i j = ∑ a, f a := by
      conv_lhs => rw [spectral]
      rw [Matrix.mul_apply]
      simp only [Matrix.mul_diagonal,Matrix.transpose_apply,f]
    _ = ∑ a : S, f a.val := restricted.symm
    _ = ∑ a : S, R i (e a)*R j (e a) := sum_congr rfl fun a _ => (eq a).symm
    _ = _ := e.sum_comp (fun b => R i b*R j b)

theorem rank_needed (v : Nodes n) (F : Fin k → Channel n) : (anchored (table v F)).rank ≤ k := by
  rw [gram_table]
  exact (Matrix.rank_mul_le_left _ _).trans (displacement v F).rank_le_width

private theorem table_positive (v : Nodes n) (F : Fin k → Channel n) : (anchored (table v F)).PosSemidef := by
  rw [gram_table,← Matrix.conjTranspose_eq_transpose_of_trivial]
  exact Matrix.posSemidef_self_mul_conjTranspose _

/-- Positivity gives both a consistency test and an interpolating bank of
optimal size. Symmetry and zero diagonal are tested on the supplied data. -/
theorem table_realizable_iff (D : Table n) (v : Nodes n) :
    (hollow D ∧ (anchored D).PosSemidef) ↔
      ∃ F : Fin (anchored D).rank → Channel n, table v F=D := by
  constructor
  · rintro ⟨hd,hp⟩
    obtain ⟨R,hR⟩ := thin_factor _ hp
    exact realize_factor D hd v R hR
  · rintro ⟨F,hF⟩
    exact hF ▸ And.intro (table_hollow v F) (table_positive v F)

/-- Grid rank gives the minimal number of jumps for the whole continuous
experiment. The polynomial degree bound persists after compression. -/
theorem minimal_bank (v : Nodes n) (F : Fin k → Channel n) :
    let d := (anchored (table v F)).rank
    (∃ G : Fin d → Channel n, rate G=rate F) ∧
      ∀ (l : ℕ) (G : Fin l → Channel n), rate G=rate F → d≤l := by
  obtain ⟨G,hG⟩ := (table_realizable_iff (table v F) v).mp ⟨table_hollow _ _,table_positive _ _⟩
  refine ⟨⟨G,(grid_complete v G F).mp (Matrix.ext_iff.mpr hG)⟩,fun l G h => ?_⟩
  have eq : table v G=table v F := Matrix.ext ((grid_complete v G F).mpr h)
  rw [← eq]
  exact rank_needed _ _

#print axioms rank_needed
#print axioms table_realizable_iff
#print axioms minimal_bank
end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk.JumpGrid
