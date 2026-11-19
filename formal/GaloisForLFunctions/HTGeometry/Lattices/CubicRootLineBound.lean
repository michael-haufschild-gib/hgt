import GaloisForLFunctions.HTGeometry.Lattices.IntegralQuadraticRootShell
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# A cubic interpolation bound for integral root lines

For norm-one vectors the doubled pairing has off-line values −1,0,1.
The cubic t³−t therefore separates each root line from all the others.
Homogenizing the linear term by the norm realizes this interpolation
inside the symmetric cube of the dual lattice.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.HTGeometry.IntegralRootShell

variable {J I : Type*} [Fintype J] [Fintype I]

/-- Coordinates of the symmetric cube of an integer vector. -/
def cubicFeatures (x : Lattice J) (p : Sym J 3) : ℤ := (p.val.map x).prod

omit [Fintype J] in
private theorem coord_lift (y : I → Lattice J) (a : I → ℤ) (L : Module.Dual ℤ (Lattice J))
    (h : ∀ j, ∑ i, a i*y i j=0) : ∑ i, a i*L (y i)=0 := by
  have hz : ∑ i, a i • y i = 0 := by
    funext j
    simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] using h j
  simpa only [map_sum,map_smul,smul_eq_mul,map_zero] using congrArg L hz

omit [Fintype J] in
private theorem three_forms (y : I → Lattice J) (a : I → ℤ)
    (h : ∑ i, a i • cubicFeatures (y i)=0)
    (L M N : Module.Dual ℤ (Lattice J)) :
    ∑ i, a i*L (y i)*M (y i)*N (y i)=0 := by
  have coord (u v w : J) : ∑ i, a i*y i u*y i v*y i w=0 := by
    let p : Sym J 3 := ⟨u ::ₘ v ::ₘ w ::ₘ 0,by simp⟩
    have e : (∑ i, a i • cubicFeatures (y i)) p=(0:ℤ) := congrFun h p
    simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply,cubicFeatures,
      p,Multiset.map_cons,Multiset.map_zero,Multiset.prod_cons,Multiset.prod_zero,mul_one,mul_assoc] using e
  have one (u v : J) : ∑ i, a i*y i u*y i v*L (y i)=0 :=
    coord_lift y _ L (coord u v)
  have two (u : J) : ∑ i, a i*y i u*L (y i)*M (y i)=0 := by
    apply coord_lift y _ M
    intro v
    convert one u v using 1
    exact sum_congr rfl fun i _ => by ring
  apply coord_lift y _ N
  intro u
  convert two u using 1
  exact sum_congr rfl fun i _ => by ring

omit [Fintype J] in
private theorem self_pairing (Q : Form J) (y : Root Q) : Q.polarBilin y.val y.val=2 := by
  rw [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar_self,two_nsmul,y.property]
  norm_num

private theorem sphere_contraction (Q : Form J) (y : I → Root Q) (a : I → ℤ)
    (h : ∑ i, a i • cubicFeatures (y i).val=0) (L : Module.Dual ℤ (Lattice J)) :
    ∑ i, a i*L (y i).val=0 := by
  classical
  let e (j : J) : Lattice J := Pi.single j 1
  have coeff (v : Lattice J) : ∑ j, v j • e j=v := by
    funext k
    simp [e,Pi.single_apply,Finset.sum_apply]
  have expansion (i : I) : ∑ j, (y i).val j*Q.polarBilin (e j) (y i).val=2 := by
    calc
      _ = (Q.polarBilin (∑ j, (y i).val j • e j)) (y i).val := by
        simp only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul]
      _ = 2 := by rw [coeff,self_pairing]
  have row (j : J) : ∑ i, a i*L (y i).val*(y i).val j*Q.polarBilin (e j) (y i).val = 0 :=
    three_forms (fun i => (y i).val) a h L (LinearMap.proj j) (Q.polarBilin (e j))
  have total : (∑ i, a i*L (y i).val)*2=0 := by
    calc
      _ = ∑ i, (a i*L (y i).val)*(∑ j, (y i).val j*Q.polarBilin (e j) (y i).val) := by
        simp only [expansion,sum_mul]
      _ = ∑ j, ∑ i, a i*L (y i).val*(y i).val j*Q.polarBilin (e j) (y i).val := by
        rw [sum_comm]
        simp only [mul_sum,mul_assoc]
      _ = 0 := by simp only [row,sum_const_zero]
  omega

/-- Cubes of distinct root lines are linearly independent over the integers.
Evaluating t³−t at their pairings recovers each coefficient individually. -/
theorem independent_cubic_features (Q : Form J) (hQ : Q.PosDef) (y : I → Root Q)
    (sep : ∀ i j, (y i).val=(y j).val ∨ (y i).val= -(y j).val → i=j) :
    LinearIndependent ℤ (fun i => cubicFeatures (y i).val) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro a h j
  let L := Q.polarBilin (y j).val
  have three := three_forms (fun i => (y i).val) a h L L L
  have one := sphere_contraction Q y a h L
  have test (i : I) : a i*L (y i).val*L (y i).val*L (y i).val-a i*L (y i).val =
      if i=j then 6*a j else 0 := by
    by_cases hij : i=j
    · subst i
      simp only [L,self_pairing,if_true]
      ring
    · rw [if_neg hij]
      rcases root_angles Q hQ (y j) (y i) with he|he|he|he|he
      · exact (hij (sep j i (Or.inl he)).symm).elim
      · exact (hij (sep j i (Or.inr he)).symm).elim
      all_goals dsimp only [L]; rw [he]; ring
  have eq : 0 = 6*a j := by
    calc
      _ = (∑ i, a i*L (y i).val*L (y i).val*L (y i).val)-(∑ i, a i*L (y i).val) := by rw [three,one,sub_self]
      _ = 6*a j := by rw [← sum_sub_distrib]; simp only [test,sum_ite_eq',mem_univ,if_true]
  omega

/-- In rank d the number of distinct minimal lines is at most
binomial(d+2,3). In particular rank eight permits at most 120 lines. -/
theorem cubic_line_bound (Q : Form J) (hQ : Q.PosDef) (y : I → Root Q)
    (sep : ∀ i j, (y i).val=(y j).val ∨ (y i).val= -(y j).val → i=j) :
    Fintype.card I ≤ (Fintype.card J+2).choose 3 := by
  classical
  have h := (independent_cubic_features Q hQ y sep).fintype_card_le_finrank
  simpa only [Module.finrank_pi,Sym.card_sym_eq_choose,show Fintype.card J+3-1=Fintype.card J+2 by omega] using h

#print axioms independent_cubic_features
#print axioms cubic_line_bound
end GaloisForLFunctions.HTGeometry.IntegralRootShell
