import Mathlib.LinearAlgebra.RootSystem.OfBilinear
import Mathlib.LinearAlgebra.RootSystem.Reduced
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# The root shell of an integer-valued positive quadratic form

Polarization doubles the metric on the norm-one shell. Its coroots are
integral even for a nonclassical quadratic form. Reduction modulo two
identifies precisely opposite roots, so any set of distinct root lines
injects into the nonzero binary coordinate vectors.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.IntegralRootShell
open QuadraticMap

variable {J : Type*}
abbrev Lattice (J : Type*) := J → ℤ
abbrev Form (J : Type*) := QuadraticForm ℤ (Lattice J)
abbrev Root (Q : Form J) := {x : Lattice J // Q x=1}

private theorem square_polar (Q : Form J) (x : Lattice J) :
    Q.polarBilin x x=2*Q x := by rw [polarBilin_apply_apply,polar_self,two_nsmul,two_mul]

private theorem parallelogram (Q : Form J) (x y : Lattice J) :
    Q (x+y)+Q (x-y)=2*(Q x+Q y) := by
  obtain ⟨B,h⟩ := Q.exists_companion
  rw [sub_eq_add_neg,h,h,Q.map_neg,map_neg]
  ring

/-- Binary coordinate class. -/
def parity (x : Lattice J) (j : J) : Bool := decide (x j % 2=1)

private theorem parity_eq {x y : Lattice J} (he : parity x=parity y) (j : J) : x j%2=y j%2 := by
  have h := congrFun he j
  simp only [parity,decide_eq_decide] at h
  omega

private theorem parity_neg (x : Lattice J) : parity (-x)=parity x := by
  funext j
  simp only [parity,Pi.neg_apply,decide_eq_decide]
  omega

/-- The midpoint and half-difference of congruent minimal vectors are
integral. Their two energies add to one, forcing one vector to vanish. -/
theorem root_parity_iff (Q : Form J) (hQ : Q.PosDef) (x y : Root Q) :
    parity x.val=parity y.val ↔ x.val=y.val ∨ x.val= -y.val := by
  constructor
  · intro he
    let a := fun j => (x.val j+y.val j)/2
    let b := fun j => (x.val j-y.val j)/2
    have hx : a+b=x.val := by
      funext j
      have h := parity_eq he j
      dsimp only [Pi.add_apply,a,b]
      omega
    have hy : a-b=y.val := by
      funext j
      have h := parity_eq he j
      dsimp only [Pi.sub_apply,a,b]
      omega
    have h := parallelogram Q a b
    rw [hx,hy,x.property,y.property] at h
    by_cases hz : b=0
    · exact Or.inl (by rw [← hx,← hy,hz,add_zero,sub_zero])
    · have ha : a=0 := by
        by_contra hn
        have hp := hQ a hn
        have hq := hQ b hz
        omega
      exact Or.inr (by rw [← hx,← hy,ha,zero_add,zero_sub,neg_neg])
  · rintro (h|h)
    · rw [h]
    · rw [h,parity_neg]

/-- A norm-one vector cannot occupy the even class. -/
theorem parity_nonzero (Q : Form J) (x : Root Q) : parity x.val ≠ fun _ => false := by
  intro he
  let v := fun j => x.val j/2
  have hv : x.val=(2:ℤ) • v := by
    funext j
    have h := congrFun he j
    simp only [parity,decide_eq_false_iff_not] at h
    change x.val j=2*(x.val j/2)
    omega
  have h := x.property
  rw [hv,Q.map_smul,smul_eq_mul] at h
  omega

/-- A finite choice of different root lines uses at most one representative
per nonzero parity class. -/
theorem line_bound [Fintype J] {I : Type*} [Fintype I] (Q : Form J) (hQ : Q.PosDef)
    (x : I → Root Q) (sep : ∀ i j, (x i).val=(x j).val ∨ (x i).val= -(x j).val → i=j) :
    Fintype.card I+1 ≤ 2^(Fintype.card J) := by
  classical
  let f : Option I → (J → Bool)
    | none => fun _ => false
    | some i => parity (x i).val
  have hi : Function.Injective f := by
    rintro (_|i) (_|j) h
    · rfl
    · exact (parity_nonzero Q _ h.symm).elim
    · exact (parity_nonzero Q _ h).elim
    · exact congrArg some (sep i j ((root_parity_iff Q hQ _ _).mp h))
  simpa only [Fintype.card_option,Fintype.card_fun,Fintype.card_bool] using Fintype.card_le_of_injective f hi

private theorem root_pair (Q : Form J) (x : Root Q) : Q.polarBilin x.val x.val=2 := by
  rw [square_polar,x.property,mul_one]

/-- All distinct nonopposite roots have doubled inner product −1, 0 or 1. -/
theorem root_angles (Q : Form J) (hQ : Q.PosDef) (x y : Root Q) :
    x.val=y.val ∨ x.val= -y.val ∨ Q.polarBilin x.val y.val= -1 ∨
      Q.polarBilin x.val y.val=0 ∨ Q.polarBilin x.val y.val=1 := by
  by_cases he : x.val=y.val
  · exact Or.inl he
  by_cases hn : x.val= -y.val
  · exact Or.inr (Or.inl hn)
  have hp : x.val+y.val ≠ 0 := fun h => hn (eq_neg_of_add_eq_zero_left h)
  have h1 := hQ _ hp
  have h2 := hQ _ (sub_ne_zero.mpr he)
  rw [QuadraticMap.map_add Q,x.property,y.property] at h1
  rw [sub_eq_add_neg,QuadraticMap.map_add Q,Q.map_neg,x.property,y.property,polar_neg_right] at h2
  change _ ∨ _ ∨ polar Q x.val y.val= -1 ∨ polar Q x.val y.val=0 ∨ polar Q x.val y.val=1
  omega

private theorem reflected_energy (Q : Form J) (x : Root Q) (y : Lattice J) :
    Q (Module.reflection (root_pair Q x) y)=Q y := by
  rw [Module.reflection_apply,sub_eq_add_neg,QuadraticMap.map_add Q,Q.map_neg,
    Q.map_smul,x.property,smul_eq_mul,mul_one,polar_neg_right,polar_smul_right,smul_eq_mul,
    polar_comm Q y x.val]
  simp only [polarBilin_apply_apply]
  ring

private def reflectRoot (Q : Form J) (x : Root Q) : Root Q ≃ Root Q where
  toFun y := ⟨Module.reflection (root_pair Q x) y.val,(reflected_energy Q x y.val).trans y.property⟩
  invFun y := ⟨Module.reflection (root_pair Q x) y.val,(reflected_energy Q x y.val).trans y.property⟩
  left_inv y := Subtype.ext (Module.involutive_reflection (root_pair Q x) y.val)
  right_inv y := Subtype.ext (Module.involutive_reflection (root_pair Q x) y.val)

/-- The exact norm-one shell, with its integral polar coroots, is a
crystallographic root datum on the original lattice and its dual. -/
def datum [Fintype J] (Q : Form J) (hQ : Q.PosDef) :
    RootDatum (Root Q) (Lattice J) (Module.Dual ℤ (Lattice J)) where
  toLinearMap := Module.Dual.eval ℤ _
  root := Function.Embedding.subtype _
  coroot := ⟨fun x => Q.polarBilin x.val,fun x y he => by
    change Q.polarBilin x.val=Q.polarBilin y.val at he
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply hQ.anisotropic
    have hz : Q.polarBilin (x.val-y.val)=0 := by rw [map_sub,he,sub_self]
    have h := square_polar Q (x.val-y.val)
    rw [hz] at h
    change 0=2*Q (x.val-y.val) at h
    omega⟩
  root_coroot_two x := root_pair Q x
  reflectionPerm := reflectRoot Q
  reflectionPerm_root _ _ := rfl
  reflectionPerm_coroot x y := by
    change Q.polarBilin y.val-(Q.polarBilin y.val x.val) • Q.polarBilin x.val =
      Q.polarBilin (Module.reflection (root_pair Q x) y.val)
    rw [Module.reflection_apply,map_sub,map_smul]
    exact congrArg (fun s : ℤ => Q.polarBilin y.val-s • Q.polarBilin x.val)
      (polar_comm Q y.val x.val)

/-- The shell is finite in finite rank. In a fixed parity class, knowing
the signs of the coordinates chooses one of the two opposite vectors. -/
theorem finite_roots [Fintype J] (Q : Form J) (hQ : Q.PosDef) : Finite (Root Q) := by
  let f (x : Root Q) := (parity x.val,fun j => decide (0<x.val j))
  apply Finite.of_injective f
  intro x y he
  apply Subtype.ext
  rcases (root_parity_iff Q hQ _ _).mp (congrArg Prod.fst he) with h|h
  · exact h
  · funext j
    have hs := congrFun (congrArg Prod.snd he) j
    have hn := congrFun h j
    change x.val j = -y.val j at hn
    change decide (0<x.val j)=decide (0<y.val j) at hs
    rw [decide_eq_decide] at hs
    omega

/-- Two linearly dependent roots must coincide up to sign. For the three
remaining angles the two-by-two integral Gram matrix is nonsingular. -/
theorem reduced [Fintype J] (Q : Form J) (hQ : Q.PosDef) : (datum Q hQ).IsReduced := by
  constructor
  intro x y hdep
  change x.val=y.val ∨ x.val= -y.val
  rcases root_angles Q hQ x y with he|he|ha
  · exact Or.inl he
  · exact Or.inr he
  exfalso
  apply hdep
  change LinearIndependent ℤ ![x.val,y.val]
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  rw [Fin.sum_univ_two] at hc
  have hx := congrArg (Q.polarBilin x.val) hc
  have hy := congrArg (Q.polarBilin y.val) hc
  have hs : Q.polarBilin y.val x.val=Q.polarBilin x.val y.val := polar_comm Q _ _
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,map_add,map_smul,root_pair,hs,smul_eq_mul,map_zero] at hx hy
  have hc0 : c 0=0 ∧ c 1=0 := by
    rcases ha with ha|ha|ha <;> rw [ha] at hx hy <;> constructor <;> omega
  exact Fin.cases hc0.1 (fun j => by
    have e : j=0 := Subsingleton.elim _ _
    subst j
    exact hc0.2) i

#print axioms root_parity_iff
#print axioms line_bound
#print axioms root_angles
#print axioms datum
#print axioms finite_roots
#print axioms reduced
end GaloisForLFunctions.HTGeometry.IntegralRootShell
