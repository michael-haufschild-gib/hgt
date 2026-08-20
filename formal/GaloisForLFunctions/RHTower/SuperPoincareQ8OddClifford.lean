import GaloisForLFunctions.HTGeometry.SuperPoincareAlgebra
import GaloisForLFunctions.RHTower.DeningerQ8RootNumberNegOneAutomorphisms

noncomputable section

namespace RHTower

abbrev Q8TopField := deningerQ8RootNumberNegOneTopField

def q8IEnd : Module.End ℚ Q8TopField where
  toFun := q8I
  map_add' x y := q8I.map_add x y
  map_smul' c x := by
    simp only [Algebra.smul_def, RingHom.id_apply]
    rw [map_mul]
    have h : q8I (algebraMap ℚ Q8TopField c) = algebraMap ℚ Q8TopField c := by
      change q8I (c : Q8TopField) = (c : Q8TopField)
      exact q8I_rat c
    exact congrArg (fun z : Q8TopField => z * q8I x) h

def q8JEnd : Module.End ℚ Q8TopField where
  toFun := q8J
  map_add' x y := q8J.map_add x y
  map_smul' c x := by
    simp only [Algebra.smul_def, RingHom.id_apply]
    rw [map_mul]
    have h : q8J (algebraMap ℚ Q8TopField c) = algebraMap ℚ Q8TopField c := by
      change q8J (c : Q8TopField) = (c : Q8TopField)
      exact q8J_rat c
    exact congrArg (fun z : Q8TopField => z * q8J x) h

def q8CEnd : Module.End ℚ Q8TopField where
  toFun := q8C
  map_add' x y := q8C.map_add x y
  map_smul' c x := by
    simp only [Algebra.smul_def, RingHom.id_apply]
    rw [map_mul]
    have h : q8C (algebraMap ℚ Q8TopField c) = algebraMap ℚ Q8TopField c := by
      change q8C (c : Q8TopField) = (c : Q8TopField)
      exact q8C_rat c
    exact congrArg (fun z : Q8TopField => z * q8C x) h

theorem q8C_comp_q8I : q8C.comp q8I = q8I.comp q8C := by
  rw [← q8I_sq_eq_q8C]
  rfl

theorem q8C_comp_q8J : q8C.comp q8J = q8J.comp q8C := by
  rw [← q8J_sq_eq_q8C]
  rfl

/-- The `-1` eigenspace of the central quaternion element. -/
def q8OddSubmodule : Submodule ℚ Q8TopField where
  carrier := {x | q8C x = -x}
  zero_mem' := by simp
  add_mem' {x y} hx hy := by
    change q8C (x + y) = -(x + y)
    change q8C x = -x at hx
    change q8C y = -y at hy
    rw [map_add, hx, hy, neg_add]
  smul_mem' c x hx := by
    change q8C (c • x) = -(c • x)
    change q8C x = -x at hx
    simp only [Algebra.smul_def]
    rw [map_mul]
    have h : q8C (algebraMap ℚ Q8TopField c) = algebraMap ℚ Q8TopField c := by
      change q8C (c : Q8TopField) = (c : Q8TopField)
      exact q8C_rat c
    calc
      q8C (algebraMap ℚ Q8TopField c) * q8C x =
          (algebraMap ℚ Q8TopField c) * q8C x :=
        congrArg (fun z : Q8TopField => z * q8C x) h
      _ = (algebraMap ℚ Q8TopField c) * (-x) :=
        congrArg (fun z : Q8TopField => (algebraMap ℚ Q8TopField c) * z) hx
      _ = -((algebraMap ℚ Q8TopField c) * x) := mul_neg _ _

theorem mem_q8OddSubmodule_iff (x : Q8TopField) :
    x ∈ q8OddSubmodule ↔ q8C x = -x := Iff.rfl

def q8IOnOdd : Module.End ℚ q8OddSubmodule where
  toFun := fun x => ⟨q8I x.1, by
    apply (mem_q8OddSubmodule_iff _).2
    have hx : q8C x.1 = -x.1 := (mem_q8OddSubmodule_iff _).1 x.2
    calc
      q8C (q8I x.1) = q8I (q8C x.1) := by
        change (q8C.comp q8I) x.1 = (q8I.comp q8C) x.1
        rw [q8C_comp_q8I]
      _ = q8I (-x.1) := by rw [hx]
      _ = -q8I x.1 := map_neg _ _⟩
  map_add' x y := by
    apply Subtype.ext
    exact q8I.map_add x.1 y.1
  map_smul' c x := by
    apply Subtype.ext
    change q8I (c • x.1) = c • q8I x.1
    exact q8IEnd.map_smul c x.1

def q8JOnOdd : Module.End ℚ q8OddSubmodule where
  toFun := fun x => ⟨q8J x.1, by
    apply (mem_q8OddSubmodule_iff _).2
    have hx : q8C x.1 = -x.1 := (mem_q8OddSubmodule_iff _).1 x.2
    calc
      q8C (q8J x.1) = q8J (q8C x.1) := by
        change (q8C.comp q8J) x.1 = (q8J.comp q8C) x.1
        rw [q8C_comp_q8J]
      _ = q8J (-x.1) := by rw [hx]
      _ = -q8J x.1 := map_neg _ _⟩
  map_add' x y := by
    apply Subtype.ext
    exact q8J.map_add x.1 y.1
  map_smul' c x := by
    apply Subtype.ext
    change q8J (c • x.1) = c • q8J x.1
    exact q8JEnd.map_smul c x.1

theorem q8IOnOdd_sq : q8IOnOdd * q8IOnOdd = -1 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change q8I (q8I x.1) = -x.1
  calc
    q8I (q8I x.1) = q8C x.1 := by
      simpa only [RingHom.comp_apply] using
        congrArg (fun f : Q8TopField →+* Q8TopField => f x.1) q8I_sq_eq_q8C
    _ = -x.1 := (mem_q8OddSubmodule_iff _).1 x.2

theorem q8JOnOdd_sq : q8JOnOdd * q8JOnOdd = -1 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change q8J (q8J x.1) = -x.1
  calc
    q8J (q8J x.1) = q8C x.1 := by
      simpa only [RingHom.comp_apply] using
        congrArg (fun f : Q8TopField →+* Q8TopField => f x.1) q8J_sq_eq_q8C
    _ = -x.1 := (mem_q8OddSubmodule_iff _).1 x.2

theorem q8IOnOdd_mul_q8JOnOdd_eq_neg :
    q8IOnOdd * q8JOnOdd = -(q8JOnOdd * q8IOnOdd) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change q8I (q8J x.1) = -(q8J (q8I x.1))
  calc
    q8I (q8J x.1) = q8C (q8J (q8I x.1)) := by
      simpa only [RingHom.comp_apply] using
        congrArg (fun f : Q8TopField →+* Q8TopField => f x.1)
          q8I_comp_q8J_eq_q8C_comp_q8J_comp_q8I
    _ = -(q8J (q8I x.1)) := by
      exact (mem_q8OddSubmodule_iff _).1 (q8JOnOdd (q8IOnOdd x)).2

/-- A nontrivial concrete quaternionic `D = 1`, `N = 2` algebra on the odd central sector. -/
def q8OddD1N2 : SuperPoincare.D1N2 (Module.End ℚ q8OddSubmodule) where
  supercharge0 := q8IOnOdd
  supercharge1 := q8JOnOdd
  momentum := -1
  supercharge0_sq := q8IOnOdd_sq
  supercharge1_sq := q8JOnOdd_sq
  mixed_anticommutator := by
    calc
      q8IOnOdd * q8JOnOdd + q8JOnOdd * q8IOnOdd =
          -(q8JOnOdd * q8IOnOdd) + q8JOnOdd * q8IOnOdd :=
        congrArg (fun z : Module.End ℚ q8OddSubmodule => z + q8JOnOdd * q8IOnOdd)
          q8IOnOdd_mul_q8JOnOdd_eq_neg
      _ = 0 := by
        ext x
        simp

theorem q8TopRoot_mem_odd : deningerQ8RootNumberNegOneTopRoot ∈ q8OddSubmodule :=
  (mem_q8OddSubmodule_iff _).2 q8C_root

theorem q8OddSubmodule_nontrivial : Nontrivial q8OddSubmodule := by
  apply nontrivial_of_ne
    ⟨deningerQ8RootNumberNegOneTopRoot, q8TopRoot_mem_odd⟩ 0
  intro h
  exact q8TopRoot_ne_zero (Subtype.ext_iff.mp h)

end RHTower
