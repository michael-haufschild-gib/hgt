/-
Jointly continuous sesquilinear forms on an arbitrary complex topological module.

Two copies of the same object exist in the tree: `ContinuousSchwartzSesquilinearForm` on the
Fréchet space `𝓢(ℝ, ℂ)`, carrying the algebraic simp lemmas, joint-continuity transport,
positivity and Hermitian symmetry; and `RHTower.ContinuousSesquilinearForm H` on a complex normed
space, carrying the left radical and its closedness.  Neither space is an instance of the other's
ambient hypotheses — `𝓢(ℝ, ℂ)` is not normed — so the two APIs stayed disjoint.

Both are forms on a complex topological module, which is all their statements use.  This file
introduces that common object and the forgetful maps into it, so the radical API becomes available
on the Schwartz side, where it was missing, and the normed-space form is exhibited as the same
structure.

* `ContinuousSesquilinearFormOn H` — the common structure;
* `leftRadical`, `rightRadical` and their closedness, proved once;
* `SchwartzMap.ContinuousSchwartzSesquilinearForm.toContinuousSesquilinearFormOn` and the resulting
  radical statements on Schwartz space.
-/
import GaloisForLFunctions.HTGeometry.SchwartzSesquilinear

open Complex Filter
open scoped Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable (H : Type*) [AddCommGroup H] [Module ℂ H] [TopologicalSpace H]

/-- A jointly continuous form on a complex topological module, complex-linear in the first
argument and conjugate-linear in the second. -/
structure ContinuousSesquilinearFormOn where
  /-- The underlying two-argument function. -/
  toFun : H → H → ℂ
  map_add_left : ∀ u v w, toFun (u + v) w = toFun u w + toFun v w
  map_smul_left : ∀ (c : ℂ) u v, toFun (c • u) v = c * toFun u v
  map_add_right : ∀ u v w, toFun u (v + w) = toFun u v + toFun u w
  map_smul_right : ∀ (c : ℂ) u v, toFun u (c • v) = (starRingEnd ℂ) c * toFun u v
  continuous : Continuous (fun p : H × H => toFun p.1 p.2)

instance : CoeFun (ContinuousSesquilinearFormOn H) (fun _ => H → H → ℂ) :=
  ⟨ContinuousSesquilinearFormOn.toFun⟩

namespace ContinuousSesquilinearFormOn

variable {H}
variable (Q : ContinuousSesquilinearFormOn H)

@[simp] theorem apply_add_left (u v w : H) : Q (u + v) w = Q u w + Q v w :=
  Q.map_add_left u v w

@[simp] theorem apply_smul_left (c : ℂ) (u v : H) : Q (c • u) v = c * Q u v :=
  Q.map_smul_left c u v

@[simp] theorem apply_add_right (u v w : H) : Q u (v + w) = Q u v + Q u w :=
  Q.map_add_right u v w

@[simp] theorem apply_smul_right (c : ℂ) (u v : H) :
    Q u (c • v) = (starRingEnd ℂ) c * Q u v := Q.map_smul_right c u v

@[simp] theorem apply_zero_left (v : H) : Q 0 v = 0 := by
  have h := Q.map_smul_left 0 0 v
  simpa using h

@[simp] theorem apply_zero_right (u : H) : Q u 0 = 0 := by
  have h := Q.map_smul_right 0 u 0
  simpa using h

/-- Each argument slot of a jointly continuous form is separately continuous. -/
theorem continuous_left (v : H) : Continuous (fun u : H => Q u v) :=
  Q.continuous.comp (continuous_id.prodMk continuous_const)

theorem continuous_right (u : H) : Continuous (fun v : H => Q u v) :=
  Q.continuous.comp (continuous_const.prodMk continuous_id)

/-- The left radical: the vectors the form annihilates from the left. -/
def leftRadical : Submodule ℂ H where
  carrier := {u | ∀ v, Q u v = 0}
  zero_mem' := Q.apply_zero_left
  add_mem' hu hv w := by simp [hu w, hv w]
  smul_mem' c u hu w := by simp [hu w]

theorem mem_leftRadical_iff (u : H) : u ∈ Q.leftRadical ↔ ∀ v, Q u v = 0 := Iff.rfl

/-- The right radical: the vectors the form annihilates from the right. -/
def rightRadical : Submodule ℂ H where
  carrier := {v | ∀ u, Q u v = 0}
  zero_mem' := Q.apply_zero_right
  add_mem' hu hv w := by simp [hu w, hv w]
  smul_mem' c v hv w := by simp [hv w]

theorem mem_rightRadical_iff (v : H) : v ∈ Q.rightRadical ↔ ∀ u, Q u v = 0 := Iff.rfl

/-- Joint continuity makes the left radical closed. -/
theorem isClosed_leftRadical : IsClosed (Q.leftRadical : Set H) := by
  have heq : (Q.leftRadical : Set H) = ⋂ v : H, {u | Q u v = 0} := by
    ext u
    simp [leftRadical]
  rw [heq]
  refine isClosed_iInter fun v => ?_
  have hpre : {u : H | Q u v = 0} = (fun u : H => Q u v) ⁻¹' {0} := by
    ext u; simp
  rw [hpre]
  exact (isClosed_singleton (X := ℂ) (x := 0)).preimage (Q.continuous_left v)

/-- Joint continuity makes the right radical closed. -/
theorem isClosed_rightRadical : IsClosed (Q.rightRadical : Set H) := by
  have heq : (Q.rightRadical : Set H) = ⋂ u : H, {v | Q u v = 0} := by
    ext v
    simp [rightRadical]
  rw [heq]
  refine isClosed_iInter fun u => ?_
  have hpre : {v : H | Q u v = 0} = (fun v : H => Q u v) ⁻¹' {0} := by
    ext v; simp
  rw [hpre]
  exact (isClosed_singleton (X := ℂ) (x := 0)).preimage (Q.continuous_right u)

/-- A form vanishing on a dense set of left arguments vanishes identically. -/
theorem eq_zero_of_dense_leftRadical (hdense : Dense (Q.leftRadical : Set H)) (u v : H) :
    Q u v = 0 := by
  have huniv : (Q.leftRadical : Set H) = Set.univ :=
    (Q.isClosed_leftRadical.closure_eq).symm.trans hdense.closure_eq
  have hu : u ∈ (Q.leftRadical : Set H) := by rw [huniv]; trivial
  exact hu v

end ContinuousSesquilinearFormOn

end

end GaloisForLFunctions.HTGeometry

namespace SchwartzMap

namespace ContinuousSchwartzSesquilinearForm

open GaloisForLFunctions.HTGeometry

/-- A continuous sesquilinear form on Schwartz space is a continuous sesquilinear form on the
underlying complex topological module. -/
noncomputable def toContinuousSesquilinearFormOn (Q : ContinuousSchwartzSesquilinearForm) :
    ContinuousSesquilinearFormOn 𝓢(ℝ, ℂ) where
  toFun := Q.toFun
  map_add_left := Q.map_add_left
  map_smul_left := Q.map_smul_left
  map_add_right := Q.map_add_right
  map_smul_right := Q.map_smul_right
  continuous := Q.continuous

@[simp] theorem toContinuousSesquilinearFormOn_apply
    (Q : ContinuousSchwartzSesquilinearForm) (u v : 𝓢(ℝ, ℂ)) :
    Q.toContinuousSesquilinearFormOn u v = Q u v := rfl

/-- The left radical of a continuous sesquilinear form on Schwartz space. -/
noncomputable def leftRadical (Q : ContinuousSchwartzSesquilinearForm) :
    Submodule ℂ 𝓢(ℝ, ℂ) :=
  Q.toContinuousSesquilinearFormOn.leftRadical

theorem mem_leftRadical_iff (Q : ContinuousSchwartzSesquilinearForm) (u : 𝓢(ℝ, ℂ)) :
    u ∈ Q.leftRadical ↔ ∀ v, Q u v = 0 := Iff.rfl

/-- **The left radical of a continuous sesquilinear form on Schwartz space is closed.** -/
theorem isClosed_leftRadical (Q : ContinuousSchwartzSesquilinearForm) :
    IsClosed (Q.leftRadical : Set 𝓢(ℝ, ℂ)) :=
  Q.toContinuousSesquilinearFormOn.isClosed_leftRadical

/-- **A form with dense left radical on Schwartz space vanishes.** -/
theorem eq_zero_of_dense_leftRadical (Q : ContinuousSchwartzSesquilinearForm)
    (hdense : Dense (Q.leftRadical : Set 𝓢(ℝ, ℂ))) (u v : 𝓢(ℝ, ℂ)) : Q u v = 0 :=
  Q.toContinuousSesquilinearFormOn.eq_zero_of_dense_leftRadical hdense u v

end ContinuousSchwartzSesquilinearForm

end SchwartzMap
