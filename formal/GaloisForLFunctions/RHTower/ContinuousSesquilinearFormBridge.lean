/-
The normed-space sesquilinear form is the general topological-module one.

`ContinuousSesquilinearForm H`, defined for a complex normed space, and
`ContinuousSesquilinearFormOn H`, defined for a complex topological module, have the same fields.
The normed hypotheses are never used by the radical statements, so the normed form maps forgetfully
into the general one and its left radical is the general left radical.  The right radical and the
density collapse, proved once on the general side, transfer along the same map.
-/
import GaloisForLFunctions.RHTower.XiThetaL2MetricSingularity
import GaloisForLFunctions.HTGeometry.ContinuousSesquilinearFormGeneral

namespace RHTower

namespace ContinuousSesquilinearForm

open GaloisForLFunctions.HTGeometry

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- The forgetful map to the general topological-module form. -/
noncomputable def toContinuousSesquilinearFormOn (Q : ContinuousSesquilinearForm H) :
    ContinuousSesquilinearFormOn H where
  toFun := Q.toFun
  map_add_left := Q.map_add_left
  map_smul_left := Q.map_smul_left
  map_add_right := Q.map_add_right
  map_smul_right := Q.map_smul_right
  continuous := Q.continuous

@[simp] theorem toContinuousSesquilinearFormOn_apply
    (Q : ContinuousSesquilinearForm H) (u v : H) :
    Q.toContinuousSesquilinearFormOn u v = Q u v := rfl

/-- **The two left radicals agree.**  The normed-space radical is the general one. -/
theorem leftRadical_toContinuousSesquilinearFormOn (Q : ContinuousSesquilinearForm H) :
    Q.toContinuousSesquilinearFormOn.leftRadical = Q.leftRadical := rfl

/-- The right radical of a continuous sesquilinear form on a normed space. -/
noncomputable def rightRadical (Q : ContinuousSesquilinearForm H) : Submodule ℂ H :=
  Q.toContinuousSesquilinearFormOn.rightRadical

theorem mem_rightRadical_iff (Q : ContinuousSesquilinearForm H) (v : H) :
    v ∈ Q.rightRadical ↔ ∀ u, Q u v = 0 := Iff.rfl

/-- **The right radical is closed**, by the same joint-continuity argument as the left one. -/
theorem isClosed_rightRadical (Q : ContinuousSesquilinearForm H) :
    IsClosed (Q.rightRadical : Set H) :=
  Q.toContinuousSesquilinearFormOn.isClosed_rightRadical

/-- **A dense left radical forces the form to vanish.** -/
theorem eq_zero_of_dense_leftRadical (Q : ContinuousSesquilinearForm H)
    (hdense : Dense (Q.leftRadical : Set H)) (u v : H) : Q u v = 0 :=
  Q.toContinuousSesquilinearFormOn.eq_zero_of_dense_leftRadical
    (by rw [leftRadical_toContinuousSesquilinearFormOn]; exact hdense) u v

end ContinuousSesquilinearForm

end RHTower
