import Mathlib.Topology.Algebra.Module.Basic

/-!
# Pure suspension scalar-spectrum no-go

A strongly continuous orbit determined by a scalar orbit on a dense subgroup
is scalar everywhere.  Hence a scalar infinitesimal generator has no
eigenvalue other than its scalar weight.

This is the unconditional formal core of
`DAC_PURE_SUSPENSION_SCALAR_SPECTRUM_NO_GO`.
-/

open Set

namespace GaloisForLFunctions.RHTower

/-- Two continuous flows that agree on a dense set of times agree at every
time.  Applied to `log ℚ₊`, this is the rigidity step in the pure-suspension
no-go theorem. -/
theorem deningerPureSuspension_orbit_eq_of_dense
    {V : Type*} [TopologicalSpace V] [T2Space V]
    (orbit scalarOrbit : ℝ → V)
    (horbit : Continuous orbit)
    (hscalar : Continuous scalarOrbit)
    (times : Set ℝ)
    (htimes : Dense times)
    (heq : Set.EqOn orbit scalarOrbit times) :
    orbit = scalarOrbit :=
  Continuous.ext_on htimes horbit hscalar heq

/-- Vectorwise dense-time agreement forces equality of the full flow with
the prescribed scalar flow. -/
theorem deningerPureSuspension_flow_eq_of_dense
    {V : Type*} [TopologicalSpace V] [T2Space V]
    (flow scalarFlow : ℝ → V → V)
    (hflow : ∀ v, Continuous fun t => flow t v)
    (hscalar : ∀ v, Continuous fun t => scalarFlow t v)
    (times : Set ℝ)
    (htimes : Dense times)
    (heq : ∀ v, Set.EqOn (fun t => flow t v) (fun t => scalarFlow t v) times) :
    flow = scalarFlow := by
  funext t v
  exact congrFun
    (deningerPureSuspension_orbit_eq_of_dense
      (fun s => flow s v) (fun s => scalarFlow s v)
      (hflow v) (hscalar v) times htimes (heq v)) t

/-- A scalar complex-linear generator has only its scalar weight as a point
eigenvalue. -/
theorem deningerPureSuspension_eigenvalue_eq_weight
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (theta : V →ₗ[ℂ] V) (weight eigenvalue : ℂ)
    (htheta : ∀ x, theta x = weight • x)
    {x : V} (hx : x ≠ 0)
    (heigen : theta x = eigenvalue • x) :
    eigenvalue = weight := by
  have hsmul : (weight - eigenvalue) • x = 0 := by
    rw [sub_smul, ← htheta x, heigen, sub_self]
  have hweight : weight - eigenvalue = 0 :=
    (smul_eq_zero.mp hsmul).resolve_right hx
  exact (sub_eq_zero.mp hweight).symm

end GaloisForLFunctions.RHTower
