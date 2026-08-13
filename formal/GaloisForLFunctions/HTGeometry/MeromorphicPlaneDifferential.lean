import GaloisForLFunctions.HTGeometry.MeromorphicPlaneField
import Mathlib.RingTheory.Derivation.DifferentialRing
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# The meromorphic plane field is a differential field over the constants

Complex differentiation descends to germs along the codiscrete filter, because a codiscrete set is
open, and the Leibniz rule holds there because two meromorphic functions are simultaneously analytic
on a codiscrete set.  This equips the field of meromorphic functions on `ℂ` with its derivation and
with the algebra structure of the constants, whose derivative vanishes.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- Differentiation of germs along the codiscrete filter. -/
noncomputable def planeGermDeriv : Germ planeCodiscrete ℂ → Germ planeCodiscrete ℂ :=
  Germ.map' deriv (by
    intro f g hfg
    have hopen : IsOpen {z : ℂ | f z = g z} := isOpen_of_mem_planeCodiscrete hfg
    have heq : Set.EqOn (deriv f) (deriv g) {z : ℂ | f z = g z} :=
      Set.EqOn.deriv (fun z hz => hz) hopen
    exact hfg.mono fun z hz => heq hz)

@[simp] theorem planeGermDeriv_coe (f : ℂ → ℂ) :
    planeGermDeriv (f : Germ planeCodiscrete ℂ) = ((deriv f : ℂ → ℂ) : Germ planeCodiscrete ℂ) :=
  rfl

theorem planeGermDeriv_mem {g : Germ planeCodiscrete ℂ} (hg : g ∈ meromorphicPlaneSubring) :
    planeGermDeriv g ∈ meromorphicPlaneSubring := by
  obtain ⟨f, hf, rfl⟩ := hg
  exact ⟨deriv f, fun z => (hf z).deriv, rfl⟩

/-- Differentiation on the field of meromorphic functions on the plane. -/
noncomputable def meromorphicPlaneDeriv (x : MeromorphicPlane) : MeromorphicPlane :=
  show MeromorphicPlane from
    ⟨planeGermDeriv x.germ, planeGermDeriv_mem (show (meromorphicPlaneSubring : Type) from x).2⟩

@[simp] theorem germ_meromorphicPlaneDeriv (x : MeromorphicPlane) :
    (meromorphicPlaneDeriv x).germ = planeGermDeriv x.germ := rfl

theorem meromorphicPlaneDeriv_ofMeromorphic (f : ℂ → ℂ) (hf : ∀ z, MeromorphicAt f z) :
    meromorphicPlaneDeriv (ofMeromorphic f hf)
      = ofMeromorphic (deriv f) (fun z => (hf z).deriv) := by
  refine MeromorphicPlane.germ_injective ?_
  rw [germ_meromorphicPlaneDeriv, germ_ofMeromorphic, germ_ofMeromorphic, planeGermDeriv_coe]

theorem meromorphicPlaneDeriv_zero : meromorphicPlaneDeriv 0 = 0 := by
  refine MeromorphicPlane.germ_injective ?_
  rw [germ_meromorphicPlaneDeriv, germ_zero, planeGermDeriv_coe]
  simp

theorem meromorphicPlaneDeriv_add (x y : MeromorphicPlane) :
    meromorphicPlaneDeriv (x + y) = meromorphicPlaneDeriv x + meromorphicPlaneDeriv y := by
  obtain ⟨f, hf, hx⟩ := x.exists_rep
  obtain ⟨g, hg, hy⟩ := y.exists_rep
  subst hx
  subst hy
  rw [ofMeromorphic_add, meromorphicPlaneDeriv_ofMeromorphic, meromorphicPlaneDeriv_ofMeromorphic,
    meromorphicPlaneDeriv_ofMeromorphic, ofMeromorphic_add]
  refine MeromorphicPlane.germ_injective ?_
  rw [germ_ofMeromorphic, germ_ofMeromorphic]
  have hmerf : MeromorphicOn f Set.univ := fun z _ => hf z
  have hmerg : MeromorphicOn g Set.univ := fun z _ => hg z
  have hset : {z : ℂ | AnalyticAt ℂ f z} ∩ {z : ℂ | AnalyticAt ℂ g z} ∈ planeCodiscrete :=
    Filter.inter_mem hmerf.analyticAt_mem_codiscreteWithin hmerg.analyticAt_mem_codiscreteWithin
  have hev : deriv (f + g) =ᶠ[planeCodiscrete] deriv f + deriv g := by
    filter_upwards [hset] with z hz
    exact deriv_add hz.1.differentiableAt hz.2.differentiableAt
  exact Germ.coe_eq.mpr hev

theorem meromorphicPlaneDeriv_mul (x y : MeromorphicPlane) :
    meromorphicPlaneDeriv (x * y)
      = x * meromorphicPlaneDeriv y + y * meromorphicPlaneDeriv x := by
  obtain ⟨f, hf, hx⟩ := x.exists_rep
  obtain ⟨g, hg, hy⟩ := y.exists_rep
  subst hx
  subst hy
  rw [ofMeromorphic_mul, meromorphicPlaneDeriv_ofMeromorphic, meromorphicPlaneDeriv_ofMeromorphic,
    meromorphicPlaneDeriv_ofMeromorphic, ofMeromorphic_mul, ofMeromorphic_mul, ofMeromorphic_add]
  refine MeromorphicPlane.germ_injective ?_
  rw [germ_ofMeromorphic, germ_ofMeromorphic]
  have hmerf : MeromorphicOn f Set.univ := fun z _ => hf z
  have hmerg : MeromorphicOn g Set.univ := fun z _ => hg z
  have hset : {z : ℂ | AnalyticAt ℂ f z} ∩ {z : ℂ | AnalyticAt ℂ g z} ∈ planeCodiscrete :=
    Filter.inter_mem hmerf.analyticAt_mem_codiscreteWithin hmerg.analyticAt_mem_codiscreteWithin
  have hev : deriv (f * g) =ᶠ[planeCodiscrete] f * deriv g + g * deriv f := by
    filter_upwards [hset] with z hz
    rw [deriv_mul hz.1.differentiableAt hz.2.differentiableAt]
    simp only [Pi.add_apply, Pi.mul_apply]
    ring
  exact Germ.coe_eq.mpr hev

/-- The derivation of the meromorphic plane field. -/
noncomputable def meromorphicPlaneDerivation :
    Derivation ℤ MeromorphicPlane MeromorphicPlane := by
  let D : MeromorphicPlane →+ MeromorphicPlane :=
    { toFun := meromorphicPlaneDeriv
      map_zero' := meromorphicPlaneDeriv_zero
      map_add' := meromorphicPlaneDeriv_add }
  exact Derivation.mk' D.toIntLinearMap meromorphicPlaneDeriv_mul

noncomputable instance : Differential MeromorphicPlane := ⟨meromorphicPlaneDerivation⟩

@[simp] theorem meromorphicPlane_deriv_eq (x : MeromorphicPlane) :
    Differential.deriv x = meromorphicPlaneDeriv x := rfl

end GaloisForLFunctions.HTGeometry
