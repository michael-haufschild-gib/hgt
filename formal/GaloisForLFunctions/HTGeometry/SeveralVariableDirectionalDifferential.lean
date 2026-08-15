import GaloisForLFunctions.Bottcher.ProductCover
import GaloisForLFunctions.HTGeometry.FractionRingDerivation
import Mathlib.RingTheory.Derivation.DifferentialRing

/-!
# The directional derivation on several-variable meromorphic germs

A constant direction `w` gives the derivation `f ↦ (z ↦ fderiv ℂ f z w)`.  It descends to germs along
an open set, preserves analytic germs — the derivative of an analytic map is analytic and evaluation
at `w` is continuous linear — and satisfies the Leibniz rule, so it extends by the quotient rule to
the several-variable meromorphic fraction field.

This is the differential-field carrier that a directional differential-matroid statement on `ℂ^d`
needs.
-/

open Filter Topology Set Function
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open Bottcher

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The directional derivative of a scalar function along a constant direction. -/
def dirDerivFun (w : E) (f : E → ℂ) : E → ℂ := fun z => fderiv ℂ f z w

/-- **The directional derivative descends to germs along an open set.** -/
theorem dirDerivFun_congr (w : E) {U : Set E} (hUo : IsOpen U) {f g : E → ℂ}
    (hfg : Set.EqOn f g U) : Set.EqOn (dirDerivFun w f) (dirDerivFun w g) U := by
  intro z hz
  have heq : f =ᶠ[nhds z] g := Filter.eventuallyEq_of_mem (hUo.mem_nhds hz) hfg
  rw [dirDerivFun, dirDerivFun, heq.fderiv_eq]

/-- The directional derivative of an analytic function is analytic. -/
theorem analyticOnNhd_dirDerivFun (w : E) {U : Set E} {f : E → ℂ}
    (hf : AnalyticOnNhd ℂ f U) : AnalyticOnNhd ℂ (dirDerivFun w f) U := by
  have happ : AnalyticOnNhd ℂ (fun L : E →L[ℂ] ℂ => L w) Set.univ := by
    intro L _
    exact ((ContinuousLinearMap.apply ℂ ℂ w).analyticAt L)
  exact (happ.comp hf.fderiv fun z _ => Set.mem_univ _)

/-- Differentiation along `w` on germs. -/
def svDirGermDeriv (w : E) {U : Set E} (hUo : IsOpen U) :
    Germ (𝓟 U) ℂ → Germ (𝓟 U) ℂ :=
  Germ.map' (dirDerivFun w) (by
    intro f g hfg
    exact eventually_principal.mpr
      (dirDerivFun_congr w hUo (eventually_principal.mp hfg)))

@[simp] theorem svDirGermDeriv_coe (w : E) {U : Set E} (hUo : IsOpen U) (f : E → ℂ) :
    svDirGermDeriv w hUo (f : Germ (𝓟 U) ℂ) = (dirDerivFun w f : Germ (𝓟 U) ℂ) := rfl

/-- Differentiation along `w` on analytic germs. -/
def analyticSubringGenDirDeriv (w : E) {U : Set E} (hUo : IsOpen U)
    (a : analyticSubringGen U) : analyticSubringGen U := by
  refine ⟨svDirGermDeriv w hUo a.1, ?_⟩
  obtain ⟨f, hf, hfa⟩ := a.2
  refine ⟨dirDerivFun w f, analyticOnNhd_dirDerivFun w hf, ?_⟩
  rw [← hfa]
  rfl

@[simp] theorem analyticSubringGenDirDeriv_coe (w : E) {U : Set E} (hUo : IsOpen U)
    (a : analyticSubringGen U) :
    (analyticSubringGenDirDeriv w hUo a : Germ (𝓟 U) ℂ) =
      svDirGermDeriv w hUo (a : Germ (𝓟 U) ℂ) := rfl

theorem analyticSubringGenDirDeriv_zero (w : E) {U : Set E} (hUo : IsOpen U) :
    analyticSubringGenDirDeriv w hUo (0 : analyticSubringGen U) = 0 := by
  apply Subtype.ext
  rw [analyticSubringGenDirDeriv_coe]
  change (dirDerivFun w (0 : E → ℂ) : Germ (𝓟 U) ℂ) = 0
  have hzero : dirDerivFun w (0 : E → ℂ) = 0 := by
    funext z
    rw [dirDerivFun]
    simp
  rw [hzero]
  simp

theorem analyticSubringGenDirDeriv_add (w : E) {U : Set E} (hUo : IsOpen U)
    (a b : analyticSubringGen U) :
    analyticSubringGenDirDeriv w hUo (a + b) =
      analyticSubringGenDirDeriv w hUo a + analyticSubringGenDirDeriv w hUo b := by
  obtain ⟨f, hf, hfa⟩ := a.2
  obtain ⟨g, hg, hgb⟩ := b.2
  apply Subtype.ext
  change svDirGermDeriv w hUo ((a : Germ (𝓟 U) ℂ) + b) =
    svDirGermDeriv w hUo a + svDirGermDeriv w hUo b
  rw [← hfa, ← hgb]
  change svDirGermDeriv w hUo (↑(f + g) : Germ (𝓟 U) ℂ) =
    svDirGermDeriv w hUo (↑f : Germ (𝓟 U) ℂ) + svDirGermDeriv w hUo (↑g : Germ (𝓟 U) ℂ)
  rw [svDirGermDeriv_coe, svDirGermDeriv_coe, svDirGermDeriv_coe, ← Germ.coe_add, Germ.coe_eq]
  refine eventually_principal.mpr fun z hz => ?_
  show fderiv ℂ (f + g) z w = fderiv ℂ f z w + fderiv ℂ g z w
  rw [fderiv_add ((hf z hz).differentiableAt) ((hg z hz).differentiableAt)]
  rfl

theorem analyticSubringGenDirDeriv_mul (w : E) {U : Set E} (hUo : IsOpen U)
    (a b : analyticSubringGen U) :
    analyticSubringGenDirDeriv w hUo (a * b) =
      a * analyticSubringGenDirDeriv w hUo b + b * analyticSubringGenDirDeriv w hUo a := by
  obtain ⟨f, hf, hfa⟩ := a.2
  obtain ⟨g, hg, hgb⟩ := b.2
  apply Subtype.ext
  change svDirGermDeriv w hUo ((a : Germ (𝓟 U) ℂ) * b) =
    (a : Germ (𝓟 U) ℂ) * svDirGermDeriv w hUo b + (b : Germ (𝓟 U) ℂ) * svDirGermDeriv w hUo a
  rw [← hfa, ← hgb]
  change svDirGermDeriv w hUo (↑(f * g) : Germ (𝓟 U) ℂ) =
    (↑f : Germ (𝓟 U) ℂ) * svDirGermDeriv w hUo (↑g : Germ (𝓟 U) ℂ) +
      (↑g : Germ (𝓟 U) ℂ) * svDirGermDeriv w hUo (↑f : Germ (𝓟 U) ℂ)
  rw [svDirGermDeriv_coe, svDirGermDeriv_coe, svDirGermDeriv_coe, ← Germ.coe_mul, ← Germ.coe_mul,
    ← Germ.coe_add, Germ.coe_eq]
  refine eventually_principal.mpr fun z hz => ?_
  show fderiv ℂ (f * g) z w = f z * fderiv ℂ g z w + g z * fderiv ℂ f z w
  rw [fderiv_mul ((hf z hz).differentiableAt) ((hg z hz).differentiableAt)]
  simp

/-- The directional derivative as an integer-linear derivation on the analytic-germ domain. -/
def analyticSubringGenDirDerivation (w : E) {U : Set E} (hUo : IsOpen U) :
    Derivation ℤ (analyticSubringGen U) (analyticSubringGen U) := by
  let D : analyticSubringGen U →+ analyticSubringGen U :=
    { toFun := analyticSubringGenDirDeriv w hUo
      map_zero' := analyticSubringGenDirDeriv_zero w hUo
      map_add' := analyticSubringGenDirDeriv_add w hUo }
  exact Derivation.mk' D.toIntLinearMap (analyticSubringGenDirDeriv_mul w hUo)

/-- **Differential-field structure on the several-variable meromorphic fraction field, for a constant
direction.** -/
@[reducible] def meroFieldGenDirDifferential (w : E) {U : Set E}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) :
    Differential (meroFieldGen U) := by
  letI := Bottcher.isDomain_analyticSubringGen U hUo hUc hUne
  letI : Algebra ℤ (analyticSubringGen U) := Ring.toIntAlgebra _
  letI : Algebra ℤ (meroFieldGen U) := Ring.toIntAlgebra _
  exact ⟨fractionRingDerivation (K := ℤ)
    ((Algebra.linearMap (analyticSubringGen U) (meroFieldGen U)).compDer
      (analyticSubringGenDirDerivation w hUo))⟩

theorem meroFieldGenDirDifferential_algebraMap (w : E) {U : Set E}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (a : analyticSubringGen U) :
    letI := Bottcher.isDomain_analyticSubringGen U hUo hUc hUne
    letI := meroFieldGenDirDifferential w hUo hUc hUne
    (algebraMap (analyticSubringGen U) (meroFieldGen U) a)′ =
      algebraMap (analyticSubringGen U) (meroFieldGen U)
        (analyticSubringGenDirDeriv w hUo a) := by
  letI := Bottcher.isDomain_analyticSubringGen U hUo hUc hUne
  letI : Algebra ℤ (analyticSubringGen U) := Ring.toIntAlgebra _
  letI : Algebra ℤ (meroFieldGen U) := Ring.toIntAlgebra _
  letI := meroFieldGenDirDifferential w hUo hUc hUne
  change fractionRingDerivation _ (algebraMap (analyticSubringGen U) (meroFieldGen U) a) = _
  rw [fractionRingDerivation_algebraMap]
  rfl

end

end GaloisForLFunctions.HTGeometry
