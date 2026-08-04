import GaloisForLFunctions.HTGeometry.FractionRingDerivation
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Order.Filter.Germ.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Derivation.DifferentialRing

/-!
# The meromorphic differential field of a directional derivative

The corpus carries the meromorphic function field of an open subset of `ℂ` with its ordinary
derivative.  A product domain such as `E × ℂ*` needs the same object one dimension up, and with a
*chosen direction*: the differential structure that a capacity statement uses is differentiation
along one factor only, so that the functions of the other factor are differential constants.

This file builds that object for an arbitrary complex normed space and an arbitrary direction
vector.  Nothing is specific to two variables:

* `analyticGermSubringOn U` — the analytic germs along an open set, an integral domain when `U` is
  connected and nonempty (the identity theorem, valid in any normed space);
* `dirFderiv v` — the directional derivative, again analytic (`AnalyticOnNhd.fderiv` composed with
  evaluation at `v`), and well defined on germs along an open set;
* `dirMeroField U` — the meromorphic fraction field, with its `Differential` instance obtained by
  extending the germ derivation by the quotient rule;
* the constants: a function that is constant along `v` — in particular a function of the other
  factor of a product — has vanishing directional derivative.

With `E = ℂ × ℂ` and `v = (0, 1)` this is exactly the differential field of a product domain in which
the first-factor functions are constants.
-/

open Filter Topology Set Function
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-! ### Analytic germs on an open set -/

/-- The analytic germs along an open set of a complex normed space. -/
def analyticGermSubringOn (U : Set E) : Subring (Germ (𝓟 U) ℂ) where
  carrier := {g | ∃ f : E → ℂ, AnalyticOnNhd ℂ f U ∧ (Germ.coeRingHom (𝓟 U) f) = g}
  mul_mem' := by rintro a b ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩; exact ⟨f * g, hf.mul hg, by rw [map_mul]⟩
  one_mem' := ⟨1, analyticOnNhd_const, map_one _⟩
  add_mem' := by rintro a b ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩; exact ⟨f + g, hf.add hg, by rw [map_add]⟩
  zero_mem' := ⟨0, analyticOnNhd_const, map_zero _⟩
  neg_mem' := by rintro a ⟨f, hf, rfl⟩; exact ⟨-f, hf.neg, by rw [map_neg]⟩

/-- **The identity theorem as a domain statement.**  If a product of two functions analytic on a
connected open set vanishes there, one factor vanishes identically. -/
theorem analyticOnNhd_domain' {U : Set E} {f g : E → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (hU : IsPreconnected U) (hUo : IsOpen U) (hfg : EqOn (fun z => f z * g z) 0 U) :
    EqOn f 0 U ∨ EqOn g 0 U := by
  by_cases h : EqOn f 0 U
  · exact Or.inl h
  right
  simp only [EqOn, not_forall] at h
  obtain ⟨z₀, hz₀U, hz₀⟩ := h
  have hz₀ne : f z₀ ≠ 0 := fun hc => hz₀ (by simp [hc])
  have hcont : ContinuousAt f z₀ := (hf z₀ hz₀U).continuousAt
  have hg0 : g =ᶠ[𝓝 z₀] 0 := by
    filter_upwards [hcont.eventually_ne hz₀ne, hUo.mem_nhds hz₀U] with z hzne hzU
    have := hfg hzU
    simp only [Pi.zero_apply] at this
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd h1 hzne
    · simpa using h1
  exact AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero hg hU hz₀U hg0

/-- **The analytic germs on a connected open set form an integral domain.** -/
theorem isDomain_analyticGermSubringOn (U : Set E) (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) : IsDomain (analyticGermSubringOn U) := by
  haveI hnb : (𝓟 U).NeBot := principal_neBot_iff.mpr hUne
  haveI hnt : Nontrivial (analyticGermSubringOn U) := by
    refine ⟨0, 1, ?_⟩
    intro h
    have hv := congrArg Subtype.val h
    rw [ZeroMemClass.coe_zero, OneMemClass.coe_one] at hv
    exact zero_ne_one hv
  haveI hnzd : NoZeroDivisors (analyticGermSubringOn U) := by
    refine ⟨fun {a b} hab => ?_⟩
    obtain ⟨f, hf, hfa⟩ := a.2
    obtain ⟨g, hg, hgb⟩ := b.2
    have hval : (a : Germ (𝓟 U) ℂ) * (b : Germ (𝓟 U) ℂ) = 0 := by
      have h2 := congrArg Subtype.val hab
      rwa [MulMemClass.coe_mul, ZeroMemClass.coe_zero] at h2
    have hfa' : (a : Germ (𝓟 U) ℂ) = (↑f : Germ (𝓟 U) ℂ) := hfa.symm
    have hgb' : (b : Germ (𝓟 U) ℂ) = (↑g : Germ (𝓟 U) ℂ) := hgb.symm
    rw [hfa', hgb', ← Germ.coe_mul, ← Germ.coe_zero, Germ.coe_eq] at hval
    have heq : EqOn (fun x => f x * g x) 0 U := fun x hx => eventually_principal.mp hval x hx
    rcases analyticOnNhd_domain' hf hg hUc hUo heq with h0 | h0
    · left
      apply Subtype.ext
      rw [ZeroMemClass.coe_zero, hfa', ← Germ.coe_zero, Germ.coe_eq]
      exact eventually_principal.mpr h0
    · right
      apply Subtype.ext
      rw [ZeroMemClass.coe_zero, hgb', ← Germ.coe_zero, Germ.coe_eq]
      exact eventually_principal.mpr h0
  exact NoZeroDivisors.to_isDomain _

/-! ### The directional derivative -/

/-- The derivative of a scalar function along a fixed direction. -/
def dirFderiv (v : E) (f : E → ℂ) : E → ℂ := fun x => fderiv ℂ f x v

theorem dirFderiv_apply (v : E) (f : E → ℂ) (x : E) : dirFderiv v f x = fderiv ℂ f x v := rfl

/-- **The directional derivative of an analytic function is analytic.** -/
theorem analyticOnNhd_dirFderiv {U : Set E} {f : E → ℂ} (hf : AnalyticOnNhd ℂ f U) (v : E) :
    AnalyticOnNhd ℂ (dirFderiv v f) U := by
  have hL : AnalyticOnNhd ℂ (⇑(ContinuousLinearMap.apply ℂ ℂ v)) (Set.univ : Set (E →L[ℂ] ℂ)) :=
    (ContinuousLinearMap.apply ℂ ℂ v).analyticOnNhd _
  have hcomp := hL.comp hf.fderiv (Set.mapsTo_univ _ _)
  exact hcomp

/-- The directional derivative only depends on the germ along an open set. -/
theorem dirFderiv_congr {U : Set E} (hUo : IsOpen U) (v : E) {f g : E → ℂ} (h : EqOn f g U) :
    EqOn (dirFderiv v f) (dirFderiv v g) U := by
  intro x hx
  have hev : f =ᶠ[𝓝 x] g := Filter.eventuallyEq_of_mem (hUo.mem_nhds hx) h
  rw [dirFderiv_apply, dirFderiv_apply, hev.fderiv_eq]

/-- The directional derivative on germs along an open set. -/
def dirGermDeriv {U : Set E} (hUo : IsOpen U) (v : E) : Germ (𝓟 U) ℂ → Germ (𝓟 U) ℂ :=
  Germ.map' (dirFderiv v) (by
    intro f g hfg
    exact eventually_principal.mpr
      (dirFderiv_congr hUo v (eventually_principal.mp hfg)))

@[simp] theorem dirGermDeriv_coe {U : Set E} (hUo : IsOpen U) (v : E) (f : E → ℂ) :
    dirGermDeriv hUo v (f : Germ (𝓟 U) ℂ) = (dirFderiv v f : Germ (𝓟 U) ℂ) := rfl

/-- The directional derivative of an analytic germ, again an analytic germ. -/
def dirSubringDeriv {U : Set E} (hUo : IsOpen U) (v : E)
    (a : analyticGermSubringOn U) : analyticGermSubringOn U := by
  refine ⟨dirGermDeriv hUo v a.1, ?_⟩
  obtain ⟨f, hf, hfa⟩ := a.2
  refine ⟨dirFderiv v f, analyticOnNhd_dirFderiv hf v, ?_⟩
  rw [← hfa]
  rfl

@[simp] theorem dirSubringDeriv_coe {U : Set E} (hUo : IsOpen U) (v : E)
    (a : analyticGermSubringOn U) :
    (dirSubringDeriv hUo v a : Germ (𝓟 U) ℂ) = dirGermDeriv hUo v (a : Germ (𝓟 U) ℂ) := rfl

theorem dirSubringDeriv_zero {U : Set E} (hUo : IsOpen U) (v : E) :
    dirSubringDeriv hUo v (0 : analyticGermSubringOn U) = 0 := by
  apply Subtype.ext
  rw [dirSubringDeriv_coe]
  change (dirFderiv v (0 : E → ℂ) : Germ (𝓟 U) ℂ) = 0
  have : dirFderiv v (0 : E → ℂ) = 0 := by
    funext x
    rw [dirFderiv_apply]
    simp
  rw [this]
  rfl

theorem dirSubringDeriv_add {U : Set E} (hUo : IsOpen U) (v : E)
    (a b : analyticGermSubringOn U) :
    dirSubringDeriv hUo v (a + b) = dirSubringDeriv hUo v a + dirSubringDeriv hUo v b := by
  obtain ⟨f, hf, hfa⟩ := a.2
  obtain ⟨g, hg, hgb⟩ := b.2
  apply Subtype.ext
  change dirGermDeriv hUo v ((a : Germ (𝓟 U) ℂ) + b)
    = dirGermDeriv hUo v (a : Germ (𝓟 U) ℂ) + dirGermDeriv hUo v (b : Germ (𝓟 U) ℂ)
  rw [← hfa, ← hgb]
  change dirGermDeriv hUo v (↑(f + g) : Germ (𝓟 U) ℂ)
    = dirGermDeriv hUo v (↑f : Germ (𝓟 U) ℂ) + dirGermDeriv hUo v (↑g : Germ (𝓟 U) ℂ)
  rw [dirGermDeriv_coe, dirGermDeriv_coe, dirGermDeriv_coe, ← Germ.coe_add, Germ.coe_eq]
  refine eventually_principal.mpr fun x hx => ?_
  simp only [dirFderiv, Pi.add_apply]
  rw [fderiv_add (hf x hx).differentiableAt (hg x hx).differentiableAt]
  simp

theorem dirSubringDeriv_mul {U : Set E} (hUo : IsOpen U) (v : E)
    (a b : analyticGermSubringOn U) :
    dirSubringDeriv hUo v (a * b)
      = a * dirSubringDeriv hUo v b + b * dirSubringDeriv hUo v a := by
  obtain ⟨f, hf, hfa⟩ := a.2
  obtain ⟨g, hg, hgb⟩ := b.2
  apply Subtype.ext
  change dirGermDeriv hUo v ((a : Germ (𝓟 U) ℂ) * b)
    = (a : Germ (𝓟 U) ℂ) * dirGermDeriv hUo v (b : Germ (𝓟 U) ℂ)
      + (b : Germ (𝓟 U) ℂ) * dirGermDeriv hUo v (a : Germ (𝓟 U) ℂ)
  rw [← hfa, ← hgb]
  change dirGermDeriv hUo v (↑(f * g) : Germ (𝓟 U) ℂ)
    = (↑f : Germ (𝓟 U) ℂ) * dirGermDeriv hUo v (↑g : Germ (𝓟 U) ℂ)
      + (↑g : Germ (𝓟 U) ℂ) * dirGermDeriv hUo v (↑f : Germ (𝓟 U) ℂ)
  rw [dirGermDeriv_coe, dirGermDeriv_coe, dirGermDeriv_coe, ← Germ.coe_mul, ← Germ.coe_mul,
    ← Germ.coe_add, Germ.coe_eq]
  refine eventually_principal.mpr fun x hx => ?_
  simp only [dirFderiv, Pi.add_apply, Pi.mul_apply]
  rw [fderiv_mul (hf x hx).differentiableAt (hg x hx).differentiableAt]
  simp

/-- The directional derivative as an integer-linear derivation of the analytic germ domain. -/
def dirSubringDerivation {U : Set E} (hUo : IsOpen U) (v : E) :
    Derivation ℤ (analyticGermSubringOn U) (analyticGermSubringOn U) := by
  let D : analyticGermSubringOn U →+ analyticGermSubringOn U :=
    { toFun := dirSubringDeriv hUo v
      map_zero' := dirSubringDeriv_zero hUo v
      map_add' := dirSubringDeriv_add hUo v }
  exact Derivation.mk' D.toIntLinearMap (dirSubringDeriv_mul hUo v)

/-- Differential-ring structure on the analytic germs, along a fixed direction. -/
@[reducible] def analyticGermDifferential {U : Set E} (hUo : IsOpen U) (v : E) :
    Differential (analyticGermSubringOn U) :=
  ⟨dirSubringDerivation hUo v⟩

/-! ### The meromorphic field -/

/-- The meromorphic function field of an open set of a complex normed space. -/
abbrev dirMeroField (U : Set E) : Type _ := FractionRing (analyticGermSubringOn U)

/-- Differential-field structure on the meromorphic field, along a fixed direction. -/
@[reducible] def dirMeroFieldDifferential {U : Set E}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (v : E) :
    Differential (dirMeroField U) := by
  letI := isDomain_analyticGermSubringOn U hUo hUc hUne
  letI : Algebra ℤ (analyticGermSubringOn U) := Ring.toIntAlgebra _
  letI : Algebra ℤ (dirMeroField U) := Ring.toIntAlgebra _
  exact ⟨fractionRingDerivation (K := ℤ)
    ((Algebra.linearMap (analyticGermSubringOn U) (dirMeroField U)).compDer
      (dirSubringDerivation hUo v))⟩

theorem dirMeroFieldDifferential_algebraMap {U : Set E}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (v : E)
    (a : analyticGermSubringOn U) :
    letI := isDomain_analyticGermSubringOn U hUo hUc hUne
    letI := dirMeroFieldDifferential hUo hUc hUne v
    (algebraMap (analyticGermSubringOn U) (dirMeroField U) a)′ =
      algebraMap (analyticGermSubringOn U) (dirMeroField U) (dirSubringDeriv hUo v a) := by
  letI := isDomain_analyticGermSubringOn U hUo hUc hUne
  letI : Algebra ℤ (analyticGermSubringOn U) := Ring.toIntAlgebra _
  letI : Algebra ℤ (dirMeroField U) := Ring.toIntAlgebra _
  letI := dirMeroFieldDifferential hUo hUc hUne v
  change fractionRingDerivation _ (algebraMap (analyticGermSubringOn U) (dirMeroField U) a) = _
  rw [fractionRingDerivation_algebraMap]
  rfl

/-! ### Constants along the direction -/

/-- A function constant along the direction has vanishing directional derivative. -/
theorem dirFderiv_eq_zero_of_hasFDerivAt {v : E} {f : E → ℂ} {x : E} {L : E →L[ℂ] ℂ}
    (hL : HasFDerivAt f L x) (hv : L v = 0) : dirFderiv v f x = 0 := by
  rw [dirFderiv_apply, hL.fderiv, hv]

/-- The directional derivative of an analytic germ vanishes when the representative is annihilated
in that direction at every point of the set. -/
theorem dirSubringDeriv_eq_zero {U : Set E} (hUo : IsOpen U) (v : E)
    {a : analyticGermSubringOn U} {f : E → ℂ}
    (hfa : (Germ.coeRingHom (𝓟 U) f) = (a : Germ (𝓟 U) ℂ))
    (hzero : ∀ x ∈ U, dirFderiv v f x = 0) :
    dirSubringDeriv hUo v a = 0 := by
  apply Subtype.ext
  rw [dirSubringDeriv_coe, ← hfa]
  change (dirFderiv v f : Germ (𝓟 U) ℂ) = ((0 : analyticGermSubringOn U) : Germ (𝓟 U) ℂ)
  rw [ZeroMemClass.coe_zero, ← Germ.coe_zero, Germ.coe_eq]
  exact eventually_principal.mpr fun x hx => hzero x hx

/-! ### A product domain: functions of the first factor are constants -/

section Product

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- **A function of the first factor is a differential constant for the second-factor
direction.**  Its derivative factors through the first projection, which annihilates `(0, v)`. -/
theorem dirFderiv_comp_fst_eq_zero {h : E → ℂ} {x : E × F} (v : F)
    (hh : DifferentiableAt ℂ h x.1) :
    dirFderiv ((0 : E), v) (fun p : E × F => h p.1) x = 0 := by
  have hcomp : HasFDerivAt (fun p : E × F => h p.1)
      ((fderiv ℂ h x.1).comp (ContinuousLinearMap.fst ℂ E F)) x :=
    HasFDerivAt.comp x hh.hasFDerivAt hasFDerivAt_fst
  rw [dirFderiv_apply, hcomp.fderiv]
  simp

/-- A function of the first factor is analytic on a product domain when it is analytic on the
projection. -/
theorem analyticOnNhd_comp_fst {h : E → ℂ} {U : Set (E × F)} {V : Set E}
    (hh : AnalyticOnNhd ℂ h V) (hUV : ∀ p ∈ U, p.1 ∈ V) :
    AnalyticOnNhd ℂ (fun p : E × F => h p.1) U :=
  hh.comp ((ContinuousLinearMap.fst ℂ E F).analyticOnNhd U) hUV

/-- **The first-factor functions are differential constants of the product field.**  Their germs are
killed by the second-factor directional derivation. -/
theorem dirSubringDeriv_comp_fst_eq_zero {U : Set (E × F)} (hUo : IsOpen U) (v : F)
    {V : Set E} {h : E → ℂ} (hh : AnalyticOnNhd ℂ h V) (hUV : ∀ p ∈ U, p.1 ∈ V)
    {a : analyticGermSubringOn U}
    (hfa : (Germ.coeRingHom (𝓟 U) fun p : E × F => h p.1) = (a : Germ (𝓟 U) ℂ)) :
    dirSubringDeriv hUo ((0 : E), v) a = 0 :=
  dirSubringDeriv_eq_zero hUo _ hfa fun x hx =>
    dirFderiv_comp_fst_eq_zero v (hh x.1 (hUV x hx)).differentiableAt

end Product

end

end GaloisForLFunctions.HTGeometry
