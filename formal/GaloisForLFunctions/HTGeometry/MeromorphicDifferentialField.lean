import GaloisForLFunctions.Bottcher.MeromorphicField
import GaloisForLFunctions.HTGeometry.FractionRingDerivation
import Mathlib.RingTheory.Derivation.DifferentialRing
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Differential structure on meromorphic germ fields

Differentiation descends to analytic germs on an open set, defines a
derivation on the analytic-germ domain, and extends by the quotient rule to
its meromorphic fraction field. This supplies the genuine differential field
carrier needed by the elliptic-gamma Ostrowski criterion.
-/

open Filter Topology Set Function
open scoped Differential

namespace GaloisForLFunctions

open Bottcher

noncomputable section

/-- Differentiation is well-defined on germs along an open set. -/
def analyticGermDeriv {U : Set ℂ} (hUo : IsOpen U) :
    Germ (𝓟 U) ℂ → Germ (𝓟 U) ℂ :=
  Germ.map' deriv (by
    intro f g hfg
    exact eventually_principal.mpr
      (Set.EqOn.deriv (eventually_principal.mp hfg) hUo))

@[simp] theorem analyticGermDeriv_coe {U : Set ℂ} (hUo : IsOpen U)
    (f : ℂ → ℂ) :
    analyticGermDeriv hUo (f : Germ (𝓟 U) ℂ) =
      (deriv f : Germ (𝓟 U) ℂ) := rfl

/-- Derivative of an analytic germ, again an analytic germ. -/
def analyticSubringDeriv {U : Set ℂ} (hUo : IsOpen U)
    (a : analyticSubring U) : analyticSubring U := by
  refine ⟨analyticGermDeriv hUo a.1, ?_⟩
  obtain ⟨f, hf, hfa⟩ := a.2
  refine ⟨deriv f, hf.deriv, ?_⟩
  rw [← hfa]
  rfl

@[simp] theorem analyticSubringDeriv_coe {U : Set ℂ} (hUo : IsOpen U)
    (a : analyticSubring U) :
    (analyticSubringDeriv hUo a : Germ (𝓟 U) ℂ) =
      analyticGermDeriv hUo (a : Germ (𝓟 U) ℂ) := rfl

theorem analyticSubringDeriv_zero {U : Set ℂ} (hUo : IsOpen U) :
    analyticSubringDeriv hUo (0 : analyticSubring U) = 0 := by
  apply Subtype.ext
  rw [analyticSubringDeriv_coe]
  change (deriv (0 : ℂ → ℂ) : Germ (𝓟 U) ℂ) = 0
  simp

theorem analyticSubringDeriv_add {U : Set ℂ} (hUo : IsOpen U)
    (a b : analyticSubring U) :
    analyticSubringDeriv hUo (a + b) =
      analyticSubringDeriv hUo a + analyticSubringDeriv hUo b := by
  obtain ⟨f, hf, hfa⟩ := a.2
  obtain ⟨g, hg, hgb⟩ := b.2
  apply Subtype.ext
  change analyticGermDeriv hUo ((a : Germ (𝓟 U) ℂ) + b) =
    analyticGermDeriv hUo a + analyticGermDeriv hUo b
  rw [← hfa, ← hgb]
  change analyticGermDeriv hUo (↑(f + g) : Germ (𝓟 U) ℂ) =
    analyticGermDeriv hUo (↑f : Germ (𝓟 U) ℂ) +
      analyticGermDeriv hUo (↑g : Germ (𝓟 U) ℂ)
  rw [analyticGermDeriv_coe, analyticGermDeriv_coe,
    analyticGermDeriv_coe, ← Germ.coe_add, Germ.coe_eq]
  exact eventually_principal.mpr fun z hz =>
    deriv_add (hf z hz).differentiableAt (hg z hz).differentiableAt

theorem analyticSubringDeriv_mul {U : Set ℂ} (hUo : IsOpen U)
    (a b : analyticSubring U) :
    analyticSubringDeriv hUo (a * b) =
      a * analyticSubringDeriv hUo b +
        b * analyticSubringDeriv hUo a := by
  obtain ⟨f, hf, hfa⟩ := a.2
  obtain ⟨g, hg, hgb⟩ := b.2
  apply Subtype.ext
  change analyticGermDeriv hUo ((a : Germ (𝓟 U) ℂ) * b) =
    (a : Germ (𝓟 U) ℂ) * analyticGermDeriv hUo b +
      (b : Germ (𝓟 U) ℂ) * analyticGermDeriv hUo a
  rw [← hfa, ← hgb]
  change analyticGermDeriv hUo (↑(f * g) : Germ (𝓟 U) ℂ) =
    (↑f : Germ (𝓟 U) ℂ) * analyticGermDeriv hUo (↑g : Germ (𝓟 U) ℂ) +
      (↑g : Germ (𝓟 U) ℂ) * analyticGermDeriv hUo (↑f : Germ (𝓟 U) ℂ)
  rw [analyticGermDeriv_coe, analyticGermDeriv_coe,
    analyticGermDeriv_coe, ← Germ.coe_mul, ← Germ.coe_mul,
    ← Germ.coe_add, Germ.coe_eq]
  exact eventually_principal.mpr fun z hz => by
    rw [deriv_mul (hf z hz).differentiableAt (hg z hz).differentiableAt]
    change deriv f z * g z + f z * deriv g z =
      f z * deriv g z + g z * deriv f z
    ring

/-- The ordinary complex derivative as an integer-linear derivation on the
analytic-germ domain. -/
def analyticSubringDerivation {U : Set ℂ} (hUo : IsOpen U) :
    Derivation ℤ (analyticSubring U) (analyticSubring U) := by
  let D : analyticSubring U →+ analyticSubring U :=
    { toFun := analyticSubringDeriv hUo
      map_zero' := analyticSubringDeriv_zero hUo
      map_add' := analyticSubringDeriv_add hUo }
  exact Derivation.mk' D.toIntLinearMap (analyticSubringDeriv_mul hUo)

/-- Differential-ring structure on analytic germs over an open set. -/
@[reducible] def analyticSubringDifferential {U : Set ℂ} (hUo : IsOpen U) :
    Differential (analyticSubring U) :=
  ⟨analyticSubringDerivation hUo⟩

/-- Differential-field structure on the meromorphic fraction field. -/
@[reducible] def meroFieldDifferential {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) :
    Differential (meroField U) := by
  letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
  letI : Algebra ℤ (analyticSubring U) := Ring.toIntAlgebra _
  letI : Algebra ℤ (meroField U) := Ring.toIntAlgebra _
  exact ⟨fractionRingDerivation (K := ℤ)
    ((Algebra.linearMap (analyticSubring U) (meroField U)).compDer
      (analyticSubringDerivation hUo))⟩

theorem meroFieldDifferential_algebraMap {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (a : analyticSubring U) :
    letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
    letI := meroFieldDifferential hUo hUc hUne
    (algebraMap (analyticSubring U) (meroField U) a)′ =
      algebraMap (analyticSubring U) (meroField U)
        (analyticSubringDeriv hUo a) := by
  letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
  letI : Algebra ℤ (analyticSubring U) := Ring.toIntAlgebra _
  letI : Algebra ℤ (meroField U) := Ring.toIntAlgebra _
  letI := meroFieldDifferential hUo hUc hUne
  change fractionRingDerivation _ (algebraMap (analyticSubring U) (meroField U) a) = _
  rw [fractionRingDerivation_algebraMap]
  rfl

/-- Restriction of analytic germs commutes with differentiation.  This is the carrier-level
naturality needed to transport differential equations and differential independence from a
connected ambient domain to a nonempty open subdomain. -/
theorem restrictAnalytic_analyticSubringDeriv
    {U V : Set ℂ} (hVU : V ⊆ U) (hUo : IsOpen U) (hVo : IsOpen V)
    (a : analyticSubring U) :
    Bottcher.restrictAnalytic hVU (analyticSubringDeriv hUo a) =
      analyticSubringDeriv hVo (Bottcher.restrictAnalytic hVU a) := by
  obtain ⟨f, hf, hfa⟩ := a.2
  apply Subtype.ext
  change (Bottcher.restrictGermHom hVU)
      (analyticGermDeriv hUo (a : Germ (𝓟 U) ℂ)) =
    analyticGermDeriv hVo
      ((Bottcher.restrictGermHom hVU) (a : Germ (𝓟 U) ℂ))
  rw [← hfa]
  change (↑(deriv f) : Germ (𝓟 U) ℂ).compTendsto id
      (tendsto_principal_principal.mpr (fun _ hx => hVU hx)) =
    analyticGermDeriv hVo
      ((↑f : Germ (𝓟 U) ℂ).compTendsto id
        (tendsto_principal_principal.mpr (fun _ hx => hVU hx)))
  rw [Germ.coe_compTendsto]
  rfl

set_option synthInstance.maxHeartbeats 100000

/-- **Differential restriction of meromorphic germs.**  The canonical restriction field embedding
`meroField U -> meroField V` commutes with the meromorphic differential whenever `V` is a nonempty
open subdomain of the open connected domain `U`. -/
theorem restrictMeroHom_deriv
    {U V : Set ℂ} (hVU : V ⊆ U)
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hVne : V.Nonempty)
    (x : meroField U) :
    letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
    letI := Bottcher.isDomain_analyticSubring V hVo hVc hVne
    letI := meroFieldDifferential hUo hUc hUne
    letI := meroFieldDifferential hVo hVc hVne
    Bottcher.restrictMeroHom hVU hUo hUc hUne hVo hVc hVne x′ =
      (Bottcher.restrictMeroHom hVU hUo hUc hUne hVo hVc hVne x)′ := by
  letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
  letI := Bottcher.isDomain_analyticSubring V hVo hVc hVne
  letI : Algebra ℤ (analyticSubring U) := Ring.toIntAlgebra _
  letI : Algebra ℤ (analyticSubring V) := Ring.toIntAlgebra _
  letI : Algebra ℤ (meroField U) := Ring.toIntAlgebra _
  letI : Algebra ℤ (meroField V) := Ring.toIntAlgebra _
  letI := meroFieldDifferential hUo hUc hUne
  letI := meroFieldDifferential hVo hVc hVne
  let ρ : meroField U →+* meroField V :=
    Bottcher.restrictMeroHom hVU hUo hUc hUne hVo hVc hVne
  change ρ x′ = (ρ x)′
  obtain ⟨a, b, hb, rfl⟩ :=
    IsFractionRing.div_surjective (analyticSubring U) x
  have hmap (c : analyticSubring U) :
      ρ (algebraMap (analyticSubring U) (meroField U) c) =
        algebraMap (analyticSubring V) (meroField V)
          (Bottcher.restrictAnalytic hVU c) := by
    exact Bottcher.restrictMeroHom_algebraMap
      hVU hUo hUc hUne hVo hVc hVne c
  have hderiv (c : analyticSubring U) :
      ρ ((algebraMap (analyticSubring U) (meroField U) c)′) =
        (algebraMap (analyticSubring V) (meroField V)
          (Bottcher.restrictAnalytic hVU c))′ := by
    rw [meroFieldDifferential_algebraMap, hmap,
      meroFieldDifferential_algebraMap,
      restrictAnalytic_analyticSubringDeriv]
  rw [Derivation.leibniz_div]
  simp only [map_sub, map_mul, map_pow, map_inv₀, map_div₀, smul_eq_mul]
  rw [Derivation.leibniz_div]
  simp only [smul_eq_mul]
  rw [hmap, hmap, hderiv, hderiv]

set_option synthInstance.maxHeartbeats 20000

end

end GaloisForLFunctions
