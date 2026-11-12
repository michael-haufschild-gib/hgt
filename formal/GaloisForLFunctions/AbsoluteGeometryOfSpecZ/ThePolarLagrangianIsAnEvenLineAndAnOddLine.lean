import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheChargedNullModesAreTheCrossingsOfThePolarLagrangian
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.ALagrangianPlaneWithAnExchangeSymmetryIsAPairOfLines
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPolarGroundParityForcing

/-!
# The polar Lagrangian is an even line and an odd line

The reflection `u(x) ↦ u(−x)` of an aperture preserves Weil's form and the mass, so it commutes
with Weil's operator (`operator_reflection`), and it exchanges the two charges
(`polarCharge_reflection_zero`, `polarCharge_reflection_one`). Hence the polar Lagrangian is
invariant under the exchange of the two poles (`exists_exchange_mem_polarLagrangian`), and it is
the sum of two lines (`finrank_polarLagrangian_inf_parityPairs`):

* the **even line**: pairs with equal charges and equal forcing coefficients;
* the **odd line**: pairs with opposite charges and opposite forcing coefficients.

So the path of polar Lagrangians is a pair of points on two projective lines, one for each
parity. A charged null mode has a charged null mode of pure parity
(`exists_pureParity_charged_null_mode`): an even one crosses the charge axis on the even line,
an odd one on the odd line. A crossing of dimension two is an even and an odd charged null mode
at one aperture (`exists_even_odd_charged_of_chargedNullity_two`).
-/

open Module
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open _root_.RHTower _root_.RHTower.PaperRestrictedWeil
open ArithmeticContinuationAndCriticalEnergy HTGeometry

variable (a : SuzukiPositiveAperture) (E : ℝ)

/-- The reflection preserves the mass pairing. -/
theorem inner_formToAperture_reflection (u v : Space a) :
    ⟪ccmArchimedeanFormToAperture a (ccmArchimedeanFormReflection a u),
        ccmArchimedeanFormToAperture a (ccmArchimedeanFormReflection a v)⟫_ℂ =
      ⟪ccmArchimedeanFormToAperture a u, ccmArchimedeanFormToAperture a v⟫_ℂ := by
  change inner ℂ
    (ccmArchimedeanFormToAperture a (ccmArchimedeanFormReflection a u) : SoninL2)
    (ccmArchimedeanFormToAperture a (ccmArchimedeanFormReflection a v) : SoninL2) = _
  rw [ccmArchimedeanFormToAperture_reflection, ccmArchimedeanFormToAperture_reflection]
  exact l2ReflectionIsometry.inner_map_map _ _

/-- Weil's operator is invariant under the reflection. -/
theorem inner_operator_reflection (u v : Space a) :
    ⟪operator a E (ccmArchimedeanFormReflection a u), ccmArchimedeanFormReflection a v⟫_ℂ =
      ⟪operator a E u, v⟫_ℂ := by
  rw [operator_mixed, operator_mixed, ccmRestrictedWeilForm_reflection,
    inner_formToAperture_reflection]

/-- **Weil's operator commutes with the reflection.** -/
theorem operator_reflection (u : Space a) :
    operator a E (ccmArchimedeanFormReflection a u) =
      ccmArchimedeanFormReflection a (operator a E u) := by
  refine ext_inner_right ℂ fun v => ?_
  have h1 := inner_operator_reflection a E u (ccmArchimedeanFormReflection a v)
  rw [ccmArchimedeanFormReflection_involutive] at h1
  have h2 := (ccmArchimedeanFormReflection a).inner_map_map (operator a E u)
    (ccmArchimedeanFormReflection a v)
  rw [ccmArchimedeanFormReflection_involutive] at h2
  rw [h1, h2]

/-- The reflection of a null mode is a null mode. -/
theorem operator_reflection_eq_zero {u : Space a} (hu : operator a E u = 0) :
    operator a E (ccmArchimedeanFormReflection a u) = 0 := by
  rw [operator_reflection, hu, map_zero]

/-- The reflection exchanges the two charges. -/
theorem polarCharge_reflection_zero (u : Space a) :
    polarCharge a (ccmArchimedeanFormReflection a u) 0 = polarCharge a u 1 := by
  rw [polarCharge_zero, polarCharge_one, ccmPolarCoordinate_reflection]
  simp only [neg_div]

theorem polarCharge_reflection_one (u : Space a) :
    polarCharge a (ccmArchimedeanFormReflection a u) 1 = polarCharge a u 0 := by
  rw [polarCharge_zero, polarCharge_one, ccmPolarCoordinate_reflection]
  simp only [neg_div, neg_neg]

/-- **The polar Lagrangian is invariant under the exchange of the two poles.** -/
theorem exists_exchange_mem_polarLagrangian {p : ChargeSpace × ChargeSpace}
    (hp : p ∈ polarLagrangian a E) :
    ∃ q ∈ polarLagrangian a E,
      q.1 0 = p.1 1 ∧ q.1 1 = p.1 0 ∧ q.2 0 = p.2 1 ∧ q.2 1 = p.2 0 := by
  obtain ⟨ξ, h1, h2⟩ := (mem_polarRelation (T := operator a E) (d := polarCharge a)).mp hp
  obtain ⟨y, hy0, hy1⟩ : ∃ y : ChargeSpace, y 0 = p.2 1 ∧ y 1 = p.2 0 :=
    ⟨(EuclideanSpace.equiv (Fin 2) ℂ).symm ![p.2 1, p.2 0], rfl, rfl⟩
  have hmem : (polarCharge a (ccmArchimedeanFormReflection a ξ), y) ∈ polarLagrangian a E := by
    refine ⟨ccmArchimedeanFormReflection a ξ, rfl, ext_inner_right ℂ fun v => ?_⟩
    have h3 := (ccmArchimedeanFormReflection a).inner_map_map (operator a E ξ)
      (ccmArchimedeanFormReflection a v)
    rw [ccmArchimedeanFormReflection_involutive] at h3
    rw [operator_reflection, inner_adjoint_polarCharge, inner_ccmPolarForcing, h3, h2,
      inner_adjoint_polarCharge, inner_ccmPolarForcing, ccmPolarCoordinate_reflection,
      ccmPolarCoordinate_reflection, hy0, hy1]
    simp only [neg_div, neg_neg]
    ring
  refine ⟨_, hmem, ?_, ?_, hy0, hy1⟩
  · show polarCharge a (ccmArchimedeanFormReflection a ξ) 0 = p.1 1
    rw [polarCharge_reflection_zero, h1]
  · show polarCharge a (ccmArchimedeanFormReflection a ξ) 1 = p.1 0
    rw [polarCharge_reflection_one, h1]

/-- **The polar Lagrangian is an even line and an odd line.** -/
theorem finrank_polarLagrangian_inf_parityPairs :
    finrank ℂ ↥(polarLagrangian a E ⊓ parityPairs 1) = 1 ∧
      finrank ℂ ↥(polarLagrangian a E ⊓ parityPairs (-1)) = 1 :=
  finrank_inf_parityPairs_eq_one (fun _ hp _ hq => polarLagrangian_isotropic a E hp hq)
    (fun _ hp => exists_exchange_mem_polarLagrangian a E hp) (finrank_polarLagrangian a E)

/-! ### Null modes of pure parity -/

/-- An even vector has equal charges. -/
theorem polarCharge_one_of_reflection_eq {v : Space a}
    (h : ccmArchimedeanFormReflection a v = v) : polarCharge a v 1 = polarCharge a v 0 := by
  have h1 := polarCharge_reflection_one a v
  rwa [h] at h1

/-- An odd vector has opposite charges. -/
theorem polarCharge_one_of_reflection_eq_neg {v : Space a}
    (h : ccmArchimedeanFormReflection a v = -v) : polarCharge a v 1 = -polarCharge a v 0 := by
  have h1 := polarCharge_reflection_one a v
  rw [h, map_neg] at h1
  have h2 : -(polarCharge a v 1) = polarCharge a v 0 := h1
  rw [← h2, neg_neg]

/-- **A charged null mode has a charged null mode of pure parity.** -/
theorem exists_pureParity_charged_null_mode {u : Space a} (hu : operator a E u = 0)
    (hc : polarCharge a u ≠ 0) :
    ∃ v : Space a, operator a E v = 0 ∧ polarCharge a v ≠ 0 ∧
      (ccmArchimedeanFormReflection a v = v ∨ ccmArchimedeanFormReflection a v = -v) := by
  have hRu := operator_reflection_eq_zero a E hu
  by_cases h : polarCharge a (u + ccmArchimedeanFormReflection a u) = 0
  · refine ⟨u - ccmArchimedeanFormReflection a u, by rw [map_sub, hu, hRu, sub_zero], ?_,
      Or.inr ?_⟩
    · intro h'
      apply hc
      have h2 : polarCharge a (u + ccmArchimedeanFormReflection a u) +
          polarCharge a (u - ccmArchimedeanFormReflection a u) = 0 := by
        rw [h, h', add_zero]
      rw [← map_add, add_add_sub_cancel, ← two_smul ℂ u, map_smul] at h2
      exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
    · rw [map_sub, ccmArchimedeanFormReflection_involutive, neg_sub]
  · exact ⟨u + ccmArchimedeanFormReflection a u, by rw [map_add, hu, hRu, add_zero], h,
      Or.inl (by rw [map_add, ccmArchimedeanFormReflection_involutive, add_comm])⟩

/-- **A crossing of dimension two is an even and an odd charged null mode at one aperture.** -/
theorem exists_even_odd_charged_of_chargedNullity_two (h : chargedNullity a E = 2) :
    (∃ v : Space a, operator a E v = 0 ∧ polarCharge a v ≠ 0 ∧
        ccmArchimedeanFormReflection a v = v) ∧
      ∃ v : Space a, operator a E v = 0 ∧ polarCharge a v ≠ 0 ∧
        ccmArchimedeanFormReflection a v = -v := by
  have htop : nullCharges a E = ⊤ :=
    Submodule.eq_top_of_finrank_eq (h.trans finrank_euclideanSpace_fin.symm)
  have hall : ∀ x : ChargeSpace, ∃ u : Space a, operator a E u = 0 ∧ polarCharge a u = x := by
    intro x
    have hx : x ∈ nullCharges a E := htop ▸ Submodule.mem_top
    obtain ⟨u, hu, hux⟩ := hx
    exact ⟨u, hu, hux⟩
  constructor
  · obtain ⟨u, hu, hux⟩ := hall ((EuclideanSpace.equiv (Fin 2) ℂ).symm ![1, 1])
    have hRu := operator_reflection_eq_zero a E hu
    refine ⟨u + ccmArchimedeanFormReflection a u, by rw [map_add, hu, hRu, add_zero], ?_,
      by rw [map_add, ccmArchimedeanFormReflection_involutive, add_comm]⟩
    intro h0
    have h1 : polarCharge a u 0 + polarCharge a (ccmArchimedeanFormReflection a u) 0 = 0 := by
      have := congrArg (fun x : ChargeSpace => x 0) h0
      rwa [map_add] at this
    rw [polarCharge_reflection_zero, hux] at h1
    have h2 : (1 : ℂ) + 1 = 0 := h1
    norm_num at h2
  · obtain ⟨u, hu, hux⟩ := hall ((EuclideanSpace.equiv (Fin 2) ℂ).symm ![1, -1])
    have hRu := operator_reflection_eq_zero a E hu
    refine ⟨u - ccmArchimedeanFormReflection a u, by rw [map_sub, hu, hRu, sub_zero], ?_,
      by rw [map_sub, ccmArchimedeanFormReflection_involutive, neg_sub]⟩
    intro h0
    have h1 : polarCharge a u 0 - polarCharge a (ccmArchimedeanFormReflection a u) 0 = 0 := by
      have := congrArg (fun x : ChargeSpace => x 0) h0
      rwa [map_sub] at this
    rw [polarCharge_reflection_zero, hux] at h1
    have h2 : (1 : ℂ) - (-1) = 0 := h1
    norm_num at h2

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
