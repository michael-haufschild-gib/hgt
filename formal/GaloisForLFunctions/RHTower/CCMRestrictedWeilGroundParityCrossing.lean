import GaloisForLFunctions.RHTower.CCMRestrictedWeilGroundDerivativeCriterion
import GaloisForLFunctions.RHTower.CCMRestrictedWeilPolarGroundParityForcing

/-!
# Multiplicity of the polar Weil ground level is a parity crossing

At a positive aperture `a`, reflection `x ↦ −x` acts on the CCM form domain, preserves the
restricted Weil form and the polar constraints, and acts on transforms by `t ↦ −t` on the real line
(`unitaryLaplace_timeRep_reflection`).  The even and odd parts of a polar ground state are polar
ground states.

**Theorem** (`two_le_finrank_iff_both_parities`).  The polar ground level has multiplicity at least
two iff it contains a nonzero reflection-even and a nonzero reflection-odd polar ground state.

**Proof.**  An even and an odd nonzero vector are independent: apply the reflection to a vanishing
combination.  Conversely, if the multiplicity is at least two, some ground state `G` has a ground
state `v` with transform `t f̂_G(t)` (`two_le_finrank_iff`, `isPolarGround_of_mul`).  Then the
odd part of `v` has transform `t f̂_{G_even}(t)` and the even part of `v` has transform
`t f̂_{G_odd}(t)`, so whichever parity part of `G` is nonzero is matched by a nonzero ground
state of the other parity.  Multiplicity therefore occurs exactly where the even and odd polar
ground energies coincide, and there the odd ground state is the derivative of an even one.
-/

noncomputable section
open Complex MeasureTheory Set Filter Topology
open scoped InnerProduct ComplexConjugate

namespace RHTower.CCMGroundParity

open GaloisForLFunctions.HTGeometry.FourierZeroFlip
open GaloisForLFunctions.HTGeometry.FourierLaplaceDivision
open RHTower.CCMRealRootedGround RHTower.CCMGroundQuadrature RHTower.CCMGroundStructure
open RHTower.CCMGroundDerivative

variable (a : SuzukiPositiveAperture)

/-- Reflection acts on transforms by `t ↦ −t` on the real line. -/
theorem unitaryLaplace_timeRep_reflection (u : CCMArchimedeanFormDomain a) (t : ℝ) :
    unitaryLaplace (timeRep a (ccmArchimedeanFormReflection a u)) t =
      unitaryLaplace (timeRep a u) (((-t : ℝ)) : ℂ) := by
  have hcont1 := continuous_unitaryLaplace_ofReal
    (integrable_timeRep a (ccmArchimedeanFormReflection a u))
  have hcont2 : Continuous fun t : ℝ => unitaryLaplace (timeRep a u) (((-t : ℝ)) : ℂ) :=
    (continuous_unitaryLaplace_ofReal (integrable_timeRep a u)).comp continuous_neg
  have hrefl : (((ccmArchimedeanFormReflection a u).1 : CCMArchimedeanFourierL2) : ℝ → ℂ)
      =ᵐ[volume] fun x : ℝ => ((u.1 : CCMArchimedeanFourierL2) : ℝ → ℂ) (-x) :=
    (Measure.absolutelyContinuous_of_le volume_le_ccmArchimedeanFormMeasure).ae_le
      (ccmArchimedeanFourierReflection_ae u.1)
  have hneg : (fun x : ℝ => ((u.1 : CCMArchimedeanFourierL2) : ℝ → ℂ) (-x)) =ᵐ[volume]
      fun x : ℝ => unitaryLaplace (timeRep a u) (((-x : ℝ)) : ℂ) :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae_eq_comp
      (freq_ae a u)
  have hae := ((freq_ae a (ccmArchimedeanFormReflection a u)).symm.trans hrefl).trans hneg
  exact congrFun ((Continuous.ae_eq_iff_eq volume hcont1 hcont2).mp hae) t

theorem unitaryLaplace_timeRep_evenPart (u : CCMArchimedeanFormDomain a) (t : ℝ) :
    unitaryLaplace (timeRep a (ccmRestrictedWeilEvenPart a u)) t = (2 : ℂ)⁻¹ *
      (unitaryLaplace (timeRep a u) t + unitaryLaplace (timeRep a u) (((-t : ℝ)) : ℂ)) := by
  unfold ccmRestrictedWeilEvenPart
  have h := unitaryLaplace_timeRep_add_smul a u (ccmArchimedeanFormReflection a u) 1 t
  rw [one_smul, one_mul] at h
  rw [unitaryLaplace_timeRep_smul, h, unitaryLaplace_timeRep_reflection]

theorem unitaryLaplace_timeRep_oddPart (u : CCMArchimedeanFormDomain a) (t : ℝ) :
    unitaryLaplace (timeRep a (ccmRestrictedWeilOddPart a u)) t = (2 : ℂ)⁻¹ *
      (unitaryLaplace (timeRep a u) t - unitaryLaplace (timeRep a u) (((-t : ℝ)) : ℂ)) := by
  unfold ccmRestrictedWeilOddPart
  have h := unitaryLaplace_timeRep_add_smul a u (ccmArchimedeanFormReflection a u) (-1) t
  rw [neg_one_smul, ← sub_eq_add_neg, neg_one_mul, ← sub_eq_add_neg] at h
  rw [unitaryLaplace_timeRep_smul, h, unitaryLaplace_timeRep_reflection]

theorem isPolarGround_evenPart {u : CCMArchimedeanFormDomain a} (hu : IsPolarGround a u) :
    IsPolarGround a (ccmRestrictedWeilEvenPart a u) :=
  ⟨hu.1.evenPart, (polarGround_evenOdd_components a u hu.1 hu.2).1⟩

theorem isPolarGround_oddPart {u : CCMArchimedeanFormDomain a} (hu : IsPolarGround a u) :
    IsPolarGround a (ccmRestrictedWeilOddPart a u) :=
  ⟨hu.1.oddPart, (polarGround_evenOdd_components a u hu.1 hu.2).2⟩

theorem exists_ne_zero_transform_ne_zero {u : CCMArchimedeanFormDomain a} (hu : u ≠ 0) :
    ∃ t : ℝ, t ≠ 0 ∧ unitaryLaplace (timeRep a u) t ≠ 0 := by
  have hJ : ccmArchimedeanFormToAperture a u ≠ 0 := fun h =>
    hu (ccmArchimedeanFormToAperture_injective a (by rw [h, map_zero]))
  obtain ⟨t, ht, ht0⟩ := ((infinite_real_ne_zero a hJ).sdiff (Set.finite_singleton 0)).nonempty
  exact ⟨t, ht0, ht⟩

theorem ne_zero_of_transform_ne_zero {u : CCMArchimedeanFormDomain a} {t : ℝ}
    (ht : unitaryLaplace (timeRep a u) t ≠ 0) : u ≠ 0 := by
  rintro rfl
  exact ht (unitaryLaplace_timeRep_zero a _)

/-- **Multiplicity is a parity crossing.**  The polar ground level has multiplicity at least two
iff it contains a nonzero reflection-even and a nonzero reflection-odd polar ground state. -/
theorem two_le_finrank_iff_both_parities :
    2 ≤ Module.finrank ℂ (groundSubmodule a) ↔
      (∃ e : CCMArchimedeanFormDomain a, IsPolarGround a e ∧ e ≠ 0 ∧
        ccmArchimedeanFormReflection a e = e) ∧
      (∃ o : CCMArchimedeanFormDomain a, IsPolarGround a o ∧ o ≠ 0 ∧
        ccmArchimedeanFormReflection a o = -o) := by
  classical
  haveI := finiteDimensional_groundSubmodule a
  constructor
  · intro hd
    obtain ⟨G, v, hG, hJG, hv, hvG⟩ := (two_le_finrank_iff a).mp hd
    have hvg := isPolarGround_of_mul a hG hv hvG
    have hvo : ∀ t : ℝ, unitaryLaplace (timeRep a (ccmRestrictedWeilOddPart a v)) t =
        (t : ℂ) * unitaryLaplace (timeRep a (ccmRestrictedWeilEvenPart a G)) t := by
      intro t
      rw [unitaryLaplace_timeRep_oddPart, unitaryLaplace_timeRep_evenPart, hvG t, hvG (-t)]
      push_cast
      ring
    have hve : ∀ t : ℝ, unitaryLaplace (timeRep a (ccmRestrictedWeilEvenPart a v)) t =
        (t : ℂ) * unitaryLaplace (timeRep a (ccmRestrictedWeilOddPart a G)) t := by
      intro t
      rw [unitaryLaplace_timeRep_evenPart, unitaryLaplace_timeRep_oddPart, hvG t, hvG (-t)]
      push_cast
      ring
    have hG0 : G ≠ 0 := fun h => hJG (by rw [h, map_zero])
    by_cases hGe : ccmRestrictedWeilEvenPart a G = 0
    · have hGo : ccmRestrictedWeilOddPart a G ≠ 0 := by
        intro h
        apply hG0
        rw [← ccmRestrictedWeilEvenPart_add_oddPart a G, hGe, h, add_zero]
      obtain ⟨t, ht0, ht⟩ := exists_ne_zero_transform_ne_zero a hGo
      have hne : ccmRestrictedWeilEvenPart a v ≠ 0 := by
        refine ne_zero_of_transform_ne_zero a (t := t) ?_
        rw [hve t]
        exact mul_ne_zero (by exact_mod_cast ht0) ht
      exact ⟨⟨_, isPolarGround_evenPart a hvg, hne, ccmArchimedeanFormReflection_evenPart a v⟩,
        ⟨_, isPolarGround_oddPart a hG, hGo, ccmArchimedeanFormReflection_oddPart a G⟩⟩
    · obtain ⟨t, ht0, ht⟩ := exists_ne_zero_transform_ne_zero a hGe
      have hne : ccmRestrictedWeilOddPart a v ≠ 0 := by
        refine ne_zero_of_transform_ne_zero a (t := t) ?_
        rw [hvo t]
        exact mul_ne_zero (by exact_mod_cast ht0) ht
      exact ⟨⟨_, isPolarGround_evenPart a hG, hGe, ccmArchimedeanFormReflection_evenPart a G⟩,
        ⟨_, isPolarGround_oddPart a hvg, hne, ccmArchimedeanFormReflection_oddPart a v⟩⟩
  · rintro ⟨⟨e, he, he0, hRe⟩, ⟨o, ho, ho0, hRo⟩⟩
    have hli : LinearIndependent ℂ ![(⟨e, he⟩ : groundSubmodule a), ⟨o, ho⟩] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have h1 : s • e + t • o = 0 := by
        have := congrArg Subtype.val hst
        simpa using this
      have h2 : s • e + t • (-o) = 0 := by
        have := congrArg (ccmArchimedeanFormReflection a) h1
        rwa [map_add, map_smul, map_smul, hRe, hRo, map_zero] at this
      have hs : (2 * s) • e = 0 := by
        calc (2 * s) • e = (s • e + t • o) + (s • e + t • (-o)) := by module
          _ = 0 := by rw [h1, h2, add_zero]
      have ht : (2 * t) • o = 0 := by
        calc (2 * t) • o = (s • e + t • o) - (s • e + t • (-o)) := by module
          _ = 0 := by rw [h1, h2, sub_zero]
      constructor
      · rcases smul_eq_zero.mp hs with h | h
        · simpa using h
        · exact absurd h he0
      · rcases smul_eq_zero.mp ht with h | h
        · simpa using h
        · exact absurd h ho0
    have := hli.fintype_card_le_finrank
    simpa using this

end RHTower.CCMGroundParity
