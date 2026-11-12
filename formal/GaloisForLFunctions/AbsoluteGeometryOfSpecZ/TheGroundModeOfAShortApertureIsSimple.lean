import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheNullModesAlongTheAperturePathAreAsManyAsTheEigenvaluesBelowTheEnergy
import GaloisForLFunctions.RHTower.Suzuki.SuzukiSmallApertureTheoremOneFour

/-!
# The ground mode of a short aperture is simple

On a short aperture the lowest eigenvalue of Weil's operator is simple (Suzuki): its eigenspace
is one complex line. Read on the form domain, the null space of Weil's form at the ground energy
has dimension one (`exists_weilNullity_groundEnergy_eq_one`): a null mode is a fixed vector of
the Birman–Schwinger operator, hence a form representative of an eigenvector, and the embedding
of the form domain is injective.

Consequently the nullities of the aperture path are not all even: at an energy just above the
ground energy of a short aperture `b`, the index at `b` is one, so the path meets exactly one
resonant aperture below `b`, and its nullity is one (`exists_single_simple_null_mode`).
-/

open Module Finset

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open _root_.RHTower _root_.RHTower.PaperRestrictedWeil
open ArithmeticContinuationAndCriticalEnergy HTGeometry

/-- **On a short aperture the null space at the ground energy is a line.** -/
theorem exists_weilNullity_groundEnergy_eq_one :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a : SuzukiPositiveAperture, a.1 < δ →
      weilNullity a (ccmRestrictedWeilGroundEnergy a) = 1 := by
  obtain ⟨δ, hδ, h⟩ := exists_suzukiSmallAperture_full_theorem_one_four
  refine ⟨δ, hδ, fun a ha => le_antisymm ?_ (weilNullity_groundEnergy_pos a)⟩
  obtain ⟨-, -, e, he0, -, -, hsimple⟩ := h a ha
  -- the embedding maps a null mode into the line of the eigenvector
  have hmem : ∀ u : Space a, operator a (ccmRestrictedWeilGroundEnergy a) u = 0 →
      ccmArchimedeanFormToAperture a u ∈
        Submodule.span ℂ {(e : suzukiApertureHilbert a)} := by
    intro u hu
    have hfix : ccmRestrictedWeilFormBirmanSchwinger a (ccmRestrictedWeilGroundEnergy a) u = u := by
      have hsub : u - ccmRestrictedWeilFormBirmanSchwinger a (ccmRestrictedWeilGroundEnergy a) u
          = 0 := hu
      exact (sub_eq_zero.mp hsub).symm
    obtain ⟨hm, heig⟩ :=
      (ccmRestrictedWeil_embedding_eigen_iff_formBirmanSchwinger_fixed a _ u).mpr hfix
    obtain ⟨c, hc⟩ := hsimple ⟨_, hm⟩ heig
    exact Submodule.mem_span_singleton.mpr ⟨c, hc.symm⟩
  obtain ⟨L, hL⟩ : ∃ L : (operator a (ccmRestrictedWeilGroundEnergy a)).toLinearMap.ker →ₗ[ℂ]
      Submodule.span ℂ {(e : suzukiApertureHilbert a)},
      ∀ u, ((L u : suzukiApertureHilbert a)) = ccmArchimedeanFormToAperture a u.1 :=
    ⟨((ccmArchimedeanFormToAperture a : Space a →ₗ[ℂ] suzukiApertureHilbert a).comp
      (Submodule.subtype _)).codRestrict _ (fun u => hmem u.1 u.2), fun _ => rfl⟩
  have hinj : Function.Injective L := fun u v huv =>
    Subtype.ext (ccmArchimedeanFormToAperture_injective a (by
      rw [← hL u, ← hL v, huv]))
  have h1 := LinearMap.finrank_le_finrank_of_injective hinj
  rw [finrank_span_singleton he0] at h1
  exact h1

/-- **The nullities of the aperture path are not all even**: at an energy just above the ground
energy of a short aperture the path meets exactly one resonant aperture, of nullity one. -/
theorem exists_single_simple_null_mode :
    ∃ (b : SuzukiPositiveAperture) (E : ℝ) (c : SuzukiPositiveAperture),
      resonantBelow b E = {c} ∧ weilNullity c E = 1 ∧ negativeRank b E = 1 := by
  obtain ⟨δ, hδ, h⟩ := exists_weilNullity_groundEnergy_eq_one
  obtain ⟨b, hb⟩ : ∃ b : SuzukiPositiveAperture, b.1 = δ / 2 := ⟨⟨δ / 2, by linarith⟩, rfl⟩
  have hν := h b (by rw [hb]; linarith)
  obtain ⟨E, hE, hjump⟩ :=
    exists_right_energy_negativeRank_eq b (ccmRestrictedWeilGroundEnergy b)
  have hN : negativeRank b E = 1 := by
    rw [hjump E hE le_rfl, hν,
      (negativeRank_eq_zero_iff_ground b (ccmRestrictedWeilGroundEnergy b)).mpr le_rfl]
  have hsum : ∑ c ∈ resonantBelow b E, weilNullity c E = 1 := by
    rw [← negativeRank_eq_sum_nullity]
    exact hN
  have hcard : (resonantBelow b E).card = 1 := by
    have hle : (resonantBelow b E).card ≤ ∑ c ∈ resonantBelow b E, weilNullity c E := by
      rw [Finset.card_eq_sum_ones]
      exact Finset.sum_le_sum fun c hc => (mem_resonantBelow.mp hc).2
    have hpos : 0 < (resonantBelow b E).card := by
      rw [Finset.card_pos]
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne, Finset.sum_empty] at hsum
      exact zero_ne_one hsum
    omega
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hcard
  refine ⟨b, E, c, hc, ?_, hN⟩
  rw [hc, Finset.sum_singleton] at hsum
  exact hsum

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
