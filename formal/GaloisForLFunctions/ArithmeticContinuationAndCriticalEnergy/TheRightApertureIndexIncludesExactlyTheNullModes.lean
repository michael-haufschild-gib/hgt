import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.NullModesForceApertureIndexGrowth
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.NonpositiveRightApertureLimits

/-!
# The right aperture index includes exactly the null modes

The index immediately to the right of an aperture is its negative index
plus its nullity. The lower bound follows from non-radiation rigidity.
For the upper bound, extra negative unit vectors could be chosen orthogonal
to the smaller nonpositive space; their compact limit would be a null mode
orthogonal to itself.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

open _root_.RHTower _root_.RHTower.PaperRestrictedWeil HTGeometry
open Filter Topology

private theorem form_inner_of_val_eq {a b : SuzukiPositiveAperture}
    (u v : Space a) (x y : Space b) (hx : x.1 = u.1) (hy : y.1 = v.1) :
    inner ℂ x y = inner ℂ u v := by
  rw [Submodule.coe_inner, Submodule.coe_inner, hx, hy]

private theorem inner_apertureExt {a b : SuzukiPositiveAperture}
    (hab : a.1 ≤ b.1) (u v : Space a) :
    inner ℂ (apertureExt hab u) (apertureExt hab v) = inner ℂ u v :=
  form_inner_of_val_eq u v _ _ (apertureExt_val hab u) (apertureExt_val hab v)

private theorem inner_rightApertureExtension (a : SuzukiPositiveAperture)
    (n : ℕ) (y : Space a) (u : Space (suzukiRightAperture a n)) :
    inner ℂ (apertureExt (suzukiRightAperture_gt a 0).le y)
        (rightApertureExtension a n u) =
      inner ℂ (apertureExt (suzukiRightAperture_gt a n).le y) u :=
  form_inner_of_val_eq _ u _ _
    ((apertureExt_val _ y).trans (apertureExt_val _ y).symm) (apertureExt_val _ u)

/-- A larger finite-dimensional space contains a unit vector orthogonal
to any smaller one. -/
theorem exists_unit_mem_orthogonal_of_finrank_lt
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (V W : Submodule ℂ H) [FiniteDimensional ℂ W]
    (h : Module.finrank ℂ W < Module.finrank ℂ V) :
    ∃ x : H, x ∈ V ∧ ‖x‖ = 1 ∧ x ∈ Wᗮ := by
  let L : V →ₗ[ℂ] W := W.orthogonalProjectionOnto.toLinearMap.comp V.subtype
  have hnot : ¬ Function.Injective L := fun hi =>
    (not_le_of_gt h) (LinearMap.finrank_le_finrank_of_injective hi)
  have hx : ∃ x : V, L x = 0 ∧ x ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hnot
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    exact hn
  obtain ⟨x, hxL, hx0⟩ := hx
  have hx0' : (x : H) ≠ 0 := fun hz => hx0 (Subtype.ext hz)
  have hn : 0 < ‖(x : H)‖ := norm_pos_iff.mpr hx0'
  have hxW : (x : H) ∈ Wᗮ :=
    (Submodule.orthogonalProjectionOnto_eq_zero_iff).mp hxL
  refine ⟨(‖(x : H)‖ : ℂ)⁻¹ • (x : H), V.smul_mem _ x.property, ?_, (Wᗮ).smul_mem _ hxW⟩
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn]
  exact inv_mul_cancel₀ hn.ne'

/-- Some right aperture has no more negative directions than the entire
nonpositive space at the limiting aperture. -/
theorem exists_rightAperture_negativeRank_le (a : SuzukiPositiveAperture) (E : ℝ) :
    ∃ n : ℕ, negativeRank (suzukiRightAperture a n) E ≤
      negativeRank a E + weilNullity a E := by
  classical
  let W : Submodule ℂ (Space a) := negativeSpace a E ⊔ (operator a E).toLinearMap.ker
  have hdim : Module.finrank ℂ W = negativeRank a E + weilNullity a E := by
    have hd := Submodule.finrank_sup_add_finrank_inf_eq
      (negativeSpace a E) (operator a E).toLinearMap.ker
    rw [(PaperNegativePart.negativeSpace_disjoint_ker
      (operator a E) (operator_selfAdjoint a E)).eq_bot,
      finrank_bot, add_zero] at hd
    exact hd
  by_contra hn
  push_neg at hn
  have hex : ∀ n, ∃ u : Space (suzukiRightAperture a n),
      u ∈ negativeSpace (suzukiRightAperture a n) E ∧ ‖u‖ = 1 ∧
      ∀ y ∈ W, inner ℂ (apertureExt (suzukiRightAperture_gt a n).le y) u = 0 := by
    intro n
    let T := apertureExtLinear (suzukiRightAperture_gt a n).le
    let e := Submodule.equivMapOfInjective T
      (apertureExtLinear_injective (suzukiRightAperture_gt a n).le) W
    have hWn : Module.finrank ℂ (W.map T) = negativeRank a E + weilNullity a E :=
      e.finrank_eq.symm.trans hdim
    obtain ⟨u, hu, hnorm, horth⟩ := exists_unit_mem_orthogonal_of_finrank_lt
      (negativeSpace (suzukiRightAperture a n) E) (W.map T)
      (by rw [hWn]; exact hn n)
    refine ⟨u, hu, hnorm, fun y hy => ?_⟩
    exact (Submodule.mem_orthogonal _ _).mp horth _ ⟨y, hy, rfl⟩
  choose u hu hnorm horth using hex
  have hq : ∀ n, (inner ℂ (operator (suzukiRightAperture a n) E (u n)) (u n)).re ≤ 0 := by
    intro n
    exact (PaperNegativePart.negativeSpace_strict _ (operator_selfAdjoint _ E) (hu n)
      (fun hz => by simpa only [hz, norm_zero, zero_ne_one] using hnorm n)).le
  obtain ⟨v, φ, _, hv0, hvq, hweak⟩ := exists_nonpositive_rightAperture_limit a E u hnorm hq
  have hvorth : ∀ y ∈ W, inner ℂ y v = 0 := by
    intro y hy
    have ht := hweak (innerSL ℂ (apertureExt (suzukiRightAperture_gt a 0).le y))
    have hz : ∀ n, inner ℂ (apertureExt (suzukiRightAperture_gt a 0).le y)
        (rightApertureExtension a (φ n) (u (φ n))) = 0 := fun n =>
      (inner_rightApertureExtension a (φ n) y (u (φ n))).trans (horth (φ n) y hy)
    have ht' : Filter.Tendsto (fun _ : ℕ => (0 : ℂ)) Filter.atTop (𝓝 (inner ℂ y v)) := by
      simpa only [innerSL_apply_apply, hz, inner_apertureExt] using ht
    exact tendsto_nhds_unique ht' tendsto_const_nhds
  have hvneg : v ∈ (negativeSpace a E)ᗮ :=
    (Submodule.mem_orthogonal _ _).mpr fun y hy =>
      hvorth y ((show negativeSpace a E ≤ W from le_sup_left) hy)
  have hvker : (operator a E) v = 0 :=
    PaperNegativePart.apply_eq_zero_of_nonpositive_orthogonal
      (operator a E) (operator_selfAdjoint a E) hvneg hvq
  exact hv0 (inner_self_eq_zero.mp
    (hvorth v ((show (operator a E).toLinearMap.ker ≤ W from le_sup_right) hvker)))

/-- Immediately to the right, the negative index equals the old negative
index plus the full null multiplicity. -/
theorem exists_right_interval_negativeRank_eq (a : SuzukiPositiveAperture) (E : ℝ) :
    ∃ b : SuzukiPositiveAperture, a.1 < b.1 ∧
      ∀ c : SuzukiPositiveAperture, a.1 < c.1 → c.1 ≤ b.1 →
        negativeRank c E = negativeRank a E + weilNullity a E := by
  obtain ⟨n, hn⟩ := exists_rightAperture_negativeRank_le a E
  refine ⟨suzukiRightAperture a n, suzukiRightAperture_gt a n, fun c hac hcb => ?_⟩
  exact le_antisymm ((negativeRank_mono_of_aperture_le hcb E).trans hn)
    (negativeRank_add_nullity_le_of_aperture_lt hac E)

/-- A nonresonant aperture has a right neighborhood with constant index. -/
theorem exists_right_interval_negativeRank_eq_of_nullity_zero
    (a : SuzukiPositiveAperture) (E : ℝ) (hnull : weilNullity a E = 0) :
    ∃ b : SuzukiPositiveAperture, a.1 < b.1 ∧
      ∀ c : SuzukiPositiveAperture, a.1 ≤ c.1 → c.1 ≤ b.1 →
        negativeRank c E = negativeRank a E := by
  obtain ⟨b, hab, heq⟩ := exists_right_interval_negativeRank_eq a E
  refine ⟨b, hab, fun c hac hcb => ?_⟩
  rcases lt_or_eq_of_le hac with hlt | heq'
  · simpa only [hnull, add_zero] using heq c hlt hcb
  · exact congrArg (fun x => negativeRank x E) (Subtype.ext heq'.symm)

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
