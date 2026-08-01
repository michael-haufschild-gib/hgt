import GaloisForLFunctions.HTGeometry.CompactAbelianCharVector

/-!
# A character vector is a continuous character

A vector of an eigenspace of a convolution operator, with nonzero eigenvalue, has a continuous
representative: it equals `λ⁻¹` times its own convolution.  If every translation acts on it by a
scalar, that scalar is therefore a ratio of values of a continuous function, hence continuous in the
group element; multiplicativity and unit modulus come from composing translations and from their
being isometries.

So the analytic machinery produces genuine continuous characters of the group.
-/

open MeasureTheory TopologicalSpace

namespace GaloisForLFunctions

namespace CompactAbelian

noncomputable section

variable {G : Type*} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

variable (k : G → ℂ) (hk : Continuous k) {C : ℝ} (hC : ∀ z, ‖k z‖ ≤ C)

omit [T2Space G] in
include hk hC in
/-- An eigenvector with nonzero eigenvalue has a continuous representative. -/
theorem exists_continuous_representative {lam : ℂ} (hlam : lam ≠ 0)
    {w : Lp ℂ 2 (haarProb G)} (hwe : convOp k hk hC w = lam • w) :
    ∃ f : G → ℂ, Continuous f ∧ (fun x => w x) =ᵐ[haarProb G] f := by
  refine ⟨fun x => lam⁻¹ * convFun k (fun y => w y) x,
    continuous_const.mul (continuous_convFun hk hC (integrable_lp w)), ?_⟩
  have h1 := convOp_coeFn k hk hC w
  have h2 : (fun x => ((lam • w : Lp ℂ 2 (haarProb G)) : G → ℂ) x)
      =ᵐ[haarProb G] fun x => lam * w x := by
    filter_upwards [Lp.coeFn_smul lam w] with x hx
    rw [hx]
    rfl
  have h3 : (fun x => ((convOp k hk hC w : Lp ℂ 2 (haarProb G)) : G → ℂ) x)
      =ᵐ[haarProb G] fun x => ((lam • w : Lp ℂ 2 (haarProb G)) : G → ℂ) x := by
    rw [hwe]
  filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
  have : lam * w x = convC k hk hC w x := by
    rw [← hx2, ← hx3, hx1]
  rw [convC_apply] at this
  rw [← this, inv_mul_cancel_left₀ hlam]

omit [T2Space G] in
include hk hC in
/-- **A character vector gives a continuous character.** -/
theorem continuous_character_of_char_vector {lam : ℂ} (hlam : lam ≠ 0)
    {w : Lp ℂ 2 (haarProb G)} (hw : w ≠ 0) (hwe : convOp k hk hC w = lam • w)
    {χ : G → ℂ} (hχ : ∀ a : G, transOp a w = χ a • w) :
    Continuous χ ∧ (∀ a b : G, χ (a + b) = χ a * χ b) ∧ (∀ a : G, ‖χ a‖ = 1) := by
  obtain ⟨f, hfc, hfw⟩ := exists_continuous_representative k hk hC hlam hwe
  have hwnorm : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  -- multiplicativity
  have hmul : ∀ a b : G, χ (a + b) = χ a * χ b := by
    intro a b
    have h1 : transOp a (transOp b w) = transOp (a + b) w := transOp_transOp a b w
    rw [hχ b, hχ (a + b)] at h1
    rw [map_smul, hχ a] at h1
    have h2 : (χ b * χ a) • w = χ (a + b) • w := by
      rw [← smul_smul]
      exact h1
    have h3 : (χ b * χ a - χ (a + b)) • w = 0 := by
      rw [sub_smul, h2, sub_self]
    have h4 : χ b * χ a - χ (a + b) = 0 := by
      by_contra hne
      exact hw (by simpa [hne] using (smul_eq_zero.mp h3).resolve_left hne)
    have : χ (a + b) = χ b * χ a := by linear_combination -h4
    rw [this, mul_comm]
  -- unit modulus
  have hnorm : ∀ a : G, ‖χ a‖ = 1 := by
    intro a
    have h1 : ‖transOp a w‖ = ‖w‖ := norm_transOp a w
    rw [hχ a, norm_smul] at h1
    have h2 : ‖χ a‖ * ‖w‖ = 1 * ‖w‖ := by rw [one_mul]; exact h1
    exact mul_right_cancel₀ hwnorm h2
  refine ⟨?_, hmul, hnorm⟩
  -- the translation relation holds pointwise for the continuous representative
  have hpt : ∀ a : G, ∀ x : G, f (x + a) = χ a * f x := by
    intro a
    have hcont1 : Continuous fun x : G => f (x + a) := hfc.comp (continuous_id.add continuous_const)
    have hcont2 : Continuous fun x : G => χ a * f x := continuous_const.mul hfc
    have hae : (fun x : G => f (x + a)) =ᵐ[haarProb G] fun x : G => χ a * f x := by
      have hA : (fun x : G => ((transOp a w : Lp ℂ 2 (haarProb G)) : G → ℂ) x)
          =ᵐ[haarProb G] fun x : G => w (x + a) := transOp_coeFn a w
      have hB : (fun x : G => ((transOp a w : Lp ℂ 2 (haarProb G)) : G → ℂ) x)
          =ᵐ[haarProb G] fun x : G => χ a * w x := by
        rw [hχ a]
        filter_upwards [Lp.coeFn_smul (χ a) w] with x hx
        rw [hx]
        rfl
      have hC1 := (measurePreserving_translate (G := G) a).quasiMeasurePreserving.ae_eq_comp hfw
      filter_upwards [hA.symm.trans hB, hC1, hfw] with x hx1 hx2 hx3
      simp only [Function.comp_apply] at hx2
      rw [← hx2, hx1, hx3]
    exact congrFun ((hcont1.ae_eq_iff_eq (haarProb G) hcont2).mp hae)
  -- a point where the representative does not vanish
  have hfne : ∃ x₀ : G, f x₀ ≠ 0 := by
    by_contra hall
    push Not at hall
    refine hw (Lp.ext ?_)
    filter_upwards [hfw, Lp.coeFn_zero ℂ 2 (haarProb G)] with x hx hz
    rw [hx, hall x, hz]
    rfl
  obtain ⟨x₀, hx₀⟩ := hfne
  have hform : ∀ a : G, χ a = f (x₀ + a) / f x₀ := by
    intro a
    rw [hpt a x₀]
    field_simp
  have : χ = fun a => f (x₀ + a) / f x₀ := funext hform
  rw [this]
  exact (hfc.comp (continuous_const.add continuous_id)).div_const _

end

end CompactAbelian

end GaloisForLFunctions
