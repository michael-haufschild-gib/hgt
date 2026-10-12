import GaloisForLFunctions.HTGeometry.PaperHalfLineSpectrum
import GaloisForLFunctions.HTGeometry.PaperCayleySourceBounds

/-!
# Invertible bounded encoding of full continuous source tails

Translation parametrizes the actual physical tail by the half-line. Cayley
multiplication is a surjective isometry; its spectrum is exactly the closure
of the encoded full tail range. The compact quotient retains every norm.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal

private abbrev H := Lp ℂ 2 halfLineMeasure

def paperHalfLineCayleySymbol (F : C(ℝ, ℝ)) (T : ℝ) : C(ℝ, ℂ) :=
  ⟨fun x => realCayley (F (T + x)),
    continuous_realCayley.comp (F.continuous.comp (continuous_const.add continuous_id))⟩

theorem paperHalfLineCayleySymbol_norm (F : C(ℝ, ℝ)) (T x : ℝ) :
    ‖paperHalfLineCayleySymbol F T x‖ = 1 := norm_realCayley _

/-- Full continuum multiplication, on the literal translated half-line. -/
def paperHalfLineCayley (F : C(ℝ, ℝ)) (T : ℝ) : H →L[ℂ] H :=
  lpBoundedMulCLM (paperHalfLineCayleySymbol F T).continuous.measurable zero_le_one
    (fun x => (paperHalfLineCayleySymbol_norm F T x).le)

theorem paperHalfLineCayley_coeFn (F : C(ℝ, ℝ)) (T : ℝ) (f : H) :
    (paperHalfLineCayley F T f : ℝ → ℂ) =ᵐ[halfLineMeasure]
      fun x => realCayley (F (T + x)) * f x := lpBoundedMulCLM_coeFn _ _ _ f

theorem paperHalfLineCayley_norm_map (F : C(ℝ, ℝ)) (T : ℝ) (f : H) :
    ‖paperHalfLineCayley F T f‖ = ‖f‖ := by
  have h : ∀ᵐ x ∂halfLineMeasure, ‖paperHalfLineCayley F T f x‖ = ‖f x‖ := by
    filter_upwards [paperHalfLineCayley_coeFn F T f] with x hx
    rw [hx, norm_mul, norm_realCayley, one_mul]
  exact le_antisymm (Lp.norm_le_norm_of_ae_le (h.mono fun _ hx => hx.le))
    (Lp.norm_le_norm_of_ae_le (h.mono fun _ hx => hx.ge))

theorem paperHalfLineCayley_surjective (F : C(ℝ, ℝ)) (T : ℝ) :
    Function.Surjective (paperHalfLineCayley F T) := by
  let ψ := paperHalfLineCayleySymbol F T
  have hne : ∀ x, ψ x ≠ 0 := fun x => norm_ne_zero_iff.mp (by rw [paperHalfLineCayleySymbol_norm]; norm_num)
  have hm : Measurable (fun x => (ψ x)⁻¹) := ψ.continuous.measurable.inv
  have hb : ∀ x, ‖(ψ x)⁻¹‖ ≤ 1 := fun x => by
    rw [norm_inv, paperHalfLineCayleySymbol_norm, inv_one]
  intro f
  refine ⟨lpBoundedMulCLM hm zero_le_one hb f, Lp.ext ?_⟩
  filter_upwards [paperHalfLineCayley_coeFn F T (lpBoundedMulCLM hm zero_le_one hb f),
    lpBoundedMulCLM_coeFn hm zero_le_one hb f] with x hA hB
  rw [hA, hB]
  change ψ x * ((ψ x)⁻¹ * f x) = f x
  rw [← mul_assoc, mul_inv_cancel₀ (hne x), one_mul]

/-- Unitary parametrization of the entire source tail. -/
def paperHalfLineCayleyEquiv (F : C(ℝ, ℝ)) (T : ℝ) : H ≃ₗᵢ[ℂ] H :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap := (paperHalfLineCayley F T).toLinearMap
      norm_map' := paperHalfLineCayley_norm_map F T }
    (paperHalfLineCayley_surjective F T)

theorem paperHalfLineCayley_spectrum (F : C(ℝ, ℝ)) (T : ℝ) :
    spectrum ℂ (paperHalfLineCayley F T) =
      closure (realCayley '' (F '' Ici T)) := by
  rw [paperHalfLine_spectrum (paperHalfLineCayleySymbol F T).continuous
    (paperHalfLineCayley_coeFn F T)]
  congr 1
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    change 0 ≤ x at hx
    exact ⟨F (T + x), ⟨T + x, show T ≤ T + x by linarith, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨t, ht, rfl⟩, rfl⟩
    change T ≤ t at ht
    refine ⟨t - T, show 0 ≤ t - T by linarith, ?_⟩
    change realCayley (F (T + (t - T))) = realCayley (F t)
    congr 2
    ring

theorem paperHalfLineCayley_norm (F : C(ℝ, ℝ)) (T : ℝ) :
    ‖paperHalfLineCayley F T‖ = 1 := by
  apply le_antisymm
  · exact norm_lpBoundedMulCLM_le _ _ _
  · have h := spectrum.norm_le_norm_of_mem
      (paperHalfLine_value_mem_spectrum (paperHalfLineCayleySymbol F T).continuous
        (paperHalfLineCayley_coeFn F T) (show (0 : ℝ) < 1 by norm_num))
    simpa only [paperHalfLineCayleySymbol_norm] using h

theorem paperHalfLineCayley_difference_coeFn (F G : C(ℝ, ℝ)) (T : ℝ) (f : H) :
    ((paperHalfLineCayley F T - paperHalfLineCayley G T) f : ℝ → ℂ) =ᵐ[halfLineMeasure]
      fun x => (realCayley (F (T + x)) - realCayley (G (T + x))) * f x := by
  filter_upwards [Lp.coeFn_sub (paperHalfLineCayley F T f) (paperHalfLineCayley G T f),
    paperHalfLineCayley_coeFn F T f, paperHalfLineCayley_coeFn G T f] with x hs hF hG
  change ((paperHalfLineCayley F T f - paperHalfLineCayley G T f : H) : ℝ → ℂ) x = _
  rw [hs, Pi.sub_apply, hF, hG, sub_mul]

theorem paperHalfLineCayley_difference_essentialNorm (F G : C(ℝ, ℝ)) (T : ℝ) :
    compactIdealDistance (paperHalfLineCayley F T - paperHalfLineCayley G T) =
      ‖paperHalfLineCayley F T - paperHalfLineCayley G T‖ :=
  paperHalfLine_compactIdealDistance (paperHalfLineCayley_difference_coeFn F G T)

/-- Equality modulo compacts is exactly equality of the full source tails. -/
theorem paperHalfLineCayley_compact_difference_iff (F G : C(ℝ, ℝ)) (T : ℝ) :
    IsCompactOperator (paperHalfLineCayley F T - paperHalfLineCayley G T) ↔
      ∀ t ≥ T, F t = G t := by
  rw [paperHalfLine_compact_iff_zero (paperHalfLineCayley_difference_coeFn F G T)]
  constructor
  · intro h t ht
    have hv := paperHalfLine_nonneg_value_mem_spectrum
      ((paperHalfLineCayleySymbol F T).continuous.sub (paperHalfLineCayleySymbol G T).continuous)
      (paperHalfLineCayley_difference_coeFn F G T) (show 0 ≤ t - T by linarith)
    have hn := spectrum.norm_le_norm_of_mem hv
    rw [h, norm_zero] at hn
    have he := sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hn (norm_nonneg _)))
    apply injective_realCayley
    simpa only [paperHalfLineCayleySymbol, ContinuousMap.coe_mk, add_sub_cancel] using he
  · intro h
    apply sub_eq_zero.mpr
    apply ContinuousLinearMap.ext
    intro f
    apply Lp.ext
    filter_upwards [paperHalfLineCayley_coeFn F T f, paperHalfLineCayley_coeFn G T f,
      ae_restrict_mem measurableSet_Ici] with x hF hG hx
    change 0 ≤ x at hx
    rw [hF, hG, h (T + x) (by linarith)]

end
end GaloisForLFunctions.HTGeometry
