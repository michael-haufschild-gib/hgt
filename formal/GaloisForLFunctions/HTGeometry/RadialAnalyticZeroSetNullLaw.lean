import GaloisForLFunctions.HTGeometry.AnalyticNullPreimage
import GaloisForLFunctions.HTGeometry.GaussianRadialPolarLaw
import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-!
# Radial analytic zero-set nullity

An analytic certificate that is nonzero at the origin is nonzero on every
radial line.  One-dimensional analytic rigidity therefore makes every radial
section of its zero set countable.  Polar disintegration upgrades these
sectionwise facts to a volume-null theorem in every finite dimension.

The theorem deliberately assumes analyticity only on radial restrictions.  It
is therefore stronger than the special case of a globally analytic function
and exposes the exact input needed by later critical-Jacobian arguments.
-/

open MeasureTheory Metric Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

private theorem volume_zero_zeroSet_of_radial_analytic_of_pos
    {m : ℕ} (_hm : 0 < m)
    {g : EuclideanSpace ℝ (Fin m) → ℝ}
    (hg : Measurable g)
    (hran : ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
      AnalyticOnNhd ℝ (fun r : ℝ => g (r • (ω : EuclideanSpace ℝ (Fin m)))) univ)
    (hg0 : g 0 ≠ 0) :
    volume {x | g x = 0} = 0 := by
  let E := EuclideanSpace ℝ (Fin m)
  haveI : Nonempty (Fin m) := ⟨⟨0, _hm⟩⟩
  haveI : Nontrivial E :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by simpa [E] using _hm)
  let T : Set (sphere (0 : E) 1 × Ioi (0 : ℝ)) :=
    {p | g ((p.2 : ℝ) • (p.1 : E)) = 0}
  have hT : MeasurableSet T := by
    exact measurableSet_eq_fun
      (hg.comp
        ((continuous_subtype_val.comp continuous_snd).smul
          (continuous_subtype_val.comp continuous_fst)).measurable)
      measurable_const
  have hsection : ∀ ω : sphere (0 : E) 1,
      (Measure.volumeIoiPow (Module.finrank ℝ E - 1))
        (Prod.mk ω ⁻¹' T) = 0 := by
    intro ω
    have hcountR : {r : ℝ | g (r • (ω : E)) = 0}.Countable :=
      analytic_zero_set_countable (hran ω) ⟨0, by simpa using hg0⟩
    have hcount : (Prod.mk ω ⁻¹' T).Countable := by
      apply hcountR.preimage
      exact Subtype.val_injective
    unfold Measure.volumeIoiPow
    exact withDensity_absolutelyContinuous _ _ (by
      rw [comap_subtype_coe_apply measurableSet_Ioi]
      exact hcount.image Subtype.val |>.measure_zero _)
  have hprod :
      ((volume : Measure E).toSphere.prod
        (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) T = 0 := by
    rw [Measure.prod_apply hT]
    simp [hsection]
  have hpre :
      ((volume : Measure E).comap ((↑) : ({0}ᶜ : Set E) → E))
        ((homeomorphUnitSphereProd E) ⁻¹' T) = 0 := by
    rw [(volume : Measure E).measurePreserving_homeomorphUnitSphereProd.measure_preimage
      hT.nullMeasurableSet]
    exact hprod
  have hset :
      ((homeomorphUnitSphereProd E) ⁻¹' T) =
        {x : ({0}ᶜ : Set E) | g (x : E) = 0} := by
    ext x
    simp only [mem_preimage, mem_setOf_eq, T,
      homeomorphUnitSphereProd_apply_fst_coe,
      homeomorphUnitSphereProd_apply_snd_coe]
    change g (‖(x : E)‖ • ‖(x : E)‖⁻¹ • (x : E)) = 0 ↔ g (x : E) = 0
    have hx0 : (x : E) ≠ 0 := by
      simpa only [mem_compl_iff, mem_singleton_iff] using x.property
    simp [smul_smul, norm_ne_zero_iff.mpr hx0]
  rw [hset] at hpre
  have hcomap :
      ((volume : Measure E).comap ((↑) : ({0}ᶜ : Set E) → E))
        {x : ({0}ᶜ : Set E) | g (x : E) = 0} =
      volume ({x : E | g x = 0} ∩ {0}ᶜ) := by
    rw [comap_subtype_coe_apply (measurableSet_singleton 0).compl]
    congr 1
    ext x
    simp [and_comm]
  rw [hcomap] at hpre
  have hsubset : {x : E | g x = 0} ⊆ {0}ᶜ := by
    intro x hx
    simp only [mem_compl_iff, mem_singleton_iff]
    intro hzero
    subst x
    exact hg0 hx
  simpa [inter_eq_left.mpr hsubset] using hpre

/-- **Radial analytic zero-set nullity.**  In every finite dimension, a
measurable real-valued function whose restriction to every radial line is real
analytic and whose value at the origin is nonzero has a volume-null zero set. -/
theorem volume_zero_zeroSet_of_radial_analytic
    {m : ℕ}
    {g : EuclideanSpace ℝ (Fin m) → ℝ}
    (hg : Measurable g)
    (hran : ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
      AnalyticOnNhd ℝ (fun r : ℝ => g (r • (ω : EuclideanSpace ℝ (Fin m)))) univ)
    (hg0 : g 0 ≠ 0) :
    volume {x | g x = 0} = 0 := by
  by_cases hm : 0 < m
  · exact volume_zero_zeroSet_of_radial_analytic_of_pos hm hg hran hg0
  · have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
    subst m
    have hzero : {x : EuclideanSpace ℝ (Fin 0) | g x = 0} = ∅ := by
      ext x
      simp [Subsingleton.elim x 0, hg0]
    simp [hzero]

end

end GaloisForLFunctions.HTGeometry
