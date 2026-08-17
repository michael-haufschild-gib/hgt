import GaloisForLFunctions.HTGeometry.GaussianAngularPolarDisintegrationLaw

/-!
# Lebesgue measure in polar coordinates

Removing the origin, the ambient space is homeomorphic to the product of the unit sphere with the
positive half line, and that homeomorphism carries Lebesgue measure to the product of the surface
measure with the weighted radial measure `r^{m-1}dr`.

Hence every integral against Lebesgue measure is an integral over the sphere of a radial integral,
with the Jacobian `r^{m-1}`.  This is the form an integration-by-parts argument on the sphere
consumes: a compactly supported radial cutoff separates, and the angular factor is left.
-/

open MeasureTheory Metric Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Polar coordinates for Lebesgue measure.**  Every integral over the ambient space is an
integral over the sphere times the half line, with the radial Jacobian carried by
`Measure.volumeIoiPow`. -/
theorem integral_eq_polar {m : ℕ} (hm : 0 < m) (f : EuclideanSpace ℝ (Fin m) → F) :
    ∫ x, f x
      = ∫ p : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 × Ioi (0 : ℝ), f (p.2.1 • p.1.1)
          ∂((volume : Measure (EuclideanSpace ℝ (Fin m))).toSphere.prod
            (Measure.volumeIoiPow (m - 1))) := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  haveI : Nontrivial (EuclideanSpace ℝ (Fin m)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by simpa using hm)
  calc ∫ x, f x
      = ∫ x : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin m))), f x.1
          ∂((volume : Measure (EuclideanSpace ℝ (Fin m))).comap (↑)) := by
        rw [integral_subtype_comap (measurableSet_singleton _).compl f, restrict_compl_singleton]
    _ = ∫ p : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 × Ioi (0 : ℝ),
          f (((homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin m))).symm p).1)
          ∂((volume : Measure (EuclideanSpace ℝ (Fin m))).toSphere.prod
            (Measure.volumeIoiPow (m - 1))) := by
        simpa using
          (volume :
            Measure (EuclideanSpace ℝ (Fin m))).measurePreserving_homeomorphUnitSphereProd.integral_comp
            (Homeomorph.measurableEmbedding _)
            (fun p : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 × Ioi (0 : ℝ) =>
              f (((homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin m))).symm p).1))
    _ = _ := by
        apply integral_congr_ae
        filter_upwards with p
        rw [homeomorphUnitSphereProd_symm_apply_coe]

/-- The radial factor of the polar formula, with the Jacobian written out. -/
theorem integral_volumeIoiPow_eq {m : ℕ} (g : ℝ → F) :
    ∫ r : Ioi (0 : ℝ), g r.1 ∂(Measure.volumeIoiPow (m - 1))
      = ∫ y in Ioi (0 : ℝ), y ^ (m - 1) • g y :=
  integral_volumeIoiPow_comp_subtype (m - 1) g

/-- **Radial--angular separation.**  An integrand that factors into a radial and an angular part
integrates to the product of the radial integral with the Jacobian and the angular integral. -/
theorem integral_polar_mul {m : ℕ} (hm : 0 < m) (φ : ℝ → ℝ)
    (G : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 → ℝ)
    (f : EuclideanSpace ℝ (Fin m) → ℝ)
    (hf : ∀ (ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) (r : Ioi (0 : ℝ)),
      f (r.1 • ω.1) = G ω * φ r.1) :
    ∫ x, f x
      = (∫ ω, G ω ∂((volume : Measure (EuclideanSpace ℝ (Fin m))).toSphere))
        * ∫ y in Ioi (0 : ℝ), y ^ (m - 1) * φ y := by
  rw [integral_eq_polar hm f]
  have hpoint : ∀ p : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 × Ioi (0 : ℝ),
      f (p.2.1 • p.1.1) = G p.1 * φ p.2.1 := fun p => hf p.1 p.2
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)]
  rw [integral_prod_mul (μ := (volume : Measure (EuclideanSpace ℝ (Fin m))).toSphere)
    (ν := Measure.volumeIoiPow (m - 1)) G (fun r : Ioi (0 : ℝ) => φ r.1)]
  congr 1
  have := integral_volumeIoiPow_eq (m := m) (F := ℝ) φ
  simpa using this

end

end GaloisForLFunctions.HTGeometry
