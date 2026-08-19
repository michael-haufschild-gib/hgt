/-
# Absolute continuity of a spectral phase pushforward on the unit sphere

A phase which is constant on rays is determined by its restriction to the unit sphere, and the
open cone over a subset of the sphere is exactly the punctured-unit-ball part of the preimage.
Since the surface measure of a set is a multiple of the Lebesgue measure of the cone over it, the
null-preimage law on Euclidean space transfers verbatim: a ray-constant phase which is analytic and
nonconstant on every open patch of a full-measure open cone pushes the surface measure forward to
an absolutely continuous measure.

This is the analytic input the Riemann--Lebesgue dephasing engine consumes.

Main results:
* `cone_preimage_eq` — the cone over a sphere preimage is a punctured-ball preimage.
* `toSphere_map_absolutelyContinuous_of_analytic` — **the pushforward is absolutely continuous**.
* `tendsto_integral_exp_sphere_phase_zero` — **the resulting angular dephasing**.
-/
import GaloisForLFunctions.HTGeometry.EuclideanAnalyticNullPreimage
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import GaloisForLFunctions.HTGeometry.AnnealedSpectralDephasing

open Set MeasureTheory Metric
open scoped Pointwise

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {m : ℕ}

/-- **The cone identity.**  For a phase constant on rays, the open cone over the sphere preimage of
a set is the punctured-unit-ball part of its preimage. -/
theorem cone_preimage_eq {Φ : EuclideanSpace ℝ (Fin m) → ℝ}
    (hhom : ∀ r : ℝ, 0 < r → ∀ y, Φ (r • y) = Φ y) (E : Set ℝ) :
    Ioo (0 : ℝ) 1 • (Subtype.val ''
        ((fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 => Φ (x : _)) ⁻¹' E))
      = (Φ ⁻¹' E) ∩ (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) 1 \ {0}) := by
  ext y
  constructor
  · rintro ⟨r, hr, z, ⟨x, hxE, rfl⟩, rfl⟩
    have hnorm : ‖(x : EuclideanSpace ℝ (Fin m))‖ = 1 := by simp
    refine ⟨?_, ?_, ?_⟩
    · simpa [hhom r hr.1 (x : EuclideanSpace ℝ (Fin m))] using hxE
    · simp only [Metric.mem_ball, dist_zero_right, norm_smul, hnorm, mul_one,
        Real.norm_eq_abs, abs_of_pos hr.1]
      exact hr.2
    · simp only [Set.mem_singleton_iff, smul_eq_zero, not_or]
      refine ⟨hr.1.ne', ?_⟩
      intro hx0
      rw [hx0] at hnorm
      simp at hnorm
  · rintro ⟨hyE, hyball, hy0⟩
    have hy0' : y ≠ 0 := hy0
    have hnorm : 0 < ‖y‖ := norm_pos_iff.mpr hy0'
    have hnorm1 : ‖y‖ < 1 := by simpa [dist_zero_right] using hyball
    refine ⟨‖y‖, ⟨hnorm, hnorm1⟩, ‖y‖⁻¹ • y, ⟨⟨‖y‖⁻¹ • y, ?_⟩, ?_, rfl⟩, ?_⟩
    · simp [norm_smul, inv_mul_cancel₀ hnorm.ne']
    · simpa [hhom ‖y‖⁻¹ (inv_pos.mpr hnorm) y] using hyE
    · show ‖y‖ • (‖y‖⁻¹ • y) = y
      rw [smul_smul, mul_inv_cancel₀ hnorm.ne', one_smul]

/-- **The pushforward of the surface measure by a ray-constant analytic phase is absolutely
continuous.** -/
theorem toSphere_map_absolutelyContinuous_of_analytic
    {Φ : EuclideanSpace ℝ (Fin m) → ℝ} (hmeasΦ : Measurable Φ)
    (hhom : ∀ r : ℝ, 0 < r → ∀ y, Φ (r • y) = Φ y)
    {U : Set (EuclideanSpace ℝ (Fin m))} (hU : IsOpen U)
    (hΦ : AnalyticOnNhd ℝ Φ U)
    (hnc : ∀ V : Set (EuclideanSpace ℝ (Fin m)), IsOpen V → V.Nonempty → V ⊆ U →
      ∃ p ∈ V, ∃ q ∈ V, Φ p ≠ Φ q)
    (hfull : volume ((Metric.ball (0 : EuclideanSpace ℝ (Fin m)) 1 \ {0}) \ U) = 0) :
    Measure.map (fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 => Φ (x : _))
      volume.toSphere ≪ volume := by
  have hphimeas : Measurable
      (fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 => Φ (x : _)) :=
    hmeasΦ.comp measurable_subtype_coe
  intro E hE
  obtain ⟨E', hEE', hE'meas, hE'null⟩ := exists_measurable_superset_of_null hE
  refine measure_mono_null hEE' ?_
  rw [Measure.map_apply hphimeas hE'meas]
  have hA : MeasurableSet
      ((fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 => Φ (x : _)) ⁻¹' E') :=
    hphimeas hE'meas
  rw [Measure.toSphere_apply' volume hA, cone_preimage_eq hhom E']
  have hsplit : (Φ ⁻¹' E') ∩ (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) 1 \ {0}) ⊆
      (U ∩ Φ ⁻¹' E') ∪ ((Metric.ball (0 : EuclideanSpace ℝ (Fin m)) 1 \ {0}) \ U) := by
    rintro y ⟨hyE, hyb⟩
    by_cases hyU : y ∈ U
    · exact Or.inl ⟨hyU, hyE⟩
    · exact Or.inr ⟨hyb, hyU⟩
  have hnull : volume ((Φ ⁻¹' E') ∩
      (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) 1 \ {0})) = 0 := by
    refine measure_mono_null hsplit ?_
    refine measure_union_null ?_ hfull
    exact analytic_preimage_volume_eq_zero_isOpen_euclidean hU hΦ hnc E' hE'null
  rw [hnull, mul_zero]

/-- **Angular dephasing on the unit sphere.**  A ray-constant phase which is analytic and
nonconstant on every open patch of a full-measure open cone dephases every bounded weight: the
oscillatory average over the sphere tends to zero at large frequency. -/
theorem tendsto_integral_exp_sphere_phase_zero
    {Φ : EuclideanSpace ℝ (Fin m) → ℝ} (hmeasΦ : Measurable Φ)
    (hhom : ∀ r : ℝ, 0 < r → ∀ y, Φ (r • y) = Φ y)
    {U : Set (EuclideanSpace ℝ (Fin m))} (hU : IsOpen U)
    (hΦ : AnalyticOnNhd ℝ Φ U)
    (hnc : ∀ V : Set (EuclideanSpace ℝ (Fin m)), IsOpen V → V.Nonempty → V ⊆ U →
      ∃ p ∈ V, ∃ q ∈ V, Φ p ≠ Φ q)
    (hfull : volume ((Metric.ball (0 : EuclideanSpace ℝ (Fin m)) 1 \ {0}) \ U) = 0)
    (g : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 → ℂ) (hg : Measurable g)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x, ‖g x‖ ≤ C) :
    Filter.Tendsto (fun t : ℝ => ∫ x, g x *
        Complex.exp (-((t * Φ (x : _) : ℝ) : ℂ) * Complex.I) ∂(volume.toSphere))
      (Filter.cocompact ℝ) (nhds 0) :=
  tendsto_integral_exp_phase_weight volume.toSphere (hmeasΦ.comp measurable_subtype_coe)
    (toSphere_map_absolutelyContinuous_of_analytic hmeasΦ hhom hU hΦ hnc hfull) g hg hC0 hC

end

end GaloisForLFunctions.HTGeometry
