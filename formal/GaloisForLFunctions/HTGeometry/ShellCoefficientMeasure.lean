/-
# The fixed-shell coefficient law and its signed-permutation invariance

Pushing the unit-sphere measure forward along the coordinate map turns it into a law on the
coefficient space itself, so every statement about ensembles indexed by a coefficient vector
applies to the fixed-shell ensemble with no change of type.  Signed permutations are linear
isometries, so they preserve that law -- this is the fixed-shell replacement for the invariance of
the centred product Gaussian.

Main results:
* `shellCoefficientMap`, `shellCoefficientMeasure` — the coefficient law of the unit shell.
* `measurePreserving_signedPerm_shell` — **the shell law is invariant under signed permutations**.
* `isFiniteMeasure_shellCoefficientMeasure` — it is finite.
-/
import GaloisForLFunctions.HTGeometry.SignedPermutationIsometry
import GaloisForLFunctions.HTGeometry.SphereMeasureIsometryInvariance

open MeasureTheory Metric

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- The coordinate map from the unit sphere to the coefficient space. -/
def shellCoefficientMap (ι : Type*) [Fintype ι] :
    sphere (0 : EuclideanSpace ℝ ι) 1 → (ι → ℝ) :=
  fun θ => WithLp.ofLp ((θ : EuclideanSpace ℝ ι))

theorem continuous_shellCoefficientMap :
    Continuous (shellCoefficientMap ι) :=
  (PiLp.continuous_ofLp 2 _).comp continuous_subtype_val

theorem measurable_shellCoefficientMap : Measurable (shellCoefficientMap ι) :=
  continuous_shellCoefficientMap.measurable

/-- **The fixed-shell coefficient law**: the unit-sphere measure read in coordinates. -/
def shellCoefficientMeasure (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.map (shellCoefficientMap ι) (volume : Measure (EuclideanSpace ℝ ι)).toSphere

instance isFiniteMeasure_shellCoefficientMeasure :
    IsFiniteMeasure (shellCoefficientMeasure ι) := by
  constructor
  rw [shellCoefficientMeasure, Measure.map_apply measurable_shellCoefficientMap MeasurableSet.univ,
    Set.preimage_univ, Measure.toSphere_apply_univ]
  exact ENNReal.mul_lt_top (by simp) measure_ball_lt_top

theorem shellCoefficientMap_sphereMap {π : Equiv.Perm ι} {ε : ι → ℝ}
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) (θ : sphere (0 : EuclideanSpace ℝ ι) 1) :
    shellCoefficientMap ι (sphereMap (signedPermIsometry π hε) θ)
      = fun i => ε i * shellCoefficientMap ι θ (π i) := rfl

/-- **The fixed-shell coefficient law is invariant under every signed permutation.** -/
theorem measurePreserving_signedPerm_shell (π : Equiv.Perm ι) {ε : ι → ℝ}
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    MeasurePreserving (fun J : ι → ℝ => fun i => ε i * J (π i))
      (shellCoefficientMeasure ι) (shellCoefficientMeasure ι) := by
  set f : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι := signedPermIsometry π hε with hf
  set T : (ι → ℝ) → (ι → ℝ) := fun J => fun i => ε i * J (π i) with hT
  have hTmeas : Measurable T := by
    refine measurable_pi_lambda _ fun i => ?_
    exact measurable_const.mul (measurable_pi_apply (π i))
  refine ⟨hTmeas, ?_⟩
  have hcomp : T ∘ shellCoefficientMap ι = shellCoefficientMap ι ∘ sphereMap f := by
    funext θ
    exact (shellCoefficientMap_sphereMap hε θ).symm
  calc Measure.map T (shellCoefficientMeasure ι)
      = Measure.map T (Measure.map (shellCoefficientMap ι)
          (volume : Measure (EuclideanSpace ℝ ι)).toSphere) := rfl
    _ = Measure.map (T ∘ shellCoefficientMap ι)
          (volume : Measure (EuclideanSpace ℝ ι)).toSphere :=
        Measure.map_map hTmeas measurable_shellCoefficientMap
    _ = Measure.map (shellCoefficientMap ι ∘ sphereMap f)
          (volume : Measure (EuclideanSpace ℝ ι)).toSphere := by rw [hcomp]
    _ = Measure.map (shellCoefficientMap ι) (Measure.map (sphereMap f)
          (volume : Measure (EuclideanSpace ℝ ι)).toSphere) :=
        (Measure.map_map measurable_shellCoefficientMap (measurable_sphereMap f)).symm
    _ = shellCoefficientMeasure ι := by
        rw [(measurePreserving_sphereMap f).map_eq]
        rfl

end

end GaloisForLFunctions.HTGeometry
