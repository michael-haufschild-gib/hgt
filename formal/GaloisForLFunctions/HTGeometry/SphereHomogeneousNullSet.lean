/-
# A homogeneous polynomial vanishes on a null set of directions

The sphere measure of a set of directions is the ambient measure of the punctured cone it spans.
For a homogeneous polynomial that cone is inside the polynomial's own zero set, which is Lebesgue
null, so the directions on which a nonzero homogeneous polynomial vanishes form a null set of the
unit sphere.  This is the sphere-side counterpart of the ambient statement the shell arguments
already use.

Main results:
* `sphereZeroSet`, `measurableSet_sphereZeroSet` — the zero set of a polynomial on the sphere.
* `volume_euclidean_zeroSet_eq_zero` — the ambient zero set is null.
* `toSphere_sphereZeroSet_eq_zero` — **a nonzero homogeneous polynomial vanishes on a null set of
  directions**.
* `toSphere_eq_zero_of_scaleInvariant` — **every scale-invariant Lebesgue-null set is null on the
  sphere**.
-/
import GaloisForLFunctions.HTGeometry.SphereMeasureIsometryInvariance
import GaloisForLFunctions.HTGeometry.PolynomialSublevelSphere
import GaloisForLFunctions.HTGeometry.RealPolynomialZeroMeasure
import GaloisForLFunctions.HTGeometry.EuclideanAnalyticNullPreimage

open MeasureTheory Metric Set
open scoped Pointwise

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {m : ℕ}

/-- The zero set of a real polynomial, read on the unit sphere of directions. -/
def sphereZeroSet (P : MvPolynomial (Fin m) ℝ) :
    Set (sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :=
  {θ | MvPolynomial.eval (WithLp.ofLp (θ : EuclideanSpace ℝ (Fin m))) P = 0}

theorem continuous_sphereEval (P : MvPolynomial (Fin m) ℝ) :
    Continuous fun θ : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
      MvPolynomial.eval (WithLp.ofLp (θ : EuclideanSpace ℝ (Fin m))) P :=
  ((MvPolynomial.continuous_eval P).comp (PiLp.continuous_ofLp 2 _)).comp continuous_subtype_val

theorem measurableSet_sphereZeroSet (P : MvPolynomial (Fin m) ℝ) :
    MeasurableSet (sphereZeroSet P) :=
  ((isClosed_singleton (x := (0 : ℝ))).preimage (continuous_sphereEval P)).measurableSet

/-- The ambient zero set of a nonzero polynomial is Lebesgue null. -/
theorem volume_euclidean_zeroSet_eq_zero {P : MvPolynomial (Fin m) ℝ} (hP : P ≠ 0) :
    (volume : Measure (EuclideanSpace ℝ (Fin m)))
      {x : EuclideanSpace ℝ (Fin m) | MvPolynomial.eval (WithLp.ofLp x) P = 0} = 0 := by
  refine measure_eq_zero_of_preimage_eq_zero (euclCoord m).toEquiv
    (measurePreserving_euclCoord_symm m) ?_
  exact realMvPolynomial_zero_set_volume_fin m P hP

/-- **A nonzero homogeneous polynomial vanishes on a null set of directions.** -/
theorem toSphere_sphereZeroSet_eq_zero {P : MvPolynomial (Fin m) ℝ} {d : ℕ}
    (hhom : P.IsHomogeneous d) (hP : P ≠ 0) :
    (volume : Measure (EuclideanSpace ℝ (Fin m))).toSphere (sphereZeroSet P) = 0 := by
  rw [Measure.toSphere_apply' _ (measurableSet_sphereZeroSet P)]
  have hsub : (Ioo (0 : ℝ) 1) • (Subtype.val '' (sphereZeroSet P))
      ⊆ {x : EuclideanSpace ℝ (Fin m) | MvPolynomial.eval (WithLp.ofLp x) P = 0} := by
    rintro y ⟨r, hr, x, hx, rfl⟩
    obtain ⟨θ, hθ, rfl⟩ := hx
    have hcoord : (WithLp.ofLp (r • ((θ : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
        EuclideanSpace ℝ (Fin m))))
        = fun i => r * (WithLp.ofLp ((θ : EuclideanSpace ℝ (Fin m)))) i := rfl
    show MvPolynomial.eval (WithLp.ofLp (r • ((θ : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
      EuclideanSpace ℝ (Fin m)))) P = 0
    rw [hcoord, eval_smul_of_isHomogeneous hhom]
    have hzero : MvPolynomial.eval (WithLp.ofLp ((θ : EuclideanSpace ℝ (Fin m)))) P = 0 := hθ
    rw [hzero, mul_zero]
  rw [measure_mono_null hsub (volume_euclidean_zeroSet_eq_zero hP), mul_zero]

/-! ## Scale-invariant null sets -/

/-- **A scale-invariant Lebesgue-null set meets the sphere in a null set of directions.**  The cone
over the directions is inside the set itself, and the sphere measure of a set of directions is the
ambient measure of that cone. -/
theorem toSphere_eq_zero_of_scaleInvariant {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {B : Set E} (hnull : (volume : Measure E) B = 0)
    (hcone : ∀ r : ℝ, 0 < r → ∀ x ∈ B, r • x ∈ B)
    {S : Set (sphere (0 : E) 1)} (hS : MeasurableSet S)
    (hsub : ∀ θ ∈ S, ((θ : E)) ∈ B) :
    (volume : Measure E).toSphere S = 0 := by
  rw [Measure.toSphere_apply' _ hS]
  have hsub2 : (Ioo (0 : ℝ) 1) • (Subtype.val '' S) ⊆ B := by
    rintro y ⟨r, hr, x, hx, rfl⟩
    obtain ⟨θ, hθ, rfl⟩ := hx
    exact hcone r hr.1 _ (hsub θ hθ)
  rw [measure_mono_null hsub2 hnull, mul_zero]

end

end GaloisForLFunctions.HTGeometry
