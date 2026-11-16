import GaloisForLFunctions.HTGeometry.Probability.ComplexBlockSphereMoments
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Coordinate moments of the Euclidean sphere

Cartesian Gaussian factorization and homogeneous polar integration evaluate
all mixed moments of the sphere coordinates. Odd coordinate exponents vanish;
the squared coordinates have the Dirichlet half-parameter moment formula.
-/

open MeasureTheory Set Metric
open scoped BigOperators
namespace GaloisForLFunctions.RepresentationLifting.Spinor
noncomputable section
open GaloisForLFunctions.HTGeometry

/-- The whole-line even Gaussian moment, with its exact Gamma normalization. -/
theorem integral_real_even_pow_gaussian (k : ℕ) :
    (∫ x : ℝ, x^(2*k) * Real.exp (-x^2)) = Real.Gamma ((k:ℝ)+1/2) := by
  have h := RHTower.integral_rpow_mul_exp_neg_mul_sq_Ioi
    (sig := (2*k : ℕ)) (lt_of_lt_of_le (by norm_num : (-1:ℝ)<0) (Nat.cast_nonneg _)) (b := 1) zero_lt_one
  have he : (((2*k : ℕ) : ℝ)+1)/2 = (k:ℝ)+1/2 := by push_cast; ring
  simp only [Real.rpow_natCast, he, div_self one_ne_zero, Real.one_rpow,
    mul_one, neg_mul, one_mul] at h
  have habs (x : ℝ) : |x|^(2*k) = x^(2*k) := by
    rw [pow_mul, sq_abs, ← pow_mul]
  have ha := integral_comp_abs (f := fun x : ℝ => x^(2*k)*Real.exp (-x^2))
  simp only [habs, sq_abs] at ha
  rw [ha, h]
  ring

/-- Odd Gaussian moments vanish by reflection, including the Bochner zero convention. -/
theorem integral_real_odd_pow_gaussian (k : ℕ) :
    (∫ x : ℝ, x^(2*k+1) * Real.exp (-x^2)) = 0 := by
  have h := (Homeomorph.neg ℝ).measurableEmbedding.integral_map
    (μ := volume) (fun x : ℝ => x^(2*k+1)*Real.exp (-x^2))
  have hn : (⇑(Homeomorph.neg ℝ) : ℝ → ℝ) = Neg.neg := rfl
  rw [hn, Measure.map_neg_eq_self] at h
  have ho : Odd (2*k+1) := ⟨k, by omega⟩
  simp only [ho.neg_pow, neg_sq, neg_mul, integral_neg] at h
  linarith only [h]

/-- An arbitrary coordinate monomial on Euclidean space. -/
def coordinateMonomial (e : Fin (d+1) → ℕ) (x : EuclideanSpace ℝ (Fin (d+1))) : ℝ :=
  ∏ i, x i ^ e i

/-- Cartesian Gaussian factorization for all coordinate monomials. -/
theorem integral_coordinateMonomial_gaussian (e : Fin (d+1) → ℕ) :
    (∫ x : EuclideanSpace ℝ (Fin (d+1)),
      coordinateMonomial e x * Real.exp (-‖x‖^2)) =
      ∏ i, ∫ t : ℝ, t^(e i)*Real.exp (-t^2) := by
  have he (x : EuclideanSpace ℝ (Fin (d+1))) :
      coordinateMonomial e x * Real.exp (-‖x‖^2) =
        ∏ i, (x i^(e i) * Real.exp (-(x i)^2)) := by
    rw [Finset.prod_mul_distrib, ← Real.exp_sum]
    congr 1
    rw [Finset.sum_neg_distrib, EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs]
  simp_rw [he]
  rw [← (PiLp.volume_preserving_toLp (Fin (d+1))).integral_comp
    (MeasurableEquiv.toLp 2 (Fin (d+1) → ℝ)).measurableEmbedding]
  change (∫ x : Fin (d+1) → ℝ, ∏ i, (x i^(e i)*Real.exp (-(x i)^2))) = _
  convert! integral_fintype_prod_volume_eq_prod
    (fun i (t : ℝ) => t^(e i)*Real.exp (-t^2)) using 1

/-- The radial factor for an arbitrary homogeneous polynomial degree. -/
lemma integral_Ioi_degree_pow_gaussian (d k : ℕ) :
    (∫ r in Ioi (0:ℝ), r^(d+k)*Real.exp (-r^2)) =
      Real.Gamma ((((d+1:ℕ):ℝ)+k)/2)/2 := by
  have h := RHTower.integral_rpow_mul_exp_neg_mul_sq_Ioi
    (sig := ((d+k:ℕ):ℝ)) (lt_of_lt_of_le (by norm_num : (-1:ℝ)<0) (Nat.cast_nonneg _)) (b := 1) zero_lt_one
  have he : (((d+k:ℕ):ℝ)+1)/2 = (((d+1:ℕ):ℝ)+k)/2 := by push_cast; ring
  simp only [Real.rpow_natCast, he, div_self one_ne_zero, Real.one_rpow,
    mul_one, neg_mul, one_mul] at h
  convert h using 1
  ring

/-- Polar separation for all coordinate monomials, including odd degrees. -/
theorem integral_coordinateMonomial_gaussian_polar (e : Fin (d+1) → ℕ) :
    (∫ x : EuclideanSpace ℝ (Fin (d+1)),
      coordinateMonomial e x * Real.exp (-‖x‖^2)) =
      (∫ ω : sphere (0 : EuclideanSpace ℝ (Fin (d+1))) 1,
        coordinateMonomial e ω.1 ∂volume.toSphere) *
      (Real.Gamma ((((d+1:ℕ):ℝ) + ∑ i, (e i:ℝ))/2)/2) := by
  have hh (r : ℝ) (_ : 0 < r) (x : EuclideanSpace ℝ (Fin (d+1))) :
      coordinateMonomial e (r • x) = r^(∑ i, e i)*coordinateMonomial e x := by
    simp only [coordinateMonomial, PiLp.smul_apply, smul_eq_mul, mul_pow,
      Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [integral_homogeneous_mul_gaussian (coordinateMonomial e) (∑ i, e i) hh]
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.add_sub_cancel,
    integral_Ioi_degree_pow_gaussian, Nat.cast_sum]

/-- A sphere monomial with any specified odd coordinate has zero integral. -/
theorem sphereCoordinateMonomial_odd (e : Fin (d+1) → ℕ) (j : Fin (d+1)) (k : ℕ) :
    (∫ ω : sphere (0 : EuclideanSpace ℝ (Fin (d+1))) 1,
      coordinateMonomial (Function.update e j (2*k+1)) ω.1 ∂volume.toSphere) = 0 := by
  have h := (integral_coordinateMonomial_gaussian (Function.update e j (2*k+1))).symm.trans
    (integral_coordinateMonomial_gaussian_polar (Function.update e j (2*k+1)))
  have hz : (∏ i, ∫ t : ℝ, t^(Function.update e j (2*k+1) i)*Real.exp (-t^2)) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp only [Function.update_self, integral_real_odd_pow_gaussian]
  rw [hz] at h
  have hg : Real.Gamma ((((d+1:ℕ):ℝ) +
      ∑ i, ((Function.update e j (2*k+1) i : ℕ):ℝ))/2)/2 ≠ 0 := by
    apply div_ne_zero _ two_ne_zero
    exact (Real.Gamma_pos_of_pos (by positivity)).ne'
  exact (mul_eq_zero.mp h.symm).resolve_right hg

/-- A mixed even coordinate monomial on Euclidean space. -/
def evenCoordinateMonomial (e : Fin (d+1) → ℕ) (x : EuclideanSpace ℝ (Fin (d+1))) : ℝ :=
  ∏ i, x i ^ (2*e i)

/-- Gaussian integration separates all coordinate moments simultaneously. -/
theorem integral_evenCoordinateMonomial_gaussian (e : Fin (d+1) → ℕ) :
    (∫ x : EuclideanSpace ℝ (Fin (d+1)),
      evenCoordinateMonomial e x * Real.exp (-‖x‖^2)) =
      ∏ i, Real.Gamma ((e i:ℝ)+1/2) := by
  change (∫ x : EuclideanSpace ℝ (Fin (d+1)),
    coordinateMonomial (fun i => 2*e i) x * Real.exp (-‖x‖^2)) = _
  rw [integral_coordinateMonomial_gaussian]
  simp only [integral_real_even_pow_gaussian]

/-- The mixed monomial is homogeneous of the sum of its coordinate degrees. -/
lemma evenCoordinateMonomial_homogeneous (e : Fin (d+1) → ℕ) (r : ℝ)
    (x : EuclideanSpace ℝ (Fin (d+1))) :
    evenCoordinateMonomial e (r • x) = r^(2*∑ i, e i)*evenCoordinateMonomial e x := by
  simp only [evenCoordinateMonomial, PiLp.smul_apply, smul_eq_mul, mul_pow,
    Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_pow_eq_pow_sum, ← Finset.mul_sum]

/-- Polar integration identifies the radial Gamma factor for every mixed moment. -/
theorem integral_evenCoordinateMonomial_gaussian_polar (e : Fin (d+1) → ℕ) :
    (∫ x : EuclideanSpace ℝ (Fin (d+1)),
      evenCoordinateMonomial e x * Real.exp (-‖x‖^2)) =
      (∫ ω : sphere (0 : EuclideanSpace ℝ (Fin (d+1))) 1,
        evenCoordinateMonomial e ω.1 ∂volume.toSphere) *
      (Real.Gamma (((d+1:ℕ):ℝ)/2 + ∑ i, (e i:ℝ))/2) := by
  rw [integral_homogeneous_mul_gaussian (evenCoordinateMonomial e) (2*∑ i, e i)
    (fun r _ x => evenCoordinateMonomial_homogeneous e r x),
    integral_Ioi_dimension_pow_gaussian Module.finrank_pos]
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.cast_sum]

/-- Normalized mixed moments of the squared Euclidean sphere coordinates. -/
def sphereEvenCoordinateMoment (e : Fin (d+1) → ℕ) : ℝ :=
  (∫ ω : sphere (0 : EuclideanSpace ℝ (Fin (d+1))) 1,
    evenCoordinateMonomial e ω.1 ∂volume.toSphere) /
    (volume.toSphere : Measure (sphere (0 : EuclideanSpace ℝ (Fin (d+1))) 1)).real univ

/-- The full Dirichlet half-parameter moment formula, with no distributional assumption. -/
theorem sphereEvenCoordinateMoment_eq (e : Fin (d+1) → ℕ) :
    sphereEvenCoordinateMoment e =
      (∏ i, Real.Gamma ((e i:ℝ)+1/2)) * Real.Gamma (((d+1:ℕ):ℝ)/2) /
        (Real.Gamma (1/2)^(d+1) *
          Real.Gamma (((d+1:ℕ):ℝ)/2 + ∑ i, (e i:ℝ))) := by
  have hzero := (integral_evenCoordinateMonomial_gaussian (d := d) (fun _ => 0)).symm.trans
    (integral_evenCoordinateMonomial_gaussian_polar (d := d) (fun _ => 0))
  have he := (integral_evenCoordinateMonomial_gaussian e).symm.trans
    (integral_evenCoordinateMonomial_gaussian_polar e)
  simp only [evenCoordinateMonomial, Nat.mul_zero, pow_zero, Finset.prod_const_one,
    Nat.cast_zero, zero_add, Finset.sum_const_zero, add_zero, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, integral_const, smul_eq_mul, mul_one] at hzero
  have hbase : Real.Gamma (1/2)^ (d+1) ≠ 0 :=
    pow_ne_zero _ (Real.Gamma_pos_of_pos (by norm_num)).ne'
  have hdim : 0 < (((d+1:ℕ):ℝ)/2) := by positivity
  have hg : Real.Gamma (((d+1:ℕ):ℝ)/2 + ∑ i, (e i:ℝ)) ≠ 0 :=
    (Real.Gamma_pos_of_pos (add_pos_of_pos_of_nonneg hdim (by positivity))).ne'
  have hm : (volume.toSphere : Measure (sphere (0 : EuclideanSpace ℝ (Fin (d+1))) 1)).real univ ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hzero
    exact hbase hzero
  unfold sphereEvenCoordinateMoment
  apply (div_eq_div_iff hm (mul_ne_zero hbase hg)).mpr
  linear_combination -2 * Real.Gamma (1/2)^(d+1) * he +
    2 * (∏ i, Real.Gamma ((e i:ℝ)+1/2)) * hzero

#print axioms sphereCoordinateMonomial_odd
#print axioms integral_evenCoordinateMonomial_gaussian
#print axioms sphereEvenCoordinateMoment_eq
end
end GaloisForLFunctions.RepresentationLifting.Spinor
